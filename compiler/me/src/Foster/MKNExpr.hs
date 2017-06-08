{-# LANGUAGE RecursiveDo, GADTs #-}
-- RecursiveDo is used in dlcSingleton

module Foster.MKNExpr (MKBound(MKBound), mkOfKNMod, mknInline, mknShrink,
                       pccOfTopTerm, knOfMK, readLink, MaybeCont(..)) where

import Foster.Base
import Foster.Config
import Foster.MainOpts(getInliningDonate)
import Foster.KNUtil
import Foster.KNExpr(knLoopHeaders')
import Foster.Worklist
import Foster.Output(putDocLn)

import Foster.CFG
import Foster.MonoType
import Foster.Letable
import Foster.Kind

import Control.Monad(liftM)
import Control.Monad.State(gets, get, put, lift, liftIO,
                           StateT, evalStateT, execStateT, runStateT)
import Data.IORef(IORef, readIORef, newIORef, writeIORef)
import Data.UnionFind.IO
import Control.Monad.IO.Class(MonadIO(..))

import qualified Data.Text as T
import qualified Data.Set as Set(toList, fromList)
import qualified Data.Map as Map
import Data.Map(Map)
import qualified Data.List as List(foldl', reverse)
import Data.Maybe(catMaybes, isJust, isNothing)
import Data.Either(partitionEithers)

import Compiler.Hoopl(UniqueMonad(..), C, O, freshLabel, intToUnique,
                      blockGraph, blockJoin, blockFromList, firstNode)

import Prelude hiding ((<$>))
import Text.PrettyPrint.ANSI.Leijen

-- Binding occurrences of variables, with link to a free occurrence (if not dead).
data MKBound x = MKBound (TypedId x) (OrdRef (Maybe (FreeOcc x)))

-- Free occurrences: doubly-linked list with union-find for access to binder.
--                   and uplink to enclosing term.
type FreeOcc x = DLCNode (FreeOccPayload x)
type FreeVar x = FreeOcc x
data FreeOccPayload x = FOP {
    fopPoint :: Point (MKBound x)
  , fopLink  :: Link (MKTerm x)
}

instance Show t => Show (MKBound t) where
    show (MKBound v _) = show v

instance Pretty t => Pretty (MKBound t) where
    pretty (MKBound v _) = pretty v

instance Eq (MKBound t) where
  (==)    (MKBound _ r1) (MKBound _ r2) = (==)    r1 r2
instance Ord (MKBound t) where
  compare (MKBound v1 _) (MKBound v2 _) = compare v1 v2
instance Eq (DLCNode x) where
  (==)    (DLCNode _ pr1 _) (DLCNode _ pr2 _) = (==)    pr1 pr2
instance Ord (DLCNode x) where
  compare (DLCNode _ pr1 _) (DLCNode _ pr2 _) = compare pr1 pr2

freeBinder :: FreeVar t -> Compiled (MKBoundVar t)
freeBinder  (DLCNode fop _ _) = liftIO $ descriptor (fopPoint fop)

freeLink :: FreeVar t -> Link (MKTerm t)
freeLink  (DLCNode fop _ _) = fopLink fop

setFreeLink :: FreeVar t -> MKTerm t -> Compiled ()
setFreeLink  (DLCNode fop _ _) tm = do writeOrdRef (fopLink fop) (Just tm)

boundVar :: MKBound t -> TypedId t
boundVar (MKBound v _) = v

boundOcc :: MKBound t -> Compiled (Maybe (FreeOcc t))
boundOcc (MKBound _ r) = readOrdRef r

{- Given a graph like this:
      b1 ----> f1       x1 <---- b2
              / \       |
            f2---f3     x2

   substVarForBound f3 b  will produce

      b1 ----> f1------x1    \--- b2
              /        |
             f2---f3---x2
-}

substVarForBound :: Pretty t => (FreeOcc t, MKBound t) -> Compiled ()
substVarForBound (fox, MKBound _ r) = do
  mb_fo <- readOrdRef r
  case mb_fo of
    Nothing -> do
      -- Substituting for a dead variable; nothing to do.
      return ()
    Just fo -> do
      substVarForVar fox fo


substVarForVar :: FreeOcc t -> FreeOcc t -> Compiled ()
substVarForVar (DLCNode px _ _) (DLCNode py _ _) = substVarForVar' (fopPoint px) (fopPoint py)

substVarForVar' :: Point (MKBound t) -> Point (MKBound t) -> Compiled ()
substVarForVar' px py | px == py = do return ()
substVarForVar' px py = do
  MKBound _ b'x <- liftIO $ descriptor px
  MKBound _ b'y <- liftIO $ descriptor py
  mergeFreeLists b'x b'y
  writeOrdRef b'y Nothing
  py `nowPointsTo` px where nowPointsTo x y = liftIO $ union x y

substVarForVar'' :: Show t => MKBound t -> MKBound t -> Compiled ()
substVarForVar'' bx by = do
  mb_fx <- boundOcc bx
  mb_fy <- boundOcc by
  case (mb_fx, mb_fy) of
    (Just fx, Just fy) -> do
      dbgDoc $ text $ "substVarForVar'' " ++ show (boundVar bx) ++ "  " ++ show (boundVar by)
      substVarForVar fx fy
    _ -> do
      dbgDoc $ text $ "substVarForVar'' doing nothing; one or both binders are dead"
      return ()

mergeFreeLists :: OrdRef (Maybe (FreeOcc t)) -> OrdRef (Maybe (FreeOcc t)) -> Compiled ()
mergeFreeLists rx ry = do
  x <- readOrdRef rx
  y <- readOrdRef ry
  case (x, y) of
    (Nothing, Nothing) -> return ()
    (Nothing, _)       -> writeOrdRef rx y
    (_, Nothing)       -> writeOrdRef ry x
    (Just nx, Just ny) -> dlcMerge nx ny

data DLCNode t = DLCNode t (OrdRef (DLCNode t)) (OrdRef (DLCNode t))

dlcNextRef (DLCNode _ _ nr) = nr
dlcPrevRef (DLCNode _ pr _) = pr

dlcNext d = readOrdRef (dlcNextRef d)
dlcPrev d = readOrdRef (dlcPrevRef d)

dlcIsSameNode :: DLCNode x -> DLCNode x -> Bool
dlcIsSameNode x y = dlcNextRef x == dlcNextRef y

dlcIsSingleton d = do
    dn <- dlcNext d
    return $ dlcIsSameNode d dn

--  +--> d=[ <*> _ <*> ]
--  +---------+<----+
dlcSingleton v = do
    rec { d <-  return (DLCNode v rp rn)
        ; rp <- newOrdRef d
        ; rn <- newOrdRef d
        }
    return d

--  d=[ <*> _ <*> ]   [ <d> vdn <dnn> ]=dn
--             +---------^
--      =>
--         di=[ <*> v <*> ]
--              /       \
--  d=[ <*> _ <*> ]   [ <d> vdn <dnn> ]=dn
dlcAppend d v = do
    dn <- dlcNext d

    dip <- newOrdRef d
    din <- newOrdRef dn
    let di = DLCNode v dip din
    writeOrdRef (dlcNextRef d ) di
    writeOrdRef (dlcPrevRef dn) di
    return di

--  d1=[ <d1p> _ <*> ]  ...  [ <dnp> vd1n <d1> ]=d1p
--  d2=[ <d2p> _ <*> ]  ...  [ <dxp> vd2n <d2> ]=d2p
--              +---- ... ----^
--      =>
--  d1=[ <D2p> _ <*> ]  ...  [ <dnp> vd1n <D2> ]=d1p
--  d2=[ <D1p> _ <*> ]  ...  [ <dxp> vd2n <D1> ]=d2p
--              +---- ... ----^
dlcMerge d1 d2 = do
  d1p <- dlcPrev d1
  d2p <- dlcPrev d2
  writeOrdRef (dlcNextRef d1p) d2
  writeOrdRef (dlcNextRef d2p) d1
  writeOrdRef (dlcPrevRef d1 ) d2p
  writeOrdRef (dlcPrevRef d2 ) d1p

-- Wrapper around dlcIsSingleton, which verifies that eliminating
-- bitcasts still results in a singleton occurrence.
freeOccIsSingleton :: Pretty t => FreeOcc t -> Compiled Bool
freeOccIsSingleton fo = do
  estimate <- dlcIsSingleton fo
  if estimate
    then do bv   <- freeBinder fo
            occs <- collectOccurrences bv
            return $ length occs == 1
    else do return False

binderIsDead (MKBound _ r) = do mbfo <- readOrdRef r
                                return $ isNothing mbfo

binderIsSingletonOrDead (MKBound _ r) = do mbfo <- readOrdRef r
                                           case mbfo of
                                             Nothing -> return True
                                             Just fo -> freeOccIsSingleton fo

dlcToList (MKBound _ r) = do
    mbfo <- readOrdRef r
    case mbfo of
      Nothing -> return []
      Just fo -> let go occs occ =
                        if occ `dlcIsSameNode` fo
                          then return (occ:occs)
                          else dlcNext occ >>= go (occ:occs) in
                 dlcNext fo >>= go []

dlcCount d1 = dlcToList d1 >>= return . length

mkbCount d1 = collectOccurrences d1 >>= return . length

type Link   val    = OrdRef (Maybe val)
type Subterm ty    = Link (MKTerm ty)
type Subexpr ty    = Link (MKExpr ty)
type Known  ty val = (MKBoundVar ty, val)

type ContVar ty = FreeVar ty

type MKBoundVar t = MKBound t

-- We want a doubly-linked mutable tree structure.
-- Since subterms are themselves links, it seems like
-- we can embed self-links directly... but we can't.
--
-- Consider: initially we have code like
--
--    MKLetCont c { formal => body(formal) }
--    in MKCont c   actual
--
-- which has mutable links for tree structure:
--
--    MKLetCont c linkCF
--    in linkCC
--                with  
--                      linkCF ---> { formal => linkCB }
--                      linkCB ---> body(formal)
--                      linkCC ---> MKCont c actual
--
-- Since c has one occurrence, we can do a shrinking beta-reduction
-- without needing to copy the body of the continuation function.
-- So beta reduction will first substitute 'actual' for 'formal',
-- then update linkCC to point to body(formal->actual).
-- So we'll have
--
--    MKLetCont c linkCF
--    in linkCC
--                with  
--                      linkCF ---> { formal => linkCB }
--                      linkCB ---> body(actual)
--                      linkCC -----^
--
-- This is the subtly broken bit with direct self-reference:
--  if 'body' directly embeds 'linkCB' as its self-link value, then
-- even though the program now accesses it via 'linkCC'.
-- Thus an attempt to subtitute 'new' for 'body' results in
--
--                      linkCB ---> new
--                      linkCC ---> body(actual)
--
-- And since the program knows about linkCC and not the now-dead linkCB,
-- the upshot is the appearance of phantom lost inlinings.
--
-- A similar problem occurs with no embedded self-link; the worklist
-- can process linkCB after linkCC, producing a lost update.
--
-- The solution is (I think?) hinted at by Kennedy: we must use
-- the parent link in the to-be-replaced term to harvest a selection
-- of "active" subterm links, from which we can select the relevant one.
-- So in the example, when we look at body(actual), perhaps via linkCB,
-- we'll examine the uplink, which points to the MKLetCont; from there,
-- we'll harvest linkCF and linkCC. We can do simple identity comparisons
-- of the uplinks in the linked terms. Thus from linkCB we update linkCC.

getActiveLinkFor :: MKTerm ty -> Compiled (Subterm ty)
getActiveLinkFor term = do
  let isLinkToOurTerm link = do
        mb_term' <- readOrdRef link
        case mb_term' of
          Nothing -> return False
          Just term' -> return $ parentLinkT term' == parentLinkT term

  parent <- readLink "linkFor" (parentLinkT term)
  case parent of
    ParentFn fn -> do
      good <- isLinkToOurTerm (mkfnBody fn)
      if good
        then return $ mkfnBody fn
        else error $ "linkFor: body of parent fn wasn't equal to our term!"
    ParentTerm p -> do
      siblings <- subtermsOf p
      goods <- mapM isLinkToOurTerm siblings
      case [sib | (True, sib) <- zip goods siblings] of
        [] -> error "linkFor didn't find our candidate among the siblings"
        [x] -> return x
        _ -> error $ "linkFor found multiple candidates among the siblings!"

subtermsOf :: MKTerm t -> Compiled [Subterm t]
subtermsOf term =
    case term of
      MKIf          _u _ _ tru fls -> return $ [tru, fls]
      MKLetVal      _u   _      k  -> return $ [k]
      MKLetRec      _u   knowns k  -> return $ k : (map snd knowns)
      MKLetFuns     _u   knowns k  -> do fns <- knownActuals knowns
                                         return $ k : map mkfnBody fns
      MKLetCont     _u   knowns k  -> do fns <- knownActuals knowns
                                         return $ k : map mkfnBody fns
      MKCase        _u _ _v arms   -> do return $ map mkcaseArmBody arms
      MKCont {} -> return []
      MKCall {} -> return []

type Uplink ty = Link (Parent ty)
data Parent ty = ParentTerm (MKTerm ty)
               | ParentFn  (MKFn (Subterm ty) ty)

-- Bindable values/expressions; distinct from MKTerm to separate program structure from computations.
data MKExpr ty =
          MKKillProcess (Uplink ty) ty T.Text
        | MKLiteral     (Uplink ty) ty Literal
        | MKTuple       (Uplink ty) ty [FreeVar ty] SourceRange
        | MKAppCtor     (Uplink ty) ty (CtorId, CtorRepr) [FreeVar ty]
        | MKCallPrim    (Uplink ty) ty (FosterPrim ty)    [FreeVar ty] SourceRange
        -- Mutable ref cells
        | MKAlloc       (Uplink ty) ty (FreeVar ty) AllocMemRegion
        | MKDeref       (Uplink ty) ty (FreeVar ty)
        | MKStore       (Uplink ty) ty (FreeVar ty) (FreeVar ty)
        -- Array operations
        | MKAllocArray  (Uplink ty) ty (FreeVar ty) AllocMemRegion ZeroInit
        | MKArrayRead   (Uplink ty) ty (ArrayIndex (FreeVar ty))
        | MKArrayPoke   (Uplink ty) ty (ArrayIndex (FreeVar ty)) (FreeVar ty)
        | MKArrayLit    (Uplink ty) ty (FreeVar ty) [Either Literal (FreeVar ty)]
        -- Others
        | MKCompiles    (Uplink ty) KNCompilesResult ty (Subterm ty)
        | MKTyApp       (Uplink ty) ty (FreeVar ty) [ty]

-- Terms are lists of bindings ending in control flow (if/case/call/cont).
data MKTerm ty =
        -- Creation of bindings
          MKLetVal      (Uplink ty) (Known ty   (Subexpr ty)) (Subterm ty)
        | MKLetRec      (Uplink ty) [Known ty   (Subterm ty)] (Subterm ty)
        | MKLetFuns     (Uplink ty) [Known ty (Link (MKFn (Subterm ty) ty))] (Subterm ty)
        | MKLetCont     (Uplink ty) [Known ty (Link (MKFn (Subterm ty) ty))] (Subterm ty)

        -- Control flow
        | MKCase        (Uplink ty) ty (FreeVar ty) [MKCaseArm (Subterm ty) ty]
        | MKIf          (Uplink ty) ty (FreeVar ty) (Subterm ty) (Subterm ty)
        | MKCall        (Uplink ty) ty (FreeVar ty)       [FreeVar ty] (ContVar ty)
        | MKCont        (Uplink ty) ty (ContVar ty)       [FreeVar ty]

-- Does double duty, representing both regular functions and continuations.
data MKFn expr ty
                = MKFn { mkfnVar   :: (MKBoundVar ty)
                       , mkfnVars  :: [MKBoundVar ty]
                       , mkfnCont  :: Maybe (MKBoundVar ty) -- return continuation for actual functions.
                       , mkfnBody  :: expr
                       , mkfnIsRec :: RecStatus
                       ,_mkfnAnnot :: ExprAnnot
                       } deriving Show -- For KNExpr and KSmallstep

data MKCaseArm expr ty = MKCaseArm { _mkcaseArmPattern  :: PatternRepr ty
                                   ,  mkcaseArmBody     :: expr
                                   , _mkcaseArmBindings :: [MKBoundVar ty]
                                   , _mkcaseArmRange    :: SourceRange
                                   }

type WithBinders ty = StateT (Map Ident (MKBoundVar ty)) Compiled

-- With the given binding map, process the given terms,
-- constructing a final term using the builder ``f``.
-- In the course of processing, each subterm gets an empty uplink.
-- Finally, backpatch the result rv into the subterms' uplinks.

mkBackpatch' :: (CanMakeFun ty, Pretty ty) =>
                [KNExpr' RecStatus ty]
             -> ContinuationContext ty
             -> ([Subterm ty] -> WithBinders ty (MKTerm ty))
             -> WithBinders ty (MKTerm ty)
mkBackpatch' es k f = do
  ms <- mapM (\e -> mkOfKN_Base e k) es
  rv <- f ms
  lift $ backpatchT rv ms

-- For each subexpr, install the given term as the parent.
backpatchE :: MKTerm ty -> [Subexpr ty] -> Compiled ()
backpatchE parent subexprs = mapM_ (\subexpr -> do
    mkexpr <- readLink "backpatchE" subexpr
    mapM_ (\fv -> setFreeLink fv parent) (freeVarsE mkexpr)
    writeOrdRef (parentLinkE mkexpr) (Just (ParentTerm parent))) subexprs

-- For each subterm, install the given term as the parent.
backpatchT :: MKTerm ty -> [Subterm ty] -> Compiled (MKTerm ty)
backpatchT parent subterms = do
    mapM_ (\subterm -> do
      mkterm <- readLink "backpatch" subterm
      writeOrdRef (parentLinkT mkterm) (Just (ParentTerm parent))) subterms
    return parent

readLink :: String -> Link val -> Compiled val
readLink msg subterm = do mb_rv <- readOrdRef subterm
                          case mb_rv of
                            Just rv -> return rv
                            Nothing -> error $ "MKNExpr.hs:readLink: " ++ msg

findBinder :: Ident -> Map Ident (MKBoundVar ty) -> (MKBoundVar ty)
findBinder id m =
    case Map.lookup id m of
        Just binder -> binder
        Nothing -> error $ "MKNExpr.hs: findBinder had nothing for " ++ show id
                      ++ "\n; m = " ++ show [(k, tidIdent (boundVar v)) | (k,v) <- Map.toList m]

mkFreeOcc :: TypedId ty -> WithBinders ty (FreeVar ty)
mkFreeOcc tid = do
    m <- get
    let xid = tidIdent tid
    let binder = findBinder ({-trace ("mkFreeOcc looking up " ++ show xid)-} xid) m
    lift $ mkFreeOccForBinder binder

mkFreeOccForBinder :: MKBoundVar t -> Compiled (FreeOcc t)
mkFreeOccForBinder binder@(MKBound _ r) = do
    pt <- liftIO $ fresh binder
    uplink <- newOrdRef Nothing
    let fop = FOP pt uplink
    mb_fo <- readOrdRef r
    case mb_fo of
      Nothing -> do
        fo <- dlcSingleton fop
        writeOrdRef r (Just fo)
        return fo
      Just fo@(DLCNode fop' _ _) -> do
        liftIO $ union pt (fopPoint fop') -- use the existing binder as representative
        dlcAppend fo fop

mkBinder :: TypedId ty -> WithBinders ty (MKBoundVar ty)
mkBinder tid = do
  ref <- lift $ newOrdRef Nothing
  let binder = MKBound tid ref
  !m <- get
  put $ extend m [tidIdent tid] [binder]
  return binder

extend :: Map Ident thing -> [Ident] -> [thing]
       -> (Map Ident thing)
extend m ids binders = let ins m (xid,binder) = Map.insert xid binder m in
                      List.foldl' ins m (zip ids binders)


mkKnownE :: MKBoundVar ty -> Subexpr ty -> Known ty (Subexpr ty)
mkKnownE bound thing = (bound, thing)

mkKnownT :: MKBoundVar ty -> Subterm ty -> Known ty (Subterm ty)
mkKnownT bound thing = (bound, thing)


-- The link for regular terms is the self link of the term;
-- functions get a separate link, since they have no self link.
mkKnown' :: MKBoundVar ty -> MKFn (Subterm ty) ty
         -> Compiled (Known ty (Link (MKFn (Subterm ty) ty)))
mkKnown' bound fn = do
    linkref <- newOrdRef (Just fn)
    return (bound, linkref)

backpatchFn :: MKFn (Subterm ty) ty -> Compiled ()
backpatchFn f@(MKFn {}) = do
  mk <- readLink "backpatchFn" (mkfnBody f)
  writeOrdRef (parentLinkT mk) (Just (ParentFn f))

mkOfKNFn :: (CanMakeFun ty, Pretty ty) =>
            Fn RecStatus (KNExpr' RecStatus ty) ty
         -> WithBinders ty (MKFn (Subterm ty) ty)
         
mkOfKNFn (Fn v vs expr isrec annot) = do
    m <- get
    v' <- mkBinder v
    vs' <- mapM mkBinder vs
    
    jb  <- genBinder ".fret" (tidType v)

    expr' <- mkOfKN_Base expr (CC_Tail jb)
    put m
    let f' = MKFn v' vs' (Just jb) expr' isrec annot
    lift $ backpatchFn f'
    return f'

data ContinuationContext ty =
      CC_Tail (MKBoundVar ty)
    | CC_Base ((FreeVar ty -> WithBinders ty (Subterm ty)), ty)

contApply :: ContinuationContext ty -> FreeVar ty
          -> WithBinders ty (Subterm ty)
contApply (CC_Tail jb) v' = do
        cv <- lift $ mkFreeOccForBinder jb
        parentLink2 <- lift $ newOrdRef Nothing
        let tm = MKCont parentLink2 (tidType $ boundVar jb)  cv [v']
        selfLink2   <- lift $ newOrdRef $ Just tm
        lift $ setFreeLink v' tm
        lift $ setFreeLink cv tm
        
        return selfLink2
contApply (CC_Base (fn, _)) v' = fn v'

mkOfKNMod kn mainBinder = do
  lift $ whenDumpIR "mono-structure" $ do
    dbgDoc $ pretty kn
    dbgDoc $ showStructure kn
  mkOfKN_Base kn (CC_Tail mainBinder)

mkOfKN_Base :: (CanMakeFun ty, Pretty ty) =>
               KNExpr' RecStatus ty ->
               ContinuationContext ty ->
                WithBinders ty (Subterm ty)
mkOfKN_Base expr k = do
  let qv = mkFreeOcc
  let qvs = mapM qv
  let qarm _k (CaseArm _pat _body (Just _) _binds _rng) = error $ "MKNExpr.hs cannot yet deal with pattern guards"
      qarm qk (CaseArm pat body Nothing binds rng) = do
            m <- get
            binds' <- mapM mkBinder binds
            body' <- mkOfKN_Base body qk
            put m
            return $ MKCaseArm pat body' binds' rng

  let
   gor expr = case expr of
    KNVar v  -> do v' <- qv v
                   contApply k v'

    KNInlined _t0 _to _tn _old new -> gor new
    KNNotInlined _ expr            -> gor expr

                   -- We're done; no further backpatching needed.
    nonvar -> do
      parentLink <- lift $ newOrdRef Nothing
      let nu = parentLink

      -- Note: should only be called once per go since it captures nu.
      let --genMKLetVal :: String -> ty -> (LinkE ty -> WithBinders ty (MKExpr ty))
          --            -> WithBinders ty (MKTerm ty)
          genMKLetVal name ty gen = do
            (xb, xo) <- genBinderAndOcc name ty
            (selfLink2, _exp) <- withLinkE gen
            subterm <- contApply k xo
            let rv = MKLetVal nu (mkKnownE xb selfLink2) subterm
            lift $ backpatchE rv [selfLink2]
            lift $ backpatchT rv [subterm]

      nvres <- case nonvar of
        KNLetVal      x e1 e2 | Just (_, gen) <- isExprNotTerm e1 -> do
            xb <- mkBinder (TypedId (typeKN e1) x) -- versus genBinderAndOcc
            (selfLink2, _exp) <- withLinkE gen
            subterm <- mkOfKN_Base e2 k
            let rv = MKLetVal nu (mkKnownE xb selfLink2) subterm
            lift $ backpatchE rv [selfLink2]
            lift $ backpatchT rv [subterm]
        
        KNLetVal      x e1 e2 -> do
            -- The 'let val' case from CwCC figure 8.
            -- Generate the continuation variable 'j'.
            jb  <- genBinder ".cont" (mkFunType [typeKN e1] (typeKN e2))
            jbx <- genBinder ".cntx" (mkFunType [typeKN e1] (typeKN e2))
            
            -- Generate the continuation's bound parameter, 'x'
            xb <- mkBinder $ TypedId (typeKN e1) x

            -- letcont j x = [[e2]] k   in    ((e1)) j
            body <- mkOfKN_Base e2 k

            let contfn = MKFn jbx [xb] Nothing body NotRec (annotForRange $ MissingSourceRange "cont")
            known <- lift $ mkKnown' jb contfn
            lift $ backpatchFn contfn

            rest' <- mkOfKN_Base e1 (CC_Tail jb)

            let rv = MKLetCont nu [known] rest'
            lift $ backpatchT rv [rest']

        KNCompiles (KNCompilesResult r) ty _expr -> do 
            genMKLetVal ".cpi" ty $ \nu' -> do
                b <- liftIO $ readIORef r
                return $ MKLiteral nu' ty (LitBool b)
        
        KNIf      ty v e1 e2 -> do
            mkBackpatch' [e1, e2] k (\[m1,m2] -> do
                v' <- qv v
                return $ MKIf nu ty v' m1 m2)
        
        KNCase    ty v arms  -> do
            v' <- qv v
            case k of
                CC_Tail {} -> do
                  arms' <- mapM (qarm k) arms
                  let rv = MKCase        nu ty v' arms'
                  lift $ backpatchT rv (map mkcaseArmBody arms')

                CC_Base kf -> do
                  -- The topmost 'case' case from CwCC figure 8,
                  --    (though we skip the conts/bindings for the pattern vars).
                  genContinuation ".caco" ".cacx" ty kf nu $ \nu' jb -> do
                      arms' <- mapM (qarm (CC_Tail jb)) arms
                      return $ MKCase nu' ty v' arms'

        KNCall       ty v vs -> do
            (v':vs') <- qvs (v:vs)
            case k of
                CC_Tail jb -> do
                  kv <- lift $ mkFreeOccForBinder jb
                  return $ MKCall nu  ty v' vs' kv

                CC_Base kf -> do
                  genContinuation ".clco" ".clcx" ty kf nu $ \nu' jb -> do
                      kv <- lift $ mkFreeOccForBinder jb
                      return $ MKCall nu'  ty v' vs' kv

        KNLetRec  xs es rest -> do 
            let vs = map (\(x,e) -> (TypedId (typeKN e) x)) (zip xs es)
            m1 <- get
            dbgDoc $ text "m1: " <> pretty (Map.toList m1)
            xs' <- mapM mkBinder vs
            m2 <- get
            dbgDoc $ text "m2: " <> pretty (Map.toList m2)
            --put $ extend m (map tidIdent vs) xs'
            -- TODO reconsider k
            ts <- mapM (\e -> mkOfKN_Base e k) es
            t  <- mkOfKN_Base rest k
            put m1
            let knowns = map (uncurry mkKnownT) (zip xs' ts)
            let rv = MKLetRec      nu knowns t
            lift $ backpatchT rv (t:ts)

        KNLetFuns ids fns st -> do
            let vs = map (\(x,fn) -> (TypedId (fnType fn) x)) (zip ids fns)
            m <- get
            binders <- mapM mkBinder vs
            fs'   <- mapM mkOfKNFn fns
            rest' <- mkOfKN_Base st k
            knowns <- lift $ mapM (uncurry mkKnown') (zip binders fs')
            put m
            lift $ backpatchT (MKLetFuns nu knowns rest') [rest']

        e | Just (bindName, gen) <- isExprNotTerm e -> do
            genMKLetVal bindName (typeKN e) gen
      
      -- Insert final backpatches etc.
      lift $ do selfLink <- newOrdRef Nothing
                installLinks selfLink nvres

  gor expr


isExprNotTerm expr = do
  let qv = mkFreeOcc
  let qvs = mapM qv
  let qa (ArrayIndex v1 v2 x y) = qvs [v1, v2] >>= \[v1', v2'] -> return (ArrayIndex v1' v2' x y)
  let qelt (Left lit) = return (Left lit)
      qelt (Right v)  = liftM  Right (qv v)
  case expr of
    KNLiteral   ty   lit -> Just $ (,) ".lit" $ \nu' -> return $ MKLiteral nu' ty lit
    KNTuple     ty vs sr -> Just $ (,) ".tup" $ \nu' -> do
                                  vs' <- mapM qv vs
                                  return $ MKTuple nu' ty vs' sr
    KNKillProcess   ty t -> Just $ (,) ".kil" $ \nu' -> return $ MKKillProcess nu' ty t
    KNCallPrim r ty p vs -> Just $ (,) ".cpr" $  \nu' -> do
                                  vs' <- qvs vs
                                  return $ MKCallPrim nu' ty p vs' r
    KNAppCtor    ty c vs -> Just $ (,) ".app" $ \nu' -> do
                                  vs' <- qvs vs
                                  return $ MKAppCtor nu' ty c vs'
    KNAlloc      ty v mr -> Just $ (,) ".alo" $  \nu' -> do
                                  v' <- qv  v 
                                  return $ MKAlloc   nu' ty v' mr
    KNDeref      ty v    -> Just $ (,) ".get" $  \nu' -> do
                                  v' <- qv  v
                                  return $ MKDeref   nu' ty v'
    KNStore      ty v v2 -> Just $ (,) ".sto" $  \nu' -> do
                                  [v', v2'] <- qvs [v,v2]
                                  return $ MKStore   nu' ty v' v2'
    KNAllocArray ty v m z-> Just $ (,) ".ala" $  \nu' -> do
                                  v' <- qv  v
                                  return $ MKAllocArray  nu' ty v' m z
    KNArrayRead  ty a    -> Just $ (,) ".ari" $  \nu' -> do
                                  a' <- qa  a
                                  return $ MKArrayRead   nu' ty a'
    KNArrayPoke  ty a v  -> Just $ (,) ".arp" $ \nu' -> do
                                  v' <- qv v
                                  a' <- qa a
                                  return $ MKArrayPoke   nu' ty a' v'
    KNArrayLit   ty v elts -> Just $ (,) ".arr" $ \nu' -> do
                                  v' <- qv v
                                  elts' <- mapM qelt elts
                                  return $ MKArrayLit nu' ty v' elts'
    KNTyApp  ty v argtys   -> Just $ (,) ".tya" $ \nu' -> do
                                   v' <- qv  v 
                                   return $ MKTyApp    nu' ty v' argtys
    _ -> Nothing

withLinkT :: (Uplink ty -> StateT s Compiled (MKTerm ty))
          -> StateT s Compiled (Subterm ty, MKTerm ty)
withLinkT gen = do
  parentLink2 <- lift $ newOrdRef Nothing
  thing <- gen parentLink2
  selfLink2 <- lift $ newOrdRef (Just thing)
  return (selfLink2, thing)

withLinkE :: (Uplink ty -> StateT s Compiled (MKExpr ty))
          -> StateT s Compiled (Subexpr ty, MKExpr ty)
withLinkE gen = do
  parentLink2 <- lift $ newOrdRef Nothing
  thing <- gen parentLink2
  selfLink2 <- lift $ newOrdRef (Just thing)
  return (selfLink2, thing)

genBinder :: String -> ty -> WithBinders ty (MKBoundVar ty)
genBinder name ty = do
  xid <- lift $ ccFreshId $ T.pack name
  let xv = TypedId ty xid
  mkBinder xv

genBinderAndOcc :: String -> ty -> WithBinders ty (MKBoundVar ty, FreeVar ty)
genBinderAndOcc name ty = do
  xb <- genBinder name ty
  xo <- mkFreeOcc (boundVar xb)
  return (xb, xo)

installLinks :: Subterm ty -> MKTerm ty -> Compiled (Subterm ty)
installLinks selfLink term = do
    writeOrdRef selfLink (Just term)
    -- Free-occurrence links for MKExprs are install by backpatchE.
    mapM_ (\fv -> setFreeLink fv term) (directFreeVarsT term)
    return selfLink

genContinuation contName contBindName ty_x (kf, resTy) nu restgen = do
    -- Generate the continuation variable 'j'.
    jb  <- genBinder contName (mkFunType [ty_x] resTy)
    jbx <- genBinder contName (mkFunType [ty_x] resTy)

    -- letcont j x = kf(x) in [[restgen]] j
    (xb, xo) <- genBinderAndOcc contBindName ty_x
    
    body <- kf xo

    let contfn = MKFn jbx [xb] Nothing body NotRec (annotForRange $ MissingSourceRange "cont")
    known <- lift $ mkKnown' jb contfn
    lift $ backpatchFn contfn

    (rest', _) <- withLinkT $ \nu' -> restgen nu' jb
    
    let rv = MKLetCont nu [known] rest'
    lift $ backpatchT rv [rest']

parentLinkE :: MKExpr ty -> Uplink ty
parentLinkE expr =
  case expr of
    MKLiteral     u       _t _it -> u
    MKTuple       u     _t _s _r -> u
    MKKillProcess u     _ty _t    -> u
    MKCallPrim    u     _ty _ _s _ -> u
    MKAppCtor     u     _ty _ _s -> u
    MKAlloc       u     _ty _  _ -> u
    MKDeref       u     _ty _    -> u
    MKStore       u     _ty _ _2 -> u
    MKAllocArray  u     _ty _ _ _ -> u
    MKArrayRead   u     _ty _a    -> u
    MKArrayPoke   u     _ty _a _  -> u
    MKArrayLit    u _ty _v _elts  -> u
    MKCompiles    u _res _ty _body -> u
    MKTyApp       u _ty _ _arg_tys -> u

parentLinkT :: MKTerm ty -> Uplink ty
parentLinkT expr =
  case expr of
    MKLetVal      u   _known  _k -> u
    MKLetRec      u   _knowns _k -> u
    MKLetFuns     u   _knowns _k -> u
    MKLetCont     u   _knowns _k -> u
    MKCase        u  _ty _ _arms  -> u
    MKIf          u  _ty _ _e1 _e2 -> u
    MKCall        u     _ty _ _s _   -> u
    MKCont        u     _ty _ _s     -> u


freeVarsE :: MKExpr ty -> [FreeOcc ty]
freeVarsE expr =
  case expr of
    MKLiteral     {} -> []
    MKTuple       _     _t vs _r -> vs
    MKKillProcess {} -> []
    MKCallPrim    _     _ty _ vs _ -> vs
    MKAppCtor     _     _ty _ vs -> vs
    MKAlloc       _     _ty v  _ -> [v]
    MKDeref       _     _ty v    -> [v]
    MKStore       _     _ty v1 v2 -> [v1,v2]
    MKAllocArray  _     _ty v _ _ -> [v]
    MKArrayRead   _     _ty ari    ->     freeVarsA ari
    MKArrayPoke   _     _ty ari v  -> v : freeVarsA ari
    MKArrayLit    _ _ty v elts  -> v : [x | Right x <- elts]
    MKCompiles    {} -> []
    MKTyApp       _ _ty v _arg_tys -> [v]

freeVarsA (ArrayIndex v1 v2 _ _) = [v1, v2]

directFreeVarsT :: MKTerm ty -> [FreeOcc ty]
directFreeVarsT expr =
  case expr of
    -- Note: we don't collect free variables from linked subterms!
    -- Ideally this function would collect occurrences from the subexpr
    -- of MKLetVal, but for now it must be done by the caller to preserve purity.
    MKLetVal      {} -> []
    MKLetRec      {} -> []
    MKLetFuns     {} -> []
    MKLetCont     {} -> []
    MKCase        _  _ty v _arms     -> [v]
    MKIf          _  _ty v _e1 _e2   -> [v]
    MKCall        _     _ty v vs c   -> c:v:vs
    MKCont        _     _ty c vs     -> c  :vs

data MaybeCont ty = YesCont (MKBoundVar ty)
                  | NoCont
                  deriving (Eq)

mbContOf Nothing = NoCont
mbContOf (Just c) = YesCont c

knOfMKFn mb_retCont (MKFn v vs mb_cont expr isrec annot) = do
      let qb (MKBound tid _) = tid
      expr' <- do let rc = case --trace ("picking new continuation for " ++ show (pretty v) ++ "from: " ++ show (pretty (mb_retCont, mb_cont))) $
                                 (mb_retCont, mb_cont) of 
                            (YesCont retCont, Nothing) -> YesCont retCont
                            (NoCont, Nothing) -> NoCont --error $ "knOfMKFn has no return continuation!"
                            (_,      Just rc) -> YesCont rc
                  readLink "knOfMKFn" expr >>= knOfMK rc
      return $ Fn (qb v) (map qb vs) expr' isrec annot

knOfMKExpr :: Pretty t =>
              MaybeCont t -> MKExpr t -> Compiled (KNExpr' RecStatus t)
knOfMKExpr mb_retCont expr = do
  let q  subterm = readLink "knOfMK" subterm >>= knOfMK mb_retCont

  let qv (DLCNode fop _ _) = do bound <- liftIO $ repr (fopPoint fop) >>= descriptor
                                return $ boundVar bound
  let qa (ArrayIndex v1 v2 x y) = mapM qv [v1, v2] >>= \[v1', v2'] -> return (ArrayIndex v1' v2' x y)
  let qelt (Left lit) = return (Left lit)
      qelt (Right v)  = liftM Right (qv v)

  case expr of
    MKLiteral     _ ty lit -> return $ KNLiteral ty lit
    MKTuple       _ ty vars sr -> do vars' <- mapM qv vars
                                     return $ KNTuple ty vars' sr
    MKKillProcess _ ty txt     -> return $ KNKillProcess ty txt
    MKCallPrim    _ ty p vs r -> do vs' <- mapM qv vs
                                    return $ KNCallPrim r ty p vs'
    MKAppCtor     _ ty cid vs -> do vs' <- mapM qv vs
                                    return $ KNAppCtor ty cid vs'
    MKAlloc       _ ty v amr  -> do v' <- qv v
                                    return $ KNAlloc ty v' amr
    MKDeref       _ ty v      -> qv v >>= \v' -> return $ KNDeref ty v'
    MKStore       _ ty v v2   -> mapM qv [v, v2] >>= \[v',v2'] -> return $ KNStore ty v' v2'
    MKAllocArray  _ ty v amr zi -> qv v >>= \v' -> return $ KNAllocArray ty v' amr zi
    MKArrayRead   _ ty ari    -> qa ari >>= \ari' -> return $ KNArrayRead ty ari'
    MKArrayPoke   _ ty ari v  -> qa ari >>= \ari' ->
                                 qv v   >>= \v' -> return $ KNArrayPoke ty ari' v'
    MKArrayLit    _ ty v elts -> qv v   >>= \v' ->
                                 mapM qelt elts >>= \elts' -> return $ KNArrayLit ty v' elts'
    MKCompiles    _ res ty body -> q body >>= \body' -> return $ KNCompiles res ty body'
    MKTyApp       _ ty v arg_tys -> qv v >>= \v' -> return $ KNTyApp ty v' arg_tys

knOfMK :: Pretty t =>
          MaybeCont t -> MKTerm t -> Compiled (KNExpr' RecStatus t)
knOfMK mb_retCont term0 = do
  let q  subterm = readLink "knOfMK" subterm >>= knOfMK mb_retCont
  let qv :: FreeOcc ty -> Compiled (TypedId ty)
      qv (DLCNode fop _ _) = do bound <- liftIO $ repr (fopPoint fop) >>= descriptor
                                return $ boundVar bound
  let qk :: (val -> Compiled res) -> Known ty (OrdRef (Maybe val)) -> Compiled (Ident, Maybe res)
      qk f (x,br) = do b <- readOrdRef br
                       b' <- liftMaybe f b
                       return (tidIdent (boundVar x), b')
  let qks f knowns = do vals <- mapM (qk f) knowns
                        return $ unzip [(x,b) | (x, Just b) <- vals]

  let qarm (MKCaseArm pat body binds rng) = do
        let binds' = map boundVar binds
        body' <- q body
        --mb_guard' <- liftMaybe q mb_guard
        return $ CaseArm pat body' Nothing binds' rng
  let qf = knOfMKFn mb_retCont

  case term0 of
    MKIf          _u  ty v e1 e2  -> do e1' <- q e1
                                        e2' <- q e2
                                        v'  <- qv v
                                        return $ KNIf ty v' e1' e2'
    MKCase        _u  ty v arms   -> do arms' <- mapM qarm arms
                                        v' <- qv v
                                        return $ KNCase         ty v' arms'
    MKLetVal      _u   known  k   -> do (x', mb) <- qk (knOfMKExpr mb_retCont) known
                                        k' <- q k
                                        case mb of
                                          Nothing -> return k'
                                          Just b' -> return $ KNLetVal x' b' k'
    MKLetRec      _u   knowns  k  -> do (xs', es')  <- qks (knOfMK mb_retCont) knowns
                                        k'  <- q k
                                        return $ mkKNLetRec xs' es' k'
    MKLetFuns     _u   knowns  k  -> do (xs', fns') <- qks qf knowns
                                        k'  <- q k
                                        return $ mkKNLetFuns  xs' fns' k'

    MKCall        _u  ty v vs _c   -> do
      (v':vs') <- mapM qv (v:vs)
      cvb <- freeBinder _c
      if --trace ("MKCall comparing " ++ (show $ pretty cvb) ++ " vs " ++ (show $ pretty mb_retCont)) $
            YesCont cvb == mb_retCont || isMainFnVar v'
        then return $ KNCall       ty v' vs'
        else do xid <- ccFreshId $ T.pack ".ctmp"
                return $ KNLetVal xid (KNCall ty v' vs')
                          (KNCall (tidType $ boundVar cvb) (boundVar cvb) [TypedId ty xid])
      
    -- TODO if we can match   letcont j x = ... in MKCall v vs j
    --      and j has no other uses,
    --      emit KNLetVar x = KNCall v vs
    MKLetCont     _u  knowns k -> do (xs', fns') <- qks qf knowns
                                     k'  <- q k
                                     return $ mkKNLetFuns  xs' fns' k'
    
    MKCont        _u ty contvar vs -> do
          vs' <- mapM qv vs
          cvb <- freeBinder contvar
          -- If contvar is the return continuation, with one argument, we don't want a call.
          let isReturn = YesCont cvb == mb_retCont
          case --trace ("MKCont comparing " ++ (show $ pretty cvb) ++ " vs " ++ (show $ pretty mb_retCont)) $
                 vs' of
            [v] | isReturn -> return $ KNVar v
            _ -> return $ KNCall ty (boundVar cvb) vs'

mkKNLetRec [] [] k = k
mkKNLetRec xs es k = KNLetRec xs es k

mkKNLetFuns [] [] k = k
mkKNLetFuns xs es k = KNLetFuns xs es k


isMainFnVar v =
  case tidIdent v of
      GlobalSymbol t -> t == T.pack "main"
      _ -> False

isMainFn fo = do
  b <- freeBinder fo
  return $ isMainFnVar (boundVar b)

isTextPrim (GlobalSymbol t) = t `elem` [T.pack "TextFragment", T.pack "TextConcat"]
isTextPrim _ = False

-- We detect and kill dead bindings for functions here as well.
-- TODO we ought to collect a single unified worklist of subterms
--      (including redexes and bindings) which we can iterate over
--      and add to as appropriate during processing.
-- For example, to remove a dead function binding we must also
-- collect and kill the free variable occurrences mentioned within the
-- body, which may in turn trigger further dead-binding elimination.
collectRedexes :: (Pretty t)
               => IORef (WorklistQ (Subterm t))
               -> IORef (Map (MKBoundVar t) (Link (MKTerm t)))
               -> IORef (Map (MKBoundVar t) (Link (MKExpr t)))
               -> IORef (Map (MKBoundVar t) (Link (MKFn (Subterm t) t)))
               -> IORef (Map (MKBoundVar t) (Link (MKTerm t)))
               -> IORef (Map (MKBoundVar t) (MKBoundVar t))
               -> Subterm t -> Compiled ()
collectRedexes ref valbindsref expbindsref funbindsref fundefsref aliasesref sbtm = go sbtm
 where
   go subterm = do
    mb_term <- readOrdRef subterm
    case mb_term of
      Nothing -> return ()
      Just term -> do
        let markRedex = liftIO $ modIORef' ref (\w -> worklistAdd w subterm)
        case term of
          MKCall _ _ fo _ _ -> whenNotM (isMainFn fo) markRedex
          MKCont {}         -> markRedex
          _ -> markAndFindSubtermsOf term >>= mapM_ go
          where markAndFindSubtermsOf term =
                    case term of
                      MKIf          _u _ _ tru fls -> return [tru, fls]

                      MKLetVal      _u  (x, br) k  -> do markExpBind (x, br)
                                                         return [k]
                      MKLetRec      _u   knowns k  -> do mapM_ markValBind knowns
                                                         return $ k : (map snd knowns)
                      MKLetFuns     _u   knowns k  -> do liftIO $ modIORef' ref (\w -> worklistAdd w subterm) -- markRedex
                                                         mapM_ (markFunBind subterm) knowns
                                                         fns <- knownActuals knowns
                                                         return $ k : map mkfnBody fns
                      MKLetCont     _u   knowns k  -> do mapM_ markCntBind knowns
                                                         fns <- knownActuals knowns
                                                         return $ k : map mkfnBody fns
                      MKCase        _u _ _v arms -> return $ map mkcaseArmBody arms
                      _ -> return []

   markValBind (x,tm) = liftIO $ modIORef' valbindsref (\m -> Map.insert x tm m)
   markCntBind (x,fn) = liftIO $ modIORef' funbindsref (\m -> Map.insert x fn m)
   markExpBind (x,exlink) = do
                        liftIO $ modIORef' expbindsref (\m -> Map.insert x exlink m)
                    
                        ex <- readLink "collectRedex.E" exlink
                        case ex of
                          MKTyApp _u _ty fv [] -> do
                            -- record alias...
                            bv <- freeBinder fv
                            liftIO $ modIORef' aliasesref (\m -> Map.insert x bv m)
                          _ -> return ()

   markFunBind subterm (x,fn) = do
            mb_mkfn <- readOrdRef fn
            case mb_mkfn of
              Nothing -> return ()
              Just mkfn -> do
                        xc <- dlcCount x
                        bc <- mkbCount x
                        fc <- dlcCount (mkfnVar mkfn)
                        dbgDoc $ text $ "markFnBind: x  = (" ++ show xc ++ " vs " ++ show bc ++ ") " ++ show (tidIdent $ boundVar x)                
                        dbgDoc $ text $ "            fv = (" ++ show fc ++ ") " ++ show (tidIdent $ boundVar (mkfnVar mkfn))
                        if xc == 0 && not (isTextPrim (tidIdent $ boundVar x))
                          then do
                            -- dbgDoc $ text $ "killing dead fn binding " ++ show (tidIdent $ boundVar x)
                            writeOrdRef fn Nothing
                          else do
                            liftIO $ modIORef' funbindsref (\m -> Map.insert x fn m)
                            liftIO $ modIORef' fundefsref  (\m -> Map.insert x subterm m)

knownActuals :: [Known ty (Link val)] -> Compiled [val]
knownActuals knowns = do
    mb_vals <- mapM (readOrdRef . snd) knowns
    return $ catMaybes mb_vals

-- {{{
shouldNotInlineFn fn =
  let id = tidIdent (boundVar (mkfnVar fn)) in
  (T.pack "noinline_" `T.isInfixOf` identPrefix id
   && not (T.pack "." `T.isInfixOf` identPrefix id))


data RedexSituation t =
       CallOfUnknownFunction
     | CallOfSingletonFunction (MKFn (Subterm t) t)
     | CallOfDonatableFunction (MKFn (Subterm t) t)
     | SomethingElse           (MKFn (Subterm t) t)

classifyRedex :: (Pretty t)
              => FreeOcc t -> [FreeOcc t]
              -> Map (MKBoundVar t) (Link (MKFn (Subterm t) t))
              -> Map (MKBoundVar t) (MKBoundVar t)
              -> Compiled (RedexSituation t)
classifyRedex callee args knownFns aliases = do
  bv <- freeBinder callee
  let bv' = case Map.lookup bv aliases of
              Nothing -> bv
              Just z  -> z
  mb_fn <- lookupBinding' bv' knownFns
  classifyRedex' bv' mb_fn args knownFns

classifyRedex' _ Nothing _ _ =
  return CallOfUnknownFunction

classifyRedex' fnbinder (Just fn) args knownFns = do
  callee_singleton <- binderIsSingletonOrDead fnbinder
  {-
  count <- mkbCount binder
  dbgDoc $ text $ "is callee singleton? " ++ show (pretty binder) ++
                      " -> " ++ show callee_singleton ++ " count: " ++ show count ++
                      " ; rec? " ++ show (mkfnIsRec fn) -}

  case (callee_singleton, mkfnIsRec fn) of
    _ | shouldNotInlineFn fn
                   -> return $ CallOfUnknownFunction
    (True, NotRec) -> return $ CallOfSingletonFunction fn
    _ -> do
      donationss <- mapM (\(arg, binder) -> do
                         argsingle <- freeOccIsSingleton arg
                         argboundfn <- lookupBinding arg knownFns
                         bindoccs <- collectOccurrences binder
                         -- Check how many times the binder occurs,
                         -- excluding recursive calls.
                         bindNonRecOccCounts <- mapM (\occ -> do
                            Just tm <- readOrdRef (freeLink occ)
                            case tm of
                              MKCall _ _ v _ _ -> do
                                vb <- freeBinder v
                                return (if vb == fnbinder || vb == mkfnVar fn then 0 else (1 :: Int))
                              _ -> return 1) bindoccs
                         let bindsingle = sum bindNonRecOccCounts <= 1

                         if argsingle && isJust argboundfn && bindsingle
                           then return [(arg, binder)]
                           else return []
                         ) (zip args (mkfnVars fn))
      let donations = concat donationss
      if null donations
        then return $ SomethingElse fn
        else return $ CallOfDonatableFunction fn
-- }}}

-- {{{
type MKRenamed t = WithBinders t

runCopyMKFn :: (Pretty t, Show t, AlphaRenamish t RecStatus)
            => MKFn (Subterm t) t -> Map Ident (MKBoundVar t)
            -> Compiled (MKFn (Subterm t) t)
runCopyMKFn mkfn bindings = evalStateT (copyMKFn mkfn) bindings

copyBinder :: String -> MKBoundVar t -> MKRenamed t (MKBoundVar t)
copyBinder msg b = do
  newid <- lift $ ccRefresh (tidIdent $ boundVar b)
  -- Like mkBinder, but we record the old id in the map instead of the new one.
  ref <- lift $ newOrdRef Nothing
  let binder = MKBound (TypedId (tidType $ boundVar b) newid) ref
  !m <- get
  put $ extend m [tidIdent $ boundVar b] [binder]
  dbgDoc $ text $ "copied binder " ++ show (prettyIdent $ tidIdent $ boundVar b) ++ " (" ++ msg ++ ") into " ++ show newid
  return binder
 where
    ccRefresh :: Ident -> Compiled Ident
    ccRefresh (Ident t _) = do
        u <- ccUniq
        return $ Ident t u
    ccRefresh (GlobalSymbol t) = do
        u <- ccUniq
        return $ GlobalSymbol $ t `T.append` T.pack (show u)

copyFreeOcc :: FreeVar t -> WithBinders t (FreeVar t)
copyFreeOcc fv = do
  -- Because copyBinder indexes binders by old idents,
  -- using mkFreeOcc implicitly grabs the new binder...
  -- except that since we only need to copy some functions
  -- (that is, we don't copy those which can't be inlined or contified)
  -- our binder map will be incomplete. Any binder which isn't in the map
  -- should be passed through unmodified.
  b <- lift $ freeBinder fv
  m <- get
  case Map.lookup (tidIdent $ boundVar b) m of
    Just binder -> lift $ mkFreeOccForBinder binder
    Nothing     -> lift $ mkFreeOccForBinder b

copyMKFn :: (Pretty t, Show t, AlphaRenamish t RecStatus)
         => MKFn (Subterm t) t
         -> MKRenamed t (MKFn (Subterm t) t)
copyMKFn fn = do
  v'  <-       copyBinder "mkFnVar"   (mkfnVar fn)
  vs' <- mapM (copyBinder "mkFnVars") (mkfnVars fn)
  cont' <- case mkfnCont fn of
             Nothing -> return Nothing
             Just cf ->
               if cf == mkfnVar fn
                 then return $ Just v'
                 else copyBinder "mkFnCont" cf >>= return . Just
  body <- lift $ readOrdRef (mkfnBody fn)
  link' <- case body of
                Just term -> copyMKTerm term
                Nothing   -> return (mkfnBody fn)
  let fn' = fn { mkfnVar = v' , mkfnVars = vs' , mkfnBody = link' , mkfnCont = cont' }
  lift $ backpatchFn fn'
  return fn'

-- Returns a Subexpr with an empty parent link.
copyMKExpr :: (Pretty t, Show t, AlphaRenamish t RecStatus)
           => MKExpr t -> MKRenamed t (Subexpr t, MKExpr t)
copyMKExpr expr = do
  let qv = copyFreeOcc
  let qa (ArrayIndex v1 v2 x y) =
        mapM qv [v1, v2] >>= \[v1', v2'] -> return (ArrayIndex v1' v2' x y)
  let qelt (Left lit) = return (Left lit)
      qelt (Right v)  = liftM  Right (qv v)
  case expr of
    MKLiteral     _ ty lit -> withLinkE $ \u -> return $ MKLiteral u ty lit
    MKTuple       _ ty vars sr -> do vars' <- mapM qv vars
                                     withLinkE $ \u -> return $ MKTuple u ty vars' sr
    MKKillProcess _ ty txt     -> withLinkE $ \u -> return $ MKKillProcess u ty txt
    --MKVar         _          _   -> u
    MKCallPrim    _ ty p vs r -> do vs' <- mapM qv vs
                                    withLinkE $ \u -> return $ MKCallPrim u   ty p  vs' r
    MKAppCtor     _ ty cid vs -> do vs' <- mapM qv vs
                                    withLinkE $ \u -> return $ MKAppCtor u ty cid vs'
    MKAlloc       _ ty v amr  -> do v' <- qv v
                                    withLinkE $ \u -> return $ MKAlloc u ty v' amr
    MKDeref       _ ty v      -> qv v >>= \v' ->
                                    withLinkE $ \u -> return $ MKDeref u ty v'
    MKStore       _ ty v v2   -> mapM qv [v, v2] >>= \[v',v2'] ->
                                    withLinkE $ \u -> return $ MKStore u ty v' v2'
    MKAllocArray  _ ty v amr zi -> qv v >>= \v' ->
                                    withLinkE $ \u -> return $ MKAllocArray u ty v' amr zi
    MKArrayRead   _ ty ari    -> qa ari >>= \ari' ->
                                    withLinkE $ \u -> return $ MKArrayRead u ty ari'
    MKArrayPoke   _ ty ari v  -> qa ari >>= \ari' ->
                                 qv v   >>= \v' ->
                                    withLinkE $ \u -> return $ MKArrayPoke u ty ari' v'
    MKArrayLit    _ ty v elts -> qv v   >>= \v' ->
                                 mapM qelt elts >>= \elts' ->
                                    withLinkE $ \u -> return $ MKArrayLit u ty v' elts'
    MKCompiles    _ res ty body -> do body' <- lift $ readLink "copyMKExpr.Compiles" body
                                      copyMKTerm body' >>= \subterm' ->
                                        withLinkE $ \u -> return $ MKCompiles u res ty subterm'
    MKTyApp       _ ty v arg_tys -> qv v >>= \v' ->
                                     withLinkE $ \u -> return $ MKTyApp u ty v' arg_tys

copyMKTerm :: (Pretty t, Show t, AlphaRenamish t RecStatus)
           => MKTerm t -> MKRenamed t (Subterm t)
copyMKTerm term = do
  let q subterm = do tm <- lift $ readLink "copyMKTerm" subterm
                     copyMKTerm tm
  let --qe :: Subexpr t -> MKRenamed (Subexpr t)
      qe subexpr = do mb_se <- lift $ readOrdRef subexpr
                      case mb_se of
                        Just se -> do se' <- copyMKExpr se
                                      return $ fst se'
                        Nothing -> error $ "copyMKTerm 1169"
  let --qf :: Link (MKFn (Subterm ty) ty) -> MKRenamed (Link (MKFn (Subterm ty) ty))
      qf link = do
          mb_fn <- lift $ readOrdRef link
          case mb_fn of
            Just fn -> do fn' <- copyMKFn fn
                          lift $ newOrdRef (Just fn')
            Nothing -> return link
  let qv = copyFreeOcc

  let qpat (PR_Ctor sr ty pats ctor) = do pats' <- mapM qpat pats
                                          return $ PR_Ctor sr ty pats' ctor
      qpat (PR_Or   sr ty pats     ) = do pats' <- mapM qpat pats
                                          return $ PR_Or   sr ty pats'
      qpat (PR_Tuple sr ty pats    ) = do pats' <- mapM qpat pats
                                          return $ PR_Tuple sr ty pats'
      qpat (PR_Atom (P_Variable sr tid)) = do
            m <- get
            case Map.lookup (tidIdent tid) m of
              Just binder -> return $ PR_Atom (P_Variable sr (boundVar binder))
              Nothing     -> return $ PR_Atom (P_Variable sr tid)
      qpat (PR_Atom atom) = return $ PR_Atom atom
  let qarm (MKCaseArm pat body binds rng) = do
        binds' <- mapM (copyBinder "qarm") binds
        body' <- q body
        --mb_guard' <- liftMaybe q mb_guard
        pat' <- qpat pat
        return $ MKCaseArm pat' body' binds' rng

  let -- qk :: (Link val -> MKRenamed ty (Link res)) -> Known ty (Link val)
      --   -> MKRenamed ty (MKBound (TypedId ty), Link res)
      qk f (boundvar, link) = do
                       bv' <- copyBinder "qk" boundvar
                       link' <- f link
                       return (bv', link')

  -- TODO maybe have withLinkT use subtermsOf ?
  (link, newterm) <- case term of
    MKLetVal      _u   known  k   -> do x' <- qk qe known
                                        k' <- q k
                                        withLinkT $ \u -> lift $ do
                                          let rv = MKLetVal u x' k'
                                          backpatchE rv [snd x']
                                          backpatchT rv [k']
    MKLetRec      _u   knowns  k  -> do knowns' <- mapM (qk q) knowns
                                        k'  <- q k
                                        withLinkT $ \u -> lift $ do
                                          let rv = MKLetRec u knowns' k'
                                          backpatchT rv [k']
    MKLetFuns     _u   knowns  k  -> do knowns' <- mapM (qk qf) knowns
                                        k'  <- q k
                                        withLinkT $ \u -> lift $ do
                                          let rv = MKLetFuns u knowns' k'
                                          backpatchT rv [k']
    MKLetCont     _u   knowns  k  -> do knowns' <- mapM (qk qf) knowns
                                        k'  <- q k
                                        withLinkT $ \u -> lift $ do
                                          let rv = MKLetCont u knowns' k'
                                          backpatchT rv [k']
    MKIf          _u  ty v e1 e2  -> do e1' <- q e1
                                        e2' <- q e2
                                        v'  <- qv v
                                        withLinkT $ \u -> lift $ do
                                          let rv = MKIf u ty v' e1' e2'
                                          backpatchT rv [e1', e2']
    MKCase        _u  ty v arms   -> do arms' <- mapM qarm arms
                                        v' <- qv v
                                        withLinkT $ \u -> lift $ do
                                          let rv = MKCase u ty v' arms'
                                          backpatchT rv (map mkcaseArmBody arms')
    MKCall        _u  ty v vs _c   -> do mapM qv (v:vs) >>= \(v':vs') ->
                                          qv  _c        >>= \c'  ->
                                           withLinkT $ \u -> lift $ return $ MKCall u       ty v' vs' c' 
    MKCont        _u  ty _c vs     -> do mapM qv    vs  >>= \    vs' ->
                                          qv  _c        >>= \c'  ->
                                           withLinkT $ \u -> return $ MKCont u       ty c' vs'
  lift $ installLinks link newterm


mknShrink :: (Pretty t, Show t, AlphaRenamish t RecStatus)
          => Subterm t -> MKBoundVar t -> WithBinders t (KNExpr' RecStatus t)
mknShrink subterm mainCont = do
  term <- lift $ readLink "mknShrink" subterm
  kn1 <- lift $ knOfMK (YesCont mainCont) term  
  dbgDoc $ text $ "mknShrink, term is " ++ show (pretty kn1)
  return kn1

mknInline :: Subterm MonoType -> MKBoundVar MonoType -> Maybe Int -> Compiled ()
mknInline subterm mainCont mb_gas = do
    wr <- liftIO $ newIORef worklistEmpty
    kr <- liftIO $ newIORef Map.empty
    er <- liftIO $ newIORef Map.empty
    fr <- liftIO $ newIORef Map.empty
    fd <- liftIO $ newIORef Map.empty
    ar <- liftIO $ newIORef Map.empty
    --term <- readLink "mknInline" subterm
    collectRedexes wr kr er fr fd ar subterm

    _knownVals <- liftIO $ readIORef kr

    do w0 <- liftIO $ readIORef wr
       k0 <- liftIO $ readIORef kr
       e0 <- liftIO $ readIORef er
       f0 <- liftIO $ readIORef fr
       dbgDoc $ text $ "collected " ++ show (length (worklistToList w0)) ++ " redexes..."
       dbgDoc $ text $ "collected " ++ show (length (Map.toList k0)) ++ " valbinds..."
       dbgDoc $ text $ "collected " ++ show (length (Map.toList e0)) ++ " expbinds..."
       dbgDoc $ text $ "collected " ++ show (length (Map.toList f0)) ++ " funbinds..."

    let worklistGet' = do
          w0 <- liftIO $ readIORef wr
          case worklistGet w0 of
            Nothing -> return Nothing
            Just (subterm, w) -> do
              liftIO $ writeIORef wr w
              mb_redex <- readOrdRef subterm
              case mb_redex of
                Nothing -> worklistGet'
                Just mredex -> do
                  parent <- readOrdRef (parentLinkT mredex)
                  return $ Just (subterm, mredex, parent)
              {-
              parent <- readOrdRef (parentLinkT mredex)
              mb_altself <- readOrdRef (selfLinkT mredex)
              case mb_altself of
                Nothing ->
                  error $ "item in worklist had null self-link...?"
                Just altself ->
                  if selfLinkT altself /= selfLinkT mredex
                    then
                      error $ "altself not the same as mredex?!?"
                    else
                      return $ Just (mredex, parent)
                      -}

    let go 0 = dbgDoc $ text "... ran outta gas"

        go gas = do
           mb_mredex_parent <- worklistGet'
           case mb_mredex_parent of
             Nothing -> dbgDoc $ text "... ran outta work"
             Just (_subterm, mredex, Nothing) -> do
                case mredex of
                  MKLetFuns _u [(bv,_)] _ | tidIdent (boundVar bv) == GlobalSymbol (T.pack "TextFragment") ->
                    return () -- The top-most function binding will be parentless; don't print about it though.
                  _ -> do
                    do redex <- knOfMK (YesCont mainCont) mredex
                       dbgDoc $ red (text "skipping parentless redex: ") <+> pretty redex
                  
                go gas
             Just (subterm, mredex, Just _parent) -> case mredex of
               MKCall _up _ty callee args kv -> do
                 knownFns   <- liftIO $ readIORef fr
                 aliases    <- liftIO $ readIORef ar
                 situation <- classifyRedex callee args knownFns aliases
                 case situation of
                   CallOfUnknownFunction -> do
                     do redex <- knOfMK NoCont mredex
                        dbgDoc $ text "CallOfUnknownFunction: " <+> pretty redex
                     return ()
                   CallOfSingletonFunction fn -> do
                     do redex <- knOfMK (mbContOf $ mkfnCont fn) mredex
                        dbgDoc $ text "CallOfSingletonFunction starting with: " <+> align (pretty redex)

                     do v <- freeBinder callee
                        dbgDoc $ green (text "inlining without copying ") <> pretty (tidIdent $ boundVar v)

                     newbody <- betaReduceOnlyCall fn args kv     wr fd

                     --do nubody <- readLink "kninline-sf" newbody
                     --   newbody' <- knOfMK NoCont nubody
                     --   dbgDoc $ text "CallOfSingletonFunction generated: " <+> pretty newbody'

                     replaceWith subterm newbody
                     killBinding callee knownFns aliases
                     -- No need to collect redexes, since the body wasn't duplicated.

{-
                     case _parent of
                            ParentTerm pt -> do
                              kn <- knOfMK   (mbContOf $ mkfnCont fn) pt
                              dbgDoc $ text "CallOfSingletonFunction parent tm became: " <+> pretty kn
                            ParentFn   pf -> do
                              kn <- knOfMKFn NoCont pf
                              dbgDoc $ text "CallOfSingletonFunction parent fn became: " <+> pretty kn
-}

                   CallOfDonatableFunction fn -> do
                     do redex <- knOfMK (mbContOf $ mkfnCont fn) mredex
                        dbgDoc $ text "CallOfDonatableFunction: " <+> pretty redex
                     flags <- gets ccFlagVals
                     if getInliningDonate flags
                       then do
                         do v <- freeBinder callee
                            dbgDoc $ green (text "copying and inlining DF ") <+> pretty (tidIdent $ boundVar v)
                            --kn1 <- knOfMKFn (mbContOf $ mkfnCont fn) fn
                            --dbgDoc $ text $ "pre-copy fn is " ++ show (pretty kn1)
                            return ()
                         fn' <- runCopyMKFn fn Map.empty
                         do kn1 <- knOfMKFn (mbContOf $ mkfnCont fn) fn'
                            dbgDoc $ text $ "post-copy fn is " ++ show (pretty kn1)
                         -- TODO Recursive-but-not-tail-recursive functions (RBNTRF)
                         --      will have a recursive call in the body, so we can't
                         --      simply use betaReduceOnlyCall as theres more than 1 call.
                         --
                         --      Most functions will be given loop headers in KNExpr,
                         --      but an un-eliminated loop header within a RBNTRF
                         --      might change the allocation behavior of a program.
                         --      
                         --      If the generated fn' isn't singleton/dead, it should
                         --      be inserted next to the original fn. (TODO)

                         rbntr <- isRecursiveButNotTailRecursive fn'
                         newbody <- if rbntr then do
                           -- We don't modify the known function list, so the recursive call in
                           -- the copied body will bottom out and not do any loop unrolling.
                           
                           dbgDoc $ red $ text "isRecursiveButNotTailRecursive!"
                           -- We must disable recursive inlining or else we'd infinitely regress!
                           
                           knfn <- knOfMKFn NoCont $ fn'

                           kn' <- knLoopHeaders' (KNLetFuns [tidIdent $ fnVar knfn] [knfn] (KNVar $ fnVar knfn))
                                                 True
                           let (KNLetFuns _ [knfn'] _) = kn'
                           dbgDoc $ text $ "loop-headered fn is " ++ show (pretty knfn')

                           fn'' <- evalStateT (mkOfKNFn knfn') $
                            Map.fromList [(tidIdent $ boundVar b, b) | (b,_) <- Map.toList knownFns]

                           -- We reuse the pieces of the original MKCall because it's now dead.
                           createLetFunAndCall fn'' (mkfnVar fn'') _ty _up args kv
                           
                          else do betaReduceOnlyCall fn' args kv     wr fd
                          
                         replaceWith subterm newbody
                         -- No need to kill the old binding, since the body was duplicated.

                         collectRedexes wr kr er fr fd ar newbody

                       else return ()

                   SomethingElse _fn -> do
                     do redex <- knOfMK (mbContOf $ mkfnCont _fn) mredex
                        dbgDoc $ text "SomethingElse (inlineNorF): " <+> align (pretty redex)
                     if shouldInlineRedex mredex _fn
                       then do
                             do v <- freeBinder callee
                                dbgDoc $ green (text "copying and inlining SE ") <+> pretty (tidIdent $ boundVar v)
                                --kn1 <- knOfMK (YesCont mainCont) term
                                --dbgDoc $ text $ "knOfMK, term is " ++ show (pretty kn1)
                             fn' <- runCopyMKFn _fn Map.empty
                             newbody <- betaReduceOnlyCall fn' args kv    wr fd
                             replaceWith subterm newbody
                             killOccurrence callee
                             collectRedexes wr kr er fr fd ar newbody
                       else return ()
                 go (gas - 1)
              
               MKCont _up _ty callee args -> do
                 knownFns   <- liftIO $ readIORef fr
                 aliases    <- liftIO $ readIORef ar
                 situation <- classifyRedex callee args knownFns aliases
                 case situation of
                   CallOfUnknownFunction -> do
                     do cb <- freeBinder callee
                        if T.pack ".fret" `T.isPrefixOf` (identPrefix $ tidIdent $ boundVar cb) 
                          then return ()
                          else do redex <- knOfMK (YesCont mainCont) mredex
                                  dbgDoc $ red (text "CallOfUnknownCont: ") <+> pretty redex
                     return ()

                   CallOfSingletonFunction fn -> do
                     do redex <- knOfMK (mbContOf $ mkfnCont fn) mredex
                        dbgDoc $ text "CallOfSingletonCont: " <+> pretty redex
                    
                        mapM_ (\arg -> do b <- freeBinder arg
                                          c <- mkbCount b
                                          dbgDoc $ text "      pre-beta occ count: " <> pretty c) args
                                          {-
      fob <- freeBinder fo
      fo_c <- mkbCount fob
      fx_c <- mkbCount b
      dbgDoc $ text "substituting var " <> pretty (boundVar b) <> text " for " <> pretty (boundVar fob)
      dbgDoc $ text "    occ lengths " <> pretty fx_c <> text " and " <> pretty fo_c

      fo_c <- mkbCount fob
      fx_c <- mkbCount b
      fa <- freeBinder fox
      dbgDoc $ text "    afteward, lengths " <> pretty fx_c <> text " and " <> pretty fo_c <> text "; fox -> " <> pretty (boundVar fa)
      -}

                     do v <- freeBinder callee
                        dbgDoc $ green (text "      beta reducing (inlining) singleton cont ") <> pretty (tidIdent $ boundVar v)

                     newbody <- betaReduceOnlyCall fn args callee         wr fd
                     
                    --  do newbody' <- knOfMK (mbContOf $ mkfnCont fn) newbody
                    --     dbgDoc $ text "CallOfSingletonCont: new: " <+> pretty newbody'

                     mapM_ (\arg -> do b <- freeBinder arg
                                       c <- mkbCount b
                                       dbgDoc $ text "      pre-kill occ count: " <> pretty c) args

                     replaceWith subterm newbody
                     killBinding callee knownFns aliases

                     mapM_ (\arg -> do b <- freeBinder arg
                                       c <- mkbCount b
                                       dbgDoc $ text "      post-kill occ count: " <> pretty c) args


                   CallOfDonatableFunction fn -> do
                     do redex <- knOfMK (mbContOf $ mkfnCont fn) mredex
                        dbgDoc $ text "CallOfDonatableCont: " <+> pretty redex
                     return ()
                     {-
                     flags <- gets ccFlagVals
                     if getInliningDonate flags
                       then do
                         fn' <- runCopyMKFn fn
                         newbody <- do mk <- betaReduceOnlyCall fn' args kv   wr fd
                                       readLink "CallOfDonatableC" mk
                         replaceWith mredex newbody
                         killOccurrence callee
                         collectRedexes wr kr er fr fd ar newbody
                       else return ()
-}
                   SomethingElse _fn -> do
                     do redex <- knOfMK (mbContOf $ mkfnCont _fn) mredex
                        dbgDoc $ text "SomethingElseC: " <+> pretty redex
                     if shouldInlineRedex mredex _fn
                       then do
                             dbgDoc $ text "skipping inlining continuation redex...?"
                             {-
                             fn' <- runCopyMKFn _fn
                             newbody <- betaReduceOnlyCall fn' args kv   wr fd  >>= readLink "CallOfDonatable"
                             replaceWith mredex newbody
                             killOccurrence callee
                             collectRedexes wr kr er fr fd ar newbody
                             -}
                             return ()
                       else return ()
                 go (gas - 1)

               MKLetFuns fnup knowns fnrest -> do
                 contifiability <- analyzeContifiability knowns
                 case contifiability of
                   GlobalsArentContifiable -> return ()
                   CantContifyWithNoFn -> do dbgDoc $ yellow (text "       can't contify with no fn...")
                                             return ()
                   NoNeedToContifySingleton -> do dbgDoc $ yellow (text "       singleton usage, no need to contify")
                                                  return ()
                   HadUnknownContinuations -> do dbgDoc $ red (text "       had one or more unknown continuations")
                                                 return ()
                   HadMultipleContinuations -> do dbgDoc $ red (text "       had too many continuations")
                                                  return ()
                   NoSupportForMultiBindingsYet -> do dbgDoc $ red (text "skipping considering " <> pretty (map (tidIdent.boundVar.fst) knowns) <> text " for contification")
                                                      return ()
                   CantContifyNestedTailCalls -> do dbgDoc $ red (text "can't contify with nested tail call...")
                                                    return ()
                   ContifyWith cont bv fn occs -> do
                      dbgDoc $ green (text "       should contify!")
                      
                      -- Replace uses of return continuation with common cont target.
                      let Just oldret = mkfnCont fn
                      -- This may result in additional functions becoming contifiable,
                      -- so we collect the uses of the old ret cont first.
                      collectRedexesUsingFnRetCont oldret   wr fd
                      substVarForVar'' cont oldret

                      -- Replacing the Call with a Cont will kill the old cont occurrences.
                      mapM_ (\occ -> do
                        mb_tm <- readOrdRef (freeLink occ)
                        case mb_tm of
                          Nothing -> error $ "asdfasdf"
                          Just tm@(MKCall uplink ty v vs _cont) -> do
                            let newterm = MKCont uplink ty v vs
                            replaceTermWith tm newterm
                            writeOrdRef (freeLink occ) (Just newterm)) occs

                      -- Replace the function with a continuation; be sure to
                      -- replace the fn's global ident with a local version!
                      contfn <- mkKnown' bv $ fn { mkfnCont = Nothing }
                      let letcont = MKLetCont fnup [contfn] fnrest
                      replaceTermWith mredex letcont

                 go (gas - 1)

               _ -> do
                 do kn <- knOfMK (YesCont mainCont) mredex
                    dbgDoc $ text $ "skipping non-call/cont redex: " ++ show (pretty kn)
                 go gas

    let gas = case mb_gas of
                Nothing -> 42000
                Just gas -> gas
    go gas

    return ()

isRecursiveButNotTailRecursive fn = do
  occs <- collectOccurrences (mkfnVar fn)
  isRecAndNotTailRec <- mapM (\occ -> do
      tm <- readLink "isRecursiveButNotTailRecursive" (freeLink occ)
      case tm of
        MKCall _ _ v _ k -> do
          vb <- freeBinder v
          kb <- freeBinder k
          return $ vb == mkfnVar fn && (Just kb) /= mkfnCont fn
        _ -> return False
    ) occs
  return $ any id isRecAndNotTailRec

-- Create a new term of the form
-- fun outerBinder <args> = <fn> in outerBinder <args>
createLetFunAndCall :: MKFn (Subterm ty) ty -> MKBoundVar ty -> ty
                    -> Link (Parent ty) -> [FreeOcc ty] -> FreeOcc ty
                    -> Compiled (Subterm ty)
createLetFunAndCall fn outerBinder ty up args kv = do
  callee <- mkFreeOccForBinder outerBinder

  up' <- newOrdRef Nothing
  
  -- We can't use args and kv directly, because replaceWith looks only at
  -- top-level occs, and these occs will be nested in the call under the letfun.
  args' <- mapM freeBinder args >>= mapM mkFreeOccForBinder
  kv'   <-      freeBinder kv   >>=      mkFreeOccForBinder

  callLink <- newOrdRef Nothing
  _ <- installLinks callLink $ MKCall up' ty callee args' kv'

  known <- mkKnown' outerBinder fn
  letfuns <- backpatchT (MKLetFuns up [known] callLink) [callLink]
  newOrdRef (Just letfuns)

collectRedexesUsingFnRetCont oldret    wr fd = do
  occs <- collectOccurrences oldret
  mb_callees <- mapM calleeOfCont occs

  fndefs <- liftIO $ readIORef fd  
  mapM_ (\calleeBV -> do
      case Map.lookup calleeBV fndefs of
        Nothing -> return ()
        Just tm -> liftIO $ modIORef' wr (\w -> worklistAdd w tm)
    ) [c | Just c <- mb_callees]

data Contifiability =
    GlobalsArentContifiable
  | NoNeedToContifySingleton
  | HadUnknownContinuations
  | HadMultipleContinuations
  | CantContifyNestedTailCalls
  | CantContifyWithNoFn
  | NoSupportForMultiBindingsYet
  | ContifyWith (MKBound MonoType)
                (MKBound MonoType)
                (MKFn (Subterm MonoType) MonoType)
                [FreeOcc MonoType]

--analyzeContifiability :: ... -> Compiled Contifiability
analyzeContifiability knowns = do
  let isTopLevel (GlobalSymbol _) = True
      isTopLevel _ = False
  if all isTopLevel $ map (tidIdent.boundVar.fst) knowns
    then return GlobalsArentContifiable
    else
      case knowns of
        [(bv, fnlink)] -> do
          dbgDoc $ blue (text "considering " <> pretty (map (tidIdent.boundVar.fst) knowns) <> text " for contification")
          mb_fn <- readOrdRef fnlink
          occs <- collectOccurrences bv
          case (occs, mb_fn) of
            (_, Nothing) -> do return CantContifyWithNoFn
            ([_], _) -> do return NoNeedToContifySingleton -- Singleton call; no need to contify since we'll just inline it...
            (_, Just fn) -> do
              mbs_conts <- mapM (contOfCall bv) occs
              case allJusts mbs_conts of
                Nothing -> return HadUnknownContinuations
                Just conts -> do
                  let (tailconts, nontailconts) = partitionEithers $
                        [if Just bv == mkfnCont fn
                          then Left bv else Right bv
                        | bv <- Set.toList $ Set.fromList conts]
                  dbgDoc $ yellow (text "       had just these conts: ")
                                        <$> text "              tail calls: " <> pretty (map (tidIdent.boundVar) tailconts)
                                        <$> text "          non-tail calls: " <> pretty (map (tidIdent.boundVar) nontailconts)
                  case (tailconts, nontailconts) of
                    ((_:_:_), _) -> return HadMultipleContinuations -- Multiple tail calls: no good!
                    (_ ,  [cont]) -> do -- Happy case: zero or one tail call, one outer continuation.
                      let isRetCont = T.pack ".fret" `T.isPrefixOf` identPrefix (tidIdent $ boundVar cont)
                      if False && isRetCont
                        then return HadMultipleContinuations
                        else return (ContifyWith cont bv fn occs)
                    _ -> return HadMultipleContinuations -- Multiple outer continuations: no good!

        _ -> do
          let bvs     = map fst knowns
              fnlinks = map snd knowns
          mb_fns <- mapM readOrdRef fnlinks
          occss <- mapM collectOccurrences bvs

          liftIO $ putDocLn $ text "recursive nest: {{{"
          mapM_ (\(occs, bv, mb_fn) -> do
            case occs of [_] -> liftIO $ putDocLn $ text "   (is  singleton)"
                         _   -> liftIO $ putDocLn $ text "   (not singleton)"
            liftIO $ putDocLn $ text "   occ:"
            mapM_ (\occ -> do
              mb_tm <- readOrdRef (freeLink occ)
              case mb_tm of
                Nothing -> do
                  liftIO $ putDocLn $ text "      no term"
                Just tm -> do
                  do kn <- knOfMK NoCont tm
                     liftIO $ putDocLn $ text "      " <> pretty kn) occs


            case mb_fn of
              Nothing -> do
                liftIO $ putDocLn $ text "    no fn"
              Just fn -> do
                aconts <- mapM (contOfCall bv) occs
                case allJusts aconts of
                  Nothing -> liftIO $ putDocLn $ text "  (some continuations not found)"
                  Just conts -> do
                             liftIO $ putDocLn $ text "  (all continuations found)"
                             let (tailconts, nontailconts) = partitionEithers $
                                                    [if Just bv == mkfnCont fn
                                                      then Left bv else Right bv
                                                    | bv <- Set.toList $ Set.fromList conts]
                             liftIO $ putDocLn $ yellow (text "       had just these conts: ")
                                                  <$> text "              tail calls: " <> pretty (map (tidIdent.boundVar) tailconts)
                                                  <$> text "          non-tail calls: " <> pretty (map (tidIdent.boundVar) nontailconts)
            ) (zip3 occss bvs mb_fns){-
          case (occs, mb_fn) of
            (_, Nothing) -> do return CantContifyWithNoFn
            ([_], _) -> do return NoNeedToContifySingleton -- Singleton call; no need to contify since we'll just inline it...
            (_, Just fn) -> do
             -}

          liftIO $ putDocLn $ text "}}}"
          return $ NoSupportForMultiBindingsYet

-- Collect the list of occurrences for the given binder,
-- but "peek through" any bitcasts.
collectOccurrences bv = do
  inits <- dlcToList bv
  initss <- mapM (\fv -> do
                mb_tm <- readOrdRef (freeLink fv)
                case mb_tm of
                  Just (MKLetVal _ (_v, exprlink) _tmlink) -> do
                    expr <- readLink "collectOccurrences" exprlink
                    case expr of
                      MKTyApp _ _ty fv' _tys -> do
                        bv' <- freeBinder fv'
                        if bv' == bv
                          then do
                            return [fv]
                          else do
                            -- Note: this can't be an infinite loop because
                            -- we are looking under letval and not letrec,
                            -- and also because we filter on v.
                            collectOccurrences bv'
                      _ -> return [fv]
                  _ -> return [fv]
    ) inits
  return $ concat initss

allJusts [] = Just []
allJusts (Nothing : _) = Nothing
allJusts (Just x:xs) = 
  case allJusts xs of
    Nothing -> Nothing
    Just res -> Just (x:res)

-- Collect the continuations associated with every use of the function binding.
contOfCall bv occ = do
  mb_tm <- readOrdRef (freeLink occ)
  case mb_tm of
    Nothing -> do
        do dbgDoc $ red $ text "free link w/ no term for" <> pretty bv
        return Nothing
    Just tm@(MKCall _ _ty v _vs cont) -> do
        vb <- freeBinder v
        if vb == bv
          then -- It's a call to the function being considered
            do cv <- freeBinder cont
               return $ Just cv
          else -- It's a call to some other function, our function is one of its args.
                -- We could possibly contify if we knew whether the callee will only
                -- tail call our function, but as of yet we don't track that information.
            do do kn <- knOfMK NoCont tm
                  dbgDoc $ text "call w/ unknown cont for" <> pretty bv <> text ":" <> indent 10 (pretty kn)
                  return Nothing
                  
    Just tm -> do
      do kn <- knOfMK NoCont tm
         dbgDoc $ text "non call w/ unknown cont for" <> pretty bv <> text ":" <> indent 10 (pretty kn)
      return Nothing

-- Collect the function vars associated with every use of a continuation variable.
calleeOfCont occ = do
  bv <- freeBinder occ
  mb_tm <- readOrdRef (freeLink occ)
  case mb_tm of
    Nothing -> do
        do dbgDoc $ red $ text "free link w/ no term for cont " <> pretty bv
        return Nothing

    Just (MKCall _ _ty v _vs _cont) -> do
        bv <- freeBinder v
        return $ Just bv
                  
    Just tm -> do
      do kn <- knOfMK NoCont tm
         dbgDoc $ text "calleeOfCont: non call for" <> pretty bv <> text ":" <> indent 10 (pretty kn)
      return Nothing

shouldInlineRedex _mredex _fn =
  -- TODO use per-call-site annotation, when we have such things.
  {-
  let id = tidIdent (boundVar (mkfnVar _fn)) in
  T.pack "doinline_" `T.isInfixOf` identPrefix id
  -}
  False

replaceWith :: Pretty ty => Subterm ty -> Subterm ty -> Compiled ()
replaceWith poss_indir_target newsubterm = do
  oldterm <- readLink "replaceWith" poss_indir_target
  newterm <- readLink "replaceWith" newsubterm
  replaceTermWith oldterm newterm
  writeOrdRef poss_indir_target     (Just newterm)

replaceTermWith :: Pretty ty => MKTerm ty -> MKTerm ty -> Compiled ()
replaceTermWith oldterm newterm = do
  target <- getActiveLinkFor oldterm

  writeOrdRef target            (Just newterm)

  let oldoccs = directFreeVarsT oldterm
  let newoccs = directFreeVarsT newterm
  mapM_ killOccurrence (oldoccs `butnot` newoccs)
  mapM_ (\fv -> setFreeLink fv newterm) newoccs
  readOrdRef (parentLinkT oldterm) >>= writeOrdRef (parentLinkT newterm)

killOccurrence :: Pretty ty => FreeVar ty -> Compiled ()
killOccurrence fo = do
    MKBound _v r <- freeBinder fo -- r :: OrdRef (Maybe (FreeOcc tyx))

    isSingleton <- freeOccIsSingleton fo
    if isSingleton
     then do
       dbgDoc $ red (text "killing singleton binding ") <> prettyId _v
       writeOrdRef r Nothing
     else do
       n <- dlcNext fo
       p <- dlcPrev fo
       writeOrdRef (dlcNextRef p) n
       writeOrdRef (dlcPrevRef n) p

    -- Make sure binder doesn't point to fo
    mb_fo' <- readOrdRef r
    case mb_fo' of
      Just fo' | dlcIsSameNode fo fo' -> do
        if isSingleton
          then writeOrdRef r Nothing
          else do fo'' <- dlcNext fo
                  writeOrdRef r $ Just fo''
      _ -> return ()

killBinding fo knownFns aliases = do
    origBinding <- freeBinder fo
    let binding@(MKBound v r') =
            case Map.lookup origBinding aliases of
                    Nothing -> origBinding
                    Just bv -> bv
    dbgDoc $ red (text "killing binding for ") <> pretty (boundVar origBinding) <> text " ~~> " <> pretty v
    writeOrdRef r' Nothing
    case Map.lookup binding knownFns of
        Nothing -> do dbgDoc $ red (text "no killable binding for ") <> pretty v
                      return ()
        Just r  -> writeOrdRef r Nothing

lookupBinding fo m = do
    binding <- freeBinder fo
    lookupBinding' binding m

lookupBinding' binding m = do
    case Map.lookup binding m of
      Nothing   -> return Nothing
      Just link -> readOrdRef link

betaReduceOnlyCall fn args kv    wr fd = do
    mapM_ substVarForBound (zip args (mkfnVars fn))
    kvb1 <- freeBinder kv

    case mkfnCont fn of
      Nothing -> return ()
      Just oldret -> do
        collectRedexesUsingFnRetCont oldret   wr fd
        -- This may result in additional functions becoming contifiable,
        -- so we collect the uses of the old ret cont first.
        substVarForBound (kv, oldret)

    kvb2 <- freeBinder kv
    dbgDoc $ text $ "      betaReduceOnlyCall on " ++ show (pretty (mkfnVar fn))
    if kvb1 /= kvb2
      then do
        dbgDoc $ text "       kv before: " <> pretty kvb1
        dbgDoc $ text "       kv after: " <> pretty kvb2
      else return ()
    dbgDoc $ text "      fn kv: " <> pretty (mkfnCont fn)
    return $ mkfnBody fn

-- TODO: ok this seems to work, more or less.
--          Implement contification & other optimizations...




baFresh :: String -> BlockAccum BlockId
baFresh s = do u <- freshLabel ; return (s, u)

baNewUniq :: BlockAccum Uniq
baNewUniq = do (uref, _, _) <- get ; mutIORef uref (+1)
  where
    mutIORef ref f = liftIO $ modIORef' ref f >> readIORef ref

type BlockAccum = StateT (IORef Uniq, Map Ident BlockId, [BasicBlock]) Compiled

baPutBlock :: Insn C O -> [Insn O O] -> CFLast -> BlockAccum ()
baPutBlock head middles last = do
  (u, m, blocks) <- get
  put (u, m, (blockJoin head (blockFromList $ List.reverse middles) (ILast last)):blocks)

instance UniqueMonad BlockAccum where freshUnique = baNewUniq >>= return . intToUnique

type PCCFns = StateT ([CFFn], [ToplevelBinding MonoType]) Compiled

pccOfTopTerm :: IORef Uniq -> Subterm MonoType -> Compiled PreCloConv
pccOfTopTerm uref subterm = do
  execStateT (go subterm) ([], []) >>= return . PreCloConv
    where
      grabFn :: Known MonoType (Link (MKFn (Subterm MonoType) MonoType)) -> PCCFns ()
      grabFn (x, link) = do
        mb_fn <- lift $ readOrdRef link
        case mb_fn of
          Nothing -> do
            dbgDoc $ text "pccOfTopTerm saw nulled-out function link " <> pretty x
            return ()
          Just fn -> do
            knfn <- lift $ knOfMKFn NoCont fn
            dbgDoc $ indent 10 (pretty x)
            dbgDoc $ indent 20 (pretty knfn)
            dbgDoc $ text "~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~"
            
            cffn <- lift $ cffnOfMKFn uref fn
            !(fns, topbinds) <- get
            put (cffn : fns, topbinds)

      go :: Subterm MonoType -> PCCFns ()
      go subterm = do
        term <- lift $ readLink "pccOfTopTerm(subterm)" subterm
        case term of
          -- Call cffnOfMKFn for each top-level function binding.
          MKLetVal   _u (bv, subexpr) k -> do
            expr <- lift $ readLink "pccTopTerm" subexpr
            handleTopLevelBinding (tidIdent $ boundVar bv) expr k
          MKLetRec      {} -> do error $ "MKLetRec in pccTopTerm"
          MKLetFuns     _u   knowns  k  -> do mapM_ grabFn knowns ; go k
          MKCall        {}              -> return ()
          MKLetCont     {} -> do error $ "MKLetCont in pccTopTerm"
          MKCont        {} -> do error $ "MKCont in pccTopTerm"

      handleTopLevelBinding id expr k = do
        case expr of
          MKLiteral    {} -> go k
          MKAllocArray {} -> go k

          MKArrayLit _ ty _fv litsOrVars -> do
            let lits = [lit | Left lit <- litsOrVars]
            if length lits == length litsOrVars
              then do !(fns, topbinds) <- get
                      put (fns, TopBindArray id ty lits : topbinds)
                      go k
              else error $ "Top-level arrays can only contain literals, not variables, for now..."
          _ -> error $ "MKLetVal in pccTopTerm"

blockIdOf :: MKBoundVar MonoType -> BlockAccum BlockId
blockIdOf bv = blockIdOfIdent (tidIdent $ boundVar bv)

blockIdOfIdent id = do
  (u, m, blocks) <- get
  case Map.lookup id m of
    Nothing -> do
      blockid <- baFresh (T.unpack $ identPrefix id)
      put (u, Map.insert id blockid m, blocks)
      return blockid
    Just b  -> return b

blockIdOf' :: FreeOcc MonoType -> BlockAccum BlockId
blockIdOf' fv = do binder <- lift $ freeBinder fv
                   blockIdOf binder

qv :: MonadIO m => FreeOcc ty -> m (TypedId ty)
qv (DLCNode fop _ _) = do bound <- liftIO $ repr (fopPoint fop) >>= descriptor
                          return $ boundVar bound

cffnOfMKCont :: MKBoundVar MonoType -> MKFn (Subterm MonoType) MonoType -> BlockAccum ()
cffnOfMKCont cv (MKFn _ vs _ subterm _isrec _annot) = do
  headerBlockId <- blockIdOf cv
  let head = ILabel (headerBlockId, map boundVar vs)

  -- Walk the term;
  --    accumulate a block body of [Insn O O]
  --    and finish it when reaching a terminator MKTerm,
  --    producing a BasicBlock, which we keep a list of statefully.
  go subterm head []
    where
      go :: Subterm MonoType -> Insn C O -> [Insn O O] -> BlockAccum ()
      go subterm head insns = do
        term <- lift $ readLink "cffnOfMKCont/0" subterm
        case term of
          MKLetVal      _u (bv, subexpr) k -> do
              letable <- lift $ letableOfSubexpr subexpr
              isDead  <- lift $ binderIsDead bv
              if isDead && isPure letable
                then go k head insns
                else go k head (ILetVal (tidIdent $ boundVar bv) letable : insns)
          MKLetRec      _u  [_known] _k -> do error $ "MKNExpr.hs: no support yet for MKLetRec..."
          MKLetRec      _u  _knowns  _k -> do error $ "MKNExpr.hs: no support yet for multi-extended-letrec"
          MKLetFuns     _u   knowns  k  -> do (uref, _, _) <- get
                                              idsfnss <- lift $ mapM (\(bv,link) -> do
                                                  mb_mkfn <- readOrdRef link
                                                  case mb_mkfn of
                                                    Nothing -> do
                                                      dbgDoc $ text $ "cffnOfMKCont removed dead fn: " ++ show (tidIdent $ boundVar bv)
                                                      return []
                                                    Just mkfn -> do
                                                      cffn <- cffnOfMKFn uref mkfn
                                                      return [(tidIdent (boundVar bv), cffn)] ) knowns
                                              let (ids, fns) = unzip (concat idsfnss)
                                              if null fns   -- avoid empty ILetFuns
                                                then go k head insns
                                                else go k head (ILetFuns ids fns : insns)
          MKLetCont     _u  knowns k   -> do -- Generate new blocks for each continuation,
                                             -- if it hasn't been removed by shrinking,
                                             mapM_ (\(bv, link) -> do
                                                mb_contfn <- lift $ readOrdRef link
                                                case mb_contfn of
                                                   Nothing -> do
                                                     dbgDoc $ text $ "cffnOfMKCont removed dead continuation " ++ show (tidIdent $ boundVar bv)
                                                   Just contfn -> do
                                                     cffnOfMKCont bv contfn)
                                               knowns
                                             -- then resume building this particular block.
                                             go k head insns

          MKCall        _u ty v vs contvar -> do
                                 blockid <- blockIdOf' contvar
                                 (v' : vs') <- mapM qv (v:vs)
                                 --dbgDoc $ text $ "putting block with ending call " ++ show (tidIdent $ boundVar cv)
                                 -- TODO avoid eliminating trivial rebindings if target contvar is uniquely ref'd?
                                 
                                 resid <- lift $ ccFreshId $ T.pack ".cr"
                                 baPutBlock head (ILetVal resid (ILCall ty v' vs') : insns)
                                        (CFCont blockid [TypedId ty resid])

          MKCont        _u _ty contvar vs -> do
                                 blockid <- blockIdOf' contvar
                                 vs' <- mapM qv vs
                                 --dbgDoc $ text $ "putting block with ending cont " ++ show (tidIdent $ boundVar cv)
                                 baPutBlock head insns (CFCont blockid vs')

          MKIf          _u _ty v tru fls -> do
                                 let pat :: Bool -> PatternRepr MonoType
                                     pat bval = PR_Atom $ P_Bool (MissingSourceRange "if.pat") boolMonoType bval

                                 blockIdTrue <- generateBlock "if.tru" [] tru
                                 blockIdFals <- generateBlock "if.fls" [] fls
                                 let trueArm = CaseArm (pat True)  blockIdTrue Nothing [] (MissingSourceRange "if.true")
                                 let falsArm = CaseArm (pat False) blockIdFals Nothing [] (MissingSourceRange "if.fals")
                                 --dbgDoc $ text $ "putting block with ending case (if) " ++ show (tidIdent $ boundVar cv)
                                 v' <- qv v
                                 baPutBlock head insns (CFCase v' [trueArm, falsArm])

          MKCase        _u _ty v arms -> do
                                 v' <- qv v
                                 arms' <- mapM (\(MKCaseArm pat subterm bindings range) -> do
                                                blockid <- generateBlock "case.arm" {-bindings-} [] subterm
                                                --dbgDoc $ text $ "bindings for " ++ show blockid ++ " are " ++ show (map (tidIdent. boundVar) bindings)
                                                return $ CaseArm pat blockid Nothing (map boundVar bindings) range) arms
                                                --return $ CaseArm pat blockid Nothing [] range) arms
                                 baPutBlock head insns (CFCase v' arms')
          -- arms  :: MKCaseArm (PatternRepr) (Subterm _)
          -- arms' :: CaseArm PatternRepr BlockId MonoType

      generateBlock name vars subterm = do
          id <- lift $ ccFreshId $ T.pack name
          blockid <- blockIdOfIdent id

          ref <- lift $ newOrdRef Nothing
          let vx = MKBound (TypedId (TyApp (TyCon "Bool") []) id) ref

          cffnOfMKCont vx (MKFn vx vars Nothing subterm _isrec _annot)
          return blockid

cffnOfMKFn :: IORef Uniq -> MKFn (Subterm MonoType) MonoType -> Compiled CFFn
cffnOfMKFn uref (MKFn v vs (Just cont) term isrec annot) = do
  -- Generate a pseudo-entry continuation to match Hoopl's semantics for graphs.
  (rk, st) <- runStateT (blockIdOf cont) (uref, Map.empty, [])
  (_,_,blocks) <- execStateT
        (cffnOfMKCont v (MKFn v vs Nothing term isrec annot))
        st

  --dbgDoc $ text $ "# blocks for " ++ show (tidIdent $ boundVar v) ++ " = " ++ show (length allblocks)

  let graph  = catClosedGraphs (map blockGraph blocks)

  --dbgDoc $ vcat (map pretty allblocks)
  --dbgDoc $ indent 20 (pretty graph)

  return $ Fn { fnVar = boundVar v,
                fnVars = map boundVar vs,
                fnBody = BasicBlockGraph (entryLab blocks) rk graph,
                fnIsRec = isrec,
                fnAnnot = annot }
 where
    --entryLab :: forall x. [Block Insn C x] -> BlockEntry
    entryLab [] = error $ "can't get entry block label from empty list!"
    entryLab (bb:_) = let _r :: Insn C O -- needed for GHC 6.12 compat
                          _r@(ILabel elab) = firstNode bb in elab


letableOfSubexpr :: Subexpr MonoType -> Compiled (Letable MonoType)
letableOfSubexpr subexpr = do
  let qv (DLCNode fop _ _) = do bound <- liftIO $ repr (fopPoint fop) >>= descriptor
                                return $ boundVar bound
  let qa (ArrayIndex v1 v2 x y) = mapM qv [v1, v2] >>= \[v1', v2'] -> return (ArrayIndex v1' v2' x y)
  let qelt (Left lit) = return (Left lit)
      qelt (Right v)  = liftM Right (qv v)

  expr <- readLink "letableOfSubexpr" subexpr
  case expr of
    MKLiteral     _ ty lit -> return $ ILLiteral ty lit
    MKTuple       _ ty vars sr -> do vars' <- mapM qv vars
                                     case ty of
                                       StructType {} ->
                                            return $ ILTuple KindAnySizeType  vars' (AllocationSource "tuple" sr)
                                       _ -> return $ ILTuple KindPointerSized vars' (AllocationSource "tuple" sr)
    MKKillProcess _ ty txt     -> return $ ILKillProcess ty txt
    MKCallPrim    _ ty p vs _r -> do vs' <- mapM qv vs
                                     return $ ILCallPrim ty p vs'
    MKAppCtor     _ ty cid vs -> do vs' <- mapM qv vs
                                    return $ ILAppCtor ty cid vs'
    MKAlloc       _ _ty v amr -> do v' <- qv v
                                    return $ ILAlloc {-ty-} v' amr
    MKDeref       _ ty v      -> qv v >>= \v' -> return $ ILDeref ty v'
    MKStore       _ _t v v2   -> mapM qv [v, v2] >>= \[v',v2'] -> return $ ILStore v' v2'
    MKAllocArray  _ ty v amr zi -> qv v >>= \v' -> return $ ILAllocArray ty v' amr zi
    MKArrayRead   _ ty ari    -> qa ari >>= \ari' -> return $ ILArrayRead ty ari'
    MKArrayPoke   _ _ty ari v -> qa ari >>= \ari' ->
                                 qv v   >>= \v' -> return $ ILArrayPoke {-ty-} ari' v'
    MKArrayLit    _ ty v elts -> qv v   >>= \v' ->
                                 mapM qelt elts >>= \elts' -> return $ ILArrayLit ty v' elts'
    MKTyApp       _ ty v [] -> qv v >>= \v' -> return $ ILBitcast ty v'
    MKTyApp       {} -> error $ "MKNExpr saw tyapp that wasn't eliminated by monomorphization"
    _ -> error $ "non-Letable thing seen by letableOfSubexpr..."


dbgDoc d =
  if False
    then liftIO $ putDocLn d
    else return ()