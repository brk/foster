{-# LANGUAGE RecursiveDo, GADTs, StrictData #-}
-- RecursiveDo is used in dlcSingleton

module Foster.MKNExpr (MKBound(MKBound), mkOfKNMod, mknInline,
                       pccOfTopTerm, knOfMK, MaybeCont(..)) where

import Foster.Base
import Foster.Config
import Foster.MainOpts(getInliningDonate)
import Foster.KNUtil
import Foster.KNExpr(knLoopHeaders')
import Foster.Worklist
import Foster.Output(putDocLn)

import Foster.CFG
import Foster.MonoType(MonoType(..), alphaRenameMonoWithState, boolMonoType)
import Foster.Letable
import Foster.Kind
import Foster.SourceRange(SourceRange(..))

import Control.Monad(liftM, when)
import Control.Monad.State(gets, get, put, lift, forM_,
                           StateT, evalStateT, execStateT, runStateT)
import Data.IORef(IORef, readIORef, newIORef, writeIORef)
import Data.UnionFind.IO
import Control.Monad.IO.Class(MonadIO(..))

import qualified Data.Text as T
import qualified Data.Set as Set(toList, fromList, empty, insert, minView)
import Data.Set(Set)
import qualified Data.Map as Map
import Data.Map(Map)
import qualified Data.List as List(foldl', reverse, all, any)
import qualified Data.Sequence as Seq(Seq, empty, fromList)
import Data.Foldable(toList)
import Data.Maybe(catMaybes, isJust, isNothing)
import Data.Either(partitionEithers)

import Compiler.Hoopl(UniqueMonad(..), C, O, freshLabel, intToUnique,
                      blockGraph, blockJoin, blockFromList, firstNode)

import Prelude hiding ((<$>))
import Prettyprinter
import Prettyprinter.Render.Terminal

-- The "M" in MKNExpr stands for Mutable.
-- This stage implements a mutable graphical program representation
-- based on Kennedy's ``Compiling with Continuations, Continued``.

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

instance PrettyT t => PrettyT (MKBound t) where
    prettyT (MKBound v _) = prettyT v

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

_boundUniq :: MKBound t -> Uniq
_boundUniq (MKBound _ r) = ordRefUniq r

{- Given a graph like this:
      b1 ----> f1       x1 <---- b2
              / \       |
            f2---f3     x2

   substVarForBound f3 b2  will produce

      b1 ----> f1------x1    \--- b2
              /        |
             f2---f3---x2
-}

substVarForBound :: PrettyT t => (FreeOcc t, MKBound t) -> Compiled ()
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
  bx <- liftIO $ descriptor px
  by <- liftIO $ descriptor py
  substBinders bx by
  py `nowPointsTo` px where nowPointsTo x y = liftIO $ union x y

substBinders (MKBound _ b'x) (MKBound _ b'y) = do
  mergeFreeLists b'x b'y
  writeOrdRef b'y Nothing

substVarForVar'' :: PrettyT t => MKBound t -> MKBound t -> Compiled ()
substVarForVar'' bx by = do
  mb_fx <- boundOcc bx
  mb_fy <- boundOcc by
  case (mb_fx, mb_fy) of
    (Just fx, Just fy) -> do
      ccWhen ccVerbose $ do
        dbgDoc $ text "substVarForVar'' " <> prettyT (boundVar bx) <> text "  " <> prettyT (boundVar by)
      substVarForVar fx fy

    (Just _x, Nothing)               -> do substBinders bx by
    (Nothing, Just (DLCNode py _ _)) -> do substBinders bx by; liftIO $ setDescriptor (fopPoint py) bx

    (Nothing, Nothing) -> do
      ccWhen ccVerbose $ do
        dbgDoc $ text $ "substVarForVar'' doing nothing; both binders are dead"
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
freeOccIsSingleton :: PrettyT t => FreeOcc t -> Compiled Bool
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
--
-- Inlining can revisit dead terms. One example of how this can happen is
-- that (1) a singleton fn is optimized, passing a statically known argument.
-- After substitution, uses of the fn's formal are (potentially) redexes.
-- Thus we enqueue the uses for further processing; note specifically that
-- this involves the ``freeLink`` of the formal's occurrence. In step (3),
-- before visiting the occurrence's link, the same call using the formal is
-- inlined, but via a different link -- the one from the call's parent term.
-- In step (4), we finally re-visit the call enqueued in step 2. At this point,
-- the call is dead, meaning its parent now points to the inlined code instead.

data ActiveLinkStatus ty = ActiveSubterm (Subterm ty)
                         | TermIsDead

getActiveLinkFor :: PrettyT ty => MKTerm ty -> Compiled (ActiveLinkStatus ty)
getActiveLinkFor term = do
  let isLinkToOurTerm link = do
        mb_term' <- readOrdRef link
        case mb_term' of
          Nothing -> do
            liftIO $ putStrLn $ "no term for link #" ++ show (ordRefUniq link)
            return False
          Just term' -> do
            return $ parentLinkT term' == parentLinkT term

  parent <- readLink "linkFor" (parentLinkT term)
  case parent of
    ParentFn fn -> do
      good <- isLinkToOurTerm (mkfnBody fn)
      if good
        then return $ ActiveSubterm $ mkfnBody fn
        else return $ TermIsDead
    ParentTerm p -> do
      siblings <- subtermsOf p
      goods <- mapM isLinkToOurTerm siblings
      case [sib | (True, sib) <- zip goods siblings] of
        [] -> return TermIsDead
        [x] -> return $ ActiveSubterm x
        _ -> error $ "linkFor found multiple candidates among the siblings!"

subtermsOf :: MKTerm t -> Compiled [Subterm t]
subtermsOf term =
    case term of
      MKIf          _u _ _ tru fls -> return $ [tru, fls]
      MKLetVal      _u   _      k  -> return $ [k]
      MKLetRec      _u   knowns k  -> return $ k : (map snd knowns)
      MKLetFuns     _u   knowns k _-> do fns <- knownActuals knowns
                                         return $ k : map mkfnBody fns
      MKLetCont     _u   knowns k  -> do fns <- knownActuals knowns
                                         return $ k : map mkfnBody fns
      MKCase        _u _ _v arms   -> do return $ map mkcaseArmBody arms
      MKCont {} -> return []
      MKCall {} -> return []
      MKRelocDoms   _u _vs k -> return $ [k]

type Uplink ty = Link (Parent ty)
data Parent ty = ParentTerm (MKTerm ty)
               | ParentFn  (MKFn (Subterm ty) ty)

-- Bindable values/expressions; distinct from MKTerm to separate program structure from computations.
data MKExpr ty =
          MKKillProcess (Uplink ty) ty T.Text
        | MKLiteral     (Uplink ty) ty Literal
        | MKRecord      (Uplink ty) ty [T.Text] [FreeVar ty] SourceRange
        | MKTuple       (Uplink ty) ty [FreeVar ty] SourceRange
        | MKAppCtor     (Uplink ty) ty (CtorId, CtorRepr) [FreeVar ty] SourceRange
        | MKCallPrim    (Uplink ty) ty (FosterPrim ty)    [FreeVar ty] SourceRange
        -- Mutable ref cells
        | MKAlloc       (Uplink ty) ty (FreeVar ty) AllocMemRegion SourceRange
        | MKDeref       (Uplink ty) ty (FreeVar ty)
        | MKStore       (Uplink ty) ty (FreeVar ty) (FreeVar ty)
        -- Array operations
        | MKAllocArray  (Uplink ty) ty (FreeVar ty) AllocMemRegion ZeroInit SourceRange
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
        | MKLetFuns     (Uplink ty) [Known ty (Link (MKFn (Subterm ty) ty))] (Subterm ty) SourceRange
        | MKLetCont     (Uplink ty) [Known ty (Link (MKFn (Subterm ty) ty))] (Subterm ty)
        | MKRelocDoms   (Uplink ty) [FreeVar ty] (Subterm ty)

        -- Control flow
        | MKCase        (Uplink ty) ty (FreeVar ty) [MKCaseArm (Subterm ty) ty]
        | MKIf          (Uplink ty) ty (FreeVar ty) (Subterm ty) (Subterm ty)
        | MKCall        (Uplink ty) ty (FreeVar ty)       [FreeVar ty] (ContVar ty) CallAnnot
        | MKCont        (Uplink ty) ty (ContVar ty)       [FreeVar ty]

-- Does double duty, representing both regular functions and continuations.
data MKFn expr ty
                = MKFn { mkfnVar   :: (MKBoundVar ty)
                       , mkfnVars  :: [MKBoundVar ty]
                       , mkfnCont  :: Maybe (MKBoundVar ty) -- return continuation for actual functions.
                       , mkfnBody  :: expr
                       , mkfnIsRec :: RecStatus
                       ,_mkfnAnnot :: ExprAnnot
                       , mkfnUnrollCount :: Int
                       } deriving Show -- For KNExpr and KSmallstep

data MKCaseArm expr ty = MKCaseArm { _mkcaseArmPattern  :: PatternRepr ty
                                   ,  mkcaseArmBody     :: expr
                                   , _mkcaseArmBindings :: Seq.Seq (MKBoundVar ty)
                                   , _mkcaseArmRange    :: SourceRange
                                   }

type WithBinders ty = StateT (Map Ident (MKBoundVar ty)) Compiled

-- With the given binding map, process the given terms,
-- constructing a final term using the builder ``f``.
-- In the course of processing, each subterm gets an empty uplink.
-- Finally, backpatch the result rv into the subterms' uplinks.

mkBackpatch' :: (ty ~ MonoType) => --(CanMakeFun ty, Pretty ty) =>
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
        Nothing -> error $ "MKNExpr.hs: findBinder had nothing for " ++ show (prettyIdent id)
                      -- ++ "\n; m = " ++ show [(k, tidIdent (boundVar v)) | (k,v) <- Map.toList m]
mkFreeOcc :: TypedId ty -> WithBinders ty (FreeVar ty)
mkFreeOcc tid = mkFreeOcc' (tidIdent tid)

mkFreeOcc' :: Ident -> WithBinders ty (FreeVar ty)
mkFreeOcc' xid = do
    m <- get
    let binder = findBinder xid m
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

unsafeForceCont id = T.pack "forcecont_" `T.isPrefixOf` (identPrefix id)

mkOfKNFn :: (ty ~ MonoType) =>
            Int -> Maybe (ContinuationContext ty)
         -> (Ident, Fn RecStatus (KNExpr' RecStatus ty) ty)
         -> WithBinders ty (Bool, MKFn (Subterm ty) ty)

mkOfKNFn unrollCount mb_k (localname, Fn v vs expr isrec annot) = do
    m <- get
    v' <- mkBinder v
    vs' <- mapM mkBinder vs

    case (mb_k, unsafeForceCont localname) of
      (Just k, True) -> do
        expr' <- mkOfKN_Base expr k -- TODO maybe need to separately track ret k?
        put m
        let f' = MKFn v' vs' Nothing expr' isrec annot unrollCount
        lift $ backpatchFn f'
        return (False, f')

      _ -> do
        jb  <- genBinder ".fret" (TupleType []) -- type is ignored
        lift $ ccWhen ccVerbose $ do
          dbgDoc $ text "Generated return continuation " <> pretty (tidIdent $ boundVar jb) <> text " for fn " <> pretty (tidIdent v)

        expr' <- mkOfKN_Base expr (CC_Tail jb)
        put m
        let f' = MKFn v' vs' (Just jb) expr' isrec annot unrollCount
        lift $ backpatchFn f'
        return (True, f')

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
    liftIO $ putDocLn $ prettyT kn
    liftIO $ putDocLn $ showStructure kn
  mkOfKN_Base kn (CC_Tail mainBinder)

mkOfKN_Base :: (ty ~ MonoType) =>
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
        KNLetVal      x e1 e2 _ | Just (_, gen) <- isExprNotTerm e1 -> do
            xb <- mkBinder (TypedId (typeKN e1) x) -- versus genBinderAndOcc
            (selfLink2, _exp) <- withLinkE gen
            subterm <- mkOfKN_Base e2 k
            let rv = MKLetVal nu (mkKnownE xb selfLink2) subterm
            lift $ backpatchE rv [selfLink2]
            lift $ backpatchT rv [subterm]

        KNLetVal      x e1 e2 _ -> do
            -- The 'let val' case from CwCC figure 8.
            -- Generate the continuation variable 'j'.
            jb  <- genBinder ".cont" (mkFunType [typeKN e1] (typeKN e2))
            jbx <- genBinder ".cntx" (mkFunType [typeKN e1] (typeKN e2))

            -- Generate the continuation's bound parameter, 'x'
            xb <- mkBinder $ TypedId (typeKN e1) x

            -- letcont j x = [[e2]] k   in    ((e1)) j
            body <- mkOfKN_Base e2 k

            let unrollCount = 0
                contfn = MKFn jbx [xb] Nothing body NotRec
                              (annotForRange $ MissingSourceRange "cont") unrollCount
            known <- lift $ mkKnown' jb contfn
            lift $ backpatchFn contfn

            rest' <- mkOfKN_Base e1 (CC_Tail jb)

            let rv = MKLetCont nu [known] rest'
            lift $ backpatchT rv [rest']

        KNRelocDoms ids e -> do
          vs <- mapM mkFreeOcc' ids
          --mapM_ (\fv -> setFreeLink fv parent) (freeVarsE mkexpr)
          mkBackpatch' [e] k (\[e'] -> do
            return $ MKRelocDoms nu vs e')
          --mapM_ (\v -> setFreeLink v rd) vs -- vs are not free vars for RelocDoms
          --return rd

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

        KNHandler {} -> error $ "MKNExpr.sh should not see KNHandler!"

        KNCall       ty v vs ca -> do
            (v':vs') <- qvs (v:vs)
            case k of
                CC_Tail jb -> do
                  if unsafeForceCont (tidIdent v)
                    then do
                      return $ MKCont nu  ty v' vs'
                    else do
                      kv <- lift $ mkFreeOccForBinder jb
                      return $ MKCall nu  ty v' vs' kv ca

                CC_Base kf -> do
                  liftIO $ putDocLn $ text "saw non-tail call of " <> prettyT v
                  genContinuation ".clco" ".clcx" ty kf nu $ \nu' jb -> do
                      kv <- lift $ mkFreeOccForBinder jb
                      return $ MKCall nu'  ty v' vs' kv ca

        KNLetRec  xs es rest -> do 
            let vs = map (\(x,e) -> (TypedId (typeKN e) x)) (zip xs es)
            m1 <- get
            do dbgDoc $ text "m1: " <> prettyT (Map.toList m1)
            xs' <- mapM mkBinder vs
            do m2 <- get
               dbgDoc $ text "m2: " <> prettyT (Map.toList m2)
            --put $ extend m (map tidIdent vs) xs'
            -- TODO reconsider k
            ts <- mapM (\e -> mkOfKN_Base e k) es
            t  <- mkOfKN_Base rest k
            put m1
            let knowns = map (uncurry mkKnownT) (zip xs' ts)
            let rv = MKLetRec      nu knowns t
            lift $ backpatchT rv (t:ts)

        KNLetFuns ids fns st sr -> do
            let vs = map (\(x,fn) -> (TypedId (fnType fn) x)) (zip ids fns)
            m <- get
            binders <- mapM mkBinder vs
            let unrollCount = 0
            fcfs' <- mapM (mkOfKNFn unrollCount (Just k)) (zip ids fns)
            rest' <- mkOfKN_Base st k
            fknowns <- lift $ mapM (uncurry mkKnown') (zip binders [f | (True,  f) <- fcfs'])
            cknowns <- lift $ mapM (uncurry mkKnown') (zip binders [f | (False, f) <- fcfs'])

            crest <- do
              if null cknowns then return rest'
                else do
                  nu'  <- lift $ newOrdRef Nothing
                  cfres <- lift $ backpatchT (MKLetCont nu' cknowns rest') [rest']
                  lift $ do selfLink <- newOrdRef Nothing
                            installLinks selfLink cfres
            put m
            lift $ backpatchT (MKLetFuns nu fknowns crest sr) [crest]

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
    KNRecord    ty ls vs sr -> Just $ (,) ".rcd" $ \nu' -> do
                                  vs' <- mapM qv vs
                                  return $ MKRecord nu' ty ls vs' sr
    KNTuple     ty vs sr -> Just $ (,) ".tup" $ \nu' -> do
                                  vs' <- mapM qv vs
                                  return $ MKTuple nu' ty vs' sr
    KNKillProcess   ty t -> Just $ (,) ".kil" $ \nu' -> return $ MKKillProcess nu' ty t
    KNCallPrim r ty p vs -> Just $ (,) ".cpr" $  \nu' -> do
                                  vs' <- qvs vs
                                  return $ MKCallPrim nu' ty p vs' r
    KNAppCtor    ty c vs sr -> Just $ (,) ".app" $ \nu' -> do
                                  vs' <- qvs vs
                                  return $ MKAppCtor nu' ty c vs' sr
    KNAlloc      ty v mr sr -> Just $ (,) ".alo" $  \nu' -> do
                                  v' <- qv  v 
                                  return $ MKAlloc   nu' ty v' mr sr
    KNDeref      ty v    -> Just $ (,) ".get" $  \nu' -> do
                                  v' <- qv  v
                                  return $ MKDeref   nu' ty v'
    KNStore      ty v v2 -> Just $ (,) ".sto" $  \nu' -> do
                                  [v', v2'] <- qvs [v,v2]
                                  return $ MKStore   nu' ty v' v2'
    KNAllocArray ty v m z sr -> Just $ (,) ".ala" $  \nu' -> do
                                  v' <- qv  v
                                  return $ MKAllocArray  nu' ty v' m z sr
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

    let unrollCount = 0
        contfn = MKFn jbx [xb] Nothing body NotRec
                      (annotForRange $ MissingSourceRange "cont") unrollCount
    known <- lift $ mkKnown' jb contfn
    lift $ backpatchFn contfn

    (rest', _) <- withLinkT $ \nu' -> restgen nu' jb
    
    let rv = MKLetCont nu [known] rest'
    lift $ backpatchT rv [rest']

prettyRootTerm :: MKTerm ty -> Doc AnsiStyle
prettyRootTerm term =
  case term of
    MKLetVal      {} -> text "MKLetVal    "
    MKLetRec      {} -> text "MKLetRec    "
    MKLetFuns     {} -> text "MKLetFuns   "
    MKLetCont     {} -> text "MKLetCont   "
    MKRelocDoms   {} -> text "MKRelocDoms "
    MKCase        {} -> text "MKCase      "
    MKIf          {} -> text "MKIf        "
    MKCall        {} -> text "MKCall      "
    MKCont        {} -> text "MKCont      "

canRemoveIfDead :: MKExpr ty -> Bool
canRemoveIfDead expr =
  case expr of
    MKLiteral     {} -> True
    MKRecord      {} -> True
    MKTuple       {} -> True
    MKKillProcess {} -> False
    MKCallPrim    {} -> False -- TODO refine
    MKAppCtor     {} -> True
    MKAlloc       {} -> True
    MKDeref       {} -> True
    MKStore       {} -> False
    MKAllocArray  {} -> True
    MKArrayRead   {} -> True
    MKArrayPoke   {} -> False
    MKArrayLit    {} -> True
    MKCompiles    {} -> True
    MKTyApp       {} -> True
    
parentLinkE :: MKExpr ty -> Uplink ty
parentLinkE expr =
  case expr of
    MKLiteral     u       _t _it -> u
    MKRecord      u     _t _l _s _r -> u
    MKTuple       u     _t _s _r -> u
    MKKillProcess u     _ty _t    -> u
    MKCallPrim    u     _ty _ _s _ -> u
    MKAppCtor     u     _ty _ _s _sr -> u
    MKAlloc       u     _ty _  _ _sr -> u
    MKDeref       u     _ty _    -> u
    MKStore       u     _ty _ _2 -> u
    MKAllocArray  u     _ty _ _ _ _sr -> u
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
    MKLetFuns     u   _knowns _k _sr -> u
    MKLetCont     u   _knowns _k -> u
    MKRelocDoms   u _vs _k      -> u
    MKCase        u  _ty _ _arms  -> u
    MKIf          u  _ty _ _e1 _e2 -> u
    MKCall        u     _ty _ _s _ _ -> u
    MKCont        u     _ty _ _s     -> u


freeVarsE :: MKExpr ty -> [FreeOcc ty]
freeVarsE expr =
  case expr of
    MKLiteral     {} -> []
    MKRecord       _     _t _ls vs _r -> vs
    MKTuple       _     _t vs _r -> vs
    MKKillProcess {} -> []
    MKCallPrim    _     _ty _ vs _ -> vs
    MKAppCtor     _     _ty _ vs _sr -> vs
    MKAlloc       _     _ty v  _ _sr -> [v]
    MKDeref       _     _ty v    -> [v]
    MKStore       _     _ty v1 v2 -> [v1,v2]
    MKAllocArray  _     _ty v _ _ _sr -> [v]
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
    MKRelocDoms   _      vs     _k   -> vs
    MKCase        _  _ty v _arms     -> [v]
    MKIf          _  _ty v _e1 _e2   -> [v]
    MKCall        _     _ty v vs c _ -> c:v:vs
    MKCont        _     _ty c vs     -> c  :vs

data MaybeCont ty = YesCont (MKBoundVar ty)
                  | NoCont
                  deriving (Eq)

mbContOf Nothing = NoCont
mbContOf (Just c) = YesCont c

knOfMKFn mb_retCont (MKFn v vs mb_cont expr isrec annot _unrollCount) = do
      let qb (MKBound tid _) = tid
      expr' <- do let rc = case --trace ("picking new continuation for " ++ show (pretty v) ++ "from: " ++ show (pretty (mb_retCont, mb_cont))) $
                                 (mb_retCont, mb_cont) of 
                            (YesCont retCont, Nothing) -> YesCont retCont
                            (NoCont, Nothing) -> NoCont --error $ "knOfMKFn has no return continuation!"
                            (_,      Just rc) -> YesCont rc
                  readLink "knOfMKFn" expr >>= knOfMK rc
      return $ Fn (qb v) (map qb vs) expr' isrec annot

knOfMKExpr :: PrettyT t =>
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
    MKRecord      _ ty labs vars sr -> do
                                     vars' <- mapM qv vars
                                     return $ KNRecord ty labs vars' sr
    MKTuple       _ ty vars sr -> do vars' <- mapM qv vars
                                     return $ KNTuple ty vars' sr
    MKKillProcess _ ty txt     -> return $ KNKillProcess ty txt
    MKCallPrim    _ ty p vs r -> do vs' <- mapM qv vs
                                    return $ KNCallPrim r ty p vs'
    MKAppCtor     _ ty cid vs sr -> do vs' <- mapM qv vs
                                       return $ KNAppCtor ty cid vs' sr
    MKAlloc       _ ty v amr sr -> do v' <- qv v
                                      return $ KNAlloc ty v' amr sr
    MKDeref       _ ty v      -> qv v >>= \v' -> return $ KNDeref ty v'
    MKStore       _ ty v v2   -> mapM qv [v, v2] >>= \[v',v2'] -> return $ KNStore ty v' v2'
    MKAllocArray  _ ty v amr zi sr -> qv v >>= \v' -> return $ KNAllocArray ty v' amr zi sr
    MKArrayRead   _ ty ari    -> qa ari >>= \ari' -> return $ KNArrayRead ty ari'
    MKArrayPoke   _ ty ari v  -> qa ari >>= \ari' ->
                                 qv v   >>= \v' -> return $ KNArrayPoke ty ari' v'
    MKArrayLit    _ ty v elts -> qv v   >>= \v' ->
                                 mapM qelt elts >>= \elts' -> return $ KNArrayLit ty v' elts'
    MKCompiles    _ res ty body -> q body >>= \body' -> return $ KNCompiles res ty body'
    MKTyApp       _ ty v arg_tys -> qv v >>= \v' -> return $ KNTyApp ty v' arg_tys

knOfMK :: PrettyT t =>
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
        let binds' = fmap boundVar binds
        body' <- q body
        --mb_guard' <- liftMaybe q mb_guard
        return $ CaseArm pat body' Nothing binds' rng
  let qf = knOfMKFn mb_retCont

  case term0 of
    MKRelocDoms   _u _vs k -> q k
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
                                          Just b' -> return $ mkKNLetVal x' b' k'
    MKLetRec      _u   knowns  k  -> do (xs', es')  <- qks (knOfMK mb_retCont) knowns
                                        k'  <- q k
                                        return $ mkKNLetRec xs' es' k'
    MKLetFuns     _u  knowns k sr -> do (xs', fns') <- qks qf knowns
                                        k'  <- q k
                                        return $ mkKNLetFuns  xs' fns' k' sr

    MKCall        _u  ty v vs _c ca -> do
      (v':vs') <- mapM qv (v:vs)
      cvb <- freeBinder _c
      if --trace ("MKCall comparing " ++ (show $ pretty cvb) ++ " vs " ++ (show $ pretty mb_retCont)) $
            YesCont cvb == mb_retCont || isMainFnVar v'
        then return $ KNCall       ty v' vs' ca
        else do xid <- ccFreshId $ T.pack ".ctmp"
                return $ mkKNLetVal xid (KNCall ty v' vs' ca)
                          (KNCall (tidType $ boundVar cvb) (boundVar cvb) [TypedId ty xid] CA_None)
      
    -- TODO if we can match   letcont j x = ... in MKCall v vs j
    --      and j has no other uses,
    --      emit KNLetVar x = KNCall v vs
    MKLetCont     _u  knowns k -> do (xs', fns') <- qks qf knowns
                                     k'  <- q k
                                     return $ mkKNLetFuns  xs' fns' k' (MissingSourceRange "letcont")
    
    MKCont        _u ty contvar vs -> do
          vs' <- mapM qv vs
          cvb <- freeBinder contvar
          -- If contvar is the return continuation, with one argument, we don't want a call.
          let isReturn = YesCont cvb == mb_retCont
          case --trace ("MKCont comparing " ++ (show $ pretty cvb) ++ " vs " ++ (show $ pretty mb_retCont)) $
                 vs' of
            [v] | isReturn -> return $ KNVar v
            _ -> return $ KNCall ty (boundVar cvb) vs' CA_None

mkKNLetRec [] [] k = k
mkKNLetRec xs es k = KNLetRec xs es k

mkKNLetFuns [] [] k _  = k
mkKNLetFuns xs es k sr = KNLetFuns xs es k sr


isMainFnVar v =
  case tidIdent v of
      GlobalSymbol t _ -> t == T.pack "main"
      _ -> False

isMainFn fo = do
  b <- freeBinder fo
  return $ isMainFnVar (boundVar b)

isTextPrim (GlobalSymbol t _) = t `elem` [T.pack "TextFragment", T.pack "TextConcat"]
isTextPrim _ = False

-- We detect and kill dead bindings for functions here as well.
-- TODO we ought to collect a single unified worklist of subterms
--      (including redexes and bindings) which we can iterate over
--      and add to as appropriate during processing.
-- For example, to remove a dead function binding we must also
-- collect and kill the free variable occurrences mentioned within the
-- body, which may in turn trigger further dead-binding elimination.
collectRedexes :: (PrettyT t) =>
      MKNInlineState t -> Subterm t -> Compiled ()
collectRedexes work sbtm = go sbtm
 where
   go subterm = do
    mb_term <- readOrdRef subterm
    case mb_term of
      Nothing -> return ()
      Just term -> do
        case term of
          MKCall _ _ fo _ _ _ -> whenNotM (isMainFn fo) (markRedex subterm)
          MKCont {}           -> markRedex subterm
          _ -> markAndFindSubtermsOf term >>= mapM_ go
          where markAndFindSubtermsOf term =
                    case term of
                      MKIf          _u _ _ tru fls -> return [tru, fls]

                      MKLetVal      _u  (x, br) k  -> do markExpBind (x, br)
                                                         return [k]
                      MKLetRec      _u   knowns k  -> do mapM_ markValBind knowns
                                                         return $ k : (map snd knowns)
                      MKLetFuns     _u   knowns k _-> do markRedex subterm
                                                         mapM_ (markFunBind subterm) knowns
                                                         fns <- knownActuals knowns
                                                         return $ k : map mkfnBody fns
                      MKLetCont     _u   knowns k  -> do mapM_ markCntBind knowns
                                                         fns <- knownActuals knowns
                                                         return $ k : map mkfnBody fns
                      MKCase        _u _ _v arms -> do markRedex subterm
                                                       return $ map mkcaseArmBody arms
                      MKRelocDoms _u  vs k -> do bvs <- mapM freeBinder vs
                                                 let ids = map (tidIdent . boundVar) bvs
                                                 liftIO $ modIORef' relocdomsref (\m -> Map.insert ids (term,k) m)
                                                 return [k]
                      _ -> return []

   markRedex subterm  = liftIO $ modIORef' ref     (\w -> worklistAdd w subterm)
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
                        ccWhen ccVerbose $ do
                          dbgDoc $ string $ "markFnBind: x  = (" ++ show xc ++ " vs " ++ show bc ++ ") " ++ show (prettyIdent $ tidIdent $ boundVar x)
                          dbgDoc $ string $ "            fv = (" ++ show fc ++ ") " ++ show (prettyIdent $ tidIdent $ boundVar (mkfnVar mkfn))
                        if xc == 0 && not (isTextPrim (tidIdent $ boundVar x))
                          then do
                            dbgDoc $ string $ "markFunBind killing dead fn binding " ++ show (prettyIdent $ tidIdent $ boundVar x)
                            writeOrdRef fn Nothing
                          else do
                            dbgDoc $ text "adding fn ordref # " <> pretty (ordRefUniq fn) <+> text " :: " <> prettyT (boundVar (mkfnVar mkfn))
                            liftIO $ modIORef' funbindsref (\m -> Map.insert x fn m)
                            liftIO $ modIORef' fundefsref  (\m -> Map.insert x subterm m)
    
   ref = mknPendingSubterms work
   valbindsref  = mknKnownTerms work
   expbindsref  = mknKnownExprs work
   funbindsref  = mknFnBinds work
   fundefsref   = mknFnDefs work
   aliasesref   = mknAliases work
   relocdomsref = mknRelocDoms work
  
knownActuals :: [Known ty (Link val)] -> Compiled [val]
knownActuals knowns = do
    mb_vals <- mapM (readOrdRef . snd) knowns
    return $ catMaybes mb_vals

-- {{{
shouldNotInlineFn fn =
  let id = tidIdent (boundVar (mkfnVar fn)) in
  (T.pack "noinline_" `T.isInfixOf` identPrefix id
   && not (T.pack "." `T.isInfixOf` identPrefix id))

flattenMaybe :: Maybe (Maybe a) -> Maybe a
flattenMaybe Nothing = Nothing
flattenMaybe (Just x) = x

data RedexSituation t =
       CallOfUnknownFunction
     | CallOfNonInlineableFunction (MKFn (Subterm t) t) (Link (MKFn (Subterm t) t))
     | CallOfSingletonFunction (MKFn (Subterm t) t)
     | CallOfDonatableFunction (MKFn (Subterm t) t) [(Int, FreeOcc t)]
     | SomethingElse           (MKFn (Subterm t) t) (Link (MKFn (Subterm t) t))

classifyRedex :: (PrettyT t)
              => FreeOcc t -> [FreeOcc t]
              -> Map (MKBoundVar t) (Link (MKFn (Subterm t) t))
              -> Map (MKBoundVar t) (MKBoundVar t)
              -> Compiled (Bool, RedexSituation t)
classifyRedex callee args knownFns aliases = do
  bv <- freeBinder callee
  let bv' = case Map.lookup bv aliases of
              Nothing -> bv
              Just z  -> z
  let mb_link = Map.lookup bv' knownFns
  mb_fn <- mapMaybeM readOrdRef mb_link >>= return . flattenMaybe
  situation <- classifyRedex' bv' mb_fn mb_link args knownFns
  return (bv /= bv', situation)

classifyRedex' _ Nothing _ _ _ = do
  return CallOfUnknownFunction

classifyRedex' fnbinder (Just fn) (Just fnlink) args knownFns = do
  callee_singleton <- binderIsSingletonOrDead fnbinder
  {-
  count <- mkbCount binder
  dbgDoc $ text $ "is callee singleton? " ++ show (pretty binder) ++
                      " -> " ++ show callee_singleton ++ " count: " ++ show count ++
                      " ; rec? " ++ show (mkfnIsRec fn) -}

  case (callee_singleton, mkfnIsRec fn) of
    _ | shouldNotInlineFn fn
                   -> do return $ CallOfNonInlineableFunction fn fnlink
    (True, NotRec) -> do return $ CallOfSingletonFunction fn
    _ -> do
      donationss <- mapM (\(n, (arg, binder)) -> do
                         argsingle <- freeOccIsSingleton arg
                         argboundfn <- lookupBinding arg knownFns
                         bindoccs <- collectOccurrences binder
                         -- Check how many times the binder occurs,
                         -- excluding recursive calls.
                         bindNonRecOccCounts <- mapM (\occ -> do
                            Just tm <- readOrdRef (freeLink occ)
                            case tm of
                              MKCall _ _ v _ _ _ -> do
                                vb <- freeBinder v
                                return (if vb == fnbinder || vb == mkfnVar fn then 0 else (1 :: Int))
                              _ -> return 1) bindoccs
                         let bindsingle = sum bindNonRecOccCounts <= 1

                         if argsingle && isJust argboundfn && bindsingle
                           then return [(n, arg)]
                           else return []
                         ) (zip [0..] $ zipSameLength args (mkfnVars fn))
      let donations = concat donationss
      if null donations || mkfnUnrollCount fn > 0
        then do ccWhen (return $ null donations) $ do
                  noccs <- dlcCount fnbinder
                  dbgDoc $ yellow (prettyT fnbinder) <> text "      not donatable because no donations; #occs "
                                <> pretty noccs <> text "; rec? " <> pretty (mkfnIsRec fn)
                ccWhen (return $ mkfnUnrollCount fn > 0) $ do
                  dbgDoc $ text "  not donatable because unroll count > 0"
                return $ SomethingElse fn fnlink
        else return $ CallOfDonatableFunction fn donations
-- }}}

-- {{{
type MKRenamed t = WithBinders t

runCopyMKFn :: (PrettyT t, AlphaRenamish t RecStatus)
            => MKFn (Subterm t) t -> Map Ident (MKBoundVar t)
            -> [(Int, FreeOcc t)]
            -> Compiled (MKFn (Subterm t) t)
runCopyMKFn mkfn bindings donations = evalStateT (copyMKFn mkfn donations) bindings

copyBinder :: String -> MKBoundVar t -> MKRenamed t (MKBoundVar t)
copyBinder msg b = do
  newid <- lift $ ccRefresh (tidIdent $ boundVar b)
  -- Like mkBinder, but we record the old id in the map instead of the new one.
  ref <- lift $ newOrdRef Nothing
  let binder = MKBound (TypedId (tidType $ boundVar b) newid) ref
  !m <- get
  put $ extend m [tidIdent $ boundVar b] [binder]
  lift $ ccWhen ccVerbose $ do
    dbgDoc $ string $ "copied binder " ++ show (prettyIdent $ tidIdent $ boundVar b) ++ " (" ++ msg ++ ") into " ++ show (prettyIdent $ newid)
  return binder

ccRefresh :: Ident -> Compiled Ident
ccRefresh (Ident t _) = do
    u <- ccUniq
    return $ Ident t u
ccRefresh (GlobalSymbol t alt) = do
    u <- ccUniq
    return $ GlobalSymbol (t `T.append` T.pack (show u)) alt

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

-- TODO increment unroll count?
copyMKFn :: (PrettyT t, AlphaRenamish t RecStatus)
         => MKFn (Subterm t) t
         -> [(Int, FreeOcc t)]
         -> MKRenamed t (MKFn (Subterm t) t)
copyMKFn fn donations = do
  v'  <-       copyBinder "mkfnVar"   (mkfnVar fn)
  vs' <- mapM (copyBinder "mkfnVars") (mkfnVars fn)
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
  -- We don't really have infrastructure for changing the formal arguments of a function,
  -- so we eagerly remove specialized formals here. This will leave call sites temporarily
  -- inconsistent; if the caller passes donations, it's the caller's responsibility to
  -- fix up call sites.
  --vs'' <- lift $ specializeArgs donations vs'
  let fn' = fn { mkfnVar = v' , mkfnVars = vs' , mkfnBody = link' , mkfnCont = cont' }
  lift $ backpatchFn fn'
  return fn'

-- Returns a Subexpr with an empty parent link.
copyMKExpr :: (PrettyT t, AlphaRenamish t RecStatus)
           => MKExpr t -> MKRenamed t (Subexpr t, MKExpr t)
copyMKExpr expr = do
  let qv = copyFreeOcc
  let qa (ArrayIndex v1 v2 x y) =
        mapM qv [v1, v2] >>= \[v1', v2'] -> return (ArrayIndex v1' v2' x y)
  let qelt (Left lit) = return (Left lit)
      qelt (Right v)  = liftM  Right (qv v)
  case expr of
    MKLiteral     _ ty lit -> withLinkE $ \u -> return $ MKLiteral u ty lit
    MKRecord      _ ty labs vars sr -> do
                                     vars' <- mapM qv vars
                                     withLinkE $ \u -> return $ MKRecord u ty labs vars' sr
    MKTuple       _ ty vars sr -> do vars' <- mapM qv vars
                                     withLinkE $ \u -> return $ MKTuple u ty vars' sr
    MKKillProcess _ ty txt     -> withLinkE $ \u -> return $ MKKillProcess u ty txt
    --MKVar         _          _   -> u
    MKCallPrim    _ ty p vs r -> do vs' <- mapM qv vs
                                    withLinkE $ \u -> return $ MKCallPrim u   ty p  vs' r
    MKAppCtor     _ ty cid vs sr -> do vs' <- mapM qv vs
                                       withLinkE $ \u -> return $ MKAppCtor u ty cid vs' sr
    MKAlloc       _ ty v amr  sr  -> do v' <- qv v
                                        withLinkE $ \u -> return $ MKAlloc u ty v' amr sr
    MKDeref       _ ty v      -> qv v >>= \v' ->
                                    withLinkE $ \u -> return $ MKDeref u ty v'
    MKStore       _ ty v v2   -> mapM qv [v, v2] >>= \[v',v2'] ->
                                    withLinkE $ \u -> return $ MKStore u ty v' v2'
    MKAllocArray  _ ty v amr zi sr -> qv v >>= \v' ->
                                    withLinkE $ \u -> return $ MKAllocArray u ty v' amr zi sr
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

copyMKTerm :: (PrettyT t, AlphaRenamish t RecStatus)
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
            Just fn -> do fn' <- copyMKFn fn []
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
    MKRelocDoms   _u   vs     k   -> do k' <- q k
                                        vs' <- mapM qv vs
                                        withLinkT $ \u -> lift $ do
                                          let rv = MKRelocDoms u vs' k'
                                          backpatchT rv [k']
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
    MKLetFuns     _u  knowns k sr -> do knowns' <- mapM (qk qf) knowns
                                        k'  <- q k
                                        withLinkT $ \u -> lift $ do
                                          let rv = MKLetFuns u knowns' k' sr
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
    MKCall        _u  ty v vs c ca -> do mapM qv (v:vs) >>= \(v':vs') ->
                                          qv   c        >>= \c'  ->
                                           withLinkT $ \u -> lift $ return $ MKCall u       ty v' vs' c' ca
    MKCont        _u  ty _c vs     -> do mapM qv    vs  >>= \    vs' ->
                                          qv  _c        >>= \c'  ->
                                           withLinkT $ \u -> return $ MKCont u       ty c' vs'
  lift $ installLinks link newterm


processDeadBindings work = do
  let bindingWorklistRef = mknDeadBindings work
  w0 <- liftIO $ readIORef bindingWorklistRef
  case worklistGet w0 of
    Nothing -> do return ()
    Just (bv, w') -> do
      liftIO $ writeIORef bindingWorklistRef w'
      expBindMap <- liftIO $ readIORef (mknKnownExprs work)
      case Map.lookup bv expBindMap of
        Nothing -> do dbgDoc $ text "processDeadBindings: unable to find expr for dead bound var " <> prettyT bv
                      return ()
        Just exprLink -> do
            e <- readLink "processDeadBindings" exprLink
            let freeOccs = freeVarsE e
            if canRemoveIfDead e && not (null freeOccs)
              then do dbgDoc $ yellow (text "killing " <> pretty (length freeOccs) <>
                                        text " occurrences in dead expr bound to ") <> red (prettyT bv)
                      kn <- knOfMKExpr NoCont e
                      dbgDoc $ indent 8 (prettyT kn)
                      mapM_ (killOccurrence work) freeOccs
              else return ()
      processDeadBindings work


data MKNInlineState t = MKNInlineState {
  mknPendingSubterms :: IORef (WorklistQ (Subterm t))
, mknPendingFnBinders :: IORef (Set (MKBoundVar t))
, mknKnownTerms      :: IORef (Map (MKBoundVar t) (Link (MKTerm t)))
, mknKnownExprs      :: IORef (Map (MKBoundVar t) (Link (MKExpr t)))
, mknFnBinds         :: IORef (Map (MKBoundVar t) (Link (MKFn (Subterm t) t)))
, mknFnDefs          :: IORef (Map (MKBoundVar t) (Link (MKTerm t)))
, mknAliases         :: IORef (Map (MKBoundVar t) (MKBoundVar t))
, mknDeadBindings    :: IORef (WorklistQ (MKBoundVar t))
, mknRelocDoms       :: IORef (Map [Ident] (MKTerm t, (Link (MKTerm t))))
}

mkMKNInlineState = do
  wr <- liftIO $ newIORef worklistEmpty -- "worklist ref"
  kr <- liftIO $ newIORef Map.empty -- "known vals ref"
  er <- liftIO $ newIORef Map.empty -- "expr (valbinds) ref"
  fr <- liftIO $ newIORef Map.empty -- "fn link ref"
  fd <- liftIO $ newIORef Map.empty -- "fn defs ref"
  ar <- liftIO $ newIORef Map.empty -- "alises ref"
  deadBindings <- liftIO $ newIORef worklistEmpty
  relocDomMarkers <- liftIO $ newIORef Map.empty
  pf <- liftIO $ newIORef Set.empty -- "pending function idents"
  return $ MKNInlineState wr pf kr er fr fd ar deadBindings relocDomMarkers

reconsiderForContification :: MKNInlineState t -> FreeVar t -> Compiled ()
reconsiderForContification work fv = do
  bv <- freeBinder fv
  dbgDoc $ text "reconsiderForContification: " <> pretty (tidIdent $ boundVar bv)
  liftIO $ modIORef' (mknPendingFnBinders work) (\w -> Set.insert bv w)

worklistGet' work = do
  let getPendingFnTerm = do
        bvset <- liftIO $ readIORef (mknPendingFnBinders work)
        case Set.minView bvset of
          Nothing -> return Nothing
          Just (bv, newset) -> do
            liftIO $ writeIORef (mknPendingFnBinders work) newset
            fndefs <- liftIO $ readIORef (mknFnDefs work)
            dbgDoc $ text "getPendingFnTerm: " <> pretty (tidIdent $ boundVar bv)
            return $ Map.lookup bv fndefs

      getPendingSubterm = do
        let wr = mknPendingSubterms work
        w0 <- liftIO $ readIORef wr
        case worklistGet w0 of
          Nothing -> getPendingFnTerm
          Just (subterm, w) -> do
            liftIO $ writeIORef wr w
            return $ Just subterm

  mb_subterm <- getPendingSubterm
  case mb_subterm of
    Nothing -> return Nothing
    Just subterm -> do
      mb_redex <- readOrdRef subterm
      case mb_redex of
        Nothing ->
          -- If the subterm is dead, move on to the next one.
          worklistGet' work
        Just mredex -> do
          parent <- readOrdRef (parentLinkT mredex)
          return $ Just (subterm, mredex, parent)

mknInline :: Subterm MonoType -> MKBoundVar MonoType -> Maybe Int -> Compiled ()
mknInline subterm mainCont mb_gas = do
    work <- mkMKNInlineState

    collectRedexes work subterm

{-
    do w0 <- liftIO $ readIORef wr
       k0 <- liftIO $ readIORef kr
       e0 <- liftIO $ readIORef er
       f0 <- liftIO $ readIORef fr
       dbgDoc $ text $ "collected " ++ show (length (worklistToList w0)) ++ " redexes..."
       dbgDoc $ text $ "collected " ++ show (length (Map.toList k0)) ++ " valbinds..."
       dbgDoc $ text $ "collected " ++ show (length (Map.toList e0)) ++ " expbinds..."
       dbgDoc $ text $ "collected " ++ show (length (Map.toList f0)) ++ " funbinds..."
-}

    origGas <- case mb_gas of
                    Nothing -> return 42000
                    Just gas -> do liftIO $ putStrLn $ "using gas: " ++ show gas
                                   return gas

    let go 0 = dbgDoc $ text "... ran outta gas"

        go gas = do
           ccWhen ccVerbose $ do
             liftIO $ putStrLn $ "gas: " ++ show gas ++ "; step: " ++ show (origGas - gas)

           processDeadBindings work
           mb_mredex_parent <- worklistGet' work
           case mb_mredex_parent of
             Nothing -> ccWhen ccVerbose $ do liftIO $ putDocLn $ text "... ran outta work"
             Just (_subterm, mredex, Nothing) -> do
                case mredex of
                  MKLetFuns _u [(bv,_)] _ _sr | tidIdent (boundVar bv) == GlobalSymbol (T.pack "TextFragment") NoRename ->
                    return () -- The top-most function binding will be parentless; don't print about it though.
                  _ -> do
                    do redex <- knOfMK (YesCont mainCont) mredex
                       dbgDoc $ red (text "skipping parentless redex: ") <+> prettyT redex
                  
                go gas

             Just (subterm, mredex, Just _parent) -> do
              linkResult <- getActiveLinkFor mredex
              case linkResult of
                TermIsDead -> go (gas - 1)

                ActiveSubterm link -> do
                  let replaceActiveSubtermWith newthing =
                        replaceWith work link subterm newthing

                  case mredex of
                    MKCall _up _ty callee args kv ca -> do
                      knownFns   <- liftIO $ readIORef (mknFnBinds work)
                      aliases    <- liftIO $ readIORef (mknAliases work)
                      (peekedThroughBitcast, situation) <- classifyRedex callee args knownFns aliases
                      case situation of
                        CallOfNonInlineableFunction fn fnlink -> do
                          ccWhen ccVerbose $ do
                              p <- prettyTermM mredex
                              dbgDoc $ text "CallOfNonInlineableFunction: " <+> p
                          
                          if peekedThroughBitcast
                            then return ()
                            else considerFunctionForArityRaising work fn fnlink callee

                        CallOfUnknownFunction -> do
                          ccWhen ccVerbose $ do
                              p <- prettyTermM mredex
                              dbgDoc $ text "CallOfUnknownFunction: " <+> p
                          return ()

                        CallOfSingletonFunction fn -> do
                          ccWhen ccVerbose $ do
                              redex <- knOfMK (mbContOf $ mkfnCont fn) mredex
                              dbgDoc $ text "CallOfSingletonFunction starting with: " <+> align (prettyT redex)

                          ccWhen ccVerbose $ do
                              v <- freeBinder callee
                              dbgDoc $ green (text "inlining without copying ") <> pretty (tidIdent $ boundVar v)

                          newbody <- betaReduceOnlyCall fn args kv     work

                          dbgDoc $ text "Invoking `replaceWith` for CallOfSingletonFunction"
                          replaceActiveSubtermWith newbody
                          dbgDoc $ text "Killing callee for CallOfSingletonFunction"
                          killBinding callee knownFns aliases
                          -- No need to collect every redex, since the body wasn't duplicated.
                          -- However, arg substitutions should be re-inspected.
                          enqueueOccurrences work args

                        CallOfDonatableFunction fn donations -> do
                          do  redex <- knOfMK (mbContOf $ mkfnCont fn) mredex
                              dbgDoc $ text "CallOfDonatableFunction: " <+> prettyT redex
                          flags <- gets ccFlagVals
                          if getInliningDonate flags
                            then do
                              ccWhen ccVerbose $ do
                                  v <- freeBinder callee
                                  dbgDoc $ blue (text "fnVar: ") <+> pretty (tidIdent $ boundVar $  mkfnVar fn)
                                  dbgDoc $ blue (text "    v: ") <+> pretty (tidIdent $ boundVar v)
                                  dbgDoc $ green (text "copying and inlining DF ") <+> pretty (tidIdent $ boundVar v)
                                  --kn1 <- knOfMKFn (mbContOf $ mkfnCont fn) fn
                                  --dbgDoc $ text $ "pre-copy fn is " ++ show (prettyT kn1)
                                  return ()

                              -- TODO we should really replace the function later on, after we've codegenned the call.
                              -- At this point, only the internal calls exist.

                              -- TODO we should also be more careful about putting cloned global functions in global context,
                              -- OR making sure to localize their names first...
                              do
                                  v <- freeBinder callee
                                  dbgDoc $ blue (text "fnVar fn : ") <+> pretty (tidIdent $ boundVar $ mkfnVar fn)
                                  dbgDoc $ blue (text "callee/v : ") <+> pretty (tidIdent $ boundVar   v)

                              -- TODO Recursive-but-not-tail-recursive functions (RBNTRF)
                              --      will have a recursive call in the body, so we can't
                              --      simply use betaReduceOnlyCall as there's more than 1 call.
                              --
                              --      Most functions will be given loop headers in KNExpr,
                              --      but an un-eliminated loop header within a RBNTRF
                              --      might change the allocation behavior of a program.
                              --      
                              --      If the generated fn' isn't singleton/dead, it should
                              --      be inserted next to the original fn. (TODO)

                              rbntr <- isRecursiveButNotTailRecursive fn
                              newbody <- if rbntr then do
                                            --fn' <- runCopyMKFn fn Map.empty donations
                                            -- We don't modify the known function list, so the recursive call in
                                            -- the copied body will bottom out and not do any loop unrolling.
                                            
                                            dbgDoc $ red $ text "isRecursiveButNotTailRecursive! unroll count before is "
                                                              <> pretty (mkfnUnrollCount fn)
                                            -- We must disable recursive inlining or else we'd infinitely regress!
                                            
                                            -- Note: the conversion between KN and MK doesn't rename
                                            -- variables, so we do so explicitly.
                                            knfn <- knOfMKFn (mbContOf $ mkfnCont fn) $ fn

                                            ccWhen ccVerbose $ do
                                                dbgDoc $ text "post-copy fn is " <> (prettyT knfn)

                                            let sr = MissingSourceRange "CallOfDonatableFunction"
                                            kn'0 <- knLoopHeaders' (KNLetFuns [tidIdent $ fnVar knfn] [knfn] (KNVar $ fnVar knfn) sr)
                                                                  True
                                            let (KNLetFuns [id'0] [knfn'0] _ _sr) = kn'0
                                            id'1 <- case id'0 of
                                                     GlobalSymbol txt _ -> do
                                                        ccFreshId (txt `T.append` T.pack "_ren_")
                                                     _ -> return id'0 -- already renamed!
                                            knfn' <- alphaRenameMonoWithState knfn'0 (Map.fromList [(id'0, id'1)])
                                            dbgDoc $ dullgreen $ text "loop-headered+renamed fn " <> prettyIdent id'1 <> text " is " <> prettyT knfn'

                                            let unrolled = mkfnUnrollCount fn + 1
                                                knownState = [(tidIdent $ boundVar b, b) | (b,_) <- Map.toList knownFns]
                                            --dbgDoc $ text "   known state: " <> prettyT [(id, b) | (id, b) <- knownState]
                                            (_, fn'') <- evalStateT (do
                                                            --bv1 <- genBinder (T.unpack $ identPrefix id'1) (tidType $ fnVar knfn'0)
                                                            --m <- get
                                                            --put $ extend m [id'1] [bv1]
                                                            mkOfKNFn unrolled Nothing (id'1 , knfn')) $
                                              Map.fromList knownState

                                            let vs' = mkfnVars fn''
                                            vs'' <- specializeArgs donations vs'
                                            let fn'3 = fn'' { mkfnVars = vs'' }
                                            
                                            dbgDoc $ blue (text "       id': ") <+> pretty (id'1)
                                            dbgDoc $ blue (text "fnVar fn'': ") <+> pretty (tidIdent $ boundVar $ mkfnVar fn'3)

                                            case id'0 of
                                              GlobalSymbol {} -> do
                                                dbgDoc $ text "TODO: do a better job of handling global symbols by putting them at top-level..."
                                                do  noccs <- dlcCount (mkfnVar fn'3)
                                                    dbgDoc $ text "before createLetFunAndCall, #noccs of " <> pretty id'1 <> text " is " <> pretty noccs
                                                newbody <- createLetFunAndCall fn'3 (mkfnVar fn'3) _ty _up args kv
                                                do  noccs <- dlcCount (mkfnVar fn'3)
                                                    dbgDoc $ text "after createLetFunAndCall, #noccs of " <> pretty id'1 <> text " is " <> pretty noccs
                                                -- Make sure the old occ is dead before specializing.
                                                killOccurrence        work callee
                                                do  noccs <- dlcCount (mkfnVar fn'3)
                                                    dbgDoc $ text "after killing old callee occ, #noccs of " <> pretty id'1 <> text " is " <> pretty noccs
                                                specializeDonatedArgs work fn'3 donations
                                                do  noccs <- dlcCount (mkfnVar fn'3)
                                                    dbgDoc $ text "after specializing donated args, #noccs of " <> pretty id'1 <> text " is " <> pretty noccs
                                                return newbody
                                              _ -> do
                                                -- We reuse the pieces of the original MKCall because it's now dead.
                                                createLetFunAndCall fn'' (mkfnVar fn'') _ty _up args kv
                                          
                                          else do
                                            fn' <- runCopyMKFn fn Map.empty []
                                            betaReduceOnlyCall fn' args kv    work
                                
                              replaceActiveSubtermWith newbody
                              -- No need to kill the old binding, since the body was duplicated.

                              dbgDoc $ green $ text "Replaced donatable call with new body (next: collecting redexes)"
                              ccWhen ccVerbose $ do
                                p <- prettyLinkM newbody
                                dbgDoc $ indent 8 p

                              collectRedexes work newbody

                            else return ()

                        SomethingElse _fn fnlink -> do
                          do  redex <- knOfMK (mbContOf $ mkfnCont _fn) mredex
                              dbgDoc $ text "SomethingElse (inlineNorF): " <+> align (prettyT redex)
                          if shouldInlineRedex mredex _fn ca
                            then do
                                  do  v <- freeBinder callee
                                      dbgDoc $ green (text "copying and inlining SE ") <+> pretty (tidIdent $ boundVar v)
                                      --kn1 <- knOfMK (YesCont mainCont) term
                                      --dbgDoc $ text $ "knOfMK, term is " ++ show (prettyT kn1)
                                  fn' <- runCopyMKFn _fn Map.empty []
                                  newbody <- betaReduceOnlyCall fn' args kv   work
                                  replaceActiveSubtermWith newbody
                                  killOccurrence work callee
                                  collectRedexes work newbody
                            else do
                              if peekedThroughBitcast
                                then return ()
                                else considerFunctionForArityRaising work _fn fnlink callee
                      go (gas - 1)
                    
                    MKCont _up _ty callee args -> do
                      knownFns   <- liftIO $ readIORef (mknFnBinds work)
                      aliases    <- liftIO $ readIORef (mknAliases work)
                      (peekedThroughBitcast, situation) <- classifyRedex callee args knownFns aliases
                      case situation of
                        CallOfUnknownFunction -> do
                          do  cb <- freeBinder callee
                              if T.pack ".fret" `T.isPrefixOf` (identPrefix $ tidIdent $ boundVar cb) 
                                then return ()
                                else do redex <- knOfMK (YesCont mainCont) mredex
                                        dbgDoc $ red (text "CallOfUnknownCont: ") <+> prettyT redex
                          return ()

                        CallOfNonInlineableFunction _fn _fnlink -> do
                          -- Treat non-inlineable functions as if they were unknown.
                          return ()

                        CallOfSingletonFunction fn -> do
                          do  redex <- knOfMK (mbContOf $ mkfnCont fn) mredex
                              dbgDoc $ text "CallOfSingletonCont: " <+> prettyT redex
                              dbgDoc $ text "      #args: " <> pretty (length args)
                          
                              mapM_ (\arg -> do b <- freeBinder arg
                                                c <- mkbCount b
                                                dbgDoc $ text "      pre-beta occ count: " <> pretty c) args

                          do  v <- freeBinder callee
                              dbgDoc $ green (text "      beta reducing (inlining) singleton cont ") <> pretty (tidIdent $ boundVar v)

                          -- If we are substituting a known argument, we should re-examine the
                          -- substituted occurrences, which might have been made reducible.
                          enqueueKnownOccurrences work fn args
                          
                          newbody <- betaReduceOnlyCall fn args callee         work

                          -- If inlining produces a new function call, we should also queue the callee for re-examination,
                          -- since it might have become contifiable.
                          newbodytm <- readLink "CallOfSingletonCont" newbody
                          case newbodytm of
                            MKCall _up _ty newcallee _args _contvar _ca -> do
                              reconsiderForContification work newcallee
                            _ -> return ()
                        
                        --  do newbody' <- knOfMK (mbContOf $ mkfnCont fn) newbody
                        --     dbgDoc $ text "CallOfSingletonCont: new: " <+> pretty newbody'

                          mapM_ (\arg -> do b <- freeBinder arg
                                            c <- mkbCount b
                                            dbgDoc $ text "      pre-kill occ count: " <> pretty c) args

                          replaceActiveSubtermWith newbody
                          killBinding callee knownFns aliases

                          mapM_ (\arg -> do b <- freeBinder arg
                                            c <- mkbCount b
                                            dbgDoc $ text "      post-kill occ count: " <> pretty c) args


                        CallOfDonatableFunction fn _donations -> do
                          do  redex <- knOfMK (mbContOf $ mkfnCont fn) mredex
                              dbgDoc $ text "CallOfDonatableCont: " <+> prettyT redex
                          return ()
                          {-
                          flags <- gets ccFlagVals
                          if getInliningDonate flags
                            then do
                              fn' <- runCopyMKFn fn
                              newbody <- do mk <- betaReduceOnlyCall fn' args kv   work
                                            readLink "CallOfDonatableC" mk
                              replaceActiveSubtermWith newbody
                              killOccurrence bindingWorklistRef callee
                              collectRedexes wr kr er fr fd ar relocDomMarkers newbody
                            else return ()
                            -}
                        SomethingElse _fn _fnlink -> do
                          do  redex <- knOfMK (mbContOf $ mkfnCont _fn) mredex
                              dbgIf dbgCont $ text "SomethingElseC: " <+> prettyT redex
                          if shouldInlineRedex mredex _fn CA_None
                            then do
                                  dbgIf dbgCont $ text "skipping inlining continuation redex...?"
                                  {-
                                  fn' <- runCopyMKFn _fn
                                  newbody <- betaReduceOnlyCall fn' args kv   work  >>= readLink "CallOfDonatable"
                                  replaceActiveSubtermWith newbody
                                  killOccurrence bindingWorklistRef callee
                                  collectRedexes wr kr er fr fd ar relocDomMarkers newbody
                                  -}
                                  return ()
                            else return ()
                      go (gas - 1)

                    MKLetFuns _u knowns fnrest _sr -> do
                      dbgIf dbgCont $ dullyellow $ (text "analyzing for contifiability:")
                          <+> align (vsep (map (pretty.tidIdent.boundVar.fst) knowns))
                      knownFns   <- liftIO $ readIORef (mknFnBinds work)
                      contifiability <- analyzeContifiability knowns knownFns
                      case contifiability of
                        GlobalsArentContifiable -> return ()
                        CantContifyWithNoFn -> do dbgIf dbgCont $ yellow (text "       can't contify with no fn...")
                                                  return ()
                        NoNeedToContifySingleton -> do  dbgIf dbgCont $ yellow (text "       singleton usage, no need to contify")
                                                        return ()
                        HadUnknownContinuations -> do dbgIf dbgCont $ red (text "       had one or more unknown continuations")
                                                      return ()
                        HadMultipleContinuations (tailconts, nontailconts) -> do
                            dbgIf dbgCont $ red (text "       had too many continuations")
                            dbgIf dbgCont $ red (text "       " <> prettyT (tailconts, nontailconts))
                            return ()
                        NoSupportForMultiBindingsYet -> do  dbgIf dbgCont $ red (text "skipping considering " <> pretty (map (tidIdent.boundVar.fst) knowns) <> text " for contification")
                                                            return ()
                        CantContifyNestedTailCalls -> do  dbgIf dbgCont $ red (text "can't contify with nested tail call...")
                                                          return ()
                        ContifyWith cont bv fn occs -> do
                            doContifyWith_part1 cont bv fn occs work
                            doContifyWith_part2 cont [bv] [fn] work mredex fnrest replaceActiveSubtermWith

                        ContifyWithMulti cont bvs_occs_fns -> do
                            mapM_ (\(bv, occs, fn) -> do
                               doContifyWith_part1 cont bv fn occs work
                               ) bvs_occs_fns
                            let (bvs, _, fns) = unzip3 bvs_occs_fns
                            doContifyWith_part2 cont bvs fns work mredex fnrest replaceActiveSubtermWith

                      go (gas - 1)

                    MKCase _up ty v arms -> do
                      x <- freeBinder v
                      expBindsMap <- liftIO $ readIORef (mknKnownExprs work)
                      case Map.lookup x expBindsMap of
                         Nothing -> do
                           dbgDoc $ text "skipping case expression because scrutinee is unknown for " <> prettyT x
                           go gas
                         Just _scrutLink -> do
                           findMatchingArm replaceActiveSubtermWith ty v arms (\v -> do
                                       x <- freeBinder v
                                       case Map.lookup x expBindsMap of
                                         Nothing -> return Nothing
                                         Just link -> readLink "case.scrut" link >>= return . Just)
                           go gas

                    -- Most likely we're re-examining a function that already got optimized
                    -- into a continuation. Nothing more to do here!
                    MKLetCont {} -> go gas

                    _ -> do
                      ccWhen ccVerbose $ do
                          kn <- knOfMK (YesCont mainCont) mredex
                          dbgDoc $ text "skipping non-call/cont redex " <> prettyRootTerm mredex
                                 <$> indent 4 (prettyT kn)
                      go gas

    go origGas

    return ()

enqueueKnownOccurrences work fn args = do
  expBindMap <- liftIO $ readIORef (mknKnownExprs work)
  forM_ (zipSameLength args (mkfnVars fn)) $ \(arg, fnbv) -> do
    bv <- freeBinder arg
    if Map.member bv expBindMap
      then do occs <- collectOccurrences fnbv
              dbgDoc $ text "Enqueueing substituted occs for " <> prettyT fnbv
              liftIO $ modIORef' (mknPendingSubterms work) (\w -> worklistAddList w $ map freeLink occs)
      else do dbgDoc $ text "Not enqueueing substituted occs for " <> prettyT bv
              return ()

-- This is like enqueueSubstitutedOccurrences but it doesn't filter on expBindMap.
enqueueOccurrences work args = do
  let nq arg = do bv <- freeBinder arg
                  occs <- collectOccurrences bv
                  liftIO $ modIORef' (mknPendingSubterms work) (\w -> worklistAddList w $ map freeLink occs)
  mapM_ nq args

doContifyWith_part1 cont bv fn occs work = do
  dbgIf dbgCont $ green (text "       should contify!")

  -- Replace uses of return continuation with common cont target.
  let Just oldret = mkfnCont fn
  -- This may result in additional functions becoming contifiable,
  -- so we collect the uses of the old ret cont first.

  --liftIO $ putDocLn $ text "   substutituing " <> pretty cont <> text " for old ret " <> pretty oldret
  collectRedexesUsingFnRetCont oldret   work
  substVarForVar'' cont oldret

  -- Replacing the Call with a Cont will kill the old cont occurrences.
  mapM_ (\occ -> do
    mb_tm <- readOrdRef (freeLink occ)
    case mb_tm of
      Nothing -> do
        liftIO $ putDocLn $ red (text "WARNING: not contifying call to " <> prettyT (boundVar bv) <> text " due to missing occ term")
        return ()

      Just (MKRelocDoms {}) ->
        return ()

      Just tm@(MKCall uplink ty v vs _cont _ca) -> do
        linkResult <- getActiveLinkFor tm
        case linkResult of
          ActiveSubterm target -> do
            let newterm = MKCont uplink ty v vs -- TODO: kosher to reuse uplink?
            replaceTermWith work target tm newterm
            writeOrdRef (freeLink occ) (Just newterm)
          TermIsDead -> do
            liftIO $ putStrLn $ "WARNING: term is dead..."
            return ()) occs

doContifyWith_part2 _cont bvs fns work mredex fnrest replaceActiveSubtermWith = do
  rdm <- liftIO $ readIORef (mknRelocDoms work)
  let ids = map (tidIdent.boundVar) bvs
  (target, targetrest) <-
      case Map.lookup ids rdm of
        Nothing -> do
          -- We have    fun f = F in fR
          -- and want to end up with
          --           cont f = F in fR
          -- Replace the function with a continuation; be sure to
          -- replace the fn's global ident with a local version!
          return (mredex, fnrest)

        Just targetandrest -> do
          -- We have fun f = F in fR   and somewhere else,   domreloc f in dR
          -- and want to end up with
          --                      fR                         cont f = F in dR
          --
          -- Remove the contified function explicitly
          _ <- replaceActiveSubtermWith fnrest
          return targetandrest

  linkResult <- getActiveLinkFor target
  case linkResult of
    ActiveSubterm link -> do
      contfns <- mapM (\(fn, bv) -> mkKnown' bv $ fn { mkfnCont = Nothing }) (zip fns bvs)
      let letcont = MKLetCont (parentLinkT target) contfns targetrest
      replaceTermWith work link target letcont
    TermIsDead -> return ()

-- A function is eligible for arity raising if every usage is a call
-- (no higher-order usages) and every call passes a known tuple.
--
considerFunctionForArityRaising work fn fnlink callee = do
  expBindsMap <- liftIO $ readIORef (mknKnownExprs work) -- for looking up tuple params
  calleeb <- freeBinder callee
  occs <- collectOccurrences calleeb
  directs <- mapM (isDirectCallWithKnownTupleArg expBindsMap calleeb) occs
  if allSameNonZeroLength directs
    then do -- Replace each call site to pass the tuple parameters instead of the tuple.
            mapM_ (\ (DC_WithTuple calltm tupleparts) -> do
              case calltm of
                MKCall uplink ty v _tup sr ca -> do
                  linkResult <- getActiveLinkFor calltm
                  case linkResult of
                    ActiveSubterm target -> do
                      tupleparts' <- mapM (\fv -> freeBinder fv >>= mkFreeOccForBinder) tupleparts
                      let newterm = MKCall uplink ty v tupleparts' sr ca -- TODO: kosher to reuse uplink?
                      replaceTermWith work target calltm newterm
                    _ -> do
                      return (error "skipping call because we didn't find an active subterm (!?)")
                _ -> error $ "line 1782 invariant violated") directs

            let createFnArg (n, bv) = do
                  genBinderAndOcc ("_" ++ show n ++ ".tuparity") (tidType (boundVar bv))


            let (DC_WithTuple _ tupleparts) = head directs
            tupleparts_bvs <- mapM freeBinder tupleparts
            newArgsAndOccs <- evalStateT (mapM createFnArg (zip [0..] tupleparts_bvs)) Map.empty
            let (newArgs, newOccs) = unzip newArgsAndOccs

            -- The body of the arity-raised function should construct a tuple
            -- out of the new function parameters, for the existing body to use.
            let tupbnd = head (mkfnVars fn)
            let tuptyp = tidType (boundVar tupbnd)
            tnu <- newOrdRef Nothing
            nu  <- newOrdRef Nothing
            let tupexp = MKTuple tnu tuptyp newOccs (MissingSourceRange "tup")
            tuplink <- newOrdRef (Just tupexp)
            let letval = MKLetVal nu (mkKnownE tupbnd tuplink) (mkfnBody fn)
            vallink <- newOrdRef (Just letval)
            backpatchE letval [tuplink]
            _ <- backpatchT letval [mkfnBody fn]
            let newbody = vallink

            let fnvar = boundVar (mkfnVar fn)
            let newfntype = case tidType fnvar of
                              FnType [_] rng cc pf ->
                                FnType (map (tidType.boundVar) tupleparts_bvs) rng cc pf
                              _ -> error "expected arity-raised function to have single-arg function type?!?"

            -- We can't (yet) change the local identifier the function is bound to, so if we generated a new
            -- identifier here, we'd encounter errors later in codegen due to the mismatch. Instead, we carefully
            -- reuse the existing identifier (ew).
            newcbvar <- evalStateT (mkBinder (TypedId newfntype (tidIdent (boundVar calleeb)))) Map.empty

            -- Different issue here: the backend special-cases function entry basic blocks based on name.
            newfnid  <- ccRefreshLocal (tidIdent $ boundVar (mkfnVar fn))
            newfnvar <- evalStateT (mkBinder (TypedId newfntype newfnid)) Map.empty

            -- Make sure we examine the tuple for subsequent optimizations (e.g. case-of-tuple elimination).
            liftIO $ modIORef' (mknDeadBindings work) (\w -> worklistAdd w tupbnd)
            liftIO $ modIORef' (mknKnownExprs work) (\m -> Map.insert tupbnd tuplink m)

            -- Apply variable substitutions to ensure the new types take effect.
            substVarForVar''  newfnvar (           mkfnVar  fn)
            substVarForVar''  newcbvar calleeb

            -- Replace the original function with an arity-raised version.
            let newfn =
                  MKFn { mkfnVar   = newfnvar
                       , mkfnVars  = newArgs
                       , mkfnCont  = mkfnCont fn
                       , mkfnBody  = newbody
                       , mkfnIsRec = (mkfnIsRec fn)
                       ,_mkfnAnnot = (_mkfnAnnot fn)
                       , mkfnUnrollCount = (mkfnUnrollCount fn)
                       }
            writeOrdRef fnlink (Just newfn)
    else do dbgDoc $ text "not all calls with known tuples"
            return ()

data DirectCallWithTupleArg = DC_WithTuple (MKTerm MonoType) [FreeVar MonoType]
                            | DC_Other

allSameNonZeroLength [] = False
allSameNonZeroLength (d:rest)= go rest (tupLen d)
  where go [] len = len > 0
        go (d:rest) len = if tupLen d == len
                            then go rest len
                            else False
        tupLen (DC_WithTuple _ vs) = length vs
        tupLen _ = 0

isDirectCallWithKnownTupleArg expBindsMap fnvar occ = do
  mb_tm <- readOrdRef (freeLink occ)
  case mb_tm of
    Just tm@(MKCall _ _ v [arg] _ _ca) -> do
      vb <- freeBinder v
      va <- freeBinder arg
      if vb /= fnvar then return DC_Other else
          case Map.lookup va expBindsMap of
            Nothing -> return $ DC_Other
            Just link -> do
              e <- readLink "isDirectCall.Exp" link
              case e of
                 MKTuple  _u _ vs _sr | not (null vs) -- No point in arity-raising unit values.
                   -> return $ DC_WithTuple tm vs
                 _ -> return DC_Other
    _ -> return DC_Other

-- Checks the given function to see if it has any occurrences which are calls
-- that use a different return continuation than the function itself.
isRecursiveButNotTailRecursive fn = do
  occs <- collectOccurrences (mkfnVar fn)
  isRecAndNotTailRec <- mapM (\occ -> do
      tm <- readLink "isRecursiveButNotTailRecursive" (freeLink occ)
      case tm of
        MKCall _ _ v _ k _ca -> do
          vb <- freeBinder v
          kb <- freeBinder k
          -- Probably need to also make sure the args don't mention the fn var.
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
  _ <- installLinks callLink $ MKCall up' ty callee args' kv' CA_None

  known <- mkKnown' outerBinder fn
  letfuns <- backpatchT (MKLetFuns up [known] callLink (MissingSourceRange "outerbinder")) [callLink]
  newOrdRef (Just letfuns)

collectRedexesUsingFnRetCont oldret    work = do
  occs <- collectOccurrences oldret
  mb_callees <- mapM calleeOfCont occs

  fndefs <- liftIO $ readIORef (mknFnDefs work)
  mapM_ (\calleeBV -> do
      case Map.lookup calleeBV fndefs of
        Nothing -> return ()
        Just tm -> liftIO $ modIORef' (mknPendingSubterms work) (\w -> worklistAdd w tm)
    ) [c | Just c <- mb_callees]

findParentFn tm = do
  parent <- readLink "findParentFn" (parentLinkT tm)
  case parent of
    ParentTerm t -> findParentFn t
    ParentFn f -> return f

-- We need to make sure we ignore trivial rebindings, which might
-- otherwise prevent us from recognizing contifiable functions.
peekTrivialCont knownFns bv = do
    mb_fn <- lookupBinding' bv knownFns
    case mb_fn of
      Nothing -> return bv -- No known continuation; nothing else to do.
      Just cf -> do
        bodytm <- readLink "analyzeContifiability" (mkfnBody cf)
        case bodytm of
          MKCont _u _ty dv fvs -> do
            binders <- mapM freeBinder fvs
            if binders == mkfnVars cf
              then do -- If we a have a call (foo ...) returning to cont C,
                      -- and C x = D x, then replace the call's cont with D.
                      db <- freeBinder dv
                      substVarForBound (dv, bv)
                      return db
              else return bv -- Reordered parameters, uh oh!
          _ -> return bv -- The cont body is non-trivial.



data Contifiability =
    GlobalsArentContifiable
  | NoNeedToContifySingleton
  | HadUnknownContinuations
  | HadMultipleContinuations ( [MKBoundVar MonoType] , [MKBoundVar  MonoType] )
  | CantContifyNestedTailCalls
  | CantContifyWithNoFn
  | NoSupportForMultiBindingsYet
  | ContifyWith (MKBound MonoType)
                (MKBound MonoType)
                (MKFn (Subterm MonoType) MonoType)
                [FreeOcc MonoType]
  | ContifyWithMulti (MKBound MonoType)
              [((MKBound MonoType)
              , [FreeOcc MonoType]
              , (MKFn (Subterm MonoType) MonoType))]

analyzeContifiability :: [Known MonoType (Link (MKFn (Subterm MonoType) MonoType))]
            -> (Map (MKBoundVar MonoType) (Link (MKFn (Subterm MonoType) MonoType)))
            -> Compiled Contifiability
analyzeContifiability knowns knownFns = do
  let isTopLevel (GlobalSymbol _ _) = True
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
              mapM_ (\occ -> do
                kont <- contOfCall bv occ
                case kont of
                  HigherOrder  -> dbgIf dbgCont $ text "       (higher order)"
                  NonCall      -> dbgIf dbgCont $ text "       (non-call)"
                  FoundCont {} -> dbgIf dbgCont $ text "       (found cont)"
                  FakeUsage    -> dbgIf dbgCont $ text "       (fake usage from MKRelocDoms)"

                mb_tm <- readOrdRef (freeLink occ)
                case mb_tm of
                  Nothing -> do dbgIf dbgCont $ text "    no occ??"
                                return ()
                  Just tm -> do when dbgCont $ do
                                    p <- prettyTermM tm
                                    dbgDoc $ text "    occ: " <> prettyRootTerm tm <$> indent 2 p
                                return ()) occs
              case allFoundConts mbs_conts of
                Nothing -> return HadUnknownContinuations
                Just rawConts -> do
                  conts <- mapM (peekTrivialCont knownFns) rawConts
                  let (tailconts, nontailconts) = partitionEithers $
                        [if Just bv == mkfnCont fn
                          then Left bv else Right bv
                        | bv <- removeDuplicates conts]
                  dbgIf dbgCont $ yellow (text "       had just these conts: ")
                                        <$> text "               all conts: " <> pretty (map (tidIdent.boundVar) conts)
                                        <$> text "              tail calls: " <> pretty (map (tidIdent.boundVar) tailconts)
                                        <$> text "          non-tail calls: " <> pretty (map (tidIdent.boundVar) nontailconts)
                  case (tailconts, nontailconts) of
                    ((_:_:_), _) -> return $ HadMultipleContinuations (tailconts, nontailconts) -- Multiple tail calls: no good!
                    (_ ,  [cont]) -> do -- Happy case: zero or one tail call, one outer continuation.
                         return (ContifyWith cont bv fn occs)
                    _ -> return $ HadMultipleContinuations (tailconts, nontailconts) -- Multiple outer continuations: no good!

        _ -> do
          let bvs     = map fst knowns
              fnlinks = map snd knowns
          mb_fns <- mapM readOrdRef fnlinks
          occss <- mapM collectOccurrences bvs
          let combinedOccs = concat occss

          mbs_retconts <- mapM (\mb_fn -> do
              case mb_fn of
                Nothing -> return Nothing
                Just fn -> return $ mkfnCont fn) mb_fns
          let retconts = [c | Just c <- mbs_retconts]

          liftIO $ putDocLn $ text "recursive nest: {{{"

          mbs_parentFns <- mapM (\occ -> do
              mb_tm <- readOrdRef (freeLink occ)
              case mb_tm of
                Nothing -> do return $ Nothing
                Just tm -> do findParentFn tm >>= return . Just
              ) combinedOccs
          let allSame = case map (tidIdent.boundVar.mkfnVar) [pf | Just pf <- mbs_parentFns] of
                          []  -> True
                          [_] -> True
                          (id:rest) -> List.all (== id) rest
          liftIO $ putDocLn $ text "        all same parent? " <> pretty allSame

          -- Describe/debug print situation.
          mapM_ (\ (occs, bv, mb_fn) -> do
            case occs of [_] -> liftIO $ putDocLn $ text "   (is  singleton)"
                         _   -> liftIO $ putDocLn $ text "   (not singleton)"

            --liftIO $ putDocLn $ text "   occ:"
            --mapM_ (\occ -> do
            --  mb_tm <- readOrdRef (freeLink occ)
            --  case mb_tm of
            --    Nothing -> do
            --      liftIO $ putDocLn $ text "      no term"
            --    Just tm -> do
            --      --do kn <- knOfMK NoCont tm
            --      --   liftIO $ putDocLn $ text "      " <> prettyT kn
            --      --parentFn <- findParentFn tm
            --      --liftIO $ putDocLn $ text "      parent: " <> pretty (boundVar $ mkfnVar parentFn)
            --  ) occs



            case mb_fn of
              Nothing -> do
                liftIO $ putDocLn $ text "    no fn"
              Just _fn -> do
                aconts <- mapM (contOfCall bv) occs
                case allFoundConts aconts of
                  Nothing -> liftIO $ putDocLn $ text "  (some continuations not found)"
                  Just conts -> do
                             liftIO $ putDocLn $ text "  (all continuations found)"
                             let (tailconts, nontailconts) = partitionEithers $
                                                    [if bv `elem` retconts
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
          splitContss <- mapM (\ (occs, bv, mb_fn) -> do
            case mb_fn of
              Nothing -> do return ([], [])
              Just _fn -> do
                aconts <- mapM (contOfCall bv) occs
                case allFoundConts aconts of
                  Nothing -> return ([], [])
                  Just conts -> do
                             let (tailconts, nontailconts) = partitionEithers $
                                                    [if bv `elem` retconts
                                                      then Left bv else Right bv
                                                    | bv <- Set.toList $ Set.fromList conts]
                             return (tailconts, nontailconts)
            ) (zip3 occss bvs mb_fns)

          let (tailcontss, nontailcontss) = unzip splitContss
          liftIO $ putDocLn $ text "  tails:    " <> prettyT (removeDuplicates (concat tailcontss))
          liftIO $ putDocLn $ text "  nontails: " <> prettyT (removeDuplicates (concat nontailcontss))

          liftIO $ putDocLn $ text "}}}"

          let fns = [f | Just f <- mb_fns]
          case removeDuplicates (concat nontailcontss) of
            nt@(_:_:_) -> do
              liftIO $ putDocLn $ text "(recursive nest had too many non-tail continuations)"
              return $ HadMultipleContinuations ( nt, removeDuplicates (concat tailcontss) )

            [] -> do
              liftIO $ putDocLn $ text "(recursive nest had zero non-tail continuations)"
              return $ HadMultipleContinuations ( [], removeDuplicates (concat tailcontss) )

            [cont] ->
              if allSame
                then do
                  liftIO $ putDocLn $ text "(no support for relocating recursive nests yet)"
                  return $ NoSupportForMultiBindingsYet
                else do
                  return (ContifyWithMulti cont (zip3 bvs occss fns))
                  --return $ NoSupportForMultiBindingsYet

          -- TODO for contifiable nests, determine whether the calls all come from
          -- within one of the functions in the nest; if so, the contified functions
          -- should be relocated there (header/census rewrites wouldn't have relocated
          -- the function). Otherwise, contify as usual.

-- Collect the list of occurrences for the given binder,
-- but "peek through" any bitcasts.
collectOccurrences :: MKBoundVar t -> Compiled [FreeOcc t]
collectOccurrences bv = do
  inits <- dlcToList bv
  initss <- mapM (\fv -> do
                mb_tm <- readOrdRef (freeLink fv)
                case mb_tm of
                  -- If we don't ignore MKRelocDoms here, we wind up with miscompilations
                  -- because contified functions that were relocated will be kept alive
                  -- by the MKRelocDoms node, and will fail codegen due to missing labels.
                  Just (MKRelocDoms {}) -> do
                    return []

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

allFoundConts [] = Just []
allFoundConts (HigherOrder  : _) = Nothing
allFoundConts (NonCall      : _) = Nothing
allFoundConts (FakeUsage    :xs) = allFoundConts xs
allFoundConts (FoundCont x _:xs) = 
  case allFoundConts xs of
    Nothing -> Nothing
    Just res -> Just (x:res)

data FoundCont =
    FoundCont    (MKBoundVar MonoType) Bool -- False if fn; True if cont (!)
  | HigherOrder
  | NonCall
  | FakeUsage

-- Collect the continuations associated with every use of the function binding.
contOfCall bv occ = do
  mb_tm <- readOrdRef (freeLink occ)
  case mb_tm of
    Nothing -> do
        do dbgDoc $ red $ text "contOfCall: free link w/ no term for" <> prettyT bv
        return NonCall

    Just tm@(MKCall _ _ty v _vs cont _ca) -> do
        vb <- freeBinder v
        if vb == bv
          then -- It's a call to the function being considered
            do cv <- freeBinder cont
               return $ FoundCont cv False
          else -- It's a call to some other function, our function is one of its args.
                -- We could possibly contify if we knew whether the callee will only
                -- tail call our function, but as of yet we don't track that information.
            do ccWhen ccVerbose $ do
                  p <- prettyTermM tm
                  dbgDoc $ text "contOfCall: call w/ unknown cont for" <> prettyT bv <> text ":" <> indent 10 p
               return $ HigherOrder

    Just (MKCont _ _ cont _vs) -> do
        vb <- freeBinder cont
        if vb == bv
          then -- It's a continuation (!!!) call to the function being considered
            do return $ NonCall --FoundCont vb True
          else 
            do return $ HigherOrder

    Just (MKRelocDoms {}) -> do
      return FakeUsage

    Just tm -> do
      when dbgCont $ do
        p <- prettyTermM tm
        dbgDoc $ text "contOfCall: non call w/ unknown cont " <> parens (prettyRootTerm tm)
                         <> text " for " <> yellow (prettyT bv) <> text ":" <> indent 10 p
        --dbgDoc $ indent 10 (showStructure kn)

      return NonCall

-- Collect the function vars associated with every use of a continuation variable.
calleeOfCont occ = do
  bv <- freeBinder occ
  mb_tm <- readOrdRef (freeLink occ)
  case mb_tm of
    Nothing -> do
        do dbgDoc $ red $ text "free link w/ no term for cont " <> prettyT bv
        return Nothing

    Just (MKCall _ _ty v _vs _cont _ca) -> do
        bv <- freeBinder v
        return $ Just bv
                  
    Just tm -> do
      ccWhen ccVerbose $ do
          p <- prettyTermM tm
          dbgDoc $ text "calleeOfCont: non call for" <> prettyT bv <> text ":" <> indent 10 p
      return Nothing

specializeDonatedArgs work fn donations = do
  let callee = mkfnVar fn
      wr = mknPendingSubterms work

  occs <- collectOccurrences callee
  mapM_ (\occ -> do
    Just tm <- readOrdRef (freeLink occ)
    case tm of
      MKCall uplink ty v vs c ca -> do
        bv <- freeBinder v
        if bv == callee
          then do status <- getActiveLinkFor tm
                  case status of
                    TermIsDead -> return ()
                    ActiveSubterm link -> do
                      let (_, vars) = matchArgs donations vs
                      -- Create a new call node which drops specialized args.
                      let newterm = MKCall uplink ty v vars c ca
                      dbgDoc $ yellow $ text "specializeDonatedArgs specializing call:"
                      replaceTermWith work link tm newterm
          else return ()
    ) occs

  -- Note: assuming here that copyMKFn already called specializeArgs.
  let donatedVals = map snd donations
  mapM_ (\donVal -> do
    -- Make sure that the usages of the values that were substituted
    -- by specializeArgs are re-examined.
    bv <- freeBinder donVal
    occs <- collectOccurrences bv
    mapM_ (\occ -> do
        let link = freeLink occ
        -- "markRedex" in collectRedexes
        -- do dbgDoc $ text "specializeDonatedArgs marking occ of " <> pretty bv
        --    prettyLinkM link >>= (\p -> dbgDoc $ indent 2 p)
        liftIO $ modIORef' wr (\w -> worklistAdd w link)
      ) occs
                      
    ) donatedVals

shouldInlineRedex _mredex _fn ca =
  -- TODO use per-call-site annotation, when we have such things.
  {-
  let id = tidIdent (boundVar (mkfnVar _fn)) in
  T.pack "doinline_" `T.isInfixOf` identPrefix id
  -}
  case ca of
    CA_DoInline -> True
    CA_NoInline -> False
    CA_None -> False

replaceWith :: PrettyT ty => MKNInlineState ty -> Subterm ty ->
               Subterm ty -> Subterm ty -> Compiled ()
replaceWith work activeLink poss_indir_target newsubterm = do
  oldterm <- readLink "replaceWith" poss_indir_target
  newterm <- readLink "replaceWith" newsubterm
  replaceTermWith work activeLink oldterm newterm
  writeOrdRef poss_indir_target     (Just newterm)

replaceTermWith :: PrettyT ty => MKNInlineState ty -> Subterm ty ->
                   MKTerm ty -> MKTerm ty -> Compiled ()
replaceTermWith work activeLink oldterm newterm = do
  ccWhen ccVerbose $ do
    po <- prettyTermM oldterm
    pn <- prettyTermM newterm
    dbgDoc $ blue (text "replacing") <$> indent 8 po <$> indent 2 (text "with") <$> indent 8 pn

  writeOrdRef activeLink           (Just newterm)

  let oldoccs = directFreeVarsT oldterm
  let newoccs = directFreeVarsT newterm
  mapM_ (killOccurrence work) (oldoccs `butnot` newoccs)
  mapM_ (\fv -> setFreeLink fv newterm) newoccs
  readOrdRef (parentLinkT oldterm) >>= writeOrdRef (parentLinkT newterm)

killOccurrence :: PrettyT ty => MKNInlineState ty ->
                  FreeVar ty -> Compiled ()
killOccurrence work fo = do
    b@(MKBound _v r) <- freeBinder fo -- r :: OrdRef (Maybe (FreeOcc tyx))

    isSingleton <- freeOccIsSingleton fo
    if isSingleton
     then do
       ccWhen ccVerbose $ do
         dbgDoc $ red (text "killing singleton binding ") <> prettyId _v
       writeOrdRef r Nothing
       liftIO $ modIORef' (mknDeadBindings work) (\w -> worklistAdd w b)
     else do
       dbgDoc $ text "killing occurrence of " <> prettyT b
       nob <- dlcCount b
       dbgDoc $ text "num occs before: " <> pretty nob
       n <- dlcNext fo
       p <- dlcPrev fo
       writeOrdRef (dlcNextRef p) n
       writeOrdRef (dlcPrevRef n) p

    -- Make sure binder doesn't point to ``fo``.
    mb_fo' <- readOrdRef r
    case mb_fo' of
      Just fo' | dlcIsSameNode fo fo' -> do
        if isSingleton
          then writeOrdRef r Nothing
          else do fo'' <- dlcNext fo
                  writeOrdRef r $ Just fo''
      _ -> return ()

    noa <- dlcCount b
    dbgDoc $ text "num occs after: " <> pretty noa

killBinding fo knownFns aliases = do
    origBinding <- freeBinder fo
    let binding@(MKBound v r') =
            case Map.lookup origBinding aliases of
                    Nothing -> origBinding
                    Just bv -> bv
    ccWhen ccVerbose $ do
      dbgDoc $ red (text "killing binding for ") <> prettyT (boundVar origBinding) <> text " ~~> " <> prettyT v
    writeOrdRef r' Nothing
    case Map.lookup binding knownFns of
        Nothing -> do dbgDoc $ red (text "no killable binding for ") <> prettyT v
                      return ()
        Just r  -> writeOrdRef r Nothing

lookupBinding fo m = do
    binding <- freeBinder fo
    lookupBinding' binding m

lookupBinding' binding m = do
    case Map.lookup binding m of
      Nothing   -> return Nothing
      Just link -> readOrdRef link

zipSameLength = zip


matchArgs donations vs0 =
  let match [] [] acc = reverse acc
      match [] ((_,v):vs) acc = match [] vs (Right v:acc)
      match d@((n, arg):rest) ((m,v):vs) acc = do
              case () of
                _ | n >  m ->
                  match d    vs ((Right v):acc)
                _ | n == m ->
                  match rest vs ((Left (arg, v)):acc)
                _ | n <  m ->
                  error $ "how did we get n < m ???"    
  in partitionEithers $ match donations (zip [0..] vs0) []

-- Return the args that were not specialized.
specializeArgs :: (PrettyT t) =>
                  [(Int, FreeOcc t)]
               -> [MKBoundVar t]
               -> Compiled [MKBoundVar t]
specializeArgs donations vs0 = do
  let (matches, vars) = matchArgs donations vs0
  mapM_ substVarForBound matches
  return vars

betaReduceOnlyCall :: MKFn (Subterm MonoType) MonoType
                      -> [FreeVar MonoType]
                      ->  ContVar MonoType
                      -> MKNInlineState MonoType
                      -> Compiled (Link (MKTerm MonoType))
betaReduceOnlyCall fn args kv    work = do
    mapM_ substVarForBound (zip args (mkfnVars fn))
    kvb1 <- freeBinder kv

    case mkfnCont fn of
      Nothing -> return ()
      Just oldret -> do
        collectRedexesUsingFnRetCont oldret work
        -- This may result in additional functions becoming contifiable,
        -- so we collect the uses of the old ret cont first.
        substVarForBound (kv, oldret)

    kvb2 <- freeBinder kv
    dbgDoc $ text "      betaReduceOnlyCall on " <> prettyT (mkfnVar fn)
    if kvb1 /= kvb2
      then do
        dbgDoc $ text "       kv before: " <> prettyT kvb1
        dbgDoc $ text "       kv after: " <> prettyT kvb2
      else return ()
    dbgDoc $ text "      fn kv: " <> prettyT (mkfnCont fn)
    return $ mkfnBody fn

-- TODO: ok this seems to work, more or less.
--          Implement contification & other optimizations...




baFresh :: T.Text -> BlockAccum BlockId
baFresh txt = do u <- freshLabel;
                 return {- (trace ("new label " ++ show u ++ " for string " ++ s) -} (txt, u)

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
            lift $ ccWhen ccVerbose $ do
              dbgDoc $ text "pccOfTopTerm saw nulled-out function link " <> prettyT x
            return ()
          Just fn -> do
            {-
            do
              knfn <- lift $ knOfMKFn NoCont fn
              dbgIf dbgFinal $ indent 10 (pretty x)
              dbgIf dbgFinal $ indent 20 (prettyT knfn)
              dbgIf dbgFinal $ text "~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~"
              dbgIf dbgFinal $ yellow $ pretty (mkfnVar fn)
              -}

            dbgDoc $ text "cffnOfMKFn from link # " <> pretty (ordRefUniq link)
            cffn <- lift $ cffnOfMKFn uref fn x
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
          MKLetFuns     _u   knowns  k _sr -> do mapM_ grabFn knowns ; go k
          MKCall        {}              -> return ()
          MKLetCont _ [(kb,c)] subterm2 -> do
            isDead  <- lift $ binderIsDead kb
            if isDead then go subterm2
              else error $ show $ text "MKLetCont in pccTopTerm, known: " <> prettyT (map (tidIdent.boundVar.fst) [(kb,c)])

          MKLetCont _ knowns _subterm2 -> do
                                 --subtm <- lift $ readLink "pccOfTopTerm(subterm2)" subterm2
                                 --kn <- lift $ knOfMK NoCont subtm
                                 error $ show $ "MKLetCont in pccTopTerm, knowns: " <> prettyT (map (tidIdent.boundVar.fst) knowns)
          MKCont        {} -> do error $ "MKCont in pccTopTerm"
          MKRelocDoms   {} -> do error $ "MKRelocDoms in pccTopTerm"

      handleTopLevelBinding id expr k = do
        case expr of
          MKLiteral _ ty lit -> do !(fns, topbinds) <- get
                                   put (fns, TopBindLiteral id ty lit : topbinds)
                                   go k

          -- TODO handle top-level records (?)

          MKTuple     _ ty fvs _sr -> do
                                   !(fns, topbinds) <- get
                                   bvs <- lift $ mapM freeBinder fvs
                                   let ids = map (tidIdent . boundVar) bvs
                                   put (fns, TopBindTuple id ty ids : topbinds)
                                   go k

          MKAppCtor  _ ty (cid, crep) fvs _sr -> do
                                   !(fns, topbinds) <- get
                                   bvs <- lift $ mapM freeBinder fvs
                                   let ids = map (tidIdent . boundVar) bvs
                                   put (fns, TopBindAppCtor id ty (cid, crep) ids : topbinds)
                                   go k

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
      blockid <- baFresh (identPrefix id)
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
cffnOfMKCont cv (MKFn _v vs _ subterm _isrec _annot _unrollCount) = do
  headerBlockId <- blockIdOf cv
  let head = ILabel (headerBlockId, map boundVar vs)
  dbgDoc $ text "cffnOfMKCont head = " <> prettyT head
  dbgDoc $ text "cffnOfMKCont cv == " <> prettyT (boundVar cv)
  dbgDoc $ text "                ~~ " <> prettyT (tidType (boundVar cv))
  dbgDoc $ text "cffnOfMKCont  v == " <> prettyT (boundVar _v)
  dbgDoc $ text "                ~~ " <> prettyT (tidType (boundVar _v))
  dbgDoc $ text "cffnOfMKCont vs = " <> align (vsep (map (prettyT.boundVar) vs))

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
          MKRelocDoms _u _ids k -> go k head insns
          MKLetVal      _u (bv, subexpr) k -> do
              letable <- lift $ letableOfSubexpr subexpr
              isDead  <- lift $ binderIsDead bv
              if isDead && isPure letable
                then go k head insns
                else go k head (ILetVal (tidIdent $ boundVar bv) letable : insns)
          MKLetRec      _u  [_known] _k -> do error $ "MKNExpr.hs: no support yet for MKLetRec..."
          MKLetRec      _u  _knowns  _k -> do error $ "MKNExpr.hs: no support yet for multi-extended-letrec"
          MKLetFuns     _u   knowns  k _sr -> do
                                              (uref, _, _) <- get
                                              idsfnss <- lift $ mapM (\(bv,link) -> do
                                                  mb_mkfn <- readOrdRef link
                                                  case mb_mkfn of
                                                    Nothing -> do
                                                      dbgDoc $ text "cffnOfMKCont removed dead fn: " <> prettyT (tidIdent $ boundVar bv)
                                                      return []
                                                    Just mkfn -> do
                                                      dbgDoc $ text "read fn from link # " <> pretty (ordRefUniq link)
                                                      cffn <- cffnOfMKFn uref mkfn bv
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
                                                     lift $ ccWhen ccVerbose $ do
                                                       dbgDoc $ text "cffnOfMKCont removed dead continuation " <> prettyT (tidIdent $ boundVar bv)
                                                   Just contfn -> do
                                                     cffnOfMKCont bv contfn)
                                               knowns
                                             -- then resume building this particular block.
                                             go k head insns

          MKCall        _u ty v vs contvar _ca -> do
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
                                 let trueArm = CaseArm (pat True)  blockIdTrue Nothing Seq.empty (MissingSourceRange "if.true")
                                 let falsArm = CaseArm (pat False) blockIdFals Nothing Seq.empty (MissingSourceRange "if.fals")
                                 --dbgDoc $ text $ "putting block with ending case (if) " ++ show (tidIdent $ boundVar cv)
                                 v' <- qv v
                                 baPutBlock head insns (CFCase v' [trueArm, falsArm])

          MKCase        _u _ty v arms -> do
                                 v' <- qv v
                                 arms' <- mapM (\(MKCaseArm pat subterm bindings range) -> do
                                                blockid <- generateBlock "case.arm" {-bindings-} [] subterm
                                                --dbgDoc $ text $ "bindings for " ++ show blockid ++ " are " ++ show (map (tidIdent. boundVar) bindings)
                                                return $ CaseArm pat blockid Nothing (fmap boundVar bindings) range) arms
                                 baPutBlock head insns (CFCase v' arms')
          -- arms  :: MKCaseArm (PatternRepr) (Subterm _)
          -- arms' :: CaseArm PatternRepr BlockId MonoType

      generateBlock name vars subterm = do
          id <- lift $ ccFreshId $ T.pack name
          blockid <- blockIdOfIdent id

          ref <- lift $ newOrdRef Nothing
          let vx = MKBound (TypedId (TyApp (TyCon "Bool") []) id) ref

          cffnOfMKCont vx (MKFn vx vars Nothing subterm _isrec _annot _unrollCount)
          return blockid

cffnOfMKFn :: IORef Uniq -> MKFn (Subterm MonoType) MonoType -> MKBoundVar MonoType -> Compiled CFFn
cffnOfMKFn uref (MKFn v vs (Just cont) term isrec annot unrollCount) bv = do
  -- Generate a pseudo-entry continuation to match Hoopl's semantics for graphs.


  (rk, st) <- runStateT (blockIdOf cont) (uref, Map.empty, [])
  (_,_,blocks) <- execStateT
        (cffnOfMKCont v (MKFn v vs Nothing term isrec annot unrollCount))
        st

  --dbgDoc $ text $ "# blocks for " ++ show (tidIdent $ boundVar v) ++ " = " ++ show (length allblocks)

  let graph  = catClosedGraphs (map blockGraph blocks)

  --dbgDoc $ vcat (map pretty allblocks)
  --dbgDoc $ indent 20 (pretty graph)

  noccsI <- dlcCount v
  noccsE <- dlcCount bv
  dbgDoc $ blue $ text "converted function " <> prettyT v <> text ", type is " <> prettyT (tidType (boundVar v))
    <+> text "    #occs = " <> pretty (noccsI, noccsE)
  showOccsOfBinder bv

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
    MKRecord      _ _ty _labs vars sr -> do
                                     vars' <- mapM qv vars
                                     return $ ILTuple KindPointerSized vars' (AllocationSource "record" sr)

    MKTuple       _ ty vars sr -> do vars' <- mapM qv vars
                                     case ty of
                                       StructType {} ->
                                            return $ ILTuple KindAnySizeType  vars' (AllocationSource "tuple" sr)
                                       _ -> return $ ILTuple KindPointerSized vars' (AllocationSource "tuple" sr)
    MKKillProcess _ ty txt     -> return $ ILKillProcess ty txt
    MKCallPrim    _ ty p vs _r -> do vs' <- mapM qv vs
                                     return $ ILCallPrim ty p vs'
    MKAppCtor     _ ty cid vs sr -> do vs' <- mapM qv vs
                                       return $ ILAppCtor ty cid vs' sr
    MKAlloc       _ _ty v amr sr -> do v' <- qv v
                                       return $ ILAlloc {-ty-} v' amr sr
    MKDeref       _ ty v      -> qv v >>= \v' -> return $ ILDeref ty v'
    MKStore       _ _t v v2   -> mapM qv [v, v2] >>= \[v',v2'] -> return $ ILStore v' v2'
    MKAllocArray  _ ty v amr zi sr -> qv v >>= \v' -> return $ ILAllocArray ty v' amr zi sr
    MKArrayRead   _ ty ari    -> qa ari >>= \ari' -> return $ ILArrayRead ty ari'
    MKArrayPoke   _ _ty ari v -> qa ari >>= \ari' ->
                                 qv v   >>= \v' -> return $ ILArrayPoke {-ty-} ari' v'
    MKArrayLit    _ ty v elts -> qv v   >>= \v' ->
                                 mapM qelt elts >>= \elts' -> return $ ILArrayLit ty v' elts'
    MKTyApp       _ ty v [] -> qv v >>= \v' -> return $ ILBitcast ty v'
    MKTyApp       {} -> error $ "MKNExpr saw tyapp that wasn't eliminated by monomorphization"
    _ -> error $ "non-Letable thing seen by letableOfSubexpr..."


--  * A very important pattern to inline is     iter x { E2 },
--    which ends up looking like    f = { E2 }; iter x f;
--    with f not referenced elsewhere.  Even if E2 is big enough
--    that we wouldn't usually inline it, given the body of iter,
--    if this is the only place f is used, we ought to inline it anyways.
--      (We rely on contification to Do The Right Thing when iter calls f once).
--    The literature identifies this as a fruitful optimization when ``iter`` is
--    a single-use function, but not a call of a many-use function being passed
--    a use-once function. Such "budget donation" can reduce the variability
--    of inlining's run-time benefits due to inlining thresholds.



-- We'll iterate through the list of arms. Initially, our match status will be
-- NoPossibleMatchYet because we haven't seen any arms at all. If e.g. the first
-- arm we see is a definite match, we'll immediately return those bindings.
-- If the first is a definite non-match, we'll discard it and continue.
-- When we first see an arm which is neither a definite yes or no match,
-- we'll change status to MatchPossible.
-- This prevents us from turning
--           case (v1, c2) of (c3, _) -> a    of (_, _) -> b  end
-- into      case (v1, c2)                    of (_, _) -> b  end
-- because we'll be in state MatchPossible (v1 ~?~ c3).
--
data MatchStatus = NoPossibleMatchYet | MatchPossible
                   deriving Show

data PatternMatchStatus t = MatchDef [(Ident, FreeVar t)]
                          | MatchSeq [(FreeVar t, PatternRepr t)]
                          | MatchAmbig
                          | MatchNeg

instance TExpr (PatternAtom ty) ty where
  freeTypedIds (P_Variable _ v) = [v]
  freeTypedIds _ = []

patternReprFreeIds :: PatternRepr ty -> [TypedId ty]
patternReprFreeIds (PR_Atom atom) = freeTypedIds atom
patternReprFreeIds (PR_Ctor  _ _ reprs _) = concatMap patternReprFreeIds reprs
patternReprFreeIds (PR_Tuple _ _ reprs  ) = concatMap patternReprFreeIds reprs
patternReprFreeIds (PR_Or    _ _ reprs  ) = concatMap patternReprFreeIds reprs

matchSeq :: t -> SourceRange -> Map Ident (MKBound t)
  -> Subterm t -> (FreeVar t, PatternRepr t) -> Compiled (Subterm t)
matchSeq ty range boundsFor subterm (v, pat) = do
  parentLink <- newOrdRef Nothing
  let patBoundVars = patternReprFreeIds pat
  let bindings = [boundsFor Map.! tidIdent tid | tid <- patBoundVars]
  let rv = MKCase parentLink ty v [MKCaseArm pat subterm (Seq.fromList bindings) range]
  _ <- backpatchT rv [subterm]
  newOrdRef (Just rv)

-- Compute the residual of matching the given term ``T`` against the given
-- pattern arms ``p1 -> e1, ... , pn -> en``.
-- If ``c`` definitely matches one of the patterns ``pj``,
-- replace the given case subterm by ``ej`` with appropriate substitutions.
-- 
findMatchingArm :: PrettyT ty =>
                   (Subterm ty -> Compiled ()) -> ty
                ->  FreeVar ty -> [MKCaseArm (Subterm ty) ty]
                -> (FreeVar ty -> Compiled (Maybe (MKExpr ty)))
                -> Compiled ()
findMatchingArm replaceCaseWith ty v arms lookupVar = go arms NoPossibleMatchYet
  where go [] _ = return ()
        go ((MKCaseArm pat subterm bindings range):rest) potentialMatch = do
              -- Map from pattern variable ids to bound vars.
              let boundsFor = Map.fromList [(tidIdent (boundVar b), b) | b <- toList bindings]

              matchRes <- matchPatternAgainst pat v
              case (matchRes, potentialMatch) of
                -- A definite match only "counts" if there were no earlier possible matches.
                (MatchDef matches, NoPossibleMatchYet) -> do
                  -- Note: matches is a list of (id, v) where id is a pattern ident and v is a FreeVar.
                  let boundAndVars = [(v, boundsFor Map.! id) | (id, v) <- matches]
                  mapM_ substVarForBound boundAndVars
                  replaceCaseWith subterm

                -- A match sequence is similar to a definite match, except that it
                -- replaces one pattern match with several simpler matches,
                -- instead of replacing a pattern match with the associated arm.
                (MatchSeq varsPats, NoPossibleMatchYet) -> do
                  if null varsPats
                    then return ()
                    else do
                      -- TODO maybe mark the generated cases as redexes?
                      caseSeq <- foldlM (matchSeq ty range boundsFor) subterm varsPats
                      replaceCaseWith caseSeq

                -- A match that definitely won't happen can be ignored.
                (MatchNeg  , _) -> go rest potentialMatch

                -- Otherwise, we have a possible match.
                _               -> go rest MatchPossible

        -- If the constant matches the pattern, return the list of bindings generated.
        --matchPatternAgainst :: PatternRepr ty -> FreeVar ty -> Compiled [PatternMatchStatus ty]
        matchPatternAgainst p v = do
          case p of
            PR_Atom (P_Wildcard _ _  ) -> return $ MatchDef []
            PR_Atom (P_Variable _ tid) -> return $ MatchDef [(tidIdent tid, v)]
            _ -> do
              mb_e <- lookupVar v
              case mb_e of
                Nothing -> return $ MatchAmbig
                Just e  ->
                  case (e, p) of
                    (MKLiteral _ _ (LitInt  i1), PR_Atom (P_Int  _ _ i2)) -> nullary $ litIntValue i1 == litIntValue i2
                    (MKLiteral _ _ (LitBool b1), PR_Atom (P_Bool _ _ b2)) -> nullary $ b1 == b2
                    -- TODO record patterns (?)
                    (MKTuple _ _ args _        , PR_Tuple _ _ pats) -> do
                        parts <- mapM (uncurry matchPatternAgainst) (zip pats args)
                        let pms = concatMapStatuses parts
                        if List.all guaranteedToMatch pats
                          then case pms of
                                 MatchDef defs -> return $ MatchDef defs
                                 _ -> return $ MatchSeq (zip args pats)
                          else return pms
                        --trace ("matched tuple const against tuple pat " ++ show p ++ "\n, parts = " ++ show parts ++ " ;;; res = " ++ show res) res

                    (MKAppCtor _ _ (kid, _) args _sr, PR_Ctor _ _ pats (LLCtorInfo cid _ _ _)) | kid == cid -> do
                      parts <- mapM (uncurry matchPatternAgainst) (zip pats args)
                      return $ concatMapStatuses parts

                    (_ , _) -> return $ MatchAmbig
        
        -- guaranteedToMatch :: PatternRepr ty -> Bool
        guaranteedToMatch p =
          case p of
            PR_Atom (P_Wildcard {}) -> True
            PR_Atom (P_Variable {}) -> True
            PR_Or    _ _ pats -> List.any guaranteedToMatch pats
            PR_Tuple _ _ pats -> List.all guaranteedToMatch pats
            PR_Ctor  _ _ pats ctorinfo -> ctorLLInfoLone ctorinfo && List.all guaranteedToMatch pats
            _ -> False

        nullary True  = return $ MatchDef []
        nullary False = return $ MatchNeg
                
        concatMapStatuses :: [PatternMatchStatus ty] -> PatternMatchStatus ty
        concatMapStatuses mbs = go mbs []
          where go []               acc = MatchDef (concat acc)
                go [MatchSeq vp]    []  = MatchSeq vp
                go (MatchNeg:_)    _acc = MatchNeg
                go (MatchAmbig:_)  _acc = MatchAmbig
                go ((MatchDef xs):rest) acc = go rest (xs : acc)
                go ((MatchSeq _ ):_rst) _   = error $ "can't yet process MatchSeq embedded..."


prettyLinkM link = do
  tm <- readLink "prettyLinkM" $ link
  prettyTermM tm

prettyTermM tm = do
  kn <- knOfMK NoCont tm
  return $ prettyT kn

showOccsOfBinder bv = do
  occs <- dlcToList bv
  let showOcc occ = do
        p <- prettyLinkM (freeLink occ)
        dbgDoc $ text "((*)" <> indent 1 p <$> text ")"
  mapM_ showOcc occs

{-
-- TODO handle partial matches:
--        case (v1,v2) of (True, x) -> f(x)
--      can become
--        case (v1,v2) of (True, x) -> f(v2)
--      even thought it can't become simply ``f(v2)`` because v1 might not be True.
-}

dbgDoc :: MonadIO m => Doc AnsiStyle -> m ()
dbgDoc d =
  if False
    then liftIO $ putDocLn d
    else return ()

dbgIf :: MonadIO m => Bool -> Doc AnsiStyle -> m ()
dbgIf cond d =
  if cond
    then liftIO $ putDocLn d
    else return ()

dbgCont = False
dbgFinal = False
