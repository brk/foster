{-# LANGUAGE RecursiveDo #-}

module Foster.MKNExpr where

import Foster.Base
import Foster.Config
import Foster.MainOpts(getInliningDonate)
import Foster.KNUtil
import Foster.Worklist
import Foster.Output(putDocLn)

import Control.Monad(liftM, liftM2)
import Control.Monad.State(gets, liftIO)
import Data.IORef(IORef, readIORef, newIORef, writeIORef)
import Data.UnionFind.IO

import qualified Data.Text as T
import qualified Data.Map as Map
import Data.Map(Map)
import qualified Data.List as List(foldl')
import Data.Maybe(catMaybes, isJust)

import System.IO(openFile, hClose, IOMode(..))

import Text.PrettyPrint.ANSI.Leijen


-- Binding occurrences of variables, with link to a free occurrence (if not dead).
data MKBound t = MKBound (TypedId t) (OrdRef (Maybe (FreeOcc t)))

-- Free occurrences: doubly-linked list with union-find for access to binder.
type FreeOcc t = DLCNode (Point (MKBound t))

instance Show t => Show (MKBound t) where
    show (MKBound v _) = show v

instance Pretty t => Pretty (MKBound t) where
    pretty (MKBound v _) = pretty v

instance Eq (MKBound t) where
  (==)    (MKBound _ r1) (MKBound _ r2) = (==)    r1 r2
instance Ord (MKBound t) where
  compare (MKBound v1 _) (MKBound v2 _) = compare v1 v2

freeBinder :: FreeOcc t -> Compiled (MKBound t)
freeBinder  (DLCNode pt _ _) = liftIO $ descriptor pt

boundVar :: MKBound t -> TypedId t
boundVar (MKBound v _) = v

substVarForBound :: Pretty t => (FreeOcc t, MKBound t) -> Compiled ()
substVarForBound (fox, MKBound v r) = do
  mb_fo <- readOrdRef r
  b <- freeBinder fox
  case mb_fo of
    Nothing -> do
      liftIO $ putDocLn $ text "can't substitute" <+> pretty b <+> text "for" <+> pretty v
      return ()
    Just fo -> do substVarForVar fox fo

substVarForVar :: FreeOcc t -> FreeOcc t -> Compiled ()
substVarForVar (DLCNode px _ _) (DLCNode py _ _) = substVarForVar' px py

substVarForVar' :: Point (MKBound t) -> Point (MKBound t) -> Compiled ()
substVarForVar' px py | px == py = do return ()
substVarForVar' px py = do
  MKBound _ b'x <- liftIO $ descriptor px
  MKBound _ b'y <- liftIO $ descriptor py
  mergeFreeLists b'x b'y
  writeOrdRef b'y Nothing
  py `nowPointsTo` px where nowPointsTo x y = liftIO $ union x y

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

data VarOccClassif = VOC_Zero | VOC_One | VOC_Many

freeOccIsSingleton :: FreeOcc t -> Compiled Bool
freeOccIsSingleton = dlcIsSingleton

binderIsSingletonOrDead (MKBound _ r) = do mbfo <- readOrdRef r
                                           case mbfo of
                                             Nothing -> return True
                                             Just fo -> freeOccIsSingleton fo

mkbClassify :: (OrdRef (Maybe (FreeOcc t))) -> Compiled VarOccClassif
mkbClassify mkb = do
  mfo <- readOrdRef mkb
  case mfo of
    Nothing -> return VOC_Zero
    Just fo -> do s <- dlcIsSingleton fo
                  return $ if s then VOC_One else VOC_Many

type Link   val    = OrdRef (Maybe val)
type Uplink ty     = Link (Parent ty)
type Subterm ty    = Link (MKTerm ty)
type Known  ty val = (MKBound ty, val)

type Linked ty = Link (MKTerm ty)

type Links ty = (Uplink ty, Subterm ty) -- parent, self
data Parent ty = ParentTerm (MKTerm ty)
               | ParentFn  (MKFn (Subterm ty) ty)

data MKTerm ty =
        -- Literals
          MKLiteral     (Links ty) ty Literal
        | MKTuple       (Links ty) ty [FreeOcc ty] SourceRange
        | MKKillProcess (Links ty) ty T.Text
        -- Control flow
        | MKIf          (Links ty) ty (FreeOcc ty) (Subterm ty) (Subterm ty)
        -- Creation of bindings
        | MKCase        (Links ty)  ty (FreeOcc ty) [MKCaseArm (Subterm ty) ty]
        | MKLetVal      (Links ty) (Known ty          (Subterm ty)) (Subterm ty)
        | MKLetRec      (Links ty) [Known ty          (Subterm ty)] (Subterm ty)
        | MKLetFuns     (Links ty) [Known ty (Link (MKFn (Subterm ty) ty))] (Subterm ty)
        -- Use of bindings
        | MKVar         (Links ty) (FreeOcc ty)
        | MKCallPrim    (Links ty) ty (FosterPrim ty)    [FreeOcc ty] SourceRange
        | MKCall        (Links ty) ty (FreeOcc ty)       [FreeOcc ty]
        | MKAppCtor     (Links ty) ty (CtorId, CtorRepr) [FreeOcc ty]
        -- Mutable ref cells
        | MKAlloc       (Links ty) ty (FreeOcc ty) AllocMemRegion
        | MKDeref       (Links ty) ty (FreeOcc ty)
        | MKStore       (Links ty) ty (FreeOcc ty) (FreeOcc ty)
        -- Array operations
        | MKAllocArray  (Links ty) ty (FreeOcc ty) AllocMemRegion ZeroInit
        | MKArrayRead   (Links ty) ty (ArrayIndex (FreeOcc ty))
        | MKArrayPoke   (Links ty) ty (ArrayIndex (FreeOcc ty)) (FreeOcc ty)
        | MKArrayLit    (Links ty) ty (FreeOcc ty) [Either Literal (FreeOcc ty)]
        -- Others
        | MKCompiles    (Links ty) KNCompilesResult ty (Subterm ty)
        | MKTyApp       (Links ty) ty (FreeOcc ty) [ty]


data MKFn expr ty
                = MKFn { mkfnVar   ::  MKBound ty
                       , mkfnVars  :: [MKBound ty]
                       , mkfnBody  :: expr
                       , mkfnIsRec :: RecStatus
                       , mkfnAnnot :: ExprAnnot
                       } deriving Show -- For KNExpr and KSmallstep
{-

data MKPatternAtom ty =
          MKP_Wildcard      SourceRange ty
        | MKP_Variable      SourceRange (MKBound ty)
        | MKP_Bool          SourceRange ty Bool
        | MKP_Int           SourceRange ty LiteralInt

data MKPatternFlat ty =
          MKPF_Atom                 (MKPatternAtom ty)
        | MKPF_Ctor  SourceRange ty [MKPatternAtom ty] (LLCtorInfo ty)
-}
data MKCaseArm expr ty = MKCaseArm { mkcaseArmPattern :: PatternRepr ty
                                   , mkcaseArmBody    :: expr
                                   , mkcaseArmBindings:: [MKBound ty]
                                   , mkcaseArmRange   :: SourceRange
                                   }
{-
data MKCaseArm expr ty = MKCaseArm { mkcaseArmPattern :: PatternFlat ty
                                   , mkcaseArmBody    :: expr
                                   , mkcaseArmBindings:: [MKBound ty]
                                   , mkcaseArmRange   :: SourceRange
                                   }
-}

-- With the given binding map, process the given terms,
-- constructing a final term using the builder ``f``.
-- In the course of processing, each subterm gets an empty uplink.
-- Finally, backpatch the result rv into the subterms' uplinks.
mkBackpatch' :: Map Ident (MKBound ty) -> [KNExpr' RecStatus ty]
             -> ([Subterm ty] -> Compiled (MKTerm ty)) -> Compiled (MKTerm ty)
mkBackpatch' m es f = do
  ms <- mapM (mkOfKN m) es
  rv <- f ms
  backpatch rv ms
  return rv

mkBackpatch m f es = mkBackpatch' m es (return . f)

backpatch :: MKTerm ty -> [Subterm ty] -> Compiled ()
backpatch mke mkes = mapM_ (\subterm -> do
    mked <- readLink "backpatch" subterm
    writeOrdRef (parentLink mked) (Just (ParentTerm mke))) mkes

backpatchFns parent@(MKLetFuns _nu _knowns subterm) = do
    readLink "backpatchFns" subterm >>= \tm -> writeOrdRef (parentLink tm) (Just (ParentTerm parent))
    return $ parent
backpatchFns _ = error $ "backpatchFns should only be given MKLetFuns"

readLink :: String -> Link val -> Compiled val
readLink msg subterm = do mb_rv <- readOrdRef subterm
                          case mb_rv of
                            Just rv -> return rv
                            Nothing -> error $ "MKNExpr.hs:readLink: " ++ msg

findBinder :: Ident -> Map Ident (MKBound ty) -> MKBound ty
findBinder id m =
    case Map.lookup id m of
        Just binder -> binder
        Nothing -> error $ "MKNExpr.hs: findBinder had nothing for " ++ show id

mkFreeOcc :: Map Ident (MKBound ty) -> TypedId ty -> Compiled (FreeOcc ty)
mkFreeOcc m tid = do
    let binder@(MKBound _ r) = findBinder (tidIdent tid) m
    pt <- liftIO $ fresh binder
    mb_fo <- readOrdRef r
    case mb_fo of
      Nothing -> do
        fo <- dlcSingleton pt
        writeOrdRef r (Just fo)
        return fo
      Just fo@(DLCNode fo_pt _ _) -> do
        liftIO $ union pt fo_pt -- use the existing binder as representative
        dlcAppend fo pt

-- Note: every time an ident is passed to mkBinder, the result should be
-- passed to extend. (too lazy to set up a state monad... or use the shift key)
mkBinder :: TypedId ty -> Compiled (MKBound ty)
mkBinder tid = liftM (MKBound tid) (newOrdRef Nothing)

mapMaybeM _ (Nothing) = return Nothing
mapMaybeM f (Just v) = f v >>= return . Just

extend m vs binders = let ins m (v,binder) = Map.insert (tidIdent v) binder m in
                      List.foldl' ins m (zip vs binders)

mkKnown :: MKBound ty -> Subterm ty -> Known ty (Subterm ty)
mkKnown bound subterm = (bound, subterm)

-- The link for regular terms is the self link of the term;
-- functions get a separate link, since they have no self link.
mkKnown' :: MKBound ty -> MKFn (Subterm ty) ty -> Compiled (Known ty (Link (MKFn (Subterm ty) ty)))
mkKnown' bound fn = do
    linkref <- newOrdRef (Just fn)
    return (bound, linkref)


mkOfKNFn m (Fn v vs expr isrec annot) = do
    v' <- mkBinder v
    vs' <- mapM mkBinder vs
    let m' = extend m (v:vs) (v' : vs' )
    expr' <- mkOfKN m' expr
    let f' = MKFn v' vs' expr' isrec annot
    readLink "mkOfKNFn" expr' >>= \mk -> writeOrdRef (parentLink mk) (Just (ParentFn f'))
    return f'

mkOfKN :: Map Ident (MKBound ty) -> KNExpr' RecStatus ty -> Compiled (Subterm ty)
mkOfKN m expr = do
  let qv = mkFreeOcc m
  let qb = mkBinder
  let qvs = mapM qv
  let qa (ArrayIndex v1 v2 x y) = qvs [v1, v2] >>= \[v1', v2'] -> return (ArrayIndex v1' v2' x y)
  let qarm (CaseArm _pat _body (Just _) _binds _rng) = error $ "MKNExpr.hs cannot yet deal with pattern guards"
      qarm (CaseArm pat body Nothing binds rng) = do
            binds' <- mapM qb binds
            let m' = extend m binds binds'
            body' <- mkOfKN m' body
            return $ MKCaseArm pat body' binds' rng
  {-
  let qarm (CaseArmFlat pat expr binds _occs rng) = do
            -- TODO should track/remap occs...
            binds' <- mapM qb binds
            let m' = extend m binds binds'
            expr' <- mkOfKN m' expr
            return $ MKCaseArm pat expr' binds' rng
            -}
  let qelt (Left lit) = return (Left lit)
      qelt (Right v)  = liftM  Right (qv v)
  let qf = mkOfKNFn

  parentLink <- newOrdRef Nothing
  selfLink   <- newOrdRef Nothing
  let nu = (parentLink, selfLink)
  let
   go expr = case expr of
    KNLiteral   ty   lit -> do return $ MKLiteral     nu ty lit
    KNTuple     ty vs sr -> do qvs vs >>= \vs' -> return $ MKTuple       nu ty vs' sr
    KNKillProcess   ty t -> do return $ MKKillProcess nu ty t
    KNIf      ty v e1 e2 -> do v' <- qv v
                               mkBackpatch' m [e1, e2] (\[m1,m2] -> do
                                    return $ MKIf          nu ty v' m1 m2)
    KNCase    ty v arms  -> do v' <- qv v
                               arms' <- mapM qarm arms
                               return $ MKCase        nu ty v' arms'
    KNLetVal      x b  k -> do let v = (TypedId (typeKN b) x)
                               x' <- qb v
                               mkBackpatch' (extend m [v] [x']) [b,k] $ \[m1,m2] -> do
                                    let known = mkKnown x' m1
                                    return $ MKLetVal nu known m2
    KNLetRec    xs es  k -> do let vs = map (\(x,e) -> (TypedId (typeKN e) x)) (zip xs es)
                               xs' <- mapM qb vs
                               let m' = extend m vs xs'
                               ts <- mapM (mkOfKN m') es
                               t  <- mkOfKN m' k
                               let knowns = map (uncurry mkKnown) (zip xs' ts)
                               let rv = MKLetRec      nu knowns t
                               backpatch rv (t:ts)
                               return rv
    KNLetFuns ids fns  k -> do let vs = map (\(x,fn) -> (TypedId (fnType fn) x)) (zip ids fns)
                               binders <- mapM qb vs
                               let m' = extend m vs binders
                               fs' <- mapM (qf m') fns
                               k'  <- mkOfKN m' k
                               knowns <- mapM (uncurry mkKnown') (zip binders fs')
                               backpatchFns $ MKLetFuns nu knowns k'
    KNVar             v  -> do qv  v  >>= \v'  -> return $ MKVar         nu v'
    KNCallPrim r ty p vs -> do qvs vs >>= \vs' -> return $ MKCallPrim    nu    ty p vs' r
    KNCall       ty v vs -> do qvs (v:vs) >>= \(v':vs') -> return $ MKCall nu  ty v' vs'
    KNAppCtor    ty c vs -> do qvs vs >>= \vs' -> return $ MKAppCtor     nu    ty c vs'
    KNAlloc      ty v mr -> do qv  v  >>= \v'  -> return $ MKAlloc       nu ty v' mr
    KNDeref      ty v    -> do qv  v  >>= \v'  -> return $ MKDeref       nu ty v'
    KNStore      ty v v2 -> do qvs [v,v2]  >>= \[v',v2']  -> return $ MKStore       nu ty v' v2'
    KNAllocArray ty v m z-> do qv  v  >>= \v'  -> return $ MKAllocArray  nu ty v' m z
    KNArrayRead  ty a    -> do qa  a  >>= \a'  -> return $ MKArrayRead   nu ty a'
    KNArrayPoke  ty a v  -> do v' <- qv v
                               a' <- qa a
                               return $ MKArrayPoke   nu ty a' v'
    KNArrayLit   ty v elts -> do liftM2 (MKArrayLit   nu ty) (qv v) (mapM qelt elts)
    KNTyApp  ty v argtys   -> do qv  v  >>= \v'  -> return $ MKTyApp       nu ty v' argtys
    KNCompiles res ty expr -> do liftM  (MKCompiles nu res ty) (mkOfKN m expr)
    KNInlined _t0 _to _tn _old new -> go new
    KNNotInlined _ expr -> go expr
  rv <- go expr
  writeOrdRef selfLink (Just rv)
  return selfLink

selfLink :: MKTerm ty -> Subterm ty
selfLink   = snd . links
parentLink = fst . links
links expr =
  case expr of
    MKLiteral     u       _t _it -> u
    MKTuple       u     _t _s _r -> u
    MKKillProcess u     _ty _t    -> u
    MKIf          u  _ty _ _e1 _e2 -> u
    MKCase        u  _ty _ _arms  -> u
    MKLetVal      u   _known  _k -> u
    MKLetRec      u   _knowns _k -> u
    MKLetFuns     u   _knowns _k -> u
    MKVar         u          _   -> u
    MKCallPrim    u     _ty _ _s _ -> u
    MKCall        u     _ty _ _s -> u
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


knOfMKFn (MKFn v vs expr isrec annot) = do
    let qb (MKBound tid _) = tid
    expr' <- readLink "knOfMKFn" expr >>= knOfMK
    return $ Fn (qb v) (map qb vs) expr' isrec annot

knOfMK :: MKTerm t -> Compiled (KNExpr' RecStatus t)
knOfMK term0 = do
  let q  subterm = readLink "knOfMK" subterm >>= knOfMK
  let qb (MKBound tid _) = tid
  let qk :: (val -> Compiled res) -> Known ty (OrdRef (Maybe val)) -> Compiled (Ident, Maybe res)
      qk f (x,br) = do b <- readOrdRef br
                       b' <- liftMaybe f b
                       return (tidIdent (qb x), b')
  let qks f knowns = do vals <- mapM (qk f) knowns
                        return $ unzip [(x,b) | (x, Just b) <- vals]
  let qv (DLCNode pt _ _) = do bound <- liftIO $ repr pt >>= descriptor
                               return $ qb bound
  let qa (ArrayIndex v1 v2 x y) = mapM qv [v1, v2] >>= \[v1', v2'] -> return (ArrayIndex v1' v2' x y)
  let qarm (MKCaseArm pat body binds rng) = do
        let binds' = map qb binds
        body' <- q body
        --mb_guard' <- liftMaybe q mb_guard
        return $ CaseArm pat body' Nothing binds' rng
  {-
  let qarm (MKCaseArm pat expr binds rng) = do
            expr' <- q expr
            let occs = []
            return $ CaseArmFlat pat expr' (map qb binds) occs rng
  -}
  let qelt (Left lit) = return (Left lit)
      qelt (Right v)  = liftM Right (qv v)
  let qf = knOfMKFn

  term' <- readOrdRef (selfLink term0)
  let term = case term' of Nothing -> term0
                           Just tm -> tm
  case term of
    MKLiteral     _u       t it   -> do return $ KNLiteral           t it
    MKTuple       _u     t vs r   -> do mapM qv vs >>= \vs' -> do return $ KNTuple  t vs' r
    MKKillProcess _u     ty t     -> do return $ KNKillProcess     ty t
    MKIf          _u  ty v e1 e2  -> do e1' <- q e1
                                        e2' <- q e2
                                        v'  <- qv v
                                        return $ KNIf ty v' e1' e2'
    MKCase        _u  ty v arms   -> do arms' <- mapM qarm arms
                                        v' <- qv v
                                        return $ KNCase         ty v' arms'
    MKLetVal      _u   known   k  -> do (x', mb) <- qk knOfMK known
                                        k' <- q k
                                        case mb of
                                          Nothing -> return k'
                                          Just b' -> return $ KNLetVal x' b' k'
    MKLetRec      _u   knowns  k  -> do (xs', es')  <- qks knOfMK knowns
                                        k'  <- q k
                                        return $ mkKNLetRec xs' es' k'
    MKLetFuns     _u   knowns  k  -> do (xs', fns') <- qks qf knowns
                                        k'  <- q k
                                        return $ mkKNLetFuns  xs' fns' k'
    MKVar         _u     v        -> do qv v >>= \v' -> do return $ KNVar v'
    MKCallPrim    _u    ty p vs r -> do mapM qv vs     >>= \vs' -> do return $ KNCallPrim      r ty p  vs'
    MKCall        _u     ty v vs  -> do mapM qv (v:vs) >>= \(v':vs') -> do return $ KNCall       ty v' vs'
    MKAppCtor     _u     ty c vs  -> do mapM qv vs     >>= \vs' -> do return $ KNAppCtor         ty c  vs'
    MKAlloc       _u     ty v amr -> do qv v >>= \v' -> return $ KNAlloc           ty v' amr
    MKDeref       _u     ty v     -> do qv v >>= \v' -> return $ KNDeref           ty v'
    MKStore       _u     ty v1 v2 -> do v1' <- qv v1
                                        v2' <- qv v2
                                        return $ KNStore           ty v1' v2'
    MKAllocArray  _u     ty v m z -> do qv v >>= \v' -> return $ KNAllocArray      ty v' m z
    MKArrayRead   _u     ty a     -> do qa a >>= \a' -> return $ KNArrayRead       ty a'
    MKArrayPoke   _u     ty a v   -> do v' <- qv v
                                        qa a >>= \a' -> return $ KNArrayPoke       ty a' v'
    MKArrayLit    _u ty v elts    -> do liftM2 (KNArrayLit ty) (qv v) (mapM qelt elts)
    MKCompiles    _u res ty body  -> do liftM (KNCompiles res ty) (q body)
    MKTyApp       _u ty v argtys  -> do qv v >>= \v' -> return $ KNTyApp       ty v' argtys

mkKNLetRec [] [] k = k
mkKNLetRec xs es k = KNLetRec xs es k

mkKNLetFuns [] [] k = k
mkKNLetFuns xs es k = KNLetFuns xs es k

isMainFn fo = do
  b <- freeBinder fo
  case tidIdent (boundVar b) of
      GlobalSymbol t | t == T.pack "main" -> return True
      _ -> return False

collectRedexes :: IORef (WorklistQ (MKTerm t))
               -> IORef (Map (MKBound t) (Link (MKTerm t)))
               -> IORef (Map (MKBound t) (Link (MKFn (Subterm t) t))) -> MKTerm t -> Compiled ()
collectRedexes ref valbindsref funbindsref term = do
  let go = collectRedexes ref valbindsref funbindsref
  let markRedex =          liftIO $ modIORef' ref        (\w -> worklistAdd w term)
  let markValBind (x,tm) = liftIO $ modIORef' valbindsref (\m -> Map.insert x tm m)
  let markFunBind (x,fn) = liftIO $ modIORef' funbindsref (\m -> Map.insert x fn m)
  case term of
    MKCallPrim    {}  -> markRedex
    MKCall _ _ fo _   -> whenNotM (isMainFn fo) markRedex
    _ -> subTermsOf term >>= mapM_ go
     where --subTermsOf :: MKTerm ty -> Compiled [MKTerm ty]
           subTermsOf term =
              case term of
                MKIf          _u _ _ tru fls -> mapM (readLink "collectRedexes.MKIf") [tru, fls]
                MKLetVal      _u  (x, br) k  -> do markValBind (x,br)
                                                   mbs <- mapM readOrdRef [br, k]
                                                   return $ catMaybes mbs
                MKLetRec      _u   knowns k  -> do mapM_ markValBind knowns
                                                   es <- knownActuals knowns
                                                   k' <- readLink "collectRedexes.MKLetRec" k
                                                   return $ k':es
                MKLetFuns     _u   knowns k  -> do mapM_ markFunBind knowns
                                                   fns <- knownActuals knowns
                                                   mapM (readLink "collectRedexes.MKLetFuns") $ k:(map mkfnBody fns)
                MKCase        _u _ _v arms -> mapM (readLink "collectRedexes.MKCase") $ map mkcaseArmBody arms
                -- Note: intentionally ignoring MKCompiles subterm...
                _ -> return []

knownActuals :: [Known ty (Link val)] -> Compiled [val]
knownActuals knowns = do
    mb_vals <- mapM (readOrdRef . snd) knowns
    return $ catMaybes mb_vals

putDocF file doc = do
    handle <- openFile file WriteMode
    displayIO handle (renderPretty 0.4 100 (plain doc))
    hClose handle

-- {{{
data RedexSituation t =
       CallOfUnknownFunction
     | CallOfSingletonFunction (MKFn (Subterm t) t)
     | CallOfDonatableFunction (MKFn (Subterm t) t)
     | SomethingElse           (MKFn (Subterm t) t)

classifyRedex callee args knownFns = do
  mb_fn <- lookupBinding callee knownFns
  classifyRedex' callee mb_fn args knownFns

classifyRedex' _ Nothing _ _ = return CallOfUnknownFunction
classifyRedex' callee (Just fn) args knownFns = do
  callee_singleton <- freeOccIsSingleton callee
  case (callee_singleton, mkfnIsRec fn) of
    (True, NotRec) -> return $ CallOfSingletonFunction fn
    _ -> do
      donationss <- mapM (\(arg, binder) -> do
                         argsingle <- freeOccIsSingleton arg
                         argboundfn <- lookupBinding arg knownFns
                         bindsingle <- binderIsSingletonOrDead binder
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
copyMKFn :: Pretty t => MKFn (Subterm t) t -> Compiled (MKFn (Subterm t) t)
copyMKFn fn = do
  knfn <- knOfMKFn fn
  allOccs    <- collectOccsFn    fn
  ourBinders <- collectBindersFn fn -- The binders we define
  occBinders <- mapM freeBinder allOccs -- The binders we use
  let freeBinders = occBinders `butnot` ourBinders -- The ones we use but don't define.
  let binderMap = Map.fromList $ [(tidIdent (boundVar b), b) | b <- freeBinders]

  -- We need to alpha-rename the converted function so that we don't wind up
  -- introducing duplicate bindings, which will cause later conversions to fail.
  uniq  <- gets ccUniqRef
  knfn' <- liftIO $ alphaRename' knfn uniq
  mkOfKNFn binderMap knfn'

collectOccsFn fn = collectOccs (mkfnBody fn)
collectOccs :: Pretty ty => Subterm ty -> Compiled [FreeOcc ty]
collectOccs subterm = do
  let go = collectOccs
  expr <- readLink "collectOccs" subterm
  case expr of
    MKLiteral     {} -> return []
    MKKillProcess {} -> return []
    MKTuple       _u     _t s _r -> return s
    MKIf          _u  _ty v t1 t2 -> do xs <- go t1 ; ys <- go t2 ; return $ v : (xs ++ ys)
    MKCase     _ _ _ arms -> do xs <- mapM (\arm -> do go (mkcaseArmBody arm)) arms
                                return $ concat xs
    MKLetVal      _u   (_,t1) t2 -> do  xs <- go t1 ; ys <- go t2 ; return $ xs ++ ys
    MKLetRec   _ knowns t1 -> do bk <- mapM (\(_,k) -> do xs <- go k ; return $ xs) knowns
                                 b1 <- go t1
                                 return $ b1 ++ concat bk
    MKLetFuns  _ knowns t1 -> do bk <- mapM (\(_b,link_mb_fn) -> do
                                         mb_fn <- readOrdRef link_mb_fn
                                         case mb_fn of
                                           Just fn -> do xs <- collectOccsFn fn ; return xs
                                           Nothing -> do return []) knowns
                                 b1 <- go t1
                                 return $ b1 ++ concat bk
    MKVar         _u           v   -> return [v]
    MKCallPrim    _u     _ty _ s _ -> return s
    MKCall        _u     _ty x s -> return $ x:s
    MKAppCtor     _u     _ty _ s -> return s
    MKAlloc       _u     _ty v  _ -> return [v]
    MKDeref       _u     _ty v    -> return [v]
    MKStore       _u     _ty x y -> return [x,y]
    MKAllocArray  _u     _ty v _ _ -> return [v]
    MKArrayRead   _u     _ty (ArrayIndex x y _ _)    -> return [x,y]
    MKArrayPoke   _u     _ty (ArrayIndex x y _ _) z  -> return [x,y,z]
    MKArrayLit    _u _ty v elts  -> return $ v : [x | Right x <- elts]
    MKCompiles    _u _res _ty body -> go body
    MKTyApp       _u _ty v _arg_tys -> return [v]

collectBindersFn fn = do bs <- collectBinders (mkfnBody fn)
                         return $ bs ++ (mkfnVar fn : mkfnVars fn)
collectBinders :: Subterm ty -> Compiled [MKBound ty]
collectBinders subterm = do
  let go = collectBinders
  expr <- readLink "collectBinders" subterm
  case expr of
    MKLiteral     {} -> return []
    MKTuple       {} -> return []
    MKKillProcess {} -> return []
    MKCase     _ _ _ arms -> do xs <- mapM (\arm -> do bs <- go (mkcaseArmBody arm)
                                                       return (mkcaseArmBindings arm ++ bs)) arms
                                return $ concat xs
    MKIf       _ _ _ t1 t2 -> do b1 <- go t1 ; b2 <- go t2 ; return $ b1 ++ b2
    MKLetVal   _ (b,t1) t2 -> do b1 <- go t1 ; b2 <- go t2 ; return $ b : (b1 ++ b2)
    MKLetRec   _ knowns t1 -> do bk <- mapM (\(b,k) -> do xs <- go k ; return $ b:xs) knowns
                                 b1 <- go t1
                                 return $ b1 ++ concat bk
    MKLetFuns  _ knowns t1 -> do bk <- mapM (\(b,link_mb_fn) -> do
                                         mb_fn <- readOrdRef link_mb_fn
                                         case mb_fn of
                                           Just fn -> do xs <- collectBindersFn fn ; return $ b:xs
                                           Nothing -> do return [b]) knowns
                                 b1 <- go t1
                                 return $ b1 ++ concat bk
    MKVar         {} -> return []
    MKCallPrim    {} -> return []
    MKCall        {} -> return []
    MKAppCtor     {} -> return []
    MKAlloc       {} -> return []
    MKDeref       {} -> return []
    MKStore       {} -> return []
    MKAllocArray  {} -> return []
    MKArrayRead   {} -> return []
    MKArrayPoke   {} -> return []
    MKArrayLit    {} -> return []
    MKCompiles    _ _ _ t1 -> go t1
    MKTyApp       {} -> return []
-- }}}

mknInline :: Pretty t => Subterm t -> Compiled (KNExpr' RecStatus t)
mknInline subterm = do
    wr <- liftIO $ newIORef worklistEmpty
    kr <- liftIO $ newIORef Map.empty
    fr <- liftIO $ newIORef Map.empty
    term <- readLink "mknInline" subterm
    collectRedexes wr kr fr term

    _knownVals <- liftIO $ readIORef kr
    knownFns   <- liftIO $ readIORef fr

    do w0 <- liftIO $ readIORef wr
       liftIO $ putStrLn $ "collected " ++ show (length (worklistToList w0)) ++ " redexes..."

    let worklistGet' = do
          w0 <- liftIO $ readIORef wr
          case worklistGet w0 of
            Nothing -> return Nothing
            Just (mredex, w) -> do
              liftIO $ writeIORef wr w
              parent <- readOrdRef (parentLink mredex)
              return $ Just (mredex, parent)
    let go 0 = liftIO $ putStrLn "... ran outta gas"
        go gas = do
           mb_mredex_parent <- worklistGet'
           case mb_mredex_parent of
             Nothing -> liftIO $ putStrLn "... ran outta work"
             Just (mredex, Nothing) -> do
                do redex <- knOfMK mredex
                   liftIO $ putDocLn $ text "skipping parentless redex: " <+> pretty redex
                go gas
             Just (mredex, _parent) -> case mredex of
               MKCall _up _ty callee args -> do
                 situation <- classifyRedex callee args knownFns
                 case situation of
                   CallOfUnknownFunction -> do
                     --do redex <- knOfMK mredex
                     --   liftIO $ putDocLn $ text "CallOfUnknownFunction: " <+> pretty redex
                     return ()
                   CallOfSingletonFunction fn -> do
                     --do redex <- knOfMK mredex
                     --   liftIO $ putDocLn $ text "CallOfSingletonFunction: " <+> pretty redex
                     newbody <- betaReduceOnlyCall fn args >>= readLink "CallOfSingleton"
                     replaceWith mredex newbody
                     killBinding callee knownFns
                   CallOfDonatableFunction fn -> do
                     --do redex <- knOfMK mredex
                     --   liftIO $ putDocLn $ text "CallOfDonatableFunction: " <+> pretty redex
                     flags <- gets ccFlagVals
                     if getInliningDonate flags
                       then do
                         fn' <- copyMKFn fn
                         newbody <- betaReduceOnlyCall fn' args >>= readLink "CallOfDonatable"
                         replaceWith mredex newbody
                         killOccurrence callee
                         collectRedexes wr kr fr newbody
                       else return ()
                   SomethingElse _fn -> do
                     --do redex <- knOfMK mredex
                     --   liftIO $ putDocLn $ text "SomethingElse: " <+> pretty redex
                     if shouldInlineRedex mredex _fn
                       then do
                             fn' <- copyMKFn _fn
                             newbody <- betaReduceOnlyCall fn' args >>= readLink "CallOfDonatable"
                             replaceWith mredex newbody
                             killOccurrence callee
                             collectRedexes wr kr fr newbody
                       else return ()
                 go (gas - 1)

               MKCallPrim _up _ty _prim _args _rng -> do
                 -- TODO: could check to see which args have known values,
                 --       and beta-reduce if all args are constants.
                 go gas

               _ -> do
                 do kn <- knOfMK mredex
                    liftIO $ putStrLn $ "skipping non-call redex: " ++ show (pretty kn)
                 go gas

    --kn0 <- knOfMK term
    --putDocF "before.mknexpr.txt" $ pretty kn0

    go 150

    kn1 <- knOfMK term
    --putDocF "after.mknexpr.txt" $ pretty kn1

    return kn1

shouldInlineRedex _mredex _fn =
  -- TODO use per-call-site annotation, when we have such things.
  let id = tidIdent (boundVar (mkfnVar _fn)) in
  T.pack "doinline_" `T.isInfixOf` identPrefix id

replaceWith :: MKTerm ty -> MKTerm ty -> Compiled ()
replaceWith target newterm = writeOrdRef (selfLink target) (Just newterm)

killOccurrence fo = do
    isSingleton <- dlcIsSingleton fo
    if isSingleton
     then return ()
     else do
       n <- dlcNext fo
       p <- dlcPrev fo
       writeOrdRef (dlcNextRef p) n
       writeOrdRef (dlcPrevRef n) p

    -- Make sure binder doesn't point to fo
    MKBound _ r <- freeBinder fo
    mb_fo' <- readOrdRef r
    case mb_fo' of
      Just fo' | dlcIsSameNode fo fo' -> do
        if isSingleton
          then writeOrdRef r Nothing
          else do fo'' <- dlcNext fo
                  writeOrdRef r $ Just fo''
      _ -> return ()

killBinding fo knownFns = do
    binding@(MKBound _ r') <- freeBinder fo
    writeOrdRef r' Nothing
    case Map.lookup binding knownFns of
        Nothing -> return ()
        Just r  -> writeOrdRef r Nothing

lookupBinding fo m = do
    binding <- freeBinder fo
    mb_mb <- liftMaybe readOrdRef (Map.lookup binding m)
    case mb_mb of Just mb -> return mb
                  _       -> return Nothing

betaReduceOnlyCall fn args = do
    mapM_ substVarForBound (zip args (mkfnVars fn))
    return $ mkfnBody fn

-- TODO: ok this seems to work, more or less.
--          Implement contification & other optimizations...

