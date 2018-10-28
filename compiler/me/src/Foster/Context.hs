{-# LANGUAGE Strict #-}
-----------------------------------------------------------------------------
-- Copyright (c) 2012 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.Context where

import Control.Monad(ap)
import Control.Applicative(Applicative(..))

import Control.Monad.State(liftM, liftM2)
import Data.IORef(IORef,newIORef,readIORef,writeIORef)
import Data.Map(Map)
import Data.List(foldl')
import qualified Data.Map as Map

import qualified Data.Text as T

import Foster.Base
import Foster.Kind
import Foster.ExprAST
import Foster.TypeAST
import Foster.TypeTC
import Foster.Config(OrdRef(..))

import Text.PrettyPrint.ANSI.Leijen
import Foster.Output

type CtxBound ty = (TypedId ty, Maybe CtorId)
data ContextBinding ty = TermVarBinding T.Text (CtxBound ty)

type ContextBindings ty = Map T.Text (CtxBound ty)
data Context ty = Context { contextBindings   :: ContextBindings ty
                          , nullCtorBindings  :: ContextBindings ty
                          , primitiveBindings :: ContextBindings ty
                          , primitiveOperations :: Map T.Text (FosterPrim ty)
                          , globalIdents       :: [Ident]
                          , pendingBindings   :: [T.Text]
                          , localTypeBindings :: Map String ty -- as introduced by, e.g. foralls.
                          , contextEffectCtorInfo :: Map CtorName [(CtorId, EffectCtor ty)]
                          , contextTypeBindings :: [(TyVar, Kind)]
                          , contextCtorInfo   :: Map CtorName     [CtorInfo ty]
                          , contextDataTypes  :: Map DataTypeName [DataType ty]
                          } deriving Show

addPendingBinding :: Context ty -> E_VarAST tx -> Context ty
addPendingBinding ctx v = ctx { pendingBindings = (evarName v) : (pendingBindings ctx) }

prependBinding :: ContextBindings ty -> ContextBinding ty -> ContextBindings ty
prependBinding m (TermVarBinding nm cxb) = Map.insert nm cxb m

prependContextBinding :: Context ty -> ContextBinding ty -> Context ty
prependContextBinding ctx binding =
    ctx { contextBindings = prependBinding (contextBindings ctx) binding }

prependContextBindings :: Context ty -> [ContextBinding ty] -> Context ty
prependContextBindings ctx prefix =
    ctx { contextBindings = foldl' prependBinding (contextBindings ctx) prefix }

instance (Show ty) => Show (ContextBinding ty) where
    show (TermVarBinding _s annvar) = "(termvar " ++ show annvar ++ ")"

termVarLookup :: T.Text -> Map T.Text v -> Maybe v
termVarLookup name bindings = Map.lookup name bindings

typeVarLookup :: String -> Map String (TyVar, Kind) -> Maybe (TyVar, Kind)
typeVarLookup name bindings = Map.lookup name bindings

extendTyCtx ctx ktvs = ctx { contextTypeBindings =
                     ktvs ++ contextTypeBindings ctx }

liftContextM :: (Monad m, Show t1, Show t2)
             => (t1 -> m t2) -> Context t1 -> m (Context t2)
liftContextM f (Context cb nb pb primops gb pend tyvars effctors tybinds ctortypeast dtinfo) = do
  cb' <- mmapM (liftCXB f) cb
  nb' <- mmapM (liftCXB f) nb
  pb' <- mmapM (liftCXB f) pb
  po' <- mmapM (liftPrimOp f) primops
  tyvars' <- mmapM f tyvars
  ec' <- mmapM (mapM (liftEffectCtorInfo f)) effctors
  ct' <- mmapM (mapM (liftCtorInfo f)) ctortypeast
  dt' <- mmapM (mapM (liftDataType f)) dtinfo
  return $ Context cb' nb' pb' po' gb pend tyvars' ec' tybinds ct' dt'

mmapM :: (Monad m, Ord k) => (a -> m b) -> Map k a -> m (Map k b)
mmapM f ka = do
  kbl <- mapM (\(k, a) -> do b <- f a ; return (k, b)) (Map.toList ka)
  return $ Map.fromList kbl

liftTID :: Monad m => (t1 -> m t2) -> TypedId t1 -> m (TypedId t2)
liftTID f (TypedId t i) = do t2 <- f t ; return $ TypedId t2 i

liftCXB :: Monad m => (t1 -> m t2) -> CtxBound t1 -> m (CtxBound t2)
liftCXB f (tid, mb_ci) = do tid' <- liftTID f tid; return (tid' , mb_ci)

liftEffectCtorInfo f (cid, EffectCtor dctor ty) = do
  ty' <- f ty
  dctor' <- liftDataCtor f dctor
  return (cid, EffectCtor dctor' ty' )

liftCtorInfo :: Monad m => (t1 -> m t2) -> CtorInfo t1 -> m (CtorInfo t2)
liftCtorInfo f (CtorInfo cid datactor) =
  liftM (CtorInfo cid) (liftDataCtor f datactor)

liftDataType :: Monad m => (t1 -> m t2) -> DataType t1 -> m (DataType t2)
liftDataType f (DataType nm formals ctors isForeign srcrange) =
  liftM (\cs' ->DataType nm formals cs'   isForeign srcrange) (mapM (liftDataCtor f) ctors)

liftDataCtor :: Monad m => (t1 -> m t2) -> DataCtor t1 -> m (DataCtor t2)
liftDataCtor f (DataCtor dataCtorName formals types repr lone range) = do
  liftM (\tys-> DataCtor dataCtorName formals tys   repr lone range) (mapM f types)

liftPrimOp f primop =
  case primop of
    NamedPrim tid      -> liftM NamedPrim (liftTID f tid)
    PrimOp s ty        -> liftM (PrimOp s) (f ty)
    PrimIntTrunc s1 s2 -> return $ PrimIntTrunc s1 s2
    CoroPrim p t1 t2   -> liftM2 (CoroPrim p) (f t1) (f t2)
    PrimInlineAsm t cnt cns fx -> do t' <- f t
                                     return $ PrimInlineAsm t' cnt cns fx
    LookupEffectHandler tag -> return $ LookupEffectHandler tag

liftBinding :: Monad m => (t1 -> m t2) -> ContextBinding t1 -> m (ContextBinding t2)
liftBinding f (TermVarBinding s (TypedId t i, mb_cid)) = do
  t2 <- f t
  return $ TermVarBinding s (TypedId t2 i, mb_cid)

data TcConstraint =
    TcC_SeqUnit (MetaTyVar TypeTC)  -- eventually
  | TcC_IsFloat (MetaTyVar TypeTC)

-- Based on "Practical type inference for arbitrary rank types."
-- One significant difference is that we do not include the Gamma context
--   (mapping term variables to types) in the TcEnv, because we do not
--   want that part of the context "threaded through" type checking of
--   subexpressions. For example, we want each function in a SCC
--   of functions to be type checked in the same Gamma context. But
--   we do need to thread the supply of unique variables through...
data TcEnv = TcEnv { tcEnvUniqs        :: IORef Uniq
                   , tcUnificationVars :: IORef [MetaTyVar TypeTC]
                   , tcParents         :: [ExprAST TypeAST]
                   , tcMetaIntConstraints :: IORef (Map (MetaTyVar TypeTC) Int)
                   , tcConstraints        :: IORef [(TcConstraint, SourceRange)]
                   , tcSubsumptionConstraints :: IORef [(TypeTC, TypeTC)]
                   , tcCurrentFnEffect :: Maybe TypeTC
                   , tcCurrentLevel    :: Level
                   , tcPendingLevelAdjustments :: IORef [TypeTC]
                   , tcUseOptimizedCtorReprs :: Bool
                   , tcVerboseMode           :: Bool
                   }

newtype Tc a = Tc (TcEnv -> IO (OutputOr a))

unTc :: TcEnv -> Tc a    -> IO (OutputOr a)
unTc e (Tc f) =   f e

retOK :: a -> IO (OutputOr a)
retOK x = return (OK x)

instance Monad Tc where
    return = pure
    fail err = Tc $ \_env -> return (Errors [outLn err])
    m >>= k  = Tc $ \ env -> do result <- unTc env m
                                case result of
                                  OK expr -> unTc env (k expr)
                                  Errors ss -> return (Errors ss)

instance Functor     Tc where fmap  = liftM
instance Applicative Tc where pure x = Tc $ \_env -> return (OK x)
                              (<*>) = ap

-- | Given a Tc function and the result of a previous Tc action,
-- | fmap the function in OutputOr (and return a monadic value).
tcInject :: (a -> Tc b) -> (OutputOr a) -> Tc b
tcInject k result = Tc $ \env -> do case result of
                                      OK expr -> unTc env (k expr)
                                      Errors ss -> return (Errors ss)

-- Modifies the standard Tc monad bind operator
-- to append an error message, if necessary.
tcOnError []   m k = m >>= k
tcOnError msgs m k = Tc $ \env -> do result <- unTc env m
                                     case result of
                                           OK expr -> unTc env (k expr)
                                           Errors ss -> return (Errors $ msgs ++ ss)

tcWhenVerbose :: Tc () -> Tc ()
tcWhenVerbose action = Tc $ \env ->
  if tcVerboseMode env then unTc env action else retOK ()

tcLift :: IO a -> Tc a
tcLift action = Tc $ \_env -> action >>= retOK

tcWarn :: [Doc] -> Tc ()
tcWarn docs =
  tcLift $ putDocLn $ blue (text "Warning") <> text ": " <> vcat docs

tcFails :: [Doc] -> Tc a
tcFails errs = Tc $ \_env -> return $ Errors errs

tcFailsMore :: [Doc] -> Tc a
tcFailsMore errs = do
  parents <- tcGetCurrentHistory
  case reverse parents of -- parents returned in root-to-child order.
    []    -> tcFails $ errs ++ [text $ "[unscoped]"]
    (e:_) -> tcFails $ errs ++ [text $ "Unification failure triggered when " ++
                                       "typechecking source line:"
                               ,prettySourceRangeInfo (rangeOf e)
                               ,highlightFirstLineDoc (rangeOf e)]

sanityCheck :: Bool -> String -> Tc ()
sanityCheck cond msg = if cond then return () else tcFails [red (text msg)]

readTcMeta :: MetaTyVar ty -> Tc (TVar ty)
readTcMeta m = tcLift $ readIORef (mtvRef m)

writeTcMeta :: Show ty => MetaTyVar ty -> ty -> Tc ()
writeTcMeta m v = do
  --tcLift $ putStrLn $ "=========== Writing meta type variable: " ++ show ((mtvDesc m, mtvUniq m)) ++ " := " ++ show v
  tcLift $ writeIORef (mtvRef m) (BoundTo v)

-- Performs selective path compression: given input  x -> y -> T
--   mutates x to point directly to T, but does not allocate given x -> T.
-- Invariant: if the returned type is a meta type variable, it is unbound.
repr :: TypeTC -> Tc TypeTC
repr x = do
  case x of
    MetaTyVarTC m -> do mty <- readTcMeta m
                        case mty of
                          Unbound _ -> return x
                          BoundTo ty -> do 
                            case ty of -- Selective path compression
                              MetaTyVarTC _ -> do ty' <- repr ty
                                                  writeTcMetaTC m ty'
                                                  return ty'
                              _ -> return ty
    _ -> return x

shallowStripRefinedTypeTC (RefinedTypeTC v _ _) = tidType v
shallowStripRefinedTypeTC t                     = t

writeTcMetaTC m t = writeTcMeta m (shallowStripRefinedTypeTC t)

newTcSkolem (tv, k) = do u <- newTcUniq
                         return (SkolemTyVar (nameOf tv) u k)
  where nameOf (BoundTyVar name _)    = name
        nameOf (SkolemTyVar name _ _) = name

-- Lazy in its argument because typechecking uses an error value
-- as a default, expected-to-be-replaced marker.
newTcRef :: a -> Tc (IORef a)
newTcRef ~v = tcLift $ newIORef v

newTcUnificationVarEffect d = newTcUnificationVar_ MTVEffect d
newTcUnificationVarSigma  d = newTcUnificationVar_ MTVSigma d
newTcUnificationVarTau    d = newTcUnificationVar_ MTVTau d

newTcUnificationVar_ :: MTVQ -> String -> Tc TypeTC
newTcUnificationVar_ q desc = do
    lvl  <- tcGetLevel
    m <- newTcUnificationVarAtLevel lvl q desc
    return $ MetaTyVarTC m

newTcUnificationVarAtLevel :: Level -> MTVQ -> String -> Tc (MetaTyVar TypeTC)
newTcUnificationVarAtLevel lvl q desc = do
    u    <- newTcUniq
    ref  <- newTcRef (Unbound lvl)
    tcRecordUnificationVar (Meta q desc u ref)
      where
        -- The typechecking environment maintains a list of all the unification
        -- variables created, for introspection/debugging/statistics wankery.
        tcRecordUnificationVar :: MetaTyVar TypeTC -> Tc (MetaTyVar TypeTC)
        tcRecordUnificationVar m = Tc $ \env ->
                        do modIORef' (tcUnificationVars env) (m:); retOK m

-- Runs the given action with the given expression added to the "call stack";
-- this is used to keep track of the path to the current expression during
-- type checking.
tcWithScope :: ExprAST TypeAST -> Tc a -> Tc a
tcWithScope expr (Tc f)
    = Tc $ \env -> f (env { tcParents = expr:(tcParents env) })

tcWithCurrentFx :: TypeTC -> Tc a -> Tc a
tcWithCurrentFx fx (Tc f)
    = Tc $ \env -> f (env { tcCurrentFnEffect = Just fx })

-- Refinement expressions embedded in types must be completely pure, no fooling!
tcGetCurrentFnFx :: Tc TypeTC
tcGetCurrentFnFx = Tc $ \env -> do case tcCurrentFnEffect env of
                                     Nothing -> retOK (TyAppTC (TyConTC "effect.Empty") [])
                                     Just fx -> retOK fx

tcWithLevel :: Tc a -> Tc a
tcWithLevel (Tc f)
    = Tc $ \env -> f (env { tcCurrentLevel = 1 + (tcCurrentLevel env) })

tcGetLevel :: Tc Level
tcGetLevel = Tc $ \env -> do retOK $ tcCurrentLevel env

tcNeedsLevelAdjustment :: TypeTC -> Tc ()
tcNeedsLevelAdjustment typ = Tc $ \env -> do
  modIORef' (tcPendingLevelAdjustments env) (typ:)
  retOK ()

tcGetNeedsLevelAdjustments :: Tc [TypeTC]
tcGetNeedsLevelAdjustments = Tc $ \env -> do
  levs <- readIORef (tcPendingLevelAdjustments env)
  retOK levs

tcSetNeedsLevelAdjustments :: [TypeTC] -> Tc ()
tcSetNeedsLevelAdjustments levs = Tc $ \env -> do
  writeIORef (tcPendingLevelAdjustments env) levs
  retOK ()

tcReadLevels :: Levels -> Tc (Level, Level)
tcReadLevels ZeroLevels = return (0, 0)
tcReadLevels (Levels old new) = do
  o <- tcLift $ readIORef (ordRef old)
  n <- tcLift $ readIORef (ordRef new)
  return (o, n)


tcNewOrdRef :: a -> Tc (OrdRef a)
tcNewOrdRef a = do
  u <- newTcUniq
  r <- tcLift $ newIORef a
  return $ OrdRef u r

mkLevels :: Tc Levels
mkLevels = do
  curr <- tcGetLevel
  mkLevelsWith (curr, curr)

mkLevelsWith (o, n) = do
  old <- tcNewOrdRef o
  new <- tcNewOrdRef n
  return $ Levels old new

newTcUniq :: Tc Uniq
newTcUniq = Tc $ \env -> do let ref = tcEnvUniqs env
                            uniq <- readIORef ref
                            writeIORef ref (uniq + 1)
                            retOK uniq


tcFreshT t = newTcUniq >>= (\u -> return (Ident t u))

tcFresh :: String -> Tc Ident
tcFresh s = tcFreshT (T.pack s)

tcGetCurrentHistory :: Tc [ExprAST TypeAST]
tcGetCurrentHistory = Tc $ \env -> do retOK $ Prelude.reverse $ tcParents env

tcShouldUseOptimizedCtorReprs = Tc $ \env -> do retOK $ tcUseOptimizedCtorReprs env

tcAddConstraint :: TcConstraint -> SourceRange -> Tc ()
tcAddConstraint c sr = Tc $ \env -> do
  modIORef' (tcConstraints env) ((c,sr):)
  retOK ()

tcGetConstraints :: Tc [(TcConstraint, SourceRange)]
tcGetConstraints = Tc $ \env -> do
  cs <- readIORef (tcConstraints env)
  retOK cs

instance Ord (MetaTyVar ty) where
  compare m1 m2 = compare (mtvUniq m1) (mtvUniq m2)

tcUpdateIntConstraint :: MetaTyVar TypeTC -> Int -> Tc ()
tcUpdateIntConstraint km n = Tc $ \env -> do
  modIORef' (tcMetaIntConstraints env) (Map.insertWith max km n)
  retOK ()

--instance Show (MetaTyVar TypeTC)  where show m = show (MetaTyVarTC m)

tcApplyIntConstraints :: Tc ()
tcApplyIntConstraints = Tc $ \env -> do
  map <- readIORef (tcMetaIntConstraints env)
  mapM_ (\(m, neededBits) -> do
            writeIORef (mtvRef m) (BoundTo $ PrimIntTC (sizeOfBits neededBits)))
        (Map.toList map)
  retOK ()
 where
  sizeOfBits :: Int -> IntSizeBits
  sizeOfBits n | n <= 8  = I8
  sizeOfBits n | n <= 16 = I16
  sizeOfBits n | n <= 32 = I32
  sizeOfBits n | n <= 64 = I64
  sizeOfBits n = error $ "Context.hs: Unsupported integer size: " ++ show n


-- The type says it all: run a Tc action, and capture any errors explicitly.
tcIntrospect :: Tc a -> Tc (OutputOr a)
tcIntrospect action = Tc $ \env -> do unTc env action >>= retOK

isOK :: OutputOr ty -> Bool
isOK (OK _) = True
isOK _      = False

-----------------------------------------------------------------------

tcShowStructure :: (Structured a, Summarizable a) => a -> Tc Doc
tcShowStructure e = do
    header <- getStructureContextMessage
    return $ header <> showStructure e


getStructureContextMessage :: Tc Doc
getStructureContextMessage = do
    hist <- tcGetCurrentHistory
    let outputs = map (\e -> (text "\t\t") <> textOf e 40) hist
    return $ if null outputs
              then outLn "\tTop-level definition:"
              else outLn ""
