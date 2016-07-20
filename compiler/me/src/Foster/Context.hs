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
liftContextM f (Context cb nb pb primops gb pend tyvars tybinds ctortypeast dtinfo) = do
  cb' <- mmapM (liftCXB f) cb
  nb' <- mmapM (liftCXB f) nb
  pb' <- mmapM (liftCXB f) pb
  po' <- mmapM (liftPrimOp f) primops
  tyvars' <- mmapM f tyvars
  ct' <- mmapM (mapM (liftCtorInfo f)) ctortypeast
  dt' <- mmapM (mapM (liftDataType f)) dtinfo
  return $ Context cb' nb' pb' po' gb pend tyvars' tybinds ct' dt'

mmapM :: (Monad m, Ord k) => (a -> m b) -> Map k a -> m (Map k b)
mmapM f ka = do
  kbl <- mapM (\(k, a) -> do b <- f a ; return (k, b)) (Map.toList ka)
  return $ Map.fromList kbl

liftTID :: Monad m => (t1 -> m t2) -> TypedId t1 -> m (TypedId t2)
liftTID f (TypedId t i) = do t2 <- f t ; return $ TypedId t2 i

liftCXB :: Monad m => (t1 -> m t2) -> CtxBound t1 -> m (CtxBound t2)
liftCXB f (tid, mb_ci) = do tid' <- liftTID f tid; return (tid' , mb_ci)

liftCtorInfo :: Monad m => (t1 -> m t2) -> CtorInfo t1 -> m (CtorInfo t2)
liftCtorInfo f (CtorInfo cid datactor) =
  liftM (CtorInfo cid) (liftDataCtor f datactor)

liftDataType :: Monad m => (t1 -> m t2) -> DataType t1 -> m (DataType t2)
liftDataType f (DataType nm formals ctors srcrange) =
  liftM (\cs' ->DataType nm formals cs' srcrange) (mapM (liftDataCtor f) ctors)

liftDataCtor :: Monad m => (t1 -> m t2) -> DataCtor t1 -> m (DataCtor t2)
liftDataCtor f (DataCtor dataCtorName formals types repr range) = do
  liftM (\tys-> DataCtor dataCtorName formals tys   repr range) (mapM f types)

liftPrimOp f primop =
  case primop of
    NamedPrim tid      -> liftM NamedPrim (liftTID f tid)
    PrimOp s ty        -> liftM (PrimOp s) (f ty)
    PrimIntTrunc s1 s2 -> return $ PrimIntTrunc s1 s2
    CoroPrim p t1 t2   -> liftM2 (CoroPrim p) (f t1) (f t2)
    PrimInlineAsm t cnt cns fx -> do t' <- f t
                                     return $ PrimInlineAsm t' cnt cns fx

liftBinding :: Monad m => (t1 -> m t2) -> ContextBinding t1 -> m (ContextBinding t2)
liftBinding f (TermVarBinding s (TypedId t i, mb_cid)) = do
  t2 <- f t
  return $ TermVarBinding s (TypedId t2 i, mb_cid)

data TcConstraint -- eventually

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
                   , tcUseOptimizedCtorReprs :: Bool
                   , tcVerboseMode           :: Bool
                   }

newtype Tc a = Tc (TcEnv -> IO (OutputOr a))

unTc :: TcEnv -> Tc a    -> IO (OutputOr a)
unTc e (Tc f) =   f e

retOK :: a -> IO (OutputOr a)
retOK x = return (OK x)

instance Monad Tc where
    return x = Tc $ \_env -> return (OK x)
    fail err = Tc $ \_env -> return (Errors [outLn err])
    m >>= k  = Tc $ \ env -> do result <- unTc env m
                                case result of
                                  OK expr -> unTc env (k expr)
                                  Errors ss -> return (Errors ss)

instance Functor     Tc where fmap  = liftM
instance Applicative Tc where pure  = return
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

readTcMeta :: MetaTyVar ty -> Tc (Maybe ty)
readTcMeta m = tcLift $ readIORef (mtvRef m)

writeTcMeta :: Show ty => MetaTyVar ty -> ty -> Tc ()
writeTcMeta m v = do
  --tcLift $ putStrLn $ "=========== Writing meta type variable: " ++ show ((mtvDesc m, mtvUniq m)) ++ " := " ++ show v
  tcLift $ writeIORef (mtvRef m) (Just v)

-- A "shallow" alternative to zonking which only peeks at the topmost tycon
shallowZonk :: TypeTC -> Tc TypeTC
shallowZonk (MetaTyVarTC m) = do
         mty <- readTcMeta m
         case mty of
             Nothing -> return (MetaTyVarTC m)
             Just ty -> do ty' <- shallowZonk ty
                           writeTcMetaTC m ty'
                           return ty'
shallowZonk t = return t

shallowStripRefinedTypeTC (RefinedTypeTC v _ _) = tidType v
shallowStripRefinedTypeTC t                     = t

writeTcMetaTC m t = writeTcMeta m (shallowStripRefinedTypeTC t)

newTcSkolem (tv, k) = do u <- newTcUniq
                         return (SkolemTyVar (nameOf tv) u k)
  where nameOf (BoundTyVar name _)    = name
        nameOf (SkolemTyVar name _ _) = name

newTcRef :: a -> Tc (IORef a)
newTcRef v = tcLift $ newIORef v

newTcUnificationVarEffect d = newTcUnificationVar_ MTVEffect d
newTcUnificationVarSigma  d = newTcUnificationVar_ MTVSigma d
newTcUnificationVarTau    d = newTcUnificationVar_ MTVTau d

newTcUnificationVar_ :: MTVQ -> String -> Tc TypeTC
newTcUnificationVar_ q desc = do
    u    <- newTcUniq
    ref  <- newTcRef Nothing
    meta <- tcRecordUnificationVar (Meta q desc u ref)
    return (MetaTyVarTC meta)
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

instance Show (MetaTyVar TypeTC)  where show m = show (MetaTyVarTC m)

tcApplyIntConstraints :: Tc ()
tcApplyIntConstraints = Tc $ \env -> do
  map <- readIORef (tcMetaIntConstraints env)
  mapM_ (\(m, neededBits) -> do writeIORef (mtvRef m)
                                    (Just $ PrimIntTC (sizeOfBits neededBits)))
        (Map.toList map)
  retOK ()

-- The type says it all: run a Tc action, and capture any errors explicitly.
tcIntrospect :: Tc a -> Tc (OutputOr a)
tcIntrospect action = Tc $ \env -> do unTc env action >>= retOK

isOK :: OutputOr ty -> Bool
isOK (OK _) = True
isOK _      = False

-----------------------------------------------------------------------

tcShowStructure :: (Structured a) => a -> Tc Doc
tcShowStructure e = do
    header <- getStructureContextMessage
    return $ header <> showStructure e


getStructureContextMessage :: Tc Doc
getStructureContextMessage = do
    hist <- tcGetCurrentHistory
    let outputs = map (\e -> (text "\t\t") <> textOf e 40) hist
    let output = case outputs of
                 [] -> (outLn $ "\tTop-level definition:")
                 _  -> (outLn $ "\tContext for AST below is:") <> vcat outputs
    return output
