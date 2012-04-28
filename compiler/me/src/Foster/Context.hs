module Foster.Context where

import Data.IORef(IORef,newIORef,readIORef,writeIORef,modifyIORef)
import Data.Map(Map)
import Data.List(foldl')
import qualified Data.Map as Map

import qualified Data.Text as T

import Foster.Base
import Foster.Kind
import Foster.ExprAST
import Foster.TypeAST
import Foster.Output(out, outLn, Output, OutputOr(..))

data ContextBinding ty = TermVarBinding T.Text (TypedId ty)

data Context ty = Context { contextBindings   :: Map T.Text (TypedId ty) -- [ContextBinding ty]
                          , primitiveBindings :: Map T.Text (TypedId ty)
                          , contextVerbose    :: Bool
                          , globalBindings    :: [ContextBinding ty]
                          , contextTypeBindings :: [(TyVar, Kind)]
                          , contextCtorInfo   :: Map CtorName [CtorInfo TypeAST]
                          }

prependBinding :: Map T.Text (TypedId ty) -> ContextBinding ty -> Map T.Text (TypedId ty)
prependBinding m (TermVarBinding nm tid) = Map.insert nm tid m

prependContextBinding :: Context ty -> ContextBinding ty -> Context ty
prependContextBinding ctx binding =
    ctx { contextBindings = prependBinding (contextBindings ctx) binding }

prependContextBindings :: Context ty -> [ContextBinding ty] -> Context ty
prependContextBindings ctx prefix =
    ctx { contextBindings = foldl' prependBinding (contextBindings ctx) prefix }

instance (Show ty) => Show (ContextBinding ty) where
    show (TermVarBinding _s annvar) = "(termvar " ++ show annvar ++ ")"

termVarLookup :: T.Text -> Map T.Text (TypedId ty) -> Maybe (TypedId ty)
termVarLookup name bindings = Map.lookup name bindings

-- Based on "Practical type inference for arbitrary rank types."
-- One significant difference is that we do not include the Gamma context
--   (mapping term variables to types) in the TcEnv, because we do not
--   want that part of the context "threaded through" type checking of
--   subexpressions. For example, we want each function in a SCC
--   of functions to be type checked in the same Gamma context. But
--   we do need to thread the supply of unique variables through...
data TcEnv = TcEnv { tcEnvUniqs :: IORef Uniq
                   , tcUnificationVars :: IORef [MetaTyVar]
                   , tcParents  :: [ExprAST TypeAST]
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

-- | Given a Tc function and the result of a previous Tc action,
-- | fmap the function in OutputOr (and return a monadic value).
tcInject :: (a -> Tc b) -> (OutputOr a) -> Tc b
tcInject k result = Tc $ \env -> do case result of
                                      OK expr -> unTc env (k expr)
                                      Errors ss -> return (Errors ss)

-- Modifies the standard Tc monad bind operator
-- to append an error message, if necessary.
tcOnError Nothing  m k = m >>= k
tcOnError (Just o) m k = Tc $ \env -> do result <- unTc env m
                                         case result of
                                           OK expr -> unTc env (k expr)
                                           Errors ss -> return (Errors (o:ss))

tcLift :: IO a -> Tc a
tcLift action = Tc $ \_env -> action >>= retOK

tcFails :: [Output] -> Tc a
tcFails errs = Tc $ \_env -> return $ Errors errs

readTcMeta :: MetaTyVar -> Tc (Maybe Tau)
readTcMeta m = tcLift $ readIORef (mtvRef m)

writeTcMeta :: MetaTyVar -> Tau -> Tc ()
writeTcMeta m v = do
  --tcLift $ putStrLn $ "=========== Writing meta type variable: " ++ show (MetaTyVar m) ++ " := " ++ show v
  tcLift $ writeIORef (mtvRef m) (Just v)

newTcSkolem (tv, k) = do u <- newTcUniq
                         return (SkolemTyVar (nameOf tv) u k)
  where nameOf (BoundTyVar name)      = name
        nameOf (SkolemTyVar name _ _) = name

newTcUnificationVarSigma d = newTcUnificationVar_ MTVSigma d
newTcUnificationVarTau   d = newTcUnificationVar_ MTVTau d

newTcUnificationVar_ :: MTVQ -> String -> Tc TypeAST
newTcUnificationVar_ q desc = do
    u    <- newTcUniq
    ref  <- newTcRef Nothing
    meta <- tcRecordUnificationVar (Meta q desc u ref)
    return (MetaTyVar meta)
      where
        newTcRef :: a -> Tc (IORef a)
        newTcRef v = tcLift $ newIORef v

        -- The typechecking environment maintains a list of all the unification
        -- variables created, for introspection/debugging/statistics wankery.
        tcRecordUnificationVar :: MetaTyVar -> Tc MetaTyVar
        tcRecordUnificationVar m = Tc $ \env ->
                        do modifyIORef (tcUnificationVars env) (m:); retOK m

-- Runs the given action with the given expression added to the "call stack";
-- this is used to keep track of the path to the current expression during
-- type checking.
tcWithScope :: ExprAST TypeAST -> Tc a -> Tc a
tcWithScope expr (Tc f)
    = Tc $ \env -> f (env { tcParents = expr:(tcParents env) })

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

-- The type says it all: run a Tc action, and capture any errors explicitly.
tcIntrospect :: Tc a -> Tc (OutputOr a)
tcIntrospect action = Tc $ \env -> do unTc env action >>= retOK

isOK :: OutputOr ty -> Bool
isOK (OK _) = True
isOK _      = False

-----------------------------------------------------------------------

tcShowStructure :: (Structured a) => a -> Tc Output
tcShowStructure e = do
    header <- getStructureContextMessage
    return $ header ++ showStructure e


getStructureContextMessage :: Tc Output
getStructureContextMessage = do
    hist <- tcGetCurrentHistory
    let outputs = map (\e -> (out "\t\t") ++ textOf e 40 ++ outLn "") hist
    let output = case outputs of
                 [] -> (outLn $ "\tTop-level definition:")
                 _  -> (outLn $ "\tContext for AST below is:") ++ concat outputs
    return output

