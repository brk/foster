module Foster.Context where

import Data.IORef(IORef,newIORef,readIORef,writeIORef,modifyIORef)
import Data.Map(Map)

import qualified Data.Text as T

import Foster.Base
import Foster.ExprAST
import Foster.TypeAST
import Foster.Output(out, outLn, Output, OutputOr(..))

data ContextBinding ty = TermVarBinding T.Text (TypedId ty)

data Context ty = Context { contextBindings   :: [ContextBinding ty]
                          , primitiveBindings :: [ContextBinding ty]
                          , contextVerbose    :: Bool
                          , globalBindings    :: [ContextBinding ty]
                          }

prependContextBinding :: Context ty -> ContextBinding ty -> Context ty
prependContextBinding ctx prefix =
    ctx { contextBindings = prefix : (contextBindings ctx) }

prependContextBindings :: Context ty -> [ContextBinding ty] -> Context ty
prependContextBindings ctx prefix =
    ctx { contextBindings = prefix ++ (contextBindings ctx) }

instance (Show ty) => Show (ContextBinding ty) where
    show (TermVarBinding _s annvar) = "(termvar " ++ show annvar ++ ")"

ctxBoundIdents :: Context ty -> [Ident]
ctxBoundIdents ctx = [tidIdent v | TermVarBinding _ v <- (contextBindings ctx)]

termVarLookup :: T.Text -> [ContextBinding ty] -> Maybe (TypedId ty)
termVarLookup name bindings = Prelude.lookup name bindingslist where
    bindingslist = [(nm, annvar) | (TermVarBinding nm annvar) <- bindings]

-- Based on "Practical type inference for arbitrary rank types."
-- One significant difference is that we do not include the Gamma context
--   (mapping term variables to types) in the TcEnv, because we do not
--   want that part of the context "threaded through" type checking of
--   subexpressions. For example, we want each function in a SCC
--   of functions to be type checked in the same Gamma context. But
--   we do need to thread the supply of unique variables through...
data TcEnv = TcEnv { tcEnvUniqs :: IORef Uniq
                   , tcUnificationVars :: IORef [MetaTyVar]
                   , tcParents  :: [ExprAST]
                   , tcCtorInfo :: Map CtorName [CtorInfo TypeAST]
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

newTcRef :: a -> Tc (IORef a)
newTcRef v = tcLift $ newIORef v

readTcRef :: IORef a -> Tc a
readTcRef r = tcLift $ readIORef r

writeTcRef :: IORef a -> a -> Tc ()
writeTcRef r v = tcLift $ writeIORef r v

readTcMeta :: MetaTyVar -> Tc (Maybe Tau)
readTcMeta (Meta _ r _) = readTcRef r

writeTcMeta :: MetaTyVar -> Tau -> Tc ()
writeTcMeta (Meta _ r _) v = writeTcRef r (Just v)

newTcUnificationVar :: String -> Tc MetaTyVar
newTcUnificationVar desc = do
    u   <- newTcUniq
    ref <- newTcRef Nothing
    tcRecordUnificationVar (Meta u ref desc)
      where
        -- The typechecking environment maintains a list of all the unification
        -- variables created, for introspection/debugging/statistics wankery.
        tcRecordUnificationVar :: MetaTyVar -> Tc MetaTyVar
        tcRecordUnificationVar m = Tc $ \env ->
                        do modifyIORef (tcUnificationVars env) (m:); retOK m

-- Runs the given action with the given expression added to the "call stack";
-- this is used to keep track of the path to the current expression during
-- type checking.
tcWithScope :: ExprAST -> Tc a -> Tc a
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

tcGetCurrentHistory :: Tc [ExprAST]
tcGetCurrentHistory = Tc $ \env -> do retOK $ Prelude.reverse $ tcParents env

tcGetCtorInfo       = Tc $ \env -> do retOK $ tcCtorInfo env

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

