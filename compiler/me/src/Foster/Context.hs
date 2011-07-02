module Foster.Context where

import Data.IORef(IORef,newIORef,readIORef,writeIORef)

import Foster.Base
import Foster.ExprAST
import Foster.TypeAST

data ContextBinding ty = TermVarBinding String (TypedId ty)
data Context ty = Context { contextBindings   :: [ContextBinding ty]
                          , primitiveBindings :: [ContextBinding ty]
                          , contextVerbose    :: Bool
                          }

emptyContext = Context [] [] True

prependContextBinding :: Context ty -> ContextBinding ty -> Context ty
prependContextBinding ctx prefix =
    ctx { contextBindings = prefix : (contextBindings ctx) }

prependContextBindings :: Context ty -> [ContextBinding ty] -> Context ty
prependContextBindings ctx prefix =
    ctx { contextBindings = prefix ++ (contextBindings ctx) }

instance (Show ty) => Show (ContextBinding ty) where
    show (TermVarBinding s annvar) = "(termvar " ++ s ++ " :: " ++ show annvar

ctxBoundIdents :: Context ty -> [Ident]
ctxBoundIdents ctx = [tidIdent v | TermVarBinding _ v <- (contextBindings ctx)]

termVarLookup :: String -> [ContextBinding ty] -> Maybe (TypedId ty)
termVarLookup name bindings =
    let termbindings = [(nm, annvar) | (TermVarBinding nm annvar) <- bindings] in
    lookup name termbindings

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
                   }

newtype Tc a = Tc (TcEnv -> IO (OutputOr a))
unTc :: TcEnv -> Tc a    -> IO (OutputOr a)
unTc e (Tc f) =   f e

instance Monad Tc where
    return x = Tc (\_env -> return (OK x))
    fail err = Tc (\_env -> return (Errors [outLn err]))
    m >>= k = Tc (\env -> do { result <- unTc env m
                             ; case result of
                                OK expr -> unTc env (k expr)
                                Errors ss -> return (Errors ss)
                             })

tcInject :: (OutputOr a) -> (a -> Tc b) -> Tc b
tcInject result k = Tc (\env -> do case result of
                                     OK expr -> unTc env (k expr)
                                     Errors ss -> return (Errors ss)
                       )

-- Modifies the standard Tc monad bind operator
-- to append an error message, if necessary.
--tcOnError :: (Maybe Output) ->
tcOnError Nothing  m k = m >>= k
tcOnError (Just o) m k = Tc (\env -> do { result <- unTc env m
                                        ; case result of
                                           OK expr -> unTc env (k expr)
                                           Errors ss -> return (Errors (o:ss))
                                        })

tcLift :: IO a -> Tc a
tcLift action = Tc (\_env -> do { r <- action; return (OK r) })

tcFails :: [Output] -> Tc a
tcFails errs = Tc (\_env -> return $ Errors errs)

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

tcRecordUnificationVar :: MetaTyVar -> Tc MetaTyVar
tcRecordUnificationVar m
    = Tc (\env -> do let vr = tcUnificationVars env
                     vs <- readIORef vr
                     writeIORef vr (m:vs)
                     return (OK m))

tcWithScope :: ExprAST -> Tc a -> Tc a
tcWithScope expr (Tc f)
    = Tc (\env -> f (env { tcParents = expr:(tcParents env) }))

newTcUniq :: Tc Uniq
newTcUniq = Tc (\tcenv -> do { let ref = tcEnvUniqs tcenv
                             ; uniq <- readIORef ref
                             ; writeIORef ref (uniq + 1)
                             ; return (OK uniq)
                             })

tcFresh :: String -> Tc Ident
tcFresh s = do
    u <- newTcUniq
    return (Ident s u)

tcGetCurrentHistory :: Tc [ExprAST]
tcGetCurrentHistory = Tc (\tcenv -> do { return (OK $
                                          Prelude.reverse $ tcParents tcenv) })

tcIntrospect :: Tc a -> Tc (OutputOr a)
tcIntrospect action =
    Tc (\env -> do { result <- unTc env action
                   ; return (OK result)
                   })

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
                    [] ->        (outLn $ "\tTop-level definition:")
                    otherwise -> (outLn $ "\tContext for AST below is:") ++ concat outputs
    return output

