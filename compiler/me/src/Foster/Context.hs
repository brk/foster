module Foster.Context where

import Data.IORef(IORef,newIORef,readIORef,writeIORef)

import Foster.Base
import Foster.ExprAST
import Foster.TypeAST

data ContextBinding = TermVarBinding String AnnVar
data Context = Context { contextBindings :: [ContextBinding]
                       --, contextTcHistory :: ContextHistory
                       }

--inExpr :: Context -> ExprAST -> Context
--inExpr c e = c { contextTcHistory = e : (contextTcHistory c) }

prependContextBinding :: Context -> ContextBinding -> Context
prependContextBinding ctx prefix =
    ctx { contextBindings = prefix : (contextBindings ctx) }

prependContextBindings :: Context -> [ContextBinding] -> Context
prependContextBindings ctx prefix =
    ctx { contextBindings = prefix ++ (contextBindings ctx) }

instance Show ContextBinding where
    show (TermVarBinding s annvar) = "(termvar " ++ s ++ " :: " ++ show annvar

ctxBoundIdents :: Context -> [Ident]
ctxBoundIdents ctx = [avarIdent v | TermVarBinding _ v <- (contextBindings ctx)]

termVarLookup :: String -> [ContextBinding] -> Maybe AnnVar
termVarLookup name bindings =
    let termbindings = [(nm, annvar) | (TermVarBinding nm annvar) <- bindings] in
    lookup name termbindings



--typecheckError ctx output = (contextTcHistory ctx, output)
typecheckError ctx output = output

-- Either, with better names for the cases...
data TypecheckResult expr
    = Annotated        expr
    | TypecheckErrors  Output
    deriving (Eq)

-- Based on "Practical type inference for arbitrary rank types."
-- One significant difference is that we do not include the Gamma context
--   (mapping term variables to types) in the TcEnv, because we do not
--   want that part of the context "threaded through" type checking of
--   subexpressions. For example, we want each function in a SCC
--   of functions to be type checked in the same Gamma context. But
--   we do need to thread the supply of unique variables through...
data TcEnv = TcEnv { tcEnvUniqs :: IORef Uniq
                   , tcParents  :: [ExprAST]
                   }

newtype Tc a = Tc (TcEnv -> IO (TypecheckResult a))
unTc :: Tc a ->   (TcEnv -> IO (TypecheckResult a))
unTc   (Tc f) =   f

instance Monad Tc where
    return x = Tc (\_env -> return (Annotated x))
    fail err = Tc (\_env -> return (TypecheckErrors (outLn err)))
    m >>= k = Tc (\env -> do { result <- unTc m env
                           ; case result of
                              Annotated expr -> unTc (k expr) env
                              TypecheckErrors ss -> return (TypecheckErrors ss)
                           })

tcLift :: IO a -> Tc a
tcLift action = Tc (\_env -> do { r <- action; return (Annotated r) })

newTcRef v = tcLift $ newIORef v

newTcUnificationVar :: Tc MetaTyVar
newTcUnificationVar = do
    u   <- newTcUniq
    ref <- newTcRef Nothing
    return $ Meta u ref

tcWithScope :: ExprAST -> Tc a -> Tc a
tcWithScope expr (Tc f)
    = Tc (\env -> f (env { tcParents = expr:(tcParents env) }))

newTcUniq :: Tc Uniq
newTcUniq = Tc (\tcenv -> do { let ref = tcEnvUniqs tcenv
                             ; uniq <- readIORef ref
                             ; writeIORef ref (uniq + 1)
                             ; return (Annotated uniq)
                             })

tcFresh :: String -> Tc Ident
tcFresh s = do
    u <- newTcUniq
    return (Ident s u)

tcGetCurrentHistory :: Tc [ExprAST]
tcGetCurrentHistory = Tc (\tcenv -> do { return (Annotated $
                                          Prelude.reverse $ tcParents tcenv) })

tcFails :: Output -> Tc a
tcFails errs = Tc (\_env -> return (TypecheckErrors errs))

wasSuccessful :: Tc a -> Tc Bool
wasSuccessful tce =
    Tc (\env -> do { result <- unTc tce env
                   ; case result of
                       Annotated expr     -> return (Annotated True)
                       TypecheckErrors ss -> return (Annotated False)
                       })

extractErrors :: Tc a -> Tc (Maybe Output)
extractErrors tce =
    Tc (\env -> do { result <- unTc tce env
                   ; case result of
                       Annotated expr     -> return (Annotated Nothing)
                       TypecheckErrors ss -> return (Annotated (Just ss))
                       })


isAnnotated :: TypecheckResult AnnExpr -> Bool
isAnnotated (Annotated _) = True
isAnnotated _ = False

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
