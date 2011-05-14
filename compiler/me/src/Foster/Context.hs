module Foster.Context where

import Data.IORef(IORef,newIORef,readIORef,writeIORef)
import Data.Maybe(isNothing)
import Control.Monad(liftM)

import Foster.Base
import Foster.ExprAST
import Foster.TypeAST

data ContextBinding = TermVarBinding String AnnVar
data Context = Context { contextBindings :: [ContextBinding]
                       , contextVerbose  :: Bool
                       }

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

-- Either, with better names for the cases...
data OutputOr expr
    = OK      expr
    | Errors  Output
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

newtype Tc a = Tc (TcEnv -> IO (OutputOr a))
unTc :: Tc a ->   (TcEnv -> IO (OutputOr a))
unTc   (Tc f) =   f

instance Monad Tc where
    return x = Tc (\_env -> return (OK x))
    fail err = Tc (\_env -> return (Errors (outLn err)))
    m >>= k = Tc (\env -> do { result <- unTc m env
                           ; case result of
                              OK expr -> unTc (k expr) env
                              Errors ss -> return (Errors ss)
                           })

-- Modifies the standard Tc monad bind operator
-- to append an error message, if necessary.
tcOnError Nothing  m k = m >>= k
tcOnError (Just o) m k = Tc (\env -> do { result <- unTc m env
                                        ; case result of
                                           OK expr -> unTc (k expr) env
                                           Errors ss -> return (Errors (ss ++ out "\n" ++ o))
                                        })

tcLift :: IO a -> Tc a
tcLift action = Tc (\_env -> do { r <- action; return (OK r) })

tcFails :: Output -> Tc a
tcFails errs = Tc (\_env -> return (Errors errs))

newTcRef :: a -> Tc (IORef a)
newTcRef v = tcLift $ newIORef v

readTcRef :: MetaTyVar -> Tc (Maybe Tau)
readTcRef (Meta _u r) = tcLift $ readIORef r

writeTcMeta :: MetaTyVar -> Tau -> Tc ()
writeTcMeta (Meta _u r) v = tcLift $ writeIORef r (Just v)

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
                             ; return (OK uniq)
                             })

tcFresh :: String -> Tc Ident
tcFresh s = do
    u <- newTcUniq
    return (Ident s u)

tcGetCurrentHistory :: Tc [ExprAST]
tcGetCurrentHistory = Tc (\tcenv -> do { return (OK $
                                          Prelude.reverse $ tcParents tcenv) })

wasSuccessful :: Tc a -> Tc Bool
wasSuccessful tce = liftM isNothing $ extractErrors tce

extractErrors :: Tc a -> Tc (Maybe Output)
extractErrors tce =
    Tc (\env -> do { result <- unTc tce env
                   ; case result of
                       OK expr   -> return (OK Nothing)
                       Errors ss -> return (OK (Just ss))
                       })

isOK :: OutputOr AnnExpr -> Bool
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

