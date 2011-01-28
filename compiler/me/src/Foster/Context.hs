module Foster.Context where

import Data.IORef(IORef,newIORef,readIORef,writeIORef)

import Foster.Base
import Foster.ExprAST

data ContextBinding = TermVarBinding String AnnVar
type Context = [ContextBinding]

instance Show ContextBinding where
    show (TermVarBinding s ty) = "(termvar " ++ s ++ " :: " ++ show ty

termVarLookup :: String -> Context -> Maybe AnnVar
termVarLookup name (bindings) =
    let termbindings = [(nm, annvar) | (TermVarBinding nm annvar) <- bindings] in
    lookup name termbindings

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
                   }

newtype Tc a = Tc (TcEnv -> IO (TypecheckResult a))
unTc :: Tc a ->   (TcEnv -> IO (TypecheckResult a))
unTc   (Tc a) = a

instance Monad Tc where
    return x = Tc (\_env -> return (Annotated x))
    fail err = Tc (\_env -> return (TypecheckErrors (outLn err)))
    m >>= k = Tc (\env -> do { result <- unTc m env
                          ; case result of
                              Annotated expr -> unTc (k expr) env
                              TypecheckErrors ss -> return (TypecheckErrors ss)
                          })

newUniq :: Tc Uniq
newUniq = Tc (\tcenv -> do { let ref = tcEnvUniqs tcenv
                          ; uniq <- readIORef ref
                          ; writeIORef ref (uniq + 1)
                          ; return (Annotated uniq)
                          })

tcFails :: Output -> Tc a
tcFails errs = Tc (\_env -> return (TypecheckErrors errs))

wasSuccessful :: Tc a -> Tc Bool
wasSuccessful tce =
    Tc (\env -> do { result <- unTc tce env
                   ; case result of
                       Annotated expr     -> return (Annotated True)
                       TypecheckErrors ss -> return (Annotated False)
                       })


isAnnotated :: TypecheckResult AnnExpr -> Bool
isAnnotated (Annotated _) = True
isAnnotated _ = False




-- Builds trees like this:
-- AnnSeq        :: i32
-- ├─AnnCall       :: i32
-- │ ├─AnnVar       expect_i32 :: ((i32) -> i32)
-- │ └─AnnTuple
-- │   └─AnnInt       999999 :: i32

showStructure :: (Expr a) => a -> Output
showStructure e = showStructureP e (out "") False where
    showStructureP e prefix isLast =
        let children = childrenOf e in
        let thisIndent = prefix ++ out (if isLast then "└─" else "├─") in
        let nextIndent = prefix ++ out (if isLast then "  " else "│ ") in
        let padding = max 6 (60 - Prelude.length thisIndent) in
        -- [ (child, index, numchildren) ]
        let childpairs = Prelude.zip3 children [1..]
                               (Prelude.repeat (Prelude.length children)) in
        let childlines = map (\(c, n, l) ->
                                showStructureP c nextIndent (n == l))
                             childpairs in
        (thisIndent :: Output) ++ (textOf e padding) ++ (out "\n") ++ (Prelude.foldl (++) (out "") childlines)

-----------------------------------------------------------------------
