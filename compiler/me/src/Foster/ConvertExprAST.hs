module Foster.ConvertExprAST where

import Foster.Base
import Foster.ExprAST
import Foster.Context

import Control.Monad.State(liftM, liftM2, liftM3)

convertModule :: (Show a, Show b) =>
                 (a -> Tc b) -> ModuleAST FnAST a -> Tc (ModuleAST FnAST b)
convertModule f (ModuleAST funs decls dts lines) = do
         funs'  <- mapM (convertFun      f) funs
         decls' <- mapM (convertDecl     f) decls
         dts'   <- mapM (convertDataType f) dts
         return $ ModuleAST funs' decls' dts' lines

convertVar f (TypedId t i) = do ty <- f t
                                return $ TypedId ty i

convertFun :: (a -> Tc b) -> FnAST a -> Tc (FnAST b)
convertFun f (FnAST rng nm tyformals retType formals body toplevel) = do
    retType' <- liftMaybeTc f retType
    formals' <- mapM (convertVar f) formals
    body'    <- convertExprAST f body
    return $ FnAST rng nm tyformals retType' formals' body' toplevel

convertDecl :: (a -> Tc b) -> (String, a) -> Tc (String, b)
convertDecl f (s, ty) = do t <- f ty ; return (s, t)

convertDataType :: (Show a, Show b) =>
                   (a -> Tc b) -> DataType a -> Tc (DataType b)
convertDataType f (DataType dtName tyformals ctors) = do
  cts <- mapM convertDataCtor ctors
  return $ DataType dtName tyformals cts
    where
      convertDataCtor (DataCtor dataCtorName n types) = do
        tys <- mapM f types
        return $ DataCtor dataCtorName n tys

liftMaybeTc :: (a -> Tc b) -> Maybe a -> Tc (Maybe b)
liftMaybeTc f m = case m of Nothing ->         return Nothing
                            Just t  -> f t >>= return.Just

convertEVar f (VarAST mt name) = do ft <- liftMaybeTc f mt; return $ VarAST ft name

convertPat :: (a -> Tc b) -> EPattern a -> Tc (EPattern b)
convertPat f pat = case pat of
        EP_Wildcard rng          -> return (EP_Wildcard rng  )
        EP_Bool     rng b        -> return (EP_Bool     rng b)
        EP_Int      rng s        -> return (EP_Int      rng s)
        EP_Variable rng evar     -> liftM  (EP_Variable rng) (convertEVar f evar)
        EP_Tuple    rng pats     -> liftM  (EP_Tuple    rng) (mapM (convertPat f) pats)
        EP_Ctor     rng pats txt -> do pats' <- mapM (convertPat f) pats
                                       return $ EP_Ctor rng pats' txt

convertTuple :: (a -> Tc b) -> TupleAST a -> Tc (TupleAST b)
convertTuple f (TupleAST rng exprs) = do
  exprs' <- mapM (convertExprAST f) exprs
  return $ TupleAST rng exprs'

convertTermBinding :: (a -> Tc b) -> TermBinding a -> Tc (TermBinding b)
convertTermBinding f (TermBinding evar expr) = do
  evar' <- convertEVar    f evar
  expr' <- convertExprAST f expr
  return $ TermBinding evar' expr'

convertExprAST :: (x -> Tc z) -> ExprAST x -> Tc (ExprAST z)
convertExprAST f expr =
  let q = convertExprAST f in
  case expr of
    E_StringAST    rng s        -> return $ (E_StringAST    rng) s
    E_BoolAST      rng b        -> return $ (E_BoolAST      rng) b
    E_IntAST       rng txt      -> return $ (E_IntAST       rng) txt
    E_CompilesAST  rng me       -> liftM  (E_CompilesAST  rng) (liftMaybeTc q me)
    E_IfAST        rng    a b c -> liftM3 (E_IfAST        rng)   (q a) (q b) (q c)
    E_UntilAST     rng a b      -> liftM2 (E_UntilAST     rng)   (q a) (q b)
    E_SeqAST       rng a b      -> liftM2 (E_SeqAST       rng)   (q a) (q b)
    E_AllocAST     rng a        -> liftM  (E_AllocAST     rng)   (q a)
    E_DerefAST     rng a        -> liftM  (E_DerefAST     rng)   (q a)
    E_StoreAST     rng a b      -> liftM2 (E_StoreAST     rng)   (q a) (q b)
    E_ArrayRead    rng a b      -> liftM2 (E_ArrayRead    rng)   (q a) (q b)
    E_ArrayPoke    rng a b c    -> liftM3 (E_ArrayPoke    rng)   (q a) (q b) (q c)
    E_TyApp        rng a mt     -> liftM2 (E_TyApp        rng)   (q a) (liftMaybe f mt)
    E_VarAST       rng v        -> liftM  (E_VarAST       rng) (convertEVar f v)
    E_TupleAST tup              -> liftM  (E_TupleAST        ) (convertTuple f tup)
    E_Case         rng e bs     -> do e' <- q e
                                      bs' <- mapM (\(pat, exp) -> do
                                                          exp' <- q exp
                                                          pat' <- convertPat f pat
                                                          return (pat', exp' )) bs
                                      return $ E_Case     rng  e' bs'
    E_LetRec       rng bnz e    -> liftM2 (E_LetRec       rng) (mapM (convertTermBinding f) bnz) (q e)
    E_LetAST       rng bnd e    -> liftM2 (E_LetAST       rng) (convertTermBinding f bnd) (q e)
    E_CallAST      rng b tup    -> liftM2 (E_CallAST      rng) (q b) (convertTuple f tup)
    E_FnAST fn                  -> liftM  (E_FnAST           ) (convertFun f fn)

liftMaybe :: Monad m => (a -> m b) -> Maybe a -> m (Maybe b)
liftMaybe _ Nothing = return Nothing
liftMaybe f (Just a) = do b <- f a ; return $ Just b

liftBinding :: Monad m => (t1 -> m t2) -> ContextBinding t1 -> m (ContextBinding t2)
liftBinding f (TermVarBinding s (TypedId t i)) = do
  t2 <- f t
  return $ TermVarBinding s (TypedId t2 i)

