module Foster.ConvertExprAST where

import Foster.Base
import Foster.ExprAST
import Foster.Context

import Control.Monad.State(liftM, liftM2, liftM3)

convertModule :: (Show a, Show b) =>
                 (a -> Tc b) -> ModuleAST FnAST a -> Tc (ModuleAST FnAST b)
convertModule f (ModuleAST hash funs decls dts lines primdts) = do
         funs'  <- mapM (convertFun      f) funs
         decls' <- mapM (convertDecl     f) decls
         prims' <- mapM (convertDataType f) primdts
         dts'   <- mapM (convertDataType f) dts
         return $ ModuleAST hash funs' decls' dts' lines prims'

convertVar f (TypedId t i) = do ty <- f t
                                return $ TypedId ty i

convertFun :: Monad m => (a -> m b) -> FnAST a -> m (FnAST b)
convertFun f (FnAST rng nm tyformals formals body toplevel) = do
    formals' <- mapM (convertVar f) formals
    body'    <- convertExprAST f body
    return $ FnAST rng nm tyformals formals' body' toplevel

convertDecl :: Monad m => (a -> m b) -> (String, a) -> m (String, b)
convertDecl f (s, ty) = do t <- f ty ; return (s, t)

convertDataType :: (Show a, Show b) =>
                   (a -> Tc b) -> DataType a -> Tc (DataType b)
convertDataType f (DataType dtName tyformals ctors) = do
  cts <- mapM convertDataCtor ctors
  return $ DataType dtName tyformals cts
    where
      convertDataCtor (DataCtor dataCtorName n formals types) = do
        tys <- mapM f types
        return $ DataCtor dataCtorName n formals tys

liftMaybeM :: Monad m => (a -> m b) -> Maybe a -> m (Maybe b)
liftMaybeM f m = case m of Nothing ->         return Nothing
                           Just t  -> f t >>= return.Just

convertEVar f (VarAST mt name) = do ft <- liftMaybeM f mt; return $ VarAST ft name

convertPat :: Monad m => (a -> m b) -> EPattern a -> m (EPattern b)
convertPat f pat = case pat of
        EP_Wildcard rng          -> return (EP_Wildcard rng  )
        EP_Bool     rng b        -> return (EP_Bool     rng b)
        EP_Int      rng s        -> return (EP_Int      rng s)
        EP_Variable rng evar     -> liftM  (EP_Variable rng) (convertEVar f evar)
        EP_Tuple    rng pats     -> liftM  (EP_Tuple    rng) (mapM (convertPat f) pats)
        EP_Ctor     rng pats txt -> do pats' <- mapM (convertPat f) pats
                                       return $ EP_Ctor rng pats' txt

convertTermBinding :: Monad m => (a -> m b) -> TermBinding a -> m (TermBinding b)
convertTermBinding f (TermBinding evar expr) = do
  evar' <- convertEVar    f evar
  expr' <- convertExprAST f expr
  return $ TermBinding evar' expr'

convertExprAST :: Monad m => (x -> m z) -> ExprAST x -> m (ExprAST z)
convertExprAST f expr =
  let q = convertExprAST f in
  case expr of
    E_MachArrayLit rng es       -> liftM  (E_MachArrayLit rng) (mapM q es)
    E_StringAST    rng s        -> return $ (E_StringAST  rng) s
    E_BoolAST      rng b        -> return $ (E_BoolAST    rng) b
    E_IntAST       rng txt      -> return $ (E_IntAST     rng) txt
    E_RatAST       rng txt      -> return $ (E_RatAST     rng) txt
    E_PrimAST      rng nm       -> return $ (E_PrimAST    rng) nm
    E_CompilesAST  rng me       -> liftM  (E_CompilesAST  rng) (liftMaybeM q me)
    E_IfAST        rng    a b c -> liftM3 (E_IfAST        rng)   (q a) (q b) (q c)
    E_UntilAST     rng a b      -> liftM2 (E_UntilAST     rng)   (q a) (q b)
    E_SeqAST       rng a b      -> liftM2 (E_SeqAST       rng)   (q a) (q b)
    E_AllocAST     rng a rgn    -> liftM2 (E_AllocAST     rng)   (q a) (return rgn)
    E_DerefAST     rng a        -> liftM  (E_DerefAST     rng)   (q a)
    E_StoreAST     rng a b      -> liftM2 (E_StoreAST     rng)   (q a) (q b)
    E_TyApp        rng a tys    -> liftM2 (E_TyApp        rng)   (q a) (mapM f tys)
    E_TyCheck      rng a ty     -> liftM2 (E_TyCheck      rng)   (q a) (f ty)
    E_VarAST       rng v        -> liftM  (E_VarAST       rng) (convertEVar f v)
    E_TupleAST     rng exprs    -> liftM  (E_TupleAST     rng) (mapM q exprs)
    E_ArrayRead    rng (ArrayIndex a b rng2 s) -> do [x, y] <- mapM q [a, b]
                                                     return $ E_ArrayRead rng (ArrayIndex x y rng2 s)
    E_ArrayPoke    rng (ArrayIndex a b rng2 s) c -> do [x, y, z] <- mapM q [a, b, c]
                                                       return $ E_ArrayPoke rng (ArrayIndex x y rng2 s) z
    E_Case         rng e arms   -> do e'    <- q e
                                      arms' <- mapM (\(CaseArm pat body guard [] rng) -> do
                                                          body' <- q body
                                                          pat'  <- convertPat f pat
                                                          grd'  <- liftMaybe q guard
                                                          return (CaseArm pat' body' grd' [] rng)) arms
                                      return $ E_Case     rng  e' arms'
    E_LetRec       rng bnz e    -> liftM2 (E_LetRec       rng) (mapM (convertTermBinding f) bnz) (q e)
    E_LetAST       rng bnd e    -> liftM2 (E_LetAST       rng) (convertTermBinding f bnd) (q e)
    E_CallAST      rng b exprs  -> liftM2 (E_CallAST      rng) (q b) (mapM q exprs)
    E_FnAST        rng fn       -> liftM  (E_FnAST        rng) (convertFun f fn)
    E_KillProcess  rng a        -> liftM  (E_KillProcess  rng) (q a)

liftBinding :: Monad m => (t1 -> m t2) -> ContextBinding t1 -> m (ContextBinding t2)
liftBinding f (TermVarBinding s (TypedId t i, mb_cid)) = do
  t2 <- f t
  return $ TermVarBinding s (TypedId t2 i, mb_cid)

