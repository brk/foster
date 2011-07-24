-----------------------------------------------------------------------------
-- Copyright (c) 2011 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.KNExpr (
kNormalizeModule, KNExpr(..), typeKN
)

where

import Control.Monad.State

import Foster.Base
import Foster.Context
import Foster.TypeIL
import Foster.AnnExprIL

-- | Foster.ILExpr binds all intermediate values to named variables
-- | via a variant of K-normalization.

data KNExpr =
        -- Literals
          KNBool        Bool
        | KNInt         TypeIL LiteralInt
        | KNTuple       [AIVar]
        -- Control flow
        | KNIf          TypeIL AIVar  KNExpr KNExpr
        | KNUntil       TypeIL KNExpr KNExpr
        -- Creation of bindings
        | KNCase        TypeIL AIVar [(Pattern, KNExpr)]
        | KNLetVal       Ident KNExpr KNExpr
        | KNLetFuns    [Ident] [Fn KNExpr] KNExpr
        -- Use of bindings
        | KNVar         AIVar
        | KNCallPrim    TypeIL ILPrim [AIVar]
        | KNCall        TypeIL AIVar  [AIVar]
        -- Mutable ref cells
        | KNAlloc              AIVar
        | KNDeref       TypeIL AIVar
        | KNStore       TypeIL AIVar AIVar
        -- Array operations
        | KNAllocArray  TypeIL AIVar
        | KNArrayRead   TypeIL AIVar AIVar
        | KNArrayPoke          AIVar AIVar AIVar
        | KNTyApp       TypeIL KNExpr TypeIL
        deriving (Show)

data KNState = KNState {
    knUniq    :: Uniq
}

type KN a = State KNState a

knFresh :: String -> KN Ident
knFresh s = do old <- get
               put (old { knUniq = (knUniq old) + 1 })
               return (Ident s (knUniq old))

kNormalizeModule :: (ModuleAST (Fn AIExpr) TypeIL)
                 -> (ModuleAST (Fn KNExpr) TypeIL)
kNormalizeModule m =
    let nameOfBinding (TermVarBinding s _) = s in
    let knFuncsKN = mapM (kNormalizeFn) (moduleASTfunctions m) in
    let knFuncs = evalState knFuncsKN (KNState 0) in
    m { moduleASTfunctions = knFuncs }


kNormalizeFn :: (Fn AIExpr) -> KN (Fn KNExpr)
kNormalizeFn fn = do
    knbody <- kNormalize (fnBody fn)
    -- Ensure that return values are codegenned through a variable binding.
    namedReturnValue <- nestedLets [knbody] (\[v] -> KNVar v)
    return $ fn { fnBody = knbody }

kNormalize :: AIExpr -> KN KNExpr
kNormalize expr =
  let g = kNormalize in
  case expr of
      AIBool b          -> return $ KNBool b
      AIInt t i         -> return $ KNInt t i
      E_AIVar v         -> return $ KNVar v
      E_AIPrim p -> error $ "KNExpr.kNormalize: Should have detected prim " ++ show p

      AIAllocArray t a      -> do a' <- g a ; nestedLets [a'] (\[x] -> KNAllocArray t x)
      AIAlloc a             -> do a' <- g a ; nestedLets [a'] (\[x] -> KNAlloc x)
      AIDeref t a           -> do a' <- g a ; nestedLets [a'] (\[x] -> KNDeref t x)
      E_AITyApp t e argty   -> do e' <- g e ; return $ KNTyApp t e' argty
      AIStore t a (AISubscript _t b c)
                             -> do [a', b', c'] <- mapM g [a, b, c]
                                   nestedLets [a', b', c'] (\[x, y, z] -> KNArrayPoke x y z)
      AILetVar id a b   -> do [a', b'] <- mapM g [a, b] ; return $ buildLet id a' b'
      AIUntil   t  a b  -> do [a', b'] <- mapM g [a, b] ; return $ (KNUntil t a' b')
      AIStore t a b     -> do [a', b'] <- mapM g [a, b] ; nestedLets [a', b'] (\[x, y] -> KNStore t x y)
      AISubscript t a b -> do [a', b'] <- mapM g [a, b] ; nestedLets [a', b'] (\[x, y] -> KNArrayRead t x y)

      AILetFuns ids fns a   -> do knFns <- mapM kNormalizeFn fns
                                  a' <- g a
                                  return $ KNLetFuns ids knFns a'

      AITuple    es         -> do ks <- mapM g es
                                  nestedLets ks (\vs -> KNTuple vs)

      AICase t e bs         -> do e' <- g e
                                  ibs <- forM bs (\(p, ae) -> do ke <- g ae
                                                                 return (p, ke))
                                  nestedLets [e'] (\[va] -> KNCase t va ibs)

      x@(E_AIFn aiFn)       -> do fn_id <- knFresh "lit_fn"
                                  knFn <- kNormalizeFn aiFn
                                  let fnvar = KNVar $ TypedId (fnType aiFn) fn_id
                                  return $ KNLetFuns [fn_id] [knFn] fnvar

      AIIf      t  a b c    -> do cond_id <- knFresh ".ife"
                                  [a', b', c'] <- mapM g [a, b, c]
                                  let v = (TypedId (typeKN a') cond_id)
                                  return $ buildLet cond_id a' (KNIf t v b' c')
      AICall    t b es -> do
          cargs <- mapM g es
          case b of
              (E_AIPrim p) -> do nestedLets cargs (\vars -> (KNCallPrim t p vars))
              (E_AIVar v)  -> do nestedLets cargs (\vars -> (KNCall t v vars))
              _ -> do cb <- g b; nestedLets (cb:cargs) (\(vb:vars) -> (KNCall t vb vars))

buildLet :: Ident -> KNExpr -> KNExpr -> KNExpr
buildLet ident bound inexpr =
  case bound of
    (KNLetVal x' e' c') ->
         -- let i = (let x' = e' in c') in inexpr
         -- ==>
         -- let x' = e' in (let i = c' in inexpr)
         KNLetVal x' e' (buildLet ident c' inexpr)
    _ -> KNLetVal ident bound inexpr

-- | If we have a call like    base(foo, bar, blah)
-- | we want to transform it so that the args are all variables:
-- | let x1 = foo in
-- |  let x2 = bar in
-- |   let x3 = blah in
-- |     base(x1,x2,x3)
nestedLets :: [KNExpr] -> ([AIVar] -> KNExpr) -> KN KNExpr
-- | The fresh variables will be accumulated and passed to a
-- | continuation which generates a LetVal expr using the variables.
nestedLets exprs g = nestedLets' exprs [] g
  where
    nestedLets' :: [KNExpr] -> [AIVar] -> ([AIVar] -> KNExpr) -> KN KNExpr
    nestedLets' []     vars k = return $ k (reverse vars)
    nestedLets' (e:es) vars k =
        case e of
          -- No point in doing  let var1 = var2 in e...
          -- Instead, pass var2 to k instead of var1.
          (KNVar v) -> nestedLets' es (v:vars) k

          otherwise -> do
            x        <- knFresh ".x"
            let v = TypedId (typeKN e) x
            innerlet <- nestedLets' es (v:vars) k
            return $ buildLet x e innerlet

-- This is necessary due to transformations of AIIf and nestedLets
-- introducing new bindings, which requires synthesizing a type.
typeKN :: KNExpr -> TypeIL
typeKN (KNBool _)          = NamedTypeIL "i1"
typeKN (KNInt t _)         = t
typeKN (KNTuple vs)        = TupleTypeIL (map tidType vs)
typeKN (KNLetVal x b e)    = typeKN e
typeKN (KNLetFuns _ _ e)   = typeKN e
typeKN (KNCall t id expr)  = t
typeKN (KNCallPrim t id e) = t
typeKN (KNAllocArray elt_ty _) = ArrayTypeIL elt_ty
typeKN (KNIf t a b c)      = t
typeKN (KNUntil t a b)     = t
typeKN (KNAlloc v)         = PtrTypeIL (tidType v)
typeKN (KNDeref t _)       = t
typeKN (KNStore t _ _)     = t
typeKN (KNArrayRead t _ _) = t
typeKN (KNArrayPoke _ _ _) = TupleTypeIL []
typeKN (KNCase t _ _)      = t
typeKN (KNVar v)           = tidType v
typeKN (KNTyApp overallType tm tyArgs) = overallType

-- This instance is primarily needed as a prereq for KNExpr to be an AExpr.
instance Structured KNExpr where
    textOf e width =
        let spaces = Prelude.replicate width '\SP'  in
        case e of
            KNBool         b    -> out $ "KNBool      " ++ (show b)
            KNCall    t b a     -> out $ "KNCall      " ++ " :: " ++ show t
            KNCallPrim t prim a -> out $ "KNCallPrim  " ++ (show prim) ++ " :: " ++ show t
            KNLetVal   x b e    -> out $ "KNLetVal    " ++ (show x) ++ " :: " ++ (show $ typeKN b) ++ " = ... in ... "
            KNLetFuns {}        -> out $ "KNLetFuns   "
            KNIf      t  a b c  -> out $ "KNIf        " ++ " :: " ++ show t
            KNUntil   t  a b    -> out $ "KNUntil     " ++ " :: " ++ show t
            KNInt ty int        -> out $ "KNInt       " ++ (litIntText int) ++ " :: " ++ show ty
            KNAlloc v           -> out $ "KNAlloc     "
            KNDeref t a         -> out $ "KNDeref     "
            KNStore t a b       -> out $ "KNStore     "
            KNCase t _ bnds     -> out $ "KNCase      " ++ (show $ map fst bnds)
            KNAllocArray _ _    -> out $ "KNAllocArray "
            KNArrayRead  t a b  -> out $ "KNArrayRead " ++ " :: " ++ show t
            KNArrayPoke v b i   -> out $ "KNArrayPoke "
            KNTuple     es      -> out $ "KNTuple     (size " ++ (show $ length es) ++ ")"
            KNVar (TypedId t (GlobalSymbol name))
                                -> out $ "KNVar(Global):   " ++ name ++ " :: " ++ show t
            KNVar (TypedId t i) -> out $ "KNVar(Local):   " ++ show i ++ " :: " ++ show t
            KNTyApp t e argty   -> out $ "KNTyApp     [" ++ show argty ++ "] :: " ++ show t

    childrenOf e =
        let var v = KNVar v in
        case e of
            KNBool b                -> []
            KNInt t _               -> []
            KNUntil t a b           -> [a, b]
            KNTuple     vs          -> map var vs
            KNCase _ e bs           -> (var e):(map snd bs)
            KNLetFuns ids fns e     -> e : map fnBody fns
            KNLetVal x b e          -> [b, e]
            KNCall     t v vs       -> [var v] ++ [var v | v <- vs]
            KNCallPrim t v vs       ->            [var v | v <- vs]
            KNIf    t v b c         -> [var v, b, c]
            KNAlloc   v             -> [var v]
            KNAllocArray _ v        -> [var v]
            KNDeref t v             -> [var v]
            KNStore t v w           -> [var v, var w]
            KNArrayRead t a b       -> [var a, var b]
            KNArrayPoke v b i       -> [var v, var b, var i]
            KNVar _                 -> []
            KNTyApp t e argty       -> [e]

