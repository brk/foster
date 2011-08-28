-----------------------------------------------------------------------------
-- Copyright (c) 2011 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.KNExpr (kNormalizeModule, KNExpr(..), typeKN)
where
import Control.Monad.State(forM, evalState, get, put, State)

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
        | KNLetFuns    [Ident] [Fn KNExpr TypeIL] KNExpr
        -- Use of bindings
        | KNVar         AIVar
        | KNCallPrim    TypeIL ILPrim [AIVar]
        | KNCall        TypeIL AIVar  [AIVar]
        | KNAppCtor     TypeIL CtorId [AIVar]
        -- Mutable ref cells
        | KNAlloc       AIVar
        | KNDeref       AIVar
        | KNStore       AIVar AIVar
        -- Array operations
        | KNAllocArray  TypeIL AIVar
        | KNArrayRead   TypeIL AIVar AIVar
        | KNArrayPoke          AIVar AIVar AIVar
        | KNTyApp       TypeIL AIVar TypeIL
        deriving (Show)

type KN a = State Uniq a

knFresh :: String -> KN Ident
knFresh s = do old <- get
               put (old + 1)
               return (Ident s old)

--------------------------------------------------------------------

kNormalizeModule :: (ModuleIL AIExpr TypeIL)
                 -> Context TypeIL
                 -> (ModuleIL KNExpr TypeIL)
kNormalizeModule m ctx =
    let nameOfBinding (TermVarBinding s _) = s in
    let knRegularFuncs = map kNormalizeFn (moduleILfunctions m) in
    -- TODO move ctor wrapping earlier?
    let knCtorFuncs    = concatMap (kNormalCtors ctx) (moduleILdataTypes m) in
    let knAllFuncsKN   = knRegularFuncs ++ knCtorFuncs in
    let knFuncs = evalState (sequence knAllFuncsKN) 0 in
    m { moduleILfunctions = knFuncs }


kNormalizeFn :: (Fn AIExpr TypeIL) -> KN (Fn KNExpr TypeIL)
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
      AIDeref   a           -> do a' <- g a ; nestedLets [a'] (\[x] -> KNDeref x)
      E_AITyApp t a argty   -> do a' <- g a ; nestedLets [a'] (\[x] -> KNTyApp t x argty)

      AILetVar id  a b  -> do [a', b'] <- mapM g [a, b] ; return $ buildLet id a' b'
      AIUntil    t a b  -> do [a', b'] <- mapM g [a, b] ; return $ (KNUntil t a' b')

      AIStore      a b  -> do [a', b'] <- mapM g [a, b] ; nestedLetsDo [a', b'] (\[x,y] -> knStore x y)
      AIArrayRead t a b -> do [a', b'] <- mapM g [a, b] ; nestedLets [a', b'] (\[x, y] -> KNArrayRead t x y)
      AIArrayPoke t a b c -> do [a', b', c'] <- mapM g [a,b,c]
                                nestedLets [a', b', c'] (\[x,y,z] -> KNArrayPoke x y z)

      AILetFuns ids fns a   -> do knFns <- mapM kNormalizeFn fns
                                  a' <- g a
                                  return $ KNLetFuns ids knFns a'

      AITuple    es         -> do ks <- mapM g es
                                  nestedLets ks (\vs -> KNTuple vs)

      AICase t e bs         -> do e' <- g e
                                  ibs <- forM bs (\(p, ae) -> do ke <- g ae
                                                                 return (p, ke))
                                  nestedLets [e'] (\[v] -> KNCase t v ibs)

      AIIf      t  a b c    -> do [a', b', c'] <- mapM g [a, b, c]
                                  nestedLets [a'] (\[v] -> KNIf t v b' c')
      AICall    t b es -> do
          cargs <- mapM g es
          case b of
              (E_AIPrim p) -> do nestedLets   cargs (\vars -> KNCallPrim t p vars)
              (E_AIVar v)  -> do nestedLetsDo cargs (\vars -> knCall t v vars)
              _ -> do cb <- g b; nestedLetsDo (cb:cargs) (\(vb:vars) -> knCall t vb vars)

--------------------------------------------------------------------
-- Type checking ignores the distinction between function types
-- marked as functions (which get an environment parameter added
-- during closure conversion) and procedures (which get no env arg).
--
-- But we can't ignore the distinction for the actual values with
-- that type mismatch, because the representations are different:
-- bare function pointer versus pointer to (code, env) pair.
-- So when we see code like (fn_expects_closure c_func),
-- we'll replace it with (fn_expects_closure { args... => c_func args... }).
--
-- We perform this transformation at this stage for two reasons:
--  * Doing it later, during or after closure conversion, complicates
--    the transformation: explicit env vars, making procs instead of thunks.
--  * Doing it earlier, directly after type checking, would involve duplicating
--    the nestedLets functions here. After all, (fec (ret_c_fnptr !)) should
--    become (let fnptr = ret_c_fnptr ! in fec { args.. => fnptr args.. } end),
--    NOT simply   fec { args... => (ret_c_fnptr !) args... }

knStore x y = do
  q <- varOrThunk (x, pointedToType $ tidType y)
  nestedLets [q] (\[z] -> KNStore z y)

knCall t a vs =
  case (tidType a) of
      FnTypeIL (TupleTypeIL tys) _ _ _ -> do
          args <- mapM varOrThunk (zip vs tys)
          nestedLets args (\xs -> KNCall t a xs)
      _ -> error $ "knCall: Called var had non-function type! " ++ show a

--------------------------------------------------------------------

varOrThunk :: (AIVar, TypeIL) -> KN KNExpr
varOrThunk (a, targetType) = do
  case needsClosureWrapper a targetType of
    Just fnty -> do withThunkFor a fnty (\z -> KNVar z)
    Nothing -> return (KNVar a)
  where
    needsClosureWrapper a ty =
      case (tidType a, ty) of
        (FnTypeIL x y z FT_Proc, FnTypeIL _ _ _ FT_Func) ->
            Just $ FnTypeIL x y z FT_Func
        _ -> Nothing

    withThunkFor :: AIVar -> TypeIL -> (AIVar -> KNExpr) -> KN KNExpr
    withThunkFor v fnty k = do
      fn <- mkThunkAround v fnty
      id <- knFresh ".kn.letfn"
      return $ KNLetFuns [id] [fn] $ k (TypedId fnty id)

      where

        mkThunkAround v fnty = do
          id <- knFresh ".kn.thunk"
          vars <- argVarsWithTypes (fnTypeILDomain fnty)
          return $ Fn { fnVar      = TypedId fnty (GlobalSymbol (show id))
                      , fnVars     = vars
                      , fnBody     = KNCall (fnTypeILRange fnty) v vars
                      , fnRange    = MissingSourceRange $ "thunk for " ++ show v
                      , fnFreeVars = case tidIdent v of
                                        Ident _ _      -> [v]
                                        GlobalSymbol _ -> []
                      }

        argVarsWithTypes (TupleTypeIL tys) = do
          let tidOfType ty = do id <- knFresh ".arg"
                                return $ TypedId ty id
          mapM tidOfType tys

        argVarsWithTypes ty = argVarsWithTypes (TupleTypeIL [ty])

--------------------------------------------------------------------

buildLet :: Ident -> KNExpr -> KNExpr -> KNExpr
buildLet ident bound inexpr =
  case bound of
    -- Convert  let i = (let x' = e' in c') in inexpr
    -- ==>      let x' = e' in (let i = c' in inexpr)
    KNLetVal x' e' c' ->
         KNLetVal x' e' (buildLet ident c' inexpr)

    -- Convert  let f = letfuns g = ... in g in <<f>>
    --     to   letfuns g = ... in let f = g in <<f>>
    KNLetFuns ids fns a ->
      KNLetFuns ids fns (buildLet ident a inexpr)

    _ -> KNLetVal ident bound inexpr


-- | If we have a call like    base(foo, bar, blah)
-- | we want to transform it so that the args are all variables:
-- | let x1 = foo in
-- |  let x2 = bar in
-- |   let x3 = blah in
-- |     base(x1,x2,x3)
-- | The fresh variables will be accumulated and passed to a
-- | continuation which generates a LetVal expr using the variables.
nestedLetsDo :: [KNExpr] -> ([AIVar] -> KN KNExpr) -> KN KNExpr
nestedLetsDo exprs g = nestedLets' exprs [] g
  where
    nestedLets' :: [KNExpr] -> [AIVar] -> ([AIVar] -> KN KNExpr) -> KN KNExpr
    nestedLets' []     vars k = k (reverse vars)
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

-- Usually, we can get by with a pure continuation.
nestedLets :: [KNExpr] -> ([AIVar] -> KNExpr) -> KN KNExpr
nestedLets exprs g = nestedLetsDo exprs (\vars -> return $ g vars)

-- Produces a list of (K-normalized) functions, eta-expansions of each ctor.
kNormalCtors :: Context TypeIL -> DataType TypeIL -> [KN (Fn KNExpr TypeIL)]
kNormalCtors ctx dtype = map (kNormalCtor ctx dtype) (dataTypeCtors dtype)
  where
    kNormalCtor :: Context TypeIL -> DataType TypeIL -> DataCtor TypeIL
                -> KN (Fn KNExpr TypeIL)
    kNormalCtor ctx (DataType dname _) (DataCtor cname small tys) = do
      let cid = CtorId dname cname (Prelude.length tys) small
      vars <- mapM (\t -> do fresh <- knFresh ".autogen"
                             return $ TypedId t fresh) tys
      let (Just tid) = termVarLookup cname (contextBindings ctx)
      return $ Fn { fnVar   = tid
                  , fnVars  = vars
                  , fnBody  = KNAppCtor (NamedTypeIL dname) cid vars
                  , fnRange = MissingSourceRange ("kNormalCtor " ++ show cid)
                  , fnFreeVars = []
                  }

-- This is necessary due to transformations of AIIf and nestedLets
-- introducing new bindings, which requires synthesizing a type.
typeKN :: KNExpr -> TypeIL
typeKN (KNBool _)          = boolTypeIL
typeKN (KNInt t _)         = t
typeKN (KNTuple vs)        = TupleTypeIL (map tidType vs)
typeKN (KNLetVal x b e)    = typeKN e
typeKN (KNLetFuns _ _ e)   = typeKN e
typeKN (KNCall t id expr)  = t
typeKN (KNCallPrim t id e) = t
typeKN (KNAppCtor t _ _  ) = t
typeKN (KNAllocArray elt_ty _) = ArrayTypeIL elt_ty
typeKN (KNIf t a b c)      = t
typeKN (KNUntil t a b)     = t
typeKN (KNAlloc v)         = PtrTypeIL (tidType v)
typeKN (KNDeref v)         = pointedToTypeOfVar v
typeKN (KNStore _ _)       = TupleTypeIL []
typeKN (KNArrayRead t _ _) = t
typeKN (KNArrayPoke _ _ _) = TupleTypeIL []
typeKN (KNCase t _ _)      = t
typeKN (KNVar v)           = tidType v
typeKN (KNTyApp overallType tm tyArgs) = overallType

-- This instance is primarily needed as a prereq for KNExpr to be an AExpr,
-- which ((childrenOf)) is needed in ILExpr for closedNamesOfKnFn.
instance Structured KNExpr where
    textOf e width =
        let spaces = Prelude.replicate width '\SP'  in
        case e of
            KNBool         b    -> out $ "KNBool      " ++ (show b)
            KNCall    t b a     -> out $ "KNCall      " ++ " :: " ++ show t
            KNCallPrim t prim a -> out $ "KNCallPrim  " ++ (show prim) ++ " :: " ++ show t
            KNAppCtor  t cid vs -> out $ "KNAppCtor   " ++ (show cid) ++ " :: " ++ show t
            KNLetVal   x b e    -> out $ "KNLetVal    " ++ (show x) ++ " :: " ++ (show $ typeKN b) ++ " = ... in ... "
            KNLetFuns {}        -> out $ "KNLetFuns   "
            KNIf      t  a b c  -> out $ "KNIf        " ++ " :: " ++ show t
            KNUntil   t  a b    -> out $ "KNUntil     " ++ " :: " ++ show t
            KNInt ty int        -> out $ "KNInt       " ++ (litIntText int) ++ " :: " ++ show ty
            KNAlloc v           -> out $ "KNAlloc     "
            KNDeref   a         -> out $ "KNDeref     "
            KNStore   a b       -> out $ "KNStore     "
            KNCase t _ bnds     -> out $ "KNCase      " ++ (show $ map fst bnds)
            KNAllocArray _ _    -> out $ "KNAllocArray "
            KNArrayRead  t a b  -> out $ "KNArrayRead " ++ " :: " ++ show t
            KNArrayPoke v b i   -> out $ "KNArrayPoke "
            KNTuple     es      -> out $ "KNTuple     (size " ++ (show $ length es) ++ ")"
            KNVar (TypedId t (GlobalSymbol name))
                                -> out $ "KNVar(Global):   " ++ name ++ " :: " ++ show t
            KNVar (TypedId t i) -> out $ "KNVar(Local):   " ++ show i ++ " :: " ++ show t
            KNTyApp t e argty   -> out $ "KNTyApp     [" ++ show argty ++ "] :: " ++ show t
    structuredChildren e = map SS $ childrenOf e
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
            KNAppCtor  t c vs       ->            [var v | v <- vs]
            KNIf    t v b c         -> [var v, b, c]
            KNAlloc   v             -> [var v]
            KNAllocArray _ v        -> [var v]
            KNDeref   v             -> [var v]
            KNStore   v w           -> [var v, var w]
            KNArrayRead t a b       -> [var a, var b]
            KNArrayPoke v b i       -> [var v, var b, var i]
            KNVar _                 -> []
            KNTyApp t v argty       -> [var v]

