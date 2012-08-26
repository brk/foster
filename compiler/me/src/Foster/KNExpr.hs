{-# LANGUAGE StandaloneDeriving #-}
-----------------------------------------------------------------------------
-- Copyright (c) 2011 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.KNExpr (kNormalizeModule, KNExpr, KNExpr'(..), TailQ(..), typeKN,
                      renderKN, renderKNM, renderKNF, renderKNFM) where

import Control.Monad.State(forM, evalState, get, put, State)
import qualified Data.Text as T

import Foster.MonoType
import Foster.Base
import Foster.Context
import Foster.TypeIL
import Foster.AnnExprIL
import Foster.Output(out, outToString)
import Text.PrettyPrint.ANSI.Leijen

-- | Foster.KNExpr binds all intermediate values to named variables
-- | via a variant of K-normalization.

data KNExpr' ty =
        -- Literals
          KNBool        ty Bool
        | KNString      ty T.Text
        | KNInt         ty LiteralInt
        | KNFloat       ty LiteralFloat
        | KNTuple       ty [TypedId ty] SourceRange
        | KNKillProcess ty T.Text
        -- Control flow
        | KNIf          ty (TypedId ty)  (KNExpr' ty) (KNExpr' ty)
        | KNUntil       ty (KNExpr' ty)  (KNExpr' ty) SourceRange
        -- Creation of bindings
        | KNCase        ty (TypedId ty) [PatternBinding (KNExpr' ty) ty]
        | KNLetVal      Ident      (KNExpr' ty)     (KNExpr' ty)
        | KNLetFuns    [Ident] [Fn (KNExpr' ty) ty] (KNExpr' ty)
        -- Use of bindings
        | KNVar         (TypedId ty)
        | KNCallPrim    ty (FosterPrim ty) [TypedId ty]
        | KNCall TailQ  ty (TypedId ty)    [TypedId ty]
        | KNAppCtor     ty CtorId [TypedId ty]
        -- Mutable ref cells
        | KNAlloc       ty (TypedId ty) AllocMemRegion
        | KNDeref       ty (TypedId ty)
        | KNStore       ty (TypedId ty) (TypedId ty)
        -- Array operations
        | KNAllocArray  ty (TypedId ty)
        | KNArrayRead   ty (ArrayIndex (TypedId ty))
        | KNArrayPoke   ty (ArrayIndex (TypedId ty)) (TypedId ty)
        | KNTyApp       ty (TypedId ty) [ty]

-- When monmomorphizing, we use (KNTyApp t v [])
-- to represent a bitcast to type t.

type KN a = State Uniq a

type KNExpr = KNExpr' TypeIL

knFresh :: String -> KN Ident
knFresh s = do old <- get
               put (old + 1)
               return (Ident (T.pack s) old)

--------------------------------------------------------------------

kNormalizeModule :: (ModuleIL AIExpr TypeIL)
                 -> Context TypeIL
                 -> (ModuleIL KNExpr TypeIL)
kNormalizeModule m ctx =
    -- TODO move ctor wrapping earlier?
    let knCtorFuncs = concatMap (kNormalCtors ctx) (moduleILprimTypes m ++
                                                    moduleILdataTypes m) in
    let knWrappedBody = do { ctors <- sequence knCtorFuncs
                           ; body  <- kNormalize YesTail (moduleILbody m)
                           ; return $ wrapFns ctors body
                           } in
    m { moduleILbody = evalState knWrappedBody 0 }
      where
        wrapFns :: [Fn KNExpr TypeIL] -> KNExpr -> KNExpr
        wrapFns fs e = foldr (\f body -> KNLetFuns [fnIdent f] [f] body) e fs

kNormalizeFn :: (Fn AIExpr TypeIL) -> KN (Fn KNExpr TypeIL)
kNormalizeFn fn = do
    knbody <- kNormalize YesTail (fnBody fn)
    return $ fn { fnBody = knbody }

-- ||||||||||||||||||||||| K-Normalization ||||||||||||||||||||||{{{
kNormalize :: TailQ -> AIExpr -> KN KNExpr
kNormalize mebTail expr =
  let gt = kNormalize mebTail in
  let gn = kNormalize NotTail in
  case expr of
      AIString s        -> return $ KNString stringTypeIL s
      AIBool b          -> return $ KNBool   boolTypeIL   b
      AIInt t i         -> return $ KNInt t i
      AIFloat t f       -> return $ KNFloat t f
      E_AIVar v         -> return $ KNVar v
      AIKillProcess t m -> return $ KNKillProcess t m
      E_AIPrim p -> error $ "KNExpr.kNormalize: Should have detected prim " ++ show p

      AIAllocArray t a      -> do a' <- gn a ; nestedLets [a'] (\[x] -> KNAllocArray (ArrayTypeIL t) x)
      AIAlloc a rgn         -> do a' <- gn a ; nestedLets [a'] (\[x] -> KNAlloc (PtrTypeIL $ tidType x) x rgn)
      AIDeref   a           -> do a' <- gn a ; nestedLets [a'] (\[x] -> KNDeref (pointedToTypeOfVar x) x)
      E_AITyApp t a argtys  -> do a' <- gn a ; nestedLets [a'] (\[x] -> KNTyApp t x argtys)

      AILetVar id  a b  -> do a' <- gn a
                              b' <- gt b; return $ buildLet id a' b'
      AIUntil t a b rng -> do [a', b'] <- mapM gn [a, b] ; return $ (KNUntil t a' b' rng)

      AIStore      a b  -> do [a', b'] <- mapM gn [a, b] ; nestedLetsDo [a', b'] (\[x,y] -> knStore x y)
      AIArrayRead  t (ArrayIndex a b rng s) -> do
                              [a', b'] <- mapM gn [a, b]
                              nestedLets [a', b'] (\[x, y] -> KNArrayRead t (ArrayIndex x y rng s))
      AIArrayPoke _t (ArrayIndex a b rng s) c -> do
                              [a', b', c'] <- mapM gn [a,b,c]
                              nestedLets [a', b', c'] (\[x,y,z] -> KNArrayPoke (TupleTypeIL []) (ArrayIndex x y rng s) z)

      AILetFuns ids fns a   -> do knFns <- mapM kNormalizeFn fns
                                  a' <- gt a
                                  return $ KNLetFuns ids knFns a'

      AITuple    es rng     -> do ks <- mapM gn es
                                  nestedLets ks (\vs ->
                                    KNTuple (TupleTypeIL (map tidType vs)) vs rng)

      AICase t e bs         -> do e' <- gn e
                                  ibs <- forM bs (\(p, ae) -> do ke <- gt ae
                                                                 return (p, ke))
                                  nestedLets [e'] (\[v] -> KNCase t v ibs)

      AIIf      t  a b c    -> do a' <- gn a ; [ b', c'] <- mapM gt [b, c]
                                  nestedLets [a'] (\[v] -> KNIf t v b' c')
      AICall    t b es -> do
          cargs <- mapM gn es
          case b of
              E_AIPrim p -> do nestedLets   cargs (\vars -> KNCallPrim t p vars)
              E_AIVar v  -> do nestedLetsDo cargs (\vars -> knCall t v vars)
              _ -> do cb <- gn b
                      nestedLetsDo (cb:cargs) (\(vb:vars) -> knCall t vb vars)
  where knStore x y = do
            q <- varOrThunk (x, pointedToType $ tidType y)
            nestedLets [q] (\[z] -> KNStore (TupleTypeIL []) z y)

        knCall t a vs =
          case (tidType a) of
              FnTypeIL tys _ _ _ -> do
                  args <- mapM varOrThunk (zip vs tys)
                  nestedLets args (\xs -> KNCall mebTail t a xs)
              _ -> error $ "knCall: Called var had non-function type!\n\t" ++
                                show a ++
                                outToString (showStructure (tidType a))
-- }}}|||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

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
varOrThunk :: (AIVar, TypeIL) -> KN KNExpr
varOrThunk (a, targetType) = do
  case needsClosureWrapper a targetType of
    Just fnty -> do withThunkFor a fnty
    Nothing -> return (KNVar a)
  where
    -- TODO: I think this only works because we don't type-check IL.
    -- Specifically, we are assuming but not verifying that the involved
    -- types are all of pointer-size kinds.
    unForAll (ForAllIL _ t) = t
    unForAll             t  = t
    needsClosureWrapper a ty =
      case (tidType a, unForAll ty) of
        (                      FnTypeIL x y z FT_Proc,  FnTypeIL _ _ _ FT_Func) ->
            Just $             FnTypeIL x y z FT_Func
        (          ForAllIL t (FnTypeIL x y z FT_Proc), FnTypeIL _ _ _ FT_Func) ->
            Just $ ForAllIL t (FnTypeIL x y z FT_Func)
        _ -> Nothing

    withThunkFor :: AIVar -> TypeIL -> KN KNExpr
    withThunkFor v fnty = do
      fn <- mkThunkAround v fnty
      id <- knFresh ".kn.letfn"
      return $ KNLetFuns [id] [fn] $ KNVar (TypedId fnty id)

      where

        mkThunkAround v fnty = do
          id <- knFresh ".kn.thunk"
          vars <- argVarsWithTypes (fnTypeILDomain fnty)
          return $ Fn { fnVar      = TypedId fnty (GlobalSymbol (T.pack $ show id))
                      , fnVars     = vars
                      , fnBody     = KNCall YesTail (fnTypeILRange fnty) v vars
                      , fnIsRec    = Just False
                      , fnRange    = MissingSourceRange $ "thunk for " ++ show v
                      }
        -- TODO the above ident/global check doesn't work correctly for
        -- global polymorphic functions, which are first type-instantiated
        -- and then bound to a local variable before being closed over.
        -- The "right" thing to do is track known vs unknown vars...
        -- TODO i think this is fixed; double-check...

        argVarsWithTypes tys = do
          let tidOfType ty = do id <- knFresh ".arg"
                                return $ TypedId ty id
          mapM tidOfType tys

-- ||||||||||||||||||||||| Let-Flattening |||||||||||||||||||||||{{{
-- Because buildLet is applied bottom-to-top, we maintain the invariant
-- that the bound form in the result is never a binder itself.
buildLet :: Ident -> KNExpr -> KNExpr -> KNExpr
buildLet ident bound inexpr =
  case bound of
    -- Convert  let i = (let x = e in c) in inexpr
    -- ==>      let x = e in (let i = c in inexpr)
    KNLetVal x e c ->   KNLetVal x e (buildLet ident c inexpr)

    -- Convert  let f = letfuns g = ... in g in <<f>>
    --     to   letfuns g = ... in let f = g in <<f>>
    KNLetFuns ids fns a -> KNLetFuns ids fns (buildLet ident a inexpr)

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

          -- We also don't particularly want to do something like
          --    let var2 = (letfun var1 = {...} in var1) in e ...
          -- because it would be later flattened out to
          --    let var1 = fn in (let var2 = var1 in e...)
          (KNLetFuns ids fns (KNVar v)) -> do
            innerlet <- nestedLets' es (v:vars) k
            return $ KNLetFuns ids fns innerlet

          _otherwise -> do
            x        <- knFresh ".x"
            let v = TypedId (typeKN e) x
            innerlet <- nestedLets' es (v:vars) k
            return $ buildLet x e innerlet

-- Usually, we can get by with a pure continuation.
-- Note: Haskell's type system is insufficiently expressive here:
--       we can't express the constraint that len [KNExpr] == len [AIVar].
--       As a result, we get many spurious pattern match warnings.
nestedLets :: [KNExpr] -> ([AIVar] -> KNExpr) -> KN KNExpr
nestedLets exprs g = nestedLetsDo exprs (\vars -> return $ g vars)
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

-- Produces a list of (K-normalized) functions, eta-expansions of each ctor.
-- Specifically, given a data type T (A1::K1) ... (An::Kn) with
--   constructor C (T1::KT1) .. (Tn::KTn), we emit a procedure with type
--
-- forall (A1::K1) ... (An::Kn), T1 -> ... -> Tn -> T A1 ... An
--
-- For example, ``type case T2 of $T2C1 Int32``
-- produces a function ``T2C1 :: Int32 -> T2``,
-- while ``type case T3 (a:Boxed) of $T3C1 a``
-- produces T3C1 :: forall b:Boxed, b -> T3 b
--
kNormalCtors :: Context TypeIL -> DataType TypeIL -> [KN (Fn KNExpr TypeIL)]
kNormalCtors ctx dtype = map (kNormalCtor ctx dtype) (dataTypeCtors dtype)
  where
    kNormalCtor :: Context TypeIL -> DataType TypeIL -> DataCtor TypeIL
                -> KN (Fn KNExpr TypeIL)
    kNormalCtor ctx datatype (DataCtor cname small _tyformals tys) = do
      let dname = dataTypeName datatype
      let arity = Prelude.length tys
      let cid = CtorId dname (T.unpack cname) arity small
      let genFreshVarOfType t = do fresh <- knFresh ".autogen"
                                   return $ TypedId t fresh
      vars <- mapM genFreshVarOfType tys
      let (Just tid) = termVarLookup cname (contextBindings ctx)
      return $ Fn { fnVar   = tid
                  , fnVars  = vars
                  , fnBody  = KNAppCtor (TyConAppIL dname []) cid vars -- TODO fix
                  , fnIsRec = Just False
                  , fnRange = MissingSourceRange ("kNormalCtor " ++ show cid)
                  }

-- ||||||||||||||||||||||||| Boilerplate ||||||||||||||||||||||||{{{
-- This is necessary due to transformations of AIIf and nestedLets
-- introducing new bindings, which requires synthesizing a type.
typeKN :: KNExpr' ty -> ty
typeKN expr =
  case expr of
    KNBool          t _      -> t
    KNString        t _      -> t
    KNInt           t _      -> t
    KNFloat         t _      -> t
    KNTuple         t _  _   -> t
    KNKillProcess   t _      -> t
    KNCall        _ t _ _    -> t
    KNCallPrim      t _ _    -> t
    KNAppCtor       t _ _    -> t
    KNAllocArray    t _      -> t
    KNIf            t _ _ _  -> t
    KNUntil         t _ _ _  -> t
    KNAlloc         t _ _rgn -> t
    KNDeref         t _      -> t
    KNStore         t _ _    -> t
    KNArrayRead     t _      -> t
    KNArrayPoke     t _ _    -> t
    KNCase          t _ _    -> t
    KNLetVal        _ _ e    -> typeKN e
    KNLetFuns       _ _ e    -> typeKN e
    KNVar                  v -> tidType v
    KNTyApp overallType _tm _tyArgs -> overallType

-- This instance is primarily needed as a prereq for KNExpr to be an AExpr,
-- which ((childrenOf)) is needed in ILExpr for closedNamesOfKnFn.
instance Show ty => Structured (KNExpr' ty) where
    textOf e _width =
        case e of
            KNString     _ _    -> out $ "KNString    "
            KNBool       _ b    -> out $ "KNBool      " ++ (show b)
            KNCall tail t _ _   -> out $ "KNCall " ++ show tail ++ " :: " ++ show t
            KNCallPrim t prim _ -> out $ "KNCallPrim  " ++ (show prim) ++ " :: " ++ show t
            KNAppCtor  t cid  _ -> out $ "KNAppCtor   " ++ (show cid) ++ " :: " ++ show t
            KNLetVal   x b    _ -> out $ "KNLetVal    " ++ (show x) ++ " :: " ++ (show $ typeKN b) ++ " = ... in ... "
            KNLetFuns ids fns _ -> out $ "KNLetFuns   " ++ (show $ zip ids (map fnVar fns))
            KNIf      t  _ _ _  -> out $ "KNIf        " ++ " :: " ++ show t
            KNUntil   t  _ _ _  -> out $ "KNUntil     " ++ " :: " ++ show t
            KNInt ty int        -> out $ "KNInt       " ++ (litIntText int) ++ " :: " ++ show ty
            KNFloat ty flt      -> out $ "KNFloat     " ++ (litFloatText flt) ++ " :: " ++ show ty
            KNAlloc      {}     -> out $ "KNAlloc     "
            KNDeref      {}     -> out $ "KNDeref     "
            KNStore      {}     -> out $ "KNStore     "
            KNCase _t v bnds    -> out $ "KNCase      " ++ show v ++ " binding " ++ (show $ map fst bnds)
            KNAllocArray {}     -> out $ "KNAllocArray "
            KNArrayRead  t _    -> out $ "KNArrayRead " ++ " :: " ++ show t
            KNArrayPoke  {}     -> out $ "KNArrayPoke "
            KNTuple   _ vs _    -> out $ "KNTuple     (size " ++ (show $ length vs) ++ ")"
            KNVar (TypedId t (GlobalSymbol name))
                                -> out $ "KNVar(Global):   " ++ T.unpack name ++ " :: " ++ show t
            KNVar (TypedId t i) -> out $ "KNVar(Local):   " ++ show i ++ " :: " ++ show t
            KNTyApp t _e argty  -> out $ "KNTyApp     " ++ show argty ++ "] :: " ++ show t
            KNKillProcess t m   -> out $ "KNKillProcess " ++ show m ++ " :: " ++ show t
    childrenOf expr =
        let var v = KNVar v in
        case expr of
            KNString {}             -> []
            KNBool   {}             -> []
            KNInt    {}             -> []
            KNFloat  {}             -> []
            KNKillProcess {}        -> []
            KNUntil _t a b _        -> [a, b]
            KNTuple   _ vs _        -> map var vs
            KNCase _ e bs           -> (var e):(map snd bs)
            KNLetFuns _ids fns e    -> map fnBody fns ++ [e]
            KNLetVal _x b e         -> [b, e]
            KNCall  _  _t  v vs     -> [var v] ++ [var v | v <- vs]
            KNCallPrim _t _v vs     ->            [var v | v <- vs]
            KNAppCtor  _t _c vs     ->            [var v | v <- vs]
            KNIf       _t v b c     -> [var v, b, c]
            KNAlloc _ v _rgn        -> [var v]
            KNAllocArray _ v        -> [var v]
            KNDeref      _ v        -> [var v]
            KNStore      _ v w      -> [var v, var w]
            KNArrayRead _t ari      -> map var $ childrenOfArrayIndex ari
            KNArrayPoke _t ari i    -> map var $ childrenOfArrayIndex ari ++ [i]
            KNVar _                 -> []
            KNTyApp _t v _argty     -> [var v]
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

renderKN m put = if put then putDoc (pretty m) >>= (return . Left)
                        else return . Right $ show (pretty m)

renderKNM :: (ModuleIL (KNExpr' MonoType) MonoType) -> String
renderKNM m = show (pretty m)

renderKNF :: (Fn (KNExpr' TypeIL) TypeIL) -> String
renderKNF m = show (pretty m)

renderKNFM :: (Fn (KNExpr' MonoType) MonoType) -> String
renderKNFM m = show (pretty m)

showTyped :: Pretty t => Doc -> t -> Doc
showTyped d t = parens (d <+> text "::" <+> pretty t)

showUnTyped d _ = d

comment d = text "/*" <+> d <+> text "*/"

instance Pretty TypeIL where
  pretty t = text (show t)

instance Pretty MonoType where
  pretty t = text (show t)

instance Pretty t => Pretty (TypedId t) where
  pretty (TypedId t i) = showUnTyped (text $ show i) t

instance Pretty AllocMemRegion where
  pretty rgn = text (show rgn)

instance Pretty t => Pretty (ArrayIndex (TypedId t)) where
  pretty (ArrayIndex b i _rng safety) =
    prettyId b <> brackets (prettyId i) <+> comment (text $ show safety)

instance Pretty t => Pretty (FosterPrim t) where
  pretty (NamedPrim tid) = prettyId tid
  pretty (PrimOp nm _ty) = text nm
  pretty (PrimIntTrunc frm to) = text ("trunc from " ++ show frm ++ " to " ++ show to)
  pretty (CoroPrim c t1 t2) = text "...coroprim..."

-- (<//>) ?vs? align (x <$> y)

kwd  s = dullblue  (text s)
lkwd s = dullwhite (text s)
end    = lkwd "end"

instance Pretty t => Pretty (Fn (KNExpr' t) t) where
  pretty fn = group (lbrace <+> (hsep (map (\v -> pretty v <+> text "=>") (fnVars fn)))
                    <$> indent 4 (pretty (fnBody fn))
                    <$> rbrace) <+> pretty (fnVar fn)

instance (Pretty body, Pretty t) => Pretty (ModuleIL body t) where
  pretty m = text "// begin decls"
            <$> vcat [showTyped (text s) t | (s, t) <- moduleILdecls m]
            <$> text "// end decls"
            <$> text "// begin datatypes"
            <$> empty
            <$> text "// end datatypes"
            <$> text "// begin prim types"
            <$> empty
            <$> text "// end prim types"
            <$> text "// begin functions"
            <$> pretty (moduleILbody m)
            <$> text "// end functions"

prettyId (TypedId _ i) = text (show i)

instance Pretty t => Pretty (Pattern t) where
  pretty p =
    case p of
        P_Wildcard      _rng _ty          -> text "_"
        P_Variable      _rng tid          -> prettyId tid
        P_Ctor          _rng _ty pats cid -> parens (text "$" <> text (ctorCtorName $ ctorInfoId cid) <> (hsep $ map pretty pats))
        P_Bool          _rng _ty b        -> text $ if b then "True" else "False"
        P_Int           _rng _ty li       -> text (litIntText li)
        P_Tuple         _rng _ty pats     -> parens (hsep $ punctuate comma (map pretty pats))

instance Pretty ty => Pretty (KNExpr' ty) where
  pretty e =
        case e of
            KNVar (TypedId _ (GlobalSymbol name))
                                -> (text $ "G:" ++ T.unpack name)
                       --showTyped (text $ "G:" ++ T.unpack name) t
            KNVar (TypedId t i) -> prettyId (TypedId t i)
            KNTyApp t e argtys  -> showTyped (pretty e <> text ":[" <> hsep (punctuate comma (map pretty argtys)) <> text "]") t
            KNKillProcess t m   -> text ("KNKillProcess " ++ show m ++ " :: ") <> pretty t
            KNString     _ s    -> dquotes (text $ T.unpack s)
            KNBool       _ b    -> text $ show b
            KNCall _tail t v [] -> showUnTyped (prettyId v <+> text "!") t
            KNCall _tail t v vs -> showUnTyped (prettyId v <> hsep (map pretty vs)) t
            KNCallPrim t prim vs-> showUnTyped (text "prim" <+> pretty prim <+> hsep (map prettyId vs)) t
            KNAppCtor  t cid vs -> showUnTyped (text "~" <> parens (text (show cid) <> hsep (map prettyId vs))) t
            KNLetVal   x b    k -> lkwd "let"
                                      <+> fill 8 (text (show x))
                                      <+> text "="
                                      <+> pretty b <+> lkwd "in"
                                   <$> pretty k
            KNLetFuns ids fns k -> text "letfuns"
                                   <$> indent 2 (vcat [text (show id) <+> text "="
                                                                      <+> pretty fn
                                                      | (id, fn) <- zip ids fns
                                                      ])
                                   <$> lkwd "in"
                                   <$> pretty k
                                   <$> end
            KNIf     _t v b1 b2 -> kwd "if" <+> prettyId v
                                   <$> nest 2 (kwd "then" <+> pretty b1)
                                   <$> nest 2 (kwd "else" <+> pretty b2)
                                   <$> end
            KNUntil  _t c b _sr -> kwd "until" <+> pretty c <//> lkwd "then"
                                   <$> nest 2 (pretty b)
                                   <$> end
            KNInt   _ty int     -> red $ text (litIntText int)
            KNFloat _ty flt     -> dullred $ text (litFloatText flt)
            KNAlloc _ v rgn     -> text "(ref" <+> prettyId v <+> comment (pretty rgn) <> text ")"
            KNDeref _ v         -> prettyId v <> text "^"
            KNStore _ v1 v2     -> text "store" <+> prettyId v1 <+> text "to" <+> prettyId v2
            KNCase _t v bnds    -> align $
                                       kwd "case" <+> pretty v
                                       <$> indent 2 (vcat [ kwd "of" <+> fill 20 (pretty pat) <+> text "->" <+> pretty expr
                                                          | ((pat, _tys), expr) <- bnds
                                                          ])
                                       <$> end
            KNAllocArray {}     -> text $ "KNAllocArray "
            KNArrayRead  _ ai   -> pretty ai
            KNArrayPoke  _ ai v -> prettyId v <+> text ">^" <+> pretty ai
            KNTuple      _ vs _ -> parens (hsep $ punctuate comma (map pretty vs))

deriving instance (Show ty) => Show (KNExpr' ty)
