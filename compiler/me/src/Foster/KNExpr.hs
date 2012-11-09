{-# LANGUAGE StandaloneDeriving #-}
-----------------------------------------------------------------------------
-- Copyright (c) 2011 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.KNExpr (kNormalizeModule, KNExpr, KNExpr'(..), TailQ(..), typeKN,
                      knSinkBlocks,
                      renderKN, renderKNM, renderKNF, renderKNFM) where
import Control.Monad(liftM, liftM2)
import qualified Data.Text as T
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Set(Set)
import Data.Map(Map)
import Data.List(foldl')
import Data.Maybe(maybeToList)

import Foster.MonoType
import Foster.Base
import Foster.Config
import Foster.Context
import Foster.TypeIL
import Foster.AnnExprIL

import Text.PrettyPrint.ANSI.Leijen

import qualified Data.Graph.Inductive.Graph            as Graph
import qualified Data.Graph.Inductive.PatriciaTree     as Graph
import qualified Data.Graph.Inductive.Query.Dominators as Graph

-- | Foster.KNExpr binds all intermediate values to named variables
-- | via a variant of K-normalization.  We also perform local block sinking,
-- | in preparation for later contification.

data KNExpr' ty =
        -- Literals
          KNLiteral     ty Literal
        | KNTuple       ty [TypedId ty] SourceRange
        | KNKillProcess ty T.Text
        -- Control flow
        | KNIf          ty (TypedId ty)  (KNExpr' ty) (KNExpr' ty)
        | KNUntil       ty (KNExpr' ty)  (KNExpr' ty) SourceRange
        -- Creation of bindings
        | KNCase        ty (TypedId ty) [PatternBinding (KNExpr' ty) ty]
        | KNLetVal      Ident      (KNExpr' ty)     (KNExpr' ty)
        | KNLetRec     [Ident]     [KNExpr' ty]     (KNExpr' ty)
        | KNLetFuns    [Ident] [Fn (KNExpr' ty) ty] (KNExpr' ty)
        -- Use of bindings
        | KNVar         (TypedId ty)
        | KNCallPrim    ty (FosterPrim ty) [TypedId ty]
        | KNCall TailQ  ty (TypedId ty)    [TypedId ty]
        | KNAppCtor     ty CtorId          [TypedId ty]
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

type KNExpr = KNExpr' TypeIL

type KN = Compiled

knFresh :: String -> KN Ident
knFresh s = ccFreshId (T.pack s)

--------------------------------------------------------------------

kNormalizeModule :: (ModuleIL AIExpr TypeIL) -> Context TypeIL ->
           Compiled (ModuleIL KNExpr TypeIL)
kNormalizeModule m ctx =
    -- TODO move ctor wrapping earlier?
    let knCtorFuncs = concatMap (kNormalCtors ctx) (moduleILprimTypes m ++
                                                    moduleILdataTypes m) in
    let knWrappedBody = do { ctors <- sequence knCtorFuncs
                           ; body  <- kNormalize YesTail (moduleILbody m)
                           ; return $ wrapFns ctors body
                           } in
    do body' <- knWrappedBody
       return m { moduleILbody = body' }
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
      AILiteral ty lit  -> return $ KNLiteral ty lit
      E_AIVar v         -> return $ KNVar v
      AIKillProcess t m -> return $ KNKillProcess t m
      E_AIPrim p -> error $ "KNExpr.kNormalize: Should have detected prim " ++ show p

      AIAllocArray t a      -> do nestedLets [gn a] (\[x] -> KNAllocArray (ArrayTypeIL t) x)
      AIAlloc a rgn         -> do nestedLets [gn a] (\[x] -> KNAlloc (PtrTypeIL $ tidType x) x rgn)
      AIDeref   a           -> do nestedLets [gn a] (\[x] -> KNDeref (pointedToTypeOfVar x) x)
      E_AITyApp t a argtys  -> do nestedLets [gn a] (\[x] -> KNTyApp t x argtys)

      AIStore      a b  -> do nestedLetsDo [gn a, gn b] (\[x,y] -> knStore x y)
      AIArrayRead  t (ArrayIndex a b rng s) ->
              nestedLets (map gn [a, b])
                               (\[x, y] -> KNArrayRead t (ArrayIndex x y rng s))
      AIArrayPoke _t (ArrayIndex a b rng s) c -> do
              nestedLets (map gn [a,b,c])
                               (\[x,y,z] -> KNArrayPoke (TupleTypeIL []) (ArrayIndex x y rng s) z)

      AILetFuns ids fns a   -> do knFns <- mapM kNormalizeFn fns
                                  liftM (KNLetFuns ids knFns) (gt a)

      AITuple   es rng      -> do nestedLets (map gn es) (\vs ->
                                    KNTuple (TupleTypeIL (map tidType vs)) vs rng)

      AILetVar id a b       -> do liftM2 (buildLet id) (gn a) (gt b)
      AILetRec ids exprs e  -> do -- Unlike with LetVal, we can't float out the
                                  -- inner bindings, because they're presuambly
                                  -- defined in terms of the ids being bound.
                                  exprs' <- mapM gn exprs
                                  e'     <- gt e
                                  return $ KNLetRec ids exprs' e'
      AIUntil   t a b rng   -> do liftM2 (\a' b' -> KNUntil t a' b' rng) (gn a) (gn b)
      AICase    t e bs      -> do e' <- gn e
                                  ibs <- mapM gtp bs
                                  nestedLets [return e'] (\[v] -> KNCase t v ibs)
                                    where gtp (p, ae) = liftM (\ae' -> (p, ae')) (gt ae)

      AIIf      t  a b c    -> do a' <- gn a
                                  [ b', c' ] <- mapM gt [b, c]
                                  nestedLets [return a'] (\[v] -> KNIf t v b' c')
      AIAppCtor t c es -> do nestedLets (map gn es) (\vars -> KNAppCtor t c vars)
      AICall    t b es -> do
          let cargs = map gn es
          case b of
              E_AIPrim p -> do nestedLets   cargs (\vars -> KNCallPrim t p vars)
              E_AIVar v  -> do nestedLetsDo cargs (\vars -> knCall t v vars)
              _ -> do nestedLetsDo (gn b:cargs) (\(vb:vars) -> knCall t vb vars)

  where knStore x y = do
            let q = varOrThunk (x, pointedToType $ tidType y)
            nestedLets [q] (\[z] -> KNStore (TupleTypeIL []) z y)

        knCall t a vs =
          case (tidType a) of
              FnTypeIL tys _ _ _ -> do
                  let args = map varOrThunk (zip vs tys)
                  nestedLets args (\xs -> KNCall mebTail t a xs)
              _ -> error $ "knCall: Called var had non-function type!\n\t" ++
                                show a ++
                                show (showStructure (tidType a))
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
                      , fnAnnot    = ExprAnnot [] (MissingSourceRange $ "thunk for " ++ show v) []
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
nestedLetsDo :: [KN KNExpr] -> ([AIVar] -> KN KNExpr) -> KN KNExpr
nestedLetsDo exprActions g = do exprs <- sequence exprActions
                                nestedLets' exprs [] g
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
nestedLets :: [KN KNExpr] -> ([AIVar] -> KNExpr) -> KN KNExpr
nestedLets exprActions g = nestedLetsDo exprActions (\vars -> return $ g vars)
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
    kNormalCtor ctx datatype dc@(DataCtor cname small _tyformals tys) = do
      let dname = dataTypeName datatype
      let arity = Prelude.length tys
      let cid   = CtorId dname (T.unpack cname) arity small
      let info  = CtorInfo cid dc
      let genFreshVarOfType t = do fresh <- knFresh ".autogen"
                                   return $ TypedId t fresh
      vars <- mapM genFreshVarOfType tys
      case termVarLookup cname (contextBindings ctx) of
        Nothing -> error $ "Unable to find binder for constructor " ++ show cname
        Just (tid, _) -> return $
               Fn { fnVar   = tid
                  , fnVars  = vars
                  , fnBody  = KNAppCtor (TyConAppIL dname []) cid vars -- TODO fix
                  , fnIsRec = Just False
                  , fnAnnot = ExprAnnot [] (MissingSourceRange $ "kNormalCtor " ++ show cid) []
                  }

-- |||||||||||||||||||||||||| Local Block Sinking |||||||||||||||{{{

-- The block-sinking transformation here is loosely based on the
-- presentation in the paper
--
--      Lambda-Dropping: Transforming Recursive Equations into
--      Programs with Block Structure
--
-- by Olivier Danvy and Ulrik P. Schultz.
--
-- http://www.brics.dk/RS/99/27/BRICS-RS-99-27.pdf

collectFunctions :: Fn (KNExpr' t) t -> [(Ident, Ident, Fn (KNExpr' t) t)]  -- (parent, binding, child)
collectFunctions knf = go [] (fnBody knf)
  where go xs e = case e of
          KNLiteral       {} -> xs
          KNTuple         {} -> xs
          KNKillProcess   {} -> xs
          KNVar           {} -> xs
          KNCallPrim      {} -> xs
          KNCall          {} -> xs
          KNAppCtor       {} -> xs
          KNAlloc         {} -> xs
          KNDeref         {} -> xs
          KNStore         {} -> xs
          KNAllocArray    {} -> xs
          KNArrayRead     {} -> xs
          KNArrayPoke     {} -> xs
          KNTyApp         {} -> xs
          KNIf            _ _ e1 e2   -> go (go xs e1) e2
          KNLetVal          _ e1 e2   -> go (go xs e1) e2
          KNUntil           _ e1 e2 _ -> go (go xs e1) e2
          KNCase       _ _ patbinds -> let es = map snd patbinds in
                                       foldl' go xs es
          KNLetRec     _ es b       -> foldl' go xs (b:es)
          KNLetFuns    ids fns b ->
                 let entries = map (\(id, f) -> (fnIdent knf, id, f)) (zip ids fns) in
                 let ys      = concatMap collectFunctions fns in
                 xs ++ entries ++ go ys b

collectMentions :: Fn (KNExpr' t) t -> Set (Ident, Ident) -- (caller, callee)
collectMentions knf = go Set.empty (fnBody knf)
  where cc       = fnIdent knf
        uu xs vs = Set.union xs (Set.fromList [(cc, tidIdent v) | v <- vs])
        vv xs v  = Set.insert (cc, tidIdent v) xs
        go xs e = case e of
          KNLiteral     {} -> xs
          KNKillProcess {} -> xs
          KNAllocArray  {} -> xs -- next few cases can't be fn-valued due to type checking.
          KNArrayRead   {} -> xs
          KNArrayPoke   {} -> xs
          KNDeref       {} -> xs
          KNTuple       _ vs _ -> uu xs vs
          KNAppCtor     _ _ vs -> uu xs vs
          KNCallPrim    _ _ vs -> uu xs vs
          KNVar           v    -> vv xs v
          KNAlloc       _ v _  -> vv xs v
          KNTyApp       _ v _  -> vv xs v
          KNStore     _  v1 v2 -> vv (vv xs v1) v2
          KNCall      _ _ v vs -> vv (uu xs vs) v
          KNIf          _ v e1 e2   -> go (go (vv xs v) e1) e2
          KNUntil       _   e1 e2 _ -> go (go xs e1) e2
          KNLetVal      _   e1 e2   -> go (go xs e1) e2
          KNCase        _ v patbinds -> let es = map snd patbinds in
                                       foldl' go (vv xs v) es
          KNLetRec     _ es b ->        foldl' go xs (b:es)
          KNLetFuns    _ fns b -> Set.union xs $ go (Set.unions $ map collectMentions fns) b

rebuildFnWith rebuilder addBindingsFor f =
         let rebuiltBody = rebuildWith rebuilder (fnBody f) in
         f { fnBody = addBindingsFor f rebuiltBody }

rebuildWith rebuilder e = q e
  where
    q x = case x of
      KNVar         {} -> x
      KNLiteral     {} -> x
      KNTuple       {} -> x
      KNKillProcess {} -> x
      KNCallPrim    {} -> x
      KNCall        {} -> x
      KNAppCtor     {} -> x
      KNAlloc       {} -> x
      KNDeref       {} -> x
      KNStore       {} -> x
      KNAllocArray  {} -> x
      KNArrayRead   {} -> x
      KNArrayPoke   {} -> x
      KNTyApp       {} -> x
      KNIf          ty v ethen eelse -> KNIf       ty v (q ethen) (q eelse)
      KNUntil       ty cond body rng -> KNUntil    ty   (q cond)  (q body) rng
      KNLetVal      id  e1   e2      -> KNLetVal   id   (q e1)    (q e2)
      KNLetRec      ids es   e       -> KNLetRec   ids (map q es) (q e)
      KNCase        ty v patbinds    -> KNCase     ty v (map (\(p,e) -> (p, q e)) patbinds)
      KNLetFuns     ids fns e        -> mkLetFuns (rebuilder (zip ids fns)) (q e)

mkLetFuns []       e = e
mkLetFuns bindings e = let (ids, fns) = unzip bindings in
                       KNLetFuns ids fns e

knSinkBlocks :: ModuleIL (KNExpr' t) t -> KN (ModuleIL (KNExpr' t) t)
knSinkBlocks m = do
  let rebuilder idsfns = [(id, localBlockSinking fn) | (id, fn) <- idsfns]
  return $ m { moduleILbody = rebuildWith rebuilder (moduleILbody m) }

-- We perform (function-)local block sinking after monomorphization.
-- Block sinking is needed for contification to work properly.
-- Performing sinking after monomorphization allows each monomorphization
-- of a given function to be separately sunk.
localBlockSinking :: Fn (KNExpr' t) t -> Fn (KNExpr' t) t
localBlockSinking knf = rebuildFn knf
 where
  rebuildFn   = rebuildFnWith rebuilder addBindingsFor
  functions   = collectFunctions knf
  allMentions = collectMentions knf
  (parents, bindings, child_functions) = unzip3 functions

  children = map fnIdent child_functions

  bindingToChildMap = Map.fromList (zip bindings children)
  functionsSet      = Set.fromList $ fnIdent knf : parents ++ children

  (block2node, node2block) = buildIsomorphism functionsSet
    where buildIsomorphism elemset =
                let elems = Set.toList elemset in
                (Map.fromList $ zip elems [0..]
                ,Map.fromList $ zip [0..] elems )
  --  (block2node, node2block) :: (Map Ident Node, Map Node Ident)

  b2n e = case Map.lookup e block2node of
                 Just r -> r
                 Nothing -> error $ "block2node failed for " ++ show e
  n2b e = case Map.lookup e node2block of
                 Just r -> r
                 Nothing -> error $ "node2block failed for " ++ show e

  root = b2n (fnIdent knf)

  -- Build the call graph based on call site info.
  callGraph :: Graph.UGr
  callGraph = Graph.mkGraph lnodes ledges
    where
      mentions = [(parent, child) | (parent, binding) <- Set.toList allMentions
                 , child <- maybeToList $ Map.lookup binding bindingToChildMap]

      mentionsL = [(b2n caller, b2n callee) | (caller, callee) <- mentions]

      lnodes = let (callers, callees) = unzip mentionsL in
               let nodes = Set.toList $ Set.fromList $ callers ++ callees in
                   (root, ()) : [(n, ()) | n <- nodes]

      ledges = [(caller, callee, ()) | (caller, callee) <- mentionsL]

  -- If a function is dominated by a node which is not its parent, relocate it.
  -- relocationTargetsList :: [(Fn (KNExpr' t) t, Ident)]
  relocationTargetsList = [((id, f), dom)
                          | f_id <- Set.toList functionsSet
                          ,parent <- maybeToList $ Map.lookup f_id parentMap
                          ,dom    <- maybeToList $ Map.lookup f_id doms
                          ,(id,f) <- maybeToList $ Map.lookup f_id fnForChildId
                          , dom /= parent]
     where
          parentMap = Map.fromList (zip children parents)

          fnForChildId = Map.fromList [(fnIdent f, (id, f))
                                      | (id, f) <- zip bindings child_functions]

          -- Compute dominators of each function.
          doms :: Map Ident (Ident {-dom-})
          doms = Map.fromList [(n2b node, n2b ndom)
                              | (node, ndom) <- Graph.iDom callGraph root]

  -- Remove bindings which are being relocated.
  rebuilder idsfns =
      [(id, fn)
      |(id, fn) <- map (\(id, fn) -> (id, rebuildFn fn)) idsfns,
       Set.notMember (fnIdent fn) shouldBeRelocated]
    where
        shouldBeRelocated = Set.fromList $ map (\((_id, fn), _) -> fnIdent fn)
                                               relocationTargetsList

  addBindingsFor f body = mkLetFuns newfns body
        where
          newfns = Map.findWithDefault [] (fnIdent f) newBindingsForFn
          newBindingsForFn  = Map.unionsWith (++)
                              [Map.singleton dom [(id, f)]
                              | ((id, f), dom) <- relocationTargetsList]
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||


-- ||||||||||||||||||||||||| Boilerplate ||||||||||||||||||||||||{{{
-- This is necessary due to transformations of AIIf and nestedLets
-- introducing new bindings, which requires synthesizing a type.
typeKN :: KNExpr' ty -> ty
typeKN expr =
  case expr of
    KNLiteral       t _      -> t
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
    KNLetRec        _ _ e    -> typeKN e
    KNLetFuns       _ _ e    -> typeKN e
    KNVar                  v -> tidType v
    KNTyApp overallType _tm _tyArgs -> overallType

-- This instance is primarily needed as a prereq for KNExpr to be an AExpr,
-- which ((childrenOf)) is needed in ILExpr for closedNamesOfKnFn.
instance Show ty => Structured (KNExpr' ty) where
    textOf e _width =
        case e of
            KNLiteral _  (LitText  _) -> text $ "KNString    "
            KNLiteral _  (LitBool  b) -> text $ "KNBool      " ++ (show b)
            KNLiteral ty (LitInt int) -> text $ "KNInt       " ++ (litIntText int) ++ " :: " ++ show ty
            KNLiteral ty (LitFloat f) -> text $ "KNFloat     " ++ (litFloatText f) ++ " :: " ++ show ty
            KNCall tail t _ _   -> text $ "KNCall " ++ show tail ++ " :: " ++ show t
            KNCallPrim t prim _ -> text $ "KNCallPrim  " ++ (show prim) ++ " :: " ++ show t
            KNAppCtor  t cid  _ -> text $ "KNAppCtor   " ++ (show cid) ++ " :: " ++ show t
            KNLetVal   x b    _ -> text $ "KNLetVal    " ++ (show x) ++ " :: " ++ (show $ typeKN b) ++ " = ... in ... "
            KNLetRec   _ _    _ -> text $ "KNLetRec    "
            KNLetFuns ids fns _ -> text $ "KNLetFuns   " ++ (show $ zip ids (map fnVar fns))
            KNIf      t  _ _ _  -> text $ "KNIf        " ++ " :: " ++ show t
            KNUntil   t  _ _ _  -> text $ "KNUntil     " ++ " :: " ++ show t
            KNAlloc      {}     -> text $ "KNAlloc     "
            KNDeref      {}     -> text $ "KNDeref     "
            KNStore      {}     -> text $ "KNStore     "
            KNCase _t v bnds    -> text $ "KNCase      " ++ show v ++ " binding " ++ (show $ map fst bnds)
            KNAllocArray {}     -> text $ "KNAllocArray "
            KNArrayRead  t _    -> text $ "KNArrayRead " ++ " :: " ++ show t
            KNArrayPoke  {}     -> text $ "KNArrayPoke "
            KNTuple   _ vs _    -> text $ "KNTuple     (size " ++ (show $ length vs) ++ ")"
            KNVar (TypedId t (GlobalSymbol name))
                                -> text $ "KNVar(Global):   " ++ T.unpack name ++ " :: " ++ show t
            KNVar (TypedId t i) -> text $ "KNVar(Local):   " ++ show i ++ " :: " ++ show t
            KNTyApp t _e argty  -> text $ "KNTyApp     " ++ show argty ++ "] :: " ++ show t
            KNKillProcess t m   -> text $ "KNKillProcess " ++ show m ++ " :: " ++ show t
    childrenOf expr =
        let var v = KNVar v in
        case expr of
            KNLiteral {}            -> []
            KNKillProcess {}        -> []
            KNUntil _t a b _        -> [a, b]
            KNTuple   _ vs _        -> map var vs
            KNCase _ e bs           -> (var e):(map snd bs)
            KNLetFuns _ids fns e    -> map fnBody fns ++ [e]
            KNLetVal _x b  e        -> [b, e]
            KNLetRec _x bs e        -> bs ++ [e]
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

-- ||||||||||||||||||||||||| Pretty-printing ||||||||||||||||||||{{{
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
  pretty t = case t of
          PrimInt        isb          -> text "Int" <> pretty isb
          PrimFloat64                 -> text "Float64"
          TyConApp       dt ts        -> text "(" <> pretty dt <+> tupled (map pretty ts) <> text "]"
          TupleType      ts           -> tupled (map pretty ts)
          StructType     ts           -> text "#" <> tupled (map pretty ts)
          FnType         ts r cc pf   -> text "{" <+> hsep [pretty t <+> text "=>" | t <- ts]
                                                  <+> pretty r <+> text "}"
          CoroType       s  r         -> text "Coro..."
          ArrayType      t            -> text "Array" <+> pretty t
          PtrType        t            -> text "Ref" <+> pretty t
          PtrTypeUnknown              -> text "?"

instance Pretty AllocMemRegion where
  pretty rgn = text (show rgn)

instance Pretty t => Pretty (ArrayIndex (TypedId t)) where
  pretty (ArrayIndex b i _rng safety) =
    prettyId b <> brackets (prettyId i) <+> comment (text $ show safety)

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
        P_Ctor          _rng _ty pats cid -> parens (text "$" <> text (ctorCtorName $ ctorInfoId cid) <+> (hsep $ map pretty pats))
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
            KNLiteral _ lit     -> pretty lit
            KNCall _tail t v [] -> showUnTyped (prettyId v <+> text "!") t
            KNCall _tail t v vs -> showUnTyped (prettyId v <> hsep (map pretty vs)) t
            KNCallPrim t prim vs-> showUnTyped (text "prim" <+> pretty prim <+> hsep (map prettyId vs)) t
            KNAppCtor  t cid  vs-> showUnTyped (text "~" <> parens (text (show cid)) <> hsep (map prettyId vs)) t
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
            KNLetRec  ids xps e -> text "rec"
                                   <$> indent 2 (vcat [text (show id) <+> text "="
                                                                      <+> pretty xpr
                                                      | (id, xpr) <- zip ids xps
                                                      ])
                                   <$> lkwd "in"
                                   <$> pretty e
                                   <$> end
            KNIf     _t v b1 b2 -> kwd "if" <+> prettyId v
                                   <$> nest 2 (kwd "then" <+> pretty b1)
                                   <$> nest 2 (kwd "else" <+> pretty b2)
                                   <$> end
            KNUntil  _t c b _sr -> kwd "until" <+> pretty c <//> lkwd "then"
                                   <$> nest 2 (pretty b)
                                   <$> end
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

deriving instance (Show ty) => Show (KNExpr' ty) -- used elsewhere...

-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

