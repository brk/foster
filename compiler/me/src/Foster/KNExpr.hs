{-# LANGUAGE StandaloneDeriving #-}
-----------------------------------------------------------------------------
-- Copyright (c) 2011 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.KNExpr (kNormalizeModule, KNExpr, KNExpr'(..), TailQ(..), typeKN,
                      knLoopHeaders, knSinkBlocks, knInline, knSize,
                      renderKN, renderKNM, renderKNF, renderKNFM) where
import qualified Data.Text as T
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Set(Set)
import Data.Map(Map)
import Data.List(foldl' , isPrefixOf)
import Data.Maybe(maybeToList, catMaybes)

import Foster.MonoType
import Foster.Base
import Foster.Config
import Foster.Context
import Foster.TypeIL
import Foster.AnnExprIL

import Debug.Trace(trace)

import Text.PrettyPrint.ANSI.Leijen

import qualified Data.Graph.Inductive.Graph            as Graph
import qualified Data.Graph.Inductive.PatriciaTree     as Graph
import qualified Data.Graph.Inductive.Query.Dominators as Graph

import Control.Monad.State(gets, liftIO, evalStateT, execStateT, StateT, liftM, liftM2, get, put, lift)
import Data.IORef(IORef, newIORef, readIORef, writeIORef, modifyIORef)

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
buildLet :: Ident -> KNExpr' t -> KNExpr' t -> KNExpr' t
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
    kNormalCtor ctx datatype _dc@(DataCtor cname small _tyformals tys) = do
      let dname = dataTypeName datatype
      let arity = Prelude.length tys
      let cid   = CtorId dname (T.unpack cname) arity small
      -- let info  = CtorInfo cid dc
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

mkLetVals []            e = e
mkLetVals ((id,b):rest) e = KNLetVal id b (mkLetVals rest e)

knSinkBlocks :: ModuleIL (KNExpr' t) t -> KN (ModuleIL (KNExpr' t) t)
knSinkBlocks m = do
  let rebuilder idsfns = [(id, localBlockSinking fn) | (id, fn) <- idsfns]
  return $ m { moduleILbody = rebuildWith rebuilder (moduleILbody m) }

-- We perform (function-)local block sinking after monomorphization.
-- Block sinking is needed for contification to work properly;
-- without it, a contifiable function would get contified into an outer scope,
-- which doesn't work (since functions eventually get lifted to toplevel).
--
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

-- ||||||||||||||||||||||||| Loop Headers |||||||||||||||||||||||{{{

-- Insert loop headers for recursive functions in the program.
--
-- For each recursive function, we'll look at all the (recursive)
-- tail calls it makes, and which arguments each call passes.
--
-- If there's a subset of arguments which are passed at every recursive
-- call, these arguments will be factored out of the loop header
-- and each recursive call.
--
-- Since the loop header is only called from tail position, it will
-- be contifiable by definition. (This is why we ignore non-tail recursive
-- calls -- because inserting a non-contifiable function wrapper would
-- change the allocation behavior of programs.)
--
-- Adding loop headers has two benefits:
--   1) Passing fewer arguments as loop arguments avoids unnecessary copies.
--   2) When inlining is applied, inlining a function wrapping a loop header
--      corresponds to specializing the recursive function to its arguments,
--      rather than merely unrolling the loop once.
--
-- See Andrew Appel's 1994 paper "Loop Headers in lambda-calculus or CPS"
-- for more examples: http://www.cs.princeton.edu/~appel/papers/460.pdf

type Hdr = StateT HdrState KN
data HdrState =   HdrState {
    headers :: LoopHeaders
  , census  :: LoopCensus
  , varmap  :: Map Ident Ident -- for tracking bitcasts...
}

-- Map each function's (outer) bound identifier to a fresh id,
-- fresh variables, and a flag indicating whether any tail calls to
-- the function were detected, since we only care about arguments
-- passed to tail calls.
type LoopHeaders = Map Ident ((Ident, [TypedId MonoType]), Bool)

-- Map each recursive fn identifier to the list of variables it is always
-- passed. This list starts as [Just x] for each formal x; if a recursive call
-- ever passes a different variable, we'll switch to Nothing for that entry.
type LoopCensus  = Map Ident [Maybe (TypedId MonoType)]

mergeInfo :: [TypedId MonoType] -> [Maybe (TypedId MonoType)] -> [Maybe (TypedId MonoType)]
mergeInfo ys xs = -- implicit: lists are the same length...
    let r = map resolve (zip xs ys) in
    trace ("mergeInfo\n\t" ++ show (map (fmap tidIdent) xs) ++ "\n\t" ++ show (map tidIdent ys) ++ "\n\n==>\t" ++ show (map (fmap tidIdent) r)) r
  where resolve (Nothing, _) = Nothing
        resolve (Just x,  y) = if x == y then Just x else Nothing

-- At each call site, we want to pass only the args which were not useless;
-- i.e. the ones for which the corresponding info was unknown (Nothing).
dropUselessArgs :: [Maybe (TypedId MonoType)] -> [TypedId MonoType] -> [TypedId MonoType]
dropUselessArgs xs ys = resolve (zip xs ys)
  where resolve [] = []
        resolve ((Just  _, _):xs) =    resolve xs
        resolve ((Nothing, x):xs) = x:(resolve xs)

-- The loop header should rename variables which are getting new bindings
-- in the loop, but keep unchanged the variables that are loop-invariant.
renameUsefulArgs :: [Maybe (TypedId MonoType)] -> [TypedId MonoType] -> [TypedId MonoType]
renameUsefulArgs xs ys = resolve (zip xs ys)
  where resolve [] = []
        resolve ((Just  y, _):xs) = y:(resolve xs)
        resolve ((Nothing, x):xs) = x:(resolve xs)

{-
getUselessArgs :: [Maybe (TypedId MonoType)] -> [TypedId MonoType]
getUselessArgs = catMaybes
-}

-- Map each recursive fn identifier to the var/s for its loop header, and a
-- list reflecting which of the original formals were recursively useless.
type LoopInfo = Map Ident ((Ident, [TypedId MonoType]), [Maybe (TypedId MonoType)])

isAllNothing [] = True
isAllNothing (Nothing:xs) = isAllNothing xs
isAllNothing (_      :_ ) = False

computeInfo :: LoopCensus -> LoopHeaders -> LoopInfo
computeInfo census headers = Map.mapMaybeWithKey go census
  where go id mt = let Just (hdr, called) = Map.lookup id headers in
                   if isAllNothing mt || not called
                     then Nothing
                     else Just (hdr, mt)

knFreshen (Ident name _) = ccFreshId name
knFreshen id@(GlobalSymbol  _) = error $ "KNExpr.hs: cannot freshen global " ++ show id
knFreshenTid (TypedId t id) = do id' <- knFreshen id
                                 return $ TypedId t id'

knLoopHeaderCensusFn activeids (id, fn) = do
  let vars = fnVars fn
  id'   <- lift $ knFresh "loop.hdr"
  vars' <- lift $ mapM knFreshenTid vars -- generate new vars for wrapper in advance
  st <- get
  put $ st { headers = Map.insert id ((id' , vars' ), False) (headers st)
           , census  = Map.insert id (map Just vars)         (census st) }
  knLoopHeaderCensus activeids (fnBody fn)

knLoopHeaderCensus :: Set Ident -> KNExpr' MonoType -> Hdr ()
knLoopHeaderCensus activeids expr = go expr where
  go expr = case expr of
    KNCase        _ _ patbinds -> do mapM_ (\(_,e) -> go e) patbinds
    KNUntil         _ e1 e2 _  -> do go e1 ; go e2
    KNIf          _ _ e1 e2    -> do go e1 ; go e2
    KNLetVal      id  e1 e2    -> do go e1
                                     case e1 of
                                       (KNTyApp _ v _)
                                         -> addIdRemapping id (tidIdent v)
                                       (KNVar v)
                                         -> addIdRemapping id (tidIdent v)
                                       _ -> return ()
                                     go e2
    KNLetRec      _   es  b    -> do mapM_ go es ; go b
    KNLetFuns     ids@[_] fns@[fn] b | isRec fn -> do
                                     mapM_ (knLoopHeaderCensusFn (Set.union activeids
                                                                   (Set.fromList ids)))
                                                                 (zip ids fns)
                                     -- Note: when we recur, activeids will not
                                     -- include the bound ids, so calls in the
                                     -- body will be ignored.
                                     go b
    KNLetFuns    _ids fns b    -> do mapM_ (knLoopHeaderCensus activeids . fnBody) fns
                                     go b
    KNCall YesTail _ v vs -> do
      id <- lookupId (tidIdent v)
      if Set.member id activeids
        then do st <- get
                put $ st { census  = Map.adjust (mergeInfo vs) id (census st)
                         , headers = Map.adjust (\(hdr, _) -> (hdr, True)) id (headers st) }
        else return ()

    -- Silently handle other cases...
    -- One potential improvement: track variable renamings.
    _ -> return ()

isRec fn = case fnIsRec fn of Just True -> True
                              _         -> False

lookupId id = do
  st <- get
  return $ Map.findWithDefault id id (varmap st)

addIdRemapping id id' = do
  id'' <- lookupId id'
  st <- get
  put $ st { varmap = Map.insert id id'' (varmap st) }

knLoopHeaders ::          (ModuleIL (KNExpr' MonoType) MonoType)
              -> Compiled (ModuleIL (KNExpr' MonoType) MonoType)
knLoopHeaders m = do body' <- knLoopHeaders' (moduleILbody m)
                     return $ m { moduleILbody = body' }

knLoopHeaders' :: KNExpr' MonoType -> Compiled (KNExpr' MonoType)
knLoopHeaders' expr = do
    HdrState h c r <- execStateT (knLoopHeaderCensus Set.empty expr)
                                 (HdrState Map.empty Map.empty Map.empty)
    let info = computeInfo c h
    --liftIO $ putStrLn $ show info
    return $ qq info r expr
 where
  qq info r expr =
   let qv id = Map.lookup (Map.findWithDefault id id r ) info in
   let q = qq info r in
   case expr of
    KNLiteral     {} -> expr
    KNVar         {} -> expr
    KNKillProcess {} -> expr
    KNTyApp       {} -> expr
    KNTuple       {} -> expr
    KNAllocArray  {} -> expr
    KNArrayRead   {} -> expr
    KNArrayPoke   {} -> expr
    KNAlloc       {} -> expr
    KNStore       {} -> expr
    KNDeref       {} -> expr
    KNCallPrim    {} -> expr
    KNAppCtor     {} -> expr
    KNUntil       ty e1 e2  rng -> KNUntil ty (q e1) (q e2) rng
    KNCase        ty v patbinds -> let patbinds' = map (\(p,e) -> (p, q e)) patbinds in
                                   KNCase ty v patbinds'
    KNIf          ty v e1 e2    -> KNIf     ty v (q e1) (q e2)
    KNLetVal      id   e1 e2    -> KNLetVal id   (q e1) (q e2)
    KNLetRec      ids es  b     -> KNLetRec ids (map q es) (q b)
    KNLetFuns     [id] [fn] b ->
        case qv id of
          Nothing -> KNLetFuns [id] [fn { fnBody = (q $ fnBody fn) }] (q b)

          -- If we have a single recursive function (as detected earlier),
          -- we should wrap its body with a minimal loop,
          -- and replace recursive calls with calls to a loop header.
          --
          -- For example, replace (rec fold = { f => x => ... fold f z ... };
          --                         in b end)
          -- with                 (fun fold = { f => x' =>
          --                         rec loop = { x => ... loop z ... };
          --                         in
          --                             loop x' end
          --                       }; in b end)
          Just ((id' , vs' ), mt ) -> -- vs' is the complete list of fresh args
            let v'  = TypedId (tidType (fnVar fn)) id' in
            -- The inner, recursive body
            let fn'' = Fn { fnVar   = mkGlobal v'
                          , fnVars  = dropUselessArgs mt (fnVars fn)
                          , fnBody  = (q $ fnBody fn)
                          , fnIsRec = Just True
                          , fnAnnot = ExprAnnot [] (annotRange $ fnAnnot fn) []
                          } in
            -- The outer, non-recursive wrapper:
            let fn' = Fn { fnVar   = fnVar fn
                         , fnVars  = renameUsefulArgs mt vs'
                         , fnBody  = KNLetFuns [ id' ] [ fn'' ]
                                         (KNCall YesTail (typeKN (fnBody fn)) v' (dropUselessArgs mt vs' ))
                         , fnIsRec = Just False
                         , fnAnnot = fnAnnot fn
                         } in
            KNLetFuns [id ] [ fn' ] (qq (Map.delete id info) r b)

    KNLetFuns     ids fns b     ->
        -- If we have a nest of recursive functions,
        -- the replacements should only happen locally, not intra-function.
        -- (TODO)
        KNLetFuns ids (map (\fn -> fn { fnBody = q (fnBody fn) }) fns) (q b)

    -- If we see a *tail* call to a recursive function, replace it with
    -- the appropriate pre-computed call to the corresponding loop header.
    KNCall tailq ty v vs ->
      case (tailq, qv (tidIdent v)) of
        (YesTail, Just ((id, _), mt)) ->
             KNCall YesTail ty (TypedId (tidType v) id) (dropUselessArgs mt vs)
        _ -> expr

mkGlobal (TypedId ty (Ident t u)) = TypedId ty (GlobalSymbol $ T.pack ((T.unpack t) ++ show u))
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
                                <+> text "(rec?:" <+> prettyfnIsRec fn <+> text ")"

prettyfnIsRec fn = p (fnIsRec fn)
  where p Nothing      = text "Nothing"
        p (Just True)  = text "True"
        p (Just False) = text "False"

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

pr YesTail = "(tail)"
pr NotTail = "(non-tail)"

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
            KNCall _tail t v vs -> showUnTyped (prettyId v <+> hsep (map pretty vs)) t <+> text "/*" <+> text (pr _tail) <+> text "*/"
            KNCallPrim t prim vs-> showUnTyped (text "prim" <+> pretty prim <+> hsep (map prettyId vs)) t
            KNAppCtor  t cid  vs-> showUnTyped (text "~" <> parens (text (show cid)) <> hsep (map prettyId vs)) t
            KNLetVal   x b    k -> lkwd "let"
                                      <+> fill 8 (text (show x))
                                      <+> text "="
                                      <+> (indent 0 $ pretty b) <+> lkwd "in"
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
                                   <$> nest 2 (kwd "then" <+> (indent 0 $ pretty b1))
                                   <$> nest 2 (kwd "else" <+> (indent 0 $ pretty b2))
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

-- {{{||||||||||||||||||||||  Inlining  ||||||||||||||||||||||||||||



{-

  Cases to consider::

   * (foo ... g ...) where
            * g   is a known value (function or other constant)
            * foo is a known function (assume w.l.o.g. it binds g to x)
            * substituting g for x doesn't blow up the code too much
              (always true if foo contains at most one occurrence of x;
               could be true if there are a few occurrences of x and
               g happens to be very small).

      There are two separate (and separable) things to do for this case:

        1. Specialize foo' = foo{g/x} and replace (foo .. g ..) w/ (foo' .. ..).
        2. Contify (foo' .. ..), because it has only a single call site.

      Note that foo may have multiple call sites,
      only some of which get inlined.

      Also note that the most important case is (probably) when g
      is a known function, rather than any other form of constant.


   * (foo ...) where foo is a very small function

      In this case, we should beta-reduce foo; even though it will
      blow the code up a little bit, there's no point in paying the
      cost of function call overhead for such a small body.

-}

knInline ::          (ModuleIL SrcExpr MonoType)
         -> Compiled (ModuleIL ResExpr MonoType)
knInline knmod = do
  liftIO $ putStrLn "~~~~~~~~~~ RUN INLINING ~~~~~~~~~~~~~~"
  uniq <- gets ccUniqRef

  expr' <- liftIO $
           evalStateT (knInlineToplevel (moduleILbody knmod)
                                        (SrcEnv Map.empty Map.empty))
                      (InlineState uniq Map.empty)

  return $ knmod { moduleILbody = expr' }

type In   = StateT InlineState IO
data InlineState = InlineState {
    inUniqRef  :: IORef Uniq
  , inVarCount :: Map Ident (IORef Int)
}

-- We really only care about functions, not arbitrary bindings (which are
-- often dead, for sequence-induced bindings). However, it's clearer to
-- just treat variables uniformly.
inNewVar :: ResId -> In ()
inNewVar id = do st <- get
                 r  <- liftIO $ newIORef 0
                 put $ st { inVarCount = Map.insert id r (inVarCount st) }

sawVar id = do vcm <- gets inVarCount
               case Map.lookup id vcm of
                 Nothing -> error $ "sawVar had no count for " ++ show id
                 Just r -> do liftIO $ modifyIORef r (+1)

{-
unSawVar id = do vcm <- gets inVarCount
                 case Map.lookup id vcm of
                   Nothing -> error $ "sawVar had no count for " ++ show id
                   Just r -> do v <- liftIO $ readIORef r
                                liftIO $ putStrLn $ "unSawVar " ++ show id ++ " with count " ++ show v
                                liftIO $ modifyIORef r (\x -> x - 1)
-}

getVarStatus id = do vcm <- gets inVarCount
                     case Map.lookup id vcm of
                       Nothing -> error $ "getVarStatus had no count for " ++ show id
                       Just r -> do v <- liftIO $ readIORef r
                                    return $ classifyVarCount v
data VarStatus = Dead | Once | Many deriving Show
classifyVarCount :: Int -> VarStatus
classifyVarCount x | x <= 0
                   = Dead
classifyVarCount 1 = Once
classifyVarCount _ = Many

notDead Dead = False
notDead _    = True

-- We need to force TextFragment to stay around because it will be
-- referenced by the standard library.
relevant occst id = notDead occst || id == (GlobalSymbol $ T.pack "TextFragment")

type SrcId = Ident
type ResId = Ident

freshenId :: SrcId -> In ResId
freshenId id = do id' <- freshenId' id
                  inNewVar id'
                  return id'

freshenId' :: SrcId -> In ResId
freshenId' (GlobalSymbol name) = -- error $ "can't freshen global symbol " ++ (T.unpack name)
     do u <- newUniq
        return $ Ident name u

freshenId' (Ident name _) = do
        u  <- newUniq
        return $ Ident name u

freshenTid tid = do
        id <- freshenId (tidIdent tid)
        return $ TypedId (tidType tid) id

-- resVar :: Env -> SrcVar -> In ResVar
resVar env v = do
        case lookupVarMb v env of
                   Just id -> do sawVar id
                                 return $ (TypedId (tidType v) id)
                   Nothing -> do return $ v

-- Specialized version of knInline' which does not rename functions.
knInlineToplevel :: SrcExpr -> SrcEnv -> In ResExpr
knInlineToplevel expr env = do
  let q v = resVar env v
  case expr of
    KNLetFuns ids fns body -> do
        liftIO $ putStrLn $ "saw toplevel fun bindings of " ++ show ids
        let ids' = ids -- Don't rename top-level functions!
        mapM_ inNewVar ids' -- but do give them occurrence counters

        refs <- mapM (\_ -> mkOpRefs) fns
        let ops  = map (\(f,(r1,r2,r3)) -> (Opnd f env' r1 r2 r3)) (zip fns refs)
            env' = extendEnv ids ids' (map VO_F ops) env

        b' <- knInlineToplevel body env'
        mb_fns <- mapM visitF ops
        let fns' = map (\(fn, mb_fn) -> case mb_fn of Just f -> f
                                                      Nothing -> fn) (zip fns mb_fns)
        --mapM_ (\id' -> do s <- getVarStatus id'
        --                  liftIO $ putStrLn $ "top level fn " ++ show id' ++ " is " ++ show s) ids'
        occ_sts <- mapM getVarStatus ids'

        let (ids'', fns'') = unzip [(id, fn) | (id, fn, occst) <- zip3 ids' fns' occ_sts
                                             , relevant occst id]
        return $ mkKNLetFuns ids'' fns'' b'

    KNCall tq ty v vs ->
        case lookupVarOp env v of
            Just (VO_F opf) -> do
                 _ <- visitF opf -- don't inline away main, just process it!
                 liftM2 (KNCall tq ty) (q v) (mapM q vs)
            _ -> error $ "knInlineToplevel couldn't find function to inline for main!"

    _ -> error $ "knInlineToplevel expected a series of KNLetFuns bindings! had " ++ show expr

mkKNLetFuns []  []  b = b
mkKNLetFuns ids fns b = KNLetFuns ids fns b

mkKNLetRec []  []  b = b
mkKNLetRec ids fns b = KNLetRec ids fns b

knInline' :: SrcExpr -> SrcEnv -> In ResExpr
knInline' expr env = do
  let qs str v = do --liftIO $ putStrLn $ "resVar << " ++ str ++ "\t;\t" ++ show (tidIdent v)
                    resVar env v
  let q v = resVar env v
  case expr of
    KNLiteral     {} -> return expr
    KNKillProcess {} -> return expr
    KNArrayRead ty (ArrayIndex v1 v2 rng sg)    -> (mapM q [v1,v2   ]) >>= \[q1,q2]    -> return $ KNArrayRead ty (ArrayIndex q1 q2 rng sg)
    KNArrayPoke ty (ArrayIndex v1 v2 rng sg) v3 -> (mapM q [v1,v2,v3]) >>= \[q1,q2,q3] -> return $ KNArrayPoke ty (ArrayIndex q1 q2 rng sg) q3
    KNAllocArray ty v      -> (q v)       >>= \zv -> return $ KNAllocArray ty zv
    KNDeref      ty v      -> (q v)       >>= \zv -> return $ KNDeref      ty zv
    KNAlloc      ty v mem  -> (q v)       >>= \zv -> return $ KNAlloc      ty zv mem
    KNTyApp      ty v tys  -> (q v)       >>= \zv -> return $ KNTyApp      ty zv tys
    KNTuple      ty vs rng -> (mapM q vs) >>= \zv -> return $ KNTuple      ty zv rng
    KNStore      ty v1 v2  -> liftM2                         (KNStore      ty) (q v1) (q v2)

    KNVar v -> do
      -- liftIO $ putStrLn $ "saw standalone var " ++ show v
      liftM KNVar (qs "KNVar" v)

    KNAppCtor     ty cid vs  -> liftM (KNAppCtor  ty cid) (mapM q vs)

    KNCallPrim    ty prim vs -> do
        -- If enough is known about the values to the prim,
        -- we might be able to partially evaluate it.

        mb_consts <- mapM (extractConstExpr env) vs
        case evalPrim ty prim mb_consts of
             Just e  -> return e
             Nothing -> do vs' <- mapM q vs
                           return $ KNCallPrim ty prim vs'

    KNCall tailq ty v vs -> do
      let resExpr s = do liftM2 (KNCall tailq ty) (qs ("KNCall v " ++ s) v) (mapM (qs "KNCall vs") vs)
      --liftIO $ putStrLn $ "saw call of var " ++ show (tidIdent v) ++ " ~?~> " ++ show (lookupVarMb v env)

      case lookupVarOp env v of
        -- Peek through type applications...
        Just (VO_E (Opnd (KNTyApp _ v' []) _ _ _ _)) -> peekTyApps v'
          where peekTyApps v' =
                  case lookupVarOp env v' of
                    Just (VO_E (Opnd (KNTyApp _ v'' []) _ _ _ _)) -> peekTyApps v''
                    Just (VO_E  _) -> resExpr "Just_VO_E"
                    Nothing        -> resExpr "Nothing"
                    Just (VO_F _) -> inlineBitcastedFunction v' tailq ty v vs env

        -- If the callee isn't a known function, we can't possibly inline it.
        Just (VO_E _)   -> do resExpr "Just_VO_E_"
        Nothing         -> do resExpr "Nothing"

        Just (VO_F opf) -> do
          let shouldNotInline nm = "noinline_" `isPrefixOf` nm
          if shouldNotInline (show $ tidIdent v)
            then do _ <- visitF opf -- don't inline this function...
                    resExpr "noinline"

            else do handleCallOfKnownFunction tailq expr resExpr opf v vs env qs

    KNUntil       ty e1 e2 rng -> do
        e1' <- knInline' e1 env
        e2' <- knInline' e2 env
        return $ KNUntil ty e1' e2' rng

    KNIf          ty v e1 e2 -> do
        -- If something is known about v's value,
        -- select either e1 or e2 appropriately;
        -- otherwise, if e2 and e3 are both the same value,
        -- we can get rid of the if;
        -- otherwise, business as usual.
        mb_const <- extractConstExpr env v
        case mb_const of
          Just (Lit (LitBool b)) -> knInline' (if b then e1 else e2) env
          _ -> do   v'  <- q v
                    e1' <- knInline' e1 env
                    e2' <- knInline' e2 env
                    return $ KNIf ty v' e1' e2'

    KNCase        ty v patbinds -> do
        let inlineArm ((pat, vars), expr) = do
                ops <- mapM (\v -> mkOpExpr (KNVar v) env) vars
                let ids  = map tidIdent vars
                ids'  <- mapM freshenId ids
                let env' = extendEnv ids ids' (map VO_E ops) env
                pat'  <- qp   (resVar env' ) pat
                vars' <- mapM (resVar env' ) vars
                expr' <- knInline' expr env'
                return ((pat' , vars' ), expr' )

        -- If something is known about v's value,
        -- select or discard the appropriate branches.
        -- TODO when are default branches inserted?
        mb_const <- extractConstExpr env v
        case mb_const of
          Just c -> case matchConstExpr c patbinds of
                      Right e -> knInline' e env
                      Left patbinds0 -> do v' <- q v
                                           patbinds' <- mapM inlineArm patbinds0
                                           return $ KNCase ty v' patbinds'
          _ -> do v' <- q v
                  patbinds' <- mapM inlineArm patbinds
                  return $ KNCase ty v' patbinds'

    KNLetVal id bound body -> do
        -- Be demand-driven: don't investigate e1 until e2 finds it necessary.
        --liftIO $ putStrLn $ "saw let binding  of " ++ show id
        id' <- freshenId id
        op <- mkOpExpr bound env
        let env' = extendEnv [ id ] [ id' ] [ VO_E op ] env

        --liftIO $ putStrLn $ "visiting body with " ++ show id ++ " remapped to " ++ show id'

        body'  <- knInline' body env'

        --liftIO $ putStrLn $ "visited  body with " ++ show id ++ " remapped to " ++ show id'
        --                                          ++ ", now visiting op " ++ show (pretty bound)

        bound' <- visitE op -- todo could this result in inlining a function?

        --s <- getVarStatus id'
        --liftIO $ putStrLn $ show id ++ " is " ++ show s

        let expr' = KNLetVal id' bound' body'

        --liftIO $ putStrLn "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"
        --liftIO $ putDoc $ text ("pre-processed let binding  of " ++ show id) <> text "\n"
        --                  <$> indent 4 (pretty expr  ) <> text "\n\n"
        --liftIO $ putDoc $ text ("postprocessed let binding  of " ++ show id)
        --                  <$> indent 4 (pretty expr' ) <> text "\n\n"
        --liftIO $ putStrLn "^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^"

        return expr'

    KNLetRec     ids es  b -> do
        --liftIO $ putStrLn $ "saw rec bindings of " ++ show ids
        ids' <- mapM freshenId ids
        refs <- mapM (\_ -> mkOpRefs) es
        let ops  = map (\(e,(r1,r2,r3)) -> (Opnd e env' r1 r2 r3)) (zip es refs)
            env' = extendEnv ids ids' (map VO_E ops) env
        b' <- knInline' b env'
        es'     <- mapM visitE ops
        occ_sts <- mapM getVarStatus ids'
        let (ids'', fns'') = unzip [ide | (ide, occst) <- zip (zip ids' es' ) occ_sts
                                        , notDead occst]
        return $ mkKNLetRec ids'' fns'' b'

    KNLetFuns    ids fns0 b -> do
        --liftIO $ putStrLn $ "saw fun bindings of " ++ show ids
        ids' <- mapM freshenId ids

        -- Rename the fnVar so we don't get duplicate procedure names.
        -- TODO would this be a good place to rename procedures to reflect scoping?
        let mkGlobal (TypedId t _) (Ident s u) = TypedId t (GlobalSymbol $ T.pack (T.unpack s ++ show u))

        let fns = map (\(f, id) -> f { fnVar = mkGlobal (fnVar f) id } ) (zip fns0 ids' )
        refs <- mapM (\_ -> mkOpRefs) fns

        let ops  = map (\(f,(r1,r2,r3)) -> (Opnd f env' r1 r2 r3)) (zip fns refs)
            env' = extendEnv ids ids' (map VO_F ops) env

        --liftIO $ putStrLn $ "processing body of fn-bindings w/ ids " ++ show ids
        b' <- knInline' b env'
        --liftIO $ putStrLn $ "processed  body of fn-bindings w/ ids " ++ show ids ++ ", now visiting the fns themselves"

        --mapM_ (\id' -> do s <- getVarStatus id'
        --                  liftIO $ putStrLn $ "nested fn " ++ show id' ++ " is " ++ show s) ids'

        mb_fns <- mapM visitF ops
        occ_sts <- mapM getVarStatus ids'
        let fns' = map (\(fn, mb_fn) -> case mb_fn of Just f -> f
                                                      Nothing -> fn) (zip fns mb_fns)
        let (ids'', fns'') = unzip [idfn | (idfn, occst) <- zip (zip ids' fns' ) occ_sts
                                         , notDead occst]
        return $ mkKNLetFuns ids'' fns'' b'

handleCallOfKnownFunction tailq expr resExprA opf v vs env qs = do
    -- liftIO $ putStrLn $ "saw call of var " ++ show (tidIdent v) ++ " ~~> " ++ show (tidIdent (fnVar fn))
    -- liftIO $ putStrLn $    "call of var " ++ show (tidIdent v) ++ " ~~> " ++ show (tidIdent (fnVar fn))
    -- liftIO $ putDoc $ text "    " <> pretty expr <> text "\n"
    -- liftIO $ putDoc $ text "resulted in:\n" <> pretty f' <+> text "\n\n"
    qvs'  <- mapM (qs "known call vs") vs
    mb_e' <- foldLambda' tailq opf qvs' env
    case mb_e' of
       Just e' -> do --liftIO $ putDoc $ text "lambda folding resulted in " <> pretty e' <> text "\n"
                     --case lookupVarMb v env of
                     --   Just id -> unSawVar id
                     --   Nothing -> return ()
                     let size@(topsz, _) = knSize e'
                     if topsz < 30
                       then do --liftIO $ putDoc $ text ("\tlambda folding " ++ show (tidIdent v) ++ " resulted in expr of size ") <> text (show size) <> text "\n"
                               --liftIO $ putDoc $ text ("\tlambda folding " ++ show (tidIdent v) ++ " resulted in expr         ") <> pretty e' <> text "\n"
                               return e'
                       else do --liftIO $ putDoc $ text ("\tlambda folding " ++ show (tidIdent v) ++ " failed due to expr of size ") <> text (show size) <> text "\n"
                               resExprA "toobig"
       Nothing -> do -- liftIO $ putDoc $ text "lambda folding " <> pretty expr' <> text " failed; residualizing call instead.\n"
                     resExprA "kNothing"
  where
    -- input are residual vars, not src vars, fwiw
    foldLambda' :: TailQ -> Opnd (Fn SrcExpr MonoType) -> [TypedId MonoType] -> SrcEnv -> In (Maybe ResExpr)
    foldLambda' tailq (Opnd fn _ _ loc_op _) vs' env = do

      let env' = extendEnv ids ids' ops env
                    where
                            ids  = map tidIdent (fnVars fn)
                            ids' = map tidIdent vs'
                            ops  = map (lookupVarOp' env) vs'

      -- ids   are the function's formals;
      -- vs'   are the function's actuals (residual vars)
      -- ops   are the corresponding operand structures.

      -- liftIO $ putDoc $ text "with arg ops:" <+> text (show ops) <> text "\n"

      o_pending <- readRef loc_op
      case o_pending of
        OP_True -> do
          -- liftIO $ putDoc $ text "lambda folding failed due to outer-pending flag...\n"
          return Nothing

        OP_False -> do
          writeRef loc_op OP_True
          let mangle = case tailq of YesTail -> id
                                     NotTail -> removeTailCallAnnots
          e' <- knInline' (mangle $ fnBody fn) env'
          writeRef loc_op OP_False
          return $ Just e'

--visitF :: OpndF -> In (Maybe (Fn ResExpr MonoType))
visitF (Opnd fn env loc_fn _ loc_ip) = do
  ff <- readRef loc_fn
  case ff of
    Unvisited -> do
        ip <- readRef loc_ip
        case ip of
          IP_False -> do
            writeRef loc_ip IP_True
            fn' <- knInlineFn' fn env
            writeRef loc_fn (Visited fn' )
            return $ Just fn'
          IP_True -> do
            liftIO $ putStrLn $ "inner-pending true for " ++ show (tidIdent $ fnVar fn)
            return Nothing
    Visited f -> return $ Just f
 where
    knInlineFn' :: Fn SrcExpr MonoType -> SrcEnv -> In (Fn ResExpr MonoType)
    knInlineFn' fn env = do
      -- liftIO $ putStrLn $ "examining function " ++ show (fnVar fn)
      let vs = fnVars fn
      vs'   <- mapM freshenTid vs
      -- TODO assert that the ops associated with the incoming vars are trivial
      -- liftIO $ putDoc $ text "mapping fn formals: " <+> pretty (zip vs vs' ) <> text " ... \n"
      let foldEnv env (v , v' ) = do
          ope <- mkOpExpr (KNVar v' ) env
          return $ extendEnv [tidIdent v] [tidIdent v' ] [ VO_E ope ] env
      env' <- foldlM foldEnv env (zip vs vs' )
      body' <- knInline' (fnBody fn) env'
      return $ fn { fnBody = body' , fnVars = vs' }

--visitE :: OpndE -> In (KNExpr' MonoType)
visitE (Opnd e env loc_e _ loc_ip) = do
  ef <- readRef loc_e
  case ef of
    Unvisited -> do
        --liftIO $ putStrLn $ "\nvisited opnd " ++ show (pretty e) ++ ", it was Unvisited..."
        ip <- readRef loc_ip
        case ip of
          IP_False -> do
            -- TODO set IP_True flag?
            e' <- knInline' e env
            --liftIO $ putStrLn $ "visited opnd " ++ show (pretty e) ++ ", it was Unvisited, visiting it resulted in\n" ++ show (pretty e' )
            --liftIO $ putStrLn $ ""
            writeRef loc_e (Visited e' )
            return e'
          IP_True -> do
            liftIO $ putStrLn $ "inner-pending true for expr...????"
            return e --TODO this is WRONG :(
    Visited r -> do
        --liftIO $ putStrLn $ "visited opnd " ++ show (pretty e) ++ ", it was Visited:\n" ++ show (pretty r)
        return r

inlineBitcastedFunction v' tailq ty v vs env = do
    -- Some of the formal parameters to the underlying function
    -- may be generically typed. Elsewhere in the compiler, we'll
    -- insert bitcasts around the called function, but when we're
    -- inlining, that won't work -- we need to bitcast every parameter
    -- with a type mismatch (not just those that are PtrTypeUnknown),
    -- and possibly also the result.
    let (FnType tys tyr _ _) = tidType v'
    binders_ref <- liftIO $ newIORef []
    vs' <- mapM (\(ty, vorig) -> do
      if ty == tidType vorig
           then return vorig
           else do
                      let e = KNTyApp ty vorig []
                      newid <- freshenId (Ident (T.pack "castarg") (error "newid"))
                      liftIO $ modifyIORef binders_ref (++[(newid, e)])
                      return $ TypedId ty newid
                   ) (zip tys vs)
    binders <- liftIO $ readIORef binders_ref
    -- If we leave a YesTail marker on a call which is, strictly speaking,
    -- not tail due to a pending bitcast of its result, CFG building will
    -- drop the pending bitcast. But we don't need to do tht if the bitcast
    -- would be a no-op. Incidentally, this highlights a slight tension:
    -- fully monomorphizing avoids the need for bitcasts, but risks code blowup.
    if ty == tyr then do knInline' (mkLetVals binders $ KNCall tailq ty  v' vs') env
                 else do newid <- freshenId (Ident (T.pack "castres") (error "newid"))
                         let vres = TypedId tyr newid
                         knInline' (KNLetVal newid
                                      (mkLetVals binders $ KNCall NotTail tyr v' vs')
                                      (KNTyApp ty vres [])) env

data ConstExpr = Lit            Literal
               | NullaryCtor    CtorId
               deriving Show

extractConstExpr :: SrcEnv -> TypedId MonoType -> In (Maybe ConstExpr)
extractConstExpr env var = go var where
 go v = case lookupVarOp env v of
            Just (VO_E ope) -> do
                 e <- visitE ope
                 case e of
                    KNLiteral _ lit    -> return $ Just $ Lit         lit
                    KNAppCtor _ cid [] -> return $ Just $ NullaryCtor cid
                    _                  -> return $ Nothing
                    -- TODO could recurse through binders
                    -- TODO could track const-ness of ctor args
            _ -> return $ Nothing

matchConstExpr :: ConstExpr -> [PatternBinding (KNExpr' MonoType) MonoType] -> (Either [PatternBinding (KNExpr' MonoType) MonoType] SrcExpr)
matchConstExpr c patbinds = go patbinds
  where go [] = Left patbinds -- no match found
        go (((p,_),e):rest) = if matchPatternWithConst p c then Right e else go rest

matchPatternWithConst :: Pattern ty -> ConstExpr -> Bool
matchPatternWithConst p c =
  case (c, p) of
    (_, P_Wildcard _ _  ) -> True
    -- (_, P_Variable _ tid) -> Just [(tidIdent tid, v)]
    (Lit (LitInt  i1), P_Int  _ _ i2) -> litIntValue i1 == litIntValue i2
    (Lit (LitBool b1), P_Bool _ _ b2) -> b1 == b2
    (NullaryCtor vid, P_Ctor _ _ [] (CtorInfo cid _)) -> vid == cid
    (_ , _) -> False

evalPrim resty (PrimOp "==" _ty)
         [Just (Lit (LitInt i1)), Just (Lit (LitInt i2))]
                = Just (KNLiteral resty (LitBool $ litIntValue i1 == litIntValue i2))
evalPrim _ _ _ = Nothing

mkOpRefs = do
  lexp <- newRef Unvisited
  oup  <- newRef OP_False
  inp  <- newRef IP_False
  return (lexp, oup, inp)

mkOpExpr e env = do
  (le, oup, inp) <- mkOpRefs
  return $ Opnd e env le oup inp

-- Apply a variable substitution in a pattern.
qp :: (TypedId ty -> In (TypedId ty)) -> (Pattern ty) -> In (Pattern ty)
qp subst pattern = do
 case pattern of
   P_Wildcard rng t            -> return $ P_Wildcard rng t
   P_Bool     rng t b          -> return $ P_Bool     rng t b
   P_Int      rng t i          -> return $ P_Int      rng t i
   P_Variable rng v            -> liftM   (P_Variable rng)   (subst v)
   P_Tuple    rng t pats       -> liftM   (P_Tuple    rng t) (mapM (qp subst) pats)
   P_Ctor     rng t pats ctor  -> do p' <- (mapM (qp subst) pats)
                                     return $ P_Ctor  rng t p' ctor

type SrcExpr = (KNExpr' MonoType)
type ResExpr = (KNExpr' MonoType)
data VisitStatus t = Unvisited | Visited t
data SrcEnv = SrcEnv (Map Ident VarOp)
                     (Map Ident Ident)
data OuterPending = OP_False | OP_True
data InnerPending = IP_False | IP_True
data Opnd v = Opnd v SrcEnv (IORef (VisitStatus v)) (IORef OuterPending) (IORef InnerPending)
data VarOp = VO_E (Opnd     SrcExpr)
           | VO_F (Opnd (Fn SrcExpr MonoType))

-- We don't track var flags here because we syntactically distinguish
-- assigned variables from pure ones, and we can use Hoopl-based liveness
-- later on to eliminate useless assignments and/or bindings.

instance Show VarOp where
  show (VO_E _) = "VO_E"
  show (VO_F (Opnd f _ _ _ _)) = "VO_F " ++ show (tidIdent $ fnVar f)

lookupVarMb :: TypedId MonoType -> SrcEnv -> Maybe Ident
lookupVarMb v (SrcEnv _ ii) = Map.lookup (tidIdent v) ii

-- src var
lookupVarOp :: SrcEnv -> TypedId MonoType -> Maybe VarOp
lookupVarOp env@(SrcEnv tv _) v =
  case lookupVarMb v env of
    Nothing -> -- Declarations for external functions won't
               -- have a known binding, obviously.
               Map.lookup (tidIdent v) tv
    Just vv ->
      case Map.lookup vv tv of
        Just op -> Just op
        Nothing -> error $ "KNExpr inlining (lookupVarOp) failed to look up var op " ++ show v ++ " ~~> " ++ show vv

-- residual var
lookupVarOp' :: SrcEnv -> TypedId MonoType -> VarOp
lookupVarOp' (SrcEnv tv _) vv =
  case Map.lookup (tidIdent vv) tv of
    Just op -> op
    Nothing -> error $ "KNExpr inlining (lookupVarOp') failed to look up var op " ++ show vv

extendEnv :: [Ident] -> [Ident] -> [VarOp] -> SrcEnv -> SrcEnv
extendEnv ids ids' ops (SrcEnv io ii) =
        (SrcEnv (Map.union (Map.fromList $ zip ids' ops  ) io)
                (Map.union (Map.fromList $ zip ids  ids' ) ii))

readRef  r   = liftIO $ readIORef  r
writeRef r v = liftIO $ writeIORef r v
newRef     v = liftIO $ newIORef     v
newUniq = do uref <- gets inUniqRef
             liftIO $ modifyIORef uref (+1) >> readIORef uref

-- When we inline a function body, it moves from a tail context to a non-tail
-- context, so we must remove any direct tail-call annotations.
removeTailCallAnnots :: KNExpr' MonoType -> KNExpr' MonoType
removeTailCallAnnots expr = go expr where
  go expr = case expr of
    KNCase        ty v patbinds -> KNCase    ty v (map (\(p,e) -> (p, go e)) patbinds)
    KNIf          ty v e1 e2    -> KNIf      ty v (go e1) (go e2)
    KNLetVal      id   e1 e2    -> KNLetVal  id       e1  (go e2)
    KNLetRec      ids  es  b    -> KNLetRec  ids      es  (go b)
    KNLetFuns     ids  fns b    -> KNLetFuns ids     fns  (go b)
    KNCall _ ty v vs -> KNCall NotTail ty v vs
    _ -> expr


-- The non-local exits in the Chez Scheme inlining algorithm
-- would be very nice to implement using coroutines!
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||


knSize :: KNExpr' t -> (Int, Int) -- toplevel, cumulative
knSize expr = go expr (0, 0) where
  go expr (t, a) = case expr of
    KNLiteral     {} -> (t, a)
    KNVar         {} -> (t, a)
    KNKillProcess {} -> (t, a)
    KNTyApp       {} -> (t, a)
    KNTuple       {} -> (t + 1, a + 1)
    KNAllocArray  {} -> (t + 1, a + 1)
    KNArrayRead   {} -> (t + 1, a + 1)
    KNArrayPoke   {} -> (t + 1, a + 1)
    KNAlloc       {} -> (t + 1, a + 1)
    KNStore       {} -> (t + 1, a + 1)
    KNDeref       {} -> (t + 1, a + 1)
    KNCallPrim    {} -> (t + 1, a + 1)
    KNCall        {} -> (t + 1, a + 1)
    KNAppCtor     {} -> (t + 1, a + 1)
    KNUntil       _   e1 e2 _  -> go e2 (go e1 (t + 1, a + 1))
    KNIf          _ _ e1 e2    -> go e2 (go e1 (t + 1, a + 1))
    KNCase        _ _ patbinds -> foldl' (\ta (_, e) -> go e ta) (t, a) patbinds
    KNLetVal      _   e1 e2    -> go e2 (go e1 (t + 1, a + 1))
    KNLetRec     _ es b        -> foldl' (\ta e -> go e ta) (go b (t, a)) es
    KNLetFuns    _ fns b       -> let n = length fns in
                                  let ta' @ (t', _ ) = go b (t, a) in
                                  let (_, bodies) = foldl' (\ta fn -> go (fnBody fn) ta) ta' fns in
                                  (t' + n, n + bodies)

