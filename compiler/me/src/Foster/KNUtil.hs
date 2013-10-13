{-# LANGUAGE StandaloneDeriving, BangPatterns #-}
-----------------------------------------------------------------------------
-- Copyright (c) 2013 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.KNUtil where

import Foster.Base

import Foster.MonoType
import Foster.TypeIL

import Text.PrettyPrint.ANSI.Leijen

import Data.List(foldl')
import Data.Map(Map)
import Data.Map as Map(insert, lookup, empty)
import qualified Data.Text as T
import Control.Monad.State(evalStateT, get, gets, put,
                               StateT, liftIO, liftM, liftM2)
import Data.IORef

--------------------------------------------------------------------

-- | Foster.KNExpr binds all intermediate values to named variables
-- | via a variant of K-normalization.  We also perform local block sinking,
-- | in preparation for later contification.

data KNExpr' r ty =
        -- Literals
          KNLiteral     ty Literal
        | KNTuple       ty [TypedId ty] SourceRange
        | KNKillProcess ty T.Text
        -- Control flow
        | KNIf          ty (TypedId ty)    (KNExpr' r ty) (KNExpr' r ty)
        | KNUntil       ty (KNExpr' r ty)  (KNExpr' r ty) SourceRange
        -- Creation of bindings
        | KNCase        ty (TypedId ty) [CaseArm PatternRepr (KNExpr' r ty) ty]
        | KNLetVal      Ident        (KNExpr' r ty)     (KNExpr' r ty)
        | KNLetRec     [Ident]       [KNExpr' r ty]     (KNExpr' r ty)
        | KNLetFuns    [Ident] [Fn r (KNExpr' r ty) ty] (KNExpr' r ty)
        -- Use of bindings
        | KNVar         (TypedId ty)
        | KNCallPrim    ty (FosterPrim ty)    [TypedId ty]
        | KNCall TailQ  ty (TypedId ty)       [TypedId ty]
        | KNAppCtor     ty (CtorId, CtorRepr) [TypedId ty]
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

type KNExpr     = KNExpr' () TypeIL
type KNExprFlat = KNExpr' () TypeIL
type KNMono     = KNExpr' RecStatus MonoType

type FnExprIL = Fn () KNExpr TypeIL
type FnMono   = Fn RecStatus KNMono MonoType

--------------------------------------------------------------------

{-
showFnStructure :: Fn r KNExpr TypeIL -> Doc
showFnStructure (Fn fnvar args body _ _srcrange) =
  pretty fnvar <+> text "=" <+>
                     text "{" <+> hsep (map pretty args)
                 <$> indent 2 (showStructure body)
                 <$> text "}" <> line
-}

alphaRename' :: Fn r (KNExpr' r2 t) t -> IORef Uniq -> IO (Fn r (KNExpr' r2 t) t)
alphaRename' fn uref = do
  renamed <- evalStateT (renameFn fn) (RenameState uref Map.empty)

  --whenMonoWanted (tidIdent $ fnVar fn) $ liftIO $ do
  --    putDoc $ text "fn:      " <$> showFnStructure fn
  --    putDoc $ text "renamed: " <$> showFnStructure renamed

  return renamed
   where
    renameV :: TypedId t -> Renamed (TypedId t)
    renameV tid@(TypedId _ (GlobalSymbol _)) = return tid
    renameV     (TypedId t id) = do
      state <- get
      case Map.lookup id (renameMap state) of
        Nothing  -> do id' <- renameI id
                       return (TypedId t id' )
        Just _u' -> error "can't rename a variable twice!"

    renameI id@(GlobalSymbol _) = return id
    renameI id@(Ident s _)      = do u' <- fresh
                                     let id' = Ident s u'
                                     remap id id'
                                     return id'
      where
        fresh :: Renamed Uniq
        fresh = do uref <- gets renameUniq ; mutIORef uref (+1)

        mutIORef :: IORef a -> (a -> a) -> Renamed a
        mutIORef r f = liftIO $ modifyIORef r f >> readIORef r

        remap id id' = do state <- get
                          put state { renameMap = Map.insert id id' (renameMap state) }

    qv :: TypedId t -> Renamed (TypedId t)
    qv (TypedId t i) = do i' <- qi i ; return $ TypedId t i'

    qi v@(GlobalSymbol _) = return v
    qi v = do state <- get
              case Map.lookup v (renameMap state) of
                Just v' -> return v'
                Nothing -> return v

    renameFn :: Fn r (KNExpr' r2 t) t -> Renamed (Fn r (KNExpr' r2 t) t)
    renameFn (Fn v vs body isrec rng) = do
       (v' : vs') <- mapM renameV (v:vs)
       body' <- renameKN body
       return (Fn v' vs' body' isrec rng)

    renameArrayIndex (ArrayIndex v1 v2 rng s) =
      mapM qv [v1,v2] >>= \[v1' , v2' ] -> return $ ArrayIndex v1' v2' rng s

    renameKN :: (KNExpr' r t) -> Renamed (KNExpr' r t)
    renameKN e =
      case e of
      KNLiteral       {}       -> return e
      KNKillProcess   {}       -> return e
      KNTuple         t vs a   -> mapM qv vs     >>= \vs' -> return $ KNTuple t vs' a
      KNCall       tc t v vs   -> mapM qv (v:vs) >>= \(v':vs') -> return $ KNCall tc t v' vs'
      KNCallPrim      t p vs   -> liftM  (KNCallPrim      t p) (mapM qv vs)
      KNAppCtor       t c vs   -> liftM  (KNAppCtor       t c) (mapM qv vs)
      KNAllocArray    t v      -> liftM  (KNAllocArray    t) (qv v)
      KNAlloc         t v _rgn -> liftM  (\v' -> KNAlloc  t v' _rgn) (qv v)
      KNDeref         t v      -> liftM  (KNDeref         t) (qv v)
      KNStore         t v1 v2  -> liftM2 (KNStore         t) (qv v1) (qv v2)
      KNArrayRead     t ai     -> liftM  (KNArrayRead     t) (renameArrayIndex ai)
      KNArrayPoke     t ai v   -> liftM2 (KNArrayPoke     t) (renameArrayIndex ai) (qv v)
      KNVar                  v -> liftM  KNVar                  (qv v)
      KNCase          t v arms -> do arms' <- mapM renameCaseArm arms
                                     v'    <- qv v
                                     return $ KNCase       t v' arms'
      KNUntil         t c b r  -> do [econd, ebody] <- mapM renameKN [c, b ]
                                     return $ KNUntil      t econd ebody r
      KNIf            t v e1 e2-> do [ethen, eelse] <- mapM renameKN [e1,e2]
                                     v' <- qv v
                                     return $ KNIf         t v' ethen eelse
      KNLetVal       id e   b  -> do id' <- renameI id
                                     [e' , b' ] <- mapM renameKN [e, b]
                                     return $ KNLetVal id' e'  b'
      KNLetRec     ids exprs e -> do ids' <- mapM renameI ids
                                     (e' : exprs' ) <- mapM renameKN (e:exprs)
                                     return $ KNLetRec ids' exprs'  e'
      KNLetFuns     ids fns b  -> do ids' <- mapM renameI ids
                                     fns' <- mapM renameFn fns
                                     b'   <- renameKN b
                                     return $ KNLetFuns ids' fns' b'
      KNTyApp t v argtys       -> qv v >>= \v' -> return $ KNTyApp t v' argtys

    renameCaseArm (CaseArm pat expr guard vs rng) = do
        pat' <- renamePattern pat
        vs' <- mapM qv vs -- TODO or renameV ?
        expr'  <-           renameKN expr
        guard' <- liftMaybe renameKN guard
        return (CaseArm pat' expr' guard' vs' rng)

    renamePatternAtom pattern = do
     case pattern of
       P_Wildcard {}          -> return pattern
       P_Bool     {}          -> return pattern
       P_Int      {}          -> return pattern
       P_Variable rng v       -> qv v >>= \v' -> return $ P_Variable rng v'

    renamePattern pattern = do
     let mp = mapM renamePattern
     case pattern of
       PR_Atom     atom             -> renamePatternAtom atom >>= \atom' -> return $ PR_Atom atom'
       PR_Ctor     rng t pats ctor  -> mp pats >>= \pats' -> return $ PR_Ctor  rng t pats' ctor
       PR_Tuple    rng t pats       -> mp pats >>= \pats' -> return $ PR_Tuple rng t pats'


data RenameState = RenameState {
                       renameUniq :: IORef Uniq
                     , renameMap  :: Map Ident Ident
                   }
type Renamed = StateT RenameState IO

--------------------------------------------------------------------


-- ||||||||||||||||||||||||| Boilerplate ||||||||||||||||||||||||{{{

deriving instance (Show ty, Show rs) => Show (KNExpr' rs ty) -- used elsewhere...

instance (Show t) => AExpr (KNExpr' rs t) where
    freeIdents e = case e of
        KNLetVal   id  b   e -> freeIdents b ++ (freeIdents e `butnot` [id])
        KNLetRec   ids xps e -> (concatMap freeIdents xps ++ freeIdents e)
                                                                   `butnot` ids
        KNLetFuns  ids fns e -> (concatMap freeIdents fns ++ freeIdents e)
                                                                   `butnot` ids
        KNCase  _t v arms    -> [tidIdent v] ++ concatMap caseArmFreeIds arms
        KNVar      v         -> [tidIdent v]
        _                    -> concatMap freeIdents (childrenOf e)

-- This is necessary due to transformations of AIIf and nestedLets
-- introducing new bindings, which requires synthesizing a type.
typeKN :: KNExpr' rs ty -> ty
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
instance Show ty => Structured (KNExpr' rs ty) where
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
            KNCase _t v arms    -> text $ "KNCase      " ++ show v ++ " binding " ++ (show $ map caseArmBindings arms)
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
            KNCase _ e arms         -> (var e):(concatMap caseArmExprs arms)
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


knSize :: KNExpr' r t -> (Int, Int) -- toplevel, cumulative
knSize expr = go expr (0, 0) where
  go expr (t, a) = let ta = let v = knSizeHead expr in (t + v, a + v) in
                   case expr of
    KNUntil       _   e1 e2 _  -> go e2 (go e1 ta)
    KNIf          _ _ e1 e2    -> go e2 (go e1 ta)
    KNCase        _ _ arms     -> foldl' (\ta e -> go e ta) ta (concatMap caseArmExprs arms)
    KNLetVal      _   e1 e2    -> go e2 (go e1 (t, a))
    KNLetRec     _ es b        -> foldl' (\ta e -> go e ta) (go b ta) es
    KNLetFuns    _ fns b       -> let n = length fns in
                                  let ta' @ (t', _ ) = go b ta in
                                  let (_, bodies) = foldl' (\ta fn -> go (fnBody fn) ta) ta' fns in
                                  (t' + n, n + bodies)
    _ -> ta

-- Only count the effect of the head constructor.
-- The caller should maintain the invariant that
-- the arguments to that constructor have already
-- been individually accounted for.
knSizeHead :: KNExpr' r t -> Int
knSizeHead expr = case expr of
    KNLiteral _ (LitText _) -> 2 -- text literals are dyn alloc'd, for now.
    KNLiteral     {} -> 0
    KNVar         {} -> 0
    KNKillProcess {} -> 0
    KNTyApp       {} -> 0
    KNLetVal      {} -> 0

    KNAllocArray  {} -> 1
    KNAlloc       {} -> 1
    KNStore       {} -> 1
    KNDeref       {} -> 1
    KNCallPrim    {} -> 1
    KNIf          {} -> 1
    KNLetRec      {} -> 1
    KNLetFuns     {} -> 1

    KNTuple       {} -> 2 -- due to allocation + stores
    KNArrayRead   {} -> 2 -- due to (potential) bounds check
    KNArrayPoke   {} -> 2 -- due to (potential) bounds check
    KNCall        {} -> 4 -- due to dyn. insn overhead, stack checks, etc
    KNUntil       {} -> 1
    KNCase        {} -> 2 -- TODO might be cheaper for let-style cases.

    KNAppCtor     {} -> 3 -- rather like a KNTuple, plus one store for the tag.
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

