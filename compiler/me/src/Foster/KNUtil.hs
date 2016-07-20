{-# LANGUAGE StandaloneDeriving, BangPatterns, FlexibleContexts #-}
-----------------------------------------------------------------------------
-- Copyright (c) 2013 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.KNUtil where

import Prelude hiding ((<$>))

import Foster.Base
import Foster.Kind
import Foster.Config(Compiled, CompilerContext(ccUniqRef))

import Text.PrettyPrint.ANSI.Leijen

import Data.List(foldl')
import Data.Map(Map)
import qualified Data.Map as Map(insert, lookup, empty)
import qualified Data.Text as T
import Control.Monad.State(evalStateT, get, gets, put, lift,
                               StateT, liftIO, liftM, liftM2, liftM3, liftM4)
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
        -- Creation of bindings
        | KNCase        ty (TypedId ty) [CaseArm PatternRepr (KNExpr' r ty) ty]
        | KNLetVal      Ident        (KNExpr' r ty)     (KNExpr' r ty)
        | KNLetRec     [Ident]       [KNExpr' r ty]     (KNExpr' r ty)
        | KNLetFuns    [Ident] [Fn r (KNExpr' r ty) ty] (KNExpr' r ty)
        -- Use of bindings
        | KNVar         (TypedId ty)
        | KNCallPrim    SourceRange ty (FosterPrim ty)    [TypedId ty]
        | KNCall        ty (TypedId ty)       [TypedId ty]
        | KNAppCtor     ty (CtorId, CtorRepr) [TypedId ty]
        -- Mutable ref cells
        | KNAlloc       ty (TypedId ty) AllocMemRegion
        | KNDeref       ty (TypedId ty)
        | KNStore       ty (TypedId ty) (TypedId ty)
        -- Array operations
        | KNAllocArray  ty (TypedId ty) AllocMemRegion ZeroInit
        | KNArrayRead   ty (ArrayIndex (TypedId ty))
        | KNArrayPoke   ty (ArrayIndex (TypedId ty)) (TypedId ty)
        | KNArrayLit    ty (TypedId ty) [Either Literal (TypedId ty)]
        -- Others
        | KNTyApp       ty (TypedId ty) [ty]
        | KNCompiles    KNCompilesResult ty (KNExpr' r ty)
        | KNNotInlined  (String, (FoldStatus, Int, Maybe Int)) (KNExpr' r ty)
        | KNInlined     Int Int Int (KNExpr' r ty) (KNExpr' r ty) -- old, new
                     --          ^ "after" time of inlining new
                     --      ^ "before" time of inlining new
                     --  ^ time of first processing opnd

-- {{{ Inlining-related definitions
data FoldStatus = FoldTooBig Int -- size (stopped before inlining)
                | FoldEffort Doc | FoldSize SizeCounter -- (stopped while inlining)
                | FoldOuterPending | FoldInnerPending | FoldRecursive
                | FoldCallSiteOptOut | FoldNoBinding deriving Show

data SizeCounter = SizeCounter Int SizeLimit deriving Show

data SizeLimit = NoLimit | Limit (Int, String) deriving Show
-- }}}

-- When monmomorphizing, we use (KNTyApp t v [])
-- to represent a bitcast to type t.

type KNExpr     = KNExpr' () TypeIL
type KNExprFlat = KNExpr' () TypeIL

type FnExprIL = Fn () KNExpr TypeIL

class AlphaRenamish t rs where
  ccAlphaRename :: Fn r (KNExpr' rs t) t -> Compiled (Fn r (KNExpr' rs t) t)

--------------------------------------------------------------------

--showFnStructureX :: Fn r KNExpr TypeIL -> Doc
showFnStructureX (Fn fnvar args body _ _srcrange) =
  pretty fnvar <+> text "=" <+>
                     text "{" <+> hsep (map pretty args)
                 <$> indent 2 (showStructure body)
                 <$> text "}" <> line

alphaRename' :: (Show r2) => Fn r (KNExpr' r2 TypeIL) TypeIL -> Compiled (Fn r (KNExpr' r2 TypeIL) TypeIL)
--alphaRename' :: Fn r (KNExpr' r2 t) t -> IORef Uniq -> IO (Fn r (KNExpr' r2 t) t)
alphaRename' fn = do
  renamed <- evalStateT (renameFn fn) (RenameState Map.empty)

  liftIO $ do
      putDoc $ text "fn (IL): " <$> showFnStructureX fn
      putDoc $ text "renamed: " <$> showFnStructureX renamed

  return renamed
   where
    renameT :: TypeIL -> Renamed TypeIL
    renameT typ = case typ of
          PrimIntIL      {}           -> return $ typ
          TyConIL        {}           -> return $ typ
          TyAppIL     con ts          -> do liftM2 TyAppIL (renameT con) (mapM renameT ts)
          TupleTypeIL  k ts           -> do liftM (TupleTypeIL k) (mapM renameT ts)
          CoroTypeIL     s  r         -> do liftM2 CoroTypeIL (renameT s) (renameT r)
          ArrayTypeIL    t            -> do liftM ArrayTypeIL (renameT t)
          PtrTypeIL      t            -> do liftM PtrTypeIL   (renameT t)
          FnTypeIL       ts r _cc _pf -> do ts' <- mapM renameT ts
                                            r'  <- renameT r
                                            return $ FnTypeIL ts' r' _cc _pf
          RefinedTypeIL v e args      -> do v'    <- qv v
                                            e'    <- renameKN e
                                            args' <- mapM qi args
                                            return $ RefinedTypeIL v' e' args'
          ForAllIL      ktvs rho      -> do liftM (ForAllIL ktvs) (renameT rho)
          TyVarIL        {}           -> do return $ typ

    renameV :: TypedId TypeIL -> Renamed (TypedId TypeIL)
    renameV (TypedId ty id@(GlobalSymbol t)) = do
        -- We want to rename any locally-bound functions that might have
        -- been duplicated by monomorphization.
        if T.pack "<anon_fn"  `T.isInfixOf` t ||
           T.pack ".anon."    `T.isInfixOf` t ||
           T.pack ".kn.thunk" `T.isPrefixOf` t
          then do state <- get
                  case Map.lookup id (renameMap state) of
                    Nothing  -> do id' <- renameI id
                                   ty' <- renameT ty
                                   return (TypedId ty' id' )
                    Just _u' -> error "can't rename a global variable twice!"
          else do ty' <- renameT ty
                  return $ TypedId ty' id

    renameV     (TypedId ty id) = do
      state <- get
      case Map.lookup id (renameMap state) of
        Nothing  -> do id' <- renameI id
                       ty' <- renameT ty
                       return (TypedId ty' id' )
        Just _u' -> error $ "KNUtil.hs: can't rename a variable twice! " ++ show id

    renameI id@(GlobalSymbol t) = do u' <- fresh
                                     let id' = GlobalSymbol $ t `T.append` T.pack (show u')
                                     remap id id'
                                     return id'
    renameI id@(Ident s _)      = do u' <- fresh
                                     let id' = Ident s u'
                                     remap id id'
                                     return id'
    fresh :: Renamed Uniq
    fresh = do uref <- lift (gets ccUniqRef) ; mutIORef uref (+1)

    mutIORef :: IORef a -> (a -> a) -> Renamed a
    mutIORef r f = liftIO $ modIORef' r f >> readIORef r

    remap id id' = do state <- get
                      put state { renameMap = Map.insert id id' (renameMap state) }

    -- Updates a usage of a variable
    qv :: TypedId TypeIL -> Renamed (TypedId TypeIL)
    qv (TypedId t i) = do i' <- qi i
                          t' <- renameT t
                          return $ TypedId t' i'

    -- Updates a usage of an identifier
    qi v = do state <- get
              case Map.lookup v (renameMap state) of
                Just v' -> return v'
                Nothing -> return v

    qt = renameT

    renameFn :: Fn r (KNExpr' r2 TypeIL) TypeIL -> Renamed (Fn r (KNExpr' r2 TypeIL) TypeIL)
    renameFn (Fn v vs body isrec rng) = do
       (v' : vs') <- mapM renameV (v:vs)
       body' <- renameKN body
       return (Fn v' vs' body' isrec rng)

    renameArrayIndex (ArrayIndex v1 v2 rng s) =
      mapM qv [v1,v2] >>= \[v1' , v2' ] -> return $ ArrayIndex v1' v2' rng s

    renameKN :: (KNExpr' r TypeIL) -> Renamed (KNExpr' r TypeIL)
    renameKN e =
      case e of
      KNLiteral       {}       -> return e
      KNKillProcess   {}       -> return e
      KNTuple         t vs a   -> do vs' <- mapM qv vs; t' <- qt t ; return $ KNTuple t' vs' a
      KNCall          t v vs   -> do (v' : vs') <- mapM qv (v:vs); t' <- qt t; return $ KNCall t' v' vs'
      KNCallPrim   sr t p vs   -> do vs' <- mapM qv vs; t' <- qt t; return $ KNCallPrim   sr t' p vs'
      KNAppCtor       t c vs   -> do vs' <- mapM qv vs; t' <- qt t; return $ KNAppCtor t' c vs'
      KNAllocArray    t v amr zi -> liftM4 KNAllocArray (qt t) (qv v) (return amr) (return zi)
      KNAlloc         t v amr  -> liftM3 KNAlloc      (qt t) (qv v) (return amr)
      KNDeref         t v      -> liftM2 KNDeref      (qt t) (qv v)
      KNStore         t v1 v2  -> liftM3 KNStore      (qt t) (qv v1) (qv v2)
      KNArrayRead     t ai     -> liftM2 KNArrayRead  (qt t) (renameArrayIndex ai)
      KNArrayPoke     t ai v   -> liftM3 KNArrayPoke  (qt t) (renameArrayIndex ai) (qv v)
      KNArrayLit    t arr vals -> liftM3 KNArrayLit   (qt t) (qv arr) (mapRightM qv vals)
      KNVar                  v -> liftM  KNVar                  (qv v)
      KNCase          t v arms -> liftM3 KNCase (qt t) (qv v) (mapM renameCaseArm arms)
      KNIf            t v e1 e2-> do [ethen, eelse] <- mapM renameKN [e1,e2]
                                     v' <- qv v
                                     t' <- qt t
                                     return $ KNIf         t' v' ethen eelse
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
      KNTyApp t v argtys       -> liftM3 KNTyApp (qt t) (qv v) (return argtys)
      KNCompiles r t e         -> liftM2 (KNCompiles r) (qt t) (renameKN e)
      KNInlined t0 tb tn old new -> do new' <- renameKN new
                                       return $ KNInlined t0 tb tn old new'
      KNNotInlined x e -> do renameKN e >>= return . (KNNotInlined x)

    renameCaseArm (CaseArm pat expr guard vs rng) = do
        pat'   <- renamePattern pat
        vs'    <- mapM qv vs
        expr'  <-           renameKN expr
        guard' <- liftMaybe renameKN guard
        return (CaseArm pat' expr' guard' vs' rng)

    renamePatternAtom pattern = do
     case pattern of
       P_Wildcard {}          -> return pattern
       P_Bool     {}          -> return pattern
       P_Int      {}          -> return pattern
       P_Variable rng v       -> liftM (P_Variable rng) (renameV v)

    renamePattern pattern = do
     let mp = mapM renamePattern
     case pattern of
       PR_Atom     atom             -> renamePatternAtom atom >>= \atom' -> return $ PR_Atom atom'
       PR_Ctor     rng t pats ctor  -> mp pats >>= \pats' -> return $ PR_Ctor  rng t pats' ctor
       PR_Tuple    rng t pats       -> mp pats >>= \pats' -> return $ PR_Tuple rng t pats'


data RenameState = RenameState { renameMap  :: Map Ident Ident }
type Renamed = StateT RenameState Compiled

--------------------------------------------------------------------


-- ||||||||||||||||||||||||| Boilerplate ||||||||||||||||||||||||{{{

newtype KNCompilesResult = KNCompilesResult (IORef Bool)
instance Show KNCompilesResult where show _ = ""

deriving instance (Show ty, Show rs) => Show (KNExpr' rs ty) -- used elsewhere...

instance (Show t, Show rs) => AExpr (KNExpr' rs t) where
    freeIdents e = case e of
        KNLetVal   id  b   e -> freeIdents b ++ (freeIdents e `butnot` [id])
        KNLetRec   ids xps e -> (concatMap freeIdents xps ++ freeIdents e)
                                                                   `butnot` ids
        KNLetFuns  ids fns e -> (concatMap freeIdents fns ++ freeIdents e)
                                                                   `butnot` ids
        KNCase  _t v arms    -> [tidIdent v] ++ concatMap caseArmFreeIds arms
        KNVar      v         -> [tidIdent v]
        KNInlined _t0 _to _tn _old new   -> freeIdents new
        _                    -> concatMap freeIdents (childrenOf e)

-- This is necessary due to transformations of AIIf and nestedLets
-- introducing new bindings, which requires synthesizing a type.
typeKN :: KNExpr' rs ty -> ty
typeKN expr =
  case expr of
    KNLiteral       t _      -> t
    KNTuple         t _  _   -> t
    KNKillProcess   t _      -> t
    KNCall          t _ _    -> t
    KNCallPrim    _ t _ _    -> t
    KNAppCtor       t _ _    -> t
    KNAllocArray    t _ _ _  -> t
    KNIf            t _ _ _  -> t
    KNAlloc         t _ _rgn -> t
    KNDeref         t _      -> t
    KNStore         t _ _    -> t
    KNArrayRead     t _      -> t
    KNArrayPoke     t _ _    -> t
    KNArrayLit      t _ _    -> t
    KNCase          t _ _    -> t
    KNLetVal        _ _ e    -> typeKN e
    KNLetRec        _ _ e    -> typeKN e
    KNLetFuns       _ _ e    -> typeKN e
    KNVar                  v -> tidType v
    KNTyApp overallType _tm _tyArgs -> overallType
    KNCompiles _ t _           -> t
    KNInlined _t0 _ _ _ new -> typeKN new
    KNNotInlined _ e -> typeKN e

-- This instance is primarily needed as a prereq for KNExpr to be an AExpr,
-- which ((childrenOf)) is needed in ILExpr for closedNamesOfKnFn.
instance (Show ty, Show rs) => Structured (KNExpr' rs ty) where
    textOf e _width =
        case e of
            KNLiteral _  (LitText  _) -> text $ "KNString    "
            KNLiteral _  (LitBool  b) -> text $ "KNBool      " ++ (show b)
            KNLiteral ty (LitInt int) -> text $ "KNInt       " ++ (litIntText int) ++ " :: " ++ show ty
            KNLiteral ty (LitFloat f) -> text $ "KNFloat     " ++ (litFloatText f) ++ " :: " ++ show ty
            KNLiteral _ty (LitByteArray bs) -> text "KNBytes     " <> text "b" <> text (show bs)
            KNCall     t _ _    -> text $ "KNCall :: " ++ show t
            KNCallPrim _ t p  _ -> text $ "KNCallPrim  " ++ (show p) ++ " :: " ++ show t
            KNAppCtor  t cid  _ -> text $ "KNAppCtor   " ++ (show cid) ++ " :: " ++ show t
            KNLetVal   x b    _ -> text $ "KNLetVal    " ++ (show x) ++ " :: " ++ (show $ typeKN b) ++ " = ... in ... "
            KNLetRec   _ _    _ -> text $ "KNLetRec    "
            KNLetFuns ids fns _ -> text $ "KNLetFuns   " ++ (show $ zip ids (map fnVar fns))
            KNIf      t  _ _ _  -> text $ "KNIf        " ++ " :: " ++ show t
            KNAlloc      {}     -> text $ "KNAlloc     "
            KNDeref      {}     -> text $ "KNDeref     "
            KNStore      {}     -> text $ "KNStore     "
            KNCase _t v arms    -> text $ "KNCase      " ++ show v ++ " binding " ++ (show $ map caseArmBindings arms)
            KNAllocArray {}     -> text $ "KNAllocArray "
            KNArrayRead  t _    -> text $ "KNArrayRead " ++ " :: " ++ show t
            KNArrayPoke  {}     -> text $ "KNArrayPoke "
            KNArrayLit   {}     -> text $ "KNArrayLit  "
            KNTuple   _ vs _    -> text $ "KNTuple     (size " ++ (show $ length vs) ++ ")"
            KNVar (TypedId t (GlobalSymbol name))
                                -> text $ "KNVar(Global):   " ++ T.unpack name ++ " :: " ++ show t
            KNVar (TypedId t i) -> text $ "KNVar(Local):   " ++ show i ++ " :: " ++ show t
            KNTyApp t _e argty  -> text $ "KNTyApp     " ++ show argty ++ "] :: " ++ show t
            KNKillProcess t m   -> text $ "KNKillProcess " ++ show m ++ " :: " ++ show t
            KNCompiles _r _t _e -> text $ "KNCompiles    "
            KNInlined _t0 _to _tn old _new   -> text "KNInlined " <> text (show old)
            KNNotInlined _ e -> text "KNNotInlined " <> text (show e)
    childrenOf expr =
        let var v = KNVar v in
        case expr of
            KNLiteral {}            -> []
            KNKillProcess {}        -> []
            KNTuple   _ vs _        -> map var vs
            KNCase _ e arms         -> (var e):(concatMap caseArmExprs arms)
            KNLetFuns _ids fns e    -> map fnBody fns ++ [e]
            KNLetVal _x b  e        -> [b, e]
            KNLetRec _x bs e        -> bs ++ [e]
            KNCall     _t  v vs     -> [var v] ++ [var v | v <- vs]
            KNCallPrim _sr _t _v vs ->            [var v | v <- vs]
            KNAppCtor  _t _c vs     ->            [var v | v <- vs]
            KNIf       _t v b c     -> [var v, b, c]
            KNAlloc _ v _rgn        -> [var v]
            KNAllocArray _ v _ _    -> [var v]
            KNDeref      _ v        -> [var v]
            KNStore      _ v w      -> [var v, var w]
            KNArrayRead _t ari      -> map var $ childrenOfArrayIndex ari
            KNArrayPoke _t ari i    -> map var $ childrenOfArrayIndex ari ++ [i]
            KNArrayLit  _t arr vals -> [var arr] ++ [var v | Right v <- vals] -- TODO should reconstruct exprs for literals
            KNVar _                 -> []
            KNTyApp _t v _argty     -> [var v]
            KNCompiles _ _ e        -> [e]
            KNInlined _t0 _to _tn _old new      -> [new]
            KNNotInlined _ e -> [e]


knSize :: KNExpr' r t -> (Int, Int) -- toplevel, cumulative
knSize expr = go expr (0, 0) where
  go expr (t, a) = let ta = let v = knSizeHead expr in (t + v, a + v) in
                   case expr of
    KNIf          _ _ e1 e2    -> go e2 (go e1 ta)
    KNCase        _ _ arms     -> foldl' (\ta e -> go e ta) ta (concatMap caseArmExprs arms)
    KNLetVal      _   e1 e2    -> go e2 (go e1 (t, a))
    KNLetRec     _ es b        -> foldl' (\ta e -> go e ta) (go b ta) es
    KNLetFuns    _ fns b       -> let n = length fns in
                                  let ta' @ (t', _ ) = go b ta in
                                  let (_, bodies) = foldl' (\ta fn -> go (fnBody fn) ta) ta' fns in
                                  (t' + n, n + bodies)
    KNInlined _t0 _to _tn _old new -> go new (t, a)
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
    KNCase        {} -> 2 -- TODO might be cheaper for let-style cases.

    KNAppCtor     {} -> 3 -- rather like a KNTuple, plus one store for the tag.
    KNInlined _t0 _ _ _ new  -> knSizeHead new
    KNNotInlined _ e -> knSizeHead e
    KNArrayLit _ty _arr vals -> 2 + length vals
    KNCompiles    {} -> 0 -- Becomes a boolean literal
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

-- ||||||||||||||||||||||||| Pretty-printing ||||||||||||||||||||{{{
renderKN m put = if put then putDoc (pretty m) >>= (return . Left)
                        else return . Right $ show (pretty m)

renderKNF :: FnExprIL -> String
renderKNF m = show (pretty m)

showTyped :: Pretty t => Doc -> t -> Doc
showTyped d t = parens (parens d <+> text "::" <+> pretty t)

showUnTyped d _ = d

comment d = text "/*" <+> d <+> text "*/"

instance Pretty TypeIL where
  pretty t = text (show t)

instance Pretty AllocMemRegion where
  pretty rgn = text (show rgn)

instance Pretty t => Pretty (ArrayIndex (TypedId t)) where
  pretty (ArrayIndex b i _rng safety) =
    prettyId b <> brackets (prettyId i) <+> comment (text $ show safety) <+> pretty (tidType b)

-- (<//>) ?vs? align (x <$> y)

kwd  s = dullblue  (text s)
lkwd s = dullwhite (text s)
end    = lkwd "end"

instance (Pretty t, Pretty rs, Pretty rs2) => Pretty (Fn rs (KNExpr' rs2 t) t) where
  pretty fn = group (lbrace <+> (hsep (map (\v -> pretty v <+> text "=>") (fnVars fn)))
                    <$> indent 4 (pretty (fnBody fn))
                    <$> rbrace) <+> pretty (fnVar fn)
                                <+> text "(rec?:" <+> pretty (fnIsRec fn) <+> text ")"
                                <+> text "// :" <+> pretty (tidType $ fnVar fn)

instance (Pretty body, Pretty t) => Pretty (ModuleIL body t) where
  pretty m = text "// begin decls"
            <$> vcat [showTyped (text s) t | (s, t) <- moduleILdecls m]
            <$> text "// end decls"
            <$> text "// begin datatypes"
            <$> vsep (map pretty $ moduleILdataTypes m)
            <$> text "// end datatypes"
            <$> text "// begin prim types"
            <$> empty
            <$> text "// end prim types"
            <$> text "// begin functions"
            <$> pretty (moduleILbody m)
            <$> text "// end functions"

prettyId (TypedId _ i) = text (show i)

instance Pretty TypeFormal where
  pretty (TypeFormal name _sr kind) =
    text name <+> text ":" <+> pretty kind

instance Pretty t => Pretty (DataType t) where
  pretty dt =
    text "type case" <+> pretty (dataTypeName dt) <+>
         hsep (map (parens . pretty) (dataTypeTyFormals dt))
     <$> indent 2 (vsep (map prettyDataTypeCtor (dataTypeCtors dt)))
     <$> text ";"
     <$> empty

prettyDataTypeCtor dc =
  text "of" <+> text "$" <> text (T.unpack $ dataCtorName dc)
                        <+> hsep (map pretty (dataCtorTypes dc))
                        <+> text "// repr:" <+> text (show (dataCtorRepr dc))

pr YesTail = "(tail)"
pr NotTail = "(non-tail)"

instance Pretty RecStatus where pretty rs = text $ show rs

desc (t0, tb, tn) = text "t_opnd=" <> pretty t0 <> text "; t_before="<>pretty tb<>text "; t_after="<>pretty tn<>text "; t_elapsed="<>pretty (tn - tb)

instance (Pretty ty, Pretty rs) => Pretty (KNExpr' rs ty) where
  pretty e =
        case e of
            KNNotInlined (msg,(why,at_effort,mb_cost)) e ->
                dullred (text "notinlined") <+> dquotes (pretty msg) <+> parens (pretty why) <+> text "@" <> pretty at_effort
                   <+> case mb_cost of
                          Nothing -> empty
                          Just cost -> text "at cost" <+> pretty cost
                   <$>  pretty e
            KNInlined t0 tb tn old new -> dullgreen (text "inlined") <+> dullwhite (pretty old) <+> text "//" <+> desc (t0, tb, tn)
                                   <$> indent 1 (pretty new)
            KNVar (TypedId _ (GlobalSymbol name))
                                -> (text $ "G:" ++ T.unpack name)
                       --showTyped (text $ "G:" ++ T.unpack name) t
            KNVar (TypedId t i) -> prettyId (TypedId t i)
            KNTyApp t e argtys  -> showTyped (pretty e <> text ":[" <> hsep (punctuate comma (map pretty argtys)) <> text "]") t
            KNKillProcess t m   -> text ("KNKillProcess " ++ show m ++ " :: ") <> pretty t
            KNLiteral t lit     -> showTyped (pretty lit) t
            KNCall     t v [] -> showTyped (prettyId v <+> text "!") t
            KNCall     t v vs -> showTyped (prettyId v <+> hsep (map pretty vs)) t
            KNCallPrim _ t p vs -> showUnTyped (text "prim" <+> pretty p <+> hsep (map prettyId vs)) t
            KNAppCtor  t cid  vs-> showUnTyped (text "~" <> parens (text (show cid)) <> hsep (map prettyId vs)) t
            KNLetVal   x b    k -> lkwd "let"
                                      <+> fill 8 (text (show x))
                                      <+> text "="
                                      <+> (indent 0 $ pretty b) <+> lkwd "in"
                                   <$> pretty k

            KNLetFuns ids fns k -> pretty k
                                   <$> indent 1 (lkwd "wherefuns")
                                   <$> indent 2 (vcat [text (show id) <+> text "="
                                                                      <+> pretty fn
                                                      | (id, fn) <- zip ids fns
                                                      ])
                                   -- <$> indent 2 end
                                   {-
            KNLetFuns ids fns k -> text "letfuns"
                                   <$> indent 2 (vcat [text (show id) <+> text "="
                                                                      <+> pretty fn
                                                      | (id, fn) <- zip ids fns
                                                      ])
                                   <$> lkwd "in"
                                   <$> pretty k
                                   <$> end
                                   -}
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
            KNAlloc _ v rgn     -> text "(ref" <+> prettyId v <+> comment (pretty rgn) <> text ")"
            KNDeref _ v         -> prettyId v <> text "^"
            KNStore _ v1 v2     -> text "store" <+> prettyId v1 <+> text "to" <+> prettyId v2
            KNCase _t v bnds    -> align $
                                       kwd "case" <+> pretty v <+> text "::" <+> pretty (tidType v)
                                       <$> indent 2 (vcat [ kwd "of" <+> fill 20 (pretty pat)
                                                                     <+> (case guard of
                                                                            Nothing -> empty
                                                                            Just g  -> text "if" <+> pretty g)
                                                                     <+> text "->" <+> pretty expr
                                                          | (CaseArm pat expr guard _ _) <- bnds
                                                          ])
                                       <$> end
            KNAllocArray {}     -> text $ "KNAllocArray "
            KNArrayRead  t ai   -> pretty ai <+> pretty t
            KNArrayPoke  t ai v -> prettyId v <+> text ">^" <+> pretty ai <+> pretty t
            KNArrayLit   _t _arr _vals -> text "<...array literal...>"
            KNTuple      _ vs _ -> parens (hsep $ punctuate comma (map pretty vs))
            KNCompiles _r _t e  -> parens (text "__COMPILES__" <+> pretty e)

instance Pretty FoldStatus where
    pretty (FoldTooBig      size) = text "too big, size=" <> pretty size
    pretty (FoldSize sizecounter) = text "size    limit hit" <+> pretty sizecounter
    pretty (FoldEffort       doc) = text "effort  limit hit" <+> doc
    pretty FoldOuterPending       = text "outer pending hit"
    pretty FoldInnerPending       = text "inner pending hit"
    pretty FoldRecursive          = text "recursiveness    "
    pretty FoldCallSiteOptOut     = text "call site opt-out"
    pretty FoldNoBinding          = text "no def for callee"

instance Pretty SizeCounter where
  pretty sc = text $ show sc

knSubst :: Map Ident Ident -> KNExpr' r t -> KNExpr' r t
knSubst m expr =
  let qv (TypedId t id) = case Map.lookup id m of Nothing  -> TypedId t id
                                                  Just id' -> TypedId t id'
      qCaseArm (CaseArm pat e guard vs rng) =
          CaseArm pat (knSubst m e) (fmap (knSubst m) guard) (map qv vs) rng
  in
  case expr of
      KNLiteral       {}       -> expr
      KNKillProcess   {}       -> expr
      KNTuple         t vs a   -> KNTuple t (map qv vs) a
      KNCall          t v vs   -> KNCall t (qv v) (map qv vs)
      KNCallPrim   sr t p vs   -> KNCallPrim   sr t p (map qv vs)
      KNAppCtor       t c vs   -> KNAppCtor       t c (map qv vs)
      KNAllocArray    t v amr zi -> KNAllocArray    t (qv v) amr zi
      KNAlloc         t v amr  -> KNAlloc         t (qv v) amr
      KNDeref         t v      -> KNDeref         t (qv v)
      KNStore         t v1 v2  -> KNStore         t (qv v1) (qv v2)
      KNArrayRead     t ai     -> KNArrayRead     t (mapArrayIndex qv ai)
      KNArrayPoke     t ai v   -> KNArrayPoke     t (mapArrayIndex qv ai) (qv v)
      KNArrayLit    t arr vals -> KNArrayLit      t (qv arr) (mapRight qv vals)
      KNVar                  v -> KNVar                  (qv v)
      KNCase          t v arms -> KNCase       t (qv v) (map qCaseArm arms)
      KNIf            t v e1 e2-> KNIf t (qv v) (knSubst m e1) (knSubst m e2)
      KNLetVal       id e   b  -> KNLetVal id (knSubst m e) (knSubst m  b)
      KNLetRec     ids exprs e -> KNLetRec ids (map (knSubst m) exprs) (knSubst m e)
      KNLetFuns   _ids _fns _b -> error "knSubst not yet implemented for KNLetFuns"
      KNTyApp t v argtys       -> KNTyApp t (qv v) argtys
      KNCompiles r t e         -> KNCompiles r t (knSubst m e)
      KNInlined t0 tb tn old new -> KNInlined t0 tb tn old (knSubst m new)
      KNNotInlined x e -> KNNotInlined x (knSubst m e)

mapArrayIndex f (ArrayIndex v1 v2 rng s) =
  let v1' = f v1
      v2' = f v2 in ArrayIndex v1' v2' rng s
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||



type RhoIL = TypeIL
data TypeIL =
           PrimIntIL       IntSizeBits
         | TyConIL         DataTypeName
         | TyAppIL         TypeIL [TypeIL]
         | TupleTypeIL     Kind [TypeIL]
         | FnTypeIL        { fnTypeILDomain :: [TypeIL]
                           , fnTypeILRange  :: TypeIL
                           , fnTypeILCallConv :: CallConv
                           , fnTypeILProcOrFunc :: ProcOrFunc }
         | CoroTypeIL      TypeIL  TypeIL
         | ForAllIL        [(TyVar, Kind)] RhoIL
         | TyVarIL           TyVar  Kind
         | ArrayTypeIL     TypeIL
         | PtrTypeIL       TypeIL
         | RefinedTypeIL   (TypedId TypeIL) (KNExpr' () TypeIL) [Ident]

type AIVar = TypedId TypeIL


instance Show TypeIL where
    show x = case x of
        TyConIL nm        -> nm
        TyAppIL con types -> "(TyAppIL " ++ (show con)
                                      ++ joinWith " " ("":map show types) ++ ")"
        PrimIntIL size       -> "(PrimIntIL " ++ show size ++ ")"
        TupleTypeIL KindAnySizeType  typs -> "#(" ++ joinWith ", " (map show typs) ++ ")"
        TupleTypeIL _                typs ->  "(" ++ joinWith ", " (map show typs) ++ ")"
        FnTypeIL   s t cc cs -> "(" ++ show s ++ " =" ++ briefCC cc ++ "> " ++ show t ++ " @{" ++ show cs ++ "})"
        CoroTypeIL s t       -> "(Coro " ++ show s ++ " " ++ show t ++ ")"
        ForAllIL ktvs rho    -> "(ForAll " ++ show ktvs ++ ". " ++ show rho ++ ")"
        TyVarIL     tv kind  -> show tv ++ ":" ++ show kind
        ArrayTypeIL ty       -> "(Array " ++ show ty ++ ")"
        PtrTypeIL   ty       -> "(Ptr " ++ show ty ++ ")"
        RefinedTypeIL v e _  -> "(Refined " ++ show (tidIdent v) ++ "::" ++ show (tidType v) ++ " ;; " ++ show e ++ ")"

instance Structured TypeIL where
    textOf e _width =
        case e of
            TyConIL nam        -> text $ nam
            TyAppIL con _types -> text $ "TyAppIL " ++ show con
            PrimIntIL     size    -> text $ "PrimIntIL " ++ show size
            TupleTypeIL   {}      -> text $ "TupleTypeIL"
            FnTypeIL      {}      -> text $ "FnTypeIL"
            CoroTypeIL    {}      -> text $ "CoroTypeIL"
            ForAllIL ktvs _rho    -> text $ "ForAllIL " ++ show ktvs
            TyVarIL       {}      -> text $ "TyVarIL "
            ArrayTypeIL   {}      -> text $ "ArrayTypeIL"
            PtrTypeIL     {}      -> text $ "PtrTypeIL"
            RefinedTypeIL v _e _  -> text $ "RefinedTypeIL " ++ show v

    childrenOf e =
        case e of
            TyConIL {}          -> []
            TyAppIL con types  -> con:types
            PrimIntIL       {}     -> []
            TupleTypeIL _bx types  -> types
            FnTypeIL  ss t _cc _cs -> ss++[t]
            CoroTypeIL s t         -> [s,t]
            ForAllIL  _ktvs rho    -> [rho]
            TyVarIL        _tv _   -> []
            ArrayTypeIL     ty     -> [ty]
            PtrTypeIL       ty     -> [ty]
            RefinedTypeIL   v  _ _ -> [tidType v]

instance Kinded TypeIL where
  kindOf x = case x of
    PrimIntIL   {}       -> KindAnySizeType
    TyConIL "Float64"    -> KindAnySizeType
    TyConIL _            -> KindPointerSized
    TyAppIL con _        -> kindOf con
    TyVarIL   _ kind     -> kind
    TupleTypeIL kind _   -> kind
    FnTypeIL    {}       -> KindPointerSized
    CoroTypeIL  {}       -> KindPointerSized
    ForAllIL _ktvs rho   -> kindOf rho
    ArrayTypeIL {}       -> KindPointerSized
    PtrTypeIL   {}       -> KindPointerSized
    RefinedTypeIL v _ _  -> kindOf (tidType v)

unitTypeIL = TupleTypeIL KindPointerSized []

boolTypeIL = PrimIntIL I1
stringTypeIL = TyAppIL (TyConIL "Text") []



-- Since datatypes are recursively defined, we must be careful when lifting
-- them. In particular, ilOf (TyConAppAST ...) calls ctxLookupDatatype,
-- and lifts the data type using ilOf, which in turn gets called on the types
-- of the data constructors, which can include TyConApps putting us in a loop!

-----------------------------------------------------------------------

pointedToType t = case t of
    PtrTypeIL y -> y
    _ -> error $ "TypeIL.hs:pointedToType\n"
              ++ "Expected type to be a pointer, but had " ++ show t

pointedToTypeOfVar v = case v of
    TypedId (PtrTypeIL t) _ -> t
    _ -> error $ "TypeIL.hs:pointedToTypeOfVar\n"
              ++ "Expected variable to be a pointer, but had " ++ show v
-----------------------------------------------------------------------

fnName f = identPrefix (tidIdent $ fnVar f)

