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
import Foster.PrettyAnnExpr
import Foster.Config(Compiled, CompilerContext(ccUniqRef))
import Foster.SourceRange(SourceRange)

import Prettyprinter
import Prettyprinter.Render.Terminal

import Data.Maybe(maybeToList)
import Data.List(foldl')
import Data.Set(Set)
import qualified Data.Set as Set(union, unions, fromList)
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
        | KNRecord      ty [T.Text] [TypedId ty] SourceRange
        | KNTuple       ty [TypedId ty] SourceRange
        | KNKillProcess ty T.Text
        -- Control flow
        | KNIf          ty (TypedId ty)    (KNExpr' r ty) (KNExpr' r ty)
        | KNHandler ExprAnnot ty ty (KNExpr' r ty) [CaseArm PatternRepr (KNExpr' r ty) ty] (Maybe (KNExpr' r ty)) ResumeIds
        -- Creation of bindings
        | KNCase        ty (TypedId ty) [CaseArm PatternRepr (KNExpr' r ty) ty]
        | KNLetVal      Ident        (KNExpr' r ty)     (KNExpr' r ty) (Set Ident)
        | KNLetRec     [Ident]       [KNExpr' r ty]     (KNExpr' r ty)
        | KNLetFuns    [Ident] [Fn r (KNExpr' r ty) ty] (KNExpr' r ty) SourceRange
        -- Use of bindings
        | KNVar         (TypedId ty)
        | KNCallPrim    SourceRange ty (FosterPrim ty)    [TypedId ty]
        | KNCall        ty (TypedId ty)       [TypedId ty] CallAnnot
        | KNAppCtor     ty (CtorId, CtorRepr) [TypedId ty] SourceRange
        -- Mutable ref cells
        | KNAlloc       ty (TypedId ty) AllocMemRegion SourceRange
        | KNDeref       ty (TypedId ty)
        | KNStore       ty (TypedId ty) (TypedId ty)
        -- Array operations
        | KNAllocArray  ty (TypedId ty) AllocMemRegion ZeroInit SourceRange
        | KNArrayRead   ty (ArrayIndex (TypedId ty))
        | KNArrayPoke   ty (ArrayIndex (TypedId ty)) (TypedId ty)
        | KNArrayLit    ty (TypedId ty) [Either Literal (TypedId ty)]
        -- Others
        | KNTyApp       ty (TypedId ty) [ty]
        | KNCompiles    KNCompilesResult ty (KNExpr' r ty)
        | KNRelocDoms   [Ident] (KNExpr' r ty)

-- {{{ Inlining-related definitions
data FoldStatus = FoldTooBig Int -- size (stopped before inlining)
                | FoldEffort (Doc AnsiStyle)
                | FoldSize SizeCounter -- (stopped while inlining)
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

mkKNLetVal id e b = KNLetVal id e b (freeIdents b)

--showFnStructureX :: Fn r KNExpr TypeIL -> Doc
showFnStructureX (Fn fnvar args body _ _srcrange) =
  pretty fnvar <+> text "=" <+>
                     text "{" <+> hsep (map pretty args)
                 <$> indent 2 (showStructure body)
                 <$> text "}" <> line

alphaRename' :: (Show r2) => Fn r (KNExpr' r2 TypeIL) TypeIL
                -> Compiled (Fn r (KNExpr' r2 TypeIL) TypeIL)
alphaRename' fn = do
  renamed <- evalStateT (renameFn fn) (RenameState Map.empty)

  --liftIO $ do
  --    putDoc $ text "fn (IL): " <$> showFnStructureX fn
  --    putDoc $ text "renamed: " <$> showFnStructureX renamed

  return renamed
   where
    renameT :: TypeIL -> Renamed TypeIL
    renameT typ = case typ of
          PrimIntIL      {}           -> return $ typ
          TyConIL        {}           -> return $ typ
          TyAppIL     con ts          -> do liftM2 TyAppIL (renameT con) (mapM renameT ts)
          RecordTypeIL labels ts      -> do liftM (RecordTypeIL labels) (mapM renameT ts)
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
    renameV (TypedId ty id@(GlobalSymbol t _alt)) = do
        -- We want to rename any locally-bound functions that might have
        -- been duplicated by monomorphization.
        if T.pack "<anon_fn"  `T.isInfixOf` t ||
           T.pack ".anon."    `T.isInfixOf` t ||
           T.pack ".kn.thunk" `T.isPrefixOf` t ||
           T.pack ".fx.thunk" `T.isPrefixOf` t
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
        Just _u' -> error $ "KNUtil.hs: can't rename a variable twice! " ++ show (prettyIdent id)

    renameI id@(GlobalSymbol t alt) = do u' <- fresh
                                         let id' = GlobalSymbol (t `T.append` T.pack (show u')) alt
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
      KNRecord        t ls vs a -> do vs' <- mapM qv vs; t' <- qt t ; return $ KNRecord t' ls vs' a
      KNTuple         t vs a   -> do vs' <- mapM qv vs; t' <- qt t ; return $ KNTuple t' vs' a
      KNCall          t v vs ca-> do (v' : vs') <- mapM qv (v:vs); t' <- qt t; return $ KNCall t' v' vs' ca
      KNCallPrim   sr t p vs   -> do vs' <- mapM qv vs; t' <- qt t; return $ KNCallPrim   sr t' p vs'
      KNAppCtor       t c vs sr-> do vs' <- mapM qv vs; t' <- qt t; return $ KNAppCtor t' c vs' sr
      KNAllocArray    t v amr zi sr -> liftM2 (\t' v' -> KNAllocArray t' v' amr zi sr) (qt t) (qv v)
      KNAlloc         t v amr    sr -> liftM4 KNAlloc      (qt t) (qv v) (return amr) (return sr)
      KNDeref         t v      -> liftM2 KNDeref      (qt t) (qv v)
      KNStore         t v1 v2  -> liftM3 KNStore      (qt t) (qv v1) (qv v2)
      KNArrayRead     t ai     -> liftM2 KNArrayRead  (qt t) (renameArrayIndex ai)
      KNArrayPoke     t ai v   -> liftM3 KNArrayPoke  (qt t) (renameArrayIndex ai) (qv v)
      KNArrayLit    t arr vals -> liftM3 KNArrayLit   (qt t) (qv arr) (mapRightM qv vals)
      KNVar                  v -> liftM  KNVar                  (qv v)
      KNCase          t v arms -> liftM3 KNCase (qt t) (qv v) (mapM renameCaseArm arms)
      KNHandler annot t eff action arms mb_xform (resumeid, resumebareid) ->
                                  do resumeid' <- renameI resumeid
                                     resumebareid' <- renameI resumebareid
                                     t' <- qt t
                                     eff' <- qt eff
                                     action' <- renameKN action
                                     arms' <- mapM renameCaseArm arms
                                     mb_xform' <- liftMaybe renameKN mb_xform
                                     return $ KNHandler annot t' eff' action' arms' mb_xform' (resumeid', resumebareid')
      KNIf            t v e1 e2-> do [ethen, eelse] <- mapM renameKN [e1,e2]
                                     v' <- qv v
                                     t' <- qt t
                                     return $ KNIf         t' v' ethen eelse
      KNLetVal       id e  b _ -> do id' <- renameI id
                                     [e' , b' ] <- mapM renameKN [e, b]
                                     return $ KNLetVal id' e'  b' (freeIdents b')
      KNLetRec     ids exprs e -> do ids' <- mapM renameI ids
                                     (e' : exprs' ) <- mapM renameKN (e:exprs)
                                     return $ KNLetRec ids' exprs'  e'
      KNLetFuns    ids fns b sr -> do ids' <- mapM renameI ids
                                      fns' <- mapM renameFn fns
                                      b'   <- renameKN b
                                      return $ KNLetFuns ids' fns' b' sr
      KNRelocDoms ids e        -> liftM2 KNRelocDoms (mapM qi ids) (renameKN e)
      KNTyApp t v argtys       -> liftM3 KNTyApp (qt t) (qv v) (return argtys)
      KNCompiles r t e         -> liftM2 (KNCompiles r) (qt t) (renameKN e)

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
       PR_Or       rng t pats       -> mp pats >>= \pats' -> return $ PR_Or    rng t pats'


data RenameState = RenameState { renameMap  :: Map Ident Ident }
type Renamed = StateT RenameState Compiled

--------------------------------------------------------------------


-- ||||||||||||||||||||||||| Boilerplate ||||||||||||||||||||||||{{{

newtype KNCompilesResult = KNCompilesResult (IORef Bool)
instance Show KNCompilesResult where show _ = ""

--deriving instance (Show ty, Show rs) => Show (KNExpr' rs ty) -- used elsewhere...

instance AExpr (KNExpr' rs t) where
    freeIdents e = case e of
        KNLetVal   id  b  _e efree -> freeIdents b `Set.union` (efree `sans` [id])
        KNLetRec   ids xps e   -> (combinedFreeIdents xps `Set.union` freeIdents e) `sans` ids
        KNLetFuns  ids fns e _ -> (combinedFreeIdents fns `Set.union` freeIdents e) `sans` ids
        KNCase  _t v arms    -> Set.fromList [tidIdent v] `Set.union` Set.unions (map caseArmFreeIds arms)
        KNVar      v         -> Set.fromList [tidIdent v]
        _                    -> combinedFreeIdents (childrenOf e)

-- This is necessary due to transformations of AIIf and nestedLets
-- introducing new bindings, which requires synthesizing a type.
typeKN :: KNExpr' rs ty -> ty
typeKN expr =
  case expr of
    KNLiteral       t _      -> t
    KNRecord        t _ _  _ -> t
    KNTuple         t _  _   -> t
    KNKillProcess   t _      -> t
    KNCall          t _ _ _  -> t
    KNCallPrim    _ t _ _    -> t
    KNAppCtor       t _ _ _  -> t
    KNAllocArray    t _ _ _ _-> t
    KNIf            t _ _ _  -> t
    KNAlloc         t _ _rgn _ -> t
    KNDeref         t _      -> t
    KNStore         t _ _    -> t
    KNArrayRead     t _      -> t
    KNArrayPoke     t _ _    -> t
    KNArrayLit      t _ _    -> t
    KNCase          t _ _    -> t
    KNHandler _ann t _ _ _ _ _ -> t
    KNLetVal        _ _ e _  -> typeKN e
    KNLetRec        _ _ e    -> typeKN e
    KNLetFuns       _ _ e _  -> typeKN e
    KNVar                  v -> tidType v
    KNTyApp overallType _tm _tyArgs -> overallType
    KNCompiles _ t _           -> t
    KNRelocDoms _ e         -> typeKN e

-- This instance is primarily needed as a prereq for KNExpr to be an AExpr,
-- which ((childrenOf)) is needed in ILExpr for closedNamesOfKnFn.
instance (PrettyT ty, Show rs) => Summarizable (KNExpr' rs ty) where
    textOf e _width =
        case e of
            KNLiteral _  (LitText  _) -> string $ "KNString    "
            KNLiteral _  (LitBool  b) -> string $ "KNBool      " ++ (show b)
            KNLiteral ty (LitInt int) -> text "KNInt       " <> (text $ litIntText int) <> text " :: " <> prettyT ty
            KNLiteral ty (LitFloat f) -> text "KNFloat     " <> (text $ litFloatText f) <> text " :: " <> prettyT ty
            KNLiteral _ty (LitByteArray bs) -> text "KNBytes     " <> text "b" <> string (show bs)
            KNCall     t _ _ _    -> string $ "KNCall :: " ++ show (prettyT t)
            KNCallPrim _ t p  _   -> string $ "KNCallPrim  " ++ (show $ prettyT p) ++ " :: " ++ show (prettyT t)
            KNAppCtor  t cid _ _  -> string $ "KNAppCtor   " ++ (show cid) ++ " :: " ++ show (prettyT t)
            KNLetVal   x b  _ _   -> string $ "KNLetVal    " ++ (show $ prettyIdent x) ++ " :: " ++ (show $ prettyT $ typeKN b) ++ " = ... in ... "
            KNLetRec   _ _    _   -> string $ "KNLetRec    "
            KNLetFuns ids fns _ _ -> text "KNLetFuns   " <> pretty (zip ids (map (tidIdent.fnVar) fns))
            KNIf      t  _ _ _  -> string $ "KNIf        " ++ " :: " ++ show (prettyT t)
            KNAlloc      {}     -> string $ "KNAlloc     "
            KNDeref      {}     -> string $ "KNDeref     "
            KNStore      {}     -> string $ "KNStore     "
            KNCase _t v arms    -> text "KNCase      " <> prettyT v <> text " binding " <> (prettyT $ map caseArmBindings arms)
            KNHandler _ _ty _eff _ arms _mb_xform _resumeid ->
                                   text "KNHandler   " <>              text " binding " <> (prettyT $ map caseArmBindings arms)
            KNAllocArray {}     -> string $ "KNAllocArray "
            KNArrayRead  t _    -> string $ "KNArrayRead " ++ " :: " ++ show (prettyT t)
            KNArrayPoke  {}     -> string $ "KNArrayPoke "
            KNArrayLit   {}     -> string $ "KNArrayLit  "
            KNRecord     {}     -> string $ "KNRecord    "
            KNTuple   _ vs _    -> string $ "KNTuple     (size " ++ (show $ length vs) ++ ")"
            KNVar (TypedId t (GlobalSymbol name _))
                                -> text "KNVar(Global):   " <> text name <> text " :: " <> prettyT t
            KNVar (TypedId t i) -> text "KNVar(Local):   " <> prettyIdent i <> " :: " <> prettyT t
            KNTyApp t _e argty  -> text "KNTyApp     " <> prettyT argty <> text "] :: " <> prettyT t
            KNKillProcess t m   -> text "KNKillProcess " <> text m <> text " :: " <> prettyT t
            KNCompiles _r _t _e -> text "KNCompiles    "
            KNRelocDoms ids _   -> text "KNRelocDoms " <> pretty ids

instance Structured (KNExpr' rs ty) where
    childrenOf expr =
        let var v = KNVar v in
        case expr of
            KNLiteral {}            -> []
            KNKillProcess {}        -> []
            KNRecord   _ _labs vs _ -> map var vs
            KNTuple   _ vs _        -> map var vs
            KNCase _ e arms         -> (var e):(concatMap caseArmExprs arms)
            KNHandler _ _ty _eff action arms mb_xform _resumeid ->
                (maybeToList mb_xform)++(action:concatMap caseArmExprs arms)
            KNLetFuns _ids fns e _  -> map fnBody fns ++ [e]
            KNLetVal _x b  e _      -> [b, e]
            KNLetRec _x bs e        -> bs ++ [e]
            KNCall     _t  v vs _   -> [var v] ++ [var v | v <- vs]
            KNCallPrim _sr _t _v vs ->            [var v | v <- vs]
            KNAppCtor  _t _c vs _sr ->            [var v | v <- vs]
            KNIf       _t v b c     -> [var v, b, c]
            KNAlloc _ v _rgn _sr    -> [var v]
            KNAllocArray _ v _ _ _sr-> [var v]
            KNDeref      _ v        -> [var v]
            KNStore      _ v w      -> [var v, var w]
            KNArrayRead _t ari      -> map var $ childrenOfArrayIndex ari
            KNArrayPoke _t ari i    -> map var $ childrenOfArrayIndex ari ++ [i]
            KNArrayLit  _t arr vals -> [var arr] ++ [var v | Right v <- vals] -- TODO should reconstruct exprs for literals
            KNVar _                 -> []
            KNTyApp _t v _argty     -> [var v]
            KNCompiles _ _ e        -> [e]
            KNRelocDoms _ e         -> [e]


knSize :: KNExpr' r t -> (Int, Int) -- toplevel, cumulative
knSize expr = go expr (0, 0) where
  go expr (t, a) = let ta = let v = knSizeHead expr in (t + v, a + v) in
                   case expr of
    KNIf          _ _ e1 e2    -> go e2 (go e1 ta)
    KNCase        _ _ arms     -> foldl' (\ta e -> go e ta) ta (concatMap caseArmExprs arms)
    KNLetVal      _   e1 e2 _  -> go e2 (go e1 (t, a))
    KNLetRec     _ es b        -> foldl' (\ta e -> go e ta) (go b ta) es
    KNLetFuns    _ fns b _     -> let n = length fns in
                                  let ta'@(t', _ ) = go b ta in
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

    KNRecord      {} -> 2
    KNTuple       {} -> 2 -- due to allocation + stores
    KNArrayRead   {} -> 2 -- due to (potential) bounds check
    KNArrayPoke   {} -> 2 -- due to (potential) bounds check
    KNCall        {} -> 4 -- due to dyn. insn overhead, stack checks, etc
    KNCase        {} -> 2 -- TODO might be cheaper for let-style cases.
    KNHandler     {} -> 8

    KNAppCtor     {} -> 3 -- rather like a KNTuple, plus one store for the tag.
    KNRelocDoms _ e -> knSizeHead e
    KNArrayLit _ty _arr vals -> 2 + length vals
    KNCompiles    {} -> 0 -- Becomes a boolean literal
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

-- ||||||||||||||||||||||||| Pretty-printing ||||||||||||||||||||{{{
renderKN m put = if put then putDoc (prettyT m) >>= (return . Left)
                        else return . Right $ show (prettyT m)

renderKNF :: FnExprIL -> String
renderKNF m = show ((prettyT m) :: Doc AnsiStyle)

instance PrettyT TypeIL        where prettyT t  = string $ show t
instance Pretty AllocMemRegion where pretty rgn = string $ show rgn

showDecl (s, t, isForeign) =
  case isForeign of
    NotForeign -> showTyped (text s) t
    IsForeign nm ->
      if s == nm
        then text "foreign import" <+> showTyped (text s) t
        else text "foreign import" <+> text s <+> text "as" <+> text nm <+> text "::" <+> prettyT t
           
instance (PrettyT body, PrettyT t) => PrettyT (ModuleIL body t) where
  prettyT m = text "// begin decls"
            <$> vcat (map showDecl (moduleILdecls m))
            <$> text "// end decls"
            <$> text "// begin datatypes"
            <$> vsep (map prettyT $ moduleILdataTypes m)
            <$> text "// end datatypes"
            <$> text "// begin prim types"
            <$> emptyDoc
            <$> text "// end prim types"
            <$> text "// begin functions"
            <$> prettyT (moduleILbody m)
            <$> text "// end functions"

pr YesTail = "(tail)"
pr NotTail = "(non-tail)"

instance Pretty RecStatus where pretty rs = string $ show rs

--desc (t0, tb, tn) = text "t_opnd=" <> pretty t0 <> text "; t_before="<>pretty tb<>text "; t_after="<>pretty tn<>text "; t_elapsed="<>pretty (tn - tb)

instance (PrettyT ty, Pretty rs) => PrettyT (KNExpr' rs ty) where
  prettyT e =
        case e of
            KNRelocDoms ids e        -> yellow (text "<reloc-doms<" <> pretty ids <> text ">>") <$> prettyT e
            KNVar (TypedId _ (GlobalSymbol name _alt))
                                -> (string $ "G:" ++ T.unpack name)
                       --showTyped (text $ "G:" ++ T.unpack name) t
            KNVar (TypedId t i) -> prettyId (TypedId t i)
            KNTyApp t e argtys  -> showTyped (prettyT e <> text ":[" <> hsep (punctuate comma (map prettyT argtys)) <> text "]") t
            KNKillProcess t m   -> string ("KNKillProcess " ++ show m ++ " :: ") <> prettyT t
            KNLiteral t lit     -> showTyped (prettyT lit) t
            KNCall     t v [] _ -> showTyped (prettyId v <+> text "!") t
            KNCall     t v vs _ -> showTyped (prettyId v <+> hsep (map prettyT vs)) t
            KNCallPrim _ t p vs -> showUnTyped (text "prim" <+> prettyT p <+> hsep (map prettyId vs)) t
            KNAppCtor  t cid vs _sr -> showUnTyped (text "~" <> parens (pretty cid) <> hsep (map prettyId vs)) t
            KNLetVal   x b  k _ -> lkwd "let"
                                      <+> fill 8 (prettyIdent x)
                                      <+> text "="
                                      <+> (indent 0 $ prettyT b) <+> lkwd "in"
                                   <$> prettyT k
{-
            KNLetFuns ids fns k -> pretty k
                                   <$> indent 1 (lkwd "wherefuns")
                                   <$> indent 2 (vcat [text (show id) <+> text "="
                                                                      <+> pretty fn
                                                      | (id, fn) <- zip ids fns
                                                      ])
                                                      -}
                                   -- <$> indent 2 end
            KNLetFuns ids fns k _sr -> text "letfuns"
                                   <$> indent 2 (vcat [prettyIdent id <+> text "="
                                                                      <+> prettyT fn
                                                      | (id, fn) <- zip ids fns
                                                      ])
                                   <$> lkwd "in"
                                   <$> prettyT k
                                   <$> end
            KNLetRec  ids xps e -> text "rec"
                                   <$> indent 2 (vcat [prettyIdent id <+> text "="
                                                                      <+> prettyT xpr
                                                      | (id, xpr) <- zip ids xps
                                                      ])
                                   <$> lkwd "in"
                                   <$> prettyT e
                                   <$> end
            KNIf     _t v b1 b2 -> kwd "if" <+> prettyId v
                                   <$> nest 2 (kwd "then" <+> (indent 0 $ prettyT b1))
                                   <$> nest 2 (kwd "else" <+> (indent 0 $ prettyT b2))
                                   <$> end
            KNAlloc _ v rgn _sr -> text "(ref" <+> prettyId v <+> comment (pretty rgn) <> text ")"
            KNDeref _ v         -> prettyId v <> text "^"
            KNStore _ v1 v2     -> text "store" <+> prettyId v1 <+> text "to" <+> prettyId v2
            KNCase _t v bnds    -> align $
                                       kwd "case" <+> prettyT v <+> text "::" <+> prettyT (tidType v)
                                       <$> indent 2 (vcat (map prettyCaseArm bnds))
                                       <$> end
            KNHandler _annot _ty _eff action arms mb_xform _resumeid ->
              align $
                text "handler" <+> prettyT action
                <$> indent 2 (vcat (map prettyCaseArm arms))
                <$> (case mb_xform of Nothing -> emptyDoc
                                      Just xf -> kwd "as" <+> prettyT xf)
                <$> end
            KNAllocArray {}     -> text $ "KNAllocArray "
            KNArrayRead  t ai   -> prettyT ai <+> prettyT t
            KNArrayPoke  t ai v -> prettyId v <+> text ">^" <+> prettyT ai <+> prettyT t
            KNArrayLit   _t _arr _vals -> text "<...array literal...>"
            KNRecord     _ _ls vs _ -> text "Record/" <> parens (hsep $ punctuate comma (map prettyT vs))
            KNTuple      _ vs _ -> parens (hsep $ punctuate comma (map prettyT vs))
            KNCompiles _r _t e  -> parens (text "prim __COMPILES__" <+> parens (prettyT e))

prettyCaseArm (CaseArm pat expr guard _ _) =
  kwd "of"  <+> fill 20 (prettyT pat)
            <+> (case guard of
                  Nothing -> emptyDoc
                  Just g  -> text "if" <+> prettyT g)
            <+> text "->" <+> prettyT expr

instance PrettyT FoldStatus where
    prettyT (FoldTooBig      size) = text "too big, size=" <> pretty size
    prettyT (FoldSize sizecounter) = text "size    limit hit" <+> pretty sizecounter
    prettyT (FoldEffort       doc) = text "effort  limit hit" <+> doc
    prettyT FoldOuterPending       = text "outer pending hit"
    prettyT FoldInnerPending       = text "inner pending hit"
    prettyT FoldRecursive          = text "recursiveness    "
    prettyT FoldCallSiteOptOut     = text "call site opt-out"
    prettyT FoldNoBinding          = text "no def for callee"

instance Pretty SizeCounter where
  pretty sc = string $ show sc

knSubst :: Map Ident Ident -> KNExpr' r t -> KNExpr' r t
knSubst m expr =
  let qv (TypedId t id) = case Map.lookup id m of Nothing  -> TypedId t id
                                                  Just id' -> TypedId t id'
      qCaseArm (CaseArm pat e guard vs rng) =
          CaseArm pat (knSubst m e) (fmap (knSubst m) guard) (fmap qv vs) rng
  in
  case expr of
      KNLiteral       {}       -> expr
      KNKillProcess   {}       -> expr
      KNRecord        t ls vs a -> KNRecord t ls (map qv vs) a
      KNTuple         t vs a   -> KNTuple t (map qv vs) a
      KNCall          t v vs ca-> KNCall t (qv v) (map qv vs) ca
      KNCallPrim   sr t p vs   -> KNCallPrim   sr t p (map qv vs)
      KNAppCtor       t c vs sr-> KNAppCtor       t c (map qv vs) sr
      KNAllocArray    t v amr zi sr -> KNAllocArray    t (qv v) amr zi sr
      KNAlloc         t v amr    sr -> KNAlloc         t (qv v) amr    sr
      KNDeref         t v      -> KNDeref         t (qv v)
      KNStore         t v1 v2  -> KNStore         t (qv v1) (qv v2)
      KNArrayRead     t ai     -> KNArrayRead     t (mapArrayIndex qv ai)
      KNArrayPoke     t ai v   -> KNArrayPoke     t (mapArrayIndex qv ai) (qv v)
      KNArrayLit    t arr vals -> KNArrayLit      t (qv arr) (mapRight qv vals)
      KNVar                  v -> KNVar                  (qv v)
      KNCase          t v arms -> KNCase       t (qv v) (map qCaseArm arms)
      KNHandler ann t fx a arms x resumeid -> -- The resumeid can't be externally bound, thus safe from subst.
            KNHandler ann t fx (knSubst m a) (map qCaseArm arms) (fmap (knSubst m) x) resumeid
      KNIf            t v e1 e2-> KNIf t (qv v) (knSubst m e1) (knSubst m e2)
      KNLetVal       id e  b _ -> let b' = knSubst m b in KNLetVal id (knSubst m e) b' (freeIdents b')
      KNLetRec     ids exprs e -> KNLetRec ids (map (knSubst m) exprs) (knSubst m e)
      KNLetFuns   _ids _fns _b _sr -> error "knSubst not yet implemented for KNLetFuns"
      KNTyApp t v argtys       -> KNTyApp t (qv v) argtys
      KNCompiles r t e         -> KNCompiles r t (knSubst m e)
      KNRelocDoms ids e        -> KNRelocDoms ids (knSubst m e)

mapArrayIndex f (ArrayIndex v1 v2 rng s) =
  let v1' = f v1
      v2' = f v2 in ArrayIndex v1' v2' rng s
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||



type RhoIL = TypeIL
data TypeIL =
           PrimIntIL       IntSizeBits
         | TyConIL         DataTypeName
         | TyAppIL         TypeIL [TypeIL]
         | RecordTypeIL    [T.Text] [TypeIL]
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
        TyConIL nm        -> T.unpack nm
        TyAppIL con types -> "(TyAppIL " ++ (show con)
                                      ++ joinWith " " ("":map show types) ++ ")"
        PrimIntIL size       -> "(PrimIntIL " ++ show size ++ ")"
        RecordTypeIL labels typs -> "Record(" ++ joinWith ", " (map show typs) ++ ")" ++ show labels
        TupleTypeIL KindAnySizeType  typs -> "#(" ++ joinWith ", " (map show typs) ++ ")"
        TupleTypeIL _                typs ->  "(" ++ joinWith ", " (map show typs) ++ ")"
        FnTypeIL   s t cc cs -> "(" ++ show s ++ " =" ++ briefCC cc ++ "> " ++ show t ++ " /*" ++ show cs ++ "*/)"
        CoroTypeIL s t       -> "(Coro " ++ show s ++ " " ++ show t ++ ")"
        ForAllIL ktvs rho    -> "(ForAll " ++ show ktvs ++ ". " ++ show rho ++ ")"
        TyVarIL     tv kind  -> show tv ++ ":" ++ show kind
        ArrayTypeIL ty       -> "(Array " ++ show ty ++ ")"
        PtrTypeIL   ty       -> "(Ptr " ++ show ty ++ ")"
        RefinedTypeIL _v _e _  -> "(Refined...)" --"(Refined " ++ show (tidIdent v) ++ "::" ++ show (tidType v) ++ " ;; " ++ show e ++ ")"

instance Summarizable TypeIL where
    textOf e _width =
        case e of
            TyConIL nam           -> text $ nam
            TyAppIL con _types    -> string $ "TyAppIL " ++ show con
            PrimIntIL     size    -> string $ "PrimIntIL " ++ show size
            RecordTypeIL  {}      -> string $ "RecordTypeIL"
            TupleTypeIL   {}      -> string $ "TupleTypeIL"
            FnTypeIL      {}      -> string $ "FnTypeIL"
            CoroTypeIL    {}      -> string $ "CoroTypeIL"
            ForAllIL ktvs _rho    -> string $ "ForAllIL " ++ show ktvs
            TyVarIL       tv k    -> text "TyVarIL " <> pretty tv <> text " :: " <> pretty k
            ArrayTypeIL   {}      -> string $ "ArrayTypeIL"
            PtrTypeIL     {}      -> string $ "PtrTypeIL"
            RefinedTypeIL v _e _  -> string $ "RefinedTypeIL " ++ show v

instance Structured TypeIL where
    childrenOf e =
        case e of
            TyConIL {}          -> []
            TyAppIL con types  -> con:types
            PrimIntIL       {}     -> []
            RecordTypeIL _ls types -> types
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
    TyConIL "Float32"    -> KindAnySizeType
    TyConIL "effect.Empty"  -> KindEffect
    TyConIL "effect.Extend" -> KindEffect
    TyConIL _            -> KindPointerSized
    TyAppIL con _        -> kindOf con
    TyVarIL   _ kind     -> kind
    RecordTypeIL _ _     -> KindPointerSized
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

-----------------------------------------------------------------------

class CanMakeFun t where
    mkFunType   :: [t] -> t -> t
