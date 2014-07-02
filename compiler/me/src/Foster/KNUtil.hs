{-# LANGUAGE StandaloneDeriving, BangPatterns #-}
-----------------------------------------------------------------------------
-- Copyright (c) 2013 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.KNUtil where

import Foster.Base

import Foster.AnnExprIL(TypeIL(..))
import Foster.Kind

import Text.PrettyPrint.ANSI.Leijen

import Data.List(foldl')
import Data.Map(Map)
import qualified Data.Map as Map(insert, lookup, empty)
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
        -- Creation of bindings
        | KNCase        ty (TypedId ty) [CaseArm PatternRepr (KNExpr' r ty) ty]
        | KNLetVal      Ident        (KNExpr' r ty)     (KNExpr' r ty)
        | KNLetRec     [Ident]       [KNExpr' r ty]     (KNExpr' r ty)
        | KNLetFuns    [Ident] [Fn r (KNExpr' r ty) ty] (KNExpr' r ty)
        -- Use of bindings
        | KNVar         (TypedId ty)
        | KNCallPrim    ty (FosterPrim ty)    [TypedId ty]
        | KNCall        ty (TypedId ty)       [TypedId ty]
        | KNAppCtor     ty (CtorId, CtorRepr) [TypedId ty]
        -- Mutable ref cells
        | KNAlloc       ty (TypedId ty) AllocMemRegion
        | KNDeref       ty (TypedId ty)
        | KNStore       ty (TypedId ty) (TypedId ty)
        -- Array operations
        | KNAllocArray  ty (TypedId ty)
        | KNArrayRead   ty (ArrayIndex (TypedId ty))
        | KNArrayPoke   ty (ArrayIndex (TypedId ty)) (TypedId ty)
        | KNArrayLit    ty (TypedId ty) [Either Literal (TypedId ty)]
        | KNTyApp       ty (TypedId ty) [ty]
        | KNInlined     Int Int Int (KNExpr' r ty) (KNExpr' r ty) -- old, new
                     --          ^ "after" time of inlining new
                     --      ^ "before" time of inlining new
                     --  ^ time of first processing opnd

-- When monmomorphizing, we use (KNTyApp t v [])
-- to represent a bitcast to type t.

type KNExpr     = KNExpr' () TypeIL
type KNExprFlat = KNExpr' () TypeIL

type FnExprIL = Fn () KNExpr TypeIL

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
    renameV tid@(TypedId ty id@(GlobalSymbol t)) = do
        -- We want to rename any locally-bound functions that might have
        -- been duplicated by monomorphization.
        if T.pack "<anon_fn" `T.isInfixOf` t ||
           T.pack ".kn.thunk" `T.isPrefixOf` t
          then do state <- get
                  case Map.lookup id (renameMap state) of
                    Nothing  -> do id' <- renameI id
                                   return (TypedId ty id' )
                    Just _u' -> error "can't rename a global variable twice!"
          else return tid

    renameV     (TypedId t id) = do
      state <- get
      case Map.lookup id (renameMap state) of
        Nothing  -> do id' <- renameI id
                       return (TypedId t id' )
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
    fresh = do uref <- gets renameUniq ; mutIORef uref (+1)

    mutIORef :: IORef a -> (a -> a) -> Renamed a
    mutIORef r f = liftIO $ modIORef' r f >> readIORef r

    remap id id' = do state <- get
                      put state { renameMap = Map.insert id id' (renameMap state) }

    qv :: TypedId t -> Renamed (TypedId t)
    qv (TypedId t i) = do i' <- qi i ; return $ TypedId t i'

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
      KNCall          t v vs   -> mapM qv (v:vs) >>= \(v':vs') -> return $ KNCall t v' vs'
      KNCallPrim      t p vs   -> liftM  (KNCallPrim      t p) (mapM qv vs)
      KNAppCtor       t c vs   -> liftM  (KNAppCtor       t c) (mapM qv vs)
      KNAllocArray    t v      -> liftM  (KNAllocArray    t) (qv v)
      KNAlloc         t v _rgn -> liftM  (\v' -> KNAlloc  t v' _rgn) (qv v)
      KNDeref         t v      -> liftM  (KNDeref         t) (qv v)
      KNStore         t v1 v2  -> liftM2 (KNStore         t) (qv v1) (qv v2)
      KNArrayRead     t ai     -> liftM  (KNArrayRead     t) (renameArrayIndex ai)
      KNArrayPoke     t ai v   -> liftM2 (KNArrayPoke     t) (renameArrayIndex ai) (qv v)
      KNArrayLit    t arr vals -> liftM2 (KNArrayLit      t) (qv arr) (mapRightM qv vals)
      KNVar                  v -> liftM  KNVar                  (qv v)
      KNCase          t v arms -> do arms' <- mapM renameCaseArm arms
                                     v'    <- qv v
                                     return $ KNCase       t v' arms'
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
      KNInlined t0 tb tn old new -> do renameKN new >>= return . (KNInlined t0 tb tn old)

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


data RenameState = RenameState {
                       renameUniq :: IORef Uniq
                     , renameMap  :: Map Ident Ident
                   }
type Renamed = StateT RenameState IO

--------------------------------------------------------------------


-- ||||||||||||||||||||||||| Boilerplate ||||||||||||||||||||||||{{{

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
    KNCallPrim      t _ _    -> t
    KNAppCtor       t _ _    -> t
    KNAllocArray    t _      -> t
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
    KNInlined _t0 _ _ _ new -> typeKN new

-- This instance is primarily needed as a prereq for KNExpr to be an AExpr,
-- which ((childrenOf)) is needed in ILExpr for closedNamesOfKnFn.
instance (Show ty, Show rs) => Structured (KNExpr' rs ty) where
    textOf e _width =
        case e of
            KNLiteral _  (LitText  _) -> text $ "KNString    "
            KNLiteral _  (LitBool  b) -> text $ "KNBool      " ++ (show b)
            KNLiteral ty (LitInt int) -> text $ "KNInt       " ++ (litIntText int) ++ " :: " ++ show ty
            KNLiteral ty (LitFloat f) -> text $ "KNFloat     " ++ (litFloatText f) ++ " :: " ++ show ty
            KNCall     t _ _    -> text $ "KNCall :: " ++ show t
            KNCallPrim t prim _ -> text $ "KNCallPrim  " ++ (show prim) ++ " :: " ++ show t
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
            KNInlined _t0 _to _tn old new   -> text "KNInlined " <> text (show old)
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
            KNCallPrim _t _v vs     ->            [var v | v <- vs]
            KNAppCtor  _t _c vs     ->            [var v | v <- vs]
            KNIf       _t v b c     -> [var v, b, c]
            KNAlloc _ v _rgn        -> [var v]
            KNAllocArray _ v        -> [var v]
            KNDeref      _ v        -> [var v]
            KNStore      _ v w      -> [var v, var w]
            KNArrayRead _t ari      -> map var $ childrenOfArrayIndex ari
            KNArrayPoke _t ari i    -> map var $ childrenOfArrayIndex ari ++ [i]
            KNArrayLit  _t arr vals -> [var arr] ++ [var v | Right v <- vals] -- TODO should reconstruct exprs for literals
            KNVar _                 -> []
            KNTyApp _t v _argty     -> [var v]
            KNInlined _t0 _to _tn _old new      -> [new]


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
    KNArrayLit _ty _arr vals -> 2 + length vals
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

-- ||||||||||||||||||||||||| Pretty-printing ||||||||||||||||||||{{{
renderKN m put = if put then putDoc (pretty m) >>= (return . Left)
                        else return . Right $ show (pretty m)

renderKNF :: FnExprIL -> String
renderKNF m = show (pretty m)

showTyped :: Pretty t => Doc -> t -> Doc
showTyped d t = parens (d <+> text "::" <+> pretty t)

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

instance (Pretty t, Pretty rs) => Pretty (Fn rs (KNExpr' rs t) t) where
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
  pretty (TypeFormal name kind) =
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

pr YesTail = "(tail)"
pr NotTail = "(non-tail)"

instance Pretty RecStatus where pretty rs = text $ show rs

desc (t0, tb, tn) = text "t_opnd=" <> pretty t0 <> text "; t_before="<>pretty tb<>text "; t_after="<>pretty tn<>text "; t_elapsed="<>pretty (tn - tb)

instance (Pretty ty, Pretty rs) => Pretty (KNExpr' rs ty) where
  pretty e =
        case e of
            KNInlined t0 tb tn old new -> dullgreen (text "inlined") <+> dullwhite (pretty old) <+> text "//" <+> desc (t0, tb, tn)
                                   <$> indent 1 (pretty new)
            KNVar (TypedId _ (GlobalSymbol name))
                                -> (text $ "G:" ++ T.unpack name)
                       --showTyped (text $ "G:" ++ T.unpack name) t
            KNVar (TypedId t i) -> prettyId (TypedId t i)
            KNTyApp t e argtys  -> showTyped (pretty e <> text ":[" <> hsep (punctuate comma (map pretty argtys)) <> text "]") t
            KNKillProcess t m   -> text ("KNKillProcess " ++ show m ++ " :: ") <> pretty t
            KNLiteral _ lit     -> pretty lit
            KNCall     t v [] -> showUnTyped (prettyId v <+> text "!") t
            KNCall     t v vs -> showUnTyped (prettyId v <+> hsep (map pretty vs)) t
            KNCallPrim t prim vs-> showUnTyped (text "prim" <+> pretty prim <+> hsep (map prettyId vs)) t
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

-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

