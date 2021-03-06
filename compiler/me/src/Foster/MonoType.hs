{-# LANGUAGE Strict, StandaloneDeriving #-}
-----------------------------------------------------------------------------
-- Copyright (c) 2010 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.MonoType where

import Prelude hiding ((<$>))

import Foster.Base
import Foster.KNUtil
import Foster.Config (Compiled, CompilerContext(ccUniqRef), ccWhen, ccVerbose)
import Foster.Output (putDocP)

import Prettyprinter

import Data.Map(Map)
import qualified Data.Map as Map(insert, lookup, empty)
import qualified Data.Text as T
import Control.Monad.State(evalStateT, get, gets, put, lift,
                               StateT, liftIO, liftM, liftM2, liftM3, liftM4)
import Data.IORef

data MonoType =
           PrimInt       IntSizeBits
         | TyCon         DataTypeName
         | TyApp         MonoType [MonoType]
         | TupleType     [MonoType]
         | StructType    [MonoType]
         | FnType        { monoFnTypeDomain :: [MonoType]
                         , monoFnTypeRange  :: MonoType
                         , monoFnTypeCallConv :: CallConv
                         , monoFnTypeProcOrFunc :: ProcOrFunc }
         | CoroType      MonoType MonoType
         | ArrayType     MonoType
         | PtrType       MonoType
         | PtrTypeUnknown
         | RefinedType   (TypedId MonoType) KNMono [Ident]
         deriving Eq

instance Eq KNMono where (==) m1 m2 = (==) (show $ prettyT m1) (show $ prettyT m2)

instance IntSizedBits MonoType where
        intSizeBitsOf (PrimInt isb) = isb
        intSizeBitsOf (RefinedType v _ _) = intSizeBitsOf (tidType v)
        intSizeBitsOf t = error $ "Unable to compute IntSizedBits for non-PrimInt type: " <> show (prettyT t)

extractFnType (FnType _ _ cc pf) = (cc, pf)
extractFnType (PtrType (StructType [FnType _ _ cc FT_Proc, _])) = (cc, FT_Func)

extractFnType other = error $ "Unable to extract fn type from " ++ show (prettyT other)

boolMonoType = PrimInt I1

type MoVar = TypedId MonoType
type MoPrim = FosterPrim MonoType

data MoExternDecl = MoExternDecl String MonoType

instance Pretty CallConv where pretty CCC    = text "ccc"
                               pretty FastCC = text "fastcc"

instance Pretty ProcOrFunc where pretty FT_Proc = text "proc"
                                 pretty FT_Func = text "func"

instance PrettyT MonoType where
  prettyT t = case t of
          PrimInt        isb          -> pretty isb
          TyCon          nm           -> text nm
          TyApp       con []          -> prettyT con
          TyApp       con ts          -> text "(" <> prettyT con <+> tupled (map prettyT ts) <> text "]"
          TupleType      ts           -> tupled (map prettyT ts)
          StructType     ts           -> text "#" <> tupled (map prettyT ts)
          FnType         ts r _cc _pf -> text "{" <+> group (align (hsep [prettyT t <+> text "=>" <> softbreak | t <- ts]))
                                                  <+> prettyT r <+> text "}" <> text "@" <> pretty (_cc,_pf)
          CoroType      _s _r         -> text "Coro..."
          ArrayType      t            -> text "Array" <+> prettyT t
          PtrType        t            -> text "Ref" <+> prettyT t
          PtrTypeUnknown              -> text "?"
          RefinedType v e args        -> parens (text "%" <+> prettyT v <+> text ":" <+> prettyT e <+> text "/" <+> pretty args)

type FnMono   = Fn RecStatus KNMono MonoType
type KNMono     = KNExpr' RecStatus MonoType

renderKNM :: (ModuleIL (KNMono) MonoType) -> String
renderKNM m = show (prettyT m)

renderKNFM :: FnMono -> String
renderKNFM m = show (prettyT m)

instance Summarizable MonoType where
    textOf e _width =
        case e of
            TyCon nam           -> text $ nam
            TyApp con _types    -> text "TyApp " <> prettyT con
            PrimInt     size    -> text "PrimInt " <> pretty size
            TupleType   {}      -> text $ "TupleType"
            StructType  {}      -> text $ "StructType"
            FnType      {}      -> text $ "FnType"
            CoroType    {}      -> text $ "CoroType"
            ArrayType   {}      -> text $ "ArrayType"
            PtrType     {}      -> text $ "PtrType"
            PtrTypeUnknown      -> text "?"
            RefinedType v _e _  -> text "RefinedType " <> prettyT v

instance Structured MonoType where
    childrenOf e =
        case e of
            TyCon {}             -> []
            TyApp con types      -> con:types
            PrimInt       {}     -> []
            TupleType     types  -> types
            StructType    types  -> types
            FnType  ss t _cc _cs -> ss++[t]
            CoroType s t         -> [s,t]
            ArrayType     ty     -> [ty]
            PtrType       ty     -> [ty]
            RefinedType   v  _ _ -> [tidType v]
            PtrTypeUnknown       -> []
            

--
showFnStructure (Fn fnvar args body _ _srcrange) =
  prettyT fnvar <+> text "=" <+>
                     text "{" <+> hsep (map prettyT args)
                 <$> indent 2 (showStructure body)
                 <$> text "}" <> line

instance AlphaRenamish MonoType RecStatus where
  ccAlphaRename = alphaRenameMono

alphaRenameMono :: Fn r (KNExpr' RecStatus MonoType) MonoType -> Compiled (Fn r (KNExpr' RecStatus MonoType) MonoType)
alphaRenameMono fn = alphaRenameMonoWithState fn Map.empty

alphaRenameMonoWithState fn map = do
  renamed <- evalStateT (renameFn fn) (MonoRenameState map)

  ccWhen ccVerbose $ do
      liftIO $ putDocP $ text "mono-fn: " <$> showFnStructure fn
      liftIO $ putDocP $ text "renamed: " <$> showFnStructure renamed

  return renamed
   where
    renameT :: MonoType -> MonoRenamed MonoType
    renameT typ = case typ of
          PrimInt        {}           -> return $ typ
          PtrTypeUnknown              -> return $ typ
          TyCon          {}           -> return $ typ
          TyApp      con ts           -> do liftM2 TyApp (renameT con) (mapM renameT ts)
          TupleType      ts           -> do liftM TupleType     (mapM renameT ts)
          StructType     ts           -> do liftM StructType    (mapM renameT ts)
          CoroType       s  r         -> do liftM2 CoroType (renameT s) (renameT r)
          ArrayType      t            -> do liftM ArrayType (renameT t)
          PtrType        t            -> do liftM PtrType   (renameT t)
          FnType         ts r _cc _pf -> do ts' <- mapM renameT ts ; r' <- renameT r ; return $ FnType ts' r' _cc _pf
          RefinedType v e args        -> do e' <- renameKN e ; args' <- mapM renameI args ; return $ RefinedType v e' args'

    renameV :: TypedId MonoType -> MonoRenamed (TypedId MonoType)
    renameV (TypedId ty id@(GlobalSymbol t _alt)) = do
      do ty' <- renameT ty
         state <- get
         case Map.lookup id (monoRenameMap state) of
            Nothing ->
              -- We want to rename any locally-bound functions that
              -- might have been duplicated by monomorphization.
              if T.pack "<anon_fn"  `T.isInfixOf` t ||
                 T.pack ".anon."    `T.isInfixOf` t ||
                 T.pack ".kn.thunk" `T.isPrefixOf` t
                  then do
                        id' <- renameI id
                        return (TypedId ty' id' )
                  else  return (TypedId ty' id  )
            Just id' -> return (TypedId ty' id' )

    renameV     (TypedId ty id) = do
      state <- get
      case Map.lookup id (monoRenameMap state) of
        Nothing  -> do id' <- renameI id
                       ty' <- renameT ty
                       return (TypedId ty' id' )
        Just _u' -> error $ "KNUtil.hs: can't rename a variable twice! " ++ show (prettyIdent id)

    renameI id@(GlobalSymbol t alt) = do
                                     u' <- fresh
                                     let id' = GlobalSymbol (t `T.append` T.pack (show u')) alt
                                     remap id id'
                                     return id'
    renameI id@(Ident s _)      = do u' <- fresh
                                     let id' = Ident s u'
                                     remap id id'
                                     return id'
    fresh :: MonoRenamed Uniq
    fresh = do uref <- lift (gets ccUniqRef) ; mutIORef uref (+1)

    mutIORef :: IORef a -> (a -> a) -> MonoRenamed a
    mutIORef r f = liftIO $ modIORef' r f >> readIORef r

    remap id id' = do state <- get
                      put state { monoRenameMap = Map.insert id id' (monoRenameMap state) }

    qv :: TypedId MonoType -> MonoRenamed (TypedId MonoType)
    qv (TypedId t i) = do i' <- qi i ;
                          t' <- renameT t
                          return $ TypedId t' i'

    qi x = do state <- get
              case Map.lookup x (monoRenameMap state) of
                Just x' -> return x'
                Nothing -> return x

    qt = renameT

    renameFn :: Fn r (KNExpr' r2 MonoType) MonoType -> MonoRenamed (Fn r (KNExpr' r2 MonoType) MonoType)
    renameFn (Fn v vs body isrec rng) = do
       (v' : vs') <- mapM renameV (v:vs)
       body' <- renameKN body
       return (Fn v' vs' body' isrec rng)

    renameArrayIndex (ArrayIndex v1 v2 rng s) =
      do v1' <- qv v1 ; v2' <- qv v2 ; return $ ArrayIndex v1' v2' rng s

    renameKN :: (KNExpr' r MonoType) -> MonoRenamed (KNExpr' r MonoType)
    renameKN e =
      case e of
      KNLiteral       {}       -> return e
      KNKillProcess   {}       -> return e
      KNRecord        t ls vs a -> do vs' <- mapM qv vs; t' <- qt t ; return $ KNRecord t' ls vs' a
      KNTuple         t vs a   -> do vs' <- mapM qv vs; t' <- qt t ; return $ KNTuple t' vs' a
      KNCall          t v vs c -> do (v' : vs') <- mapM qv (v:vs); t' <- qt t; return $ KNCall t' v' vs' c
      KNCallPrim   sr t p vs   -> do vs' <- mapM qv vs; t' <- qt t; return $ KNCallPrim   sr t' p vs'
      KNAppCtor       t c vs sr -> do vs' <- mapM qv vs; t' <- qt t; return $ KNAppCtor t' c vs' sr
      KNAllocArray    t v amr zi sr -> do t' <- qt t; v' <- qv v; return $ KNAllocArray t' v' amr zi sr
      KNAlloc         t v amr    sr -> liftM4 KNAlloc      (qt t) (qv v) (return amr) (return sr)
      KNDeref         t v      -> liftM2 KNDeref      (qt t) (qv v)
      KNStore         t v1 v2  -> liftM3 KNStore      (qt t) (qv v1) (qv v2)
      KNArrayRead     t ai     -> liftM2 KNArrayRead  (qt t) (renameArrayIndex ai)
      KNArrayPoke     t ai v   -> liftM3 KNArrayPoke  (qt t) (renameArrayIndex ai) (qv v)
      KNArrayLit    t arr vals -> liftM3 KNArrayLit   (qt t) (qv arr) (mapRightM qv vals)
      KNVar                  v -> liftM  KNVar                  (qv v)
      KNCase          t v arms -> liftM3 KNCase (qt t) (qv v) (mapM renameCaseArm arms)
      KNHandler ann   t fx a arms x resumeid -> do t' <- qt t
                                                   fx' <- qt fx
                                                   a' <- renameKN a
                                                   arms' <- mapM renameCaseArm arms
                                                   x' <- liftMaybe renameKN x
                                                   return $ KNHandler ann t' fx' a' arms' x' resumeid
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
      KNLetFuns     ids fns b sr -> do ids' <- mapM renameI ids
                                       fns' <- mapM renameFn fns
                                       b'   <- renameKN b
                                       return $ KNLetFuns ids' fns' b' sr
      KNTyApp t v argtys       -> liftM3 KNTyApp (qt t) (qv v) (return argtys)
      KNCompiles r t e         -> liftM2 (KNCompiles r) (qt t) (renameKN e)
      KNRelocDoms ids e -> do liftM2 KNRelocDoms (mapM qi ids) (renameKN e)

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

data MonoRenameState = MonoRenameState { monoRenameMap  :: Map Ident Ident }
type MonoRenamed = StateT MonoRenameState Compiled
