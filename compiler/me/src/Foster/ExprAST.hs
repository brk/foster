-----------------------------------------------------------------------------
-- Copyright (c) 2010 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.ExprAST where

import Foster.Base
import Foster.TypeAST

data TermBinding = TermBinding E_VarAST ExprAST
        deriving (Show)
type AnnVar = TypedId TypeAST
data ExprAST =
          E_BoolAST       ESourceRange Bool
        | E_IntAST        ESourceRange String
        | E_TupleAST      TupleAST
        | E_FnAST         FnAST
        | E_LetAST        ESourceRange  TermBinding  ExprAST (Maybe TypeAST)
        | E_LetRec        ESourceRange [TermBinding] ExprAST (Maybe TypeAST)
        | E_CallAST       ESourceRange ExprAST TupleAST
        | E_CompilesAST   ESourceRange (Maybe ExprAST)
        | E_IfAST         ESourceRange ExprAST ExprAST ExprAST
        | E_UntilAST      ESourceRange ExprAST ExprAST
        | E_SeqAST        ESourceRange ExprAST ExprAST
        | E_AllocAST      ESourceRange ExprAST
        | E_DerefAST      ESourceRange ExprAST
        | E_StoreAST      ESourceRange ExprAST ExprAST
        | E_SubscriptAST  ESourceRange ExprAST ExprAST
        | E_VarAST        ESourceRange E_VarAST
        | E_Primitive     ESourceRange E_VarAST
        | E_TyApp         ESourceRange ExprAST TypeAST
        | E_Case          ESourceRange ExprAST [(EPattern, ExprAST)]
        deriving Show
data TupleAST = TupleAST { tupleAstRange :: ESourceRange
                         , tupleAstExprs :: [ExprAST] } deriving (Show)
data FnAST  = FnAST { fnAstRange :: ESourceRange
                    , fnAstName :: String
                    , fnRetType :: Maybe TypeAST
                    , fnFormals :: [AnnVar]
                    , fnBody  :: ExprAST
                    , fnWasToplevel :: Bool
                    } deriving (Show)

-- | Converts a right-leaning "list" of SeqAST nodes to a List
unbuildSeqs :: ExprAST -> [ExprAST]
unbuildSeqs (E_SeqAST _rng a b) = a : unbuildSeqs b
unbuildSeqs expr = [expr]

-----------------------------------------------------------------------

data AnnExpr =
          AnnBool       ESourceRange Bool
        | AnnInt        { aintRange  :: ESourceRange
                        , aintType   :: TypeAST
                        , aintLitInt :: LiteralInt }

        -- No need for an explicit type, so long as subexprs are typed.
        | AnnTuple      AnnTuple

        | E_AnnFn       AnnFn

        -- Add an overall type for the application
        | AnnCall       ESourceRange TypeAST AnnExpr AnnTuple

        -- Add an overall type for the if branch
        | AnnIf         ESourceRange TypeAST AnnExpr AnnExpr AnnExpr
        | AnnUntil      ESourceRange TypeAST AnnExpr AnnExpr

        | AnnLetVar     ESourceRange Ident AnnExpr AnnExpr

        -- We have separate syntax for a SCC of recursive functions
        -- because they are compiled differently from non-recursive closures.
        | AnnLetFuns    ESourceRange [Ident] [AnnFn] AnnExpr

        | AnnAlloc      ESourceRange AnnExpr
        | AnnDeref      ESourceRange TypeAST AnnExpr
        | AnnStore      ESourceRange TypeAST AnnExpr AnnExpr

        -- Subscripts get an overall type
        | AnnSubscript  ESourceRange TypeAST AnnExpr AnnExpr

        --Vars go from a Maybe TypeAST to a required TypeAST
        | E_AnnVar       ESourceRange AnnVar

        | AnnPrimitive   ESourceRange AnnVar

        | E_AnnTyApp {  annTyAppRange       :: ESourceRange
                     ,  annTyAppOverallType :: TypeAST
                     ,  annTyAppExpr        :: AnnExpr
                     ,  annTyAppArgTypes    :: TypeAST }

        | AnnCase    ESourceRange TypeAST AnnExpr [(Pattern, AnnExpr)]
        -- This one's a bit odd, in that we can't always include an AnnExpr
        -- because the subterm doesn't need to be well-typed.
        -- But we should include one if possible, for further checking.
        | AnnCompiles   ESourceRange (CompilesResult AnnExpr)
        deriving (Show)

data AnnTuple = E_AnnTuple { annTupleRange :: ESourceRange
                           , annTupleExprs :: [AnnExpr] } deriving (Show)

-- Body annotated, and overall type added
data AnnFn        = AnnFn  { annFnType  :: TypeAST
                           , annFnIdent :: Ident
                           , annFnVars  :: [AnnVar]
                           , annFnBody  :: AnnExpr
                           , annFnRange :: ESourceRange
                           } deriving (Show)

fnNameA f = identPrefix (annFnIdent f)

-----------------------------------------------------------------------

typeAST :: AnnExpr -> TypeAST
typeAST annexpr =
  let recur = typeAST in
  case annexpr of
     (AnnBool _rng _)        -> fosBoolType
     (AnnInt _rng t _)       -> t
     (AnnTuple tup)          -> TupleTypeAST [recur e | e <- childrenOf annexpr]
     (E_AnnFn annFn)         -> annFnType annFn
     (AnnCall r t b a)       -> t
     (AnnCompiles _rng _)    -> fosBoolType
     (AnnIf _rng t a b c)    -> t
     (AnnUntil _rng t _ _)   -> t
     (AnnLetVar _rng _ a b)  -> recur b
     (AnnLetFuns _rng _ _ e) -> recur e
     (AnnAlloc _rng e)       -> RefTypeAST (recur e)
     (AnnDeref _rng t _)     -> t
     (AnnStore _rng t _ _)   -> t
     (AnnSubscript _r t _ _) -> t
     (AnnCase _rng t _ _)    -> t
     (E_AnnVar _rng tid)     -> tidType tid
     (AnnPrimitive _rng tid) -> tidType tid
     (E_AnnTyApp _rng substitutedTy tm tyArgs) -> substitutedTy

-----------------------------------------------------------------------


tryGetCallNameE :: ExprAST -> String
tryGetCallNameE (E_VarAST rng (VarAST mt v)) = v
tryGetCallNameE (E_Primitive rng (VarAST mt v)) = v
tryGetCallNameE _ = ""

instance Structured ExprAST where
    textOf e width =
        let spaces = Prelude.replicate width '\SP'  in
        case e of
            E_BoolAST rng  b     -> out $ "BoolAST      " ++ (show b)
            E_CallAST rng b args -> out $ "CallAST      " ++ tryGetCallNameE b
            E_CompilesAST _rng _ -> out $ "CompilesAST  "
            E_IfAST _rng _ _ _   -> out $ "IfAST        "
            E_UntilAST _rng _ _  -> out $ "UntilAST     "
            E_IntAST rng text    -> out $ "IntAST       " ++ text
            E_FnAST f            -> out $ "FnAST        " ++ (fnAstName f)
            E_LetRec rnd bnz e t -> out $ "LetRec       "
            E_LetAST rng bnd e t -> out $ "LetAST       " ++ (case bnd of (TermBinding v _) -> evarName v)
            E_SeqAST _rng a b    -> out $ "SeqAST       "
            E_AllocAST rng a     -> out $ "AllocAST     "
            E_DerefAST rng a     -> out $ "DerefAST     "
            E_StoreAST rng a b   -> out $ "StoreAST     "
            E_SubscriptAST a b r -> out $ "SubscriptAST "
            E_TupleAST _         -> out $ "TupleAST     "
            E_TyApp rng a t      -> out $ "TyApp        "
            E_Case rng _ _       -> out $ "Case         "
            E_VarAST rng v       -> out $ "VarAST       " ++ evarName v ++ " :: " ++ show (evarMaybeType v)
            E_Primitive rng v    -> out $ "PrimitiveAST " ++ evarName v ++ " :: " ++ show (evarMaybeType v)
    childrenOf e =
        case e of
            E_BoolAST rng b      -> []
            E_CallAST rng b tup -> b:(tupleAstExprs tup)
            E_CompilesAST _rng (Just e) -> [e]
            E_CompilesAST _rng Nothing -> []
            E_IfAST _rng    a b c -> [a, b, c]
            E_UntilAST _rng a b   -> [a, b]
            E_IntAST rng txt     -> []
            E_FnAST f            -> [fnBody f]
            E_LetRec rnd bnz e t -> [termBindingExpr bnd | bnd <- bnz] ++ [e]
            E_LetAST rng bnd e t -> (termBindingExpr bnd):[e]
            E_SeqAST _rng  a b   -> unbuildSeqs e
            E_AllocAST rng a     -> [a]
            E_DerefAST rng a     -> [a]
            E_StoreAST rng a b   -> [a, b]
            E_SubscriptAST r a b -> [a, b]
            E_TupleAST tup       -> tupleAstExprs tup
            E_TyApp  rng a t     -> [a]
            E_Case rng e bs      -> e:(map snd bs)
            E_VarAST _ _         -> []
            E_Primitive _ _      -> []

termBindingExpr (TermBinding _ e) = e
termBindingExprs bs = map termBindingExpr bs
termBindingNames bs = map (\(TermBinding v _) -> evarName v) bs
bindingFreeVars (TermBinding v e) = freeVars e `butnot` [evarName v]

instance SourceRanged ExprAST
  where
    rangeOf e = case e of
      E_BoolAST       rng _ -> rng
      E_IntAST        rng _ -> rng
      E_TupleAST    tup -> tupleAstRange tup
      E_FnAST         f -> fnAstRange f
      E_LetAST        rng _ _ _ -> rng
      E_LetRec        rng _ _ _ -> rng
      E_CallAST       rng _ _   -> rng
      E_CompilesAST   rng _     -> rng
      E_IfAST         rng _ _ _ -> rng
      E_UntilAST      rng _ _   -> rng
      E_SeqAST        rng _ _   -> rng
      E_AllocAST      rng _     -> rng
      E_DerefAST      rng _     -> rng
      E_StoreAST      rng _ _   -> rng
      E_SubscriptAST  rng _ _   -> rng
      E_VarAST        rng _     -> rng
      E_Primitive     rng _     -> rng
      E_TyApp         rng _ _   -> rng
      E_Case          rng _ _   -> rng

instance Expr ExprAST where
    freeVars e = case e of
        E_VarAST rng v       -> [evarName v]
        E_Primitive rng v    -> [] -- Primitives are never actually closed over...
        E_LetAST rng bnd e t -> freeVars e ++ (bindingFreeVars bnd)
        E_Case rng e epatbnds -> freeVars e ++ (concatMap epatBindingFreeVars epatbnds)
        E_FnAST f           -> let bodyvars  = freeVars (fnBody f) in
                               let boundvars = map (identPrefix.tidIdent) (fnFormals f) in
                               bodyvars `butnot` boundvars
        _                   -> concatMap freeVars (childrenOf e)

epatBindingFreeVars (pat, expr) =
  freeVars expr `butnot` epatBoundNames pat
  where epatBoundNames :: EPattern -> [String]
        epatBoundNames pat =
          case pat of
            EP_Wildcard _rng      -> []
            EP_Variable _rng evar -> [evarName evar]
            EP_Bool     _rng _    -> []
            EP_Int      _rng _    -> []
            EP_Tuple    _rng pats -> concatMap epatBoundNames pats


instance Structured AnnExpr where
    textOf e width =
        let spaces = Prelude.replicate width '\SP'  in
        case e of
            AnnBool _rng    b    -> out $ "AnnBool      " ++ (show b)
            AnnCall rng t b args -> out $ "AnnCall      " ++ " :: " ++ show t
            AnnCompiles rng cr   -> out $ "AnnCompiles  " ++ show cr
            AnnIf _rng t  a b c  -> out $ "AnnIf        " ++ " :: " ++ show t
            AnnUntil _rng t a b  -> out $ "AnnUntil     " ++ " :: " ++ show t
            AnnInt _rng ty int   -> out $ "AnnInt       " ++ (litIntText int) ++ " :: " ++ show ty
            AnnLetVar _rng id a b -> out $ "AnnLetVar    " ++ show id ++ " :: " ++ show (typeAST b)
            AnnLetFuns _r ids fns e -> out $ "AnnLetFuns   " ++ show ids
            AnnAlloc _rng   a    -> out $ "AnnAlloc     "
            AnnDeref _rng t a    -> out $ "AnnDeref     "
            AnnStore _rng t a b  -> out $ "AnnStore     "
            AnnSubscript _r t a b-> out $ "AnnSubscript " ++ " :: " ++ show t
            AnnTuple     es      -> out $ "AnnTuple     "
            AnnCase _rng t e bs  -> out $ "AnnCase      "
            AnnPrimitive _r (TypedId t v) -> out $ "AnnPrimitive " ++ show v ++ " :: " ++ show t
            E_AnnVar _r (TypedId t v) -> out $ "AnnVar       " ++ show v ++ " :: " ++ show t
            E_AnnFn annFn        -> out $ "AnnFn " ++ fnNameA annFn ++ " // " ++ (show $ annFnBoundNames annFn) ++ " :: " ++ show (annFnType annFn)
            E_AnnTyApp _rng t e argty -> out $ "AnnTyApp     [" ++ show argty ++ "] :: " ++ show t
    childrenOf e =
        case e of
            AnnBool _rng    b                    -> []
            AnnCall  r t b argtup                -> b:(annTupleExprs argtup)
            AnnCompiles _rng (CompilesResult (OK e))     -> [e]
            AnnCompiles _rng (CompilesResult (Errors _)) -> []
            AnnIf _rng t  a b c                  -> [a, b, c]
            AnnUntil _rng t  a b                 -> [a, b]
            AnnInt   _rng t _                    -> []
            E_AnnFn annFn                        -> [annFnBody annFn]
            AnnLetVar _rng _ a b                 -> [a, b]
            AnnLetFuns _rng ids fns e            -> (map E_AnnFn fns) ++ [e]
            AnnAlloc _rng   a                    -> [a]
            AnnDeref _rng t a                    -> [a]
            AnnStore _rng t a b                  -> [a, b]
            AnnSubscript _rng t a b              -> [a, b]
            AnnTuple tup                         -> annTupleExprs tup
            AnnCase _rng t e bs                  -> e:(map snd bs)
            E_AnnVar     _rng v                  -> []
            AnnPrimitive _rng v                  -> []
            E_AnnTyApp _rng t a argty            -> [a]

instance AExpr AnnExpr where
    freeIdents e = case e of
        E_AnnVar     _rng v -> [tidIdent v]
        AnnPrimitive _rng v -> []
        AnnLetVar _rng id a b     -> freeIdents a ++ (freeIdents b `butnot` [id])
        AnnCase _rng _t e patbnds -> freeIdents e ++ (concatMap patBindingFreeIds patbnds)
        -- Note that all free idents of the bound expr are free in letvar,
        -- but letfuns removes the bound name from that set!
        AnnLetFuns _rng ids fns e ->
                           concatMap boundvars (zip ids fns) ++ (freeIdents e `butnot` ids) where
                                     boundvars (id, fn) = freeIdents (E_AnnFn fn) `butnot` [id]
        E_AnnFn f       -> let bodyvars =  freeIdents (annFnBody f) in
                           let boundvars = map tidIdent (annFnVars f) in
                           bodyvars `butnot` boundvars
        _               -> concatMap freeIdents (childrenOf e)

annFnBoundNames :: AnnFn -> [String]
annFnBoundNames fn = map show (annFnVars fn)

instance SourceRanged AnnExpr where
  rangeOf expr = case expr of
      AnnBool rng    b            -> rng
      AnnCall rng t b argtup      -> rng
      AnnCompiles rng _           -> rng
      AnnIf rng t  a b c          -> rng
      AnnUntil rng t  a b         -> rng
      AnnInt   rng t _            -> rng
      E_AnnFn f                   -> annFnRange f
      AnnLetVar rng _ a b         -> rng
      AnnLetFuns rng ids fns e    -> rng
      AnnAlloc rng   a            -> rng
      AnnDeref rng t a            -> rng
      AnnStore rng t a b          -> rng
      AnnSubscript rng t a b      -> rng
      AnnTuple tup                -> annTupleRange tup
      AnnCase rng t e bs          -> rng
      E_AnnVar     rng v          -> rng
      AnnPrimitive rng v          -> rng
      E_AnnTyApp rng t a argty    -> rng

