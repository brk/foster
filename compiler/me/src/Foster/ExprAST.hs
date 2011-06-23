-----------------------------------------------------------------------------
-- Copyright (c) 2010 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.ExprAST where

import Foster.Base
import Foster.TypeAST

data CompilesStatus = CS_WouldCompile | CS_WouldNotCompile | CS_NotChecked
    deriving (Eq, Show)

class Expr a where
    freeVars   :: a -> [String]

data TermBinding = TermBinding E_VarAST ExprAST
        deriving (Show)

data ExprAST =
          E_BoolAST       ESourceRange Bool
        | E_IntAST        ESourceRange String
        | E_TupleAST      [ExprAST]
        | E_FnAST         FnAST
        | E_LetAST        ESourceRange  TermBinding  ExprAST (Maybe TypeAST)
        | E_LetRec        ESourceRange [TermBinding] ExprAST (Maybe TypeAST)
        | E_CallAST       ESourceRange ExprAST [ExprAST]
        | E_CompilesAST   ExprAST CompilesStatus
        | E_IfAST         ExprAST ExprAST ExprAST
        | E_UntilAST      ExprAST ExprAST
        | E_SeqAST        ExprAST ExprAST
        | E_AllocAST      ESourceRange ExprAST
        | E_DerefAST      ESourceRange ExprAST
        | E_StoreAST      ESourceRange ExprAST ExprAST
        | E_SubscriptAST  { subscriptBase  :: ExprAST
                          , subscriptIndex :: ExprAST
                          , subscriptRange :: ESourceRange }
        | E_VarAST        ESourceRange E_VarAST
        | E_TyApp         ESourceRange ExprAST TypeAST
        | E_Case          ESourceRange ExprAST [(EPattern, ExprAST)]
        deriving Show

data FnAST  = FnAST { fnAstRange :: ESourceRange
                    , fnAstName :: String
                    , fnRetType :: Maybe TypeAST
                    , fnFormals :: [AnnVar]
                    , fnBody  :: ExprAST
                    , fnWasToplevel :: Bool
                    } deriving (Show)

-- | Converts a right-leaning "list" of SeqAST nodes to a List
unbuildSeqs :: ExprAST -> [ExprAST]
unbuildSeqs (E_SeqAST a b) = a : unbuildSeqs b
unbuildSeqs expr = [expr]

-----------------------------------------------------------------------

data AnnExpr =
          AnnBool       Bool
        | AnnInt        { aintType   :: TypeAST
                        , aintLitInt :: LiteralInt }

        -- No need for an explicit type, so long as subexprs are typed.
        | AnnTuple      [AnnExpr]

        | E_AnnFn       AnnFn

        -- Add an overall type for the application
        | AnnCall       ESourceRange TypeAST AnnExpr [AnnExpr]

        -- Add an overall type for the if branch
        | AnnIf         TypeAST AnnExpr AnnExpr AnnExpr
        | AnnUntil      TypeAST AnnExpr AnnExpr

        | AnnLetVar     Ident AnnExpr AnnExpr

        -- We have separate syntax for a SCC of recursive functions
        -- because they are compiled differently from non-recursive closures.
        | AnnLetFuns    [Ident] [AnnFn] AnnExpr

        | AnnAlloc      AnnExpr
        | AnnDeref      TypeAST AnnExpr
        | AnnStore      TypeAST AnnExpr AnnExpr

        -- Subscripts get an overall type
        | AnnSubscript  TypeAST AnnExpr AnnExpr

        --Vars go from a Maybe TypeAST to a required TypeAST
        | E_AnnVar       AnnVar

        | E_AnnTyApp {  annTyAppOverallType :: TypeAST
                     ,  annTyAppExpr        :: AnnExpr
                     ,  annTyAppArgTypes    :: TypeAST }

        | AnnCase    TypeAST AnnExpr [(Pattern, AnnExpr)]
        -- This one's a bit odd, in that we can't include an AnnExpr
        -- because the subterm doesn't need to be well-typed...
        | AnnCompiles   CompilesStatus String
        deriving (Show)

-- Body annotated, and overall type added
data AnnFn        = AnnFn  { annFnType  :: TypeAST
                           , annFnIdent :: Ident
                           , annFnVars  :: [AnnVar]
                           , annFnBody  :: AnnExpr
                           , annFnClosedVars :: (Maybe [AnnVar])
                           , annFnRange :: ESourceRange
                           } deriving (Show)

fnNameA f = identPrefix (annFnIdent f)

-----------------------------------------------------------------------

typeAST :: AnnExpr -> TypeAST
typeAST (AnnBool _)          = fosBoolType
typeAST (AnnInt t _)         = t
typeAST (AnnTuple es)        = TupleTypeAST [typeAST e | e <- es]
typeAST (E_AnnFn annFn)      = annFnType annFn
typeAST (AnnCall r t b a)    = t
typeAST (AnnCompiles c msg)  = fosBoolType
typeAST (AnnIf t a b c)      = t
typeAST (AnnUntil t _ _)     = t
typeAST (AnnLetVar _ a b)    = typeAST b
typeAST (AnnLetFuns _ _ e)   = typeAST e
typeAST (AnnAlloc e)         = RefType (typeAST e)
typeAST (AnnDeref t _)       = t
typeAST (AnnStore t _ _)     = t
typeAST (AnnSubscript t _ _) = t
typeAST (AnnCase t _ _)      = t
typeAST (E_AnnVar (AnnVar t s)) = t
typeAST (E_AnnTyApp substitutedTy tm tyArgs) = substitutedTy

-----------------------------------------------------------------------


tryGetCallNameE :: ExprAST -> String
tryGetCallNameE (E_VarAST rng (VarAST mt v)) = v
tryGetCallNameE _ = ""

instance Structured ExprAST where
    textOf e width =
        let spaces = Prelude.replicate width '\SP'  in
        case e of
            E_BoolAST rng  b     -> out $ "BoolAST      " ++ (show b)
            E_CallAST rng b args -> out $ "CallAST      " ++ tryGetCallNameE b
            E_CompilesAST e c    -> out $ "CompilesAST  "
            E_IfAST _ _ _        -> out $ "IfAST        "
            E_UntilAST _ _       -> out $ "UntilAST     "
            E_IntAST rng text    -> out $ "IntAST       " ++ text
            E_FnAST f            -> out $ "FnAST        " ++ (fnAstName f)
            E_LetRec rnd bnz e t -> out $ "LetRec       "
            E_LetAST rng bnd e t -> out $ "LetAST       " ++ (case bnd of (TermBinding v _) -> evarName v)
            E_SeqAST   a b       -> out $ "SeqAST       "
            E_AllocAST rng a     -> out $ "AllocAST     "
            E_DerefAST rng a     -> out $ "DerefAST     "
            E_StoreAST rng a b   -> out $ "StoreAST     "
            E_SubscriptAST a b r -> out $ "SubscriptAST "
            E_TupleAST     es    -> out $ "TupleAST     "
            E_TyApp rng a t      -> out $ "TyApp        "
            E_Case rng _ _       -> out $ "Case         "
            E_VarAST rng v       -> out $ "VarAST       " ++ evarName v ++ " :: " ++ show (evarMaybeType v)
    childrenOf e =
        case e of
            E_BoolAST rng b      -> []
            E_CallAST rng b args -> b:args
            E_CompilesAST   e c  -> [e]
            E_IfAST a b c        -> [a, b, c]
            E_UntilAST a b       -> [a, b]
            E_IntAST rng txt     -> []
            E_FnAST f            -> [fnBody f]
            E_LetRec rnd bnz e t -> [termBindingExpr bnd | bnd <- bnz] ++ [e]
            E_LetAST rng bnd e t -> (termBindingExpr bnd):[e]
            E_SeqAST       a b   -> unbuildSeqs e
            E_AllocAST rng a     -> [a]
            E_DerefAST rng a     -> [a]
            E_StoreAST rng a b   -> [a, b]
            E_SubscriptAST a b r -> [a, b]
            E_TupleAST     es    -> es
            E_TyApp  rng a t     -> [a]
            E_Case rng e bs      -> e:(map snd bs)
            E_VarAST _ _         -> []

termBindingExpr (TermBinding _ e) = e
termBindingExprs bs = map termBindingExpr bs
termBindingNames bs = map (\(TermBinding v _) -> evarName v) bs
bindingFreeVars (TermBinding v e) = freeVars e `butnot` [evarName v]

instance Expr ExprAST where
    freeVars e = case e of
        E_VarAST rng v      -> [evarName v]
        E_LetAST rng bnd e t -> freeVars e ++ (bindingFreeVars bnd)
        E_Case rng e epatbnds -> freeVars e ++ (concatMap epatBindingFreeVars epatbnds)
        E_FnAST f           -> let bodyvars  = freeVars (fnBody f) in
                               let boundvars = map (identPrefix.avarIdent) (fnFormals f) in
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
            AnnBool         b    -> out $ "AnnBool      " ++ (show b)
            AnnCall  r t b args  -> out $ "AnnCall      " ++ " :: " ++ show t
            AnnCompiles c msg    -> out $ "AnnCompiles  " ++ show c ++ " - " ++ msg
            AnnIf      t  a b c  -> out $ "AnnIf        " ++ " :: " ++ show t
            AnnUntil   t  a b    -> out $ "AnnUntil     " ++ " :: " ++ show t
            AnnInt ty int        -> out $ "AnnInt       " ++ (litIntText int) ++ " :: " ++ show ty
            E_AnnFn annFn        -> out $ "AnnFn " ++ fnNameA annFn ++ " // " ++ (show $ annFnBoundNames annFn) ++ " :: " ++ show (annFnType annFn)
            AnnLetVar id    a b  -> out $ "AnnLetVar    " ++ show id ++ " :: " ++ show (typeAST b)
            AnnLetFuns ids fns e -> out $ "AnnLetFuns   " ++ show ids
            AnnAlloc        a    -> out $ "AnnAlloc     "
            AnnDeref      t a    -> out $ "AnnDeref     "
            AnnStore      t a b  -> out $ "AnnStore     "
            AnnSubscript  t a b  -> out $ "AnnSubscript " ++ " :: " ++ show t
            AnnTuple     es      -> out $ "AnnTuple     "
            AnnCase      t e bs  -> out $ "AnnCase      "
            E_AnnVar (AnnVar t v) -> out $ "AnnVar       " ++ show v ++ " :: " ++ show t
            E_AnnTyApp t e argty -> out $ "AnnTyApp     [" ++ show argty ++ "] :: " ++ show t
    childrenOf e =
        case e of
            AnnBool         b                    -> []
            AnnCall  r t b args                  -> b:args
            AnnCompiles c msg                    -> []
            AnnIf      t  a b c                  -> [a, b, c]
            AnnUntil   t  a b                    -> [a, b]
            AnnInt t _                           -> []
            E_AnnFn annFn                        -> [annFnBody annFn]
            AnnLetVar _ a b                      -> [a, b]
            AnnLetFuns ids fns e                 -> (map E_AnnFn fns) ++ [e]
            AnnAlloc        a                    -> [a]
            AnnDeref      t a                    -> [a]
            AnnStore      t a b                  -> [a, b]
            AnnSubscript t a b                   -> [a, b]
            AnnTuple     es                      -> es
            AnnCase t e bs                       -> e:(map snd bs)
            E_AnnVar      v                      -> []
            E_AnnTyApp t a argty                 -> [a]

instance Expr AnnExpr where
    freeVars e = [identPrefix i | i <- freeIdentsA e]

freeIdentsA e = case e of
        E_AnnVar v      -> [avarIdent v]
        AnnLetVar id a b     -> freeIdentsA a ++ (freeIdentsA b `butnot` [id])
        AnnCase _t e patbnds -> freeIdentsA e ++ (concatMap patBindingFreeIds patbnds)
        -- Note that all free idents of the bound expr are free in letvar,
        -- but letfuns removes the bound name from that set!
        AnnLetFuns ids fns e ->
                           concatMap boundvars (zip ids fns) ++ (freeIdentsA e `butnot` ids) where
                                     boundvars (id, fn) = freeIdentsA (E_AnnFn fn) `butnot` [id]
        E_AnnFn f       -> let bodyvars =  freeIdentsA (annFnBody f) in
                           let boundvars = map avarIdent (annFnVars f) in
                           bodyvars `butnot` boundvars
        _               -> concatMap freeIdentsA (childrenOf e)

patBindingFreeIds (pat, expr) =
  freeIdentsA expr `butnot` patBoundIds pat
  where patBoundIds :: Pattern -> [Ident]
        patBoundIds pat =
          case pat of
            P_Wildcard _rng      -> []
            P_Variable _rng id   -> [id]
            P_Bool     _rng _    -> []
            P_Int      _rng _    -> []
            P_Tuple    _rng pats -> concatMap patBoundIds pats

annFnBoundNames :: AnnFn -> [String]
annFnBoundNames fn = map show (annFnVars fn)

