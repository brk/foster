-----------------------------------------------------------------------------
-- Copyright (c) 2010 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.ExprAST where

import Data.Int
import Data.Set as Set(fromList, toList, difference)

import Data.Sequence as Seq
import Data.Maybe(fromJust)
import Data.List(replicate)
import qualified Data.Text as T

import Foster.Base
import Foster.TypeAST

data CompilesStatus = CS_WouldCompile | CS_WouldNotCompile | CS_NotChecked
    deriving (Eq, Show)

class Expr a where
    freeVars   :: a -> [String]

data ExprAST =
          E_BoolAST       ESourceRange Bool
        | E_IntAST        ESourceRange String
        | E_TupleAST      [ExprAST]
        | E_FnAST         FnAST
        | E_CallAST       ESourceRange ExprAST [ExprAST]
        | E_CompilesAST   ExprAST CompilesStatus
        | E_IfAST         ExprAST ExprAST ExprAST
        | E_SeqAST        ExprAST ExprAST
        | E_SubscriptAST  { subscriptBase  :: ExprAST
                          , subscriptIndex :: ExprAST }
        | E_VarAST       { evarMaybeType :: Maybe TypeAST
                         , evarName      :: String }
        deriving Show

data FnAST  = FnAST { fnProto :: PrototypeAST
                    , fnBody  :: ExprAST
                    , fnClosedVars :: (Maybe [AnnVar])
                    } deriving (Show)
data PrototypeAST = PrototypeAST {
                          prototypeASTretType :: TypeAST
                        , prototypeASTname    :: String
                        , prototypeASTformals :: [AnnVar]
                    } deriving (Show)

-- | Converts a right-leaning "list" of SeqAST nodes to a List
unbuildSeqs :: ExprAST -> [ExprAST]
unbuildSeqs (E_SeqAST a b) = a : unbuildSeqs b
unbuildSeqs expr = [expr]


fnTypeCloses' :: FnAST -> Maybe [(Ident, TypeAST)]
fnTypeCloses' f =
    let devar (AnnVar ty id) = (id, ty) in
    fmap (map devar) (fnClosedVars f)

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

        -- The type of a sequence is the type of its second part
        | AnnSeq        AnnExpr AnnExpr

        -- Subscripts get an overall type
        | AnnSubscript  TypeAST AnnExpr AnnExpr

        --Vars go from a Maybe TypeAST to a required TypeAST
        | E_AnnVar       AnnVar

        | E_AnnTyApp {  annTyAppOverallType :: TypeAST
                     ,  annTyAppExpr        :: AnnExpr
                     ,  annTyAppArgTypes    :: TypeAST }

        -- This one's a bit odd, in that we can't include an AnnExpr
        -- because the subterm doesn't need to be well-typed...
        | AnnCompiles   CompilesStatus String
        deriving (Show)

-- Body annotated, and overall type added
data AnnFn        = AnnFn  { annFnType :: TypeAST
                           , annFnProto :: AnnPrototype
                           , annFnBody :: AnnExpr
                           , annFnClosedVars :: (Maybe [AnnVar])
                           } deriving (Show)


data AnnPrototype = AnnPrototype    { annProtoReturnType :: TypeAST
                                    , annProtoIdent      :: Ident
                                    , annProtoVars       :: [AnnVar]
                                    } deriving (Eq, Show)

fnNameA f = identPrefix $ annProtoIdent (annFnProto f)

-----------------------------------------------------------------------

unbuildSeqsA :: AnnExpr -> [AnnExpr]
unbuildSeqsA (AnnSeq a b) = a : unbuildSeqsA b
unbuildSeqsA expr = [expr]

-----------------------------------------------------------------------

typeAST :: AnnExpr -> TypeAST
typeAST (AnnBool _)          = fosBoolType
typeAST (AnnInt t _)         = t
typeAST (AnnTuple es)        = TupleTypeAST [typeAST e | e <- es]
typeAST (E_AnnFn annFn)      = annFnType annFn
typeAST (AnnCall r t b a)    = t
typeAST (AnnCompiles c msg)  = fosBoolType
typeAST (AnnIf t a b c)      = t
typeAST (AnnSeq a b)         = typeAST b
typeAST (AnnSubscript t _ _) = t
typeAST (E_AnnVar (AnnVar t s)) = t
typeAST (E_AnnTyApp substitutedTy tm tyArgs) = substitutedTy

-----------------------------------------------------------------------


tryGetCallNameE :: ExprAST -> String
tryGetCallNameE (E_VarAST mt v) = v
tryGetCallNameE _ = ""

instance Structured ExprAST where
    textOf e width =
        let spaces = Prelude.replicate width '\SP'  in
        case e of
            E_BoolAST rng  b     -> out $ "BoolAST      " ++ (show b)
            E_CallAST rng b args -> out $ "CallAST      " ++ tryGetCallNameE b
            E_CompilesAST e c    -> out $ "CompilesAST  "
            E_IfAST _ _ _        -> out $ "IfAST        "
            E_IntAST rng text    -> out $ "IntAST       " ++ text
            E_FnAST f            -> out $ "FnAST        " ++ (prototypeASTname $ fnProto f)
            E_SeqAST   a b       -> out $ "SeqAST       "
            E_SubscriptAST  a b  -> out $ "SubscriptAST "
            E_TupleAST     es    -> out $ "TupleAST     "
            E_VarAST mt v        -> out $ "VarAST       " ++ v ++ " :: " ++ show mt
    childrenOf e =
        case e of
            E_BoolAST rng b      -> []
            E_CallAST rng b args -> b:args
            E_CompilesAST   e c  -> [e]
            E_IfAST a b c        -> [a, b, c]
            E_IntAST rng txt     -> []
            E_FnAST f            -> [fnBody f]
            E_SeqAST        a b  -> unbuildSeqs e
            E_SubscriptAST  a b  -> [a, b]
            E_TupleAST     es    -> es
            E_VarAST       mt v  -> []

instance Expr ExprAST where
    freeVars e = case e of
        E_VarAST mt nm      -> [nm]
        E_FnAST f           -> let bodyvars =  Set.fromList (freeVars (fnBody f)) in
                               let boundvars = Set.fromList (map (identPrefix.avarIdent) (prototypeASTformals (fnProto f))) in
                               Set.toList (Set.difference bodyvars boundvars)
        _                   -> concatMap freeVars (childrenOf e)


instance Structured AnnExpr where
    textOf e width =
        let spaces = Prelude.replicate width '\SP'  in
        case e of
            AnnBool         b    -> out $ "AnnBool      " ++ (show b)
            AnnCall  r t b args  -> out $ "AnnCall      " ++ " :: " ++ show t
            AnnCompiles c msg    -> out $ "AnnCompiles  " ++ show c ++ " - " ++ msg
            AnnIf      t  a b c  -> out $ "AnnIf        " ++ " :: " ++ show t
            AnnInt ty int        -> out $ "AnnInt       " ++ (litIntText int) ++ " :: " ++ show ty
            E_AnnFn annFn        -> out $ "AnnFn " ++ fnNameA annFn ++ " // " ++ (show $ annFnBoundNames annFn)
            AnnSeq          a b  -> out $ "AnnSeq       " ++ " :: " ++ show (typeAST b)
            AnnSubscript  t a b  -> out $ "AnnSubscript " ++ " :: " ++ show t
            AnnTuple     es      -> out $ "AnnTuple     "
            E_AnnVar (AnnVar t v) -> out $ "AnnVar       " ++ show v ++ " :: " ++ show t
            E_AnnTyApp t e argty -> out $ "AnnTyApp     [" ++ show argty ++ "] :: " ++ show t
    childrenOf e =
        case e of
            AnnBool         b                    -> []
            AnnCall  r t b args                  -> b:args
            AnnCompiles c msg                    -> []
            AnnIf      t  a b c                  -> [a, b, c]
            AnnInt t _                           -> []
            E_AnnFn annFn                        -> [annFnBody annFn]
            AnnSeq      a b                      -> unbuildSeqsA e
            AnnSubscript t a b                   -> [a, b]
            AnnTuple     es                      -> es
            E_AnnVar      v                      -> []
            E_AnnTyApp t e argty                 -> [e]

instance Expr AnnExpr where
    freeVars e = [identPrefix i | i <- freeIdentsA e]

freeIdentsA e = case e of
        E_AnnVar v      -> [avarIdent v]
        E_AnnFn f       -> let bodyvars =  freeIdentsA (annFnBody f) in
                           let boundvars = map avarIdent (annProtoVars (annFnProto f)) in
                           bodyvars `butnot` boundvars
        _               -> concatMap freeIdentsA (childrenOf e)


annFnBoundNames :: AnnFn -> [String]
annFnBoundNames fn =
    let vars = annProtoVars (annFnProto fn) in
    map show vars

