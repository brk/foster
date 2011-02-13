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
    textOf     :: a -> Int -> Output
    childrenOf :: a -> [a]
    freeVars   :: a -> [String]

tryGetCallNameE :: ExprAST -> String
tryGetCallNameE (E_VarAST mt v) = v
tryGetCallNameE _ = ""

instance Expr ExprAST where
    textOf e width =
        let spaces = Prelude.replicate width '\SP'  in
        case e of
            E_BoolAST rng  b     -> out $ "BoolAST      " ++ (show b)
            E_CallAST rng call   -> out $ "CallAST      " ++ tryGetCallNameE (callASTbase call)
            E_CompilesAST e c    -> out $ "CompilesAST  "
            E_IfAST _            -> out $ "IfAST        "
            E_IntAST litInt      -> out $ "IntAST       " ++ (litIntText litInt)
            E_FnAST f            -> out $ "FnAST        " ++ (prototypeASTname $ fnProto f)
            E_SeqAST   a b       -> out $ "SeqAST       "
            E_SubscriptAST  a b  -> out $ "SubscriptAST "
            E_TupleAST     es b  -> out $ "TupleAST     "
            E_VarAST mt v        -> out $ "VarAST       " ++ v ++ " :: " ++ show mt
    childrenOf e =
        case e of
            E_BoolAST rng b      -> []
            E_CallAST rng call   -> [callASTbase call, callASTargs call]
            E_CompilesAST   e c  -> [e]
            E_IfAST (IfAST a b c)-> [a, b, c]
            E_IntAST litInt      -> []
            E_FnAST f            -> [fnBody f]
            E_SeqAST        a b  -> unbuildSeqs e
            E_SubscriptAST  a b  -> [a, b]
            E_TupleAST     es b  -> es
            E_VarAST       mt v  -> []
    freeVars e = case e of
        E_VarAST mt nm      -> [nm]
        E_FnAST f           -> let bodyvars =  Set.fromList (freeVars (fnBody f)) in
                               let boundvars = Set.fromList (map (identPrefix.avarIdent) (prototypeASTformals (fnProto f))) in
                               Set.toList (Set.difference bodyvars boundvars)
        _                   -> concatMap freeVars (childrenOf e)


instance Expr AnnExpr where
    textOf e width =
        let spaces = Prelude.replicate width '\SP'  in
        case e of
            AnnBool         b    -> out $ "AnnBool      " ++ (show b)
            AnnCall  r t b a     -> out $ "AnnCall      " ++ " :: " ++ show t
            AnnCompiles c msg    -> out $ "AnnCompiles  " ++ show c ++ " - " ++ msg
            AnnIf      t  a b c  -> out $ "AnnIf        " ++ " :: " ++ show t
            AnnInt ty int        -> out $ "AnnInt       " ++ (litIntText int) ++ " :: " ++ show ty
            E_AnnFn annFn        -> out $ "AnnFn " ++ fnNameA annFn ++ " // " ++ (show $ annFnBoundNames annFn)
            AnnSeq          a b  -> out $ "AnnSeq       " ++ " :: " ++ show (typeAST b)
            AnnSubscript  t a b  -> out $ "AnnSubscript " ++ " :: " ++ show t
            AnnTuple     es b    -> out $ "AnnTuple     "
            E_AnnVar (AnnVar t v) -> out $ "AnnVar       " ++ show v ++ " :: " ++ show t
            E_AnnTyApp t e argty -> out $ "AnnTyApp     [" ++ show argty ++ "] :: " ++ show t
    childrenOf e =
        case e of
            AnnBool         b                    -> []
            AnnCall  r t b a                     -> [b, a]
            AnnCompiles c msg                    -> []
            AnnIf      t  a b c                  -> [a, b, c]
            AnnInt t _                           -> []
            E_AnnFn annFn                        -> [annFnBody annFn]
            AnnSeq      a b                      -> unbuildSeqsA e
            AnnSubscript t a b                   -> [a, b]
            AnnTuple     es b                    -> es
            E_AnnVar      v                      -> []
            E_AnnTyApp t e argty                 -> [e]
    freeVars e = [identPrefix i | i <- freeIdentsA e]

butnot :: Ord a => [a] -> [a] -> [a]
butnot bs zs =
    let sbs = Set.fromList bs in
    let szs = Set.fromList zs in
    Set.toList (Set.difference sbs szs)

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

data ModuleAST fnType = ModuleAST {
          moduleASTfunctions   :: [fnType]
        , moduleASTsourceLines :: SourceLines
     }

data CallAST = CallAST { callASTbase :: ExprAST
                       , callASTargs :: ExprAST
                       } deriving (Show)

data IfAST = IfAST { ifASTcond :: ExprAST
                   , ifASTthen :: ExprAST
                   , ifASTelse :: ExprAST } deriving (Show)

data ExprAST =
          E_BoolAST       ESourceRange Bool
        | E_IntAST        LiteralInt
        | E_TupleAST      { tupleParts :: [ExprAST]
                          , tupleIsEnv :: Bool }
        | E_FnAST         FnAST
        | E_CallAST       ESourceRange CallAST
        | E_CompilesAST   ExprAST CompilesStatus
        | E_IfAST         IfAST
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
        | AnnTuple      { annTupleParts :: [AnnExpr]
                        , annTupleIsEnv :: Bool }

        | E_AnnFn       AnnFn

        -- Add an overall type for the application
        | AnnCall       ESourceRange TypeAST AnnExpr AnnExpr

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

data AnnVar       = AnnVar { avarType :: TypeAST, avarIdent :: Ident } deriving (Eq, Show)

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
typeAST (AnnTuple es b)      = TupleTypeAST [typeAST e | e <- es]
typeAST (E_AnnFn annFn)      = annFnType annFn
typeAST (AnnCall r t b a)    = t
typeAST (AnnCompiles c msg)  = fosBoolType
typeAST (AnnIf t a b c)      = t
typeAST (AnnSeq a b)         = typeAST b
typeAST (AnnSubscript t _ _) = t
typeAST (E_AnnVar (AnnVar t s)) = t
typeAST (E_AnnTyApp substitutedTy tm tyArgs) = substitutedTy

-----------------------------------------------------------------------


