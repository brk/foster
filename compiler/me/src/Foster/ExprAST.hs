-----------------------------------------------------------------------------
-- Copyright (c) 2010 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.ExprAST(
  ExprAST, ModuleExpr, ExprSkel(..), exprAnnot
, FnAST(..), moduleASTfunctions, moduleASTnonfndefs
, SourceString(..), StringRawFlag(..)
, TermBinding(..)
, termBindingName
)
where

import Foster.Base(Structured(..), Summarizable(..), Literal, TypeFormal,
                   ToplevelItem(..), ModuleAST(..), CallAnnot, CallFlavor,
                   TypedId(..), ArrayIndex(..),
                   AllocMemRegion, childrenOfArrayIndex, ArrayEntry(..),
                   CaseArm(..), caseArmExprs, EPattern(..), E_VarAST(..),
                   ExprAnnot(..), annotComments, showComments)
import Foster.Kind
import Foster.SourceRange(SourceRanged, rangeOf)

import Data.Maybe(maybeToList)
import Prettyprinter
import qualified Data.Text as T
import qualified Data.ByteString as B

-----------------------------------------------------------------------

type ExprAST ty = ExprSkel ExprAnnot ty
type ModuleExpr ty = ModuleAST (ExprSkel ExprAnnot) ty
data StringRawFlag = YesRaw | NotRaw deriving (Eq, Show)
data SourceString = SS_Text  StringRawFlag T.Text
                  | SS_Bytes StringRawFlag B.ByteString
                  deriving (Eq, Show)

data ExprSkel annot ty =
        -- Literals
          E_StringAST     annot SourceString
        | E_BoolAST       annot Bool
        | E_IntAST        annot T.Text
        | E_RatAST        annot T.Text
        | E_TupleAST      annot Kind [ExprSkel annot ty]
        | E_RecordAST     annot [T.Text] [ExprSkel annot ty]
        | E_FnAST         annot (FnAST ty)
        | E_MachArrayLit  annot (Maybe ty) [ArrayEntry (ExprSkel annot ty)]
        -- Control flow
        | E_IfAST         annot (ExprSkel annot ty) (ExprSkel annot ty) (ExprSkel annot ty)
        | E_SeqAST        annot (ExprSkel annot ty) (ExprSkel annot ty)
        | E_Handler       annot (ExprSkel annot ty) [CaseArm EPattern (ExprSkel annot ty) ty]
                                                    (Maybe (ExprSkel annot ty))
        -- Creation of bindings
        | E_Case          annot (ExprSkel annot ty) [CaseArm EPattern (ExprSkel annot ty) ty]
        | E_LetAST        annot (TermBinding ty) (ExprSkel annot ty)
        | E_LetRec        annot [TermBinding ty] (ExprSkel annot ty)
        -- Use of bindings
        | E_VarAST        annot (E_VarAST ty)
        | E_CallPrimAST   annot T.Text [Literal] [ty] [ExprSkel annot ty]
        | E_CallAST       annot (ExprSkel annot ty) [ExprSkel annot ty] CallAnnot CallFlavor
        -- Mutable ref cells
        | E_AllocAST      annot (ExprSkel annot ty) AllocMemRegion
        | E_DerefAST      annot (ExprSkel annot ty)
        | E_StoreAST      annot (ExprSkel annot ty) (ExprSkel annot ty)
        -- Array subscripting
        | E_ArrayRead     annot (ArrayIndex (ExprSkel annot ty))
        | E_ArrayPoke     annot (ArrayIndex (ExprSkel annot ty)) (ExprSkel annot ty)
        -- Terms indexed by types
        | E_TyApp         annot (ExprSkel annot ty) [ty]
        -- Others
        | E_CompilesAST   annot (Maybe (ExprSkel annot ty))
        | E_KillProcess   annot (ExprSkel annot ty) -- arg must be string literal
        | E_TyCheck       annot (ExprSkel annot ty) ty
        deriving Show

data FnAST ty  = FnAST { fnAstAnnot    :: ExprAnnot
                       , fnAstName     :: T.Text
                       , fnTyFormals   :: [TypeFormal]
                       , fnFormals     :: [TypedId ty]
                       , fnAstBody     :: ExprAST ty
                       , fnWasToplevel :: Bool
                       } deriving (Show)

moduleASTfunctions :: ModuleExpr ty -> [FnAST ty]
moduleASTfunctions m = [fn | ToplevelDefn (_, E_FnAST _ fn) <- moduleASTitems m]

moduleASTnonfndefs :: ModuleExpr ty -> [TermBinding ty]
moduleASTnonfndefs m = concat [case expr of
                                 E_FnAST {} -> []
                                 _          -> [TermBinding (VarAST Nothing name) expr]
                              | ToplevelDefn (name, expr) <- moduleASTitems m]


data TermBinding ty = TermBinding (E_VarAST ty) (ExprAST ty) deriving (Show)

termBindingName :: TermBinding t -> T.Text
termBindingName (TermBinding v _) = evarName v

-- ||||||||||||||||||||||||| Instances ||||||||||||||||||||||||||{{{

string :: String -> Doc a
string s = pretty s

showSome (SS_Text  _raw txt) = take 40 $ show txt
showSome (SS_Bytes _raw bs)  = take 40 $ show bs

instance Summarizable (ExprAST t) where
    textOf e _width =
        let tryGetCallNameE (E_VarAST _rng (VarAST _mt v)) = T.unpack v
            tryGetCallNameE _                              = "" in
        case e of
            E_StringAST _rng  _s   -> string $ "StringAST    " ++ (showSome _s)                  ++ (exprCmnts e)
            E_BoolAST   _rng  b    -> string $ "BoolAST      " ++ (show b)                       ++ (exprCmnts e)
            E_IntAST    _rng txt   -> string $ "IntAST       " ++ T.unpack txt                            ++ (exprCmnts e)
            E_RatAST    _rng txt   -> string $ "RatAST       " ++ T.unpack txt                            ++ (exprCmnts e)
            E_CallAST _rng b _ _ _ -> string $ "CallAST      " ++ tryGetCallNameE b              ++ (exprCmnts e)
            E_CallPrimAST _rng nm _ _ _
                                   -> string $ "CallPrimAST  " ++ T.unpack nm                             ++ (exprCmnts e)
            E_CompilesAST {}       -> string $ "CompilesAST  "                                   ++ (exprCmnts e)
            E_IfAST       {}       -> string $ "IfAST        "                                   ++ (exprCmnts e)
            E_FnAST    _rng f      -> string $ "FnAST        " ++ T.unpack (fnAstName f)         ++ (exprCmnts e)
            E_LetRec      {}       -> string $ "LetRec       "                                   ++ (exprCmnts e)
            E_LetAST   _rng bnd _  -> string $ "LetAST       " ++ T.unpack (termBindingName bnd) ++ (exprCmnts e)
            E_SeqAST      {}       -> string $ "SeqAST       "                                   ++ (exprCmnts e)
            E_AllocAST    {}       -> string $ "AllocAST     "                                   ++ (exprCmnts e)
            E_DerefAST    {}       -> string $ "DerefAST     "                                   ++ (exprCmnts e)
            E_StoreAST    {}       -> string $ "StoreAST     "                                   ++ (exprCmnts e)
            E_ArrayRead   {}       -> string $ "SubscriptAST "                                   ++ (exprCmnts e)
            E_ArrayPoke   {}       -> string $ "ArrayPokeAST "                                   ++ (exprCmnts e)
            E_RecordAST _ labs _   -> string $ "RecordAST " ++ show labs                         ++ (exprCmnts e)
            E_TupleAST    {}       -> string $ "TupleAST     "                                   ++ (exprCmnts e)
            E_TyApp       {}       -> string $ "TyApp        "                                   ++ (exprCmnts e)
            E_Handler     {}       -> string $ "Handler      "                                   ++ (exprCmnts e)
            E_Case        {}       -> string $ "Case         "                                   ++ (exprCmnts e)
            E_KillProcess {}       -> string $ "KillProcess  "                                   ++ (exprCmnts e)
            E_TyCheck     {}       -> string $ "TyCheck      "                                   ++ (exprCmnts e)
            E_VarAST _rng v        -> string $ "VarAST       " ++ T.unpack (evarName v)          ++ (exprCmnts e) -- ++ " :: " ++ show (pretty $ evarMaybeType v)
            E_MachArrayLit {}      -> string $ "MachArrayLit "                                   ++ (exprCmnts e)

instance Structured (ExprAST t) where
    childrenOf e =
        let termBindingExpr (TermBinding _ e) = e in
        case e of
            E_StringAST   {}             -> []
            E_BoolAST     {}             -> []
            E_IntAST      {}             -> []
            E_RatAST      {}             -> []
            E_KillProcess {}             -> []
            E_VarAST      {}             -> []
            E_MachArrayLit _rng _ty entries -> [e | AE_Expr e <- entries]
            E_CompilesAST _rng Nothing   -> []
            E_CompilesAST _rng (Just e)  -> [e]
            E_CallAST     _rng b exprs _ _ -> b:exprs
            E_CallPrimAST  _rng _nm _ls _ts exprs -> exprs
            E_IfAST       _rng    a b c  -> [a, b, c]
            E_FnAST       _rng f         -> [fnAstBody f]
            E_SeqAST      _rng  _a _b    -> unbuildSeqs e
            E_AllocAST    _rng a _       -> [a]
            E_DerefAST    _rng a         -> [a]
            E_StoreAST    _rng a b       -> [a, b]
            E_ArrayRead   _rng ari       -> childrenOfArrayIndex ari
            E_ArrayPoke   _rng ari c     -> childrenOfArrayIndex ari ++ [c]
            E_RecordAST   _rng _ exprs   -> exprs
            E_TupleAST    _rng _ exprs   -> exprs
            E_TyApp       _rng a _t      -> [a]
            E_TyCheck     _rng a _t      -> [a]
            E_Handler     _rng e bs mbe  -> (maybeToList mbe) ++ e:(concatMap caseArmExprs bs)
            E_Case        _rng e bs      -> e:(concatMap caseArmExprs bs)
            E_LetRec      _rng bnz e     -> [termBindingExpr bnd | bnd <- bnz] ++ [e]
            E_LetAST      _rng bnd e     -> (termBindingExpr bnd):[e]
       where     -- | Converts a right-leaning "list" of SeqAST nodes to a List
                unbuildSeqs :: (ExprAST ty) -> [ExprAST ty]
                unbuildSeqs (E_SeqAST _rng a b) = a : unbuildSeqs b
                unbuildSeqs expr = [expr]

exprCmnts e = showComments $ annotComments (exprAnnot e)

exprAnnot :: ExprSkel annot ty -> annot
exprAnnot e = case e of
      E_StringAST     annot _     -> annot
      E_BoolAST       annot _     -> annot
      E_IntAST        annot _     -> annot
      E_RatAST        annot _     -> annot
      E_RecordAST     annot _ _   -> annot
      E_TupleAST      annot _ _   -> annot
      E_FnAST         annot _     -> annot
      E_LetAST        annot _ _   -> annot
      E_LetRec        annot _ _   -> annot
      E_CallPrimAST   ann _ _ _ _ -> ann
      E_CallAST       annot _ _ _ _ -> annot
      E_CompilesAST   annot _     -> annot
      E_KillProcess   annot _     -> annot
      E_IfAST         annot _ _ _ -> annot
      E_SeqAST        annot _ _   -> annot
      E_AllocAST      annot _ _   -> annot
      E_DerefAST      annot _     -> annot
      E_StoreAST      annot _ _   -> annot
      E_ArrayRead     annot _     -> annot
      E_ArrayPoke     annot _ _   -> annot
      E_VarAST        annot _     -> annot
      E_TyApp         annot _ _   -> annot
      E_TyCheck       annot _ _   -> annot
      E_Handler       annot _ _ _ -> annot
      E_Case          annot _ _   -> annot
      E_MachArrayLit  annot _ _   -> annot

instance SourceRanged (ExprAST ty) where rangeOf e = rangeOf (exprAnnot e)
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

