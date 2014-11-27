-----------------------------------------------------------------------------
-- Copyright (c) 2010 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.ExprAST(
  ExprAST, ExprSkel(..), exprAnnot
, FnAST(..)
, TypeFormal(..) -- TODO remove?
, TermBinding(..)
, termBindingName
)
where

import Foster.Base(Structured(..), Literal,
                   SourceRanged(..), TypedId(..), ArrayIndex(..),
                   AllocMemRegion, childrenOfArrayIndex, ArrayEntry,
                   CaseArm(..), caseArmExprs, EPattern(..), E_VarAST(..),
                   ExprAnnot(..), rangeOf, annotComments, showComments)
import Foster.Kind

import Text.PrettyPrint.ANSI.Leijen
import qualified Data.Text as T
import qualified Data.ByteString as B

-----------------------------------------------------------------------

type ExprAST ty = ExprSkel ExprAnnot ty

data ExprSkel annot ty =
        -- Literals
          E_StringAST     annot (Either T.Text B.ByteString)
        | E_BoolAST       annot Bool
        | E_IntAST        annot String
        | E_RatAST        annot String
        | E_TupleAST      annot [ExprAST ty]
        | E_FnAST         annot (FnAST ty)
        | E_MachArrayLit  annot (Maybe ty) [ArrayEntry (ExprAST ty)]
        -- Control flow
        | E_IfAST         annot (ExprAST ty) (ExprAST ty) (ExprAST ty)
        | E_SeqAST        annot (ExprAST ty) (ExprAST ty)
        -- Creation of bindings
        | E_Case          annot (ExprAST ty) [CaseArm EPattern (ExprAST ty) ty]
        | E_LetAST        annot (TermBinding ty) (ExprAST ty)
        | E_LetRec        annot [TermBinding ty] (ExprAST ty)
        -- Use of bindings
        | E_VarAST        annot (E_VarAST ty)
        | E_PrimAST       annot String [Literal] [ty]
        | E_CallAST       annot (ExprAST ty) [ExprAST ty]
        -- Mutable ref cells
        | E_AllocAST      annot (ExprAST ty) AllocMemRegion
        | E_DerefAST      annot (ExprAST ty)
        | E_StoreAST      annot (ExprAST ty) (ExprAST ty)
        -- Array subscripting
        | E_ArrayRead     annot (ArrayIndex (ExprAST ty))
        | E_ArrayPoke     annot (ArrayIndex (ExprAST ty)) (ExprAST ty)
        -- Terms indexed by types
        | E_TyApp         annot (ExprAST ty) [ty]
        -- Others
        | E_CompilesAST   annot (Maybe (ExprAST ty))
        | E_KillProcess   annot (ExprAST ty) -- arg must be string literal
        | E_TyCheck       annot (ExprAST ty) ty
        deriving Show

data FnAST ty  = FnAST { fnAstAnnot    :: ExprAnnot
                       , fnAstName     :: T.Text
                       , fnTyFormals   :: [TypeFormal]
                       , fnFormals     :: [TypedId ty]
                       , fnAstBody     :: ExprAST ty
                       , fnWasToplevel :: Bool
                       } deriving (Show)

data TermBinding ty = TermBinding (E_VarAST ty) (ExprAST ty) deriving (Show)

termBindingName :: TermBinding t -> T.Text
termBindingName (TermBinding v _) = evarName v

-- ||||||||||||||||||||||||| Instances ||||||||||||||||||||||||||{{{

instance Structured (ExprAST t) where
    textOf e _width =
        let tryGetCallNameE (E_VarAST _rng (VarAST _mt v)) = T.unpack v
            tryGetCallNameE _                              = "" in
        case e of
            E_StringAST _rng _s    -> text $ "StringAST    "                                   ++ (exprCmnts e)
            E_BoolAST   _rng  b    -> text $ "BoolAST      " ++ (show b)                       ++ (exprCmnts e)
            E_IntAST    _rng txt   -> text $ "IntAST       " ++ txt                            ++ (exprCmnts e)
            E_RatAST    _rng txt   -> text $ "RatAST       " ++ txt                            ++ (exprCmnts e)
            E_CallAST _rng b _args -> text $ "CallAST      " ++ tryGetCallNameE b              ++ (exprCmnts e)
            E_PrimAST _rng nm _ _  -> text $ "PrimAST      " ++ nm                             ++ (exprCmnts e)
            E_CompilesAST {}       -> text $ "CompilesAST  "                                   ++ (exprCmnts e)
            E_IfAST       {}       -> text $ "IfAST        "                                   ++ (exprCmnts e)
            E_FnAST    _rng f      -> text $ "FnAST        " ++ T.unpack (fnAstName f)         ++ (exprCmnts e)
            E_LetRec      {}       -> text $ "LetRec       "                                   ++ (exprCmnts e)
            E_LetAST   _rng bnd _  -> text $ "LetAST       " ++ T.unpack (termBindingName bnd) ++ (exprCmnts e)
            E_SeqAST      {}       -> text $ "SeqAST       "                                   ++ (exprCmnts e)
            E_AllocAST    {}       -> text $ "AllocAST     "                                   ++ (exprCmnts e)
            E_DerefAST    {}       -> text $ "DerefAST     "                                   ++ (exprCmnts e)
            E_StoreAST    {}       -> text $ "StoreAST     "                                   ++ (exprCmnts e)
            E_ArrayRead   {}       -> text $ "SubscriptAST "                                   ++ (exprCmnts e)
            E_ArrayPoke   {}       -> text $ "ArrayPokeAST "                                   ++ (exprCmnts e)
            E_TupleAST    {}       -> text $ "TupleAST     "                                   ++ (exprCmnts e)
            E_TyApp       {}       -> text $ "TyApp        "                                   ++ (exprCmnts e)
            E_Case        {}       -> text $ "Case         "                                   ++ (exprCmnts e)
            E_KillProcess {}       -> text $ "KillProcess  "                                   ++ (exprCmnts e)
            E_TyCheck     {}       -> text $ "TyCheck      "                                   ++ (exprCmnts e)
            E_VarAST _rng v        -> text $ "VarAST       " ++ T.unpack (evarName v)          ++ (exprCmnts e) -- ++ " :: " ++ show (pretty $ evarMaybeType v)
            E_MachArrayLit {}      -> text $ "MachArrayLit "                                   ++ (exprCmnts e)
    childrenOf e =
        let termBindingExpr (TermBinding _ e) = e in
        case e of
            E_StringAST   {}             -> []
            E_BoolAST     {}             -> []
            E_IntAST      {}             -> []
            E_RatAST      {}             -> []
            E_PrimAST     {}             -> []
            E_KillProcess {}             -> []
            E_VarAST      {}             -> []
            E_MachArrayLit {}     -> []
            E_CompilesAST _rng Nothing   -> []
            E_CompilesAST _rng (Just e)  -> [e]
            E_CallAST     _rng b exprs   -> b:exprs
            E_IfAST       _rng    a b c  -> [a, b, c]
            E_FnAST       _rng f         -> [fnAstBody f]
            E_SeqAST      _rng  _a _b    -> unbuildSeqs e
            E_AllocAST    _rng a _       -> [a]
            E_DerefAST    _rng a         -> [a]
            E_StoreAST    _rng a b       -> [a, b]
            E_ArrayRead   _rng ari       -> childrenOfArrayIndex ari
            E_ArrayPoke   _rng ari c     -> childrenOfArrayIndex ari ++ [c]
            E_TupleAST    _rng exprs     -> exprs
            E_TyApp       _rng a _t      -> [a]
            E_TyCheck     _rng a _t      -> [a]
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
      E_TupleAST      annot _     -> annot
      E_FnAST         annot _     -> annot
      E_LetAST        annot _ _   -> annot
      E_LetRec        annot _ _   -> annot
      E_PrimAST       annot _ _ _ -> annot
      E_CallAST       annot _ _   -> annot
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
      E_Case          annot _ _   -> annot
      E_MachArrayLit  annot _ _   -> annot

instance SourceRanged (ExprAST ty) where rangeOf e = rangeOf (exprAnnot e)

instance Pretty Kind where
  pretty KindAnySizeType = text "Type"
  pretty KindPointerSized = text "Boxed"
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

