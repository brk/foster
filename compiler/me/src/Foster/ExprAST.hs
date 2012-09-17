-----------------------------------------------------------------------------
-- Copyright (c) 2010 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.ExprAST(
  ExprAST, ExprSkel(..)
, FnAST(..)
, TypeFormalAST(..)
, TermBinding(..)
, termBindingName
)
where

import Foster.Base(SourceRange, Expr(..), freeVars, identPrefix, Structured(..),
                   SourceRanged(..), TypedId(..), butnot, ArrayIndex(..),
                   AllocMemRegion, childrenOfArrayIndex)
import Foster.TypeAST(TypeAST, EPattern(..), E_VarAST(..))
import Foster.Kind

import Text.PrettyPrint.ANSI.Leijen(text, pretty)
import qualified Data.Text as T

-----------------------------------------------------------------------

type ExprAST ty = ExprSkel SourceRange ty

data ExprSkel annot ty =
        -- Literals
          E_StringAST     annot T.Text
        | E_BoolAST       annot Bool
        | E_IntAST        annot String
        | E_RatAST        annot String
        | E_TupleAST      annot [ExprAST ty]
        | E_FnAST         annot (FnAST ty)
        -- Control flow
        | E_IfAST         annot (ExprAST ty) (ExprAST ty) (ExprAST ty)
        | E_UntilAST      annot (ExprAST ty) (ExprAST ty)
        | E_SeqAST        annot (ExprAST ty) (ExprAST ty)
        -- Creation of bindings
        | E_Case          annot (ExprAST ty) [(EPattern ty, ExprAST ty)]
        | E_LetAST        annot (TermBinding ty) (ExprAST ty)
        | E_LetRec        annot [TermBinding ty] (ExprAST ty)
        -- Use of bindings
        | E_VarAST        annot (E_VarAST ty)
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
        deriving Show

data FnAST ty  = FnAST { fnAstRange    :: SourceRange
                       , fnAstName     :: T.Text
                       , fnTyFormals   :: [TypeFormalAST]
                       , fnFormals     :: [TypedId ty]
                       , fnAstBody     :: ExprAST ty
                       , fnWasToplevel :: Bool
                       } deriving (Show)

data TermBinding ty = TermBinding (E_VarAST ty) (ExprAST ty) deriving (Show)

termBindingName :: TermBinding t -> T.Text
termBindingName (TermBinding v _) = evarName v

-- ||||||||||||||||||||||||| Instances ||||||||||||||||||||||||||{{{

instance Structured (ExprAST TypeAST) where
    textOf e _width =
        let tryGetCallNameE (E_VarAST _rng (VarAST _mt v)) = T.unpack v
            tryGetCallNameE _                              = "" in
        case e of
            E_StringAST _rng _s    -> text $ "StringAST    "
            E_BoolAST   _rng  b    -> text $ "BoolAST      " ++ (show b)
            E_IntAST    _rng txt   -> text $ "IntAST       " ++ txt
            E_RatAST    _rng txt   -> text $ "RatAST       " ++ txt
            E_CallAST _rng b _args -> text $ "CallAST      " ++ tryGetCallNameE b
            E_CompilesAST {}       -> text $ "CompilesAST  "
            E_IfAST       {}       -> text $ "IfAST        "
            E_UntilAST _rng _ _    -> text $ "UntilAST     "
            E_FnAST    _rng f      -> text $ "FnAST        " ++ T.unpack (fnAstName f)
            E_LetRec      {}       -> text $ "LetRec       "
            E_LetAST   _rng bnd _  -> text $ "LetAST       " ++ T.unpack (termBindingName bnd)
            E_SeqAST      {}       -> text $ "SeqAST       "
            E_AllocAST    {}       -> text $ "AllocAST     "
            E_DerefAST    {}       -> text $ "DerefAST     "
            E_StoreAST    {}       -> text $ "StoreAST     "
            E_ArrayRead   {}       -> text $ "SubscriptAST "
            E_ArrayPoke   {}       -> text $ "ArrayPokeAST "
            E_TupleAST    {}       -> text $ "TupleAST     "
            E_TyApp       {}       -> text $ "TyApp        "
            E_Case        {}       -> text $ "Case         "
            E_KillProcess {}       -> text $ "KillProcess  "
            E_VarAST _rng v        -> text $ "VarAST       " ++ T.unpack (evarName v) ++ " :: " ++ show (pretty $ evarMaybeType v)
    childrenOf e =
        let termBindingExpr (TermBinding _ e) = e in
        case e of
            E_StringAST   _rng _s        -> []
            E_BoolAST     _rng _b        -> []
            E_IntAST      _rng _txt      -> []
            E_RatAST      _rng _txt      -> []
            E_CallAST     _rng b exprs   -> b:exprs
            E_CompilesAST _rng (Just e)  -> [e]
            E_CompilesAST _rng Nothing   -> []
            E_KillProcess _rng _         -> []
            E_IfAST       _rng    a b c  -> [a, b, c]
            E_UntilAST    _rng a b       -> [a, b]
            E_FnAST       _rng f         -> [fnAstBody f]
            E_SeqAST      _rng  _a _b    -> unbuildSeqs e
            E_AllocAST    _rng a _       -> [a]
            E_DerefAST    _rng a         -> [a]
            E_StoreAST    _rng a b       -> [a, b]
            E_ArrayRead   _rng ari       -> childrenOfArrayIndex ari
            E_ArrayPoke   _rng ari c     -> childrenOfArrayIndex ari ++ [c]
            E_TupleAST    _rng exprs     -> exprs
            E_TyApp       _rng a _t      -> [a]
            E_Case        _rng e bs      -> e:(map snd bs)
            E_VarAST      _rng _         -> []
            E_LetRec      _rng bnz e     -> [termBindingExpr bnd | bnd <- bnz] ++ [e]
            E_LetAST      _rng bnd e     -> (termBindingExpr bnd):[e]
       where     -- | Converts a right-leaning "list" of SeqAST nodes to a List
                unbuildSeqs :: (ExprAST ty) -> [ExprAST ty]
                unbuildSeqs (E_SeqAST _rng a b) = a : unbuildSeqs b
                unbuildSeqs expr = [expr]

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
      E_CallAST       annot _ _   -> annot
      E_CompilesAST   annot _     -> annot
      E_KillProcess   annot _     -> annot
      E_IfAST         annot _ _ _ -> annot
      E_UntilAST      annot _ _   -> annot
      E_SeqAST        annot _ _   -> annot
      E_AllocAST      annot _ _   -> annot
      E_DerefAST      annot _     -> annot
      E_StoreAST      annot _ _   -> annot
      E_ArrayRead     annot _     -> annot
      E_ArrayPoke     annot _ _   -> annot
      E_VarAST        annot _     -> annot
      E_TyApp         annot _ _   -> annot
      E_Case          annot _ _   -> annot

instance SourceRanged (ExprAST ty) where rangeOf e = exprAnnot e

-- The free-variable determination logic here is tested in
--      test/bootstrap/testcases/rec-fn-detection
instance Expr (ExprAST TypeAST) where
  freeVars e = case e of
    E_LetAST _rng (TermBinding v b) e ->
                                freeVars b ++ (freeVars e `butnot` [evarName v])
    E_LetRec _rng nest _ -> concatMap freeVars (childrenOf e) `butnot`
                                          [evarName v | TermBinding v _ <- nest]
    E_Case _rng e pbinds -> freeVars e ++ (concatMap epatBindingFreeVars pbinds)
    E_FnAST _rng f       -> let bodyvars  = freeVars (fnAstBody f) in
                            let boundvars = map (identPrefix.tidIdent) (fnFormals f) in
                            bodyvars `butnot` boundvars
    E_VarAST _rng v      -> [evarName v]
    _                    -> concatMap freeVars (childrenOf e)

epatBindingFreeVars (pat, expr) =
  freeVars expr `butnot` epatBoundNames pat
  where epatBoundNames :: EPattern ty -> [T.Text]
        epatBoundNames pat =
          case pat of
            EP_Wildcard {}        -> []
            EP_Variable _rng evar -> [evarName evar]
            EP_Ctor     {}        -> []
            EP_Bool     {}        -> []
            EP_Int      {}        -> []
            EP_Tuple    _rng pats -> concatMap epatBoundNames pats

-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

