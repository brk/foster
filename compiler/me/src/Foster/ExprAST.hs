-----------------------------------------------------------------------------
-- Copyright (c) 2010 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.ExprAST(
  ExprAST(..)
, FnAST(..)
, TupleAST(..)
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
import Foster.Output(out)

import qualified Data.Text as T

-----------------------------------------------------------------------

data ExprAST ty =
        -- Literals
          E_StringAST     SourceRange T.Text
        | E_BoolAST       SourceRange Bool
        | E_IntAST        SourceRange String
        | E_RatAST        SourceRange String
        | E_TupleAST      (TupleAST ty)
        | E_FnAST         (FnAST ty)
        -- Control flow
        | E_IfAST         SourceRange (ExprAST ty) (ExprAST ty) (ExprAST ty)
        | E_UntilAST      SourceRange (ExprAST ty) (ExprAST ty)
        | E_SeqAST        SourceRange (ExprAST ty) (ExprAST ty)
        -- Creation of bindings
        | E_Case          SourceRange (ExprAST ty) [(EPattern ty, ExprAST ty)]
        | E_LetAST        SourceRange (TermBinding ty) (ExprAST ty)
        | E_LetRec        SourceRange [TermBinding ty] (ExprAST ty)
        -- Use of bindings
        | E_VarAST        SourceRange (E_VarAST ty)
        | E_CallAST       SourceRange (ExprAST ty) (TupleAST ty)
        -- Mutable ref cells
        | E_AllocAST      SourceRange (ExprAST ty) AllocMemRegion
        | E_DerefAST      SourceRange (ExprAST ty)
        | E_StoreAST      SourceRange (ExprAST ty) (ExprAST ty)
        -- Array subscripting
        | E_ArrayRead     SourceRange (ArrayIndex (ExprAST ty))
        | E_ArrayPoke     SourceRange (ArrayIndex (ExprAST ty)) (ExprAST ty)
        -- Terms indexed by types
        | E_TyApp         SourceRange (ExprAST ty) [ty]
        -- Others
        | E_CompilesAST   SourceRange (Maybe (ExprAST ty))
        | E_KillProcess   SourceRange (ExprAST ty) -- arg must be string literal
        deriving Show

data TupleAST ty = TupleAST { tupleAstRange :: SourceRange
                            , tupleAstExprs :: [ExprAST ty] } deriving (Show)

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
            E_StringAST _rng _s    -> out $ "StringAST    "
            E_BoolAST   _rng  b    -> out $ "BoolAST      " ++ (show b)
            E_IntAST _rng text     -> out $ "IntAST       " ++ text
            E_RatAST _rng text     -> out $ "RatAST       " ++ text
            E_CallAST _rng b _args -> out $ "CallAST      " ++ tryGetCallNameE b
            E_CompilesAST {}       -> out $ "CompilesAST  "
            E_IfAST       {}       -> out $ "IfAST        "
            E_UntilAST _rng _ _    -> out $ "UntilAST     "
            E_FnAST f              -> out $ "FnAST        " ++ T.unpack (fnAstName f)
            E_LetRec    {}         -> out $ "LetRec       "
            E_LetAST _rng bnd _    -> out $ "LetAST       " ++ T.unpack (termBindingName bnd)
            E_SeqAST    {}         -> out $ "SeqAST       "
            E_AllocAST  {}         -> out $ "AllocAST     "
            E_DerefAST  {}         -> out $ "DerefAST     "
            E_StoreAST  {}         -> out $ "StoreAST     "
            E_ArrayRead {}         -> out $ "SubscriptAST "
            E_ArrayPoke {}         -> out $ "ArrayPokeAST "
            E_TupleAST  {}         -> out $ "TupleAST     "
            E_TyApp     {}         -> out $ "TyApp        "
            E_Case      {}         -> out $ "Case         "
            E_KillProcess {}       -> out $ "KillProcess  "
            E_VarAST _rng v        -> out $ "VarAST       " ++ T.unpack (evarName v) ++ " :: " ++ show (evarMaybeType v)
    childrenOf e =
        let termBindingExpr (TermBinding _ e) = e in
        case e of
            E_StringAST   _rng _s        -> []
            E_BoolAST     _rng _b        -> []
            E_IntAST      _rng _txt      -> []
            E_RatAST      _rng _txt      -> []
            E_CallAST     _rng b tup     -> b:(tupleAstExprs tup)
            E_CompilesAST _rng (Just e)  -> [e]
            E_CompilesAST _rng Nothing   -> []
            E_KillProcess _rng _         -> []
            E_IfAST       _rng    a b c  -> [a, b, c]
            E_UntilAST    _rng a b       -> [a, b]
            E_FnAST f                    -> [fnAstBody f]
            E_SeqAST      _rng  _a _b    -> unbuildSeqs e
            E_AllocAST    _rng a _       -> [a]
            E_DerefAST    _rng a         -> [a]
            E_StoreAST    _rng a b       -> [a, b]
            E_ArrayRead   _rng ari       -> childrenOfArrayIndex ari
            E_ArrayPoke   _rng ari c     -> childrenOfArrayIndex ari ++ [c]
            E_TupleAST tup               -> tupleAstExprs tup
            E_TyApp       _rng a _t      -> [a]
            E_Case        _rng e bs      -> e:(map snd bs)
            E_VarAST      _rng _         -> []
            E_LetRec      _rng bnz e     -> [termBindingExpr bnd | bnd <- bnz] ++ [e]
            E_LetAST      _rng bnd e     -> (termBindingExpr bnd):[e]
       where     -- | Converts a right-leaning "list" of SeqAST nodes to a List
                unbuildSeqs :: (ExprAST ty) -> [ExprAST ty]
                unbuildSeqs (E_SeqAST _rng a b) = a : unbuildSeqs b
                unbuildSeqs expr = [expr]

instance SourceRanged (ExprAST ty)
  where
    rangeOf e = case e of
      E_StringAST     rng _ -> rng
      E_BoolAST       rng _ -> rng
      E_IntAST        rng _ -> rng
      E_RatAST        rng _ -> rng
      E_TupleAST    tup -> tupleAstRange tup
      E_FnAST         f -> fnAstRange f
      E_LetAST        rng _ _   -> rng
      E_LetRec        rng _ _   -> rng
      E_CallAST       rng _ _   -> rng
      E_CompilesAST   rng _     -> rng
      E_KillProcess   rng _     -> rng
      E_IfAST         rng _ _ _ -> rng
      E_UntilAST      rng _ _   -> rng
      E_SeqAST        rng _ _   -> rng
      E_AllocAST      rng _ _   -> rng
      E_DerefAST      rng _     -> rng
      E_StoreAST      rng _ _   -> rng
      E_ArrayRead     rng _     -> rng
      E_ArrayPoke     rng _ _   -> rng
      E_VarAST        rng _     -> rng
      E_TyApp         rng _ _   -> rng
      E_Case          rng _ _   -> rng

instance Expr (ExprAST TypeAST) where
  freeVars e = case e of
    E_VarAST _rng v        -> [evarName v]
    E_LetAST _rng bnd e    -> let bindingFreeVars (TermBinding v e) =
                                   freeVars e `butnot` [evarName v]
                               in  freeVars e ++ (bindingFreeVars bnd)
    E_Case _rng e epatbnds -> freeVars e ++ (concatMap epatBindingFreeVars epatbnds)
    E_FnAST f           -> let bodyvars  = freeVars (fnAstBody f) in
                           let boundvars = map (identPrefix.tidIdent) (fnFormals f) in
                           bodyvars `butnot` boundvars
    _                   -> concatMap freeVars (childrenOf e)

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

