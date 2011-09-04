-----------------------------------------------------------------------------
-- Copyright (c) 2010 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.ExprAST(
  ExprAST(..)
, FnAST(..)
, TupleAST(..)
, TermBinding(..)
)
where

import Foster.Base(SourceRange, Expr(..), freeVars, identPrefix, Structured(..),
                   SourceRanged(..), TypedId(..), butnot, out)
import Foster.TypeAST(TypeAST, EPattern(..), E_VarAST(..), AnnVar)

data ExprAST =
        -- Literals
          E_BoolAST       SourceRange Bool
        | E_IntAST        SourceRange String
        | E_TupleAST      TupleAST
        | E_FnAST         FnAST
        -- Control flow
        | E_IfAST         SourceRange ExprAST ExprAST ExprAST
        | E_UntilAST      SourceRange ExprAST ExprAST
        | E_SeqAST        SourceRange ExprAST ExprAST
        -- Creation of bindings
        | E_Case          SourceRange ExprAST [(EPattern, ExprAST)]
        | E_LetAST        SourceRange  TermBinding  ExprAST (Maybe TypeAST)
        | E_LetRec        SourceRange [TermBinding] ExprAST (Maybe TypeAST)
        -- Use of bindings
        | E_VarAST        SourceRange E_VarAST
        | E_CallAST       SourceRange ExprAST TupleAST
        -- Mutable ref cells
        | E_AllocAST      SourceRange ExprAST
        | E_DerefAST      SourceRange ExprAST
        | E_StoreAST      SourceRange ExprAST ExprAST
        -- Array subscripting
        | E_ArrayRead     SourceRange ExprAST ExprAST
        | E_ArrayPoke     SourceRange ExprAST ExprAST ExprAST
        -- Terms indexed by types
        | E_TyApp         SourceRange ExprAST TypeAST
        -- Others
        | E_CompilesAST   SourceRange (Maybe ExprAST)
        deriving Show

data TupleAST = TupleAST { tupleAstRange :: SourceRange
                         , tupleAstExprs :: [ExprAST] } deriving (Show)

data FnAST  = FnAST { fnAstRange :: SourceRange
                    , fnAstName  :: String
                    , fnTyFormals:: [String]
                    , fnRetType  :: Maybe TypeAST
                    , fnFormals  :: [AnnVar]
                    , fnAstBody  :: ExprAST
                    , fnWasToplevel :: Bool
                    } deriving (Show)

data TermBinding = TermBinding E_VarAST ExprAST
        deriving (Show)

-- | Converts a right-leaning "list" of SeqAST nodes to a List
unbuildSeqs :: ExprAST -> [ExprAST]
unbuildSeqs (E_SeqAST _rng a b) = a : unbuildSeqs b
unbuildSeqs expr = [expr]

-----------------------------------------------------------------------

instance Structured ExprAST where
    textOf e width =
        let spaces = Prelude.replicate width '\SP'  in
        let tryGetCallNameE (E_VarAST rng (VarAST mt v)) = v
            tryGetCallNameE _                            = "" in
        let termBindingName (TermBinding v _) = evarName v    in
        case e of
            E_BoolAST rng  b     -> out $ "BoolAST      " ++ (show b)
            E_CallAST rng b args -> out $ "CallAST      " ++ tryGetCallNameE b
            E_CompilesAST _rng _ -> out $ "CompilesAST  "
            E_IfAST _rng _ _ _   -> out $ "IfAST        "
            E_UntilAST _rng _ _  -> out $ "UntilAST     "
            E_IntAST rng text    -> out $ "IntAST       " ++ text
            E_FnAST f            -> out $ "FnAST        " ++ (fnAstName f)
            E_LetRec rnd bnz e t -> out $ "LetRec       "
            E_LetAST rng bnd e t -> out $ "LetAST       " ++ termBindingName bnd
            E_SeqAST _rng a b    -> out $ "SeqAST       "
            E_AllocAST rng a     -> out $ "AllocAST     "
            E_DerefAST rng a     -> out $ "DerefAST     "
            E_StoreAST rng a b   -> out $ "StoreAST     "
            E_ArrayRead r a b    -> out $ "SubscriptAST "
            E_ArrayPoke r a b c  -> out $ "ArrayPokeAST "
            E_TupleAST _         -> out $ "TupleAST     "
            E_TyApp rng a t      -> out $ "TyApp        "
            E_Case rng _ _       -> out $ "Case         "
            E_VarAST rng v       -> out $ "VarAST       " ++ evarName v ++ " :: " ++ show (evarMaybeType v)
    childrenOf e =
        let termBindingExpr (TermBinding _ e) = e
            termBindingExprs bs = map termBindingExpr bs
            termBindingNames bs = map (\(TermBinding v _) -> evarName v) bs
        in case e of
            E_BoolAST rng b             -> []
            E_CallAST rng b tup         -> b:(tupleAstExprs tup)
            E_CompilesAST _rng (Just e) -> [e]
            E_CompilesAST _rng Nothing  -> []
            E_IfAST _rng    a b c       -> [a, b, c]
            E_UntilAST _rng a b         -> [a, b]
            E_IntAST rng txt            -> []
            E_FnAST f                   -> [fnAstBody f]
            E_SeqAST _rng  a b          -> unbuildSeqs e
            E_AllocAST rng a            -> [a]
            E_DerefAST rng a            -> [a]
            E_StoreAST rng a b          -> [a, b]
            E_ArrayRead r a b           -> [a, b]
            E_ArrayPoke r a b c         -> [a, b, c]
            E_TupleAST tup              -> tupleAstExprs tup
            E_TyApp  rng a t            -> [a]
            E_Case rng e bs             -> e:(map snd bs)
            E_VarAST _ _                -> []
            E_LetRec rnd bnz e t        -> [termBindingExpr bnd | bnd <- bnz] ++ [e]
            E_LetAST rng bnd e t        -> (termBindingExpr bnd):[e]

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
      E_ArrayRead     rng _ _   -> rng
      E_ArrayPoke     rng _ _ _ -> rng
      E_VarAST        rng _     -> rng
      E_TyApp         rng _ _   -> rng
      E_Case          rng _ _   -> rng

instance Expr ExprAST where
  freeVars e = case e of
    E_VarAST rng v       -> [evarName v]
    E_LetAST rng bnd e t -> let bindingFreeVars (TermBinding v e) =
                                 freeVars e `butnot` [evarName v]
                             in  freeVars e ++ (bindingFreeVars bnd)
    E_Case rng e epatbnds -> freeVars e ++ (concatMap epatBindingFreeVars epatbnds)
    E_FnAST f           -> let bodyvars  = freeVars (fnAstBody f) in
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
            EP_Ctor     _rng pats nm -> []
            EP_Bool     _rng _    -> []
            EP_Int      _rng _    -> []
            EP_Tuple    _rng pats -> concatMap epatBoundNames pats


