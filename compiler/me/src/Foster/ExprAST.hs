-----------------------------------------------------------------------------
-- Copyright (c) 2010 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.ExprAST where

import Foster.TypeAST
import Data.Int
import Data.Sequence as Seq
import Data.Maybe(fromJust)
import Data.List(replicate)
import qualified Data.Text as T


data CompilesStatus = CS_WouldCompile | CS_WouldNotCompile | CS_NotChecked
    deriving Show

data ESourceLocation = ESourceLocation Int Int
    deriving (Show)

data ESourceRange = ESourceRange ESourceLocation ESourceLocation SourceLines
                  | EMissingSourceRange

instance Show ESourceRange where
    show = showSourceRange

showSourceRange :: ESourceRange -> String
showSourceRange EMissingSourceRange = ""
showSourceRange (ESourceRange begin end lines) = showSourceLines begin end lines

showSourceLines (ESourceLocation bline bcol) (ESourceLocation eline ecol) lines =
    if bline == eline
        then joinWith "\n" [fromJust $ sourceLine lines bline, highlightLineRange bcol ecol]
        else joinWith "\n" [fromJust $ sourceLine lines n | n <- [bline..eline]]

highlightLineRange :: Int -> Int -> String
highlightLineRange bcol ecol =
    let len = ecol - bcol in
    if len <= 0
        then ""
        else (Data.List.replicate bcol ' ') ++ (Data.List.replicate len '~')

data SourceLines = SourceLines (Seq T.Text)

data ModuleAST fnType = ModuleAST {
          moduleASTfunctions   :: [fnType]
        , moduleASTsourceLines :: SourceLines
     }

data ExprAST =
          BoolAST       Bool
        | IntAST        { eintActive :: Integer
                        , eintText   :: String
                        , eintClean  :: String
                        , eintBase   :: Int }
                        -- parts  is_env_tuple
        | TupleAST      [ExprAST] Bool
        | E_FnAST       FnAST

        | CallAST       ESourceRange ExprAST ExprAST
        | CompilesAST   ExprAST CompilesStatus
        | IfAST         ExprAST ExprAST ExprAST
        | SeqAST        ExprAST ExprAST
        | SubscriptAST  ExprAST ExprAST
        | E_PrototypeAST    PrototypeAST
        | VarAST        (Maybe TypeAST) String
        deriving Show

                          -- proto    body
data FnAST  = FnAST     PrototypeAST ExprAST deriving (Show)
data PrototypeAST = PrototypeAST {
                          prototypeASTretType :: TypeAST
                        , prototypeASTname    :: String
                        , prototypeASTformals :: [AnnVar] } deriving (Show)


sourceLine :: SourceLines -> Int -> Maybe String
sourceLine (SourceLines seq) n =
    if n < 0 || Seq.length seq < n
        then Nothing
        else Just (T.unpack $ Seq.index seq n)


-- Builds trees like this:
--
--
showStructure :: ExprAST -> String
showStructure e = showStructureP e "" False where
    showStructureP e prefix isLast =
        let children = childrenOf e in
        let thisIndent = prefix ++ if isLast then "└─" else "├─" in
        let nextIndent = prefix ++ if isLast then "  " else "│ " in
        let padding = max 6 (60 - Prelude.length thisIndent) in
        -- [ (child, index, numchildren) ]
        let childpairs = Prelude.zip3 children [1..]
                               (Prelude.repeat (Prelude.length children)) in
        let childlines = map (\(c, n, l) ->
                                showStructureP c nextIndent (n == l))
                             childpairs in
        thisIndent ++ (textOf e padding ++ "\n") ++ Prelude.foldl (++) "" childlines


childrenOf :: ExprAST -> [ExprAST]
childrenOf e =
    case e of
        BoolAST         b    -> []
        CallAST   r b es     -> [b, es]
        CompilesAST   e c    -> [e]
        IfAST         a b c  -> [a, b, c]
        IntAST i s1 s2 i2    -> []
        E_FnAST (FnAST a b)  -> [E_PrototypeAST a, b]
        SeqAST      a b      -> unbuildSeqs e
        SubscriptAST  a b    -> [a, b]
        E_PrototypeAST (PrototypeAST t s es) -> (map (\(AnnVar t s) -> VarAST (Just t) s) es)
        TupleAST     es b    -> es
        VarAST       mt v    -> []

-- | Converts a right-leaning "list" of SeqAST nodes to a List
unbuildSeqs :: ExprAST -> [ExprAST]
unbuildSeqs (SeqAST a b) = a : unbuildSeqs b
unbuildSeqs expr = [expr]


-- Formats a single-line tag for the given ExprAST node.
-- Example:  textOf (VarAST "x")      ===     "VarAST x"
textOf :: ExprAST -> Int -> String
textOf e width =
    let spaces = Prelude.replicate width '\SP'  in
    case e of
        BoolAST         b    -> "BoolAST      " ++ (show b)
        CallAST   r b es     -> "CallAST      "
        CompilesAST   e c    -> "CompilesAST  "
        IfAST         a b c  -> "IfAST        "
        IntAST i t c base    -> "IntAST       " ++ t
        E_FnAST (FnAST a b)  -> "FnAST        "
        SeqAST     a b       -> "SeqAST       "
        SubscriptAST  a b    -> "SubscriptAST "
        E_PrototypeAST (PrototypeAST t s es)     -> "PrototypeAST " ++ s
        TupleAST     es b    -> "TupleAST     "
        VarAST mt v          -> "VarAST       " ++ v ++ " :: " ++ show mt


-----------------------------------------------------------------------

data AnnExpr =
          AnnBool       Bool
        | AnnInt        { aintType   :: TypeAST
                        , aintActive :: Integer
                        , aintText   :: String
                        , aintClean  :: String
                        , aintBase   :: Int }
                        -- parts  is_env_tuple
        | AnnTuple      [AnnExpr] Bool
        | E_AnnFn       AnnFn

        | AnnCall       ESourceRange TypeAST AnnExpr AnnExpr
        | AnnCompiles   CompilesStatus
        | AnnIf         TypeAST AnnExpr AnnExpr AnnExpr
        | AnnSeq        AnnExpr AnnExpr
        | AnnSubscript  TypeAST AnnExpr AnnExpr
        | E_AnnPrototype  TypeAST AnnPrototype
        | E_AnnVar       AnnVar
        deriving Show

data AnnVar       = AnnVar { avarType :: TypeAST, avarName :: String } deriving (Show)
data AnnFn        = AnnFn           AnnPrototype AnnExpr deriving (Show)
data AnnPrototype = AnnPrototype    { annProtoReturnType :: TypeAST
                                    , annProtoName       :: String
                                    , annProtoVars       :: [AnnVar]
                                    } deriving (Show)

-----------------------------------------------------------------------

unbuildSeqsA :: AnnExpr -> [AnnExpr]
unbuildSeqsA (AnnSeq a b) = a : unbuildSeqsA b
unbuildSeqsA expr = [expr]

