-----------------------------------------------------------------------------
-- Copyright (c) 2010 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.ExprAST where

import Foster.TypeAST
import Data.Int
import Data.Set as Set(fromList, toList, difference)
import Data.Sequence as Seq
import Data.Maybe(fromJust)
import Data.List(replicate)
import qualified Data.Text as T


data CompilesStatus = CS_WouldCompile | CS_WouldNotCompile | CS_NotChecked
    deriving (Eq, Show)

data ESourceLocation = ESourceLocation { sourceLocationLine :: Int
                                       , sourceLocationCol  :: Int
                                       } deriving (Eq, Show)

data ESourceRange = ESourceRange { sourceRangeBegin :: ESourceLocation
                                 , sourceRangeEnd   :: ESourceLocation
                                 , sourceRangeLines :: SourceLines
                                 }
                  | EMissingSourceRange

instance Show ESourceRange where
    show = showSourceRange

showSourceRange :: ESourceRange -> String
showSourceRange EMissingSourceRange = ""
showSourceRange (ESourceRange begin end lines) = "\n" ++ showSourceLines begin end lines ++ "\n"

-- If a single line is specified, show it with highlighting;
-- otherwise, show the lines spanning the two locations (inclusive).
showSourceLines (ESourceLocation bline bcol) (ESourceLocation eline ecol) lines =
    if bline == eline
        then joinWith "\n" [fromJust $ sourceLine lines bline, highlightLineRange bcol ecol]
        else joinWith "\n" [fromJust $ sourceLine lines n | n <- [bline..eline]]

-- Generates a string of spaces and twiddles which underlines
-- a given range of characters.
highlightLineRange :: Int -> Int -> String
highlightLineRange bcol ecol =
    let len = ecol - bcol in
    if len <= 0
        then ""
        else (Data.List.replicate bcol ' ') ++ (Data.List.replicate len '~')

data SourceLines = SourceLines (Seq T.Text)

sourceLine :: SourceLines -> Int -> Maybe String
sourceLine (SourceLines seq) n =
    if n < 0 || Seq.length seq < n
        then Nothing
        else Just (T.unpack $ Seq.index seq n)

-- |||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

data ModuleAST fnType = ModuleAST {
          moduleASTfunctions   :: [fnType]
        , moduleASTsourceLines :: SourceLines
     }

data Literal = LitInt LiteralInt

data LiteralInt = LiteralInt { litIntMinBits :: Integer
                             , litIntText    :: String
                             , litIntClean   :: String
                             , litIntBase    :: Int
                             } deriving (Show)

data ExprAST =
          BoolAST       Bool
        | IntAST        LiteralInt
                        -- parts  is_env_tuple
        | TupleAST      { tupleParts :: [ExprAST]
                        , tupleIsEnv :: Bool
                        }
        | E_FnAST       FnAST

        | CallAST       ESourceRange ExprAST ExprAST
        | CompilesAST   ExprAST CompilesStatus
        | IfAST         ExprAST ExprAST ExprAST
        | SeqAST        ExprAST ExprAST
        | SubscriptAST  { subscriptBase  :: ExprAST
                        , subscriptIndex :: ExprAST
                        }
        | E_PrototypeAST    PrototypeAST
        | VarAST        (Maybe TypeAST) String
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


-- Builds trees like this:
-- AnnSeq        :: i32
-- ├─AnnCall       :: i32
-- │ ├─AnnVar       expect_i32 :: ((i32) -> i32)
-- │ └─AnnTuple
-- │   └─AnnInt       999999 :: i32

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
        IntAST litInt        -> []
        E_FnAST f            -> [E_PrototypeAST (fnProto f), (fnBody f)]
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
        CallAST   r b a      -> "CallAST      "
        CompilesAST   e c    -> "CompilesAST  "
        IfAST         a b c  -> "IfAST        "
        IntAST litInt        -> "IntAST       " ++ (litIntText litInt)
        E_FnAST f            -> "FnAST        "
        SeqAST     a b       -> "SeqAST       "
        SubscriptAST  a b    -> "SubscriptAST "
        E_PrototypeAST (PrototypeAST t s es)     -> "PrototypeAST " ++ s
        TupleAST     es b    -> "TupleAST     "
        VarAST mt v          -> "VarAST       " ++ v ++ " :: " ++ show mt



freeVariables :: ExprAST -> [String]
freeVariables e = case e of
    BoolAST         b    -> []
    CallAST   r b a      -> freeVariables b ++ freeVariables a
    CompilesAST   e c    -> freeVariables e
    IfAST         a b c  -> freeVariables a ++ freeVariables b ++ freeVariables c
    IntAST litInt        -> []
    E_FnAST f           -> let bodyvars =  Set.fromList (freeVariables (fnBody f)) in
                               let boundvars = Set.fromList (map avarName (prototypeASTformals (fnProto f))) in
                               Set.toList (Set.difference bodyvars boundvars)

    SeqAST     a b       -> freeVariables a ++ freeVariables b
    SubscriptAST  a b    -> freeVariables a ++ freeVariables b
    E_PrototypeAST (PrototypeAST t s es)     -> []
    TupleAST     es b    -> concatMap freeVariables es
    VarAST mt v          -> [v]

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
        deriving (Show)

data AnnVar       = AnnVar { avarType :: TypeAST, avarName :: String } deriving (Eq, Show)
data AnnFn        = AnnFn           AnnPrototype AnnExpr (Maybe [AnnVar]) deriving (Show)
data AnnPrototype = AnnPrototype    { annProtoReturnType :: TypeAST
                                    , annProtoName       :: String
                                    , annProtoVars       :: [AnnVar]
                                    } deriving (Eq, Show)


-----------------------------------------------------------------------

unbuildSeqsA :: AnnExpr -> [AnnExpr]
unbuildSeqsA (AnnSeq a b) = a : unbuildSeqsA b
unbuildSeqsA expr = [expr]

