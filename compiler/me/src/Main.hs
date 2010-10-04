-----------------------------------------------------------------------------
--
-- Module      :  Main
-- Copyright   :
-- License     :  BSD3
--
-- Maintainer  :
-- Stability   :
-- Portability :
--
-- |
--
-----------------------------------------------------------------------------

module Main (
main
) where

import Control.Monad(when)
import System.Environment(getArgs,getProgName)

import qualified Data.ByteString.Lazy as L(readFile)
import qualified Data.ByteString.Lazy.UTF8 as U(toString)
import qualified System.IO.UTF8 as U(putStrLn)
import qualified Data.Foldable as F(forM_)

import qualified Data.ByteString as B
import qualified Data.Text as T

import Data.Sequence
import Data.Maybe
import Data.Foldable
import Data.Char

import Control.Exception(assert)

import Text.ProtocolBuffers(messageGet,utf8,isSet,getVal)
import Text.ProtocolBuffers.Basic(uToString)

import Foster.Pb.Expr as PbExpr
import Foster.Pb.Expr.Tag(Tag(PB_INT, BOOL, VAR, OP, TUPLE, FN, PROTO, CALL, SEQ, SIMD, SUBSCRIPT))
import Foster.Pb.Proto as Proto
import Foster.Pb.PBIf as PBIf
import Foster.Pb.PBInt as PBInt
import qualified Foster.Pb.SourceRange as Pb

import Foster.Pb.Type as PbType

-----------------------------------------------------------------------

outLn = U.putStrLn . U.toString . utf8

exprTagString :: Tag -> [Char]
exprTagString tag =
        case tag of
                PB_INT  -> "PB_INT"
                BOOL    -> "BOOL"
                VAR     -> "VAR"
                OP      -> "OP"
                TUPLE   -> "TUPLE"
                FN      -> "FN"
                PROTO   -> "PROTO"
                CALL    -> "CALL"
                SEQ     -> "SEQ"
                SIMD    -> "SIMD"
                SUBSCRIPT -> "SUBSCRIPT"
--

data CompilesStatus = CS_WouldCompile | CS_WouldNotCompile | CS_NotChecked
    deriving Show

data ESourceLocation = ESourceLocation Int Int
    deriving (Show)

data ESourceRange = ESourceRange ESourceLocation ESourceLocation String
    deriving (Show)

data ExprAST =
          AssignAST     ExprAST ExprAST
        | BoolAST       Bool
        | BinaryOpAST   String ExprAST ExprAST
        | CallAST       ExprAST [ExprAST]
        | CompilesAST   ExprAST CompilesStatus
        | DerefAST      ExprAST
        | IfAST         ExprAST ExprAST ExprAST
                        -- active text clean base
        | IntAST        Integer String String Int
        | FnAST         ExprAST ExprAST
        | RefAST        ExprAST
        | SeqAST        [ExprAST]
        | SubscriptAST  ExprAST ExprAST
        | PrototypeAST  TypeAST String [ExprAST]
        | TupleAST      ExprAST Bool
        | VarAST        String
        deriving Show

data TypeAST =
         MissingTypeAST
         deriving (Show)

-----------------------------------------------------------------------

childrenOf :: ExprAST -> [ExprAST]
childrenOf e =
    case e of
        AssignAST     a b    -> [a, b]
        BoolAST         b    -> []
        BinaryOpAST s a b    -> [a, b]
        CallAST     b es     -> [b] ++ es
        CompilesAST   e c    -> [e]
        DerefAST      e      -> [e]
        IfAST         a b c  -> [a, b, c]
        IntAST i s1 s2 i2    -> []
        FnAST         a b    -> [a, b]
        RefAST        a      -> [a]
        SeqAST        es     -> es
        SubscriptAST  a b    -> [a, b]
        PrototypeAST  t s es -> es
        TupleAST      e b    -> [e]
        VarAST        s      -> []

textOf :: ExprAST -> Int -> String
textOf e width =
    let spaces = Prelude.replicate width '\SP'  in
    case e of
        AssignAST     a b    -> "AssignAST    "
        BoolAST         b    -> "BoolAST      " ++ (show b)
        BinaryOpAST s a b    -> "BinaryOpAST  " ++ s
        CallAST     b es     -> "CallAST      "
        CompilesAST   e c    -> "CompilesAST  "
        DerefAST      e      -> "DerefAST     "
        IfAST         a b c  -> "IfAST        "
        IntAST i t c base    -> "IntAST       " ++ t
        FnAST         a b    -> "FnAST        "
        RefAST        a      -> "RefAST       "
        SeqAST        es     -> "SeqAST       "
        SubscriptAST  a b    -> "SubscriptAST "
        PrototypeAST  t s es -> "PrototypeAST " ++ s
        TupleAST      e b    -> "TupleAST     "
        VarAST        s      -> "VarAST       " ++ s

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



-----------------------------------------------------------------------

listExprs :: Expr -> IO ()
listExprs pb_exprs = do
  F.forM_ (PbExpr.parts pb_exprs) $ \expr -> do
    putStr "Expr tag: " >> print (PbExpr.tag expr)

    printProtoName (PbExpr.proto expr)

    if (isSet expr PbExpr.name)
      then do putStr "  name: " >> outLn (getVal expr PbExpr.name)
      else do putStr "  no name\n"

    putStrLn $ showStructure $ parseExpr expr

printProtoName :: Maybe Proto -> IO ()
printProtoName Nothing = do
        putStr "No proto\n"
printProtoName (Just p) = do
        putStr "Proto: " >> outLn (Proto.name p)


-- hprotoc cheat sheet:
--
-- required string name         => (name person)
-- required int32 id            => (Person.id person)
-- optional string email        => (getVal person email)
-- optional PhoneType type      => (getVal phone_number type')
-----------------------------------------------------------------------

part :: Int -> Seq Expr -> ExprAST
part i parts = parseExpr $ index parts i

parseAssign pbexpr =    let parts = PbExpr.parts pbexpr in
                        AssignAST (part 0 parts) (part 1 parts)

parseBool pbexpr = BoolAST $ fromMaybe False (PbExpr.bool_value pbexpr)

parseCall pbexpr =
        case map parseExpr $ toList (PbExpr.parts pbexpr) of
                (hd:tl) -> CallAST hd tl
                _ -> error "call needs a base!"

compileStatus :: Maybe Bool -> CompilesStatus
compileStatus Nothing      = CS_NotChecked
compileStatus (Just True)  = CS_WouldCompile
compileStatus (Just False) = CS_WouldNotCompile

parseCompiles pbexpr =  CompilesAST (part 0 $ PbExpr.parts pbexpr)
                                    (compileStatus $ PbExpr.compiles pbexpr)

parseDeref pbexpr =     DerefAST $ part 0 (PbExpr.parts pbexpr)

parseFn pbexpr =        let parts = PbExpr.parts pbexpr in
                        let fn = FnAST (part 0 parts) (part 1 parts) in
                        assert ((Data.Sequence.length parts) == 2) $
                        fn

parseIf pbexpr =
        if (isSet pbexpr PbExpr.pb_if)
                then parseFromPBIf (getVal pbexpr PbExpr.pb_if)
                else error "must have if to parse from if!"
        where parseFromPBIf pbif =
                IfAST (parseExpr $ PBIf.test_expr pbif)
                      (parseExpr $ PBIf.then_expr pbif)
                      (parseExpr $ PBIf.else_expr pbif)

parseInt :: Expr -> ExprAST
parseInt pbexpr =
        if (isSet pbexpr PbExpr.pb_int)
                then parseFromPBInt (getVal pbexpr PbExpr.pb_int)
                else error "must have int to parse from int!"

splitString :: String -> String -> [String]
splitString needle haystack =
        let textParts = T.split (T.pack needle) (T.pack haystack) in
        map T.unpack textParts

onlyHexDigitsIn :: String -> Bool
onlyHexDigitsIn str =
        Prelude.all (\x -> (toLower x) `Prelude.elem` "0123456789abcdef") str

parseFromPBInt :: PBInt -> ExprAST
parseFromPBInt pbint =
        let text = uToString $ PBInt.text pbint in
        let clean2 = Prelude.filter (/= '`') text in
        let (clean, base) = case splitString "_" clean2 of
                [main, base] -> (main, read base)
                otherwise    -> (clean2, 10) in
        let i = parseIntFromClean clean text base in
        assert (base `Prelude.elem` [2, 8, 10, 16]) $
        assert (onlyHexDigitsIn clean) $
        i

parseIntFromClean :: String -> String -> Int -> ExprAST
parseIntFromClean clean text base =
        let bitsPerDigit = ceiling $ (log $ fromIntegral base) / (log 2) in
        let conservativeBitsNeeded = bitsPerDigit * (Prelude.length clean) + 2 in
        let activeBits = toInteger conservativeBitsNeeded in
        IntAST activeBits text clean base

parseRef pbexpr = RefAST $ part 0 (PbExpr.parts pbexpr)

parseSeq pbexpr = SeqAST (map parseExpr $ toList (PbExpr.parts pbexpr))

parseSubscript pbexpr = let parts = PbExpr.parts pbexpr in
                        SubscriptAST (part 0 parts) (part 1 parts)

parseTuple pbexpr =
        TupleAST (part 0 $ PbExpr.parts pbexpr)
                 (fromMaybe False $ PbExpr.is_closure_environment pbexpr)

parseVar pbexpr = VarAST $ uToString (fromJust $ PbExpr.name pbexpr)

emptyRange :: ESourceRange
emptyRange = ESourceRange e e "<no file>"
                    where e = (ESourceLocation (-1::Int) (-1::Int))

parseProto :: Expr -> ExprAST
parseProto pbexpr =
    case PbExpr.proto pbexpr of
                Nothing -> error "Need a proto to parse a proto!"
                Just x  -> parseProtoP x

getVarName :: ExprAST -> String
getVarName (VarAST s) = s
getVarName x = error "getVarName must be given a var!" ++ show x

getVar :: Expr -> ExprAST
getVar e = case PbExpr.tag e of
            VAR -> parseVar e
            _   ->  error "getVar must be given a var!"

parseProtoP :: Proto -> ExprAST
parseProtoP proto =
    let args = Proto.in_args proto in
    let vars = map getVar $ toList args in
    let retTy = MissingTypeAST in
    let name = uToString $ Proto.name proto in
    PrototypeAST retTy name vars

parseOp :: Expr -> ExprAST
parseOp pbexpr =
    let parts = PbExpr.parts pbexpr in
        case Data.Sequence.length $ parts   of
            2 -> BinaryOpAST (uToString $ fromJust $ PbExpr.name pbexpr)
                             (part 0 parts) (part 1 parts)
            _ -> error "Protobuf Expr tagged OP with too many parts"

sourceRangeFromPBRange :: Pb.SourceRange -> ESourceRange
sourceRangeFromPBRange pbrange = error "no"

parseExpr :: Expr -> ExprAST
parseExpr pbexpr =
    let range = case PbExpr.range pbexpr of
                    Nothing   -> emptyRange
                    (Just r)  -> sourceRangeFromPBRange r in
    let fn = case PbExpr.tag pbexpr of
                PB_INT  -> parseInt
                BOOL    -> parseBool
                VAR     -> parseVar
                OP      -> parseOp
                TUPLE   -> parseTuple
                FN      -> parseFn
                PROTO   -> parseProto
                CALL    -> parseCall
                SEQ     -> parseSeq
                --SIMD    -> "SIMD"
                SUBSCRIPT -> parseSubscript
        in
   fn pbexpr

-----------------------------------------------------------------------


main :: IO ()
main = do
  args <- getArgs
  f <- case args of
         [file] -> L.readFile file
         _ -> getProgName >>= \self -> error $ "Usage "++self++" path/to/file.foster"

  case messageGet f of
    Left msg -> error ("Failed to parse protocol buffer.\n"++msg)
    Right (pb_exprs,_) -> listExprs pb_exprs

  return ()


