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

import Control.Monad(when,sequence)
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
import Monad(join,liftM)
import Data.IORef(IORef,newIORef,readIORef,writeIORef)
import qualified Data.HashTable as HashTable

import Control.Exception(assert)

import Text.ProtocolBuffers(messageGet,utf8,isSet,getVal)
import Text.ProtocolBuffers.Basic(uToString)

import Foster.Pb.Expr as PbExpr
import Foster.Pb.Expr.Tag(Tag(PB_INT, BOOL, VAR, TUPLE, FN, PROTO, CALL, SEQ, SUBSCRIPT))
import Foster.Pb.Proto as Proto
import Foster.Pb.PBIf as PBIf
import Foster.Pb.PBInt as PBInt
import qualified Foster.Pb.SourceRange as Pb

import Foster.Pb.Type as PbType

-----------------------------------------------------------------------

outLn = U.putStrLn . U.toString . utf8

exprTagString :: Tag -> String
exprTagString tag =
        case tag of
                PB_INT    -> "PB_INT"
                BOOL      -> "BOOL"
                VAR       -> "VAR"
                TUPLE     -> "TUPLE"
                FN        -> "FN"
                PROTO     -> "PROTO"
                CALL      -> "CALL"
                SEQ       -> "SEQ"
                SUBSCRIPT -> "SUBSCRIPT"
                otherwise -> "<unknown>"
--

data CompilesStatus = CS_WouldCompile | CS_WouldNotCompile | CS_NotChecked
    deriving Show

data ESourceLocation = ESourceLocation Int Int
    deriving (Show)

data ESourceRange = ESourceRange ESourceLocation ESourceLocation String
    deriving (Show)

data ExprAST =
          BoolAST       Bool
                        -- active text clean base
        | IntAST        Integer String String Int
        | TupleAST      [ExprAST] Bool
        | E_FnAST       FnAST

        | CallAST       ExprAST [ExprAST]
        | CompilesAST   ExprAST CompilesStatus
        | IfAST         ExprAST ExprAST ExprAST
        | SeqAST        [ExprAST]
        | SubscriptAST  ExprAST ExprAST
        | E_PrototypeAST    PrototypeAST
        | E_VarAST      VarAST
        deriving Show

data TypeAST =
           MissingTypeAST
         | TypeBoolAST
         | TypeIntAST
         | FnTypeAST        [TypeAST] TypeAST
         deriving (Eq,Show)

                -- proto    body
data FnAST  = FnAST     PrototypeAST ExprAST deriving (Show)
data VarAST = VarAST    String          deriving (Show)
data PrototypeAST = PrototypeAST TypeAST String [VarAST] deriving (Show)

-----------------------------------------------------------------------


childrenOf :: ExprAST -> [ExprAST]
childrenOf e =
    case e of
        BoolAST         b    -> []
        CallAST     b es     -> [b] ++ es
        CompilesAST   e c    -> [e]
        IfAST         a b c  -> [a, b, c]
        IntAST i s1 s2 i2    -> []
        E_FnAST (FnAST a b)  -> [E_PrototypeAST a, b]
        SeqAST        es     -> es
        SubscriptAST  a b    -> [a, b]
        E_PrototypeAST (PrototypeAST t s es) -> (map (\x -> E_VarAST x) es)
        TupleAST     es b    -> es
        E_VarAST (VarAST s)  -> []

textOf :: ExprAST -> Int -> String
textOf e width =
    let spaces = Prelude.replicate width '\SP'  in
    case e of
        BoolAST         b    -> "BoolAST      " ++ (show b)
        CallAST     b es     -> "CallAST      "
        CompilesAST   e c    -> "CompilesAST  "
        IfAST         a b c  -> "IfAST        "
        IntAST i t c base    -> "IntAST       " ++ t
        E_FnAST (FnAST a b)  -> "FnAST        "
        SeqAST        es     -> "SeqAST       "
        SubscriptAST  a b    -> "SubscriptAST "
        E_PrototypeAST (PrototypeAST t s es)     -> "PrototypeAST " ++ s
        TupleAST     es b    -> "TupleAST     "
        E_VarAST (VarAST s)  -> "VarAST       " ++ s

-----------------------------------------------------------------------
varName (VarAST name) = name
getBindings (PrototypeAST t s vars) = vars

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

typesEqual :: TypeAST -> TypeAST -> Bool
typesEqual ta tb = ta == tb

typecheck :: ExprAST -> Maybe TypeAST
typecheck expr =
    case expr of
        E_FnAST (FnAST proto body)  ->
            -- let bindings = getBindings proto in
            typecheck body
        BoolAST         b    -> Just TypeBoolAST
        CallAST     b es     -> let tbs = map typecheck es in
                                let tb = typecheck b in
                                case tb of
                                    Just (FnTypeAST argtypes restype) ->
                                        if Prelude.all (\(x,y) -> typesEqual x y)
                                                (Prelude.zip (map fromJust (tb:tbs))
                                                        (restype:argtypes))
                                            then Just restype
                                            else Nothing
                                    otherwise -> Nothing
        CompilesAST   e c    -> Just TypeBoolAST
        IfAST         a b c  -> case (typecheck a, typecheck b, typecheck c) of
                                    (Just ta, Just tb, Just tc) ->
                                        if typesEqual ta TypeBoolAST then
                                            if typesEqual tb tc
                                                then Just tb
                                                else Nothing
                                            else Nothing
                                    otherwise -> Nothing
        IntAST i s1 s2 i2    -> Just TypeIntAST
        SeqAST        es     -> let tes = map typecheck es in
                                Nothing
        SubscriptAST  a b    -> let ta = typecheck a in
                                let tb = typecheck b in
                                Nothing
        E_PrototypeAST (PrototypeAST t s es) ->
                                Nothing
        TupleAST      es b   -> let tes = map typecheck es in
                                Nothing
        E_VarAST (VarAST s)  -> Nothing
-----------------------------------------------------------------------

listExprs :: Expr -> IO ()
listExprs pb_exprs = do
  F.forM_ (PbExpr.parts pb_exprs) $ \expr -> do
    putStr "Expr tag: " >> print (PbExpr.tag expr)

    printProtoName (PbExpr.proto expr)

    if (isSet expr PbExpr.name)
      then do putStr "  name: " >> outLn (getVal expr PbExpr.name)
      else do putStr "  no name\n"

    ast <- return $ parseExpr expr

    putStrLn "ast:"
    putStrLn $ showStructure ast
    let typechecked = typecheck ast
    return ()

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

parseFn pbexpr =        let parts = PbExpr.parts pbexpr in
                        let fn = E_FnAST $ FnAST (parseProtoP $ index parts 0)
                                                 (part 1 parts) in
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
        let text = uToString $ PBInt.originalText pbint in
        let (clean, base) = extractCleanBase text in
        assert (base `Prelude.elem` [2, 8, 10, 16]) $
        assert (onlyHexDigitsIn clean) $
        mkIntASTFromClean clean text base

-- Given "raw" integer text like "123`456_10",
-- return ("123456", 10)
extractCleanBase :: String -> (String, Int)
extractCleanBase text =
        let noticks = Prelude.filter (/= '`') text in
        case splitString "_" noticks of
            [first, base] -> (first, read base)
            otherwise     -> (noticks, 10)

mkIntASTFromClean :: String -> String -> Int -> ExprAST
mkIntASTFromClean clean text base =
        let bitsPerDigit = ceiling $ (log $ fromIntegral base) / (log 2) in
        let conservativeBitsNeeded = bitsPerDigit * (Prelude.length clean) + 2 in
        let activeBits = toInteger conservativeBitsNeeded in
        IntAST activeBits text clean base

parseSeq pbexpr = SeqAST (map parseExpr $ toList (PbExpr.parts pbexpr))

parseSubscript pbexpr = let parts = PbExpr.parts pbexpr in
                        SubscriptAST (part 0 parts) (part 1 parts)

parseTuple pbexpr =
        TupleAST (map parseExpr $ toList (PbExpr.parts pbexpr))
                 (fromMaybe False $ PbExpr.is_closure_environment pbexpr)

parseVar :: Expr -> VarAST
parseVar pbexpr = VarAST $ uToString (fromJust $ PbExpr.name pbexpr)

emptyRange :: ESourceRange
emptyRange = ESourceRange e e "<no file>"
                    where e = (ESourceLocation (-1::Int) (-1::Int))

parseProtoP :: Expr -> PrototypeAST
parseProtoP pbexpr =
    case PbExpr.proto pbexpr of
                Nothing  -> error "Need a proto to parse a proto!"
                Just proto  -> parseProtoPP proto

parseProto :: Expr -> ExprAST
parseProto pbexpr = E_PrototypeAST (parseProtoP pbexpr)

getVarName :: VarAST -> String
getVarName (VarAST s) = s

getVar :: Expr -> VarAST
getVar e = case PbExpr.tag e of
            VAR -> parseVar e
            _   -> error "getVar must be given a var!"

parseProtoPP :: Proto -> PrototypeAST
parseProtoPP proto =
    let args = Proto.in_args proto in
    let vars = map getVar $ toList args in
    let retTy = MissingTypeAST in
    let name = uToString $ Proto.name proto in
    PrototypeAST retTy name vars

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
                VAR     -> (\x -> E_VarAST $ parseVar x)
                TUPLE   -> parseTuple
                FN      -> parseFn
                PROTO   -> parseProto
                CALL    -> parseCall
                SEQ     -> parseSeq
                SUBSCRIPT -> parseSubscript
        in
   fn pbexpr

-----------------------------------------------------------------------


main :: IO ()
main = do
  args <- getArgs
  f <- case args of
         [file] -> L.readFile file
         _ -> getProgName >>= \self -> error $ "Usage: " ++ self ++ " path/to/file.foster"

  case messageGet f of
    Left msg -> error ("Failed to parse protocol buffer.\n"++msg)
    Right (pb_exprs,_) -> listExprs pb_exprs

  return ()


