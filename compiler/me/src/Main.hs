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

        | CallAST       ExprAST ExprAST
        | CompilesAST   ExprAST CompilesStatus
        | IfAST         ExprAST ExprAST ExprAST
        | SeqAST        [ExprAST]
        | SubscriptAST  ExprAST ExprAST
        | E_PrototypeAST    PrototypeAST
        | E_VarAST      VarAST
        deriving Show

data TypeAST =
           MissingTypeAST
         | TypeUnitAST
         | TypeBoolAST
         | TypeInt32AST
         | TypeInt64AST
         | TupleTypeAST     [TypeAST]
         | FnTypeAST        TypeAST TypeAST
         deriving (Eq,Show)

                -- proto    body
data FnAST  = FnAST     PrototypeAST ExprAST deriving (Show)
data VarAST = VarAST    String               deriving (Show)
data PrototypeAST = PrototypeAST TypeAST String [VarAST] deriving (Show)

-----------------------------------------------------------------------


typesEqual :: TypeAST -> TypeAST -> Bool
typesEqual TypeUnitAST (TupleTypeAST []) = True
typesEqual ta tb = ta == tb

type Context = [(String, TypeAST)]

ctxLookup :: Context -> String -> Maybe TypeAST
ctxLookup []         s = Nothing
ctxLookup ((v,t):xs) s =
    if s == v then Just t
              else ctxLookup xs s

extendContext :: Context -> PrototypeAST -> Context
extendContext ctx proto =
    let vars = getBindings proto in
    vars ++ ctx

data TypecheckResult
    = JustType        TypeAST
    | TypecheckErrors [String]
    deriving (Show)

getTypeCheckedType (JustType t) = t
getTypeCheckedType (TypecheckErrors _) = MissingTypeAST

typecheck :: Context -> ExprAST -> TypecheckResult
typecheck ctx expr =
    case expr of
        E_FnAST (FnAST proto body)  ->
            let extCtx = extendContext ctx proto in
            typecheck extCtx body
        BoolAST         b    -> JustType TypeBoolAST
        CallAST     b es     -> let tbs = typecheck ctx es in
                                let tb = typecheck ctx b in
                                case (tb, tbs) of
                                    (JustType _, TypecheckErrors e) ->
                                        TypecheckErrors ("call args had errors: ":e)
                                    (TypecheckErrors e, JustType _) ->
                                        TypecheckErrors ("call base had errors: ":e)
                                    (JustType (FnTypeAST argtype restype), JustType tbs_ty) ->
                                        if typesEqual argtype tbs_ty
                                            then JustType restype
                                            else TypecheckErrors ["CallAST mismatches: "
                                                                   ++ show argtype ++ " vs " ++ show tbs_ty]
                                    otherwise -> TypecheckErrors ["CallAST w/o FnAST type: " ++ (show b) ++ " :: " ++ (show tb)]
        IfAST         a b c  -> case (typecheck ctx a, typecheck ctx b, typecheck ctx c) of
                                    (JustType ta, JustType tb, JustType tc) ->
                                        if typesEqual ta TypeBoolAST then
                                            if typesEqual tb tc
                                                then JustType tb
                                                else TypecheckErrors ["IfAST"]
                                            else TypecheckErrors ["IfAST"]
                                    otherwise -> TypecheckErrors ["IfAST"]
        IntAST i s1 s2 i2    -> JustType TypeInt32AST
        SeqAST        es     -> let tes = map (typecheck ctx) es in
                                head tes
        SubscriptAST  a b    -> let ta = typecheck ctx a in
                                let tb = typecheck ctx b in
                                TypecheckErrors ["SubscriptAST"]
        E_PrototypeAST (PrototypeAST t s es) ->
                                TypecheckErrors ["PrototypeAST"]
        TupleAST      es b   -> let tes = map (typecheck ctx) es in
                                let typs = map (\x -> case x of
                                                        JustType t  -> t
                                                        TypecheckErrors _ -> MissingTypeAST) tes in
                                JustType (TupleTypeAST typs)
        E_VarAST (VarAST s) -> case ctxLookup ctx s of
                                    Just t -> JustType t
                                    Nothing -> TypecheckErrors ["Missing var"]
        CompilesAST   e c    -> JustType TypeBoolAST
-----------------------------------------------------------------------

getRootContext :: () -> Context
getRootContext () =
    [("llvm_readcyclecounter", FnTypeAST TypeUnitAST TypeInt64AST)
    ,("expect_i32", FnTypeAST TypeInt32AST TypeUnitAST)
    ,( "print_i32", FnTypeAST TypeInt32AST TypeUnitAST)
    ,(  "read_i32", FnTypeAST TypeUnitAST TypeInt32AST)
    ,("expect_Bool", FnTypeAST TypeBoolAST TypeUnitAST)
    ,( "print_Bool", FnTypeAST TypeBoolAST TypeUnitAST)

    ,("primitive_<_i64", FnTypeAST (TupleTypeAST [TypeInt64AST, TypeInt64AST]) TypeBoolAST)
    ,("primitive_-_i64", FnTypeAST (TupleTypeAST [TypeInt64AST, TypeInt64AST]) TypeInt64AST)
    ]

listExprs :: Expr -> IO ()
listExprs pb_exprs = do
  F.forM_ (PbExpr.parts pb_exprs) $ \expr -> do
    putStr "Expr tag: " >> print (PbExpr.tag expr)

    printProtoName (PbExpr.proto expr)

    if (isSet expr PbExpr.name)
      then do putStr "  name: " >> outLn (getVal expr PbExpr.name)
      else do putStr "  no name\n"

    let ast = parseExpr expr
    putStrLn "ast:"
    putStrLn $ showStructure ast
    putStrLn "typechecking..."
    let typechecked = typecheck (getRootContext ()) ast
    putStrLn "typechecked:"
    putStrLn $ show typechecked
    return ()

printProtoName :: Maybe Proto -> IO ()
printProtoName Nothing = do
        putStrLn "No proto"
printProtoName (Just p) = do
        putStr "Proto: "  >> outLn (Proto.name p)


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
                [base, arg] -> CallAST base arg
                (base:args) -> CallAST base (TupleAST args False)
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





childrenOf :: ExprAST -> [ExprAST]
childrenOf e =
    case e of
        BoolAST         b    -> []
        CallAST     b es     -> [b, es]
        CompilesAST   e c    -> [e]
        IfAST         a b c  -> [a, b, c]
        IntAST i s1 s2 i2    -> []
        E_FnAST (FnAST a b)  -> [E_PrototypeAST a, b]
        SeqAST        es     -> es
        SubscriptAST  a b    -> [a, b]
        E_PrototypeAST (PrototypeAST t s es) -> (map (\x -> E_VarAST x) es)
        TupleAST     es b    -> es
        E_VarAST     v       -> []

-- Formats a single-line tag for the given ExprAST node.
-- Example:  textOf (VarAST "x")      ===     "VarAST x"
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
        E_VarAST v           -> "VarAST       " ++ varName v

-----------------------------------------------------------------------
varName (VarAST name) = name

getBindings :: PrototypeAST -> [(String, TypeAST)]
getBindings (PrototypeAST t s vars) =
    map (\v -> (varName v, MissingTypeAST)) vars

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
