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

import List
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
import Foster.Pb.FnType as PbFnType
import Foster.Pb.Type.Tag as PbTypeTag
import Foster.Pb.Type as PbType

-----------------------------------------------------------------------

outLn = U.putStrLn . U.toString . utf8

exprTagString :: Foster.Pb.Expr.Tag.Tag -> String
exprTagString tag =
        case tag of
                PB_INT    -> "PB_INT"
                BOOL      -> "BOOL"
                VAR       -> "VAR"
                Foster.Pb.Expr.Tag.TUPLE -> "TUPLE"
                Foster.Pb.Expr.Tag.FN    -> "FN"
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
        | IntAST        { eintActive :: Integer
                        , eintText   :: String
                        , eintClean  :: String
                        , eintBase   :: Int }
                        -- parts  is_env_tuple
        | TupleAST      [ExprAST] Bool
        | E_FnAST       FnAST

        | CallAST       ExprAST ExprAST
        | CompilesAST   ExprAST CompilesStatus
        | IfAST         ExprAST ExprAST ExprAST
        | SeqAST        [ExprAST]
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

        | AnnCall       TypeAST AnnExpr AnnExpr
        | AnnCompiles   CompilesStatus
        | AnnIf         TypeAST AnnExpr AnnExpr AnnExpr
        | AnnSeq        TypeAST [AnnExpr]
        | AnnSubscript  TypeAST AnnExpr AnnExpr
        | E_AnnPrototype  TypeAST AnnPrototype
        | E_AnnVar       AnnVar
        deriving Show

data AnnVar       = AnnVar          TypeAST String deriving (Show)
data AnnFn        = AnnFn           AnnPrototype AnnExpr deriving (Show)
data AnnPrototype = AnnPrototype    TypeAST String [AnnVar] deriving (Show)

normalize :: TypeAST -> TypeAST
normalize (TupleTypeAST [t]) = t
normalize x = x

typeAST :: AnnExpr -> TypeAST
-- {{{
typeAST (AnnBool _)          = NamedTypeAST "i1"
typeAST (AnnInt t _ _ _ _)   = t
typeAST (AnnTuple es b)      = TupleTypeAST [typeAST e | e <- es]
typeAST (E_AnnFn (AnnFn (AnnPrototype rt s vs) e))
                             = FnTypeAST (normalize $ TupleTypeAST [t | (AnnVar t v) <- vs]) rt
typeAST (AnnCall t b a)      = t
typeAST (AnnCompiles c)    = NamedTypeAST "i1"
typeAST (AnnIf t a b c)      = t
typeAST (AnnSeq t es)        = t
typeAST (AnnSubscript t _ _) = t
typeAST (E_AnnPrototype t p) = t
typeAST (E_AnnVar (AnnVar t s)) = t
-- }}}

data TypeAST =
           MissingTypeAST String
         | TypeUnitAST
         -- | TypeBoolAST
         | NamedTypeAST     String
         | TupleTypeAST     [TypeAST]
         | FnTypeAST        TypeAST TypeAST
         deriving (Eq)

instance Show TypeAST where
    show = showTypeAST

showTypeAST :: TypeAST -> String
showTypeAST (MissingTypeAST s) = "(MissingTypeAST " ++ s ++ ")"
showTypeAST (TypeUnitAST) = "()"
showTypeAST (NamedTypeAST s) = s
showTypeAST (TupleTypeAST types) = "(" ++ commas [showTypeAST t | t <- types] ++ ")"
showTypeAST (FnTypeAST s t) = "(" ++ show s ++ " -> " ++ show t ++ ")"

commas :: [String] -> String
commas strings = List.foldr1 (++) (List.intersperse ", " strings)

-----------------------------------------------------------------------

typesEqual :: TypeAST -> TypeAST -> Bool
typesEqual TypeUnitAST (TupleTypeAST []) = True
typesEqual (TupleTypeAST as) (TupleTypeAST bs) = Prelude.and [typesEqual a b | (a, b) <- Prelude.zip as bs]
typesEqual ta tb = ta == tb

type Context = [(String, TypeAST)]

extendContext :: Context -> PrototypeAST -> Context
extendContext ctx proto =
    let vars = getBindings proto in
    vars ++ ctx

data TypecheckResult expr
    = Annotated        expr
    | TypecheckErrors [String]
    deriving (Show)

instance Functor TypecheckResult where
    fmap f (Annotated e)        = Annotated (f e)
    fmap _ (TypecheckErrors ss) = TypecheckErrors ss

instance Monad TypecheckResult where
    return                   = Annotated
    (TypecheckErrors ss) >>= _ = (TypecheckErrors ss)
    (Annotated e)        >>= f = f e
    fail msg                 = TypecheckErrors [msg]

getTypeCheckedType :: TypecheckResult AnnExpr -> TypeAST
getTypeCheckedType (Annotated e) = typeAST e
getTypeCheckedType (TypecheckErrors _) = MissingTypeAST "getTypeCheckedType"

typeJoin :: TypeAST -> TypeAST -> Maybe TypeAST
typeJoin (MissingTypeAST _) x = Just x
typeJoin x (MissingTypeAST _) = Just x
typeJoin x y = if typesEqual x y then Just x else Nothing

typecheck :: Context -> ExprAST -> TypecheckResult AnnExpr
typecheck ctx expr =
    case expr of
        E_FnAST (FnAST proto body)  ->
            let extCtx = extendContext ctx proto in
            do annbody <- typecheck extCtx body
               let j = typeJoin (prototypeASTretType proto) (typeAST annbody)
               if isJust j
                 then
                   let annproto = case proto of
                                   (PrototypeAST t s vars) ->
                                    (AnnPrototype (fromJust j) s vars) in
                   return (E_AnnFn (AnnFn annproto annbody))
                 else TypecheckErrors ["FnAST: proto ret type did not match body: "
                                            ++ show (prototypeASTretType proto)
                                            ++ " vs " ++ show (typeAST annbody)]

        BoolAST         b    -> do return (AnnBool b)
        IfAST         a b c  -> do ea <- typecheck ctx a
                                   eb <- typecheck ctx b
                                   ec <- typecheck ctx c
                                   if typesEqual (typeAST ea) (NamedTypeAST "i1") then
                                    if typesEqual (typeAST eb) (typeAST ec)
                                        then return (AnnIf (typeAST eb) ea eb ec)
                                        else TypecheckErrors ["IfAST: types of branches didn't match"]
                                    else TypecheckErrors ["IfAST: type of conditional wasn't BoolAST"]

        CallAST     b a ->
           do ea <- typecheck ctx a
              eb <- typecheck ctx b
              case (typeAST eb, typeAST ea) of
                 (FnTypeAST formaltype restype, argtype) ->
                    if typesEqual formaltype argtype
                        then return $ AnnCall restype eb ea
                        else TypecheckErrors ["CallAST mismatches:\n"
                                               ++ show formaltype ++ "\nvs\n" ++ show argtype]
                 otherwise -> TypecheckErrors ["CallAST w/o FnAST type: " ++ (showStructureA eb) ++ " :: " ++ (show $ typeAST eb)]

        IntAST i s1 s2 i2    -> do return (AnnInt (NamedTypeAST "i32") i s1 s2 i2)
        SeqAST        es     -> let subparts = map (typecheck ctx) es in
                                if Prelude.and (map isAnnotated subparts)
                                    then return (AnnSeq (typeAST . annotated $ Prelude.last subparts)
                                                        [annotated part | part <- subparts])
                                    else TypecheckErrors $ collectErrors subparts
        SubscriptAST  a b    -> do ta <- typecheck ctx a
                                   tb <- typecheck ctx b
                                   TypecheckErrors ["SubscriptAST"]
        E_PrototypeAST (PrototypeAST t s es) ->
                                TypecheckErrors ["PrototypeAST"]
        TupleAST      es b   ->
        -- We want to examine  every part of the tuple, and
        -- collect all the errors that we find in the subparts, not just the first.
            let subparts = map (typecheck ctx) es in
            if Prelude.and (map isAnnotated subparts)
                then return (AnnTuple [annotated part | part <- subparts] b)
                else TypecheckErrors $ collectErrors subparts
        VarAST mt s -> case lookup s ctx of
                        Just t ->  Annotated $ E_AnnVar (AnnVar t s)
                        Nothing -> TypecheckErrors ["Missing var " ++ s]
        CompilesAST   e c    -> case c of
                                    CS_NotChecked ->
                                      return $ AnnCompiles $ case typecheck ctx e of
                                        Annotated ae -> CS_WouldCompile
                                        otherwise    -> CS_WouldNotCompile
                                    otherwise -> return $ AnnCompiles c
annotated :: TypecheckResult AnnExpr -> AnnExpr
annotated (Annotated x) = x
annotated _ = error "Can't extract annotated part from typecheck error!"

isAnnotated :: TypecheckResult AnnExpr -> Bool
isAnnotated (Annotated _) = True
isAnnotated _ = False

errsTypecheckResult :: TypecheckResult AnnExpr -> [String]
errsTypecheckResult (Annotated _) = []
errsTypecheckResult (TypecheckErrors es) = es

collectErrors :: [TypecheckResult AnnExpr] -> [String]
collectErrors results =
    [e | r <- results, e <- errsTypecheckResult r, e /= ""]
-----------------------------------------------------------------------

getRootContext :: () -> Context
getRootContext () =
    [("llvm_readcyclecounter", FnTypeAST TypeUnitAST (NamedTypeAST "i64"))
    ,("expect_i32", FnTypeAST (NamedTypeAST "i32") TypeUnitAST)
    ,( "print_i32", FnTypeAST (NamedTypeAST "i32") TypeUnitAST)
    ,(  "read_i32", FnTypeAST TypeUnitAST (NamedTypeAST "i32"))
    ,("expect_i1", FnTypeAST (NamedTypeAST "i1") TypeUnitAST)
    ,( "print_i1", FnTypeAST (NamedTypeAST "i1") TypeUnitAST)

    --,("primitive_<_i64", FnTypeAST (TupleTypeAST [(NamedTypeAST "i64"), (NamedTypeAST "i64")]) (NamedTypeAST "i1"))
    ,("primitive_<_i64", FnTypeAST (TupleTypeAST [(NamedTypeAST "i32"), (NamedTypeAST "i64")]) (NamedTypeAST "i1"))
    ,("primitive_-_i64", FnTypeAST (TupleTypeAST [(NamedTypeAST "i64"), (NamedTypeAST "i64")]) (NamedTypeAST "i64"))
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
    inspect typechecked
    return ()

inspect :: TypecheckResult AnnExpr -> IO ()
inspect typechecked =
    case typechecked of
        Annotated e -> do putStrLn $ "Successful typecheck! " ++  showStructureA e
        TypecheckErrors errs ->
            F.forM_ errs $ \err -> do putStrLn $ "Typecheck error: " ++ err

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

compileStatus :: Maybe String -> CompilesStatus
compileStatus Nothing                   = CS_NotChecked
compileStatus (Just "kWouldCompile")    = CS_WouldCompile
compileStatus (Just "kWouldNotCompile") = CS_WouldNotCompile
compileStatus (Just x                 ) = error $ "Unable to interpret compiles status " ++ x

parseCompiles pbexpr =  CompilesAST (part 0 $ PbExpr.parts pbexpr)
                                    (compileStatus $ fmap uToString $ PbExpr.compiles_status pbexpr)

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

parseVar :: Expr -> ExprAST
parseVar pbexpr = VarAST (fmap parseType (PbExpr.type' pbexpr))
                       $ uToString (fromJust $ PbExpr.name pbexpr)

emptyRange :: ESourceRange
emptyRange = ESourceRange e e "<no file>"
                    where e = (ESourceLocation (-1::Int) (-1::Int))

parseProtoP :: Expr -> PrototypeAST
parseProtoP pbexpr =
    case PbExpr.proto pbexpr of
                Nothing  -> error "Need a proto to parse a proto!"
                Just proto  -> parseProtoPP proto (getType pbexpr)

parseProto :: Expr -> ExprAST
parseProto pbexpr = E_PrototypeAST (parseProtoP pbexpr)

getVarName :: ExprAST -> String
getVarName (VarAST mt s) = s

-- used?
getVar :: Expr -> ExprAST
getVar e = case PbExpr.tag e of
            VAR -> parseVar e
            _   -> error "getVar must be given a var!"

getType :: Expr -> TypeAST
getType e = case PbExpr.type' e of
                Just t -> parseType t
                Nothing -> MissingTypeAST "getType"

getFormal :: Expr -> AnnVar
getFormal e = case PbExpr.tag e of
            VAR -> case parseVar e of
                    (VarAST mt v) ->
                        case mt of
                            Just t  -> (AnnVar t v)
                            Nothing -> (AnnVar (MissingTypeAST "getFormal") v)
            _   -> error "getVar must be given a var!"

parseProtoPP :: Proto -> TypeAST ->  PrototypeAST
parseProtoPP proto retTy =
    let args = Proto.in_args proto in
    let vars = map getFormal $ toList args in
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
                VAR     -> parseVar
                Foster.Pb.Expr.Tag.TUPLE   -> parseTuple
                Foster.Pb.Expr.Tag.FN      -> parseFn
                PROTO   -> parseProto
                CALL    -> parseCall
                SEQ     -> parseSeq
                SUBSCRIPT -> parseSubscript
        in
   fn pbexpr




parseType :: Type -> TypeAST
parseType t = case PbType.tag t of
                PbTypeTag.LLVM_NAMED -> NamedTypeAST $ uToString (fromJust $ PbType.name t)
                PbTypeTag.REF -> error "Ref types not yet implemented"
                PbTypeTag.FN -> parseFnTy . fromJust $ PbType.fnty t
                PbTypeTag.TUPLE -> TupleTypeAST [parseType p | p <- toList $ PbType.tuple_parts t]
                PbTypeTag.TYPE_VARIABLE -> error "Type variable parsing not yet implemented."

parseFnTy :: FnType -> TypeAST
parseFnTy fty = FnTypeAST (parseType $ PbFnType.ret_type fty)
                          (TupleTypeAST [parseType x | x <- toList $ PbFnType.arg_types fty])
-----------------------------------------------------------------------


main :: IO ()
main = do
  args <- getArgs
  (f, outfile) <- case args of
         [infile, outfile] -> do
                protobuf <- L.readFile infile
                return (protobuf, outfile)
         _ -> do
                self <- getProgName
                return (error $ "Usage: " ++ self ++ " path/to/infile.pb path/to/outfile.pb")

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
        E_PrototypeAST (PrototypeAST t s es) -> (map (\(AnnVar t s) -> VarAST (Just t) s) es)
        TupleAST     es b    -> es
        VarAST       mt v    -> []

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
        VarAST mt v          -> "VarAST       " ++ v ++ " :: " ++ show mt

-----------------------------------------------------------------------

childrenOfA :: AnnExpr -> [AnnExpr]
childrenOfA e =
    case e of
        AnnBool         b                    -> []
        AnnCall    t b a                     -> [b, a]
        AnnCompiles   c                      -> []
        AnnIf      t  a b c                  -> [a, b, c]
        AnnInt t i s1 s2 i2                  -> []
        E_AnnFn (AnnFn p b)                  -> [E_AnnPrototype (MissingTypeAST "childrenOfA") p, b]
        AnnSeq      t es                     -> es
        AnnSubscript t a b                   -> [a, b]
        E_AnnPrototype t' (AnnPrototype t s es) -> [E_AnnVar v | v <- es]
        AnnTuple     es b                    -> es
        E_AnnVar      v                      -> []

-- Formats a single-line tag for the given ExprAST node.
-- Example:  textOf (VarAST "x")      ===     "VarAST x"
textOfA :: AnnExpr -> Int -> String
textOfA e width =
    let spaces = Prelude.replicate width '\SP'  in
    case e of
        AnnBool         b    -> "AnnBool      " ++ (show b)
        AnnCall    t b a     -> "AnnCall      " ++ " :: " ++ show t
        AnnCompiles     c    -> "AnnCompiles  "
        AnnIf      t  a b c  -> "AnnIf        " ++ " :: " ++ show t
        AnnInt ty i t c base -> "AnnInt       " ++ t ++ " :: " ++ show ty
        E_AnnFn (AnnFn a b)  -> "AnnFn        "
        AnnSeq     t  es     -> "AnnSeq       " ++ " :: " ++ show t
        AnnSubscript  t a b    -> "AnnSubscript " ++ " :: " ++ show t
        E_AnnPrototype t (AnnPrototype rt s es)     -> "PrototypeAST " ++ s ++ " :: " ++ show t
        AnnTuple     es b    -> "AnnTuple     "
        E_AnnVar (AnnVar t v) -> "AnnVar       " ++ v ++ " :: " ++ show t

-----------------------------------------------------------------------
varName (VarAST mt name) = name
avarName (AnnVar _ s) = s
avarType (AnnVar t _) = t

getBindings :: PrototypeAST -> [(String, TypeAST)]
getBindings (PrototypeAST t s vars) =
    map (\v -> (avarName v, avarType v)) vars

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

showStructureA :: AnnExpr -> String
showStructureA e = showStructureP e "" False where
    showStructureP e prefix isLast =
        let children = childrenOfA e in
        let thisIndent = prefix ++ if isLast then "└─" else "├─" in
        let nextIndent = prefix ++ if isLast then "  " else "│ " in
        let padding = max 6 (60 - Prelude.length thisIndent) in
        -- [ (child, index, numchildren) ]
        let childpairs = Prelude.zip3 children [1..]
                               (Prelude.repeat (Prelude.length children)) in
        let childlines = map (\(c, n, l) ->
                                showStructureP c nextIndent (n == l))
                             childpairs in
        thisIndent ++ (textOfA e padding ++ "\n") ++ Prelude.foldl (++) "" childlines

-----------------------------------------------------------------------
