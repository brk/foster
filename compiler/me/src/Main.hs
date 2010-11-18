-----------------------------------------------------------------------------
-- Copyright (c) 2010 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Main (
main
) where

import System.Environment(getArgs,getProgName)

import qualified Data.ByteString.Lazy as L(readFile)
import qualified Data.ByteString.Lazy.UTF8 as U(toString)
import qualified System.IO.UTF8 as U(putStrLn)

import Data.Maybe(isJust, fromJust)
import Data.Foldable(forM_)
import Monad(join,liftM)
--import Data.IORef(IORef,newIORef,readIORef,writeIORef)

import Text.ProtocolBuffers(messageGet)

import Foster.ProtobufUtils
import Foster.ExprAST
import Foster.TypeAST

-----------------------------------------------------------------------

--outLn = U.putStrLn . U.toString . utf8

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
        | AnnSeq        AnnExpr AnnExpr
        | AnnSubscript  TypeAST AnnExpr AnnExpr
        | E_AnnPrototype  TypeAST AnnPrototype
        | E_AnnVar       AnnVar
        deriving Show

data AnnFn        = AnnFn           AnnPrototype AnnExpr deriving (Show)
data AnnPrototype = AnnPrototype    { annProtoReturnType :: TypeAST
                                    , annProtoName       :: String
                                    , annProtoVars       :: [AnnVar]
                                    } deriving (Show)

typeAST :: AnnExpr -> TypeAST
-- {{{
typeAST (AnnBool _)          = fosBoolType
typeAST (AnnInt t _ _ _ _)   = t
typeAST (AnnTuple es b)      = TupleTypeAST [typeAST e | e <- es]
typeAST (E_AnnFn (AnnFn (AnnPrototype rt s vs) e))
                             = FnTypeAST (normalizeTypes [t | (AnnVar t v) <- vs]) rt
typeAST (AnnCall t b a)      = t
typeAST (AnnCompiles c)      = fosBoolType
typeAST (AnnIf t a b c)      = t
typeAST (AnnSeq a b)         = typeAST b
typeAST (AnnSubscript t _ _) = t
typeAST (E_AnnPrototype t p) = t
typeAST (E_AnnVar (AnnVar t s)) = t
-- }}}

unbuildSeqsA :: AnnExpr -> [AnnExpr]
unbuildSeqsA (AnnSeq a b) = a : unbuildSeqsA b
unbuildSeqsA expr = [expr]

-----------------------------------------------------------------------

typesEqual :: TypeAST -> TypeAST -> Bool
typesEqual TypeUnitAST (TupleTypeAST []) = True
typesEqual (TupleTypeAST as) (TupleTypeAST bs) = Prelude.and [typesEqual a b | (a, b) <- Prelude.zip as bs]
typesEqual ta tb = ta == tb

getBindings :: PrototypeAST -> [(String, TypeAST)]
getBindings (PrototypeAST t s vars) =
    map (\v -> (avarName v, avarType v)) vars

type Context = [(String, TypeAST)]

extendContext :: Context -> PrototypeAST -> Context
extendContext ctx proto = (getBindings proto) ++ ctx

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

throwError :: String -> TypecheckResult AnnExpr
throwError s = TypecheckErrors [s]

typecheck :: Context -> ExprAST -> Maybe TypeAST -> TypecheckResult AnnExpr
typecheck ctx expr maybeExpTy =
    case expr of
        E_FnAST (FnAST proto body)  ->
            let extCtx = extendContext ctx proto in
            do annbody <- typecheck extCtx body Nothing
               let j = typeJoin (prototypeASTretType proto) (typeAST annbody)
               if isJust j
                 then
                   let annproto = case proto of
                                   (PrototypeAST t s vars) ->
                                    (AnnPrototype (fromJust j) s vars) in
                   return (E_AnnFn (AnnFn annproto annbody))
                 else throwError $ "FnAST: proto ret type did not match body: "
                                            ++ show (prototypeASTretType proto)
                                            ++ " vs " ++ show (typeAST annbody)

        BoolAST         b    -> do return (AnnBool b)
        IfAST         a b c  -> do ea <- typecheck ctx a (Just fosBoolType)
                                   eb <- typecheck ctx b Nothing
                                   ec <- typecheck ctx c Nothing
                                   if typesEqual (typeAST ea) (NamedTypeAST "i1") then
                                    if typesEqual (typeAST eb) (typeAST ec)
                                        then return (AnnIf (typeAST eb) ea eb ec)
                                        else throwError $ "IfAST: types of branches didn't match"
                                    else throwError $ "IfAST: type of conditional wasn't BoolAST"

        CallAST     b a ->
           do ea <- typecheck ctx a Nothing
              eb <- typecheck ctx b Nothing
              case (typeAST eb, typeAST ea) of
                 (FnTypeAST formaltype restype, argtype) ->
                    if typesEqual formaltype argtype
                        then return $ AnnCall restype eb ea
                        else throwError $ "CallAST mismatches:\n"
                                               ++ show formaltype ++ "\nvs\n" ++ show argtype
                 otherwise -> throwError $ "CallAST w/o FnAST type: " ++ (showStructureA eb)
                                               ++ " :: " ++ (show $ typeAST eb)

        IntAST i s1 s2 i2    -> do return (AnnInt (NamedTypeAST "i32") i s1 s2 i2)
        SeqAST a b -> do
            ea <- typecheck ctx a (Just TypeUnitAST)
            eb <- typecheck ctx b maybeExpTy
            return (AnnSeq ea eb)
        SubscriptAST  a b    -> do ta <- typecheck ctx a Nothing
                                   tb <- typecheck ctx b Nothing
                                   throwError $ "SubscriptAST"
        E_PrototypeAST (PrototypeAST t s es) ->
                                throwError "PrototypeAST"
        TupleAST      es b   ->
        -- We want to examine  every part of the tuple, and
        -- collect all the errors that we find in the subparts, not just the first.
            let subparts = map (\e -> typecheck ctx e Nothing) es in
            if Prelude.and (map isAnnotated subparts)
                then return (AnnTuple [part | (Annotated part) <- subparts] b)
                else TypecheckErrors $ collectErrors subparts
        VarAST mt s -> case lookup s ctx of
                        Just t ->  Annotated $ E_AnnVar (AnnVar t s)
                        Nothing -> throwError $ "Missing var " ++ s
        CompilesAST   e c  ->
            case c of
            CS_NotChecked ->
              return $ AnnCompiles $ case typecheck ctx e Nothing of
                Annotated ae -> CS_WouldCompile
                otherwise    -> CS_WouldNotCompile
            otherwise -> return $ AnnCompiles c


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

listModule :: ModuleAST -> IO ()
listModule mod = do
    forM_ (moduleASTFunctions mod) $ \ast -> do
        putStrLn "ast:"
        putStrLn $ showStructure (E_FnAST ast)
        putStrLn "typechecking..."
        let typechecked = typecheck (getRootContext ()) (E_FnAST ast) Nothing
        putStrLn "typechecked:"
        inspect typechecked
    return ()

inspect :: TypecheckResult AnnExpr -> IO Bool
inspect typechecked =
    case typechecked of
        Annotated e -> do
            putStrLn $ "Successful typecheck! " ++ showStructureA e
            return True
        TypecheckErrors errs -> do
            forM_ errs $ \err -> do putStrLn $ "Typecheck error: " ++ err
            return False

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
    Right (pb_exprs,_) -> listModule $ parseSourceModule pb_exprs

  return ()


-----------------------------------------------------------------------

fnTypeFrom :: AnnPrototype -> AnnExpr -> TypeAST
fnTypeFrom p b =
    let intype = normalizeTypes [avarType v | v <- annProtoVars p] in
    let outtype = typeAST b in
    FnTypeAST intype outtype

childrenOfA :: AnnExpr -> [AnnExpr]
childrenOfA e =
    case e of
        AnnBool         b                    -> []
        AnnCall    t b a                     -> [b, a]
        AnnCompiles   c                      -> []
        AnnIf      t  a b c                  -> [a, b, c]
        AnnInt t i s1 s2 i2                  -> []
        E_AnnFn (AnnFn p b)                  -> [E_AnnPrototype t p, b] where t = fnTypeFrom p b
        AnnSeq      a b                      -> unbuildSeqsA e
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
        AnnSeq          a b  -> "AnnSeq       " ++ " :: " ++ show (typeAST b)
        AnnSubscript  t a b    -> "AnnSubscript " ++ " :: " ++ show t
        E_AnnPrototype t (AnnPrototype rt s es)     -> "PrototypeAST " ++ s ++ " :: " ++ show t
        AnnTuple     es b    -> "AnnTuple     "
        E_AnnVar (AnnVar t v) -> "AnnVar       " ++ v ++ " :: " ++ show t

-----------------------------------------------------------------------
varName (VarAST mt name) = name
avarName (AnnVar _ s) = s
avarType (AnnVar t _) = t

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
