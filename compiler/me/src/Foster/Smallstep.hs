module Foster.Smallstep where

import List(foldr)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Int
import Data.Bits
import Data.Maybe(isJust)

import Foster.Base
import Foster.TypeAST
import Foster.ILExpr

interpretProg prog = do
  let procmap = buildProcMap prog
  let main = (procmap Map.! (Ident "main" irrelevantIdentNum))
  let mainCoro = Coro (ilProcBody main) Map.empty
  let emptyHeap = Heap 0 Map.empty
  let globalState = MachineState procmap emptyHeap mainCoro
  val <- interpret globalState
  return val

interpret gs =
  if isValue (exprOf gs)
     then do return gs
     else do gs' <- step gs
             interpret gs'

buildProcMap (ILProgram procdefs) =
  List.foldr ins Map.empty procdefs where
    ins procdef map = Map.insert (ilProcIdent procdef) procdef map

type Location = Int
nextLocation x = x + 1
data Heap = Heap {
          hpBump :: Location
        , hpMap  :: Map Location ILExpr
}
data Coro = Coro {
    coroExpr :: ILExpr
  , coroEnv  :: Map Ident ILExpr
}
data MachineState = MachineState {
           stProcmap :: Map Ident ILProcDef
        ,  stHeap    :: Heap
        ,  stCoro    :: Coro
}

exprOf gs = coroExpr (stCoro gs)
getval gs avar = case Map.lookup (avarIdent avar) (coroEnv (stCoro gs)) of
        Just e -> e
        Nothing -> error $ "Unable to look up local variable " ++ show avar

withExpr gs e =
  let coro = stCoro gs in
  gs { stCoro = coro { coroExpr = e } }

step gs =
  let coro = stCoro gs in
  case coroExpr coro of
    ILBool b                -> do return gs
    ILInt t _               -> do return gs
    ILTuple     vs          -> do return gs
    ILVar (AnnVar t i)      -> do return gs
    ILClosures bnds clos e  -> error "step ilclo"
    ILLetVal x b e          -> if isValue b
                                then
                                  let env' = Map.insert x b (coroEnv coro) in
                                  let newCoro = coro { coroExpr = e, coroEnv = env' } in
                                  return $ gs { stCoro = newCoro }
                                else do
                                  gs' <- step (withExpr gs b)
                                  return $ withExpr gs' (ILLetVal x (exprOf gs' ) e)
    ILCall t b vs ->
        let args = map (getval gs) vs in
        case Map.lookup (avarIdent b) (stProcmap gs) of
           Just proc ->
              let names = map avarIdent (ilProcVars proc) in
              let gs' = extendEnv gs names args in
              return $ withExpr gs' (ilProcBody proc)
           Nothing -> tryEvalPrimitive gs (identPrefix (avarIdent b)) args

    ILIf t v b c -> error "step ilif"
    ILSubscript t v (ILInt _ i) ->
        let n = fromInteger (litIntValue i) in
        case getval gs v of
          ILTuple vars -> return $ withExpr gs (getval gs (vars !! n))
          _ -> error "Expected base of subscript to be tuple"

    ILSubscript t v e ->
        if isValue e
          then error $ ("step ilsubsc " ++ show t ++ " !! " ++ show v ++ " // " ++ show e)
          else do gs' <- step (withExpr gs e)
                  return $ withExpr gs' (ILSubscript t v (exprOf gs' ))
    ILTyApp t e argty -> error "step iltyapp"

extendEnv gs names args =
  let ins (id, arg) map = Map.insert id arg map in
  let coro = stCoro gs in
  let env  = coroEnv coro in
  let env' = List.foldr ins env (zip names args) in
  gs { stCoro = coro {coroEnv = env' } }

isPrintFunction name =
  case name of
    "expect_i64" -> True
    "print_i64"  -> True
    "expect_i32" -> True
    "print_i32"  -> True
    "expect_i1"  -> True
    "print_i1"   -> True
    otherwise -> False

liftInt :: (Integral a) => (a -> a -> b) ->
          LiteralInt -> LiteralInt -> b
liftInt f i1 i2 =
  let v1 = fromInteger (litIntValue i1) in
  let v2 = fromInteger (litIntValue i2) in
  f v1 v2

modifyInt32With :: (Int32 -> Int32 -> Int32)
       -> LiteralInt -> LiteralInt -> LiteralInt
modifyInt32With f i1 i2 =
  let int = fromIntegral (liftInt f i1 i2) in
  i1 { litIntValue = int }

ashr32   a b = shiftR a (fromIntegral b)
shl32    a b = shiftL a (fromIntegral b)

tryGetInt32PrimOp2Int32 :: String -> Maybe (LiteralInt -> LiteralInt -> LiteralInt)
tryGetInt32PrimOp2Int32 name =
  case name of
    "primitive_*_i32"       -> Just (modifyInt32With (*))
    "primitive_+_i32"       -> Just (modifyInt32With (+))
    "primitive_-_i32"       -> Just (modifyInt32With (-))
    "primitive_/_i32"       -> Just (modifyInt32With div)
    "primitive_bitashr_i32" -> Just (modifyInt32With ashr32)
    "primitive_bitshl_i32"  -> Just (modifyInt32With shl32)
    "primitive_bitxor_i32"  -> Just (modifyInt32With xor)
    "primitive_bitor_i32"   -> Just (modifyInt32With (.|.))
    "primitive_bitand_i32"  -> Just (modifyInt32With (.&.))
    otherwise -> Nothing

tryGetInt32PrimOp2Bool :: String -> Maybe (Int32 -> Int32 -> Bool)
tryGetInt32PrimOp2Bool name =
  case name of
    "primitive_<_i32"        -> Just ((<))
    "primitive_<=_i32"       -> Just ((<=))
    "primitive_==_i32"       -> Just ((==))
    "primitive_!=_i32"       -> Just ((/=))
    "primitive_>=_i32"       -> Just ((>=))
    "primitive_>_i32"        -> Just ((>))
    otherwise -> Nothing

tryEvalPrimitive gs primName [ILInt t i1, ILInt _ i2]
  | isJust (tryGetInt32PrimOp2Int32 primName) =
 let (Just fn) = tryGetInt32PrimOp2Int32 primName in
 return $ withExpr gs (ILInt t (fn i1 i2))

tryEvalPrimitive gs primName [ILInt t i1, ILInt _ i2]
  | isJust (tryGetInt32PrimOp2Bool primName) =
 let (Just fn) = tryGetInt32PrimOp2Bool primName in
 return $ withExpr gs (ILBool (liftInt fn i1 i2))


tryEvalPrimitive gs "primitive_negate_i32" [ILInt t i] =
 let int = litIntValue i in
 return $ withExpr gs (ILInt t (i { litIntValue = negate int }))

tryEvalPrimitive gs "force_gc_for_debugging_purposes" _args =
  return $ withExpr gs (ILTuple [])

tryEvalPrimitive gs primName [val]
  | isPrintFunction primName =
      do putStrLn (display gs val)
         return $ withExpr gs val

tryEvalPrimitive gs "expect_i32b" [val@(ILInt _ i)] =
      do putStrLn (showBits32 (litIntValue i))
         return $ withExpr gs val

tryEvalPrimitive gs "print_i32b" [val@(ILInt _ i)] =
      do putStrLn (showBits32 (litIntValue i))
         return $ withExpr gs val

tryEvalPrimitive gs primName args =
      error ("step ilcall " ++ show primName ++ " with args: " ++ show args)

showBits32 n =
  let bits = map (testBit n) [0 .. (32 - 1)] in
  let s = map (\b -> if b then '1' else '0') bits in
  (reverse s) ++ "_2"

isValue (ILBool _)           = True
isValue (ILInt t _)          = True
isValue (ILTuple vs)         = True
isValue (ILVar (AnnVar t i)) = True
isValue (ILClosures n b e)   = False
isValue (ILLetVal x b e)     = False
isValue (ILCall t id expr)   = False
isValue (ILIf t a b c)       = False
isValue (ILSubscript t _ _)  = False
isValue (ILTyApp overallType tm tyArgs) = False

display gs (ILBool True)        = "true"
display gs (ILBool False)       = "false"
display gs (ILInt t i)          = show (litIntValue i)
display gs (ILTuple vs)         = "(" ++ joinWith ", " (map (display gs) (map (getval gs) vs)) ++ ")"
display gs (ILVar (AnnVar t i)) = show i
display gs (ILClosures n b e)   = "<...closures...>"
display gs (ILLetVal x b e)     = error "Should not try to display non-value expr!"
display gs (ILCall t id expr)   = error "Should not try to display non-value expr!"
display gs (ILIf t a b c)       = error "Should not try to display non-value expr!"
display gs (ILSubscript t _ _)  = error "Should not try to display non-value expr!"
display gs (ILTyApp overallType tm tyArgs) = error "Should not try to display non-value expr!"
