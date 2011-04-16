module Foster.Smallstep where

import List(foldr)
import Data.Map (Map)
import qualified Data.Map as Map

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
getvar gs avar = case Map.lookup (avarIdent avar) (coroEnv (stCoro gs)) of
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
        let args = map (getvar gs) vs in
        case Map.lookup (avarIdent b) (stProcmap gs) of
           Just proc ->
              let names = map avarIdent (ilProcVars proc) in
              let gs' = extendEnv gs names args in
              return $ withExpr gs' (ilProcBody proc)
           Nothing -> tryEvalPrimitive gs (identPrefix (avarIdent b)) args

    ILIf t v b c -> error "step ilif"
    ILSubscript t v (ILInt _ i) ->
        let n = fromInteger (litIntValue i) in
        case getvar gs v of
          ILTuple vars -> return $ withExpr gs (getvar gs (vars !! n))
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

tryEvalPrimitive gs "force_gc_for_debugging_purposes" args =
  do return $ withExpr gs (ILTuple [])

tryEvalPrimitive gs primName args =
    let coro = stCoro gs in
    if isPrintFunction primName
      then
           case args of
               [arg]      -> do putStrLn (show arg)
                                return $ gs { stCoro = coro { coroExpr=arg } }
               otherwise -> undefined
      else error ("step ilcall " ++ show primName)

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

interpret gs =
  if isValue (coroExpr (stCoro gs))
     then do return gs
     else do gs' <- step gs
             interpret gs'

