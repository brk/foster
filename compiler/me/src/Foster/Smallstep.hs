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

-- Extend ILExpr et al with a way of representing
-- intermediate results of evaluation like locations
-- and closures.

-- A term is either a normal-form value,
-- or a non-normal-form expression.
data SSTerm = SSTmExpr  IExpr
            | SSTmValue SSValue
            deriving (Show)

data SSValue = SSBool     Bool
             | SSInt      LiteralInt
             | SSTuple    [SSValue]
             | SSLocation Location
             | SSClosure  ILClosure
             deriving (Show)

-- Expressions are terms that are not in normal form.
data IExpr =
          ITuple [AnnVar]
        | IVar    AnnVar
        -- Procedures may be implicitly recursive,
        -- but we need to put a smidgen of effort into
        -- codegen-ing closures so they can be mutually recursive.
        | IClosures    [Ident] [ILClosure] SSTerm
        | ILetVal       Ident    SSTerm    SSTerm
        | ISubscript   AnnVar SSTerm
        | IIf          AnnVar SSTerm SSTerm
        | ICall        AnnVar [AnnVar]
        | ITyApp       TypeAST SSTerm  TypeAST
        deriving (Show)

data SSProcDef = SSProcDef { ssProcIdent      :: Ident
                           , ssProcVars       :: [AnnVar]
                           , ssProcBody       :: SSTerm
                           } deriving Show

-- There is a trivial translation from ILExpr to SSTerm...
ssTermOfExpr :: ILExpr -> SSTerm
ssTermOfExpr expr =
  let tr = ssTermOfExpr in
  case expr of
    ILBool b               -> SSTmValue $ SSBool b
    ILInt t i              -> SSTmValue $ SSInt i
    ILVar a                -> SSTmExpr  $ IVar a
    ILTuple vs             -> SSTmExpr  $ ITuple vs
    ILClosures bnds clos e -> SSTmExpr  $ IClosures bnds clos (tr e)
    ILLetVal x b e         -> SSTmExpr  $ ILetVal x (tr b) (tr e)
    ILCall    t b vs       -> SSTmExpr  $ ICall b vs
    ILIf      t  v b c     -> SSTmExpr  $ IIf v (tr b) (tr c)
    ILSubscript t a b      -> SSTmExpr  $ ISubscript a (tr b)
    ILTyApp t e argty      -> SSTmExpr  $ ITyApp t (tr e) argty

-- ... which lifts in a  straightfoward way to procedure definitions.
ssProcDefFrom pd =
  SSProcDef (ilProcIdent pd) (ilProcVars pd)
               (ssTermOfExpr (ilProcBody pd))

-- To interpret a program, we construct a coroutine for main
-- (no arguments need be passed yet) and step until the program finishes.
interpretProg prog = do
  let procmap = buildProcMap prog
  let main = (procmap Map.! (Ident "main" irrelevantIdentNum))
  let mainCoro = Coro (ssProcBody main) Map.empty
  let emptyHeap = Heap 0 Map.empty
  let globalState = MachineState procmap emptyHeap mainCoro
  val <- interpret globalState
  return val

interpret gs =
  case (termOf gs) of
    SSTmValue _ -> do return gs
    otherwise   -> do gs' <- step gs
                      interpret gs'

buildProcMap (ILProgram procdefs) =
  List.foldr ins Map.empty procdefs where
    ins procdef map = Map.insert (ilProcIdent procdef)
                                 (ssProcDefFrom procdef) map

type Location = Int
nextLocation x = x + 1
data Heap = Heap {
          hpBump :: Location
        , hpMap  :: Map Location SSTerm
}
data Coro = Coro {
    coroTerm :: SSTerm
  , coroEnv  :: Map Ident SSValue
}
data MachineState = MachineState {
           stProcmap :: Map Ident SSProcDef
        ,  stHeap    :: Heap
        ,  stCoro    :: Coro
}

termOf gs = coroTerm (stCoro gs)

getval :: MachineState -> AnnVar -> SSValue
getval gs avar = case Map.lookup (avarIdent avar) (coroEnv (stCoro gs)) of
        Just e -> e
        Nothing -> error $ "Unable to look up local variable " ++ show avar

withTerm gs e =
  let coro = stCoro gs in
  gs { stCoro = coro { coroTerm = e } }

step :: MachineState -> IO MachineState
step gs =
  let coro = stCoro gs in
  case coroTerm coro of
    SSTmExpr e -> stepExpr gs e
    SSTmValue _ -> return gs

stepExpr :: MachineState -> IExpr -> IO MachineState
stepExpr gs expr =
  let coro = stCoro gs in
  case expr of
    ITuple     vs          -> do return gs -- TODO
    IVar (AnnVar t i)      -> do return gs
    IClosures bnds clos e  -> error $ "step ilclo bnds=" ++ show bnds ++ "\nclos = " ++ show clos
    ILetVal x b e          ->
      case b of
        SSTmValue bval -> let env' = Map.insert x bval (coroEnv coro) in
                          let newCoro = coro { coroTerm = e, coroEnv = env' } in
                          return $ gs { stCoro = newCoro }
        SSTmExpr _     -> do
                          gs' <- step (withTerm gs b)
                          {- TODO: gs might contain a non-expr value... -}
                          return $ withTerm gs' (SSTmExpr $ ILetVal x (termOf gs' ) e)
    ICall b vs ->
        let args = map (getval gs) vs in
        case Map.lookup (avarIdent b) (stProcmap gs) of
           Just proc ->
              let names = map avarIdent (ssProcVars proc) in
              let gs' = extendEnv gs names args in
              return $ withTerm gs' (ssProcBody proc)
           Nothing -> tryEvalPrimitive gs (identPrefix (avarIdent b)) args

    IIf v b c ->
        case getval gs v of
           (SSBool True ) -> return $ withTerm gs b
           (SSBool False) -> return $ withTerm gs c
           otherwise -> error "if cond was not a boolean"

    ISubscript v (SSTmValue (SSInt i)) ->
        let n = fromInteger (litIntValue i) in
        case getval gs v of
          SSTuple vals ->
               return $ withTerm gs (SSTmValue (vals !! n))
          _ -> error "Expected base of subscript to be tuple value"

    ISubscript v e@(SSTmExpr _) ->
      do gs' <- step (withTerm gs e)
         return $ withTerm gs' (SSTmExpr $ ISubscript v (termOf gs' ))

    ISubscript v (SSTmValue e) ->
      error $ ("step ilsubsc "  ++ show v ++ " // " ++ show e)

    ITyApp t e argty -> error "step iltyapp"

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

tryEvalPrimitive :: MachineState -> String -> [SSValue] -> IO MachineState
tryEvalPrimitive gs primName [SSInt i1, SSInt i2]
  | isJust (tryGetInt32PrimOp2Int32 primName) =
 let (Just fn) = tryGetInt32PrimOp2Int32 primName in
 return $ withTerm gs (SSTmValue $ SSInt (fn i1 i2))

tryEvalPrimitive gs primName [SSInt i1, SSInt i2]
  | isJust (tryGetInt32PrimOp2Bool primName) =
 let (Just fn) = tryGetInt32PrimOp2Bool primName in
 return $ withTerm gs (SSTmValue $ SSBool (liftInt fn i1 i2))


tryEvalPrimitive gs "primitive_negate_i32" [SSInt i] =
 let int = litIntValue i in
 return $ withTerm gs (SSTmValue $ SSInt (i { litIntValue = negate int }))

tryEvalPrimitive gs "force_gc_for_debugging_purposes" _args =
  return $ withTerm gs (SSTmValue $ SSTuple [])

tryEvalPrimitive gs primName [val]
  | isPrintFunction primName =
      do putStrLn (display val)
         return $ withTerm gs (SSTmValue val)

tryEvalPrimitive gs "expect_i32b" [val@(SSInt i)] =
      do putStrLn (showBits32 (litIntValue i))
         return $ withTerm gs (SSTmValue val)

tryEvalPrimitive gs "print_i32b" [val@(SSInt i)] =
      do putStrLn (showBits32 (litIntValue i))
         return $ withTerm gs (SSTmValue val)

tryEvalPrimitive gs primName args =
      error ("step ilcall " ++ show primName ++ " with args: " ++ show args)

showBits32 n =
  let bits = map (testBit n) [0 .. (32 - 1)] in
  let s = map (\b -> if b then '1' else '0') bits in
  (reverse s) ++ "_2"


display :: SSValue -> String
display (SSBool True ) = "true"
display (SSBool False) = "false"
display (SSInt i     ) = show (litIntValue i)
display (SSTuple vals) = "(" ++ joinWith ", " (map display vals) ++ ")"
display (SSLocation z) = "<location " ++ show z ++ ">"
display (SSClosure c ) = "<closure>"
