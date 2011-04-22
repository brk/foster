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
             | SSCoro     Coro
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
        | ITyApp       SSTerm  TypeAST
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
    ILTyApp t e argty      -> SSTmExpr  $ ITyApp (tr e) argty

-- ... which lifts in a  straightfoward way to procedure definitions.
ssProcDefFrom pd =
  SSProcDef (ilProcIdent pd) (ilProcVars pd)
               (ssTermOfExpr (ilProcBody pd))

-- To interpret a program, we construct a coroutine for main
-- (no arguments need be passed yet) and step until the program finishes.
interpretProg prog = do
  let procmap = buildProcMap prog
  let main = (procmap Map.! (Ident "main" irrelevantIdentNum))
  let mainCoro = Coro (ssProcBody main) [] Map.empty CoroStatusRunning Nothing
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
        , hpMap  :: Map Location SSValue
}
data CoroStatus = CoroStatusInvalid
                | CoroStatusSuspended
                | CoroStatusDormant
                | CoroStatusRunning
                | CoroStatusDead
                deriving (Show)
data Coro = Coro {
    coroTerm :: SSTerm
  , coroArgs :: [AnnVar]
  , coroEnv  :: Map Ident SSValue
  , coroStat :: CoroStatus
  , coroPrev :: Maybe Location
} deriving (Show)

data MachineState = MachineState {
           stProcmap :: Map Ident SSProcDef
        ,  stHeap    :: Heap
        ,  stCoro    :: Coro
}

coroFromClosure gs (ILClosure id avars) =
  let ssproc = (stProcmap gs) Map.! id in
  let ins avar map = Map.insert (avarIdent avar) (getval gs avar) map in
  let initmap = List.foldr ins Map.empty avars in
  Coro (ssProcBody ssproc) (ssProcVars ssproc) initmap CoroStatusSuspended Nothing

modifyHeap gs loc val =
  let heap = stHeap gs in
  heap { hpMap = Map.insert loc val (hpMap heap) }

extendHeap :: MachineState -> SSValue -> (Location, MachineState)
extendHeap gs val =
  let heap = stHeap gs in
  let loc = nextLocation (hpBump heap) in
  let hmp = Map.insert loc val (hpMap heap) in
  (loc, gs { stHeap = Heap { hpBump = loc, hpMap = hmp } })

lookupHeap :: MachineState -> Location -> SSValue
lookupHeap gs loc =
  case Map.lookup loc (hpMap (stHeap gs)) of
    Just v -> v
    Nothing -> error $ "Unable to find heap cell for location " ++ show loc

termOf gs = coroTerm (stCoro gs)

isGlobalPrimitive name = case name of
  "coro_invoke" -> True
  otherwise -> False

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
    SSTmExpr e -> do --putStrLn (show e)
                     stepExpr gs e
    SSTmValue _ -> return gs

stepExpr :: MachineState -> IExpr -> IO MachineState
stepExpr gs expr =
  let coro = stCoro gs in
  case expr of
    IVar avar              -> do return $ withTerm gs (SSTmValue $ getval gs avar)
    ITuple     vs          -> do return $ withTerm gs (SSTmValue $ SSTuple (map (getval gs) vs))
    IClosures bnds clos e  ->
      -- This is not quite right; closures should close over each other!
      let clovals = map SSClosure clos in
      let gs' = extendEnv gs bnds clovals in
      return $ withTerm gs' e

    ILetVal x b e          ->
      case b of
        SSTmValue bval -> let env' = Map.insert x bval (coroEnv coro) in
                          let newCoro = coro { coroTerm = e, coroEnv = env' } in
                          return $ gs { stCoro = newCoro }
        SSTmExpr _     -> step (withTerm gs b) >>= \gs' ->
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

    ITyApp e@(SSTmExpr (IVar (AnnVar _ (Ident "coro_invoke" _)))) argty
      -> return $ withTerm gs e

    ITyApp e@(SSTmExpr _) argty ->
       do gs' <- step (withTerm gs e)
          return $ withTerm gs' (SSTmExpr $ ITyApp (termOf gs' ) argty)

    ITyApp (SSTmValue e) argty -> error $ "step iltyapp " ++ show e

extendEnv gs names args =
  let ins (id, arg) map = Map.insert id arg map in
  let coro = stCoro gs in
  let env  = coroEnv coro in
  let env' = List.foldr ins env (zip names args) in
  gs { stCoro = coro {coroEnv = env' } }

tryInvokeToCoro gs loc args =
  let (SSCoro ncoro) = lookupHeap gs loc in
  let ccoro = stCoro gs in
  -- Change ccoro state to suspended
  -- ensure that ncoro is not dead or running
  -- change ncoro state to running
  let gs2 = gs {
      stHeap = modifyHeap gs loc (SSCoro $ ccoro { coroStat = CoroStatusSuspended })
    , stCoro = ncoro { coroPrev = (Just loc), coroStat = CoroStatusRunning }
  } in
  extendEnv gs2 (tail $ map avarIdent $ coroArgs ncoro) args

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

tryEvalPrimitive gs "primitive_bitnot_i1" [SSBool b] =
  return $ withTerm gs (SSTmValue $ SSBool (not b))

tryEvalPrimitive gs "force_gc_for_debugging_purposes" _args =
  return $ withTerm gs (SSTmValue $ SSTuple [])

{- "Rule 4 describes the action of creating a coroutine.
    It creates a new label to represent the coroutine and extends the
    store with a mapping from this label to the coroutine main function." -}
tryEvalPrimitive gs ("coro_create_i32_i32") [SSClosure clo] =
  let coro = coroFromClosure gs clo in
  let (loc, gs') = extendHeap gs (SSCoro coro) in
  return $ withTerm gs' (SSTmValue $ SSLocation loc)

tryEvalPrimitive gs ("appty_coro_invoke") ((SSLocation loc):args) =
  return $ tryInvokeToCoro gs loc args

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
display (SSCoro    c ) = "<coro>"

