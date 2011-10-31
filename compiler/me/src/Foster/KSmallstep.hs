-----------------------------------------------------------------------------
-- Copyright (c) 2011 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.KSmallstep (
interpretKNormalMod
)
where

import Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Int
import Data.Bits
import Data.IORef
import Data.Array

import System.Console.ANSI
import Control.Exception(assert)

import Foster.Base
import Foster.TypeIL
import Foster.KNExpr

-- Relatively simple small-step "definitional" interpreter.
--
-- The largest chunks of complication come from
--   A) having coroutines, which forces us to explicitly model
--      stateful management of continuations in the store, and
--   B) enforcing proper lexical scoping with environments as
--      part of per-coroutine machine state.
--
-- But the flip side is that coroutines are *easier* to implement
-- (efficiently) at the real machine level, even if they're a tad
-- uglier in the abstract machine.

-- ||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

errFile gs = (stTmpDir gs) ++ "/istderr.txt"
outFile gs = (stTmpDir gs) ++ "/istdout.txt"

-- To interpret a program, we construct a coroutine for main
-- (no arguments need be passed yet) and step until the program finishes.
interpretKNormalMod kmod tmpDir = do
  let funcmap = Map.fromList $ map (\sf -> (ssFuncIdent sf, sf))
                             (map ssFunc (moduleILfunctions kmod))
  let main = (funcmap Map.! (GlobalSymbol "main"))
  let loc  = 0 :: Int
  let mainCoro = Coro { coroTerm = (ssFuncBody main)
                      , coroArgs = []
                      , coroEnv  = env
                      , coroStat = CoroStatusRunning
                      , coroLoc  = loc
                      , coroPrev = Nothing
                      , coroStack = [(env, Prelude.id)]
                      } where env = Map.empty
  let emptyHeap = Heap (nextLocation loc)
                       (Map.singleton loc (SSCoro mainCoro))
  let globalState = MachineState funcmap emptyHeap loc tmpDir

  _ <- writeFile (outFile globalState) ""
  _ <- writeFile (errFile globalState) ""

  stepsTaken <- newIORef 0
  val <- interpret stepsTaken globalState
  numSteps <- readIORef stepsTaken
  putStrLn ("Interpreter finished in " ++ show numSteps ++ " steps.")
  return val

-- Step a machine state until there is nothing left to step.
interpret :: IORef Int -> MachineState -> IO MachineState
interpret stepsTaken gs =
  case (coroStack $ stCoro gs) of
    [] -> do return gs
    _  -> do modifyIORef stepsTaken (+1)
             (interpret stepsTaken =<< step gs)

-- Stepping an expression is unsurprising.
-- To step a value, we pop a "stack frame" and apply the value to the
-- meta-continuation, which corresponds to the "hole" into which
-- the value should be plugged.
step :: MachineState -> IO MachineState
step gs =
  let coro = stCoro gs in
  case coroTerm coro of
    SSTmExpr e -> do --putStrLn ("\n\n" ++ show (coroLoc coro) ++ " ==> " ++ show e)
                     --putStrLn (show (coroLoc coro) ++ " ==> " ++ show (coroStack coro))
                     stepExpr gs e
    SSTmValue _ -> do let ((env, cont), gs2) = popContext gs
                      return $ withEnv (withTerm gs2 (cont (termOf gs2))) env

-- ||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

-- A machine state consists of a (static) mapping of proc ids to
-- proc definitions, a heap mapping locations (ints) to values,
-- and the location of the current coroutine. Note that the machine
-- state does not include the coroutine value itself!

data MachineState = MachineState {
           stFuncmap :: Map Ident SSFunc
        ,  stHeap    :: Heap
        ,  stCoroLoc :: Location
        ,  stTmpDir  :: String
}

-- A coroutine has an actively evaluating term, which is updated as part
-- of each machine step. The coroArgs are used when a coroutine is first
-- invoked to extend the environment associated with the active term.
-- Coroutines maintain a status to detect improper recursive invokes.
-- To be "mutated," coroutines also must know where they are stored.
-- coroPrev marks our invoker, if any (we have asymmetric coroutines).
-- The trickiest bit is the coroStack. TODO
data Coro = Coro {
    coroTerm :: SSTerm
  , coroArgs :: [Ident]
  , coroEnv  :: ValueEnv
  , coroStat :: CoroStatus
  , coroLoc  :: Location
  , coroPrev :: Maybe Location
  , coroStack :: [(ValueEnv, SSTerm -> SSTerm)]
} deriving (Show)

type ValueEnv = Map Ident SSValue

data CoroStatus = CoroStatusInvalid
                | CoroStatusSuspended
                | CoroStatusDormant
                | CoroStatusRunning
                | CoroStatusDead
                deriving (Show, Eq)

-- ||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

type Location = Int
nextLocation x = x + 1
data Heap = Heap {
          hpBump :: Location
        , hpMap  :: Map Location SSValue
}

-- Fetch the current coroutine from the heap.
stCoro gs = let (SSCoro c) = lookupHeap gs (stCoroLoc gs) in c

lookupHeap :: MachineState -> Location -> SSValue
lookupHeap gs loc =
  case Map.lookup loc (hpMap (stHeap gs)) of
    Just v -> v
    Nothing -> error $ "Unable to find heap cell for location " ++ show loc

extendHeap :: MachineState -> SSValue -> (Location, MachineState)
extendHeap gs val =
  let heap = stHeap gs in
  let loc = nextLocation (hpBump heap) in
  let hmp = Map.insert loc val (hpMap heap) in
  (loc, gs { stHeap = Heap { hpBump = loc, hpMap = hmp } })

-- Simple helper to store two values in two locations.
modifyHeap2 gs l1 v1 l2 v2 =
  let heap = stHeap gs in
  heap { hpMap = Map.insert l2 v2 (Map.insert l1 v1 (hpMap heap)) }

-- Updates the value at the given location according to the provided function.
modifyHeapWith :: MachineState -> Location -> (SSValue -> SSValue)
               -> MachineState
modifyHeapWith gs loc fn =
  let oldheap = stHeap gs in
  let val  = lookupHeap gs loc in
  let heap = oldheap { hpMap = Map.insert loc (fn val) (hpMap oldheap) } in
  gs { stHeap = heap }

-- Pervasively used helper functions to update the term/env of the current coro.
withTerm gs e = modifyHeapWith gs (stCoroLoc gs) (\(SSCoro c) -> SSCoro $ c { coroTerm = e })
withEnv  gs e = modifyHeapWith gs (stCoroLoc gs) (\(SSCoro c) -> SSCoro $ c { coroEnv  = e })

-- ||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

-- A term is either a normal-form value,
-- or a non-normal-form expression.
data SSTerm = SSTmExpr  IExpr
            | SSTmValue SSValue
            deriving (Show)

-- Expressions are terms that are not values.
-- IExpr is a type-erased version of KNExpr.
data IExpr =
          ITuple [Ident]
        | IVar    Ident
        | IAlloc  Ident
        | IDeref  Ident
        | IStore  Ident Ident
        | ILetFuns     [Ident] [Fn KNExpr TypeIL] SSTerm
        | ILetVal       Ident   SSTerm  SSTerm
        | IArrayRead    Ident   Ident
        | IArrayPoke    Ident   Ident Ident
        | IAllocArray   Ident
        | IIf           Ident   SSTerm     SSTerm
        | IUntil                SSTerm     SSTerm
        | ICall         Ident  [Ident]
        | ICallPrim     ILPrim [Ident]
        | ICase         Ident  {-(DecisionTree KNExpr)-} [(Pattern, SSTerm)]
        | ITyApp        Ident  TypeIL
        | IAppCtor      CtorId [Ident]
        deriving (Show)

-- Values in the (intermediate) language are mostly standard.
-- Coro values are the most interesting, as defined above.
-- A closure value has a proc ident, env+captures var names,
-- and captured values.
data SSValue = SSBool      Bool
             | SSInt       Integer
             | SSArray     (Array Int Location)
             | SSTuple     [SSValue]
             | SSCtorVal   CtorId [SSValue]
             | SSLocation  Location
             | SSFunc      SSFunc
             | SSCoro      Coro
             deriving (Eq, Show)

-- There is a trivial translation from ILExpr to SSTerm...
ssTermOfExpr :: KNExpr -> SSTerm
ssTermOfExpr expr =
  let tr   = ssTermOfExpr in
  let idOf = tidIdent     in
  case expr of
    KNBool b               -> SSTmValue $ SSBool b
    KNInt _t i             -> SSTmValue $ SSInt $ litIntValue i
    KNVar v                -> SSTmExpr  $ IVar (idOf v)
    KNTuple vs             -> SSTmExpr  $ ITuple (map idOf vs)
    KNLetFuns ids funs e   -> SSTmExpr  $ ILetFuns ids funs (tr e)
    KNLetVal x b e         -> SSTmExpr  $ ILetVal x (tr b) (tr e)
    KNCall     _t b vs     -> SSTmExpr  $ ICall (idOf b) (map idOf vs)
    KNCallPrim _t b vs     -> SSTmExpr  $ ICallPrim b (map idOf vs)
    KNIf       _t  v b c   -> SSTmExpr  $ IIf (idOf v) (tr b) (tr c)
    KNUntil    _t  a b     -> SSTmExpr  $ IUntil    (tr a) (tr b)
    KNArrayRead _t a b     -> SSTmExpr  $ IArrayRead (idOf a) (idOf b)
    KNArrayPoke v b i      -> SSTmExpr  $ IArrayPoke (idOf v) (idOf b) (idOf i)
    KNAllocArray _ety n    -> SSTmExpr  $ IAllocArray (idOf n)
    KNAlloc a              -> SSTmExpr  $ IAlloc (idOf a)
    KNDeref   a            -> SSTmExpr  $ IDeref (idOf a)
    KNStore   a b          -> SSTmExpr  $ IStore (idOf a) (idOf b)
    KNTyApp _t v argty     -> SSTmExpr  $ ITyApp (idOf v) argty
    KNCase _t a bs {-dt-}  -> SSTmExpr  $ ICase (idOf a) {-dt-} [(p, tr e) | (p, e) <- bs]
    KNAppCtor _t cid vs    -> SSTmExpr  $ IAppCtor cid (map idOf vs)

-- ... which lifts in a  straightfoward way to procedure definitions.
ssFunc f =
    Func { ssFuncIdent =     tidIdent $ fnVar  f
         , ssFuncVars  = map tidIdent $ fnVars f
         , ssFuncBody  = ssTermOfExpr $ fnBody f
         , ssFuncEnv   = Map.empty
         }
ssClosure f env = SSFunc $ f { ssFuncEnv = env }

data SSFunc = Func { ssFuncIdent      :: Ident
                   , ssFuncVars       :: [Ident]
                   , ssFuncBody       :: SSTerm
                   , ssFuncEnv        :: ValueEnv
                   }
instance Show SSFunc where
  show f = "<func " ++ show (ssFuncIdent f) ++ " ~ " ++ show (ssFuncBody f) ++ ">"

tryLookupFunc :: MachineState -> Ident -> Maybe SSFunc
tryLookupFunc gs id = Map.lookup id (stFuncmap gs)

-- ||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

extendEnv :: ValueEnv -> [Ident] -> [SSValue] -> ValueEnv
extendEnv env names args =
  let ins (id, arg) map = Map.insert id arg map in
  List.foldr ins env (zip names args)

withExtendEnv :: MachineState -> [Ident] -> [SSValue] -> MachineState
withExtendEnv gs names args =
  withEnv gs (extendEnv (envOf gs) names args)

-- Create a new, un-activated closure given a function to begin execution with.
-- Returns a new machine state and a fresh location holding the new Coro value.
coroFromClosure :: MachineState -> SSFunc -> ((Location, MachineState), Coro)
coroFromClosure gs func =
  let coro = Coro { coroTerm = ssFuncBody func
                  , coroArgs = ssFuncVars func
                  , coroEnv  = ssFuncEnv func
                  , coroStat = CoroStatusDormant
                  , coroLoc  = nextLocation (hpBump (stHeap gs))
                  , coroPrev = Nothing
                  , coroStack = [(ssFuncEnv func, Prelude.id)]
                  } in
  ((extendHeap gs (SSCoro coro)), coro)

termOf gs = coroTerm (stCoro gs)
envOf  gs = coroEnv  (stCoro gs)

unit = (SSTmValue $ SSTuple [])

-- Looks up the given id as either a local variable or a proc definition.
getval :: MachineState -> Ident -> SSValue
getval gs id =
  let env = envOf gs in
  case Map.lookup id env of
    Just v -> v
    Nothing -> case tryLookupFunc gs id of
      Just f -> SSFunc f
      Nothing ->
               error $ "Unable to get value for " ++ show id
                      ++ "\n\tenv (unsorted) is " ++ show env

-- Update the current term to be the body of the given procedure, with
-- the environment set up to match the proc's formals to the given args.
callFunc gs func args =
  let names = ssFuncVars func in
  let extenv = extendEnv (ssFuncEnv func) names args in
  withTerm (withEnv gs extenv) (ssFuncBody func)

-- ||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

pushContext gs termWithHole = do
  let currStack = coroStack (stCoro gs)
  return $ modifyHeapWith gs (stCoroLoc gs)
             (\(SSCoro c) -> SSCoro $ c { coroStack = termWithHole:currStack })

popContext gs =
  let cont:restStack = coroStack (stCoro gs) in
  (cont, modifyHeapWith gs (stCoroLoc gs)
             (\(SSCoro c) -> SSCoro $ c { coroStack = restStack }))

-- ||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

stepExpr :: MachineState -> IExpr -> IO MachineState
stepExpr gs expr = do
  case expr of
    IVar i         -> do return $ withTerm gs (SSTmValue $ getval gs i)
    ITuple      vs -> do return $ withTerm gs (SSTmValue $ SSTuple      (map (getval gs) vs))
    IAppCtor id vs -> do return $ withTerm gs (SSTmValue $ SSCtorVal id (map (getval gs) vs))

    -- If b is a value, we extend the environment and prepare to evaluate e.
    -- But if b is not a value, we must begin stepping it. The straightforward
    -- thing to do would be
    --           gs' <- step (withExpr gs b)
    --           return $ withExpr gs' (ILLetVal x (exprOf gs' ) e)
    -- The recursive call to step neatly hides the object language
    -- call stack in the meta level call stack. Unfortunately, this doesn't
    -- properly save the environment of the let; the environment from stepping
    -- b will leak back to the letval, wrecking havoc with recursive functions.
    -- To implement lexical scoping instead of dynamic scoping, we explicitly
    -- save the environment and a context expression to be restored when b
    -- eventually steps to a value.
    ILetVal x b e ->
      case b of
        SSTmValue v -> do return $ withTerm (withExtendEnv gs [x] [v]) e
        SSTmExpr _  -> pushContext (withTerm gs b)
                                     (envOf gs, \t -> SSTmExpr $ ILetVal x t e)

    IAlloc i     -> do let (loc, gs') = extendHeap gs (getval gs i)
                       return $ withTerm gs' (SSTmValue $ SSLocation loc)
    IDeref i     -> do case getval gs i of
                         SSLocation z -> return $ withTerm gs  (SSTmValue $ lookupHeap gs z)
                         other -> error $ "cannot deref non-location value " ++ show other
    IStore iv ir -> do let (SSLocation z) = getval gs ir
                       let gs' = modifyHeapWith gs z (\_ -> getval gs iv)
                       return $ withTerm gs' unit

    ILetFuns ids fns e ->
      let extenv = extendEnv (envOf gs) ids (map clo fns)
          clo fn = ssClosure (ssFunc fn) extenv
      in
      return $ withTerm (withEnv gs extenv) e

    ICase _a {-_dt-} [] -> error $ "Smallstep.hs: Pattern match failure when evaluating case expr!"
    ICase  a {- dt-} ((p, e):bs) ->
       -- First, interpret the pattern list directly
       -- (using recursive calls to discard unmatched branches).
       case matchPattern p (getval gs a) of
         Nothing -> return $ withTerm gs (SSTmExpr $ ICase a {-dt-} bs)
         Just varsvals ->
           -- Then check that interpreting the decision tree
           -- gives identical results to direct pattern interpretation.
           --case evalDecisionTree dt (getval gs a) of
           --   Just vv | vv == varsvals ->
                    let (vars, vals) = unzip varsvals in
                    return $ withTerm (withExtendEnv gs vars vals) e
           -- elsewise ->
           --       error $ "Direct pattern matching disagreed with decision tree!"
           --           ++ "\n" ++ show elsewise ++ " vs \n" ++ show varsvals
    ICallPrim prim vs ->
        let args = map (getval gs) vs in
        case prim of
          ILNamedPrim (TypedId _ id) ->
                              evalNamedPrimitive (identPrefix id) gs args
          ILPrimOp op size -> return $ withTerm gs (SSTmValue $
                                        evalPrimitiveOp size op args)
          ILCoroPrim prim _t1 _t2 -> evalCoroPrimitive prim gs args

    ICall b vs ->
        let args = map (getval gs) vs in
        case tryLookupFunc gs b of
           -- Call of top-level function
           Just func -> return (callFunc gs func args)
           Nothing -> --  call of locally bound function
             case getval gs b of
               SSFunc func -> return (callFunc gs func args)
               v -> error $ "Cannot call non-closure value " ++ display v

    IIf v b c ->
        case getval gs v of
           (SSBool True ) -> return $ withTerm gs b
           (SSBool False) -> return $ withTerm gs c
           _ -> error $ "if cond was not a boolean: " ++ show v
                     ++ " => " ++ display (getval gs v)

    IUntil c b ->
      let v = (Ident "!untilval" 0) in
      return $ withTerm gs (SSTmExpr $
        ILetVal v c (SSTmExpr $ IIf v unit
                    (SSTmExpr $ ILetVal (Ident "_" 0) b (SSTmExpr $ IUntil c b))))

    IArrayRead base idxvar ->
        let (SSInt i) = getval gs idxvar in
        let n = (fromInteger i) :: Int in
        case getval gs base of
          SSArray arr  ->  let (SSLocation z) = arraySlotLocation arr n in
                           return $ withTerm gs  (SSTmValue $ lookupHeap gs z)
          _ -> error "Expected base of array read to be array value"

    IArrayPoke iv base idxvar ->
        let (SSInt i) = getval gs idxvar in
        let n = (fromInteger i) :: Int in
        case getval gs base of
          SSArray arr  -> let (SSLocation z) = arraySlotLocation arr n in
                          let gs' = modifyHeapWith gs z (\_ -> getval gs iv) in
                          return $ withTerm gs' unit
          other -> error $ "Expected base of array write to be array value; had " ++ show other

    IAllocArray sizeid -> do
        let (SSInt i) = getval gs sizeid
        -- The array cells are initially filled with constant zeros,
        -- regardless of what type we will eventually store.
        (inits, gs2) <- mapFoldM [0.. i - 1] gs (\n -> \gs1 ->
                                let (loc, gs) = extendHeap gs1 (SSInt 0) in
                                return ([(fromInteger n, loc)], gs)
                       )
        return $ withTerm gs2 (SSTmValue $ SSArray $
                        array (0, fromInteger $ i - 1) inits)

    ITyApp v _argty -> return $ withTerm gs (SSTmValue $ getval gs v)

-- ||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

arraySlotLocation arr n = SSLocation (arr ! n)

-- ||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

matchPattern :: Pattern -> SSValue -> Maybe [(Ident, SSValue)]
matchPattern p v =
  let trivialMatchSuccess = Just [] in
  let matchFailure        = Nothing in
  let matchIf cond = if cond then trivialMatchSuccess
                             else matchFailure in
  case (v, p) of
    (_, P_Wildcard _   ) -> trivialMatchSuccess
    (_, P_Variable _ id) -> Just [(id, v)]

    (SSInt i1, P_Int _ i2)   -> matchIf $ i1 == litIntValue i2
    (_       , P_Int _ _ )   -> matchFailure

    (SSBool b1, P_Bool _ b2) -> matchIf $ b1 == b2
    (_        , P_Bool _ _ ) -> matchFailure

    (SSCtorVal vid vals, P_Ctor _ pats cid) -> do _ <- matchIf $ vid == cid
                                                  matchPatterns pats vals
    (_                 , P_Ctor _ _ _)      -> matchFailure

    (SSTuple vals, P_Tuple _ pats) -> matchPatterns pats vals
    (_, P_Tuple _ _) -> matchFailure


matchPatterns :: [Pattern] -> [SSValue] -> Maybe [(Ident, SSValue)]
matchPatterns pats vals = do
  matchLists <- mapM (\(p, v) -> matchPattern p v) (zip pats vals)
  return $ concat matchLists

-- ||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

liftInt2 :: (Integral a) => (a -> a -> b) ->
          Integer -> Integer -> b
liftInt2 f i1 i2 = f (fromInteger i1) (fromInteger i2)

liftInt :: (Integral a) => (a -> b) -> Integer -> b
liftInt f i1 =     f (fromInteger i1)

modifyInt32sWith :: (Int32 -> Int32 -> Int32) -> Integer -> Integer -> Integer
modifyInt32sWith f i1 i2 = fromIntegral (liftInt2 f i1 i2)

modifyInt32With :: (Int32 -> Int32) -> Integer -> Integer
modifyInt32With f i1 =     fromIntegral (liftInt f i1)

ashr32   a b = shiftR a (fromIntegral b)
shl32    a b = shiftL a (fromIntegral b)

tryGetInt32PrimOp2Int32 :: String -> Maybe (Integer -> Integer -> Integer)
tryGetInt32PrimOp2Int32 name =
  case name of
    "*"       -> Just (modifyInt32sWith (*))
    "+"       -> Just (modifyInt32sWith (+))
    "-"       -> Just (modifyInt32sWith (-))
    "/"       -> Just (modifyInt32sWith div)
    "bitashr" -> Just (modifyInt32sWith ashr32)
    "bitshl"  -> Just (modifyInt32sWith shl32)
    "bitxor"  -> Just (modifyInt32sWith xor)
    "bitor"   -> Just (modifyInt32sWith (.|.))
    "bitand"  -> Just (modifyInt32sWith (.&.))
    _ -> Nothing

tryGetInt32PrimOp2Bool :: String -> Maybe (Int32 -> Int32 -> Bool)
tryGetInt32PrimOp2Bool name =
  case name of
    "<"        -> Just ((<))
    "<="       -> Just ((<=))
    "=="       -> Just ((==))
    "!="       -> Just ((/=))
    ">="       -> Just ((>=))
    ">"        -> Just ((>))
    _ -> Nothing

--------------------------------------------------------------------

evalPrimitiveOp :: Int -> String -> [SSValue] -> SSValue
evalPrimitiveOp 32 opName [SSInt i1, SSInt i2] =
  case tryGetInt32PrimOp2Int32 opName of
    (Just fn)       -> SSInt (fn i1 i2)
    _ -> case tryGetInt32PrimOp2Bool opName of
          (Just fn) -> SSBool (liftInt2 fn i1 i2)
          _ -> error $ "Unknown primitive operation " ++ opName

evalPrimitiveOp 32 "negate" [SSInt i] = SSInt (negate i)

evalPrimitiveOp  1 "bitnot" [SSBool b] = SSBool (not b)

evalPrimitiveOp 32 "bitnot" [SSInt i] =
        SSInt ((modifyInt32With complement) i)

evalPrimitiveOp size opName args =
  error $ "Smallstep.evalPrimitiveOp " ++ show size ++ " " ++ opName ++ " " ++ show args

--------------------------------------------------------------------

evalNamedPrimitive :: String -> MachineState -> [SSValue] -> IO MachineState

evalNamedPrimitive primName gs [val] | isPrintFunction primName =
      do printString gs (display val)
         return $ withTerm gs unit

evalNamedPrimitive primName gs [val] | isExpectFunction primName =
      do expectString gs (display val)
         return $ withTerm gs unit

evalNamedPrimitive "expect_i32b" gs [SSInt i] =
      do expectString gs (showBits32 i)
         return $ withTerm gs unit

evalNamedPrimitive "print_i32b" gs [SSInt i] =
      do printString gs (showBits32 i)
         return $ withTerm gs unit

evalNamedPrimitive "force_gc_for_debugging_purposes" gs _args =
         return $ withTerm gs unit

evalNamedPrimitive "opaquely_i32" gs [val] =
         return $ withTerm gs (SSTmValue $ val)

evalNamedPrimitive prim _gs _args = error $ "evalNamedPrimitive " ++ show prim
                                         ++ " not yet defined"

-- ||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

canSwitchToCoro c =
  case coroStat c of
    CoroStatusInvalid   -> False
    CoroStatusSuspended -> True
    CoroStatusDormant   -> True
    CoroStatusRunning   -> False
    CoroStatusDead      -> False

evalCoroPrimitive CoroInvoke gs [(SSLocation targetloc),arg] =
   let (SSCoro ncoro) = lookupHeap gs targetloc in
   let ccoro = if canSwitchToCoro ncoro
                 then stCoro gs
                 else error "Unable to invoke coroutine!" in
   let hadRun = CoroStatusDormant /= coroStat ncoro in
   let newcoro2 = ncoro { coroPrev = (Just $ coroLoc ccoro)
                        , coroStat = CoroStatusRunning } in
   if hadRun
     then
        let newcoro = newcoro2 { coroTerm = SSTmValue arg } in
        return $ gs {
            stHeap = modifyHeap2 gs (coroLoc ccoro) (SSCoro $ ccoro { coroStat = CoroStatusSuspended })
                                    (coroLoc ncoro) (SSCoro $ newcoro)
          , stCoroLoc = coroLoc ncoro
        }
     else
        let newcoro = newcoro2 in
        let gs2 = gs {
            stHeap = modifyHeap2 gs (coroLoc ccoro) (SSCoro $ ccoro { coroStat = CoroStatusSuspended })
                                    (coroLoc ncoro) (SSCoro $ newcoro)
          , stCoroLoc = coroLoc ncoro
        } in
        return $ withExtendEnv gs2 (coroArgs newcoro) [arg]

evalCoroPrimitive CoroInvoke _gs bad =
         error $ "Wrong arguments to coro_invoke: "++ show bad


-- "Rule 4 describes the action of creating a coroutine.
--  It creates a new label to represent the coroutine and extends the
--  store with a mapping from this label to the coroutine main function."

evalCoroPrimitive CoroCreate gs [SSFunc f] =
  let ((loc, gs2), _coro) = coroFromClosure gs f in
  return $ withTerm gs2 (SSTmValue $ SSLocation loc)

evalCoroPrimitive CoroCreate _gs args =
        error $ "Wrong arguments to coro_create: " ++ show args


-- The current coro is returned to the heap, marked suspended, with no previous coro.
-- The previous coro becomes the new coro, with status running.
evalCoroPrimitive CoroYield gs [arg] =
  let ccoro = stCoro gs in
  case coroPrev ccoro of
    Nothing -> error $ "Cannot yield from initial coroutine!\n" ++ show ccoro
    Just prevloc ->
      let (SSCoro prevcoro) = assert (prevloc /= coroLoc ccoro) $
                               lookupHeap gs prevloc in
      let newpcoro = if canSwitchToCoro prevcoro then
                      prevcoro { coroStat = CoroStatusRunning
                               , coroTerm = SSTmValue arg }
                      else error "Unable to yield to saved coro!" in
      let gs2 = gs {
          stHeap = modifyHeap2 gs prevloc (SSCoro newpcoro)
                          (coroLoc ccoro) (SSCoro $ ccoro { coroPrev = Nothing
                                                          , coroStat = CoroStatusSuspended })
        , stCoroLoc = prevloc
      } in
      return $ gs2
evalCoroPrimitive CoroYield _gs _ = error $ "Wrong arguments to coro_yield"

--------------------------------------------------------------------

printString  gs s = do
  runOutput (outCSLn Blue s)
  appendFile (errFile gs) (s ++ "\n")

expectString gs s = do
  runOutput (outCSLn Green s)
  appendFile (outFile gs) (s ++ "\n")

--------------------------------------------------------------------

showBits32 n =
  let bits = map (testBit n) [0 .. (32 - 1)] in
  let s = map (\b -> if b then '1' else '0') bits in
  (reverse s) ++ "_2"

isPrintFunction name =
  case name of
    "print_i64"  -> True
    "print_i32"  -> True
    "print_i1"   -> True
    _ -> False

isExpectFunction name =
  case name of
    "expect_i64" -> True
    "expect_i32" -> True
    "expect_i1"  -> True
    _ -> False

display :: SSValue -> String
display (SSBool True )  = "true"
display (SSBool False)  = "false"
display (SSInt i     )  = show i
display (SSArray a   )  = show a
display (SSTuple vals)  = "(" ++ joinWith ", " (map display vals) ++ ")"
display (SSLocation z)  = "<location " ++ show z ++ ">"
display (SSCtorVal id vals) = "(" ++ show id ++ joinWith " " (map display vals) ++ ")"
display (SSFunc f) = "<closure " ++ (show $ ssFuncIdent f) ++ ">"
display (SSCoro    _  ) = "<coro>"

-- Declare some instances that are only needed in this module.
instance Eq SSFunc
  where f1 == f2 = ssFuncIdent f1 == ssFuncIdent f2

instance Eq Coro
  where c1 == c2 = (coroLoc c1) == (coroLoc c2)

instance Show (SSTerm -> SSTerm) where show _f = "<coro cont>"
