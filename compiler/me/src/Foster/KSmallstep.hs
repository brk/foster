{-# LANGUAGE BangPatterns #-}
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
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Data.Int
import Data.Word
import Data.DoubleWord
import Data.Bits
import Data.Char(toUpper)
import Data.IORef(IORef, readIORef, newIORef)
import Data.Array
import Numeric
import qualified Data.ByteString as BS
import Text.Printf(printf)
import Text.PrettyPrint.ANSI.Leijen
import Criterion.Measurement(getTime)

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

-- |||||||||||||||||||||||  Entry Point  ||||||||||||||||||||||||{{{
errFile gs = (stTmpDir $ stConfig gs) ++ "/istderr.txt"
outFile gs = (stTmpDir $ stConfig gs) ++ "/istdout.txt"

-- To interpret a program, we construct a coroutine for main
-- (no arguments need be passed yet) and step until the program finishes.
interpretKNormalMod kmod tmpDir cmdLineArgs = do
  let loc  = 0 :: Int
  let mainCoro = Coro { coroTerm = ssTermOfExpr $ moduleILbody kmod
                      , coroArgs = []
                      , coroEnv  = env
                      , coroStat = CoroStatusRunning
                      , coroLoc  = loc
                      , coroPrev = Nothing
                      , coroStack = [(env, Prelude.id)]
                      } where env = Map.empty
  let emptyHeap = Heap (nextLocation loc)
                       (IntMap.singleton loc (SSCoro mainCoro))
  let globalState = MachineState emptyHeap $
                    MachineStateConfig loc tmpDir ("ksmallstep":cmdLineArgs)

  _ <- writeFile (outFile globalState) ""
  _ <- writeFile (errFile globalState) ""

  stepsTaken <- newIORef 0
  val <- interpret stepsTaken globalState
  numSteps <- readIORef stepsTaken
  putStrLn ("Interpreter finished in " ++ show numSteps ++ " steps.")
  return val
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

-- ||||||||||||||||||||||||||  Running  |||||||||||||||||||||||||{{{
-- Step a machine state until there is nothing left to step.
interpret :: IORef Int -> MachineState -> IO MachineState
interpret stepsTaken gs =
  case (coroStack $ stCoro gs) of
    [] -> do return gs
    _  -> do modIORef' stepsTaken (+1)
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
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

-- |||||||||||||||||||||||  Machine State  ||||||||||||||||||||||{{{
-- A machine state consists of a (static) mapping of proc ids to
-- proc definitions, a heap mapping locations (ints) to values,
-- and the location of the current coroutine. Note that the machine
-- state does not include the coroutine value itself!

data MachineState = MachineState {
           stHeap    :: !Heap
        ,  stConfig  :: MachineStateConfig
}

-- Split out the invariant stuff to make updating the heap faster.
data MachineStateConfig = MachineStateConfig {
           stCoroLoc :: Location
        ,  stTmpDir  :: String
        ,  stCmdArgs :: [String]
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
  , coroEnv  :: !ValueEnv
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

-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||
-- |||||||||||||||||||||||||  Locations  ||||||||||||||||||||||||{{{

type Location = Int
nextLocation x = x + 1
data Heap = Heap {
          hpBump :: !Location
        , hpMap  :: !(IntMap SSValue)
}

-- Fetch the current coroutine from the heap.
stCoro gs = let (SSCoro c) = lookupHeap gs (stCoroLoc $ stConfig gs) in c

lookupHeap :: MachineState -> Location -> SSValue
lookupHeap gs loc = (IntMap.!) (hpMap (stHeap gs)) loc

extendHeap :: MachineState -> SSValue -> (Location, MachineState)
extendHeap gs val =
  let heap = stHeap gs in
  let loc = nextLocation (hpBump heap) in
  let hmp = IntMap.insert loc val (hpMap heap) in
  (loc, gs { stHeap = Heap { hpBump = loc, hpMap = hmp } })

-- Simple helper to store two values in two locations.
modifyHeap2 gs l1 v1 l2 v2 =
  let heap = stHeap gs in
  heap { hpMap = IntMap.insert l2 v2 (IntMap.insert l1 v1 (hpMap heap)) }

-- Updates the value at the given location according to the provided function.
modifyHeapWith :: MachineState -> Location -> (SSValue -> SSValue)
               -> MachineState
modifyHeapWith gs loc fn =
  let oldheap = stHeap gs in
  let val  = lookupHeap gs loc in
  let heap = oldheap { hpMap = IntMap.insert loc (fn val) (hpMap oldheap) } in
  gs { stHeap = heap }

modifyCoro gs f =
  modifyHeapWith gs (stCoroLoc $ stConfig gs) (\ss ->
                    case ss of SSCoro c -> SSCoro $ f c
                               _        -> error "Expected coro in coro slot!")

-- Pervasively used helper functions to update the term/env of the current coro.
withTerm gs e = modifyCoro gs (\c -> c { coroTerm = e })
withEnv  gs e = modifyCoro gs (\c -> c { coroEnv  = e })

-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

-- |||||||||||||||||||||||  Terms and Values  |||||||||||||||||||{{{
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
        | ILetFuns     [Ident] [Fn () KNExpr TypeIL] SSTerm
        | ILetVal       Ident   SSTerm  SSTerm
        | ILetRec      [Ident] [SSTerm] SSTerm
        | IArrayRead    Ident   Ident
        | IArrayPoke    Ident   Ident Ident
        | IAllocArray   Ident
        | IIf           Ident   SSTerm     SSTerm
        | ICall         Ident  [Ident]
        | ICallPrim     ILPrim [Ident]
        | ICase         Ident  {-(DecisionTree KNExpr)-} [CaseArm PatternRepr SSTerm TypeIL] [PatternRepr TypeIL]
        | ICaseGuard    SSTerm SSTerm ShowableMachineState
                        Ident  [CaseArm PatternRepr SSTerm TypeIL] [PatternRepr TypeIL]
        | ITyApp        Ident  [TypeIL]
        | IAppCtor      CtorId [Ident]
        deriving (Show)

data ShowableMachineState = SMS MachineState

-- Values in the (intermediate) language are mostly standard.
-- Coro values are the most interesting, as defined above.
-- A closure value has a proc ident, env+captures var names,
-- and captured values.
data SSValue = SSBool      Bool
             | SSInt       Integer
             | SSFloat     Double
             | SSArray     (Array Int Location)
             | SSByteString BS.ByteString -- strictly redundant, but convenient.
             | SSTuple     [SSValue]
             | SSCtorVal   CtorId [SSValue]
             | SSLocation  Location
             | SSFunc      SSFunc
             | SSCoro      Coro
             deriving (Eq, Show)
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

-- |||||||||||||||||||||| KNExpr -> SSTerm ||||||||||||||||||||||{{{
-- There is a trivial translation from KNExpr to SSTerm...
ssTermOfExpr :: KNExpr -> SSTerm
ssTermOfExpr expr =
  let tr   = ssTermOfExpr in
  let idOf = tidIdent     in
  case expr of
    KNLiteral _ (LitBool  b) -> SSTmValue $ SSBool b
    KNLiteral _ (LitInt   i) -> SSTmValue $ SSInt (litIntValue i)
    KNLiteral _ (LitFloat f) -> SSTmValue $ SSFloat (litFloatValue f)
    KNLiteral _ (LitText  s) -> SSTmValue $ textFragmentOf s
    KNVar        v         -> SSTmExpr  $ IVar (idOf v)
    KNTuple   _t vs _      -> SSTmExpr  $ ITuple (map idOf vs)
    KNLetFuns ids funs e   -> SSTmExpr  $ ILetFuns   ids funs           (tr e)
    KNLetVal x b e         -> SSTmExpr  $ ILetVal      x (tr b)         (tr e)
    KNLetRec ids exprs e   -> SSTmExpr  $ ILetRec    ids (map tr exprs) (tr e)
    KNCall     _t b vs     -> SSTmExpr  $ ICall (idOf b) (map idOf vs)
    KNCallPrim _t b vs     -> SSTmExpr  $ ICallPrim b (map idOf vs)
    KNIf       _t  v b c   -> SSTmExpr  $ IIf      (idOf v) (tr b) (tr c)
    KNArrayRead _t (ArrayIndex a b _ _)
                           -> SSTmExpr  $ IArrayRead (idOf a) (idOf b)
    KNArrayPoke _t (ArrayIndex b i _ _) v
                           -> SSTmExpr  $ IArrayPoke (idOf v) (idOf b) (idOf i)
    KNAllocArray _ety n    -> SSTmExpr  $ IAllocArray (idOf n)
    KNAlloc    _t a _rgn   -> SSTmExpr  $ IAlloc (idOf a)
    KNDeref    _t a        -> SSTmExpr  $ IDeref (idOf a)
    KNStore    _t a b      -> SSTmExpr  $ IStore (idOf a) (idOf b)
    KNTyApp    _t v argtys -> SSTmExpr  $ ITyApp (idOf v) argtys
    KNCase _t a bs {-dt-}  -> SSTmExpr  $ ICase (idOf a) {-dt-} [CaseArm p (tr e) (fmap tr g) b r
                                                                |CaseArm p e g b r <- bs] []
    KNAppCtor     _t cr vs -> SSTmExpr  $ IAppCtor (fst cr) (map idOf vs)
    KNKillProcess _t msg   -> SSTmExpr  $ error $ "prim kill-process: " ++ T.unpack msg

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
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

-- |||||||||||||||||||| Machine State Helpers |||||||||||||||||||{{{
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

extendEnv :: ValueEnv -> [Ident] -> [SSValue] -> ValueEnv
extendEnv env names args =
  let ins !map !(id, !arg) = Map.insert id arg map in
  List.foldl' ins env (zip names args)

withExtendEnv :: MachineState -> [Ident] -> [SSValue] -> MachineState
withExtendEnv gs names args =
  withEnv gs (extendEnv (envOf gs) names args)

termOf gs = coroTerm (stCoro gs)
envOf  gs = coroEnv  (stCoro gs)

unit = (SSTmValue $ SSTuple [])

-- Looks up the given id as either a local variable or a proc definition.
getval :: MachineState -> Ident -> SSValue
getval gs id =
  case Map.lookup id (envOf gs) of
    Just v -> v
    Nothing -> error $ "Unable to get value for " ++ show id
                      ++ "\n\tenv (unsorted) is " ++ show (envOf gs)

-- Update the current term to be the body of the given procedure, with
-- the environment set up to match the proc's formals to the given args.
callFunc :: MachineState -> SSFunc -> [SSValue] ->
           (MachineState -> SSTerm -> r) -> r
callFunc gs func args kont =
                      kont (withEnv gs extenv) (ssFuncBody func)
  where extenv = extendEnv (ssFuncEnv func) names args
        names  = ssFuncVars func

evalIf gs v b c kont =
  case getval gs v of
    SSBool True  -> kont gs b
    SSBool False -> kont gs c
    _ -> error $ "Smallstep.hs: if's conditional was not a boolean: "
                  ++ show v ++ " => " ++ display (getval gs v)

-- ||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

pushContext gs termWithHole = do
  let currStack = coroStack (stCoro gs)
  return $ modifyCoro gs (\c -> c { coroStack = termWithHole:currStack })

popContext gs =
  let cont:restStack = coroStack (stCoro gs) in
  (cont, modifyCoro gs (\c -> c { coroStack = restStack }))

-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

-- |||||||||| (big-step) Evaluating An Expression, Purely |||||||{{{
-- Unlike stepExpr, evalExpr won't (indeed, cannot) allocate new
-- heap locations or otherwise affect the abstract machine state.
-- Note that some concrete allocations (e.g. for tuples or closures)
-- do not correspond to heap allocations on this abstract machine.
evalTerm :: MachineState -> SSTerm -> SSValue
evalTerm _ (SSTmValue v) = v
evalTerm gs (SSTmExpr expr) = evalExpr gs expr

evalExpr :: MachineState -> IExpr -> SSValue
evalExpr gs expr =
  case expr of
    IVar        id -> getval gs id
    ITyApp v _argty-> getval gs v
    ITuple      vs -> SSTuple      (map (getval gs) vs)
    IAppCtor id vs -> SSCtorVal id (map (getval gs) vs)
    IDeref      id -> case getval gs id of
                         SSLocation z -> lookupHeap gs z
                         other -> error $ "cannot deref non-location value "
                                                             ++ show other
    ILetRec  ids terms e -> evalRec gs ids terms e evalTerm evalTerm
    ILetFuns ids fns   e -> evalRec gs ids fns   e evalFunc evalTerm

    -- We syntatically restrict other expressions from being recursively
    -- bound, so anything that makes it past typechecking shouldn't fail here.
    other -> error $ "Smallstep.hs: evalExpr cannot handle " ++ show other

type ExtMachineState = MachineState

-- This helper is called from both evalExpr and stepExpr; the only difference
-- between the two cases is whether `kont` is evalTerm or withTerm.
evalRec :: MachineState -> [Ident] -> [term] -> SSTerm
        -> (ExtMachineState -> term   -> SSValue)
        -> (ExtMachineState -> SSTerm -> r) -> r
evalRec gs ids terms e eval kont = kont gs' e
 where extenv = extendEnv (envOf gs) ids values
       gs'    = withEnv gs extenv
       values = map (eval gs') terms

evalFunc gs' fn = ssClosure (ssFunc fn) (envOf gs')

-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

-- |||||||||||||||||||||| Stepping An Expression ||||||||||||||||{{{
stepExpr :: MachineState -> IExpr -> IO MachineState
stepExpr gs expr = do
  case expr of
    -- These terms step to a value with no side effects:
    IVar     {} -> do return $ withTerm gs (SSTmValue $ evalExpr gs expr)
    ITuple   {} -> do return $ withTerm gs (SSTmValue $ evalExpr gs expr)
    IAppCtor {} -> do return $ withTerm gs (SSTmValue $ evalExpr gs expr)
    IDeref   {} -> do return $ withTerm gs (SSTmValue $ evalExpr gs expr)
    ITyApp   {} -> do return $ withTerm gs (SSTmValue $ evalExpr gs expr)

    ILetRec  ids terms e -> return $ evalRec gs ids terms e evalTerm withTerm
    ILetFuns ids fns   e -> return $ evalRec gs ids fns   e evalFunc withTerm

    IIf v b c            -> return $ evalIf gs v b c                 withTerm

    -- These cases involve modifying the machine state in ways beyond simple
    -- environment extensions or heap lookups:

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

    IStore iv ir -> do let (SSLocation z) = getval gs ir
                       let gs' = modifyHeapWith gs z (\_ -> getval gs iv)
                       return $ withTerm gs' unit

    ICase  a {-_dt-} [] rejectedPatterns ->
        error $ "Smallstep.hs: Pattern match failure when evaluating case expr!"
             ++ "\n\tFailing value: " ++ (show $ getval gs a)
             ++ "\n\tRejected patterns: " ++ (show (list $ map pretty rejectedPatterns))
    ICase  a {- dt-} ((CaseArm p e g _ _):bs) rejectedPatterns ->
       -- First, interpret the pattern list directly
       -- (using recursive calls to discard unmatched branches).
       case matchPattern p (getval gs a) of
         Nothing -> return $ withTerm gs (SSTmExpr $ ICase a {-dt-} bs (p:rejectedPatterns))
         Just varsvals ->
           -- Then check that interpreting the decision tree
           -- gives identical results to direct pattern interpretation.
           --case evalDecisionTree dt (getval gs a) of
           --   Just vv | vv == varsvals ->
                    let (vars, vals) = unzip varsvals in
                    let gs' = withExtendEnv gs vars vals in
                    -- We've successfully matched a pattern and generated
                    -- some bindings, but if there's a guard, we need to
                    -- evaluate the guard before determining whether the
                    -- overall case arm actually matched.
                    return $ case g of
                               Nothing -> withTerm gs' e
                               Just ge -> withTerm gs' (SSTmExpr $ ICaseGuard ge e (SMS gs) a bs (p:rejectedPatterns))
           -- elsewise ->
           --       error $ "Direct pattern matching disagreed with decision tree!"
           --           ++ "\n" ++ show elsewise ++ " vs \n" ++ show varsvals

    ICaseGuard ge e (SMS oldgs) a bs rejectedPatterns ->
      -- This is a bit of a hack to properly evaluate guards on patterns,
      -- since guards must evaluate in an extended environment, but if the guard fails,
      -- the environment should be "rolled back" and pattern matching should continue
      -- in the un-extended environment.
      case ge of
        SSTmValue (SSBool True)  -> return $ withTerm    gs e
        SSTmValue (SSBool False) -> return $ withTerm oldgs (SSTmExpr $ ICase a bs rejectedPatterns)
        SSTmValue _ -> error "case guard evaluated to non-boolean value"
        SSTmExpr _  -> pushContext (withTerm gs ge)
                                     (envOf gs, \t -> SSTmExpr $ ICaseGuard t e (SMS oldgs) a bs rejectedPatterns)

    ICallPrim prim vs ->
        let args = map (getval gs) vs in
        case prim of
          NamedPrim (TypedId _ id) ->
                          evalNamedPrimitive (T.unpack $ identPrefix id) gs args
          PrimOp op ty -> return $
              withTerm gs (SSTmValue $ evalPrimitiveOp ty op args)
          PrimIntTrunc from to -> return $
              withTerm gs (SSTmValue $ evalPrimitiveIntTrunc from to args)
          CoroPrim prim _t1 _t2 -> evalCoroPrimitive prim gs args
          PrimArrayLiteral -> let (base:vals) = args
                                  go :: MachineState -> Int -> [SSValue] -> IO MachineState
                                  go gs _ [] = return $ withTerm gs (SSTmValue base)
                                  go gs n (val:vals) = do
                                    gs' <- arrayPoke gs base n val
                                    go gs' (n + 1) vals
                              in
                              go gs 0 vals

    ICall b vs ->
        let args = map (getval gs) vs in
        case getval gs b of
           SSFunc func -> return (callFunc gs func args withTerm)
           v -> error $ "Cannot call non-function value " ++ display v

    IArrayRead base idxvar ->
        let (SSInt i) = getval gs idxvar in
        let n = (fromInteger i) :: Int in
        case getval gs base of
          a@(SSArray _)      ->
            return $ withTerm gs (SSTmValue $ prim_arrayRead gs n a)
          a@(SSByteString _) -> return $ withTerm gs (SSTmValue $ prim_arrayRead gs n a)
          other -> error $ "KSmallstep: Expected base of array read "
                        ++ "(" ++ show base ++ "["++ show idxvar++"])"
                        ++ " to be array value; had " ++ show other

    IArrayPoke iv base idxvar ->
        let (SSInt i) = getval gs idxvar in
        let n = (fromInteger i) :: Int in
        arrayPoke gs (getval gs base) n (getval gs iv)

    IAllocArray sizeid -> do
        let (SSInt i) = getval gs sizeid
        -- The array cells are initially filled with constant zeros,
        -- regardless of what type we will eventually store.
        arrayOf gs [SSInt n | n <- [0 .. i - 1]]
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

-- |||||||||||||||||||||||| Pattern Matching ||||||||||||||||||||{{{
matchPattern :: PatternRepr TypeIL -> SSValue -> Maybe [(Ident, SSValue)]
matchPattern p v =
  case (v, p) of
    (_, PR_Atom (P_Wildcard _ _  )) -> trivialMatchSuccess
    (_, PR_Atom (P_Variable _ tid)) -> Just [(tidIdent tid, v)]

    (SSInt i1, PR_Atom (P_Int _ _ i2))   -> matchIf $ i1 == litIntValue i2
    (_       , PR_Atom (P_Int _ _ _ ))   -> matchFailure

    (SSBool b1, PR_Atom (P_Bool _ _ b2)) -> matchIf $ b1 == b2
    (_        , PR_Atom (P_Bool _ _ _ )) -> matchFailure

    (SSCtorVal vid vals, PR_Ctor _ _ pats (LLCtorInfo cid _ _)) -> do
                                            _ <- matchIf $ vid == cid
                                            matchPatterns pats vals
    (_                 , PR_Ctor _ _ _ _) -> matchFailure

    (SSTuple vals, PR_Tuple _ _ pats) -> matchPatterns pats vals
    (_, PR_Tuple _ _ _) -> matchFailure
 where
   trivialMatchSuccess = Just []
   matchFailure        = Nothing
   matchIf cond = if cond then trivialMatchSuccess
                          else matchFailure

matchPatterns :: [PatternRepr TypeIL] -> [SSValue] -> Maybe [(Ident, SSValue)]
matchPatterns pats vals = do
  matchLists <- mapM (\(p, v) -> matchPattern p v) (zip pats vals)
  return $ concat matchLists
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

-- |||||||||||||||||||||| Primitive Operators ||||||||||||||||||{{{
kVirtualWordSize = 64
type IntVW0 = Int64
type IntVW1 = Int128

arraySlotLocation arr n = SSLocation (arr ! n)

prim_arrayLength :: SSValue -> Int
prim_arrayLength (SSArray a) = let (b,e) = bounds a in e - b
prim_arrayLength (SSByteString bs) = BS.length bs
prim_arrayLength _ = error "prim_arrayLength got non-array value!"

prim_arrayRead :: MachineState -> Int -> SSValue -> SSValue
prim_arrayRead gs n (SSArray arr) =
        let (SSLocation z) = arraySlotLocation arr n in lookupHeap gs z
prim_arrayRead _  n (SSByteString bs) = SSInt . fromIntegral $ BS.index bs n
prim_arrayRead _  _ _ = error "prim_arrayRead got non-array value!"

prim_arrayPoke :: MachineState -> Int -> Array Int Location -> SSValue -> IO MachineState
prim_arrayPoke gs n arr val = do
  let (SSLocation z) = arraySlotLocation arr n
  let gs' = modifyHeapWith gs z (\_ -> val)
  return $ withTerm gs' unit

arrayPoke gs base n val =
    case base of
      SSArray arr  -> prim_arrayPoke gs n arr val
      other -> error $ "Expected base of array write to be array value; had " ++ show other

liftInt2 :: (Integral a) => (a -> a -> b) -> Integer -> Integer -> b
liftInt2 f i1 i2 = f (fromInteger i1) (fromInteger i2)

liftInt  :: (Integral a) => (a -> b)      -> Integer -> b
liftInt f i1 =     f (fromInteger i1)

modifyIntWith :: (Integral a) => Integer -> (a -> a) -> Integer
modifyIntWith i1 f = fromIntegral (liftInt f i1)

modifyIntsWith :: (Integral a) => Integer -> Integer -> (a -> a -> a) -> Integer
modifyIntsWith i1 i2 f = fromIntegral (liftInt2 f i1 i2)

lowShiftBits k b = (k - 1) .&. fromIntegral b

ashr k a b = shiftR a (lowShiftBits k b)
lshr k a b = shiftR a (lowShiftBits k b)
shl  k a b = shiftL a (lowShiftBits k b)

tryGetFixnumPrimOp :: (Bits a, Integral a) => Int -> String -> Maybe (a -> a -> a)
tryGetFixnumPrimOp k name =
  case name of
    "*"       -> Just (*)
    "+"       -> Just (+)
    "-"       -> Just (-)
    "sdiv"    -> Just div
    "udiv"    -> Just div
    "srem"    -> Just rem
    "urem"    -> Just rem
    "bitxor"  -> Just xor
    "bitor"   -> Just (.|.)
    "bitand"  -> Just (.&.)
    "bitashr" -> Just (ashr k)
    "bitlshr" -> Just (lshr k)
    "bitshl"  -> Just (shl  k)
    _ -> Nothing

tryGetPrimCmp :: (Ord a) => String -> (Maybe (a -> a -> Bool))
tryGetPrimCmp name =
  -- Strip off any identifying prefix.
  let clean_name = case name of
                        'f':n -> n
                        n     -> n
                   in
  case clean_name of
    "=="       -> Just ((==))
    "!="       -> Just ((/=))
    -- signed variants
    "<s"       -> Just ((<))
    "<=s"      -> Just ((<=))
    ">=s"      -> Just ((>=))
    ">s"       -> Just ((>))
    -- unsigned variants...
    "<u"       -> Just ((<))
    "<=u"      -> Just ((<=))
    ">=u"      -> Just ((>=))
    ">u"       -> Just ((>))
    -- float variants
    "<"        -> Just ((<))
    "<="       -> Just ((<=))
    ">="       -> Just ((>=))
    ">"        -> Just ((>))
    _ -> Nothing

tryGetFlonumPrimOp :: (Fractional a) => String -> Maybe (a -> a -> a)
tryGetFlonumPrimOp name =
  case name of
    "f*"       -> Just (*)
    "f+"       -> Just (+)
    "f-"       -> Just (-)
    "fdiv"     -> Just (/)
    _ -> Nothing

tryGetFlonumPrimUnOp :: (Floating a) => String -> Maybe (a -> a)
tryGetFlonumPrimUnOp name =
  case name of
    "fsqrt"    -> Just sqrt
    _ -> Nothing

--------------------------------------------------------------------

evalPrimitiveOp :: TypeIL -> String -> [SSValue] -> SSValue
evalPrimitiveOp (PrimIntIL size) nm args = evalPrimitiveIntOp size nm args
evalPrimitiveOp PrimFloat64IL nm args = evalPrimitiveDoubleOp nm args
evalPrimitiveOp ty opName args =
  error $ "Smallstep.evalPrimitiveOp " ++ show ty ++ " " ++ opName ++ " " ++ show args

evalPrimitiveDoubleOp :: String -> [SSValue] -> SSValue
evalPrimitiveDoubleOp opName [SSFloat d1] =
  case tryGetFlonumPrimUnOp opName of
    (Just fn) -> SSFloat $ (fn :: Double -> Double) d1
    _         -> error $ "Smallstep.evalPrimitiveDoubleOp:"
                      ++ "Unknown primitive unary operation " ++ opName

evalPrimitiveDoubleOp opName [SSFloat d1, SSFloat d2] =
  case tryGetFlonumPrimOp opName of
    (Just fn)
      -> SSFloat $ (fn :: Double -> Double -> Double) d1 d2
    _ -> case tryGetPrimCmp opName of
          (Just fn) -> SSBool ((fn :: Double -> Double -> Bool) d1 d2)
          _ -> error $ "Smallstep.evalPrimitiveDoubleOp:"
                    ++ "Unknown primitive operation " ++ opName

evalPrimitiveDoubleOp "fmuladd" [SSFloat d1, SSFloat d2, SSFloat d3] =
    SSFloat (d1 * d2 + d3)

evalPrimitiveDoubleOp opName args =
  error $ "Smallstep.evalPrimitiveDoubleOp " ++ opName ++ " " ++ show args

evalPrimitiveIntOp :: IntSizeBits -> String -> [SSValue] -> SSValue

evalPrimitiveIntOp I64 opName [SSInt i1, SSInt i2] =
  case tryGetFixnumPrimOp 64 opName of
    (Just fn)
      -> SSInt (modifyIntsWith i1 i2 (fn :: Int64 -> Int64 -> Int64))
    _ -> case tryGetPrimCmp opName of
          (Just fn) -> SSBool (liftInt2 fn i1 i2)
          _ -> error $ "Unknown primitive operation " ++ opName

evalPrimitiveIntOp I32 opName [SSInt i1, SSInt i2] =
  case tryGetFixnumPrimOp 32 opName of
    (Just fn)
      -> SSInt (modifyIntsWith i1 i2 (fn :: Int32 -> Int32 -> Int32))
    _ -> case tryGetPrimCmp opName of
          (Just fn) -> SSBool (liftInt2 fn i1 i2)
          _ -> error $ "Unknown primitive operation " ++ opName

evalPrimitiveIntOp I8 opName [SSInt i1, SSInt i2] =
  case tryGetFixnumPrimOp  8 opName of
    (Just fn)
      -> SSInt (modifyIntsWith i1 i2 (fn :: Int8 -> Int8 -> Int8))
    _ -> case tryGetPrimCmp opName of
          (Just fn) -> SSBool (liftInt2 fn i1 i2)
          _ -> error $ "Unknown primitive operation " ++ opName

evalPrimitiveIntOp (IWord 0) opName [SSInt i1, SSInt i2] =
  case tryGetFixnumPrimOp kVirtualWordSize opName of
    (Just fn)
      -> SSInt (modifyIntsWith i1 i2 (fn :: IntVW0 -> IntVW0 -> IntVW0))
    _ -> case tryGetPrimCmp opName of
          (Just fn) -> SSBool (liftInt2 fn i1 i2)
          _ -> error $ "Unknown primitive operation " ++ opName

evalPrimitiveIntOp (IWord 1) opName [SSInt i1, SSInt i2] =
  case tryGetFixnumPrimOp kVirtualWordSize opName of
    (Just fn)
      -> SSInt (modifyIntsWith i1 i2 (fn :: IntVW1 -> IntVW1 -> IntVW1))
    _ -> case tryGetPrimCmp opName of
          (Just fn) -> SSBool (liftInt2 fn i1 i2)
          _ -> error $ "Unknown primitive operation " ++ opName

-- TODO hmm
evalPrimitiveIntOp I32 "negate" [SSInt i] = SSInt (negate i)
evalPrimitiveIntOp I64 "negate" [SSInt i] = SSInt (negate i)
evalPrimitiveIntOp I8  "negate" [SSInt i] = SSInt (negate i)
evalPrimitiveIntOp (IWord 0) "negate" [SSInt i] = SSInt (negate i)

evalPrimitiveIntOp I1  "bitnot" [SSBool b] = SSBool (not b)
evalPrimitiveIntOp I32 "bitnot" [SSInt i] = SSInt $ modifyIntWith i (complement :: Int32 -> Int32)
evalPrimitiveIntOp I8  "bitnot" [SSInt i] = SSInt $ modifyIntWith i (complement :: Int8 -> Int8)
evalPrimitiveIntOp I64 "bitnot" [SSInt i] = SSInt $ modifyIntWith i (complement :: Int64 -> Int64)
evalPrimitiveIntOp (IWord 0) "bitnot" [SSInt i] = SSInt $ modifyIntWith i (complement :: IntVW0 -> IntVW0)

evalPrimitiveIntOp I32       "ctpop" [SSInt i] = SSInt (ctpop i 32)
evalPrimitiveIntOp I64       "ctpop" [SSInt i] = SSInt (ctpop i 64)
evalPrimitiveIntOp I8        "ctpop" [SSInt i] = SSInt (ctpop i 8 )
evalPrimitiveIntOp (IWord 0) "ctpop" [SSInt i] = SSInt (ctpop i 64)

evalPrimitiveIntOp I32       "ctlz"  [SSInt i] = SSInt (ctlz i 32)
evalPrimitiveIntOp I64       "ctlz"  [SSInt i] = SSInt (ctlz i 64)
evalPrimitiveIntOp I8        "ctlz"  [SSInt i] = SSInt (ctlz i 8 )
evalPrimitiveIntOp (IWord 0) "ctlz"  [SSInt i] = SSInt (ctlz i 64)

-- Extension (on Integers) is a no-op.
--evalPrimitiveIntOp _ "sext_i8"  [SSInt i] | i >= -128 && i <= 127 = SSInt i
--evalPrimitiveIntOp _ "zext_i8"  [SSInt i] | i >= 0    && i <= 255 = SSInt i
evalPrimitiveIntOp _ "sext_i32" [SSInt i] = SSInt i
evalPrimitiveIntOp _ "zext_i32" [SSInt i] = SSInt i
evalPrimitiveIntOp _ "sext_i64" [SSInt i] = SSInt i
evalPrimitiveIntOp _ "zext_i64" [SSInt i] = SSInt i
evalPrimitiveIntOp _ "sext_Word" [SSInt i] = SSInt i
evalPrimitiveIntOp _ "zext_Word" [SSInt i] = SSInt i
-- note: above case assumes virtual word size is 64, not 32.
evalPrimitiveIntOp _ "zext_WordX2" [SSInt i] = SSInt i

evalPrimitiveIntOp I32 "sitofp_f64"     [SSInt i] = SSFloat (fromIntegral i)
evalPrimitiveIntOp I32 "fptosi_f64_i32" [SSFloat f] =
  let ft = truncate f in
  let fi = toInteger (trunc32 ft) in
  if ft == fi then SSInt fi
              else error $ "Smallstep.fptosi: Can't fit in an Int32: " ++ show f

evalPrimitiveIntOp size opName args =
  error $ "Smallstep.evalPrimitiveIntOp " ++ show size ++ " " ++ opName ++ " " ++ show args

--------------------------------------------------------------------

ctpop i n = fromIntegral $ length [x | x <- showBits n i , x == '1']

ctlz  i n = fromIntegral $ length $ takeWhile (=='0') (showBits n i)

trunc8  = fromInteger :: Integer -> Int8
trunc32 = fromInteger :: Integer -> Int32
trunc64 = fromInteger :: Integer -> Int64

evalPrimitiveIntTrunc :: IntSizeBits -> IntSizeBits -> [SSValue] -> SSValue
evalPrimitiveIntTrunc I32 I8  [SSInt i] = SSInt (toInteger $ trunc8 i)
evalPrimitiveIntTrunc I64 I32 [SSInt i] = SSInt (toInteger $ trunc32 i)
evalPrimitiveIntTrunc (IWord 0) I32 [SSInt i] = SSInt (toInteger $ trunc32 i)
evalPrimitiveIntTrunc I64 (IWord 0) [SSInt i] = SSInt i
evalPrimitiveIntTrunc (IWord 1) I32 [SSInt i] = SSInt (toInteger $ trunc32 i)
evalPrimitiveIntTrunc (IWord 1) I64 [SSInt i] = SSInt (toInteger $ trunc64 i)
evalPrimitiveIntTrunc (IWord 1) (IWord 0) [SSInt i] = SSInt (toInteger $ trunc64 i)

evalPrimitiveIntTrunc from to _args =
  error $ "Smallstep.evalPrimitiveIntTrunc " ++ show from ++ " " ++ show to

-- This relies on the invariant that lists are created & stored densely.
packBytes :: MachineState -> Array Int Location -> Integer -> BS.ByteString
packBytes gs a n = let locs = List.take (fromInteger n) (elems a) in
                   let ints = map (\z -> let (SSInt i) = lookupHeap gs z in i) locs in
                   let bytes = (map fromInteger ints) :: [Word8] in
                   BS.takeWhile (/= 0) (BS.pack bytes)

-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||
-- |||||||||||||||||||||||  Named Primitives  |||||||||||||||||||{{{

evalNamedPrimitive :: String -> MachineState -> [SSValue] -> IO MachineState

evalNamedPrimitive primName gs [val] | isPrintFunction primName =
      do printStringNL gs (display val)
         return $ withTerm gs unit

evalNamedPrimitive primName gs [val] | isExpectFunction primName =
      do expectStringNL gs (display val)
         return $ withTerm gs unit

evalNamedPrimitive primName gs [SSInt i] | Just act <- lookupPrintInt i primName
    = do act gs ; return $ withTerm gs unit

evalNamedPrimitive "force_gc_for_debugging_purposes" gs _args =
         return $ withTerm gs unit

evalNamedPrimitive opaq gs [val] | opaq `elem` ["opaquely_i32", "opaquely_i64"] =
         return $ withTerm gs (SSTmValue $ val)

evalNamedPrimitive "print_newline" gs [] =
      do printStringNL gs ""
         return $ withTerm gs unit

evalNamedPrimitive "expect_newline" gs [] =
      do expectStringNL gs ""
         return $ withTerm gs unit

evalNamedPrimitive "prim_print_bytes_stdout" gs [SSArray a, SSInt n] =
      do printString gs (stringOfBytes $ packBytes gs a n)
         return $ withTerm gs unit

evalNamedPrimitive "prim_print_bytes_stderr" gs [SSArray a, SSInt n] =
      do expectString gs (stringOfBytes $ packBytes gs a n)
         return $ withTerm gs unit

evalNamedPrimitive "prim_print_bytes_stdout" gs [SSByteString bs, SSInt n] =
      do printString  gs (stringOfBytes $ BS.take (fromInteger n) bs)
         return $ withTerm gs unit

evalNamedPrimitive "prim_print_bytes_stderr" gs [SSByteString bs, SSInt n] =
      do expectString gs (stringOfBytes $ BS.take (fromInteger n) bs)
         return $ withTerm gs unit

evalNamedPrimitive "prim_arrayLength" gs [arr@(SSArray _)] =
      do return $ withTerm gs (SSTmValue $ SSInt (fromIntegral $ (prim_arrayLength arr)))

evalNamedPrimitive "prim_arrayLength" gs [arr@(SSByteString _)] =
      do return $ withTerm gs (SSTmValue $ SSInt (fromIntegral $ (prim_arrayLength arr)))

evalNamedPrimitive "get_cmdline_arg_n" gs [SSInt i] =
      do let argN = let args = stCmdArgs $ stConfig gs in
                    let ii = fromIntegral i in
                    T.pack $ if ii < List.length args && ii >= 0
                              then args !! ii else ""
         return $ withTerm gs (SSTmValue $ textFragmentOf argN)

evalNamedPrimitive "expect_float_p9f64" gs [SSFloat f] =
      do expectStringNL gs (printf "%.9f" f)
         return $ withTerm gs unit

evalNamedPrimitive "print_float_p9f64" gs [SSFloat f] =
      do printStringNL gs (printf "%.9f" f)
         return $ withTerm gs unit

evalNamedPrimitive "memcpy_i8_to_from_at_len" gs
         [SSArray arr, from_bs_or_arr, SSInt req_at_I, SSInt req_len_I] =
      do
         let min0 a b = max 0 (min a b)
         let (_, to_len) = bounds arr
         let   from_len  = prim_arrayLength from_bs_or_arr
         let    req_len  = min0 (fromInteger req_len_I) from_len
         let    req_at   = fromInteger req_at_I
         let to_rem = to_len - req_at
         if to_rem < 0 then error "memcpy_i8_to_from_at_len: req_at > to_len"
          else do
             let len = min0 to_rem req_len
             let idxs = take len $ [0..]
             (_, gs') <- mapFoldM idxs gs (\idx gs -> do
                             let val = prim_arrayRead gs idx from_bs_or_arr
                             let to_idx = req_at + fromIntegral idx
                             gs' <- prim_arrayPoke gs to_idx arr val
                             return ([], gs' ))
             return $ withTerm gs' unit

-- This should really be an opaque sized value, not a concrete Int64.
evalNamedPrimitive "foster_getticks" gs [] = do
  t <- getTime
  -- "Convert" seconds to ticks by treating our abstract machine
  -- as a blazingly fast 2 MHz beast!
  let t64 = round (t * 2000000.0)
  return $ withTerm gs (SSTmValue $ SSInt t64)

evalNamedPrimitive "foster_getticks_elapsed" gs [SSInt t1, SSInt t2] = do
  return $ withTerm gs (SSTmValue $ SSFloat (fromIntegral (t2 - t1)))

evalNamedPrimitive prim _gs args = error $ "evalNamedPrimitive " ++ show prim
                                         ++ " not yet defined for args:\n"
                                         ++ show args

lookupPrintInt :: Integer -> String -> Maybe (MachineState -> IO ())
lookupPrintInt i  "print_i64_bare" = Just (\gs -> printString   gs (showBits 64 i))
lookupPrintInt i  "print_i64b" =    Just (\gs ->  printStringNL gs (showBits 64 i))
lookupPrintInt i "expect_i64b" =    Just (\gs -> expectStringNL gs (showBits 64 i))
lookupPrintInt i  "print_i32b" =    Just (\gs ->  printStringNL gs (showBits 32 i))
lookupPrintInt i "expect_i32b" =    Just (\gs -> expectStringNL gs (showBits 32 i))
lookupPrintInt i  "print_i16b" =    Just (\gs ->  printStringNL gs (showBits 16 i))
lookupPrintInt i "expect_i16b" =    Just (\gs -> expectStringNL gs (showBits 16 i))
lookupPrintInt i  "print_i8b"  =    Just (\gs ->  printStringNL gs (showBits  8 i))
lookupPrintInt i "expect_i8b"  =    Just (\gs -> expectStringNL gs (showBits  8 i))
lookupPrintInt i  "print_i64x" =    Just (\gs ->  printStringNL gs (map toUpper $ showHex i "_16"))
lookupPrintInt i "expect_i64x" =    Just (\gs -> expectStringNL gs (map toUpper $ showHex i "_16"))
lookupPrintInt i  "print_i32x" =    Just (\gs ->  printStringNL gs (map toUpper $ showHex i "_16"))
lookupPrintInt i "expect_i32x" =    Just (\gs -> expectStringNL gs (map toUpper $ showHex i "_16"))
lookupPrintInt i  "print_i16x" =    Just (\gs ->  printStringNL gs (map toUpper $ showHex i "_16"))
lookupPrintInt i "expect_i16x" =    Just (\gs -> expectStringNL gs (map toUpper $ showHex i "_16"))
lookupPrintInt i  "print_i8x"  =    Just (\gs ->  printStringNL gs (map toUpper $ showHex i "_16"))
lookupPrintInt i "expect_i8x"  =    Just (\gs -> expectStringNL gs (map toUpper $ showHex i "_16"))
lookupPrintInt _ _ = Nothing

-- ByteString -> Text -> String
stringOfBytes = T.unpack . TE.decodeUtf8

-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

-- ||||||||||||||||||||  Coroutine Primitives  ||||||||||||||||||{{{
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
          , stConfig = (stConfig gs) { stCoroLoc = coroLoc ncoro }
        }
     else
        let newcoro = newcoro2 in
        let gs2 = gs {
            stHeap = modifyHeap2 gs (coroLoc ccoro) (SSCoro $ ccoro { coroStat = CoroStatusSuspended })
                                    (coroLoc ncoro) (SSCoro $ newcoro)
          , stConfig = (stConfig gs) { stCoroLoc = coroLoc ncoro }
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
        , stConfig = (stConfig gs) { stCoroLoc = prevloc }
      } in
      return $ gs2
evalCoroPrimitive CoroYield _gs _ = error $ "Wrong arguments to coro_yield"
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

-- ||||||||||||||||||||  Helpers & Boilerplate  |||||||||||||||||{{{
printStringNL gs s  = printString  gs (s ++ "\n")
expectStringNL gs s = expectString gs (s ++ "\n")

printString  gs s = do
  putDoc (blue $ text s)
  appendFile (outFile gs) s

expectString gs s = do
  putDoc (green $ text s)
  appendFile (errFile gs)  s

--------------------------------------------------------------------

textFragmentOf txt = SSCtorVal textFragmentCtor [SSByteString (TE.encodeUtf8 txt),
                                            SSInt $ fromIntegral (T.length txt)]
  where textFragmentCtor = CtorId "Text" "TextFragment" 2 -- see Primitives.hs

arrayOf :: MachineState -> [SSValue] -> IO MachineState
arrayOf gs0 vals = do
        (locs, gs2) <- mapFoldM (zip [0..] vals) gs0 $ \(n, val) gs1 ->
                              let (loc, gs2) = extendHeap gs1 val in
                              return ([(n, loc)], gs2)
        return $ withTerm gs2 (SSTmValue $ SSArray $
                                         array (0, List.length locs - 1) locs)
--------------------------------------------------------------------

showBits k n = -- k = 32, for example
  let bits = map (testBit n) [0 .. (k - 1)] in
  let s = map (\b -> if b then '1' else '0') bits in
  (reverse s) ++ "_2"

isPrintFunction name =
  case name of
    "print_i64"  -> True
    "print_i32"  -> True
    "print_i8"   -> True
    "print_i1"   -> True
    _ -> False

isExpectFunction name =
  case name of
    "expect_i64" -> True
    "expect_i32" -> True
    "expect_i8"  -> True
    "expect_i1"  -> True
    _ -> False

display :: SSValue -> String
display (SSBool True )  = "true"
display (SSBool False)  = "false"
display (SSByteString bs)= show bs
display (SSInt   i   )  = show i
display (SSFloat f   )  = show f
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

instance Show ShowableMachineState where show _ = "<machine state>"
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

