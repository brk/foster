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
import Data.Bits.Floating
import Data.Char(toUpper)
import Data.IORef(IORef, readIORef, newIORef)
import Data.Array
import Numeric(showHex)
import qualified Data.ByteString as BS
import Data.Double.Conversion.Text(toFixed)
import Text.PrettyPrint.ANSI.Leijen
import Criterion.Measurement(getTime, secs)

import Control.Exception(assert)
import System.Timeout(timeout)

import Foster.Base
import Foster.KNExpr
import Foster.KNUtil(TypeIL(..))

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

  let fiveSeconds = 5 * 1000 * 1000
  stepsTaken <- newIORef 0
  mbval <- timeout fiveSeconds $ interpret stepsTaken globalState
  numSteps <- readIORef stepsTaken
  case mbval of
    Just val -> do
      putStrLn ("Interpreter finished in " ++ show numSteps ++ " steps.")
      return $ Just val
    Nothing -> do
      putStrLn ("Interpreter timed out after " ++ show numSteps ++ " steps.")
      return Nothing
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
        | IArrayLit     Ident  [SSTerm]
        | IAllocArray   Ident
        | IIf           Ident   SSTerm     SSTerm
        | ICall         Ident  [Ident]
        | ICallPrim     (FosterPrim TypeIL) [Ident]
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
             | SSInt8      Int8
             | SSInt16     Int16
             | SSInt32     Int32
             | SSInt64     Int64
             | SSIntWd     Int64
             | SSIntDw     Int128
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
    KNLiteral (PrimIntIL isb) (LitInt i) -> SSTmValue $ mkSSInt isb (litIntValue i)
    --KNLiteral (PrimIntIL IWd) (LitInt i) -> SSTmValue $ SSInt8 (fromInteger $ litIntValue i)
    --KNLiteral (PrimIntIL IDw) (LitInt i) -> SSTmValue $ SSInt8 (fromInteger $ litIntValue i)
    KNLiteral _ (LitFloat f) -> SSTmValue $ SSFloat (litFloatValue f)
    KNLiteral _ (LitText  s) -> SSTmValue $ textFragmentOf s
    KNLiteral _ (LitByteArray bs) -> SSTmValue $ SSByteString bs
    KNVar        v         -> SSTmExpr  $ IVar (idOf v)
    KNTuple   _t vs _      -> SSTmExpr  $ ITuple (map idOf vs)
    KNLetFuns ids funs e _ -> SSTmExpr  $ ILetFuns   ids funs           (tr e)
    KNLetVal x b e _       -> SSTmExpr  $ ILetVal      x (tr b)         (tr e)
    KNLetRec ids exprs e   -> SSTmExpr  $ ILetRec    ids (map tr exprs) (tr e)
    KNCall     _t b vs     -> SSTmExpr  $ ICall (idOf b) (map idOf vs)
    KNCallPrim _ _t b vs   -> SSTmExpr  $ ICallPrim b (map idOf vs)
    KNIf       _t  v b c   -> SSTmExpr  $ IIf      (idOf v) (tr b) (tr c)
    KNArrayRead _t (ArrayIndex a b _ _)
                           -> SSTmExpr  $ IArrayRead (idOf a) (idOf b)
    KNArrayPoke _t (ArrayIndex b i _ _) v
                           -> SSTmExpr  $ IArrayPoke (idOf v) (idOf b) (idOf i)
    KNArrayLit t arr vals  -> SSTmExpr  $ IArrayLit  (idOf arr) (map (arrEntry t) vals)
    KNAllocArray _ety n _ _ _sr -> SSTmExpr  $ IAllocArray (idOf n)
    KNAlloc    _t a _rgn _ -> SSTmExpr  $ IAlloc (idOf a)
    KNDeref    _t a        -> SSTmExpr  $ IDeref (idOf a)
    KNStore    _t a b      -> SSTmExpr  $ IStore (idOf a) (idOf b)
    KNTyApp    _t v argtys -> SSTmExpr  $ ITyApp (idOf v) argtys
    KNCase _t a bs {-dt-}  -> SSTmExpr  $ ICase (idOf a) {-dt-} [CaseArm p (tr e) (fmap tr g) b r
                                                                |CaseArm p e g b r <- bs] []
    KNHandler {} -> error $ "KSmallstep.hs: KNHandler not yet implemented"
    KNAppCtor     _t cr vs _sr -> SSTmExpr  $ IAppCtor (fst cr) (map idOf vs)
    KNKillProcess _t msg   -> SSTmExpr  $ error $ "prim kill-process: " ++ T.unpack msg
    KNCompiles {} -> SSTmValue $ SSBool True -- TODO maybe have __COMPILES__ take a default parameter for us to return?
    KNRelocDoms         _ e -> ssTermOfExpr e

arrEntry _t (Right var) = SSTmExpr $ IVar $ tidIdent var
arrEntry              (PrimIntIL isb)  (Left (LitInt lit)) = SSTmValue $ mkSSInt isb (litIntValue lit)
arrEntry (ArrayTypeIL (PrimIntIL isb)) (Left (LitInt lit)) = SSTmValue $ mkSSInt isb (litIntValue lit)
arrEntry ty other = error $ "KSmallstep.hs: Unsupported array entry type: " ++ show other ++ "\nof type" ++ show ty

mkSSInt I1  i = SSInt8  (fromInteger i)
mkSSInt I8  i = SSInt8  (fromInteger i)
mkSSInt I16 i = SSInt16 (fromInteger i)
mkSSInt I32 i = SSInt32 (fromInteger i)
mkSSInt I64 i = SSInt64 (fromInteger i)
mkSSInt IWd i = SSIntWd (fromInteger i)
mkSSInt IDw i = SSIntDw (fromInteger i)

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

    IArrayLit arr entries ->
      let args = map (evalTerm gs) entries
          base = getval gs arr
          go :: MachineState -> Int -> [SSValue] -> IO MachineState
          go gs _ [] = return $ withTerm gs (SSTmValue base)
          go gs n (val:vals) = do
            gs' <- arrayPoke gs base n val
            go gs' (n + 1) vals
      in
      go gs 0 args


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
          PrimInlineAsm {} -> error $ "KSmallstep.hs: Interpreter cannot handle inline asm!"
          LookupEffectHandler _ -> error $ "KSmallstep.hs: Interpreter cannot yet look up effect handlers"
    ICall b vs ->
        let args = map (getval gs) vs in
        case getval gs b of
           SSFunc func -> return (callFunc gs func args withTerm)
           v -> error $ "Cannot call non-function value " ++ display v

    IArrayRead base idxvar ->
        let Right n = getint $ getval gs idxvar in
        case getval gs base of
          a@(SSArray _)      ->
            return $ withTerm gs (SSTmValue $ prim_arrayRead gs n a)
          a@(SSByteString _) -> return $ withTerm gs (SSTmValue $ prim_arrayRead gs n a)
          other -> error $ "KSmallstep: Expected base of array read "
                        ++ "(" ++ show base ++ "["++ show idxvar++"])"
                        ++ " to be array value; had " ++ show other

    IArrayPoke iv base idxvar ->
        let Right n = getint $ getval gs idxvar  in
        arrayPoke gs (getval gs base) n (getval gs iv)

    IAllocArray sizeid -> do
        let (SSInt32 i) = getval gs sizeid
        -- The array cells are initially filled with constant zeros,
        -- regardless of what type we will eventually store.
        arrayOf gs [SSInt32 n | n <- [0 .. i - 1]]

getint :: SSValue -> Either SSValue Int
getint (SSInt32 i) = Right $ fromIntegral i
getint (SSInt16 i) = Right $ fromIntegral i
getint (SSInt8  i) = Right $ fromIntegral i
getint val = Left val
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

-- |||||||||||||||||||||||| Pattern Matching ||||||||||||||||||||{{{
matchPattern :: PatternRepr TypeIL -> SSValue -> Maybe [(Ident, SSValue)]
matchPattern p v =
  case (v, p) of
    (_, PR_Atom (P_Wildcard _ _  )) -> trivialMatchSuccess
    (_, PR_Atom (P_Variable _ tid)) -> Just [(tidIdent tid, v)]

    (SSInt8  i1, PR_Atom (P_Int _ _ i2))   -> matchIf $ i1 == fromIntegral (litIntValue i2)
    (SSInt16 i1, PR_Atom (P_Int _ _ i2))   -> matchIf $ i1 == fromIntegral (litIntValue i2)
    (SSInt32 i1, PR_Atom (P_Int _ _ i2))   -> matchIf $ i1 == fromIntegral (litIntValue i2)
    (SSInt64 i1, PR_Atom (P_Int _ _ i2))   -> matchIf $ i1 == fromIntegral (litIntValue i2)
    (_       , PR_Atom (P_Int _ _ _ ))   -> matchFailure

    (SSBool b1, PR_Atom (P_Bool _ _ b2)) -> matchIf $ b1 == b2
    (_        , PR_Atom (P_Bool _ _ _ )) -> matchFailure

    (SSCtorVal vid vals, PR_Ctor _ _ pats (LLCtorInfo cid _ _ _)) -> do
                                            _ <- matchIf $ vid == cid
                                            matchPatterns pats vals
    (_                 , PR_Ctor _ _ _ _) -> matchFailure

    (SSTuple vals, PR_Tuple _ _ pats) -> matchPatterns pats vals
    (_, PR_Or _ _ pats) -> matchOr v pats
    (_, PR_Tuple _ _ _) -> matchFailure
 where
   trivialMatchSuccess = Just []
   matchFailure        = Nothing
   matchIf cond = if cond then trivialMatchSuccess
                          else matchFailure
   matchOr _ [] = matchFailure
   matchOr v (p:pats) = case matchPattern p v of
                          Just ok -> Just ok
                          Nothing -> matchOr v pats

matchPatterns :: [PatternRepr TypeIL] -> [SSValue] -> Maybe [(Ident, SSValue)]
matchPatterns pats vals = do
  matchLists <- mapM (\(p, v) -> matchPattern p v) (zip pats vals)
  return $ concat matchLists
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

-- |||||||||||||||||||||| Primitive Operators ||||||||||||||||||{{{
kVirtualWordSize = 64
type IntVW0 = Int64
type IntVW1 = Int128
type WordVW0 = Word64
type WordVW1 = Word128

arraySlotLocation arr n = SSLocation (arr ! n)

prim_arrayLength :: SSValue -> Int64
prim_arrayLength (SSArray a) = let (b,e) = bounds a in fromIntegral $ e - b + 1
prim_arrayLength (SSByteString bs) =                 fromIntegral $ BS.length bs
prim_arrayLength _ = error "prim_arrayLength got non-array value!"

prim_arrayRead :: MachineState -> Int -> SSValue -> SSValue
prim_arrayRead gs n (SSArray arr) =
        let (SSLocation z) = arraySlotLocation arr n in lookupHeap gs z
prim_arrayRead _  n (SSByteString bs) = SSInt8 . fromIntegral $ BS.index bs n
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

lowShiftBits k b = (k - 1) .&. fromIntegral b

shr k a b = shiftR a (lowShiftBits k b)
shl k a b = shiftL a (lowShiftBits k b)

data PrimOpResult a b = POR_Signed    (a -> a -> a)
                      | POR_Unsigned  (b -> b -> b)
                      | POR_SignedB   (a -> a -> Bool)
                      | POR_UnsignedB (b -> b -> Bool)
                      | POR_Missing

-- k is the paramerized bitwidth.
tryGetFixnumPrimOp :: (Bits a, Integral a, Bits b, Integral b)
                   => Int -> String -> PrimOpResult a b
tryGetFixnumPrimOp k name =
  case name of
    "*"           -> POR_Signed   (*)
    "+"           -> POR_Signed   (+)
    "-"           -> POR_Signed   (-)
    "sdiv-unsafe" -> POR_Signed   quot -- not div! (which is F-division)
    "udiv-unsafe" -> POR_Unsigned quot
    "srem-unsafe" -> POR_Signed   rem
    "urem-unsafe" -> POR_Unsigned rem
    "bitxor"      -> POR_Unsigned xor
    "bitor"       -> POR_Unsigned (.|.)
    "bitand"      -> POR_Unsigned (.&.)
    "bitashr"     -> POR_Signed   (shr k)
    "bitlshr"     -> POR_Unsigned (shr k)
    "bitshl"      -> POR_Unsigned (shl k)

    "=="       -> POR_SignedB ((==))
    "!="       -> POR_SignedB ((/=))
    -- signed variants
    "<s"       -> POR_SignedB ((<))
    "<=s"      -> POR_SignedB ((<=))
    ">=s"      -> POR_SignedB ((>=))
    ">s"       -> POR_SignedB ((>))
    -- unsigned variants...
    "<u"       -> POR_UnsignedB ((<))
    "<=u"      -> POR_UnsignedB ((<=))
    ">=u"      -> POR_UnsignedB ((>=))
    ">u"       -> POR_UnsignedB ((>))

    _ -> POR_Missing


data PrimOpFloat = PrimOpFloat2 (Double -> Double -> Double)
                 | PrimOpFloatB (Double -> Double -> Bool)
                 | PrimOpFloatMissing

tryGetFlonumPrimOp :: String -> PrimOpFloat
tryGetFlonumPrimOp name =
  case name of
    "f*"       -> PrimOpFloat2 (*)
    "f+"       -> PrimOpFloat2 (+)
    "f-"       -> PrimOpFloat2 (-)
    "fdiv"     -> PrimOpFloat2 (/)

    "f=="      -> PrimOpFloatB ((==))
    "f<"       -> PrimOpFloatB ((<))
    "f<="      -> PrimOpFloatB ((<=))
    "f>="      -> PrimOpFloatB ((>=))
    "f>"       -> PrimOpFloatB ((>))
    _ -> PrimOpFloatMissing

tryGetFlonumPrimUnOp :: (Floating a) => String -> Maybe (a -> a)
tryGetFlonumPrimUnOp name =
  case name of
    "fsqrt"    -> Just sqrt
    _ -> Nothing

--------------------------------------------------------------------

evalPrimitiveOp :: TypeIL -> String -> [SSValue] -> SSValue
evalPrimitiveOp (PrimIntIL size) nm args = evalPrimitiveIntOp size nm args
evalPrimitiveOp (TyAppIL (TyConIL "Float64") []) nm args = evalPrimitiveDoubleOp nm args
--evalPrimitiveOp (TyAppIL (TyConIL "Float32") []) nm args = evalPrimitiveFloat32Op nm args
evalPrimitiveOp ty opName args =
  error $ "Smallstep.evalPrimitiveOp " ++ show ty ++ " " ++ opName ++ " " ++ show args

evalPrimitiveDoubleOp :: String -> [SSValue] -> SSValue
evalPrimitiveDoubleOp "bitcast_i64" [SSFloat f] = let val = (fromIntegral $ coerceToWord f) in
 --trace ("f64-to-i64: f = " ++ show f ++ "; (coerceToWord f) == " ++ show (coerceToWord f) ++ "; result = " ++ show val) $
  SSInt64 val
evalPrimitiveDoubleOp "fpowi" [SSFloat d, SSInt32 z] =
  SSFloat (d ** fromIntegral z)

evalPrimitiveDoubleOp opName [SSFloat d1] =
  case tryGetFlonumPrimUnOp opName of
    (Just fn) -> SSFloat $ (fn :: Double -> Double) d1
    _         -> error $ "Smallstep.evalPrimitiveDoubleOp:"
                      ++ "Unknown primitive unary operation " ++ opName

evalPrimitiveDoubleOp opName [SSFloat d1, SSFloat d2] =
  case tryGetFlonumPrimOp opName of
    PrimOpFloat2 fn -> SSFloat $ fn d1 d2
    PrimOpFloatB fn -> SSBool  $ fn d1 d2
    _ -> error $ "Smallstep.evalPrimitiveDoubleOp:"
               ++ "Unknown primitive operation " ++ opName

evalPrimitiveDoubleOp "fmuladd" [SSFloat d1, SSFloat d2, SSFloat d3] =
    SSFloat (d1 * d2 + d3)

evalPrimitiveDoubleOp opName args =
  error $ "Smallstep.evalPrimitiveDoubleOp " ++ opName ++ " " ++ show args

coerceU :: (Integral a, Integral b) => (a -> a -> a) -> (b -> b -> b)
coerceU f2 b1 b2 = fromIntegral (coerce f2 b1 b2)

coerce :: (Integral a, Integral b) => (a -> a -> c) -> (b -> b -> c)
coerce f2 b1 b2 = f2 (fromIntegral b1) (fromIntegral b2)

evalPrimitiveIntOp :: IntSizeBits -> String -> [SSValue] -> SSValue
evalPrimitiveIntOp I64 "bitcast_f64" [SSInt64 z] =
  SSFloat (coerceToFloat $ fromIntegral z)

evalPrimitiveIntOp I64 opName [SSInt64 i1, SSInt64 i2] =
  case tryGetFixnumPrimOp 64 opName :: PrimOpResult Int64 Word64 of
    (POR_Signed   fn) -> SSInt64 (        fn i1 i2)
    (POR_Unsigned fn) -> SSInt64 (coerceU fn i1 i2)
    (POR_SignedB   fn) -> SSBool (        fn i1 i2)
    (POR_UnsignedB fn) -> SSBool (coerce  fn i1 i2)
    _ -> error $ "Unknown primitive operation " ++ opName

evalPrimitiveIntOp I32 opName [SSInt32 i1, SSInt32 i2] =
  case tryGetFixnumPrimOp 32 opName :: PrimOpResult Int32 Word32 of
    (POR_Signed   fn) -> SSInt32 (        fn i1 i2)
    (POR_Unsigned fn) -> SSInt32 (coerceU fn i1 i2)
    (POR_SignedB   fn) -> SSBool (        fn i1 i2)
    (POR_UnsignedB fn) -> SSBool (coerce  fn i1 i2)
    _ -> error $ "Unknown primitive operation " ++ opName

evalPrimitiveIntOp I16 opName [SSInt16 i1, SSInt16 i2] =
  case tryGetFixnumPrimOp 16 opName :: PrimOpResult Int16 Word16 of
    (POR_Signed   fn) -> SSInt16 (        fn i1 i2)
    (POR_Unsigned fn) -> SSInt16 (coerceU fn i1 i2)
    (POR_SignedB   fn) -> SSBool (        fn i1 i2)
    (POR_UnsignedB fn) -> SSBool (coerce  fn i1 i2)
    _ -> error $ "Unknown primitive operation " ++ opName

evalPrimitiveIntOp I8 opName [SSInt8 i1, SSInt8 i2] =
  case tryGetFixnumPrimOp  8 opName :: PrimOpResult Int8 Word8 of
    (POR_Signed   fn) -> SSInt8 (        fn i1 i2)
    (POR_Unsigned fn) -> SSInt8 (coerceU fn i1 i2)
    (POR_SignedB   fn) -> SSBool (       fn i1 i2)
    (POR_UnsignedB fn) -> SSBool (coerce fn i1 i2)
    _ -> error $ "Unknown primitive operation " ++ opName

evalPrimitiveIntOp IWd opName [SSIntWd i1, SSIntWd i2] =
  case tryGetFixnumPrimOp kVirtualWordSize opName :: PrimOpResult IntVW0 WordVW0 of
    (POR_Signed   fn) -> SSIntWd (        fn i1 i2)
    (POR_Unsigned fn) -> SSIntWd (coerceU fn i1 i2)
    (POR_SignedB   fn) -> SSBool (       fn i1 i2)
    (POR_UnsignedB fn) -> SSBool (coerce fn i1 i2)
    _ -> error $ "Unknown primitive operation " ++ opName

evalPrimitiveIntOp IDw opName [SSIntDw i1, SSIntDw i2] =
  case tryGetFixnumPrimOp kVirtualWordSize opName :: PrimOpResult IntVW1 WordVW1 of
    (POR_Signed   fn) -> SSIntDw (        fn i1 i2)
    (POR_Unsigned fn) -> SSIntDw (coerceU fn i1 i2)
    (POR_SignedB   fn) -> SSBool (       fn i1 i2)
    (POR_UnsignedB fn) -> SSBool (coerce fn i1 i2)
    _ -> error $ "Unknown primitive operation " ++ opName

evalPrimitiveIntOp I32 "negate" [SSInt32 i] = SSInt32 (negate i)
evalPrimitiveIntOp I64 "negate" [SSInt64 i] = SSInt64 (negate i)
evalPrimitiveIntOp I8  "negate" [SSInt8  i] = SSInt8  (negate i)
evalPrimitiveIntOp I16 "negate" [SSInt16 i] = SSInt16 (negate i)
evalPrimitiveIntOp IWd "negate" [SSIntWd i] = SSIntWd (negate i)

evalPrimitiveIntOp I1  "bitnot" [SSBool b] = SSBool (not b)
evalPrimitiveIntOp I32 "bitnot" [SSInt32 i] = SSInt32 $ complement i
evalPrimitiveIntOp I64 "bitnot" [SSInt64 i] = SSInt64 $ complement i
evalPrimitiveIntOp I8  "bitnot" [SSInt8  i] = SSInt8  $ complement i
evalPrimitiveIntOp I16 "bitnot" [SSInt16 i] = SSInt16 $ complement i
evalPrimitiveIntOp IWd "bitnot" [SSIntWd i] = SSIntWd $ complement i

evalPrimitiveIntOp I32       "ctpop" [SSInt32 i] = SSInt32 (ctpop i 32)
evalPrimitiveIntOp I64       "ctpop" [SSInt64 i] = SSInt64 (ctpop i 64)
evalPrimitiveIntOp I8        "ctpop" [SSInt8  i] = SSInt8  (ctpop i 8 )
evalPrimitiveIntOp I16       "ctpop" [SSInt16 i] = SSInt16 (ctpop i 16)
evalPrimitiveIntOp IWd       "ctpop" [SSIntWd i] = SSIntWd (ctpop i kVirtualWordSize)

evalPrimitiveIntOp I32       "ctlz"  [SSInt32 i] = SSInt32 (ctlz i 32)
evalPrimitiveIntOp I64       "ctlz"  [SSInt64 i] = SSInt64 (ctlz i 64)
evalPrimitiveIntOp I8        "ctlz"  [SSInt8  i] = SSInt8  (ctlz i 8 )
evalPrimitiveIntOp I16       "ctlz"  [SSInt16 i] = SSInt16 (ctlz i 16)
evalPrimitiveIntOp IWd       "ctlz"  [SSIntWd i] = SSIntWd (ctlz i kVirtualWordSize)

evalPrimitiveIntOp _  "sext_i16" [SSInt8  i] = SSInt16 (fromIntegral i)
evalPrimitiveIntOp _  "sext_i32" [SSInt8  i] = SSInt32 (fromIntegral i)
evalPrimitiveIntOp _  "sext_i64" [SSInt8  i] = SSInt64 (fromIntegral i)
evalPrimitiveIntOp _  "sext_i32" [SSInt16 i] = SSInt32 (fromIntegral i)
evalPrimitiveIntOp _  "sext_i64" [SSInt16 i] = SSInt64 (fromIntegral i)
evalPrimitiveIntOp _  "sext_i64" [SSInt32 i] = SSInt64 (fromIntegral i)

evalPrimitiveIntOp _  "zext_i16" [SSInt8  i] = SSInt16 $ unsigned 8  (fromIntegral i)
evalPrimitiveIntOp _  "zext_i32" [SSInt8  i] = SSInt32 $ unsigned 8  (fromIntegral i)
evalPrimitiveIntOp _  "zext_i64" [SSInt8  i] = SSInt64 $ unsigned 8  (fromIntegral i)
evalPrimitiveIntOp _  "zext_i32" [SSInt16 i] = SSInt32 $ unsigned 16 (fromIntegral i)
evalPrimitiveIntOp _  "zext_i64" [SSInt16 i] = SSInt64 $ unsigned 16 (fromIntegral i)
evalPrimitiveIntOp _  "zext_i64" [SSInt32 i] = SSInt64 $ unsigned 32 (fromIntegral i)

evalPrimitiveIntOp I32 "sitofp_f64"     [SSInt32 i] = SSFloat (fromIntegral i)
evalPrimitiveIntOp I32 "uitofp_f64"     [SSInt32 i] = SSFloat (fromIntegral i)
evalPrimitiveIntOp I64 "sitofp_f64"     [SSInt64 i] = SSFloat $ toDoubleLikeC              (fromIntegral i)
evalPrimitiveIntOp I64 "uitofp_f64"     [SSInt64 i] = SSFloat $ toDoubleLikeC (unsigned 64 (fromIntegral i))
evalPrimitiveIntOp I32 "fptosi_f64_i32" [SSFloat f] = SSInt32 (truncate f)
evalPrimitiveIntOp I32 "fptoui_f64_i32" [SSFloat f] = SSInt32 (truncate f) -- TODO probably wrong
evalPrimitiveIntOp I64 "fptosi_f64_i64" [SSFloat f] = SSInt64 (truncate f)
evalPrimitiveIntOp I64 "fptoui_f64_i64" [SSFloat f] = SSInt64 (truncate f) -- TODO probably wrong

evalPrimitiveIntOp size opName args =
  error $ "Smallstep.evalPrimitiveIntOp " ++ show size ++ " " ++ opName ++ " " ++ show args

-- This is true with GHC 8.0.1 on 32-bit Linux
--    and false with GHC 8.0.1 on 64-bit Linux (!)
defaultRoundsDown = ((fromInteger 4611686018427387648) :: Double) == 4611686018427387392.0

toDoubleLikeC :: Integer -> Double
toDoubleLikeC i =
  if defaultRoundsDown
   then let val = fromInteger i :: Double in
        let ulps = ulp val in
        case (ulps >= 2.0, i > 0) of
          (True, True)  -> fromInteger (i + (round $ ulps / 2.0))
          (True, False) -> fromInteger (i - (round $ ulps / 2.0))
          _ -> val
   else fromInteger i
--------------------------------------------------------------------

ctpop i n = fromIntegral $ length [x | x <- showBits n i , x == '1']

ctlz  i n = fromIntegral $ length $ takeWhile (=='0') (showBits n i)

evalPrimitiveIntTrunc :: IntSizeBits -> IntSizeBits -> [SSValue] -> SSValue
evalPrimitiveIntTrunc   _ I8  [SSInt32 i] = SSInt8  $ fromIntegral i
evalPrimitiveIntTrunc   _ I8  [SSInt64 i] = SSInt8  $ fromIntegral i
evalPrimitiveIntTrunc   _ I32 [SSInt64 i] = SSInt32 $ fromIntegral i

--evalPrimitiveIntTrunc I64 (IWord 0) [SSInt i] = SSInt i
--evalPrimitiveIntTrunc (IWord 1) (IWord 0) [SSInt i] = SSInt (toInteger $ trunc64 i)

evalPrimitiveIntTrunc from to _args =
  error $ "Smallstep.evalPrimitiveIntTrunc " ++ show from ++ " " ++ show to

-- This relies on the invariant that lists are created & stored densely.
packBytes :: MachineState -> Array Int Location -> Int32 -> BS.ByteString
packBytes gs a n = let locs = List.take (fromIntegral n) (elems a) in
                   let ints = map (\z -> let (SSInt8 i) = lookupHeap gs z in i) locs in
                   let bytes = (map fromIntegral ints) :: [Word8] in
                   BS.takeWhile (/= 0) (BS.pack bytes)

-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||
-- |||||||||||||||||||||||  Integer Helpers   |||||||||||||||||||{{{
mbInteger :: SSValue -> Maybe (IntSizeBits, Integer)
mbInteger (SSInt8  i) = Just (I8 , fromIntegral i)
mbInteger (SSInt32 i) = Just (I32, fromIntegral i)
mbInteger (SSInt64 i) = Just (I64, fromIntegral i)
mbInteger _ = Nothing
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||
-- |||||||||||||||||||||||  Named Primitives  |||||||||||||||||||{{{

evalNamedPrimitive :: String -> MachineState -> [SSValue] -> IO MachineState

evalNamedPrimitive primName gs [val] | Just fmt <- isPrintFunction primName =
      do printStringNL gs (fmt val)
         return $ withTerm gs unit

evalNamedPrimitive primName gs [val] | Just fmt <- isExpectFunction primName =
      do expectStringNL gs (fmt val)
         return $ withTerm gs unit

evalNamedPrimitive primName gs [intish] | Just (_, i) <- mbInteger intish,
                                          Just act <- lookupPrintInt (fromIntegral i) primName
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

evalNamedPrimitive "prim_print_bytes_stdout" gs [SSArray a, SSInt32 n] =
      do printString gs (stringOfBytes $ packBytes gs a n)
         return $ withTerm gs unit

evalNamedPrimitive "prim_print_bytes_stderr" gs [SSArray a, SSInt32 n] =
      do expectString gs (stringOfBytes $ packBytes gs a n)
         return $ withTerm gs unit

evalNamedPrimitive "prim_print_bytes_stdout" gs [SSByteString bs, SSInt32 n] =
      do printString  gs (stringOfBytes $ BS.take (fromIntegral n) bs)
         return $ withTerm gs unit

evalNamedPrimitive "prim_print_bytes_stderr" gs [SSByteString bs, SSInt32 n] =
      do expectString gs (stringOfBytes $ BS.take (fromIntegral n) bs)
         return $ withTerm gs unit

evalNamedPrimitive "prim_arrayLength" gs [arr@(SSArray _)] =
      do return $ withTerm gs (SSTmValue $ SSInt64 (fromIntegral (prim_arrayLength arr)))

evalNamedPrimitive "prim_arrayLength" gs [arr@(SSByteString _)] =
      do return $ withTerm gs (SSTmValue $ SSInt64 (fromIntegral (prim_arrayLength arr)))

evalNamedPrimitive "get_cmdline_arg_n" gs [SSInt32 i] =
      do let argN = let args = stCmdArgs $ stConfig gs in
                    let ii = fromIntegral i in
                    T.pack $ if ii < List.length args && ii >= 0
                              then args !! ii else ""
         return $ withTerm gs (SSTmValue $ textFragmentOf argN)

evalNamedPrimitive "expect_float_p9f64" gs [SSFloat f] =
      do expectStringNL gs (T.unpack $ toFixed 9 f)
         return $ withTerm gs unit

evalNamedPrimitive "print_float_p9f64" gs [SSFloat f] =
      do printStringNL gs (T.unpack $ toFixed 9 f)
         return $ withTerm gs unit

-- {{{
-- to[req_at..whatever] = from[0..req_len]
evalNamedPrimitive "memcpy_i8_to_at_from_len" gs
         [SSArray arr, SSInt32 req_at_I , from_bs_or_arr, SSInt32 req_len_I] =
  evalNamedPrimitive "memcpy_i8_to_at_from_at_len" gs
         [SSArray arr, SSInt64 (fromIntegral req_at_I) , from_bs_or_arr,
                       SSInt64 0, SSInt64 (fromIntegral req_len_I)]

-- to[0..req_len] = from[req_at..req_at+req_len]
evalNamedPrimitive "memcpy_i8_to_from_at_len" gs
         [SSArray arr, from_bs_or_arr, SSInt32 req_at_I, SSInt32 req_len_I] =
  evalNamedPrimitive "memcpy_i8_to_at_from_at_len" gs
         [SSArray arr, SSInt64 0, from_bs_or_arr, SSInt64 (fromIntegral req_at_I),
                       SSInt64 (fromIntegral req_len_I)]

-- to[to_at..to_at+req_len] = from[from_at..from_at+req_len]
evalNamedPrimitive "memcpy_i8_to_at_from_at_len" gs
         [SSArray arr, SSInt64 to_at, from_bs_or_arr, SSInt64 from_at, SSInt64 req_len_I] =
   if isSameArray (SSArray arr) from_bs_or_arr
    then error "memcpy_i8_to_from_at_len: arrays were aliased!"
    else
      do let min0 a b c = max 0 (min (min a b) c)
         let     to_len  = prim_arrayLength (SSArray arr)
         let   from_len  = prim_arrayLength from_bs_or_arr
         let    req_len  = min0 req_len_I from_len to_len
         let   to_rem =   to_len -   to_at
         let from_rem = from_len - from_at
         let len = min0 to_rem from_rem req_len
         case () of
           _ | to_rem < 0 || from_rem < 0
            -> error "memcpy_i8_to_from_at_len: *_at > *_len"
           _ | len /= req_len
            -> error "memcpy_i8_to_from_at_len: unable to copy requested length"
           _ -> do
             let idxs = take (fromIntegral len) $ [from_at..] :: [Int64]
             (_, gs') <- mapFoldM idxs gs (\idx64 gs -> do
                             let val = prim_arrayRead gs (fromIntegral idx64) from_bs_or_arr
                             let to_idx = fromIntegral (to_at + (idx64 - from_at))
                             gs' <- prim_arrayPoke gs to_idx arr val
                             return ([], gs' ))
             return $ withTerm gs' unit
-- }}}

-- {{{
evalNamedPrimitive "foster_getticks" gs [] = do
  t <- getTime
  -- "Convert" seconds to ticks by treating our abstract machine
  -- as a blazingly fast 2 MHz beast!
  let t64 = round (t * 2000000.0)
  return $ withTerm gs (SSTmValue $ SSInt64 t64)

evalNamedPrimitive "foster_getticks_elapsed" gs [SSInt64 t1, SSInt64 t2] = do
  return $ withTerm gs (SSTmValue $ SSFloat (fromIntegral (t2 - t1)))
-- }}}

-- {{{
evalNamedPrimitive "foster_gettime_microsecs" gs [] = do
  t_secs <- getTime
  let t_us = round (t_secs * 1e6)
  return $ withTerm gs (SSTmValue $ SSInt64 t_us)

evalNamedPrimitive "foster_gettime_elapsed_secs" gs [SSInt64 t1_us, SSInt64 t2_us] = do
  return $ withTerm gs (SSTmValue $ SSFloat (fromIntegral (t2_us - t1_us) * 1e6))

evalNamedPrimitive "foster_fmttime_secs" gs [SSFloat d] = do
  return $ withTerm gs (SSTmValue $ textFragmentOf $ T.pack (secs d))
-- }}}

evalNamedPrimitive prim _gs args = error $ "evalNamedPrimitive " ++ show prim
                                         ++ " not yet defined for args:\n"
                                         ++ show args

isSameArray (SSArray a) (SSArray b) =
  case (elems a, elems b) of
    ((x:_), (y:_)) -> x == y
    _ -> False -- Either at least one empty array, in which case there are no
               -- observations to show aliasing; else the arrays aren't aliased.
isSameArray _ _ = False

lookupPrintInt :: Integer -> String -> Maybe (MachineState -> IO ())
lookupPrintInt i  "print_i64_bare" = Just (\gs -> printString   gs (showSigned 64 i))
lookupPrintInt i  "print_i64b" =    Just (\gs ->  printStringNL gs (showBits 64 i))
lookupPrintInt i "expect_i64b" =    Just (\gs -> expectStringNL gs (showBits 64 i))
lookupPrintInt i  "print_i32b" =    Just (\gs ->  printStringNL gs (showBits 32 i))
lookupPrintInt i "expect_i32b" =    Just (\gs -> expectStringNL gs (showBits 32 i))
lookupPrintInt i  "print_i16b" =    Just (\gs ->  printStringNL gs (showBits 16 i))
lookupPrintInt i "expect_i16b" =    Just (\gs -> expectStringNL gs (showBits 16 i))
lookupPrintInt i  "print_i8b"  =    Just (\gs ->  printStringNL gs (showBits  8 i))
lookupPrintInt i "expect_i8b"  =    Just (\gs -> expectStringNL gs (showBits  8 i))
lookupPrintInt i  "print_i64x" =    Just (\gs ->  printStringNL gs (showHexy 64 i))
lookupPrintInt i "expect_i64x" =    Just (\gs -> expectStringNL gs (showHexy 64 i))
lookupPrintInt i  "print_i32x" =    Just (\gs ->  printStringNL gs (showHexy 32 i))
lookupPrintInt i "expect_i32x" =    Just (\gs -> expectStringNL gs (showHexy 32 i))
lookupPrintInt i  "print_i16x" =    Just (\gs ->  printStringNL gs (showHexy 16 i))
lookupPrintInt i "expect_i16x" =    Just (\gs -> expectStringNL gs (showHexy 16 i))
lookupPrintInt i  "print_i8x"  =    Just (\gs ->  printStringNL gs (showHexy  8 i))
lookupPrintInt i "expect_i8x"  =    Just (\gs -> expectStringNL gs (showHexy  8 i))
lookupPrintInt _ _ = Nothing

showHexy :: (Integral x, Show x) => x -> x -> String
showHexy bitwidth n = "0x" ++ (map toUpper $ showHex (unsigned bitwidth n) "")

showSigned :: Integer -> Integer -> String
showSigned bitwidth n =
  let maxpos = 2 ^ (bitwidth - 1)
      maxnat = 2 ^ bitwidth in
  case (n >= maxpos, n < -maxpos) of
    (True, _) -> showSigned bitwidth $ n - maxnat
    (_, True) -> showSigned bitwidth $ n + maxnat
    _ -> show n

unsigned bitwidth n = if n >= 0 then n else (2 ^ bitwidth) + n

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
textFragmentOf txt = SSCtorVal textFragmentCtor [SSByteString bytes, SSInt32 len]
  where textFragmentCtor = CtorId "Text" "TextFragment" 2 -- see Primitives.hs
        bytes = TE.encodeUtf8 txt
        len   = fromIntegral $ BS.length bytes
        -- Note: length in *bytes*, not Unicode chars!

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
  "0b" ++ (reverse s)

isPrintFunction name =
  case name of
    "print_i64"  -> Just $ \(SSInt64 i) -> show i
    "print_i32"  -> Just $ \(SSInt32 i) -> show i
    "print_i8"   -> Just $ \(SSInt8  i) -> show i
    "print_i1"   -> Just $ display
    _ -> Nothing

isExpectFunction name =
  case name of
    "expect_i64" -> Just $ \(SSInt64 i) -> show i
    "expect_i32" -> Just $ \(SSInt32 i) -> show i
    "expect_i8"  -> Just $ \(SSInt8  i) -> show i
    "expect_i1"  -> Just $ display
    _ -> Nothing

display :: SSValue -> String
display (SSBool True )  = "true"
display (SSBool False)  = "false"
display (SSByteString bs)= show bs
display (SSInt8  i   )  = show i
display (SSInt16 i   )  = show i
display (SSInt32 i   )  = show i
display (SSInt64 i   )  = show i
display (SSIntWd i   )  = show i
display (SSIntDw i   )  = show i
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

