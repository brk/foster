module Foster.Smallstep (
interpretProg
)
where

import Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Int
import Data.Bits
import Data.Maybe(isJust)
import Data.IORef
import Data.Array

import System.Console.ANSI
import Control.Exception(assert)

import Foster.Base
import Foster.TypeIL
import Foster.ILExpr
import Foster.PatternMatch

-- A term is either a normal-form value,
-- or a non-normal-form expression.
data SSTerm = SSTmExpr  IExpr
            | SSTmValue SSValue
            deriving (Show)

data SSValue = SSBool      Bool
             | SSInt       Integer
             | SSArray     (Array Int Location)
             | SSTuple     [SSValue]
             | SSLocation  Location
             | SSClosure   ILClosure [SSValue]
             | SSCoro      Coro
             deriving (Eq, Show)

instance Eq ILClosure
  where c1 == c2 = (ilClosureProcIdent c1) == (ilClosureProcIdent c2)
                &&  (map tidIdent $ ilClosureCaptures c1)
                 == (map tidIdent $ ilClosureCaptures c2)

instance Eq Coro
  where c1 == c2 = (coroLoc c1) == (coroLoc c2)

-- Expressions are terms that are not in normal form.
data IExpr =
          ITuple [Ident]
        | IVar    Ident
        | IAlloc  Ident
        | IDeref  Ident
        | IStore  Ident Ident
        -- Procedures may be implicitly recursive,
        -- but we need to put a smidgen of effort into
        -- codegen-ing closures so they can be mutually recursive.
        | IClosures    [Ident] [ILClosure] SSTerm
        | ILetVal       Ident   SSTerm     SSTerm
        | IArrayRead    Ident   Ident
        | IArrayPoke    Ident   Ident Ident
        | IAllocArray   Ident
        | IIf           Ident   SSTerm     SSTerm
        | IUntil                SSTerm     SSTerm
        | ICall         Ident  [Ident]
        | ICallPrim     ILPrim [Ident]
        | ICase         Ident  (DecisionTree ILExpr) [(Pattern, SSTerm)]
        | ITyApp        SSTerm TypeIL
        deriving (Show)

data SSProcDef = SSProcDef { ssProcIdent      :: Ident
                           , ssProcVars       :: [Ident]
                           , ssProcBody       :: SSTerm
                           } deriving Show

-- There is a trivial translation from ILExpr to SSTerm...
ssTermOfExpr :: ILExpr -> SSTerm
ssTermOfExpr expr =
  let tr   = ssTermOfExpr in
  let idOf = tidIdent     in
  case expr of
    ILBool b               -> SSTmValue $ SSBool b
    ILInt t i              -> SSTmValue $ SSInt $ litIntValue i
    ILVar v                -> SSTmExpr  $ IVar (idOf v)
    ILTuple vs             -> SSTmExpr  $ ITuple (map idOf vs)
    ILClosures bnds clos e -> SSTmExpr  $ IClosures bnds clos (tr e)
    ILLetVal x b e         -> SSTmExpr  $ ILetVal x (tr b) (tr e)
    ILCall     t b vs      -> SSTmExpr  $ ICall (idOf b) (map idOf vs)
    ILCallPrim t b vs      -> SSTmExpr  $ ICallPrim b (map idOf vs)
    ILIf       t  v b c    -> SSTmExpr  $ IIf (idOf v) (tr b) (tr c)
    ILUntil    t  a b      -> SSTmExpr  $ IUntil    (tr a) (tr b)
    ILArrayRead t a b      -> SSTmExpr  $ IArrayRead (idOf a) (idOf b)
    ILArrayPoke v b i      -> SSTmExpr  $ IArrayPoke (idOf v) (idOf b) (idOf i)
    ILAllocArray ety n     -> SSTmExpr  $ IAllocArray (idOf n)
    ILAlloc a              -> SSTmExpr  $ IAlloc (idOf a)
    ILDeref t a            -> SSTmExpr  $ IDeref (idOf a)
    ILStore t a b          -> SSTmExpr  $ IStore (idOf a) (idOf b)
    ILTyApp t e argty      -> SSTmExpr  $ ITyApp (tr e) argty
    ILCase t a bs dt       -> SSTmExpr  $ ICase (idOf a) dt [(p, tr e) | (p, e) <- bs]

-- ... which lifts in a  straightfoward way to procedure definitions.
ssProcDefFrom pd =
  SSProcDef (ilProcIdent pd) (map tidIdent $ ilProcVars pd)
               (ssTermOfExpr (ilProcBody pd))

errFile gs = (stTmpDir gs) ++ "/istderr.txt"
outFile gs = (stTmpDir gs) ++ "/istdout.txt"

-- To interpret a program, we construct a coroutine for main
-- (no arguments need be passed yet) and step until the program finishes.
interpretProg prog tmpDir = do
  let procmap = buildProcMap prog
  let main = (procmap Map.! (GlobalSymbol "main"))
  let loc  = 0
  let mainCoro = Coro { coroTerm = (ssProcBody main)
                      , coroArgs = []
                      , coroEnv  = env
                      , coroStat = CoroStatusRunning
                      , coroLoc  = loc
                      , coroPrev = Nothing
                      , coroStack = [(env, Prelude.id)]
                      } where env = Map.empty
  let emptyHeap = Heap (nextLocation loc) (Map.singleton loc (SSCoro mainCoro))
  let globalState = MachineState procmap emptyHeap loc tmpDir

  _ <- writeFile (outFile globalState) ""
  _ <- writeFile (errFile globalState) ""

  stepsTaken <- newIORef 0
  val <- interpret stepsTaken globalState
  numSteps <- readIORef stepsTaken
  putStrLn ("Interpreter finished in " ++ show numSteps ++ " steps.")
  return val

interpret stepsTaken gs =
  case (coroStack $ stCoro gs) of
    []         -> do return gs
    otherwise  -> modifyIORef stepsTaken (+1) >>
                  step gs >>= interpret stepsTaken

buildProcMap (ILProgram procdefs _decls _lines) =
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
                deriving (Show, Eq)
type CoroEnv = Map Ident SSValue
data Coro = Coro {
    coroTerm :: SSTerm
  , coroArgs :: [Ident]
  , coroEnv  :: CoroEnv
  , coroStat :: CoroStatus
  , coroLoc  :: Location
  , coroPrev :: Maybe Location
  , coroStack :: [(CoroEnv, SSTerm -> SSTerm)]
} deriving (Show)

instance Show (SSTerm -> SSTerm) where show f = "<coro cont>"

data MachineState = MachineState {
           stProcmap :: Map Ident SSProcDef
        ,  stHeap    :: Heap
        ,  stCoroLoc :: Location
        ,  stTmpDir  :: String
}

stCoro gs = let (SSCoro c) = lookupHeap gs (stCoroLoc gs) in c

step :: MachineState -> IO MachineState
step gs =
  let coro = stCoro gs in
  case coroTerm coro of
    SSTmExpr e -> do --putStrLn ("\n\n" ++ show (coroLoc coro) ++ " ==> " ++ show e)
                     --putStrLn (show (coroLoc coro) ++ " ==> " ++ show (coroStack coro))
                     stepExpr gs e
    SSTmValue _ -> do let (gs2, (env, cont)) = popCoroCont gs
                      return $ withEnv (withTerm gs2 (cont (termOf gs2))) env

coroFromClosure :: MachineState -> ILClosure -> [SSValue] -> ((Location, MachineState), Coro)
coroFromClosure gs (ILClosure id _envid avars) cenv =
  let (Just ssproc) = tryLookupProc gs id in
  let (clo_env:args) = ssProcVars ssproc in
  let ins (id,val) map = Map.insert id val map in
  let env = List.foldr ins Map.empty [(clo_env, SSTuple cenv)] in
  let coro = Coro { coroTerm = ssProcBody ssproc
                  , coroArgs = args
                  , coroEnv  = env
                  , coroStat = CoroStatusDormant
                  , coroLoc  = nextLocation (hpBump (stHeap gs))
                  , coroPrev = Nothing
                  , coroStack = [(env, Prelude.id)]
                  } in
  ((extendHeap gs (SSCoro coro)), coro)

extendHeap :: MachineState -> SSValue -> (Location, MachineState)
extendHeap gs val =
  let heap = stHeap gs in
  let loc = nextLocation (hpBump heap) in
  let hmp = Map.insert loc val (hpMap heap) in
  (loc, gs { stHeap = Heap { hpBump = loc, hpMap = hmp } })

tryLookupProc gs id = Map.lookup id (stProcmap gs)

modifyHeap2 gs l1 v1 l2 v2 =
  let heap = stHeap gs in
  heap { hpMap = Map.insert l2 v2 (Map.insert l1 v1 (hpMap heap)) }

modifyHeapWith gs loc fn =
  let oldheap = stHeap gs in
  let val  = lookupHeap gs loc in
  let heap = oldheap { hpMap = Map.insert loc (fn val) (hpMap oldheap) } in
  gs { stHeap = heap }

lookupHeap :: MachineState -> Location -> SSValue
lookupHeap gs loc =
  case Map.lookup loc (hpMap (stHeap gs)) of
    Just v -> v
    Nothing -> error $ "Unable to find heap cell for location " ++ show loc

termOf gs = coroTerm (stCoro gs)
envOf  gs = coroEnv  (stCoro gs)

beginsWith s p = isJust (stripPrefix p s)

trivialClosureForProc p =
  SSClosure (ILClosure (ssProcIdent p) (error "proc env ident?") []) []

getval :: MachineState -> Ident -> SSValue
getval gs id =
  let env = coroEnv (stCoro gs) in
  case Map.lookup id env of
    Just v -> v
    Nothing -> case tryLookupProc gs id of
      Just p -> trivialClosureForProc p
      Nothing ->
               error $ "Unable to get value for " ++ show id
                      ++ "\n\tenv (unsorted) is " ++ show env

unit = (SSTmValue $ SSTuple [])

withTerm gs e = modifyHeapWith gs (stCoroLoc gs) (\(SSCoro c) -> SSCoro $ c { coroTerm = e })
withEnv  gs e = modifyHeapWith gs (stCoroLoc gs) (\(SSCoro c) -> SSCoro $ c { coroEnv  = e })

callProc gs proc args =
  let names = ssProcVars proc in
  withTerm (extendEnv gs names args) (ssProcBody proc)

pushCoroCont gs delimCont =
  let currStack = coroStack (stCoro gs) in
  modifyHeapWith gs (stCoroLoc gs)
             (\(SSCoro c) -> SSCoro $ c { coroStack = delimCont:currStack })

popCoroCont gs =
  let cont:restStack = coroStack (stCoro gs) in
  (modifyHeapWith gs (stCoroLoc gs)
             (\(SSCoro c) -> SSCoro $ c { coroStack = restStack }), cont)

subStep gs delimCont = step (pushCoroCont gs delimCont)

arraySlotLocation arr n = SSLocation (arr ! n)

stepExpr :: MachineState -> IExpr -> IO MachineState
stepExpr gs expr = do
  let coro = stCoro gs
  case expr of
    IVar i    -> do return $ withTerm gs (SSTmValue $ getval gs i)
    ITuple vs -> do return $ withTerm gs (SSTmValue $ SSTuple (map (getval gs) vs))

    IAlloc i     -> do let (loc, gs') = extendHeap gs (getval gs i)
                       return $ withTerm gs' (SSTmValue $ SSLocation loc)
    IDeref i     -> do case getval gs i of
                         SSLocation z -> return $ withTerm gs  (SSTmValue $ lookupHeap gs z)
                         other -> error $ "cannot deref non-location value " ++ show other
    IStore iv ir -> do let (SSLocation z) = getval gs ir
                       let gs' = modifyHeapWith gs z (\_ -> getval gs iv)
                       return $ withTerm gs' unit

    IClosures bnds clos e  ->
      -- This is not quite right; closures should close over each other!
      let mkSSClosure clo = SSClosure clo (map ((getval gs).tidIdent)
                                              (ilClosureCaptures clo)) in
      let clovals = map mkSSClosure clos in
      let gs' = extendEnv gs bnds clovals in
      return $ withTerm gs' e

    ILetVal x b e          ->
      case b of
        SSTmValue bval -> do return $ withTerm (extendEnv gs [x] [bval]) e
        SSTmExpr _     -> subStep (withTerm gs b) ( envOf gs
                                                  , \t -> SSTmExpr $ ILetVal x t e)

    ICase a _dt [] -> error $ "Smallstep.hs: Pattern match failure when evaluating case expr!"
    ICase a dt ((p, e):bs) ->
       -- First, interpret the pattern list directly
       -- (using recursive calls to discard unmatched branches).
       case matchPattern p (getval gs a) of
         Nothing -> return $ withTerm gs (SSTmExpr $ ICase a dt bs)
         Just varsvals ->
           -- Then check that interpreting the decision tree
           -- gives identical results to direct pattern interpretation.
           case evalDecisionTree dt (getval gs a) of
              Just vv | vv == varsvals ->
                    let (vars, vals) = unzip varsvals in
                    return $ withTerm (extendEnv gs vars vals) e
              elsewise ->
                    error $ "Direct pattern matching disagreed with decision tree!"
                        ++ "\n" ++ show elsewise ++ " vs \n" ++ show varsvals
    ICallPrim prim vs ->
        let args = map (getval gs) vs in
        case prim of
          ILNamedPrim (TypedId _ id) ->
                                   evalNamedPrimitive (identPrefix id) gs args
          ILPrimOp op size -> let name = "primitive_"++op++"_i"++show size in
                                   evalNamedPrimitive name gs args
          ILCoroPrim prim t1 t2 -> evalCoroPrimitive prim gs args

    ICall b vs ->
        let args = map (getval gs) vs in
        case tryLookupProc gs b of
           -- Call of known procedure
           Just proc -> return (callProc gs proc args)
           Nothing ->
             -- Call of closure
             case getval gs b of
               (SSClosure clo env) ->
                 case tryLookupProc gs (ilClosureProcIdent clo) of
                   Just proc -> return (callProc gs proc ((SSTuple env):args))
                   Nothing -> error $ "No proc for closure!"
               v -> error $ "Cannot call non-closure value " ++ display v

    IIf v b c ->
        case getval gs v of
           (SSBool True ) -> return $ withTerm gs b
           (SSBool False) -> return $ withTerm gs c
           otherwise -> error $ "if cond was not a boolean: " ++ show v ++ " => " ++ display (getval gs v)

    IUntil c b ->
      let v = (Ident "!untilval" 0) in
      return $ withTerm gs (SSTmExpr $
        ILetVal v c (SSTmExpr $ IIf v unit
                    (SSTmExpr $ ILetVal (Ident "_" 0) b (SSTmExpr $ IUntil c b))))

    IArrayRead base idxvar ->
        let (SSInt i) = getval gs idxvar in
        let n = fromInteger i in
        case getval gs base of
          SSArray arr  ->  let (SSLocation z) = arraySlotLocation arr n in
                           return $ withTerm gs  (SSTmValue $ lookupHeap gs z)
          _ -> error "Expected base of array read to be array value"

    IArrayPoke iv base idxvar ->
        let (SSInt i) = getval gs idxvar in
        let n = fromInteger i in
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


    ITyApp e@(SSTmExpr _) argty -> subStep (withTerm gs e) (envOf gs, \t -> SSTmExpr $ ITyApp t argty)
    ITyApp (SSTmValue e) argty -> error $ "step iltyapp " ++ show e


evalDecisionTree :: DecisionTree ILExpr -> SSValue -> Maybe [(Ident, SSValue)]
evalDecisionTree (DT_Fail) v = error "evalDecisionTree hit DT_Fail!"
evalDecisionTree (DT_Swap i dt) v = evalDecisionTree dt v
evalDecisionTree (DT_Leaf _ idsoccs) v =
  Just $ map (lookupOcc v) idsoccs
    where lookupOcc v (id, []) = (id, v)
          lookupOcc v (id, all@(occ:occs)) =
            case v of SSTuple vs -> lookupOcc (vs !! occ) (id, occs)
                      otherwise  -> error $ "Pattern match failure: "
                                        ++ "Cannot index non-tuple value: " ++ show v

evalDecisionTree (DT_Switch occ (SwitchCase branches def)) v =
  evalSwitchCase (getOcc occ v) branches def where
    evalSwitchCase w ((ctor, dt):rest) def =
      if ctorMatches w ctor
        then evalDecisionTree dt v
        else evalSwitchCase w rest def
    evalSwitchCase w [] (Just dt) = evalDecisionTree dt v
    evalSwitchCase w [] Nothing = error $ "evalSwitchCase " ++ show w ++ " [] Nothing"

    ctorMatches (SSBool b)  (CtorId "Bool" n) = (b == True  && n == 1)
                                             || (b == False && n == 0)
    ctorMatches (SSInt i) (CtorId "Int32" n) = n == fromInteger i
    ctorMatches (SSInt _) (CtorId _ _) = False
    ctorMatches (SSTuple vs) (CtorId "()" n) = n == (Prelude.length vs)
    ctorMatches (SSTuple _ ) (CtorId _ _) = False
    ctorMatches v ctor = error $ "ctorMatches " ++ show ctor ++ " ==? " ++ show v

    getOcc [] v = v
    getOcc (i:rest) (SSTuple vs) = getOcc rest (vs !! i)
    getOcc occ v = error $ "getOcc " ++ show occ ++ ";; " ++ show v

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

    (SSTuple [], P_Tuple _ []) -> trivialMatchSuccess
    (SSTuple (v1:vals), P_Tuple _ (p1:pats)) -> do
        b1 <- matchPattern p1 v1
        b2 <- mapM (\(p,v) -> matchPattern p v) (zip pats vals)
        return $ b1 ++ (concat b2)
    (_, P_Tuple _ _) -> matchFailure

canSwitchToCoro c =
  case coroStat c of
    CoroStatusInvalid   -> False
    CoroStatusSuspended -> True
    CoroStatusDormant   -> True
    CoroStatusRunning   -> False
    CoroStatusDead      -> False

extendEnv :: MachineState -> [Ident] -> [SSValue] -> MachineState
extendEnv gs names args =
  let ins (id, arg) map = Map.insert id arg map in
  let coro = stCoro gs in
  let env  = coroEnv coro in
  withEnv gs (List.foldr ins env (zip names args))

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
    "primitive_*_i32"       -> Just (modifyInt32sWith (*))
    "primitive_+_i32"       -> Just (modifyInt32sWith (+))
    "primitive_-_i32"       -> Just (modifyInt32sWith (-))
    "primitive_/_i32"       -> Just (modifyInt32sWith div)
    "primitive_bitashr_i32" -> Just (modifyInt32sWith ashr32)
    "primitive_bitshl_i32"  -> Just (modifyInt32sWith shl32)
    "primitive_bitxor_i32"  -> Just (modifyInt32sWith xor)
    "primitive_bitor_i32"   -> Just (modifyInt32sWith (.|.))
    "primitive_bitand_i32"  -> Just (modifyInt32sWith (.&.))
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

evalNamedPrimitive primName gs  [SSInt i1, SSInt i2]
          | isJust (tryGetInt32PrimOp2Int32 primName) =
    let (Just fn) = tryGetInt32PrimOp2Int32 primName in
    return $ withTerm gs (SSTmValue $ SSInt (fn i1 i2))

evalNamedPrimitive primName gs [SSInt i1, SSInt i2]
          | isJust (tryGetInt32PrimOp2Bool primName) =
    let (Just fn) = tryGetInt32PrimOp2Bool primName in
    return $ withTerm gs (SSTmValue $ SSBool (liftInt2 fn i1 i2))

evalNamedPrimitive "primitive_negate_i32" gs [SSInt i] =
  return $ withTerm gs (SSTmValue $ SSInt (negate i))

evalNamedPrimitive "primitive_bitnot_i1" gs [SSBool b] =
  return $ withTerm gs (SSTmValue $ SSBool (not b))

evalNamedPrimitive "primitive_bitnot_i32" gs [SSInt i] =
  return $ withTerm gs (SSTmValue $ SSInt ((modifyInt32With complement) i))

evalNamedPrimitive prim gs args = error $ "evalNamedPrimitive " ++ show prim
                                 ++ " not yet defined"


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
        return $ extendEnv gs2 (coroArgs newcoro) [arg]

evalCoroPrimitive CoroInvoke gs _ = error $ "Wrong arguments to coro_invoke"
--
--
-- {- "Rule 4 describes the action of creating a coroutine.
--     It creates a new label to represent the coroutine and extends the
--     store with a mapping from this label to the coroutine main function." -}
evalCoroPrimitive CoroCreate gs [SSClosure clo env] =
  let ((loc, gs2), coro) = coroFromClosure gs clo env in
  return $ withTerm gs2 (SSTmValue $ SSLocation loc)

evalCoroPrimitive CoroCreate gs _ = error $ "Wrong arguments to coro_create"


-- -- The current coro is returned to the heap, marked suspended, with no previous coro.
-- -- The previous coro becomes the new coro, with status running.
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
evalCoroPrimitive CoroYield gs _ = error $ "Wrong arguments to coro_yield"

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
    otherwise    -> False

isExpectFunction name =
  case name of
    "expect_i64" -> True
    "expect_i32" -> True
    "expect_i1"  -> True
    otherwise    -> False

view :: SSTerm -> String
view (SSTmValue v) = display v
view (SSTmExpr (ILetVal x t e)) = "let " ++ show x ++ " = " ++ view t ++ " in\n" ++ view e
view (SSTmExpr (IIf v a b)) = "if " ++ show v ++ " then { " ++ view a ++ " } else { " ++ view b ++ " }"
view (SSTmExpr (ICall b vs)) = show b ++ show vs
view (SSTmExpr e) = show e

display :: SSValue -> String
display (SSBool True )  = "true"
display (SSBool False)  = "false"
display (SSInt i     )  = show i
display (SSArray a   )  = show a
display (SSTuple vals)  = "(" ++ joinWith ", " (map display vals) ++ ")"
display (SSLocation z)  = "<location " ++ show z ++ ">"
display (SSClosure _ _) = "<closure>"
display (SSCoro    _  ) = "<coro>"

