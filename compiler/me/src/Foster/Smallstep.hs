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

import Control.Exception(assert)
import System.Console.ANSI

import Foster.Base
import Foster.TypeAST
import Foster.ILExpr
import Foster.PatternMatch

-- A term is either a normal-form value,
-- or a non-normal-form expression.
data SSTerm = SSTmExpr  IExpr
            | SSTmValue SSValue
            deriving (Show)

data SSValue = SSBool      Bool
             | SSInt       Integer
             | SSPrimitive SSPrimId
             | SSArray     (Array Int Location)
             | SSTuple     [SSValue]
             | SSLocation  Location
             | SSClosure   ILClosure [SSValue]
             | SSCoro      Coro
             deriving (Eq, Show)

instance Eq ILClosure
  where c1 == c2 = (ilClosureProcIdent c1) == (ilClosureProcIdent c2)
                &&  (map avarIdent $ ilClosureCaptures c1)
                 == (map avarIdent $ ilClosureCaptures c2)

instance Eq Coro
  where c1 == c2 = (coroLoc c1) == (coroLoc c2)

data SSPrimId = PrimCoroInvoke | PrimCoroCreate | PrimCoroYield
              | PrimNamed String
             deriving (Eq, Show)

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
        | ISubscript    Ident   Ident
        | IIf           Ident   SSTerm     SSTerm
        | IUntil                SSTerm     SSTerm
        | ICall         Ident  [Ident]
        | ICase         Ident  (DecisionTree ILExpr) [(Pattern, SSTerm)]
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
    ILInt t i              -> SSTmValue $ SSInt $ litIntValue i
    ILVar a                -> SSTmExpr  $ IVar (avarIdent a)
    ILTuple vs             -> SSTmExpr  $ ITuple (map avarIdent vs)
    ILClosures bnds clos e -> SSTmExpr  $ IClosures bnds clos (tr e)
    ILLetVal x b e         -> SSTmExpr  $ ILetVal x (tr b) (tr e)
    ILCall    t b vs       -> SSTmExpr  $ ICall (avarIdent b) (map avarIdent vs)
    ILIf      t  v b c     -> SSTmExpr  $ IIf (avarIdent v) (tr b) (tr c)
    ILUntil   t  a b       -> SSTmExpr  $ IUntil            (tr a) (tr b)
    ILSubscript t a b      -> SSTmExpr  $ ISubscript (avarIdent a) (avarIdent b)
    ILAlloc a              -> SSTmExpr  $ IAlloc (avarIdent a)
    ILDeref t a            -> SSTmExpr  $ IDeref (avarIdent a)
    ILStore t a b          -> SSTmExpr  $ IStore (avarIdent a) (avarIdent b)
    ILTyApp t e argty      -> SSTmExpr  $ ITyApp (tr e) argty
    ILCase t a bs dt       -> SSTmExpr  $ ICase (avarIdent a) dt [(p, tr e) | (p, e) <- bs]

-- ... which lifts in a  straightfoward way to procedure definitions.
ssProcDefFrom pd =
  SSProcDef (ilProcIdent pd) (ilProcVars pd)
               (ssTermOfExpr (ilProcBody pd))

errFile gs = (stTmpDir gs) ++ "/istderr.txt"
outFile gs = (stTmpDir gs) ++ "/istdout.txt"

-- To interpret a program, we construct a coroutine for main
-- (no arguments need be passed yet) and step until the program finishes.
interpretProg prog tmpDir = do
  let procmap = buildProcMap prog
  let main = (procmap Map.! (Ident "main" irrelevantIdentNum))
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
  , coroArgs :: [AnnVar]
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
coroFromClosure gs (ILClosure id avars) cenv =
  let (Just ssproc) = tryLookupProc gs id in
  let ins (id,val) map = Map.insert id val map in
  let env = List.foldr ins Map.empty (zip (map avarIdent avars) cenv) in
  let coro = Coro { coroTerm = ssProcBody ssproc
                  , coroArgs = ssProcVars ssproc
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

tryGetVal :: MachineState -> Ident -> Maybe SSValue
tryGetVal gs id =
  let mv = Map.lookup id (coroEnv (stCoro gs)) in
  if isJust mv then mv else
    case identPrefix id of
       s | s `beginsWith` "coro_invoke" -> Just $ SSPrimitive PrimCoroInvoke
       s | s `beginsWith` "coro_create" -> Just $ SSPrimitive PrimCoroCreate
       s | s `beginsWith` "coro_yield"  -> Just $ SSPrimitive PrimCoroYield
       s | isPrintFunction  s -> Just $ SSPrimitive (PrimNamed "print")
       s | isExpectFunction s -> Just $ SSPrimitive (PrimNamed "expect")
       otherwise -> Nothing

getval :: MachineState -> Ident -> SSValue
getval gs id =
  case tryGetVal gs id of
    Just e -> e
    Nothing -> error $ "Unable to look up local variable " ++ show id

unit = (SSTmValue $ SSTuple [])

withTerm gs e = modifyHeapWith gs (stCoroLoc gs) (\(SSCoro c) -> SSCoro $ c { coroTerm = e })
withEnv  gs e = modifyHeapWith gs (stCoroLoc gs) (\(SSCoro c) -> SSCoro $ c { coroEnv  = e })

callProc gs proc args =
  let names = map avarIdent (ssProcVars proc) in
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

arrayIndex arr n = SSLocation (arr ! n)

stepExpr :: MachineState -> IExpr -> IO MachineState
stepExpr gs expr = do
  let coro = stCoro gs
  case expr of
    IVar i    -> do return $ withTerm gs (SSTmValue $ getval gs i)
    ITuple vs -> do return $ withTerm gs (SSTmValue $ SSTuple (map (getval gs) vs))

    IAlloc i     -> do let (loc, gs') = extendHeap gs (getval gs i)
                       return $ withTerm gs' (SSTmValue $ SSLocation loc)
    IDeref i     -> do let (SSLocation z) = getval gs i
                       return $ withTerm gs  (SSTmValue $ lookupHeap gs z)
    IStore iv ir -> do let (SSLocation z) = getval gs ir
                       let gs' = modifyHeapWith gs z (\_ -> getval gs iv)
                       return $ withTerm gs' unit

    IClosures bnds clos e  ->
      -- This is not quite right; closures should close over each other!
      let mkSSClosure clo = SSClosure clo (map ((getval gs).avarIdent)
                                              (ilClosureCaptures clo)) in
      let clovals = map mkSSClosure clos in
      let gs' = extendEnv gs bnds clovals in
      return $ withTerm gs' e

    ILetVal x b e          ->
      case b of
        SSTmValue bval -> do return $ withTerm (extendEnv gs [x] [bval]) e
        SSTmExpr _     -> subStep (withTerm gs b) ( envOf gs
                                                  , \t -> SSTmExpr $ ILetVal x t e)

    ICase a _dt [] -> error $ "Pattern match failure!"
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
    ICall b vs ->
        let args = map (getval gs) vs in
        case tryLookupProc gs b of
           -- Call of known procedure
           Just proc -> return (callProc gs proc args)
           Nothing ->
             -- Call of closure or primitive
             case tryGetVal gs b of
               Just (SSClosure clo env) ->
                 case tryLookupProc gs (ilClosureProcIdent clo) of
                   Just proc -> return (callProc gs proc ((SSTuple env):args))
                   Nothing -> error $ "No proc for closure!"
               Just (SSPrimitive p) -> evalPrimitive p gs args
               Just v -> error $ "Cannot call non-closure value " ++ display v
               Nothing -> tryEvalPrimitive gs (identPrefix b) args

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

    ISubscript v idxvar ->
        let (SSInt i) = getval gs idxvar in
        let n = fromInteger i in
        case getval gs v of
          SSArray arr  -> return $ withTerm gs (SSTmValue (arrayIndex arr n))
          _ -> error "Expected base of subscript to be array value"

    ITyApp e@(SSTmExpr _) argty -> subStep (withTerm gs e) (envOf gs, \t -> SSTmExpr $ ITyApp t argty)
    ITyApp e@(SSTmValue (SSPrimitive PrimCoroInvoke)) _ -> return $ withTerm gs e
    ITyApp e@(SSTmValue (SSPrimitive PrimCoroCreate)) _ -> return $ withTerm gs e
    ITyApp e@(SSTmValue (SSPrimitive PrimCoroYield )) _ -> return $ withTerm gs e
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

liftInt :: (Integral a) => (a -> a -> b) ->
          Integer -> Integer -> b
liftInt f i1 i2 =
  let v1 = fromInteger i1 in
  let v2 = fromInteger i2 in
  f v1 v2

modifyInt32With :: (Int32 -> Int32 -> Int32)
       -> Integer -> Integer -> Integer
modifyInt32With f i1 i2 =
  fromIntegral (liftInt f i1 i2)

ashr32   a b = shiftR a (fromIntegral b)
shl32    a b = shiftL a (fromIntegral b)

tryGetInt32PrimOp2Int32 :: String -> Maybe (Integer -> Integer -> Integer)
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

--------------------------------------------------------------------

evalPrimitive :: SSPrimId -> MachineState -> [SSValue] -> IO MachineState
evalPrimitive PrimCoroInvoke gs [(SSLocation targetloc),arg] =
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
       return $ extendEnv gs2 (tail $ map avarIdent $ coroArgs newcoro) [arg]

evalPrimitive PrimCoroInvoke gs _ = error $ "Wrong arguments to coro_invoke"


{- "Rule 4 describes the action of creating a coroutine.
    It creates a new label to represent the coroutine and extends the
    store with a mapping from this label to the coroutine main function." -}
evalPrimitive PrimCoroCreate gs [SSClosure clo env] =
  let ((loc, gs2), coro) = coroFromClosure gs clo env in
  return $ withTerm gs2 (SSTmValue $ SSLocation loc)

evalPrimitive PrimCoroCreate gs _ = error $ "Wrong arguments to coro_create"


-- The current coro is returned to the heap, marked suspended, with no previous coro.
-- The previous coro becomes the new coro, with status running.
evalPrimitive PrimCoroYield gs [arg] =
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
evalPrimitive PrimCoroYield gs _ = error $ "Wrong arguments to coro_yield"


evalPrimitive (PrimNamed "print") gs [val] =
      do printString gs (display val)
         return $ withTerm gs (SSTmValue val)

evalPrimitive (PrimNamed "expect") gs [val] =
      do expectString gs (display val)
         return $ withTerm gs (SSTmValue val)

evalPrimitive (PrimNamed p) gs args =
  error $ "step evalPrimitive named " ++ p ++ " with " ++ show (map display args)

--------------------------------------------------------------------

printString  gs s = do
  runOutput (outCSLn Blue s)
  appendFile (errFile gs) (s ++ "\n")

expectString gs s = do
  runOutput (outCSLn Green s)
  appendFile (outFile gs) (s ++ "\n")

--------------------------------------------------------------------

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
  return $ withTerm gs (SSTmValue $ SSInt (negate i))

tryEvalPrimitive gs "primitive_bitnot_i1" [SSBool b] =
  return $ withTerm gs (SSTmValue $ SSBool (not b))

tryEvalPrimitive gs "force_gc_for_debugging_purposes" _args =
  return $ withTerm gs unit

tryEvalPrimitive gs "opaquely_i32" [val] =
  return $ withTerm gs (SSTmValue val)

tryEvalPrimitive gs "expect_i32b" [val@(SSInt i)] =
      do expectString gs (showBits32 i)
         return $ withTerm gs unit

tryEvalPrimitive gs "print_i32b" [val@(SSInt i)] =
      do printString gs (showBits32 i)
         return $ withTerm gs unit

tryEvalPrimitive gs0 "allocDArray32" [SSInt i] =
      do (inits, gs) <- mapFoldM [0.. i - 1] gs0 (\n -> \gs1 ->
                                let (loc, gs) = extendHeap gs1 (SSInt 0) in
                                return ([(fromInteger n, loc)], gs)
                        )
         return $ withTerm gs (SSTmValue $ SSArray $
                        array (0, fromInteger $ i - 1) inits)

tryEvalPrimitive gs primName args =
      error ("step ilcall 'prim' " ++ show primName ++ " with args: " ++ show args)

--------------------------------------------------------------------

mapFoldM :: (Monad m) => [a] -> b ->
                         (a -> b -> m ([c], b))
                                 -> m ([c], b)
mapFoldM []  b  f    = return ([], b)
mapFoldM [a] b1 f    = f a b1
mapFoldM (a:as) b1 f = do
    (cs1, b2) <- f a b1
    (cs2, b3) <- mapFoldM as b2 f
    return (cs1 ++ cs2, b3)

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
display (SSPrimitive p) = "<" ++ show p ++ ">"
display (SSInt i     )  = show i
display (SSArray a   )  = show a
display (SSTuple vals)  = "(" ++ joinWith ", " (map display vals) ++ ")"
display (SSLocation z)  = "<location " ++ show z ++ ">"
display (SSClosure _ _) = "<closure>"
display (SSCoro    _  ) = "<coro>"

