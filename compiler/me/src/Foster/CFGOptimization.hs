{-# LANGUAGE GADTs, ScopedTypeVariables, PatternGuards, NoMonoLocalBinds #-}
-----------------------------------------------------------------------------
-- Copyright (c) 2012 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.CFGOptimization (optimizeCFGs, collectMayGCConstraints) where

import Foster.Base
import Foster.MonoType
import Foster.Letable(Letable(..), letableSize, canGC, willNotGCGlobal)
import Foster.Config
import Foster.CFG

import Compiler.Hoopl
import Text.PrettyPrint.ANSI.Leijen
import qualified Text.PrettyPrint.Boxes as Boxes

import qualified Data.Text as T
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe(fromJust, isJust)
import Data.List(nubBy, last)
import Control.Monad.State
import Data.IORef
import Prelude hiding (id, last)

optimizeCFGs :: CFBody -> IORef [Ident] -> Compiled CFBody
optimizeCFGs c@(CFB_Call {}) _ = return c
optimizeCFGs (CFB_LetFuns ids cffns cfbody) r = do
          cffns'  <- mapM (optimizeCFFn r) cffns
          cfbody' <- optimizeCFGs cfbody r
          return $ CFB_LetFuns ids cffns' cfbody'

optimizeCFFn :: IORef [Ident] -> CFFn -> Compiled CFFn
optimizeCFFn r fn = do
  liftIO $ modIORef' r (fnIdent fn :)
  wantedFns <- gets ccDumpFns
  uref      <- gets ccUniqRef

  let optimizations = [ elimContInBBG
                      , runCensusRewrites' , elimContInBBG
                     -- ,runLiveness
                      ]

  -- Depth-first optimization: first optimize every sub-function,
  -- then work on the function body itself.
  bbg  <- mapFunctions (optimizeCFFn r) (fnBody fn)
  bbgs <- liftIO $ scanlM (\bbg opt -> opt uref bbg) bbg optimizations

  let catboxes bbgs = Boxes.hsep 1 Boxes.left $ map (boxify . measure . annotate) $
                        (nubBy sndEq $ zip [1..] $ map (show . pretty) bbgs)
       where sndEq (_, a) (_, b) = a == b
             annotate (n, s) = s ++ "\n        (stage " ++ show n ++ ")"

  when (fn `isWanted` wantedFns) $ liftIO $ do
      putStrLn "BEFORE/AFTER"
      -- Discards duplicates before annotating
      Boxes.printBox $ catboxes bbgs
      putStrLn ""

  let bbg' = last bbgs

  when (fn `isWanted` wantedFns) $ liftIO $ do
      let jumpTo bbg = case bbgEntry bbg of (bid, _) -> ILast $ CFCont bid undefined
      Boxes.printBox $ catboxes $ map blockGraph $
                         preorder_dfs $ mkLast (jumpTo bbg') |*><*| bbgBody bbg'

  ccRecordCFGSizes (show (tidIdent $ fnVar fn), cfgSize bbg, cfgSize bbg' )

  return $ fn { fnBody = bbg' }
    where
        isWanted fn wanted = -- Could be fancier and use regexp matching.
           T.unpack (identPrefix (fnIdent fn)) `elem` wanted

        measure :: String -> Boxes.Box
        measure s = Boxes.vcat Boxes.left (map Boxes.text $ lines s)

        boxify :: Boxes.Box -> Boxes.Box
        boxify b = v Boxes.<> (h Boxes.// b Boxes.// h) Boxes.<> v
                     where v = Boxes.vcat Boxes.left (take (Boxes.rows b + 2) (repeat (Boxes.char '|')))
                           h = Boxes.text $          (take (Boxes.cols b    ) (repeat '-'))

mapFunctions :: forall m. MonadIO m => (CFFn -> m CFFn) -> BasicBlockGraph -> m BasicBlockGraph
mapFunctions optFn bbg = do
  body' <- rebuildGraphM (fst $ bbgEntry bbg) (bbgBody bbg) recurse
  return bbg { bbgBody = body' }
    where recurse :: forall e x. Insn e x -> m (Graph Insn e x)
          recurse insn@(ILabel  {}) = return (mkFirst  insn)
          recurse insn@(ILetVal {}) = return (mkMiddle insn)
          recurse insn@(ILast   {}) = return (mkLast   insn)

          recurse (ILetFuns ids fns) = do
            fns' <- mapM optFn fns
            return (mkMiddle (ILetFuns ids fns' ))

-- |||||||||||||||||||||||||| CFG Analysis ||||||||||||||||||||||{{{
instance Pretty (Set.Set HowUsed) where pretty s = string (show s)

-- |||||||||||||||||||| Cont-Cont Elimination |||||||||||||||||||{{{
--data Renamer   = Renamer BlockId (Maybe ([MoVar] -> [MoVar]))
--instance Show Renamer where show (Renamer bid _) = "(Renamer " ++ show bid ++ ")"

data CFGTrivia = CFGTrivia { cfgTrivEndsCont   :: Maybe (BlockId, [MoVar])
                           , cfgTrivEquivs     :: Map.Map BlockId BlockId
                           } deriving Show

elimContInBBG :: IORef Uniq -> BasicBlockGraph -> IO BasicBlockGraph
elimContInBBG uref bbg = runWithUniqAndFuel uref infiniteFuel (elimContInBBG' bbg)
  where elimContInBBG' :: BasicBlockGraph -> M BasicBlockGraph
        elimContInBBG' bbg = do
         (bb', _, _) <- analyzeAndRewriteBwd bwd (JustC [bbgEntry bbg])
                                                        (bbgBody  bbg)
                                                        mapEmpty
         return $ bbg { bbgBody = bb' }

        -- _bwd = debugBwdTransfers trace showing (\_ _ -> True) bwd
        bwd = BwdPass { bp_lattice  = contEquivLattice
                      , bp_transfer = contContFind
                      , bp_rewrite  = contContElim
                      }

        contEquivLattice :: DataflowLattice CFGTrivia
        contEquivLattice = DataflowLattice
                          { fact_name = "Continued continuations"
                          , fact_bot  = CFGTrivia Nothing Map.empty
                          , fact_join = fj
                          }
                            where fj _ (OldFact old) (NewFact new) = (ch, j)
                                    where
                                      j = (CFGTrivia Nothing m)
                                      o = cfgTrivEquivs old
                                      m = Map.union o (cfgTrivEquivs new)
                                      ch = changeIf (Map.size m > Map.size o)

        contContFind :: BwdTransfer Insn CFGTrivia
        contContFind = mkBTransfer go
          where
            go :: Insn e x -> Fact x CFGTrivia -> CFGTrivia
            go (ILabel   (bid, vs)   ) s =
                 let s' = s { cfgTrivEndsCont = Nothing } in
                 case {-trace ("F("++show bid++")") $-} cfgTrivEndsCont s of
                   Just (otherid, ovs) ->
                       if bid /= otherid && vs == ovs
                         then -- let o = Renamer otherid (renamerFunc vs ovs) in
                              s' { cfgTrivEquivs = Map.insert bid otherid (cfgTrivEquivs s') }
                         else s'
                   Nothing -> s'
            go (ILetVal  {}         ) s = s { cfgTrivEndsCont = Nothing }
            go (ILetFuns _ids _fns  ) s = s { cfgTrivEndsCont = Nothing }
            go node@(ILast    cf    ) fdb =
              let s = joinFacts contEquivLattice (error "fake label") (successorFacts' node fdb) in
              --let s = {-trace ("fact base F: " ++ showFactBase fdb) $-}
              --          joinOutFacts' contEquivLattice node fdb in
              case cf of
                    (CFCont bid vs) -> s { cfgTrivEndsCont = Just (bid, vs) }
                    (CFCall {})     -> s { cfgTrivEndsCont = Nothing }
                    (CFCase {})     -> s { cfgTrivEndsCont = Nothing }

            -- Example to illuminate what these variable names mean:
            --     k []    = j [a,b]      ==> k []    = c [b,z,a]
            --     j [x,y] = c [y,z,x]    ==> ...
            -- bid/vs is j/[x,y], otherid/ovs is c/[y,z,x], & [a,b] (will b) avs
            ----renamerFunc vs ovs = if vs == ovs then Nothing
            ----                       else Just (\avs -> applySubst
            ----                                         (buildSubst vs avs) ovs)
            ----buildSubst oldvars newvars = Map.fromList (zip oldvars newvars)
            ----applySubst subst   tgtvars = map (\v -> Map.findWithDefault v v subst) tgtvars
            ----
            ----fact :: FactBase CFGTrivia -> Label -> CFGTrivia
            ----fact f l = fromMaybe (fact_bot contEquivLattice) $ lookupFact l f

            successorFacts' :: NonLocal n => n O C -> FactBase f -> [f]
            successorFacts' n fb = [ fromJust f | id <- successors n,
                                            let f = lookupFact id fb, isJust f ]

        contContElim :: FuelMonad m => BwdRewrite m Insn CFGTrivia
        contContElim = mkBRewrite d
          where
            d :: FuelMonad m => Insn e x -> Fact x CFGTrivia -> m (Maybe (Graph Insn e x))
            d (ILast (CFCont bid     vs)) triv = return $ rw bid triv
                            --(\(Renamer newbid mf) -> CFCont newbid (r mf vs))
                                            (\newbid -> CFCont newbid vs)
            --d (ILast (CFCall bid t v vs)) triv = return $ rw bid triv
            --                --(\(Renamer newbid mf) -> case mf of Nothing -> CFCall newbid t v vs
            --                --                                    Just _  -> CFCall    bid t v vs)
            d _ _ = return Nothing

            -- r Nothing  vs =   vs
            -- r (Just f) vs = f vs

            rw :: BlockId -> FactBase CFGTrivia -> (BlockId -> CFLast) -> Maybe (Graph Insn O C)
            rw bid@(_,lab) fdb k =
              case lookupFact lab fdb of
                Nothing -> Nothing
                Just triv ->
                  case Map.lookup bid (cfgTrivEquivs triv) of
                    Just otherid -> Just $ mkLast (ILast $ k otherid)
                    Nothing      -> Nothing

-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

-- |||||||||||||||||||| Census-based Rewrites |||||||||||||||||||{{{
data HowUsed = UnknownCall BlockId
             | KnownCall   BlockId {- provided cont; -}
                           (RecStatus,BlockId) {- of known fn entry point -}
             | TailRecursion
             | UsedFirstClass | UsedSecondClass -- as cont arg
                 deriving (Eq, Ord, Show)

type CenFuns = Map.Map Ident CFFn

-- Build a mapping from the (local, not global) idents to the
-- locally-defined (and thus known) functions they are bound to.
getCensusFns :: BasicBlockGraph -> CenFuns
getCensusFns bbg = gobbg bbg Map.empty
  where
    gobbg bbg m = foldGraphNodes go (bbgBody bbg) m

    go :: Insn e x -> CenFuns -> CenFuns
    go (ILetFuns ids fns    ) m = foldr gobbg m' (map fnBody fns)
                                   where m' = Map.union m $ Map.fromList (zip ids fns)
    go _                      m = m

type Census = Map.Map Ident (Set.Set HowUsed)

getCensus :: BasicBlockGraph -> Census
getCensus bbg = let cf = getCensusFns bbg in
                getCensusForFn cf bbg Map.empty
  where
    addUsed c lst = Map.unionWith Set.union c
                                (Map.fromList [(tidIdent v, Set.singleton u)
                                              | (v, u) <- lst])

    getCensusForFn cf bbg m = foldGraphNodes (go cf) (bbgBody bbg) m

    go :: CenFuns -> Insn e x -> Census -> Census
    go _  (ILabel   _bentry    ) m = m
    go _  (ILetVal  _id letable) m = censusLetable letable m
    go cf (ILetFuns _ids fns   ) m = foldr (getCensusForFn cf) m (map fnBody fns)
    go cf (ILast    cflast     ) m =
      case cflast of
            (CFCont _bid    vs) -> addUsed m [(v, UsedSecondClass) | v <- vs]
            (CFCall bid _ v vs) ->
                 case Map.lookup (tidIdent v) cf of
                   Nothing -> addUsed m $ (v, UnknownCall bid):
                                         [(v, UsedFirstClass) | v <- vs]

                   -- This identifies only self-recursive tail calls;
                   -- it does not distinguish between (tail calls to other
                   -- functions within the same recursive SCC) or (tail calls to
                   -- known functions defined outside of the current fn's SCC).
                   Just fn | bid == bbgRetK (fnBody fn)
                           -> addUsed m $ (v, TailRecursion):
                                         [(v, UsedFirstClass) | v <- vs]

                   Just fn -> addUsed m $ (v, (KnownCall bid (fnEntryId fn))):
                                         [(v, UsedFirstClass) | v <- vs]
            (CFCase v _pats)    -> addUsed m [(v, UsedSecondClass)]

    fnEntryId fn = (fnIsRec fn, blockId $ bbgEntry (fnBody fn))

    censusLetable letable m =
      case letable of
        ILLiteral      {}        -> m
        ILKillProcess  {}        -> m
        ILOccurrence   {}        -> m
        ILBitcast      _ v       -> addUsed m [(v, UsedFirstClass)] -- conservatively :(
        ILTuple  _kind vs _asrc  -> addUsed m [(v, UsedFirstClass) | v <- vs]
        ILCallPrim     _ _ vs    -> addUsed m [(v, UsedFirstClass) | v <- vs]
        ILAppCtor      _ _ vs    -> addUsed m [(v, UsedFirstClass) | v <- vs]
        ILAlloc        v _rgn    -> addUsed m [(v, UsedFirstClass)]
        ILDeref        _ v       -> addUsed m [(v, UsedFirstClass)]
        ILStore        v1 v2     -> addUsed m [(v1, UsedFirstClass), (v2, UsedFirstClass)]
        ILObjectCopy   v1 _id    -> addUsed m [(v1, UsedFirstClass)]
        ILAllocArray    _ v _ _  -> addUsed m [(v, UsedFirstClass)]
        ILArrayRead  _t (ArrayIndex v1 v2 _rng _s) -> addUsed m [(v1, UsedFirstClass), (v2, UsedFirstClass)]
        ILArrayPoke  (ArrayIndex v1 v2 _rng _s) v3 -> addUsed m [(v1, UsedFirstClass), (v2, UsedFirstClass),
                                                                 (v3, UsedFirstClass)]
        ILArrayLit _t arr vals -> addUsed m ([(arr, UsedFirstClass)] ++ [(v, UsedFirstClass) | Right v <- vals])
        ILAllocate {}            -> m -- Might have been introduced by KNLetRec.
        ILCall         _ v _vs   -> error $ "census encountered non-tail ILCall of " ++ show v

type EquivalentBlockIds = Map.Map BlockId BlockId

collectEquivalentBlockIds :: BasicBlockGraph -> EquivalentBlockIds
collectEquivalentBlockIds bbg = execState (mapM go blocks) Map.empty
  where
    blocks = preorder_dfs (mkLast (branchTo (fst $ bbgEntry bbg)) |*><*| bbgBody bbg)

    go block = let (h, b, t) = blockSplit block in
               case (h, blockToList b, t) of
                 (ILabel (eb, evars), [], ILast (CFCont cb cvars))
                    | evars == cvars -> modify (Map.insert eb cb)
                 (_, _, _) -> return ()

data ContInfo = NoConts
              | OneCont BlockId BlockId
              | ManyConts
              deriving (Show)

runCensusRewrites' :: IORef Uniq -> BasicBlockGraph -> IO BasicBlockGraph
runCensusRewrites' uref bbg = do
     runWithUniqAndFuel uref infiniteFuel (go (getCensus bbg) bbg)
  where
        equivBlockIds = collectEquivalentBlockIds bbg

        sharedTrivialCont [] = Nothing
        sharedTrivialCont (first:others) =
          case first of
            KnownCall bid0 (_, fn_ent) ->
                let
                    try bids [] = bids
                    try bids ((KnownCall bid' (_, fn_ent')):others)
                        | fn_ent == fn_ent'
                        = try (bid' : bids) others
                    try _ _ = []

                    nextbids = [Map.lookup bid equivBlockIds
                               | bid <- try [bid0] others] in
                case Set.toList $ Set.fromList nextbids of
                    [Just commonbid] -> Just (OneCont commonbid fn_ent)
                    _ -> Nothing
            _ -> Nothing

        go :: Census -> BasicBlockGraph -> M BasicBlockGraph
        go ci bbg = do
          let (bid,_) = bbgEntry bbg
          bb' <- rebuildGraphM bid (bbgBody bbg) (transform ci)
          return $ bbg { bbgBody = bb' }

        getKnownCall :: Census -> Ident -> ContInfo
        getKnownCall ci id =
          case fmap Set.toList (Map.lookup id ci) of
            -- Simple case: non-recursive function, with only one return cont.
            Just [KnownCall bid (NotRec, fn_ent)] -> OneCont bid fn_ent

            -- A recursive continuation must have one return cont provided
            -- from the outside, and only tail recursive calls from inside.
            -- (does not handle non-trivial SCCs of tail recursive functions...)
            Just [TailRecursion, KnownCall bid (_, fn_ent)] -> OneCont bid fn_ent
            Just [KnownCall bid (_, fn_ent), TailRecursion] -> OneCont bid fn_ent

            Just others | Just result <- sharedTrivialCont others -> result
            Just _others -> --trace ("getKnownCall returning ManyConts for " ++ show id ++ " due to " ++ show _others)
                            ManyConts
            Nothing -> NoConts

        transformFn ci fn = do
          bbg' <- go ci (fnBody fn)
          return $ fn { fnBody = bbg' }

        transform :: Census -> Insn e x -> M (Graph Insn e x)
        transform ci = rw
         where
          rw :: Insn e x -> M (Graph Insn e x)
          rw n = case n of
             ILabel   {} -> do return $ mkFirst n
             -- TODO may need to re-position contified functions in a smaller
             --      scope. For example:
             --                    let f1 = { ... };
             --                        f2 = { ... f1 ! ... }; in f2 ! end
             -- cannot be transformed to
             --                letcont j1 = { ... };
             --                letfun  f2 = { ... j1 ! ... }; in f2 ! end
             -- because f2 can't call a continuation that belongs to its parent.
             ILetFuns ids rawfns -> do
               fns <- mapM (transformFn ci) rawfns
               let (contifiables, nonconts) = splitContifiable (zip ids fns) ci
               let nonconts_ag = aGraphOfGraph $ mkMiddle $ uncurry ILetFuns $ unzip nonconts

               fngs <- mapM (\(_, fn, bid) -> aGraphOfFn ci fn bid) contifiables
               graphOfAGraph (foldr (flip addBlocks) nonconts_ag fngs)

             ILetVal  _id _letable -> return $ mkMiddle n
             ILast cflast -> return $ mkLast $ ILast (contifyCalls ci cflast)

        splitContifiable :: [(Ident, CFFn)] -> Census -> ([(Ident, CFFn, BlockId)],
                                                          [(Ident, CFFn)])
        splitContifiable idsfns ci =
          let idsfns' = map (\(id, fn) -> (id, fn, getKnownCall ci id)) idsfns in
          let contifiables = [(id, fn, bid) | (id, fn, OneCont bid _fn_ent) <- idsfns' ] in
          let nonconts     = [(id, fn)      | (id, fn, ManyConts)           <- idsfns' ] in
          -- Silently drop dead functions...
          (contifiables, nonconts)

        contifyCalls :: Census -> CFLast -> CFLast
        contifyCalls ci (CFCall _k _t v vs)
          | OneCont _bid fn_ent <- getKnownCall ci (tidIdent v) =
                     -- Replace (v k vs) with (j vs) if all calls to v had eq k.
                     CFCont (contified fn_ent) vs
        contifyCalls _ci other = other

        contified ("postalloca", l) = ("contified_postalloca", l)
        contified entry             = entry

        -- Rewrite the function's body so that returns become jumps to the
        -- continuation that all callers had provided.
        -- This computes  K[k0/k]  from the paper Comp w/ Continuations, Cont'd.
        aGraphOfFn :: Monad m =>
                      Census -> Fn r BasicBlockGraph ty -> BlockId -> m (AGraph Insn C C)
        aGraphOfFn ci fn retbid = do
          let ret bid = if bid == bbgRetK (fnBody fn) then retbid else bid
          let rw :: Insn e x -> Insn e x
              rw (ILabel (entry,vs)) = ILabel (contified entry, vs)
              rw (ILast cflast) =
                ILast $ case (contifyCalls ci cflast) of
                  CFCont bid vs     -> CFCont (ret bid) vs
                  CFCall bid t v vs -> CFCall (ret bid) t v vs
                  CFCase v arms     -> CFCase v (map (\(CaseArm p e g b r) -> CaseArm p (ret e) (fmap ret g) b r) arms)
              rw insn = insn
          let g_old = bbgBody $ fnBody fn
          let g_new = mapGraph rw g_old
          return $ aGraphOfGraph g_new
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

-- |||||||||||||||||||| Liveness ||||||||||||||||||||||||||||||||{{{
{-
type Live = Set.Set Ident

liveLattice :: DataflowLattice Live
liveLattice = DataflowLattice
  { fact_name = "Live variables"
  , fact_bot  = Set.empty
  , fact_join = add
  }
    where add _ (OldFact old) (NewFact new) = (ch, j)
            where
              j = new `Set.union` old
              ch = changeIf (Set.size j > Set.size old)

liveness :: BwdTransfer Insn Live
liveness = mkBTransfer go
  where
    go :: Insn e x -> Fact x Live -> Live
    go (ILabel (_bid, _vs)  ) s = s
    go (ILetVal  id letable ) s = Set.union  (without s [id]) (Set.fromList $ freeIdents letable)
    go (ILetFuns ids fns    ) s = Set.unions ((without s ids):(map (Set.fromList . freeIdents) fns))
    go node@(ILast    cflast) fdb =
          let s = Set.unions (map (fact fdb) (successors node)) in
          case cflast of
            (CFCont _bid     vs) -> insert s vs
            (CFCall _bid _ v vs) -> insert s (v:vs)
            (CFCase v _pats)     -> insert s [v]

    without s ids = Set.difference s (Set.fromList ids)
    insert s vs = Set.union s (Set.fromList (map tidIdent vs))

    fact :: FactBase (Set.Set Ident) -> Label -> Live
    fact f l = fromMaybe (fact_bot liveLattice) $ lookupFact l f

deadBindElim :: forall m . FuelMonad m => BwdRewrite m Insn Live
deadBindElim = mkBRewrite d
  where
    d :: Insn e x -> Fact x Live -> m (Maybe (Graph Insn e x))
    d (ILetVal id letable) live |
      not (id `Set.member` live) && isPure letable = return $ Just emptyGraph
    d (ILetFuns [id] [_])  live |
      not (id `Set.member` live)                   = return $ Just emptyGraph
    -- If LetFuns forms a SCC, then we can't drop any entry unless we can drop
    -- every entry. However, if it's not a SCC, then we can drop any entry which
    -- is dead and does not appear in any of the other functions.
    d (ILetFuns ids fns)   live = do
      let inOthers = map (\(id, ofns) ->
                         Set.member id (Set.fromList (concatMap freeIdents ofns)))
                         (zip ids (others fns))
      let kept = filter (\(id,_fn,inother) -> Set.member id live || inother) (zip3 ids fns inOthers)
      return $ if null kept then Just emptyGraph
                            else let (ids' , fns' , _) = unzip3 kept in
                                 Just (mkMiddle $ ILetFuns  ids' fns' )
      --return $ trace (concatMap (\id -> show id ++ " live?" ++ show (id `Set.member` live) ++ "\n") ids) Nothing
    d _ _ = return Nothing

    -- others [1,2,3,4] = [[2,3,4],[1,3,4],[1,2,4],[1,2,3]]
    others xs = map (\n -> take n xs ++ tail (drop n xs)) [0..length xs - 1]

runLiveness :: IORef Uniq -> BasicBlockGraph -> IO BasicBlockGraph
runLiveness uref bbg = runWithUniqAndFuel uref infiniteFuel (go bbg)
  where go bbg = do
            (bb', _, _) <- analyzeAndRewriteBwd bwd (JustC [bbgEntry bbg])
                                                           (bbgBody  bbg)
                                                           mapEmpty
            return $ bbg { bbgBody = bb' }

        -- bwd' = debugBwdTransfers trace showing (\_ _ -> True) bwd
        bwd = BwdPass { bp_lattice  = liveLattice
                      , bp_transfer = liveness
                      , bp_rewrite  = deadBindElim
                      }
-}
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

instance AExpr (Letable ty)    where freeIdents x = map tidIdent $ ((freeTypedIds x) :: [TypedId ty])
instance AExpr BasicBlockGraph where freeIdents x = map tidIdent $ ((freeTypedIds x) :: [TypedId MonoType])

--showing :: Insn e x -> String
--showing insn = "SHOWING: " ++ show (pretty insn) ++ "\nEND SHOWING\n"
--showing insn = show (pretty insn)

cfgSize :: BasicBlockGraph -> (Int, Int) -- toplevel, cumulative
cfgSize bbg = foldGraphNodes go (bbgBody bbg) (0, 0)
  where
    go :: Insn e x -> (Int, Int) -> (Int, Int)
    go (ILabel   (_bid, _vs)) (t,a) = (t             , a)
    go (ILetVal _id  letable) (t,a) = (t + size      , a + size)
                                     where size = letableSize letable
    go (ILetFuns _ids fns   ) (t,a) = (t + length fns, a + length fns +
                                      sum [snd $ cfgSize (fnBody f) | f <- fns])
    go (ILast   _cflast     ) (t,a) = (t + 1         , a + 1)

{-
cfgCalls :: BasicBlockGraph -> Map Ident (Set BlockId) -- fn var to continuation
cfgCalls bbg = foldGraphNodes go (bbgBody bbg) Map.empty
  where
    go :: Insn e x -> Map Ident (Set BlockId) -> Map Ident (Set BlockId)
    go (ILabel   {}           ) m = m
    go (ILetVal  {}           ) m = m
    go (ILetFuns _   fns      ) m = Map.unionsWith Set.union
                                               (m:(map (cfgCalls . fnBody) fns))
    go (ILast (CFCall k _ v _)) m = Map.insertWith Set.union (tidIdent v)
                                                        (Set.singleton k) m
    go (ILast _               ) m = m
-}
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

-- ||||||||||| Bottom-up May-GC constraint propagation ||||||||||{{{
type MGCM a = State MayGCConstraints a -- MGCM = "may-gc monad"

collectMayGCConstraints :: CFBody -> MayGCConstraints
collectMayGCConstraints cfbody = execState (go cfbody) Map.empty
  where
    go :: CFBody -> MGCM ()
    go (CFB_Call {}) = return ()
    go (CFB_LetFuns ids cffns cfbody) = do
          collectMayGCConstraints_CFFns ids cffns
          go cfbody

defaultMayGCConstraint = (GCUnknown "maygc-init", Set.empty)

collectMayGCConstraints_CFFns :: [Ident] -> [CFFn] -> MGCM ()
collectMayGCConstraints_CFFns ids fns = do
  mapM_ initializeMayGCConstraint ids
  mapM_ collectMayGCConstraints_CFFn fns
 where
   initializeMayGCConstraint id = modify (Map.insert id defaultMayGCConstraint)

collectMayGCConstraints_CFFn :: CFFn -> MGCM ()
collectMayGCConstraints_CFFn fn = collectMayGCConstraints_CFG (fnBody fn)
                                                    (tidIdent (fnVar  fn))

collectMayGCConstraints_CFG :: BasicBlockGraph -> Ident -> MGCM ()
collectMayGCConstraints_CFG bbg fnid = let (bid,_) = bbgEntry bbg in
                                       mapGraphNodesM_ go bid (bbgBody bbg)
  where
        go :: forall e x. Insn e x -> MGCM ()
        go (ILabel  _    )    = return ()
        -- This is a conservative approximation; we may not actually call v
        -- through the ident it is bound to, but it's good enough for now...
        -- The indirect constraint is a hack to ensure that the SCC/call graph
        -- built during may-gc resolution will not be under-approximated.
        -- The aliasing bit makes sure that calls to x are treated as being
        -- GCUnknown rather than MayGC.
        go (ILetVal x (ILBitcast _ v)) = do addIndirectConstraint (tidIdent v)
                                            modify $ aliasing x v
        go (ILetVal _  lt)    = withGC $ canGC Map.empty lt
        go (ILetFuns ids fns) = collectMayGCConstraints_CFFns ids fns
           -- Note: the function bindings themselves don't (yet) contribute
           -- to their parent's GC status; we need the representation decisions
           -- made by closure conversion before getting a final answer.
        go (ILast cflast)     = case cflast of
                     CFCont {}      -> return ()
                     CFCase {}      -> return ()
                     CFCall _ _ v _ -> callGC (tidIdent v)

        aliasing x v = \m -> Map.insert x (looky m (tidIdent v) `addAlias` v) m
        addAlias (maygc, s) v = (maygc, Set.insert (tidIdent v) s)
        looky m id = Map.findWithDefault defaultMayGCConstraint id m

        withGC WillNotGC     = return ()
        withGC MayGC         = modify $ Map.adjust (\_ -> (MayGC, Set.empty)) fnid
        withGC (GCUnknown _) = return ()

        callGC :: Ident -> MGCM ()

        callGC id@(GlobalSymbol name) = do
           if willNotGCGlobal name
             then return ()
             else addIndirectConstraint id

        callGC localid = do
                m <- get
                case Map.lookup localid m of
                  Nothing -> withGC MayGC
                     -- Note: Because we collect may-gc constraints after
                     --       running optimizations, the conservative estimate
                     --       that every unknown call site might GC is probably
                     --       not a bad approximation to the truth.

                  Just (GCUnknown _, _) -> addIndirectConstraint localid
                  Just (maygc,       _) -> withGC maygc

        addIndirectConstraint id =
          modify $ Map.adjust (\(maygc, indirs) ->
                                (maygc, Set.insert id indirs)) fnid
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

