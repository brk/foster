-- This file contains code from the (un-exported) implementation
-- of the SBV library, which is copyright Levent Erkok
-- and is released under the 3-clause BSD license.

module Foster.RunZ3 (runZ3) where

import qualified Control.Exception as C

import Control.Concurrent (newEmptyMVar, takeMVar, putMVar, forkIO)
import Control.Monad      (when)
import Data.Char          (isSpace)
import Data.List          (intercalate, isPrefixOf, isInfixOf)
import Data.Maybe         (isNothing, fromJust)
import System.Directory   (findExecutable)
import System.Process     (readProcessWithExitCode, runInteractiveProcess, waitForProcess)
import System.Exit        (ExitCode(..))
import System.IO          (hClose, hFlush, hPutStr, hGetContents, hGetLine)

data SMTConfig = SMTConfig {
         verbose        :: Bool             -- ^ Debug mode
       , timing         :: Bool             -- ^ Print timing information on how long different phases took (construction, solving, etc.)
       , sBranchTimeOut :: Maybe Int        -- ^ How much time to give to the solver for each call of 'sBranch' check. (In seconds. Default: No limit.)
       , timeOut        :: Maybe Int        -- ^ How much time to give to the solver. (In seconds. Default: No limit.)
       , printBase      :: Int              -- ^ Print integral literals in this base (2, 8, and 10, and 16 are supported.)
       , printRealPrec  :: Int              -- ^ Print algebraic real values with this precision. (SReal, default: 16)
       , solverTweaks   :: [String]         -- ^ Additional lines of script to give to the solver (user specified)
       , satCmd         :: String           -- ^ Usually "(check-sat)". However, users might tweak it based on solver characteristics.
       , smtFile        :: Maybe FilePath   -- ^ If Just, the generated SMT script will be put in this file (for debugging purposes mostly)
       , useSMTLib2     :: Bool             -- ^ If True, we'll treat the solver as using SMTLib2 input format. Otherwise, SMTLib1
       , solver         :: SMTSolver        -- ^ The actual SMT solver.
       --, roundingMode   :: RoundingMode     -- ^ Rounding mode to use for floating-point conversions
       --, useLogic       :: Maybe Logic      -- ^ If Nothing, pick automatically. Otherwise, either use the given one, or use the custom string.
       }


-- | A script, to be passed to the solver.
data SMTScript = SMTScript {
          scriptBody  :: String        -- ^ Initial feed
        , scriptModel :: Maybe String  -- ^ Optional continuation script, if the result is sat
        }

-- | An SMT engine
--type SMTEngine = SMTConfig -> Bool -> [(Quantifier, NamedSymVar)] -> [(String, UnintKind)] -> [Either SW (SW, [SW])] -> String -> IO SMTResult

-- | An SMT solver
data SMTSolver = SMTSolver {
         name           :: String               -- ^ Printable name of the solver
       , executable     :: String               -- ^ The path to its executable
       , options        :: [String]             -- ^ Options to provide to the solver
       --, engine         :: SMTEngine            -- ^ The solver engine, responsible for interpreting solver output
       , xformExitCode  :: ExitCode -> ExitCode -- ^ Should we re-interpret exit codes. Most solvers behave rationally, i.e., id will do. Some (like CVC4) don't.
       --, capabilities   :: SolverCapabilities   -- ^ Various capabilities of the solver
       }

-- | Helper function to spin off to an SMT solver.
pipeProcess :: SMTConfig -> String -> String -> [String] -> SMTScript -> (String -> String) -> IO (Either String [String])
pipeProcess cfg nm execName opts script cleanErrs = do
        mbExecPath <- findExecutable execName
        case mbExecPath of
          Nothing -> return $ Left $ "Unable to locate executable for " ++ nm
                                   ++ "\nExecutable specified: " ++ show execName
          Just execPath -> do (ec, contents, allErrors) <- runSolver cfg execPath opts script
                              let errors = dropWhile isSpace (cleanErrs allErrors)
                              case (null errors, xformExitCode (solver cfg) ec) of
                                (True, ExitSuccess)  -> return $ Right $ map clean (filter (not . null) (lines contents))
                                (_, ec')             -> let errors' = if null errors
                                                                      then (if null (dropWhile isSpace contents)
                                                                            then "(No error message printed on stderr by the executable.)"
                                                                            else contents)
                                                                      else errors
                                                            finalEC = case (ec', ec) of
                                                                        (ExitFailure n, _) -> n
                                                                        (_, ExitFailure n) -> n
                                                                        _                  -> 0 -- can happen if ExitSuccess but there is output on stderr
                                                        in return $ Left $  "Failed to complete the call to " ++ nm
                                                                         ++ "\nExecutable   : " ++ show execPath
                                                                         ++ "\nOptions      : " ++ unwords opts
                                                                         ++ "\nExit code    : " ++ show finalEC
                                                                         ++ "\nSolver output: "
                                                                         ++ "\n" ++ line ++ "\n"
                                                                         ++ intercalate "\n" (filter (not . null) (lines errors'))
                                                                         ++ "\n" ++ line
                                                                         ++ "\nGiving up.."
  where clean = reverse . dropWhile isSpace . reverse . dropWhile isSpace
        line  = replicate 78 '='

-- | A standard solver interface. If the solver is SMT-Lib compliant, then this function should suffice in
-- communicating with it.
standardSolver :: SMTConfig -> SMTScript -> (String -> String) -> ([String] -> a) -> ([String] -> a) -> IO a
standardSolver config script cleanErrs failure success = do
    let msg      = when (verbose config) . putStrLn . ("** " ++)
        smtSolver= solver config
        exec     = executable smtSolver
        opts     = options smtSolver
        isTiming = timing config
        nmSolver = name smtSolver
    msg $ "Calling: " ++ show (unwords (exec:opts))
    case smtFile config of
      Nothing -> return ()
      Just f  -> do msg $ "Saving the generated script in file: " ++ show f
                    writeFile f (scriptBody script)
    contents <- pipeProcess config nmSolver exec opts script cleanErrs
    msg $ nmSolver ++ " output:\n" ++ either id (intercalate "\n") contents
    case contents of
      Left e   -> return $ failure (lines e)
      Right xs -> return $ success (mergeSExpr xs)

h1 :: C.SomeException -> IO String
h1 _ = return ""

-- | A variant of 'readProcessWithExitCode'; except it knows about continuation strings
-- and can speak SMT-Lib2 (just a little).
runSolver :: SMTConfig -> FilePath -> [String] -> SMTScript -> IO (ExitCode, String, String)
runSolver cfg execPath opts script
 | isNothing $ scriptModel script
 = let checkCmd | useSMTLib2 cfg = '\n' : satCmd cfg
                | True           = ""
   in readProcessWithExitCode execPath opts (scriptBody script ++ checkCmd)
 | True
 = do (send, ask, cleanUp) <- do
                (inh, outh, errh, pid) <- runInteractiveProcess execPath opts Nothing Nothing
                let send l    = hPutStr inh (l ++ "\n") >> hFlush inh
                    recv      = hGetLine outh `C.catch` h1
                    ask l     = send l >> recv
                    cleanUp r = do outMVar <- newEmptyMVar
                                   out <- hGetContents outh
                                   _ <- forkIO $ C.evaluate (length out) >> putMVar outMVar ()
                                   err <- hGetContents errh
                                   _ <- forkIO $ C.evaluate (length err) >> putMVar outMVar ()
                                   hClose inh
                                   takeMVar outMVar
                                   takeMVar outMVar
                                   hClose outh
                                   hClose errh
                                   ex <- waitForProcess pid
                                   -- if the status is unknown, prepare for the possibility of not having a model
                                   -- TBD: This is rather crude and potentially Z3 specific
                                   return $ if "unknown" `isPrefixOf` r && "error" `isInfixOf` (out ++ err)
                                            then (ExitSuccess, r               , "")
                                            else (ex,          r ++ "\n" ++ out, err)
                return (send, ask, cleanUp)
      mapM_ send (lines (scriptBody script))
      r <- ask $ satCmd cfg
      when (any (`isPrefixOf` r) ["sat", "unknown"]) $ do
        let mls = lines (fromJust (scriptModel script))
        when (verbose cfg) $ do putStrLn "** Sending the following model extraction commands:"
                                mapM_ putStrLn mls
        mapM_ send mls
      cleanUp r

-- | In case the SMT-Lib solver returns a response over multiple lines, compress them so we have
-- each S-Expression spanning only a single line. We'll ignore things line parentheses inside quotes
-- etc., as it should not be an issue
mergeSExpr :: [String] -> [String]
mergeSExpr []       = []
mergeSExpr (x:xs)
 | d == 0 = x : mergeSExpr xs
 | True   = let (f, r) = grab d xs in unwords (x:f) : mergeSExpr r
 where d = parenDiff x
       parenDiff :: String -> Int
       parenDiff = go 0
         where go i ""       = i
               go i ('(':cs) = let i'= i+1 in i' `seq` go i' cs
               go i (')':cs) = let i'= i-1 in i' `seq` go i' cs
               go i (_  :cs) = go i cs
       grab i ls
         | i <= 0    = ([], ls)
       grab _ []     = ([], [])
       grab i (l:ls) = let (a, b) = grab (i+parenDiff l) ls in (l:a, b)

runZ3 :: String -> IO (Either String [String])
runZ3 smtlib2cmd = do
  let z3solver = SMTSolver "z3" "z3" ["-T:1"] id
  let cfg = SMTConfig False False Nothing Nothing 10 16 [] "(check-sat)" Nothing True z3solver
  let scr = SMTScript smtlib2cmd (Just "(get-model)")
  pipeProcess cfg "z3" "z3" ["-smt2", "-in"] scr id

