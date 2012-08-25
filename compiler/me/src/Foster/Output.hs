-----------------------------------------------------------------------------
-- Copyright (c) 2011 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.Output where

import System.Console.ANSI
import Data.IORef
import Control.Monad(forM_)

-- Either, with better names for the cases...
data OutputOr expr
    = OK      expr
    | Errors [Output]
    deriving (Eq)

data OutputData = OutputData { outputDataSGRs :: [SGR]
                             , outputDataString :: String }
type Output = [OutputData]

instance Eq OutputData where
    (OutputData _ sa) == (OutputData _ sb) = sa == sb

out :: String -> Output
out s = [(OutputData ([] :: [SGR]) s)]

outLn s = out (s ++ "\n")

outCS :: Color -> String -> Output
outCS c s = [OutputData [SetColor Foreground Dull c] s]

outCSLn c s = outCS c (s ++ "\n")

outToString :: Output -> String
outToString o = unlines $ map outputDataString o

-- Conceptually, for each string, we apply its graphics commands,
-- print the string, and then reset the SGR mode. But resetting
-- turns out to be expensive, so we track our state and only do
-- the apply/resets when we actually need to.
runOutput :: Output -> IO ()
runOutput outs = do
    stateRef <- newIORef OutputStateUnknown
    let forciblyRunOutput sgrs str = do
          _ <- setSGR sgrs
          putStr str
          case sgrs of -- no need to reset if we already reset!
                [] -> return ()
                _  -> setSGR [] -- [] means reset, not do nothing.
          writeIORef stateRef OutputStateClean
    forM_ outs $ (\(OutputData sgrs str) -> do
        state <- readIORef stateRef
        case state of -- if we're clean and not modifying, we can just putStr.
          OutputStateUnknown -> forciblyRunOutput sgrs str
          OutputStateClean ->
                    case sgrs of [] -> putStr str
                                 _  -> forciblyRunOutput sgrs str
      )
data OutputState = OutputStateUnknown | OutputStateClean

