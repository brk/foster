-----------------------------------------------------------------------------
-- Copyright (c) 2012 Ben Karel. All rights reserved (except for ccTime).
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.Config where

import Foster.Base(Uniq, Ident(..), modIORef')
import Foster.MainOpts

import Data.IORef(IORef, readIORef)
import Control.Monad.State(StateT, gets, when, liftIO)
import Control.Monad.Error(ErrorT, Error(..))
import Control.Monad.Trans.Error(ErrorList(..))
import Control.Monad.IO.Class(MonadIO)
import qualified Data.Text as T(Text)

import Data.Time.Clock.POSIX (getPOSIXTime)

import Text.PrettyPrint.ANSI.Leijen(Doc, text)
import System.Console.GetOpt

type Compiled = StateT CompilerContext (ErrorT CompilerFailures IO)
data CompilerContext = CompilerContext {
        ccVerbose   :: Bool
      , ccUniqRef   :: IORef Uniq
      , ccFlagVals  :: ([Flag], [String])
      , ccInline    :: Bool
      , ccDumpFns   :: [String]
      , ccSMTStats  :: IORef (Int, [(Double, Double)])
      , ccCFGSizes  :: IORef [(String, (Int, Int), (Int, Int) )]
}

type CompilerFailures = [Doc]

instance Error Doc where strMsg s = text s
instance ErrorList Doc where listMsg s = [text s]

ccUniq :: Compiled Uniq
ccUniq = do uref <- gets ccUniqRef
            liftIO $ modIORef' uref (+1) >> readIORef uref

ccFreshId :: T.Text -> Compiled Ident
ccFreshId txt = do u <- ccUniq
                   return $ Ident txt u

ccRecordCFGSizes :: (String, (Int, Int), (Int, Int)) -> Compiled ()
ccRecordCFGSizes entry = do
  r <- gets ccCFGSizes
  liftIO $ modIORef' r (entry:)

-- `time` from Criterion.Measurement, for actions wrapping IO.
ioTime :: MonadIO m => m a -> m (Double, a)
ioTime act = do
  start  <- liftIO $ realToFrac `fmap` getPOSIXTime
  result <- act
  end    <- liftIO $ realToFrac `fmap` getPOSIXTime
  let !delta = end - start
  return (delta, result)

ccWhen :: (CompilerContext -> Bool) -> IO () -> Compiled ()
ccWhen getter action = do cond <- gets getter ; liftIO $ when cond action

whenDumpIR :: String -> IO () -> Compiled ()
whenDumpIR ir action = do flags <- gets ccFlagVals
                          let cond = getDumpIRFlag ir flags
                          liftIO $ when cond action

parseOpts :: [String] -> IO ([Flag], [String])
parseOpts argv =
  case getOpt Permute options argv of
    (o,n,[]  ) -> return (o,n)
    (_,_,errs) -> ioError (userError (concat errs ++ usageInfo header options))
  where header = "Usage: me [OPTION...] files..."


