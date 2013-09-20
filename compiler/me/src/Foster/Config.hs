-----------------------------------------------------------------------------
-- Copyright (c) 2012 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.Config where

import Foster.Base(Uniq, Ident(..))
import Data.IORef(IORef, modifyIORef, readIORef)
import Control.Monad.State(StateT, gets, when, liftIO)
import qualified Data.Text as T(Text)

type Compiled = StateT CompilerContext IO
data CompilerContext = CompilerContext {
        ccVerbose   :: Bool
      , ccUniqRef   :: IORef Uniq
      , ccFlagVals  :: ([Flag], [String])
      , ccInline    :: Bool
      , ccDumpFns   :: [String]
}

ccUniq :: Compiled Uniq
ccUniq = do uref <- gets ccUniqRef
            liftIO $ modifyIORef uref (+1) >> readIORef uref

ccFreshId :: T.Text -> Compiled Ident
ccFreshId txt = do u <- ccUniq
                   return $ Ident txt u

ccWhen :: (CompilerContext -> Bool) -> IO () -> Compiled ()
ccWhen getter action = do cond <- gets getter ; liftIO $ when cond action

data Flag = Interpret String
          | DumpIR    String
          | DumpFn    String
          | ProgArg   String
          | Verbose
          | DumpPrims
          | NoCtorOpt
          | NoInline
          | Inline
          | NoDonate
          | InlineSize String
          deriving Eq
