-----------------------------------------------------------------------------
-- Copyright (c) 2011 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.Worklist where

import Data.Sequence
import Data.Sequence as Seq(empty)

-- Add new items to the right, and take items from the left.
data WorklistQ item = WorklistQ (Seq item)

worklistEmpty = WorklistQ Seq.empty

worklistToList (WorklistQ s) = go (viewl s)
  where go EmptyL   = []
        go (a :< s) = a : go (viewl s)

worklistAdd :: WorklistQ item -> item -> WorklistQ item
worklistAdd (WorklistQ s) a = WorklistQ (s |> a)

worklistGet :: WorklistQ item -> Maybe (item, WorklistQ item)
worklistGet (WorklistQ s) =
  case viewl s of
        EmptyL  -> Nothing
        a :< s' -> Just (a, WorklistQ s')

