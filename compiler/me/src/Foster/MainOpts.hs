-----------------------------------------------------------------------------
-- Copyright (c) 2012 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.MainOpts where

import Foster.Config(Flag(..))

import System.Console.GetOpt

options :: [OptDescr Flag]
options =
 -- short chars, long options,  argument descriptor,      explanation of option.
 [ Option []     ["interpret"]  (ReqArg Interpret  "DIR") "interpret in DIR"
 , Option []     ["prog-arg"]   (ReqArg ProgArg    "ARG") "pass through ARG"
 , Option []     ["dump-ir"]    (ReqArg DumpIR      "IR") "dump a particular IR"
 , Option []     ["dump-fn"]    (ReqArg DumpFn      "FN") "dump a particular fn"
 , Option []     ["verbose"]    (NoArg  Verbose)          "verbose mode"
 , Option []     ["dump-prims"] (NoArg  DumpPrims)        "dump primitive bindings"
 ]

parseOpts :: [String] -> IO ([Flag], [String])
parseOpts argv =
  case getOpt Permute options argv of
    (o,n,[]  ) -> return (o,n)
    (_,_,errs) -> ioError (userError (concat errs ++ usageInfo header options))
  where header = "Usage: me [OPTION...] files..."

-- Accessors to query the result of parsing options.
getInterpretFlag (flags, _) = foldr (\f a -> case f of Interpret d -> Just d  ; _ -> a) Nothing flags
getProgArgs      (flags, _) = foldr (\f a -> case f of ProgArg arg -> arg:a   ; _ -> a) []      flags
getDumpFns       (flags, _) = foldr (\f a -> case f of DumpFn  arg -> arg:a   ; _ -> a) []      flags
getVerboseFlag   (flags, _) = Verbose   `elem` flags
getDumpIRFlag ir (flags, _) = DumpIR ir `elem` flags
getDumpPrimitives(flags, _) = DumpPrims `elem` flags

