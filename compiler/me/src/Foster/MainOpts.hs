-----------------------------------------------------------------------------
-- Copyright (c) 2012 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.MainOpts where

import System.Console.GetOpt

options :: [OptDescr Flag]
options =
 -- short chars, long options,  argument descriptor,      explanation of option.
 [ Option []     ["interpret"]  (ReqArg Interpret  "DIR") "interpret in DIR"
 , Option []     ["prog-arg"]   (ReqArg ProgArg    "ARG") "pass through ARG"
 , Option []     ["dump-ir"]    (ReqArg DumpIR      "IR") "dump a particular IR (ast, ann, kn, mono, mono-sunk, cfg, cc, may-gc, prealloc, il)"
 , Option []     ["dump-fn"]    (ReqArg DumpFn      "FN") "dump a particular fn"
 , Option []     ["verbose"]    (NoArg  Verbose)          "verbose mode"
 , Option []     ["interactive"](NoArg  Interactive)      "interactive mode (pause on errors)"
 , Option []     ["dump-prims"] (NoArg  DumpPrims)        "dump primitive bindings"
 , Option []     ["fmt"]        (NoArg  FmtOnly)          "pretty-print source AST"
 , Option []     ["inline-gas"] (ReqArg InlineGas "GAS")  "stop inlining after GAS steps"
 , Option []     ["no-donate"]  (NoArg  NoDonate)         "diable inlining donation"
 , Option []     ["no-ctor-opt"] (NoArg NoCtorOpt)        "diable ctor representation optimizations"
 , Option []     ["no-prealloc-opt"] (NoArg NoPreAllocOpt)"diable pre-allocation optimizations"
 , Option []     ["typecheck-only"] (NoArg TypecheckOnly) "typecheck only, no codegen"
 , Option []     ["no-quant"] (NoArg NoQuantification)    "disable automatic polymorphic quantification (dev tool only)"
 , Option []     ["inline-size-limit"]
                                (ReqArg InlineSize "SIZE")"size counter value for inlining"
 ]

-- Accessors to query the result of parsing options.
getInterpretFlag (flags, _) = foldr (\f a -> case f of Interpret d -> Just d  ; _ -> a) Nothing flags
getProgArgs      (flags, _) = foldr (\f a -> case f of ProgArg arg -> arg:a   ; _ -> a) []      flags
getDumpFns       (flags, _) = foldr (\f a -> case f of DumpFn  arg -> arg:a   ; _ -> a) []      flags
getVerboseFlag   (flags, _) =        Verbose     `elem` flags
getInteractiveFlag(flags, _) =       Interactive `elem` flags
getDumpIRFlag ir (flags, _) =        DumpIR ir   `elem` flags
getDumpPrimitives(flags, _) =        DumpPrims   `elem` flags
getFmtOnlyFlag   (flags, _) =        FmtOnly     `elem` flags
getCtorOpt       (flags, _) = (not $ NoCtorOpt   `elem` flags)
getNoPreAllocOpt (flags, _) =        NoPreAllocOpt `elem` flags
getTypecheckOnly (flags, _) =        TypecheckOnly `elem` flags
getNoQuant       (flags, _) =     NoQuantification `elem` flags
getInliningDonate(flags, _) = (not $ NoDonate    `elem` flags)
getInliningSize  (flags, _) = foldr (\f a -> case f of InlineSize s -> Just (read s :: Int) ; _ -> a) Nothing flags
getInliningGas   (flags, _) = foldr (\f a -> case f of InlineGas s  -> Just (read s :: Int) ; _ -> a) Nothing flags

data Flag = Interpret String
          | DumpIR    String
          | DumpFn    String
          | ProgArg   String
          | Verbose
          | Interactive
          | DumpPrims
          | FmtOnly
          | NoCtorOpt
          | NoPreAllocOpt
          | TypecheckOnly
          | NoQuantification
          | InlineGas String
          | NoDonate
          | InlineSize String
          deriving Eq

