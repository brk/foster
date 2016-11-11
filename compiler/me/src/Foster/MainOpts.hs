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
 , Option []     ["dump-ir"]    (ReqArg DumpIR      "IR") "dump a particular IR (ast, ann, kn, mono, mono-sunk, cfg, cc, may-gc, maygc, prealloc, il)"
 , Option []     ["dump-fn"]    (ReqArg DumpFn      "FN") "dump a particular fn"
 , Option []     ["standalone"] (NoArg  Standalone)       "no extra/hidden code"
 , Option []     ["verbose"]    (NoArg  Verbose)          "verbose mode"
 , Option []     ["interactive"](NoArg  Interactive)      "interactive mode (pause on errors)"
 , Option []     ["dump-prims"] (NoArg  DumpPrims)        "dump primitive bindings"
 , Option []     ["fmt"]        (NoArg  FmtOnly)          "pretty-print source AST"
 , Option []     ["no-inline"]  (NoArg  NoInline)         "disable inlining"
 , Option []     ["inline"]     (NoArg  Inline)           "enable inlining"
 , Option []     ["no-donate"]  (NoArg  NoDonate)         "diable inlining donation"
 , Option []     ["shrink"]     (NoArg  Shrink)           "enable shrinking"
 , Option []     ["no-ctor-opt"] (NoArg NoCtorOpt)        "diable ctor representation optimizations"
 , Option []     ["non-moving-gc"] (NoArg NonMovingGC)    "assume non-moving GC (for testing codegen effect of reloads)"
 , Option []     ["inline-size-limit"]
                                (ReqArg InlineSize "SIZE")"size counter value for inlining"
 ]

-- Accessors to query the result of parsing options.
getInterpretFlag (flags, _) = foldr (\f a -> case f of Interpret d -> Just d  ; _ -> a) Nothing flags
getProgArgs      (flags, _) = foldr (\f a -> case f of ProgArg arg -> arg:a   ; _ -> a) []      flags
getDumpFns       (flags, _) = foldr (\f a -> case f of DumpFn  arg -> arg:a   ; _ -> a) []      flags
getVerboseFlag   (flags, _) =        Verbose     `elem` flags
getInteractiveFlag(flags, _) =       Interactive `elem` flags
getStandaloneFlag (flags, _) =       Standalone  `elem` flags
getDumpIRFlag ir (flags, _) =        DumpIR ir   `elem` flags
getDumpPrimitives(flags, _) =        DumpPrims   `elem` flags
getFmtOnlyFlag   (flags, _) =        FmtOnly     `elem` flags
getShrinkFlag    (flags, _) =        Shrink      `elem` flags
getCtorOpt       (flags, _) = (not $ NoCtorOpt   `elem` flags)
getNonMovingGC   (flags, _) =        NonMovingGC `elem` flags
getInlining      (flags, _) = (not $ NoInline    `elem` flags) && (Inline  `elem` flags)
getInliningDonate(flags, _) = (not $ NoDonate    `elem` flags)
getInliningSize  (flags, _) = foldr (\f a -> case f of InlineSize s -> Just (read s :: Int) ; _ -> a) Nothing flags


data Flag = Interpret String
          | DumpIR    String
          | DumpFn    String
          | ProgArg   String
          | Verbose
          | Interactive
          | Standalone
          | DumpPrims
          | FmtOnly
          | NoCtorOpt
          | NonMovingGC
          | NoInline
          | Inline
          | Shrink
          | NoDonate
          | InlineSize String
          deriving Eq

