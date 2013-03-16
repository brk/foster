#!/usr/bin/env python

# Copyright (c) 2010 Ben Karel. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

import sys
import os
import os.path
from optparse import OptionParser

from run_cmd import *

def get_parser(usage):
  parser = OptionParser(usage=usage)
  parser.add_option("--bindir", dest="bindir", action="store", default="",
                    help="Use bindir as default place to find binaries")
  parser.add_option("--srcroot", dest="srcroot", action="store", default="",
                    help="Use srcroot as default place to find Foster project source")
  parser.add_option("--recompile", dest="recompile", action="store_true", default=False,
                    help="Force GHC to recompile all Haskell sources.")
  parser.add_option("--profile", dest="profile", action="store_true", default=False,
                    help="Force GHC to profile all Haskell sources.")
  parser.add_option("--optimize", dest="optimize", action="store_true", default=False,
                    help="Enable optimization when compiling Haskell code.")
  parser.add_option("--coverage", dest="coverage", action="store_true", default=False,
                    help="Enable coverage when compiling Haskell code.")
  return parser

def normalize(path):
  return os.path.expanduser(path)

def ghc7plus():
  import subprocess as sub
  p = sub.Popen(['ghc','--version'], stdout=sub.PIPE)
  output, errors = p.communicate()
  return not 'version 6' in output

if __name__ == "__main__":
  parser = get_parser("%prog --bindir <BINDIR> --root <FOSTER_ROOT> [other args]")
  (options, args) = parser.parse_args()

  if options.bindir == "" or options.srcroot == "":
    parser.print_help()
    sys.exit(1)

  params = {
        'bindir' :  normalize(options.bindir),
        'srcroot':  normalize(options.srcroot),
        'hsflags': "-XFlexibleInstances -XMultiParamTypeClasses -XDeriveDataTypeable" +
                   " -XTypeSynonymInstances -XDeriveFunctor -XBangPatterns" +
                   " -Wall -fwarn-unused-do-bind -fwarn-tabs" +
                   " -fno-warn-missing-signatures -fno-warn-name-shadowing" +
                   " -fno-warn-type-defaults -fno-warn-orphans",
      }

  if options.recompile:
    params['hsflags'] += ' -fforce-recomp'

  if options.profile:
    params['hsflags'] += ' -prof -auto-all'

  if options.optimize:
    params['hsflags'] += ' -O2'

  if options.coverage:
    params['hsflags'] += ' -fhpc'

  if ghc7plus():
    # GHC 6 allows all runtime opts to be late-bound,
    # but GHC 7 does not, by default. Forcefully revert to the old behavior.
    params['hsflags'] += ' -rtsopts'

  cmd = ("ghc --make -i%(srcroot)s/compiler/me/src %(hsflags)s " +
         "%(srcroot)s/compiler/me/src/Main.hs -o %(bindir)s/me") % params
  run_command(cmd, {}, "")
