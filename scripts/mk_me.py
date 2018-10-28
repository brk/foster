#!/usr/bin/env python2

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

if __name__ == "__main__":
  parser = get_parser("%prog --bindir <BINDIR> --root <FOSTER_ROOT> [other args]")
  (options, args) = parser.parse_args()

  if options.bindir == "" or options.srcroot == "":
    parser.print_help()
    sys.exit(1)

  params = {
        'bindir' :  normalize(options.bindir),
        'srcroot':  normalize(options.srcroot),
        'hsflags':  ['-rtsopts'],
        'stackflags' : []
      }

  if options.profile:
    if not options.optimize:
      params['hsflags'].append('-fprof-auto')
      params['hsflags'].append('-prof')
      params['stackflags'].append('--executable-profiling')
      params['stackflags'].append('--library-profiling')
    else:
      print "Warning: profiling disabled due to --optimize flag"

  if options.optimize:
    params['hsflags'].append('-O2')

  if options.coverage:
    params['hsflags'].append('-fhpc')

  # Allow runtime opts to be late-bound.

  def build_with_stack():
    cmd = [
       'stack', 'install',
       '--stack-yaml', ('%(srcroot)s/compiler/me/stack.yaml' % params),
       '--local-bin-path', params['bindir'],
       ] + ['--ghc-options="%s"' % s for s in params['hsflags']] + params['stackflags']
    run_command(cmd, {}, "")

  def build_with_ghcmake():
    params['ghcmake'] = 'ghc --make'

    with open(os.devnull, 'w') as devnull:
      (rv, ms) = run_command("which ghc-make", {}, "", stdout=devnull, strictrv=False)
      if rv == 0:
         # Prevent a spurious/buggy error (race condition?) from ghc-make
         run_command('touch %(bindir)s/me' % params, {}, "")
         params['ghcmake'] = 'ghc-make'


    params['hsflags'] = (' '.join(params['hsflags']) +
                         " -XFlexibleInstances -XFlexibleContexts -XMultiParamTypeClasses -XDeriveDataTypeable" +
                         " -XTypeSynonymInstances -XDeriveFunctor -XBangPatterns" +
                         " -Wall -fwarn-unused-do-bind -fwarn-tabs" +
                         " -fno-warn-missing-signatures -fno-warn-name-shadowing" +
                         " -fno-warn-type-defaults -fno-warn-orphans -fno-warn-redundant-constraints")
    cmd = ("cabal exec -- %(ghcmake)s -i%(srcroot)s/compiler/me/src %(hsflags)s " +
           "%(srcroot)s/compiler/me/src/Main.hs -o %(bindir)s/me") % params
    os.chdir(os.path.join(options.srcroot, 'compiler', 'me'))
    run_command(cmd, {}, "")

  if False:
     build_with_stack()
  else:
     build_with_ghcmake()

