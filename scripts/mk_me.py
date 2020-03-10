#!/usr/bin/env python3

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
        'cabalflags' : ['-j']
      }

  if options.profile:
    if not options.optimize:
      params['cabalflags'].append('--enable-profiling')
      params['cabalflags'].append('--disable-optimization')
    else:
      print("Warning: profiling disabled due to --optimize flag")

  if options.optimize:
    params['cabalflags'].append('-O2')

  if options.coverage:
    params['cabalflags'].append('--enable-coverage')

  # Allow runtime opts to be late-bound.

  def build_with_cabal():
    cmd = ("cabal v2-build exe:me " +
                " ".join(params['cabalflags']))
    os.chdir(os.path.join(options.srcroot, 'compiler', 'me'))
    run_command(cmd, {}, "")
    # We need at least the -O2 flag for cabal to execute the correct executable.
    # Otherwise, cabal defaults to using the non-optimized artifact.
    run_command(
        ''.join(["cabal v2-exec " +
                  (" ".join(params['cabalflags'])) +
            " -- sh %(srcroot)s/scripts/cp_me.sh %(bindir)s/me" % params]), {}, "")

  build_with_cabal()

