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
        'hsflags': "-XFlexibleInstances -XMultiParamTypeClasses -XDeriveDataTypeable" +
                   " -XTypeSynonymInstances" +
                   " -fwarn-unused-imports -fwarn-incomplete-patterns",
      }

  if options.recompile:
    params['hsflags'] += ' -fforce-recomp'

  if options.profile:
    params['hsflags'] += ' -prof -auto'

  cmd = ("ghc --make -i%(srcroot)s/compiler/me/src %(hsflags)s " +
         "%(srcroot)s/compiler/me/src/Main.hs -o %(bindir)s/me") % params
  run_command(cmd, {}, "")
