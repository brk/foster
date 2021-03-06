#!/usr/bin/env python3

# Copyright (c) 2009 Ben Karel. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt


import sys
import re
import os
import os.path
import subprocess
import shutil

from optparse import OptionParser

clang = "<llvm compiler not set>"
bindir = "<bindir not set>"
outdir = "<outdir not set>"
coro_method = "<coro_method not set>"
debug_flag = ""

def ensure_dir_exists(output):
  """Creates the given directory if it doesn't exist;
      if the name refers to a path, prints an error and aborts."""
  if not os.path.exists(output):
    os.mkdir(output)
  elif not os.path.isdir(output):
    print("Error: %s must be a directory!" % output)
    sys.exit(1)

def transplant(path, newdir):
  """Given '/some/path/to/file.txt'  and  '/some/new/dir',
     returns '/some/new/dir/file.txt'."""
  head, tail = os.path.split(path)
  return os.path.join(newdir, tail)

def replace_extension_with(path, newext):
  preext, oldext = os.path.splitext(path)
  return preext + newext

def compile_source(src):
  outbc      = replace_extension_with(transplant(src, outdir), '.bc')
  hdrhist    = os.path.join(srcdir, 'third_party', 'HdrHistogram_c', 'src')
  include_dirs = [bindir, hdrhist]
  includes = ' '.join(['-I ' + path for path in include_dirs])
  flags = debug_flag + " -O2 -march=native"
  cmd = "%s %s %s %s -emit-llvm -c -o %s" % (clang, src, includes, flags, outbc)
  if options.verbose:
    print(cmd)
  subprocess.call(cmd.split(" "))
  return outbc

def link_all(all_bcs):
  outbc  = os.path.join(bindir, "_bitcodelibs_", "foster_hdrhist.bc")
  cmd = "%s %s -o %s" % (llvmld, " ".join(all_bcs), outbc)
  if options.verbose:
    print(cmd)
  return subprocess.call(cmd.split(" "))

def get_libfoster_parser(usage):
  parser = OptionParser(usage=usage)
  parser.add_option("--bindir", dest="bindir", action="store",
                    help="Use bindir as default place to find binaries")
  parser.add_option("--srcdir", dest="srcdir", action="store",
                    help="Use srcdir as default place to find source")
  parser.add_option("--clang", dest="clang", action="store",
                    help="Path to clang")
  parser.add_option("--llvmdir", dest="llvmdir", action="store",
                    help="Path to LLVM bin dir (llvm-link should be found here)")
  parser.add_option("--debug_mode", action="store_true", dest="debug", default=False,
                    help="Show more information about program output.")
  parser.add_option("--verbose", action="store_true", dest="verbose", default=False,
                    help="Show more information about program output.")
  return parser

if __name__ == "__main__":
  parser = get_libfoster_parser("usage: %prog [options]")
  (options, args) = parser.parse_args()

  clang  = options.clang
  srcdir = options.srcdir
  bindir = options.bindir
  llvmld = os.path.join(options.llvmdir, 'llvm-link')
  outdir = os.path.join(bindir, "_bitcodelibs_")
  ensure_dir_exists(outdir)

  sources = args
  if options.debug:
    debug_flag = "-g"

  bitcodes = [compile_source(source) for source in sources]

  status = link_all(bitcodes)
  sys.exit(status)
