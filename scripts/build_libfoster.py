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
debug_flag = "" # "-gdwarf-4"

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
  runtime_gc = os.path.join(srcdir, 'runtime', 'gc')
  runtime    = os.path.join(srcdir, 'runtime')
  basedir    = os.path.join(srcdir, 'third_party', 'chromium_base')
  corodir    = os.path.join(srcdir, 'third_party', 'libcoro')
  jepages    = os.path.join(srcdir, 'third_party', 'jemalloc_pages', 'include')
  hdrhist    = os.path.join(srcdir, 'third_party', 'HdrHistogram_c', 'src')
  include_dirs = [bindir, runtime, runtime_gc, basedir, corodir, jepages, hdrhist]
  includes = ' '.join(['-I ' + path for path in include_dirs])
  defines = ' -D'.join(['', coro_method])
  flags = debug_flag + defines + " -std=c++14 -O2 -march=native"
  cmd = "%s %s %s %s -emit-llvm -c -o %s" % (clang, src, includes, flags, outbc)
  if options.verbose:
    print(cmd)
  subprocess.call(cmd.split(" "))
  return outbc

# Clang doesn't accept -disable-fp-elim when compiling to bitcode
# (I don't know why), but we can apply a post-pass here to disable
# frame pointer elimination, which is introduced by default with -O{1,2}.
def finalpass(outbc, outbc0):
  cmd = "%s --frame-pointer=all %s -o %s" % (llvmopt, outbc0, outbc)
  return subprocess.call(cmd.split(" "))

def link_all(all_bcs):
  outbc0 = os.path.join(bindir, "_bitcodelibs_", "foster_runtime.bc.0")
  outbc  = os.path.join(bindir, "_bitcodelibs_", "foster_runtime.bc")
  all_bcs.append(os.path.join(bindir, "_bitcodelibs_", "foster_hdrhist.bc"))
  # Well, actually, link all except what fosterlower.cpp links beforehand, to
  # avoid multiply-defined symbols when everything comes together at the end.
  bcs = [bc for bc in all_bcs if not (bc.endswith("libfoster_coro.bc") or bc.endswith(".h"))]
  cmd = "%s %s -o %s" % (llvmld, " ".join(bcs), outbc0)
  if options.verbose:
    print(cmd)
  subprocess.call(cmd.split(" "))

  return finalpass(outbc, outbc0)

def get_libfoster_parser(usage):
  parser = OptionParser(usage=usage)
  parser.add_option("--bindir", dest="bindir", action="store",
                    help="Use bindir as default place to find binaries")
  parser.add_option("--srcdir", dest="srcdir", action="store",
                    help="Use srcdir as default place to find source")
  parser.add_option("--clang", dest="clang", action="store",
                    help="Path to clang(++)")
  parser.add_option("--llvmdir", dest="llvmdir", action="store",
                    help="Path to LLVM bin dir (llvm-link should be found here)")
  parser.add_option("--corodef", dest="corodef", action="store",
                    help="libcoro method definition, like CORO_ASM")
  parser.add_option("--verbose", action="store_true", dest="verbose", default=False,
                    help="Show more information about program output.")
  return parser

if __name__ == "__main__":
  parser = get_libfoster_parser("usage: %prog [options]")
  (options, sources) = parser.parse_args()

  clang  = options.clang
  srcdir = options.srcdir
  bindir = options.bindir
  llvmld = os.path.join(options.llvmdir, 'llvm-link')
  llvmopt = os.path.join(options.llvmdir, 'opt')
  outdir = os.path.join(bindir, "_bitcodelibs_/gc_bc")
  ensure_dir_exists(outdir)

  coro_method = options.corodef

  bitcodes = [compile_source(source) for source in sources]

  status = link_all(bitcodes)
  sys.exit(status)
