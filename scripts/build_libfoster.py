#!/usr/bin/env python

# Copyright (c) 2009 Ben Karel. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

from __future__ import with_statement
import sys
import re
import os
import os.path
import subprocess
import shutil

clang = "<llvm compiler not set>"
bindir = "<bindir not set>"
outdir = "<outdir not set>"

def ensure_dir_exists(output):
  """Creates the given directory if it doesn't exist;
      if the name refers to a path, prints an error and aborts."""
  if not os.path.exists(output):
    os.mkdir(output)
  elif not os.path.isdir(output):
    print "Error: %s must be a directory!" % output
    sys.exit(1)

def transplant(path, newdir):
  """Given '/some/path/to/file.txt'  and  '/some/new/dir',
     returns '/some/new/dir/file.txt'."""
  head, tail = os.path.split(path)
  return os.path.join(newdir, tail)

def compile_source(src):
  outbc = re.sub('\.cpp$', '.bc', transplant(src, outdir))
  incdir = os.path.join(srcdir, 'runtime', 'gc')
  cmd = "%s %s -I %s -emit-llvm -c -o %s" % (clang, src, incdir, outbc)
  print cmd
  subprocess.call(cmd.split(" "))
  return outbc

def link_all(bcs):
  outbc = os.path.join(bindir, "libfoster.bc")
  cmd = "%s %s -link-as-library -o %s" % (llvmld, " ".join(bcs), outbc)
  print cmd
  subprocess.call(cmd.split(" "))

if __name__ == '__main__':
  clang  = sys.argv[1]
  srcdir = sys.argv[2]
  bindir = sys.argv[3]
  llvmld = os.path.join(sys.argv[4], 'llvm-ld')
  outdir = os.path.join(bindir, "gc_bc")
  ensure_dir_exists(outdir)

  sources = sys.argv[5:]

  bitcodes = [compile_source(source) for source in sources]

  link_all(bitcodes)
