#!/usr/bin/env python

# Copyright (c) 2009 Ben Karel. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

from __future__ import with_statement
import sys
import re
import os
import os.path

USAGE = "args: path/to/antlr.jar path/to/output-dir path/to/inputgrammar.g"

def without_ext(name):
  (root, ext) = os.path.splitext(name)
  return root

def invoke_antlr(antlr, output, input):
  """Copies the input grammar to the output directory,
      rewrites it in-place to enable C output,
      and invokes ANTLR on the modified file."""
  import shutil
  in_head, in_tail = os.path.split(input)
  assert in_head != output

  ensure_dir_exists(output)

  output_file = os.path.join(output, in_tail)
  copy_and_rewrite(input, output_file, uncomment_language_C)

  print "run_antlr.py: Using %s to process %s" % (antlr, output_file)

  cmd = "java -cp %s org.antlr.Tool %s" % (antlr, output_file)
  arglist = cmd.split(" ")
  print cmd
  import subprocess
  subprocess.call(arglist)

  # ANTLR 3.2 is naughty and spits out <grammar>.tokens
  # in the cwd, but we don't need to keep it around.
  os.remove(without_ext(in_tail)+".tokens")

def ensure_dir_exists(output):
  """Creates the given directory if it doesn't exist;
      if the name refers to a path, prints an error and aborts."""
  if not os.path.exists(output):
    os.mkdir(output)
  elif not os.path.isdir(output):
    print "Error: %s must be a directory!" % output
    sys.exit(1)

def uncomment_language_C(line):
  """Replaces '//language = C' with 'language = C',
      leaving all other lines alone."""
  if re.match(r"\s*//\s*language\s*=\s*C;\s*", line):
    return re.sub(r"//", '  ', line)
  else:
    return line

def copy_and_rewrite(input, output, translate):
  """Copies input to output, running each line through translate()"""
  with open(input) as infile:
    with open(output, 'w+') as outfile:
      for line in infile:
        outfile.write(translate(line))

if __name__  == '__main__':
  if len(sys.argv) != 4:
    print USAGE
    sys.exit(1)
  invoke_antlr(sys.argv[1], sys.argv[2], sys.argv[3])

