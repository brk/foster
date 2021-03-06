#!/usr/bin/env python3

# Copyright (c) 2009 Ben Karel. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt


import sys
import re
import os
import os.path

USAGE = "args: path/to/antlr.jar path/to/output-dir path/to/inputgrammar.g"

def without_ext(name):
  (root, ext) = os.path.splitext(name)
  return root

def invoke_antlr(antlr, outdir, grammarfile):
  """Copies the input grammar to the output directory,
      rewrites it in-place to enable C output,
      and invokes ANTLR on the modified file."""
  import shutil, subprocess
  in_head, in_tail = os.path.split(grammarfile)
  assert in_head != outdir
  assert os.path.isdir(outdir)

  output_file = os.path.join(outdir, in_tail)
  copy_and_rewrite(grammarfile, output_file, uncomment_language_C)

  cmd = "java -cp %s org.antlr.Tool %s" % (antlr, output_file)
  subprocess.call(cmd.split(" "))

  # ANTLR 3.2 is naughty and spits out <grammar>.tokens
  # in the cwd, but we don't need to keep it around.
  tokens_file = without_ext(in_tail)+".tokens"
  if os.path.exists(tokens_file):
    os.remove(tokens_file)

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
    print(USAGE)
    sys.exit(1)
  invoke_antlr(sys.argv[1], sys.argv[2], sys.argv[3])

