#!/usr/bin/env python3

# Copyright (c) 2010 Ben Karel. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

import os
import subprocess
import time

if os.name == 'nt':
  walltime = time.clock
else:
  walltime = time.time

def elapsed(start, end):
  return int( (end - start) * 1000 )

def elapsed_since(start):
  return elapsed(start, walltime())

# returns (status, elapsed-time-ms)
def run_cmd(cmd, showcmd=False, stdout=None, stderr=None, stdin=None):
  if type(cmd) == str:
    cmd = cmd.strip().split(' ')

  start = walltime()
  rv = 1
  proc = None
  try:
    proc = subprocess.Popen(cmd, stdout=stdout, stderr=stderr, stdin=stdin)
    rv = proc.wait()
  except KeyboardInterrupt as e:
    proc.terminate()
    raise e
  except OSError:
    print(": error: Unable to execute ", cmd)
    raise
  end = walltime()

  cmdline = ' '.join(cmd)
  if not stdin is None:
    cmdline += " < " + stdin.name
  if not stdout is None:
    cmdline += " > " + stdout.name

  if showcmd:
      print("::^^^::", cmdline)

  return (rv, elapsed(start, end))

#############################

class TestFailed(Exception):
  def __init__(self, cmdline, path):
    self.cmdline = cmdline
    self.path = path
  def __str__(self):
    return "Failed to run " + self.cmdline + "\n\tfor input file " + self.path

def default_lookup(word, table):
  if word in table:
    return table[word]
  else:
    return word

# returns (status, elapsed-time-ms)
def run_command(rawcmd, paths, inputfile, showcmd=False, stdout=None, stderr=None, stdin=None, strictrv=True):
  if type(rawcmd) == str:
    rawcmd = rawcmd.strip().split(' ')
  cmd = [default_lookup(arg, paths) for arg in rawcmd]

  (rv, ms) = run_cmd(cmd, showcmd=showcmd, stdout=stdout, stderr=stderr, stdin=stdin)

  if strictrv:
    if rv != 0:
      if showcmd is False and (stderr is not None):
        print("((stderr has been redirected to ", stderr)
        print("  use --show-cmdlines to disable redirection))")
      print("Failed to run:")
      print("     ", ' '.join(cmd))
      raise TestFailed(cmd, inputfile)
    else:
      return ms
  return (rv, ms)
