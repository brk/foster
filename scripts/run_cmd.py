#!/usr/bin/env python

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
  rv = subprocess.call(cmd, stdout=stdout, stderr=stderr, stdin=stdin)
  end = walltime()

  cmdline = ' '.join(cmd)
  if not stdin is None:
    cmdline += " < " + stdin.name
  if not stdout is None:
    cmdline += " > " + stdout.name

  if showcmd:
      print "::^^^::", cmdline

  return (rv, elapsed(start, end))

#############################

class TestFailed(Exception):
  def __init__(self, cmdline, path):
    self.cmdline = cmdline
    self.path = path
  def __str__(self):
    return "Failed to run " + self.cmdline + "\n\tfor test " + self.path

def default_lookup(word, table):
  if word in table:
    return table[word]
  else:
    return word

# returns (status, elapsed-time-ms)
def run_command(cmd, paths, testpath, showcmd=False, stdout=None, stderr=None, stdin=None, strictrv=True):
  if type(cmd) == str:
    cmd = cmd.strip().split(' ')
  arglist = [default_lookup(arg, paths) for arg in cmd]

  (rv, ms) = run_cmd(arglist, stdout=stdout, stderr=stderr, stdin=stdin)

  if strictrv and rv != 0:
    raise TestFailed(cmdline, testpath)
  return (rv, ms)
