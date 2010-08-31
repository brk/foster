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


def default_lookup(word, table):
  if word in table:
    return table[word]
  else:
    return word

def elapsed(start, end):
  return int( (end - start) * 1000 )

def elapsed_since(start):
  return elapsed(start, walltime())


class TestFailed(Exception):
  def __init__(self, arglist, path):
    self.arglist = arglist
    self.path = path
  def __str__(self):
    return "Failed to run " + ' '.join(self.arglist) + "\n\tfor test " + self.path

# returns (status, elapsed-time-ms)
def run_command(cmd, paths, testpath, stdout=None, stderr=None, stdin=None, strictrv=True):
  if type(cmd) == str:
    cmd = cmd.split(' ')
  arglist = [default_lookup(arg, paths) for arg in cmd]

  start = walltime()
  rv = subprocess.call( arglist, stdout=stdout, stderr=stderr, stdin=stdin)
  #print ' '.join(arglist) , ' returned rv = ' , rv

  end = walltime()

  if strictrv and rv != 0:
    raise TestFailed(arglist, testpath)
  return (rv, elapsed(start, end))

