#!/usr/bin/env python

# Copyright (c) 2013 Ben Karel. All rights reserved.
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

class TestFailed(Exception):
  def __init__(self, cmdline, path):
    self.cmdline = cmdline
    self.path = path
  def __str__(self):
    return "Failed to run " + self.cmdline + "\n\tfor test " + self.path

# returns (status, elapsed-time-ms)
def run_command(cmd, showcmd=False, stdout=None, stderr=None, stdin=None):
  if type(cmd) == str:
    cmd = cmd.strip().split(' ')
  arglist = cmd

  start = walltime()
  rv = subprocess.call( arglist, stdout=stdout, stderr=stderr, stdin=stdin)
  end = walltime()

  cmdline = ' '.join(arglist)
  if not stdin is None:
    cmdline += " < " + stdin.name
  if not stdout is None:
    cmdline += " > " + stdout.name

  if showcmd:
      print "::^^^::", cmdline

  return (rv, elapsed(start, end))

#########################################

if __name__ == '__main__':
  cmds = 'pd_pure.exe pd_small.exe pd.foster.exe'.split(' ')
  vals = '100 200 300 400 500 600 700 800 900 1000 1200 1600 2400 3200 4000 4800 5200 5600 6000 6400'.split(' ')
  #vals = '100 200 300 400 500 600 700 800 900'.split(' ')
  results = {}
  for c in cmds:
    for v in vals:
      (r, ms) = run_command("./timeout3 -t 2 silent ./%s %s" % (c, v))
      if r != 0:
        break
      print c, "\t", v, "\t", ms
      results[(c, v)] = ms

  print "=========================="

  def res(cv):
    try:
      return results[cv]
    except:
      return ""

  for c in cmds:
    print "\t", c,
  print

  for v in vals:
    print v,
    for c in cmds:
      print "\t", res((c,v)),
    print

