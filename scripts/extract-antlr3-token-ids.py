#!/usr/bin/env python

import sys
import fileinput
import re
import random

# Simple script to grub through ANTLR3C's generated output
# and extract the mapping between token names and numbers.

def collectTokenIdPairs():
  pairs = []
  for line in fileinput.input():
    m = re.match(r"#define ([^ ]+) +(\d+)", line)
    if m:
      pairs.append( (m.group(1), m.group(2)) )
  return pairs

def formatHaskellTokenDef(pair):
  return "tok_%s = %s" % pair

def printHaskellTokenDefs(pairs):
  for p in pairs:
    print formatHaskellTokenDef(p)

  print
  print "tokNameOf id ="
  print "  case id of"
  for p in pairs:
    nm, num = p
    print '    %s -> "%s"' % (num, nm)
  print '    _ -> "<unknown token" ++ show id ++ ">"'

if __name__ == "__main__":
  print "module FosterTokens where"
  print
  printHaskellTokenDefs(collectTokenIdPairs())

