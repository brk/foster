#!/usr/bin/env python

# A simple script to compare opcode mix logs generated from pin.

from collections import defaultdict
import math
import sys

# Based on code from http://bytes.com/topic/python/answers/164802-human-readable-number-formatting
def human_readable(n):
  '''Return a human friendly approximation of n, using SI prefixes'''
  if n == 0:
    return '0'
  else:
    prefixes = ['','k','M','G','T']
    order = int(round(math.log(n, 10))) // 3
    return '%.1f %s' % (float(n)/10**(order*3), prefixes[order])

print_star_props = True
print_missing    = True
ratio_threshold = 10
abs_threshold   = 10000000

def parse_opcodemix(p):
  d = defaultdict(int)

  for line in file(p).readlines():
    parts = line.split()
    if len(parts) == 4 and parts[0] != '#':
      opcode, name, count_unpredicated, count_predicated = line.split()
      d[name] = count_unpredicated

  return d

def maxratio(x, y):
  if x == 0 and y == 0:
    return 0
  if x == 0:
    return x/y
  if y == 0:
    return y/x
  return max(x/y, y/x)

def compare_opcodemixes(p1, p2):
  m1 = parse_opcodemix(p1)
  m2 = parse_opcodemix(p2)

  print "{0:8s} {1:16s}\t{2:16s}".format('', p1, p2)
  print "{0:16s} {1:16s} {2:19s} {3:14s} {4:11s}".format("opcode", 'file 1', 'file 2', 'diff', 'ratio')

  allkeys = set(m1.keys() + m2.keys())
  print_key = {}
  for k in allkeys:
    try:
      v1 = int(m1[k])
      v2 = int(m2[k])
    except:
      print k, ':', m1[k]
      continue

    should_print = False

    if ((v1 == 0) != (v2 == 0)) and print_missing:
      should_print = True

    elif k[0] == '*' and print_star_props:
      should_print = True

    elif abs(v2 - v1) >= abs_threshold:
      should_print = True

    elif not v2 == 0:
      ratio = v1 / v2
      should_print = (ratio > ratio_threshold or ratio < (1/ratio_threshold))

    print_key[k] = should_print

  def show(k):
     v1, v2 = int(m1[k]), int(m2[k])
     print "{0:16s} {1:16s} {2:16s} {3:11d} {4:11d}".format(k, human_readable(v1), human_readable(v2), v2 - v1, maxratio(v1, v2))

  for k in [k for k in print_key if print_key[k]]:
    if not k[0] == '*':
      show(k)

  for k in [k for k in print_key if print_key[k]]:
    if    k[0] == '*':
      show(k)

assert len(sys.argv) == 3
f1 = sys.argv[1]
f2 = sys.argv[2]

compare_opcodemixes(f1, f2)
