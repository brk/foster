#!/usr/bin/env python3

# A simple script to compare opcode mix logs generated from pin.

from collections import defaultdict
import math
import sys

from optparse import OptionParser

# Based on code from http://bytes.com/topic/python/answers/164802-human-readable-number-formatting
def human_readable(n):
  '''Return a human friendly approximation of n, using SI prefixes'''
  if n == 0:
    return '0'
  else:
    prefixes = ['','k','M','G','T']
    order = int(round(math.log(n, 10))) // 3
    return '%.1f %s' % (float(n)/10**(order*3), prefixes[order])

def parse_opcodemix(p):
  d = defaultdict(int)

  for line in file(p).readlines():
    parts = line.split()
    if len(parts) == 4 and parts[0] != '#':
      opcode, name, count_unpredicated, count_predicated = line.split()
      d[name] = count_unpredicated

  return d

def divzero(x, y):
  if y == 0:
    return 0.0
  return float(x)/float(y)

def maxratio(x, y):
  return max(divzero(x,y), divzero(y,x))

def classify_keys(print_key, m1, m2):
  num_identical  = 0
  num_trivial    = 0
  num_nontrivial = 0

  for k in print_key:
    v1 = int(m1[k])
    v2 = int(m2[k])
    if v1 == v2:
      num_identical += 1
    elif print_key[k]:
      num_nontrivial += 1
    else:
      num_trivial += 1
  return (num_identical, num_trivial, num_nontrivial)

def compare_opcodemixes(p1, p2, options):
  m1 = parse_opcodemix(p1)
  m2 = parse_opcodemix(p2)

  allkeys = set(list(m1.keys()) + list(m2.keys()))
  print_key = {}
  for k in allkeys:
    try:
      v1 = int(m1[k])
      v2 = int(m2[k])
    except:
      print(k, ':', m1[k])
      continue

    should_print = False

    if ((v1 == 0) != (v2 == 0)) and options.print_missing:
      should_print = True

    elif (abs(v2 - v1) >= options.abs_threshold) and \
         (v2 == 0 or maxratio(v1, v2) > 1.0001):
      should_print = True

    elif not v2 == 0:
      ratio = maxratio(v1, v2)
      should_print = ratio > options.ratio_threshold

    print_key[k] = should_print

  (num_identical, num_trivial, num_nontrivial) = classify_keys(print_key, m1, m2)

  if num_nontrivial > 0:
    print("{0:8s} {1:16s}\t{2:16s}".format('', p1, p2))
    print("{0:16s} {1:16s} {2:16s} {3:11s} {4:11s}".format("opcode", 'file 1', 'file 2', '    diff', '   maxratio'))

    def show(k):
       v1, v2 = int(m1[k]), int(m2[k])
       diff = v2 - v1
       print("{0:16s} {1:16s} {2:16s} {3:11d} {4:11f}".format(k, human_readable(v1), human_readable(v2), diff, maxratio(v1, v2)))

    for k in [k for k in print_key if print_key[k]]:
      if not k[0] == '*':
        show(k)

    for k in print_key:
      if    k[0] == '*' and (print_key[k] or options.print_star_props):
        show(k)

  if num_nontrivial > 0 or options.summarize:
    print("Pin metrics: %d identical; %d with trivial differences; %d with non-trivial differences" % (num_identical, num_trivial, num_nontrivial))


if __name__ == '__main__':
  parser = OptionParser(usage="""usage: %prog [options] <opcodemix-1.out> <opcodemix-2.out>""")
  parser.add_option("--show-missing", dest="print_missing", action="store_true", default=False,
                    help="Show missing properties")
  parser.add_option("--abs", dest="abs_threshold", action="store", default=100000,
                    help="Use the given value as the threshold of significance in absolute values")
  parser.add_option("--ratio", dest="ratio_threshold", action="store", default=1.005,
                    help="Use the given value as the threshold of significance in ratios")
  parser.add_option("--show-stars", dest="print_star_props", action="store_true", default=False,
                    help="Show Pin's aggregate properties, even when they don't vary")
  parser.add_option("--summarize", dest="summarize", action="store_true", default=False,
                    help="Show a summary line even when there are only trivial differences")

  (options, args) = parser.parse_args()

  compare_opcodemixes(args[0], args[1], options)
