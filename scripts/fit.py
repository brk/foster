#!/usr/bin/env python3

#---------------------------------------------------------------------------
# Copyright (c) 2013 Ben Karel. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
#---------------------------------------------------------------------------
import numpy as np
import matplotlib.pyplot as plt
from scipy.optimize import curve_fit

import itertools

import fileinput

def lnr(x, a, b, c):
    return a * x + b

def sqr(x, a, b, c):
    return a * x*x + b*x + c

def xpo(x, a, b, c):
    return a * np.exp(b * x) + c

#def nxp(x, a, b, c):
#    return a * np.exp(-b * x) + c

def lgg(x, a, b, c):
    return a * np.log2(b * x) + c

def nln(x, a, b, c):
    return a * x * np.log2(b * x) + c

#def nlg(x, a, b, c):
#    return a * np.log2(-b * x) + c


funcs = [
  (lnr, 'O(n)'),
  (sqr, 'O(n^2)'),
  (xpo, 'O(k^n)'),
  (lgg, 'O(lg n)'),
  (nln, 'O(n lg n)'),
  #(nlg, 'O(-lg n)'),
  #(nxp, 'O(-k^n)'),
]

colors = ['r', 'b', 'g', 'k', 'm', 'c']
color  = 0
def get_next_color():
  global color
  c = colors[color]
  color = (color + 1) % len(colors)
  return c

# xs and ys should be converted to np.array by the caller.
# Returns a list of one or more tuples (f, name, ssqerr, popt)
# corresponding to the best-fitting category, the computed sum-of-squares
# error, and the optimized parameters giving the minimal error.
def find_best_match_and_plot(xs, ys, do_plot=False, show_ssqerr=True):
  results = []
  for (f,name) in funcs:
    try:
      popt, pcov = curve_fit(f, xs, ys)
      #print ("popt = ", popt)
      #print ("pcov = ", pcov)
      errs = np.array([f(x, *popt) for x in xs]) - ys
      ssqerr = sum(errs * errs)
      #if show_ssqerr:
      #  print(name, "\t", popt, "\t", ssqerr)
      results.append( (f,name,ssqerr,popt) )
    except Exception as e:
      print(e)
      print("discarding results for ", name)

  def ssq_of(data): (f,n,s,p) = data; return s

  choices = sorted(results, key=ssq_of)
  if show_ssqerr:
    for x in choices:
      print(x[1], "had sum-of-squares error:", x[2], "with parameters", x[3])

  min_ssqerr = choices[0][2]

  candidates = list(itertools.takewhile(lambda v: v[2] < (3.0 * min_ssqerr + 0.001), choices))

  if do_plot:
    plt.plot(xs, ys, 'ok:', label="Data Points") # o=circle, k=black, :=dotted
    for vals in candidates:
      (f, name, ssqerr, popt) = vals
      c = get_next_color()
      plt.plot(xs, f(xs, *popt), c+'-', label=name + " (%.1e,%.1e,%.1e)" % tuple(popt))

  return candidates

#plt.figure()

#c1 = get_next_color()
#plt.plot(p_x, p_y, c1+'o', label="pd_small")
#find_best_match_and_plot(np.array(p_x), np.array(p_y), c1)

#c2 = get_next_color()
#plt.plot(f_x, f_y, c2+'o', label="pd_foster")
#find_best_match_and_plot(np.array(f_x), np.array(f_y), c2)

#plt.legend(loc='upper left')
#plt.show()

if __name__ == '__main__':
  #xs = [0.01, 0.3, 0.52, 1.3, 1.9, 2.6]
  #ys = [1, 5, 15, 130, 300, 600]

  xs = []
  ys = []
  for line in fileinput.input():
    trimmed = line.strip()
    if trimmed is not "":
      parts = trimmed.split()
      xs.append(float(parts[0]))
      ys.append(float(parts[1]))

  # TODO parse command line arg for --plot to control do_plot.
  do_plot = True

  results = find_best_match_and_plot(np.array(xs), np.array(ys), do_plot)
  if len(results) == 1:
    print("This data seems to clearly be:", results[0][1])
  else:
    print("No categorization was unambiguously best; potential choices included:")
    for x in results:
      print("   ", x[1])

  if do_plot:
    plt.legend(loc='upper left')
    plt.show()