#---------------------------------------------------------------------------
# Copyright (c) 2013 Ben Karel. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
#---------------------------------------------------------------------------
import numpy as np
import matplotlib.pyplot as plt
from scipy.optimize import curve_fit

def lnr(x, a, b, c):
    return a * x + b

def sqr(x, a, b, c):
    return a * x*x + b*x + c

def xpo(x, a, b, c):
    return a * np.exp(b * x) + c

def nxp(x, a, b, c):
    return a * np.exp(-b * x) + c

def lgg(x, a, b, c):
    return a * np.log2(b * x) + c

def nln(x, a, b, c):
    return a * x * np.log2(b * x) + c

def nlg(x, a, b, c):
    return a * np.log2(-b * x) + c


funcs = [
  (lnr, 'O(n)'),
  (sqr, 'O(n^2)'),
  (xpo, 'O(k^n)'),
  (lgg, 'O(lg n)'),
  (nln, 'O(n lg n)'),
  (nlg, 'O(-lg n)'),
  (nxp, 'O(-k^n)'),
]

colors = ['r', 'b', 'g', 'k', 'm', 'c']
color  = 0
def get_next_color():
  global color
  c = colors[color]
  color = (color + 1) % len(colors)
  return c

def find_best_match_and_plot(xs, ys, c, show_ssqerr=False):
  results = []
  for (f,name) in funcs:
    try:
      popt, pcov = curve_fit(f, xs, ys)
      errs = f(xs, *popt) - ys
      ssqerr = sum(errs * errs)
      if show_ssqerr:
        print name, "\t", popt, "\t", ssqerr
      results.append( (f,name,ssqerr,popt) )
    except:
      print "discarding results for ", name

  def ssq_of((f,n,s,p)): return s

  (f,name,ssqerr,popt) = min(results, key=ssq_of)
  plt.plot(xs, f(xs, *popt), c+'-', label=name + " (%.1e,%.1e,%.1e)" % tuple(popt))


#plt.figure()

#c1 = get_next_color()
#plt.plot(p_x, p_y, c1+'o', label="pd_small")
#find_best_match_and_plot(np.array(p_x), np.array(p_y), c1)

#c2 = get_next_color()
#plt.plot(f_x, f_y, c2+'o', label="pd_foster")
#find_best_match_and_plot(np.array(f_x), np.array(f_y), c2)

#plt.legend(loc='upper left')
#plt.show()
