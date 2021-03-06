#!/usr/bin/env python3

# Copyright (c) 2013 Ben Karel. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

# This file also contains a function violin_plot() which is third-party code.

import yaml
import subprocess
from jinja2 import Template
from collections import defaultdict
import itertools
import sys
import re

from optparse import OptionParser

from matplotlib import pyplot, cm
from matplotlib.pyplot import figure, show
from scipy.stats import gaussian_kde
from numpy import arange
from matplotlib.font_manager import FontProperties

from longest_common_substring import lcs

options = None
tick_width = 10
interactive = True

ignore_third_party = False

todisplay = []

_png_name_id = 0
def gen_png_name():
  global _png_name_id
  _png_name_id += 1
  return "out_%d.png" % _png_name_id

def testfrag_to_pathfrag(testfrag):
  return testfrag.replace('/', '__')

def load(jsonpath):
  with open(jsonpath, 'r') as jsonfile:
    return yaml.safe_load(jsonfile)

def partition_into(lst, size):
  """Splits |lst| into a sequence of sublists of length at most |size|."""
  return [lst[i:i+size] for i in range(0, len(lst), size)]

def matches(needle, haystack):
  return needle in haystack

def matches_any(subj, needles):
  for needle in needles:
    if matches(needle, subj):
      return True
  return False

def should_consider(test):
  if len(options.tests) > 0:
    if not matches_any(test['test'], options.tests):
      print("dropping ", test['test'], " for not matching ", options.tests)
      return False
  if len(options.tags) > 0:
    if not matches_any(test['tags'], options.tags):
      print("dropping ", test['test'], test['tags'], " for not matching ", options.tags)
      return False
  if len(options.argstrs) > 0:
    if not matches_any(test['input'], options.argstrs):
      return False
  if ignore_third_party and matches_any(test['test'], ["third_party/"]):
    return False
  return True

def collect_relevant_tests(all_tests):
  tests = []
  for test in all_tests:
    #print_test(test)
    if should_consider(test):
      tests.append(test)
  return tests

# For example, go from
#{
#  "test":"speed/shootout/nbody-loops-inlined",
#  "input":"200000",
#  "py_run_ms":[...],
#  "flags":{...},
#  "tags":"[inline=yes,LLVMopt=O2,abc=unsafe,donate=yes]"
#}
# to
# {
#  "test":"speed/shootout/nbody-loops-inlined",
#  "samples":[{"input":"200000",
#              "outputs": { "py_run_ms":[...], ... },
#             }],
#  "flags":{...},
#  "tags":"[inline=yes,LLVMopt=O2,abc=unsafe,donate=yes]"
# }
def coalesce_tests_inputs(raw_tests):
  test_d = {}
  for test in raw_tests:
    key = test['test'] + test['tags']
    if not key in test_d:
      test_d[key] = {
        'test' : test['test'],
        'tags' : test['tags'],
        'flags': test['flags'],
        'samples' : []
      }
    #print test
    if 'outputs' in test:
      sample = {
        'input'     : test['input'],
        'outputs'   : test['outputs'],
      }
    else:
      sample = {
        'input'     : test['input'],
        'outputs'   : { 'py_run_ms' : test['py_run_ms'] },
      }

    test_d[key]['samples'].append(sample)

  tests = []
  for k in test_d:
    tests.append(test_d[k])
  return tests

def print_test(test):
  samples = test['samples']
  print(test['test'], test['tags'])
  for sample in samples:
    print("\t", "input:", sample['input'])
    print("\t", "metrics:", list(sample['outputs'].keys()))

def append_to(arr, key, val):
  if not key in arr:
    arr[key] = []
  arr[key].append(val)

def coalesce_tests(raw_tests):
  t1 = coalesce_tests_inputs(raw_tests)
  if options.group_by_name:
    byname = {}
    for t in t1:
      name = t['test']
      appended = False
      for test_shortname in options.tests:
        if matches(test_shortname, name):
          append_to(byname, test_shortname, t)
          appended = True
          break
      if not appended:
        append_to(byname, name, t)
    return { 'byname': byname }
    #for name in byname:
    #  print name
    #  for t in byname[name]:
    #    print_test(t)
    #print ""
  elif options.group_by_tags:
    bytags = {}
    for t in t1:
      tags = t['tags']
      if not tags in bytags:
        bytags[tags] = []
      bytags[tags].append(t)
    return { 'bytags' : bytags }
    #for tag in bytags:
    #  print tag
    #  for t in bytags[tag]:
    #    print_test(t)
    #print ""
  return { 'other' : t1 }

# http://pyinsci.blogspot.com/2009/09/violin-plot-with-matplotlib.html
def violin_plot(ax,data,pos, facecolor='y', bp=False, x_to_scale=False, rugplot=True):
  '''
  create violin plots on an axis
  '''
  global tick_width
  dist = max(pos)-min(pos)
  dist_pos = dist if dist > 0 else pos[0]
  w1 = min(0.30*max(dist,1.0),0.75)
  w2 = tick_width * (2./5.)
  if x_to_scale or bp:
    w = w1
  else:
    w = w2
  #print pos
  #print "dist:", dist
  #print "w1:", w1
  #print "w2:", w2
  #print "dist_pos:", dist_pos

  for d,p in zip(data,pos):
    d = [float(x) for x in d] # kde chokes on ints...
    k = gaussian_kde(d) #calculates the kernel density
    m = k.dataset.min() #lower bound of violin
    M = k.dataset.max() #upper bound of violin
    x = arange(m,M,(M-m)/100.) # support for violin
    v = k.evaluate(x) #violin profile (density curve)
    v = v/v.max()*w #scaling the violin to the available space
    ax.fill_betweenx(x,p,v+p,facecolor=facecolor,alpha=0.3)
    ax.fill_betweenx(x,p,-v+p,facecolor=facecolor,alpha=0.3)
    if rugplot:
      # plot translucent horizontal lines at each datapoint.
      ax.plot([p for z in d], d, 'k_', markersize=10, alpha=0.5)
    if bp:
      #ax.boxplot(data,notch=True,positions=[p], vert=True)
      ax.boxplot(d,notch=True,positions=[p], vert=True)
      #ax.boxplot(d, positions=pos)
    if bp or rugplot:
      # plot invisible points at the corners of the violins,
      # because otherwise the fill_between colored area will be cut off
      # when matplotlib "focuses" on the box/rug plot markers.
      ax.plot([p+w, p+w, p-w, p-w], [m,M,m,M], 'b.', markersize=0, alpha=1)

def proj(objs, key):
  return [obj[key] for obj in objs if key in obj]

def viz_datasets(datasets, x_positions, title, legend_labels=[], xlabels=[], outfile=None, noshow=False):
  pyplot.rc('font', size=10)
  if len(xlabels) > 6:
    w,h = (10,6)
  else:
    w,h = (8,6)
  fig=figure(figsize=(w,h))
  ax = fig.add_subplot(111)
  ax.set_position([0.1,0.12,0.89,0.7])

  do_boxplot = False
  x_to_scale = False
  legend_boxes = [None for x in legend_labels]
  for ds in datasets:
    color = colorfor(indexof_v01(ds['label'], legend_labels), ds['test'])
    violin_plot(ax, ds['data'], ds['pos'], color, do_boxplot, x_to_scale)

    idx = legend_labels.index(ds['label'])
    if legend_boxes[idx] == None:
      rect = pyplot.Rectangle((0, 0), 1, 1, fc=color)
      legend_boxes[idx] = rect

  #ax.set_title(tests[0]['test'])
  ax.set_xlabel('test')
  if options.normalize:
    ax.set_ylabel('runtime (normalized) [py]')
  else:
    ax.set_ylabel('runtime (ms) [py]')
  ax.xaxis.set_ticks(x_positions)
  ax.xaxis.set_smart_bounds(True)
  if xlabels and len(xlabels) > 0:
    def format_axis_label(x):
      return x.replace('speed/shootout', 's/s') \
              .replace('third_party/shootout', 'tp/s')
    ax.set_xticklabels([format_axis_label(x) for x in xlabels])
    pyplot.xticks(rotation=8)
    ax.axes.relim()
    ax.axes.autoscale_view(True,True,True)

  fontP = FontProperties()
  fontP.set_size('small')

  pyplot.figlegend(legend_boxes, legend_labels,
            loc = 'upper right',
            fancybox=True, shadow=True,
            prop = fontP)
  pyplot.margins(0.02, tight=True)

  # change position to not conflict with legend
  # (not supported in my old version of matplotlib)
  #ax.set_title(title, loc='left')

  pyplot.savefig('bench-out.png')
  if outfile:
    pyplot.savefig(outfile)

  if interactive and not noshow:
    show()

def viz(tests):
  # With one test and one input, plot the py_run_ms values against their index.
  # With one test and multiple integer inputs, plot the py_run_ms values against the input.
  # With multiple tests and one input, show (independent) violin plots for each test.
  # With multiple tests and multiple inputs, show (independent) violin plots for the .
  if len(tests) == 1 and False:
    if len(tests[0]['samples']) == 1:
      print("one test, one input")
      pos  = [1]
      data = [tests[0]['samples'][0]['outputs']['py_run_ms']]

      with open('tmp.txt', 'w') as f:
        for x in data[0]:
          f.write(str(x) + '\n')
      subprocess.call("ministat tmp.txt ; rm tmp.txt", shell=True)

      fig=figure()
      ax = fig.add_subplot(111)
      violin_plot(ax,data,pos,bp=False)
      show()

    else:
      print("one test, multiple (integer?) inputs")
      # TODO: infer program growth order?

      pos  = [int(x) for x in proj(tests[0]['samples'], 'input')]
      data = proj(tests[0]['samples']['outputs'], 'py_run_ms')

      with open('tmp1.txt', 'w') as f:
        for x in data[0]:
          f.write(str(x) + '\n')
      with open('tmp2.txt', 'w') as f:
        for x in data[1]:
          f.write(str(x) + '\n')
      subprocess.call("ministat tmp1.txt tmp2.txt ; rm tmp*.txt", shell=True)

      fig=figure()
      ax = fig.add_subplot(111)
      violin_plot(ax,data,pos,bp=False)
      ax.set_title(tests[0]['test'])
      ax.set_xlabel('input')
      ax.set_ylabel('runtime (ms) [py]')
      ax.xaxis.set_ticks(pos)
      show()
  else:
    viz_multiple_tests(tests)

def intersection_of_sets(sets):
  return set.intersection(*sets)

def union_of_sets(sets):
  return set.union(*sets)

def is_c_code(testname):
  return testname.startswith('third_party')

def colorfor(v_0_1, testname):
  if True:
    if is_c_code(testname):
      return cm.spectral(v_0_1)
    else:
      return cm.spectral(v_0_1)
  else:
    if is_c_code(testname):
      return cm.winter(v_0_1)
    else:
      return cm.autumn(v_0_1)

def interesting_ministat_flags(f):
  mustbe = [
             ('LLVMopt', 'O2'),
           ]
  for (k, v) in mustbe:
    if k in f and not f[k] == v:
      return False
  return True

def reformat_ministat_output(lines):
  labels = {}
  labellines = []
  x = 0
  # collect labels
  while True:
    line = lines[x]
    x += 1
    if line.startswith('+-'):
      break
    labellines.append(line)
    labels[line[0]] = line

  plotlines = [lines[x - 1]]
  while True:
    line = lines[x]
    x += 1
    plotlines.append(line)
    if line.startswith('+-'):
      break

  o = ''
  o += ''.join(plotlines)

  header = lines[x]
  x += 1
  refline = lines[x]
  x += 1
  o += ''.join([header, labellines[0], refline, '.'*40 + '\n'])
  label = 1
  while True:
    if x >= len(lines):
      break
    stats = lines[x]
    verdict = lines[x + 1]
    x += 2
    o += ''.join([labellines[label], stats])
    if verdict.startswith('Difference at'):
      absdiff = lines[x]
      reldiff = lines[x + 1]
      pooled  = lines[x + 2]
      x += 3
      o += verdict.strip() +  ' '*50 + reldiff
    else:
      o += ' '*82 + verdict
    o += '.'*40 + '\n'
    label += 1

  return o


def collect_ministat_output(all_fnames):
  o = ""
  # Ministat can only handle a limited number of comparisons.
  # If we have too many for it to handle in one go, give it a few at a time,
  # always using the same element as the first (anchor/baseline) result.
  for tail_fnames in partition_into(all_fnames[1:], 6):
    fnames = [all_fnames[0]] + tail_fnames
    subprocess.call("ministat %s > ministat_out.txt" % ' '.join(fnames), shell=True)
    o += reformat_ministat_output(open('ministat_out.txt', 'r').readlines())
  #print o
  return o

def elapsed_runtime_ms(stats):
  outputs = stats['outputs']
  if 'Elapsed_runtime_ms' in outputs:
    return outputs['Elapsed_runtime_ms']
  if 'py_run_ms' in outputs:
    return outputs['py_run_ms']
  raise "Unable to get elapsed runtime from " + str(stats)

def viz_multiple_tests(unsorted_tests):
  tests = sorted(unsorted_tests, key=lambda t: t['test'])
  names = set(t['test'] for t in tests)

  inputs = [set(proj(t['samples'], 'input')) for t in tests]
  common_inputs = intersection_of_sets(inputs)
  dropped_inputs = union_of_sets(inputs) - common_inputs
  #print "common inputs:", common_inputs
  if len(dropped_inputs) > 0:
    print("dropped inputs: ", dropped_inputs)
  # same test, different tags: take intersection of inputs

  if len(common_inputs) == 0:
    print("Skipping tests", names, "because there were no common inputs.")
    return

  #pos  = [int(x) for x in common_inputs]
  datas = [
            [elapsed_runtime_ms(t['samples'][n]) for n in range(len(t['samples']))
                             if t['samples'][n]['input'] in common_inputs]
            for t in tests
          ]

  assert len(datas) == len(tests)
  ministat_outputs = []
  for n in range(len(common_inputs)):
    fnames = []
    for k in range(len(tests)):
      t = tests[k]
      # Only give ministat interesting tests if there are too many overall.
      if len(tests) >= 7 and not interesting_ministat_flags(t['flags']):
        continue
      fname = 'tmp_%s_%s.txt' % (testfrag_to_pathfrag(t['test']), t['tags'])

      # Put c code at the front of the list so that ministat uses it as baseline.
      if is_c_code(t['test']):
        if t['flags'].get('LLVMopt', 'O0') != 'O0':
          fnames.insert(0, fname)
        else:
          fnames.insert(1, fname)
      else:
        fnames.append(fname)

      with open(fname, 'w') as f:
        for x in datas[k][n]:
          f.write(str(x) + '\n')
    minioutput = collect_ministat_output(fnames)
    ministat_outputs.append({'n':n, 'output':minioutput})
    subprocess.call("rm ministat_out.txt tmp_*.txt", shell=True)

  assert len(ministat_outputs) == len(common_inputs)

  unique_test_names = set(proj(tests, 'test'))
  pos_for_test_names = compute_positions_for_names(unique_test_names, list(zip(tests, datas)), 'test')
  x_positions = list(pos_for_test_names.values())
  legend_labels = sorted(set(proj(tests, 'tags')))

  if options.normalize:
    # datas :: [[ [sample] ]]
    samples_lists = list(itertools.chain.from_iterable(datas))
    samples       = list(itertools.chain.from_iterable(samples_lists))
    normalize_to_value = float(min(samples))
    datas = [ [ [float(x) / normalize_to_value for x in samples ]
                 for samples in samples_lists] for samples_lists in datas]
  datasets = [
    {
      'data': datas[k],
      'color': colorfor(indexof_v01(tests[k]['tags'], legend_labels), tests[k]['test']),
      'pos': [pos_for_test_names[tests[k]['test']]],
      'label': tests[k]['tags'],
      'test' : tests[k]['test'],
      'tags' : tests[k]['tags'],
    } for k in range(len(tests))
  ]
  todisplay.append({'pos_for_names':pos_for_test_names,
                    'ministat_outputs':ministat_outputs,
                    'datasets':datasets,
                    'legend_labels':legend_labels,
                    'outpng_name':gen_png_name(),
                    'x_positions':x_positions,
                    'title':title_for(legend_labels, tests),
                   })

def viz_by_tags(tagnames, tests):
  datas = [
            [elapsed_runtime_ms(t['samples'][n]) for n in range(len(t['samples']))]
            for t in tests
          ]
  # We don't include any ministat comparisons because
  # comparing results from different tests for the same tags
  # doesn't make any sense! (unlike the reverse situation)
  pos_for_names = compute_positions_for_names(tagnames, list(zip(tests, datas)), 'tags')
  x_positions = list(pos_for_names.values())
  legend_labels = list(set(proj(tests, 'test')))
  datasets = [
    {
      'data': datas[k],
      'color': colorfor(indexof_v01(tests[k]['test'], legend_labels),
                        tests[k]['test']),
      'pos': [pos_for_names[tests[k]['tags']]],
      'label': tests[k]['test'],
      'test' : tests[k]['test'],
      'tags' : tests[k]['tags'],
    } for k in range(len(tests))
  ]
  todisplay.append({'pos_for_names':pos_for_names,
                    'ministat_outputs':[],
                    'legend_labels':legend_labels,
                    'datasets':datasets,
                    'outpng_name':gen_png_name(),
                    'x_positions':x_positions,
                    'title':title_for(legend_labels, tests),
                   })

def title_for(labels, tests):
  valset = {}
  for d in proj(tests, 'flags'):
    for (f, v) in d.items():
      if not f in valset:
        valset[f] = [v]
      elif len(valset[f]) > 1:
        continue
      elif not v in valset[f]:
        valset[f].append(v)
  singletons = {}
  for (k, vs) in valset.items():
    if len(vs) == 1:
      singletons[k] = vs[0]
  cs_tags = ','.join("%s=%s" % (k,v) for (k,v) in singletons.items())
  print("title_for: labels = ", labels)
  title = 'varying: %s [common: %s]' % (testname_of(labels), cs_tags)
  return title

def testname_of(labels):
  if ',' in labels[0] and '@' in labels[0]:
    labelset = set()
    for label in labels:
      labelset = labelset.union(set(re.findall('[,\[]([^=]+)=', label)))
    return ','.join(list(labelset))
  else:
    testname = lcs(labels)
    if testname.startswith('/'):
      testname = testname[1:]
    return testname

def indexof_v01(k, vs):
  return vs.index(k) / float(len(vs))

def display_compiletime_results(all_tests, output_file):
  # Overall/combined compile times
  if True:
    outfile = gen_png_name()
    fig = figure()
    ax1 = fig.add_subplot(111)

    fos_opt_O0 = []
    fos_opt_O2 = []
    oth_opt_O0 = []
    oth_opt_O2 = []
    for t in all_tests:
      if 'compile' in t:
        if t['flags']['lang'] == 'foster' and t['flags']['LLVMopt'] == 'O0':
          fos_opt_O0.append(t['compile'])
        if t['flags']['lang'] == 'foster' and t['flags']['LLVMopt'] == 'O2':
          fos_opt_O2.append(t['compile'])
        if t['flags']['lang'] != 'foster':
          if ('LLVMopt' in t['flags'] and t['flags']['LLVMopt'] == 'O0') \
              or ('opt' in t['flags'] and t['flags']['opt'] == 'O0'):
            oth_opt_O0.append(t['compile'])
          if ('LLVMopt' in t['flags'] and t['flags']['LLVMopt'] == 'O2') \
              or ('opt' in t['flags'] and t['flags']['opt'] == 'O2'):
            oth_opt_O2.append(t['compile'])

    ax2 = ax1.twinx()

    lA = ax1.scatter(proj(fos_opt_O0, 'num_lines'),
                proj(fos_opt_O0, 'all_lines_per_s'), s=10, c='#0000ff', marker="s")
    lB = ax1.scatter(proj(fos_opt_O2, 'num_lines'),
                proj(fos_opt_O2, 'all_lines_per_s'), s=10, c='#ff0000', marker="s")
    lC = ax2.scatter(proj(oth_opt_O0, 'num_lines'),
                proj(oth_opt_O0, 'all_lines_per_s'), s=10, c='#8899ff', marker="o")
    lD = ax2.scatter(proj(oth_opt_O2, 'num_lines'),
                proj(oth_opt_O2, 'all_lines_per_s'), s=10, c='#ff9988', marker="o")

    ax1.set_xlabel('number of lines input to compiler')
    ax1.set_ylabel('lines-per-second throughput')

    pyplot.ylim(ymin=0)

    # We need to manually/explicitly put legends like this, because the
    # autogenerated legend only picks up the second axis's values.
    pyplot.legend([lA, lB, lC, lD],
      ['O0, no inlining',
       'O2, with inlining',
       'O0',
       'O2'], loc='upper right') # framealpha=0.6

    pyplot.savefig(outfile)
    print(Template("""
      <center><h3>{{ title }}</h3></center>
      <img src="{{ outpng_name }}"/>
      """).render( { 'outpng_name' : outfile , 'title':'Lines-per-second throughput' } ), file=output_file)

  # Plot by optimization level
  if True:
    outfile = gen_png_name()
    fig = figure()
    ax1 = fig.add_subplot(111)

    fos_opt_O0 = []
    fos_opt_O2 = []
    oth_opt_O0 = []
    oth_opt_O2 = []
    for t in all_tests:
      if 'compile' in t:
        if t['flags']['lang'] == 'foster' and t['flags']['LLVMopt'] == 'O0':
          fos_opt_O0.append(t['compile'])
        if t['flags']['lang'] == 'foster' and t['flags']['LLVMopt'] == 'O2':
          fos_opt_O2.append(t['compile'])

        if t['flags']['lang'] != 'foster':
          if ('LLVMopt' in t['flags'] and t['flags']['LLVMopt'] == 'O0') \
              or ('opt' in t['flags'] and t['flags']['opt'] == 'O0'):
            oth_opt_O0.append(t['compile'])
          if ('LLVMopt' in t['flags'] and t['flags']['LLVMopt'] == 'O2') \
              or ('opt' in t['flags'] and t['flags']['opt'] == 'O2'):
            oth_opt_O2.append(t['compile'])

    ax1.scatter(proj(fos_opt_O0, 'num_lines'),
                proj(fos_opt_O0, 'mid_total_ms'), s=10, c='#0000ff', marker="s", label='O0, no inlining')
    ax1.scatter(proj(fos_opt_O2, 'num_lines'),
                proj(fos_opt_O2, 'mid_total_ms'), s=10, c='#ff0000', marker="s", label='O2, with inlining')
    ax1.scatter(proj(oth_opt_O0, 'num_lines'),
                proj(oth_opt_O0, 'all_total_ms'), s=10, c='#3344aa', marker="o", label='O0')
    ax1.scatter(proj(oth_opt_O2, 'num_lines'),
                proj(oth_opt_O2, 'all_total_ms'), s=10, c='#aa4433', marker="o", label='O2')

    ax1.set_xlabel('number of lines input to compiler')
    ax1.set_ylabel('compilation time (ms)')

    pyplot.ylim(ymin=0)
    pyplot.legend(loc='upper left')

    pyplot.savefig(outfile)
    print(Template("""
      <center><h3>{{ title }}</h3></center>
      <img src="{{ outpng_name }}"/>
      """).render( { 'outpng_name' : outfile , 'title':'Inlining+O2 compile time' } ), file=output_file)

def display_results(output_file):
  print("""
    <p>Command line: <pre>%s</pre></p>
  """ % ' '.join(sys.argv), file=output_file)
  format_output(todisplay, output_file)

def format_output(outputs, output_file):
  for o in outputs:
    xaxis_labels  = list(o['pos_for_names'].keys())
    #for mo in o['ministat_outputs']:
    #  print mo['output']
    viz_datasets(o['datasets'], o['x_positions'], o['title'],
                 o['legend_labels'], xaxis_labels,
                 o['outpng_name'], noshow=True)

  print(Template( """
    {% for o in outputs %}
      <center><h3>{{ o.title }}</h3></center>
      <img src="{{ o.outpng_name }}"/>
      {% for mo in o.ministat_outputs %}
      <pre>{{ mo.output }}</pre><br>
      {% endfor %}
      <br>
    {% endfor %}
""").render(outputs=outputs), file=output_file)

def compute_positions_for_names(names, testsdatas, key):
  """Given a list of (distinct) names,
     and statistics corresponding to those names,
     returns a dict mapping names to positions."""
  # compute the maximum sample for each name,
  # which we will use to assign positions.
  maxes = {}
  for (t,d) in testsdatas:
    m = max(max(xs) for xs in d)
    maxes[t[key]] = max(m, maxes.get(t[key], m))
  sorted_pairs = sorted(list(maxes.items()), key=lambda p: p[1], reverse=True)
  sorted_names = [p[0] for p in sorted_pairs]
  assert set(sorted_names) == set(names)

  global tick_width
  k = 1
  pos_for_test_names = {}
  for utn in sorted_names:
    pos_for_test_names[utn] = k * tick_width
    k += 1
  return pos_for_test_names

def print_tests(tests):
  for test in tests:
    print_test(test)

# d should be either a list of dicts containing key t,
# or a dict recursively containing (eventually)
# lists of dicts containing key t.
# if t is a list like [t1, t2, t3],
# this function will return a value equivalent to
# organize_by(organize_by(organize_by(d, t1), t2), t3)
def organize_by(d, t):
  if type(t) == list:
    r = d
    for v in t:
      r = _organize_by(r, v)
    return r
  else:
    return _organize_by(d, t)

def _organize_by(d, t):
  if type(d) == list:
    r = {}
    for v in d:
      assert t in v
      k = v[t]
      if not k in r:
        r[k] = []
      r[k].append(v)
    return r
  elif type(d) == dict:
    r = {}
    for k,v in d.items():
      r[k] = _organize_by(v, t)
    return r
  else:
    raise "Unknown type for "

def give_overview(all_tests):
  raw_tests = collect_relevant_tests(all_tests)
  d = organize_by(raw_tests, ['test', 'tags'])
  last_tst = None
  for tst, rst in d.items():
    for tgs, rst2 in rst.items():
      if tst == last_tst:
        ptst = ' '*len(tst)
      else:
        ptst = tst
      print(ptst, tgs, {'inputs': proj(rst2, 'input')})
      last_tst = tst

def accumulate_results(all_tests):
  raw_tests = collect_relevant_tests(all_tests)
  organized = coalesce_tests(raw_tests)
  # organized is a dict with one key: 'byname', 'bytags', or 'other'
  # 'byname' and 'bytags' map to a dict; 'other' maps to a list.
  if 'other' in organized:
    tests = organized['other']
    print_tests(tests)
    viz(tests)
  elif 'byname' in organized:
    byname = organized['byname']
    for name in byname:
      print(name)
      tests = byname[name]
      print_tests(tests)
      print()
      viz(tests)
  elif 'bytags' in organized:
    bytags = organized['bytags']
    nontrivials = {}
    for tags in bytags:
      print('tags:', tags)
      tests = bytags[tags]
      print_tests(tests)
      if len(tests) > 1:
        nontrivials[tags] = tests
    tagnames = list(nontrivials.keys())
    tests = []
    for tagtests in list(nontrivials.values()):
      tests.extend(tagtests)
    if len(tests) > 0:
      viz_by_tags(tagnames, tests)
    else:
      print("No tags had more than one associated test!")
  else:
    print("organized by '%s', not sure what to do!" % str(organized))

def get_test_parser(usage):
  parser = OptionParser(usage=usage)
  parser.add_option("--test", action="append", dest="tests", default=[],
                    help="Consider only these tests by (substring of) name.")
  parser.add_option("--tags", action="append", dest="tags", default=[],
                    help="Consider only these tags (key-value pairs)")
  parser.add_option("--group-by-tags", action="store_true", dest="group_by_tags", default=False,
                    help="TODO")
  parser.add_option("--group-by-name", action="store_true", dest="group_by_name", default=False,
                    help="TODO")
  parser.add_option("--argstr", action="append", dest="argstrs", default=[],
                    help="Consider only tests with these argstrs")
  parser.add_option("--format", action="store", dest="format", default=None,
                    help="Output format (eventually: html, png, txt, ...). Currently unimplemented.")
  parser.add_option("--normalize", action="store_true", dest="normalize", default=False,
                    help="Whether to use normalized instead of absolute measurements in graphs.")
  # Note: normalization doesn't apply to ministat output, for example...
  parser.add_option("--overview", action="store_true", dest="overview", default=False,
                    help="Give an overview of what tests & tags have timings available.")
  parser.add_option("--compiletime", action="store_true", dest="compiletime", default=False,
                    help="Include a graph of compile times and lines-per-second metrics")
  return parser

def use_default_options():
  return options.tests == [] and options.tags == [] and options.argstrs == []

def set_default_options():
  options.tests = ['spectralnorm', 'fannkuchredux', 'nbody', 'addtobits', 'siphash',
                   'mandelbrot', 'binarytrees']
  options.group_by_name = True

if __name__ == "__main__":
  parser = get_test_parser("""usage: %prog [options] <bench_data_paths>

  The input paths should be paths to the all_timings.json generated by running
  bench-all.py. At least one input file is required.

  Use --test and --tags to select a subset of the input results to view.
  (Use --overview to get a list of what is available). --test can be given
  multiple times.

  With a single input file, you can compare the performance metrics of
  a given set of tests as the optimization levels or flags (tags) vary.

  Inspecting multiple tests with a constant tag is useful for comparing
  alternative implementations of the same algorithm.

  With --group-by-name, each test name substring will generate a separate
  graph of all the tests that match that substring. The x-axis will be
  tests, and there will be separate labels for each tag.

  Without --group-by-name, all the tests will generate a common graph,
  but there must be common inputs -- otherwise, no graph will be generated.

  With --group-by-tags, the roles of x-axis and labels will be switched:
  tests become labels, and tags are put on the x-axis.
""")
  (options, args) = parser.parse_args()

  assert len(args) > 0
  all_tests = list(itertools.chain.from_iterable(list(map(load, args))))

  if options.overview:
    give_overview(all_tests)
  else:
    if len(args) > 1:
      # Comparing multiple runs; toss third party results
      ignore_third_party = True

    if use_default_options():
      set_default_options()

    with open('bench-ized.html', 'w') as output_file:
      accumulate_results(all_tests)
      display_results(output_file)
      display_compiletime_results(all_tests, output_file)
      print("Output written to '%s'" % output_file.name)
