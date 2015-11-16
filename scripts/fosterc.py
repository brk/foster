#!/usr/bin/env python

# Copyright (c) 2010-2015 Ben Karel. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

from __future__ import with_statement

import os
import re
import os.path
import subprocess
import sys
import shutil
import traceback
import math

from run_cmd import *

from optparse import OptionParser

options = None

def progname(inputfile):
  """Given '/path/to/some/test.foster'
        or '/path/to/some/test',       returns 'test'"""
  return os.path.basename(inputfile).replace('.foster', '')

def default_exename(inputfile):
  import platform
  return progname(inputfile) + {
    'Darwin': "",
    'Linux':  "",
    'Windows': ".exe"
  }[platform.system()]

def nativelib_dir():
  return mkpath(options.bindir, "_nativelibs_")

def shared(lib):
  import platform
  suffix = {
    'Darwin': ".dylib",
    'Linux':  ".so"
  }[platform.system()]
  return lib + suffix

def get_static_libs():
    return ' '.join([os.path.join(nativelib_dir(), lib) for lib in
         ("libfoster_main.o " + shared("libchromium_base") + " " +
          "libcpuid.a libcoro.a libcycle.a").split(" ")])

def get_link_flags():
  common = ['-lpthread']
  if options and options.profile:
    common.append('-lprofiler') # from gperftools
  import platform
  flags = {
    'Darwin': lambda: common + ['-framework', 'CoreFoundation',
                                '-framework', 'Cocoa',
                                '-lobjc'],
    'Linux': lambda: common + ['-lrt', '-lglib-2.0']
  }[platform.system()]()
  return ' '.join(flags)

def rpath(path):
  import platform
  return {
    'Darwin': lambda: '',
    'Linux' : lambda: '-Wl,-R,' + os.path.abspath(path),
  }[platform.system()]()

def show_cmdlines(options):
  return options and options.show_cmdlines == True

def optlevel(options):
  if options and options.backend_optimize:
    # Right now fosteroptc only recognizes -O0, not -O2 or such.
    return []
  else:
    return ['-O0']

class StopAfterMiddle(Exception):
    def __str__(self):
        return repr(self.value)

def should_stop_after_middle():
  if '--fmt' in options.meargs:
    return True
  return False

def insert_before_each(val, vals):
  return [x for v in vals for x in [val, v]]

def get_ghc_rts_args():
  ghc_rts_args = ["-smeGCstats.txt", "-K400M"]

  if options and options.stacktraces:
    ghc_rts_args.append('-xc') # Produce stack traces

  # https://downloads.haskell.org/~ghc/latest/docs/html/users_guide/prof-heap.html
  if options and options.profileme:
    ghc_rts_args.append("-p") # general time profile, written to me.prof
    ghc_rts_args.append("-hc") # break down space used by function (cost center)
    #ghc_rts_args.append("-hm") # break down space used by module (producer)
    #ghc_rts_args.append("-hy") # break down space used by type
    #ghc_rts_args.append("-hd") # break down space used by ctor
    #ghc_rts_args.append("-hr") # break down space used by retainer

    #ghc_rts_args.append("-hySet,[],ByteString,ARR_WORDS,Node") # restrict to given types
    ghc_rts_args.append("-L50") # give longer labels
  return ghc_rts_args

def compile_foster_to_bitcode(paths, inputfile, compilelog, finalpath, tmpdir):
    finalname = os.path.basename(finalpath)

    if options.asm:
      outpath = paths["_out.s"]
    else:
      outpath = paths["_out.o"]

    if options.standalone and options.exepath is not None:
      outpath = options.exepath

    # Getting tee functionality in Python is a pain in the behind
    # so we just disable logging when running with --show-cmdlines.
    if show_cmdlines(options):
      compilelog = None

    importpath = insert_before_each('-I', options.importpaths)

    if options and options.interpret:
      interpret = ["--interpret", tmpdir]
    else:
      interpret = []

    ghc_rts_args = get_ghc_rts_args()

    parse_output = paths['_out.parsed.pb']
    check_output = paths['_out.checked.pb']

    def crun(cmdlist):
      return run_command(cmdlist,
                paths, inputfile, showcmd=show_cmdlines(options),
                stdout=compilelog, stderr=compilelog, strictrv=True)

    # running fosterparse on a source file produces a ParsedAST
    e1 = crun(['fosterparse', inputfile, parse_output] + importpath)

    # running fostercheck on a ParsedAST produces an ElaboratedAST
    prog_args = [arg for _arg in options.progargs or []
                     for arg in ['--prog-arg', _arg]]
    e2 = crun(['fostercheck', parse_output, check_output] +
                     ["+RTS"] + ghc_rts_args + ["-RTS"] +
                     interpret + options.meargs + prog_args)

    if should_stop_after_middle():
      raise StopAfterMiddle()

    # running fosterlower on a ParsedAST produces a bitcode Module
    # linking a bunch of Modules produces a Module
    e3 = crun(['fosterlower', check_output, '-o', finalname,
                         '-outdir', tmpdir, '-fosterc-time',
                         '-bitcodelibs', mkpath(options.bindir, '_bitcodelibs_')]
                    + options.beargs)

    # Running opt on a Module produces a Module
    # Running llc on a Module produces an assembly file
    e4 = crun(['fosteroptc', finalpath + '.preopt.bc',
                                         '-fosterc-time', '-o', outpath]
                    + optlevel(options)
                    + options.optcargs)

    return (e1, e2, e3, e4)

def link_to_executable(finalpath, exepath, paths, inputfile):
    assert options.cxxpath and len(options.cxxpath) > 0
    return run_command('%(cxx)s %(_out.o)s %(staticlibs)s %(linkflags)s -o %(exepath)s %(rpath)s' % {
                         '_out.o'    : paths['_out.o'],
                         'staticlibs': get_static_libs(),
                         'linkflags' : get_link_flags(),
                         'exepath'   : exepath,
                         'cxx'       : options.cxxpath,
                         'rpath'     : rpath(nativelib_dir())
                       },  paths, inputfile, showcmd=show_cmdlines(options))

# options args are mutable state, reused when running all tests...
def insert(lst, val):
  if not val in lst:
    lst.append(val)

def compile_foster_code(inputfile):
  paths = get_paths(inputfile)

  # Dump extra files, but only when running directly,
  # not when running via run_all.py
  if options.extrabitcode:
    insert(options.optcargs, '-dump-preopt')
    insert(options.optcargs, '-dump-postopt')
    insert(options.beargs  , '-dump-prelinked')

  if options.standalone:
    insert(options.beargs, "--unsafe-disable-gc")
    # unsafe-disable-array-bounds-checks
    insert(options.beargs, "--standalone")
    insert(options.meargs, "--standalone")

  tmpdir = options.tmpdir

  finalpath = os.path.join(tmpdir, os.path.basename(inputfile))
  exepath   = os.path.join(tmpdir, default_exename(inputfile))

  allprogargs = options.progargs + insert_before_each("--foster-runtime", options.progrtargs)
  exe_cmd = [exepath] + allprogargs

  log_filename = os.path.join(tmpdir, "compile.log.txt")
  rv = 0
  with open(log_filename, 'w') as compilelog:
    fp_elapsed, fm_elapsed, fl_elapsed, fc_elapsed = \
            compile_foster_to_bitcode(paths, inputfile, compilelog, finalpath, tmpdir)

    if options.asm:
      outpath = "%s.o" % finalpath
      if options.standalone and options.exepath is not None:
        outpath = options.exepath
      as_elapsed = run_command('%s -g %s.s -c -o %s' % (options.cxxpath, finalpath, outpath), paths, inputfile,
                                   showcmd=show_cmdlines(options))
    else: # fosteroptc emitted a .o directly.
      as_elapsed = 0

    if options.standalone:
      ld_elapsed = 0
    else:
      ld_elapsed = link_to_executable(finalpath, exepath, paths, inputfile)

      if options.exepath is not None:
        exe_cmd = [options.exepath] + allprogargs
        shutil.copy2(exepath, options.exepath)
        print "Try running:"
        print  ''.join()

  return (paths, exe_cmd, (fp_elapsed, fm_elapsed, fl_elapsed, fc_elapsed, as_elapsed, ld_elapsed))

def mkpath(root, prog):
  if os.path.isabs(prog):
    return prog
  else:
    return os.path.join(root, prog)

def get_paths(inputfile):
  join = os.path.join
  bindir = options.bindir
  paths = {
      'bindir':    bindir,
  }
  for prog in ['fosterparse', 'fosterlower', 'fosteroptc']:
    paths[prog] = mkpath(bindir, prog)

  for lib in ['foster_runtime.bc']:
    paths[lib] =  mkpath(bindir, os.path.join('_bitcodelibs_', lib))

  for lib in [ 'libfoster_main.o']:
    paths[lib] =  mkpath(bindir, os.path.join('_nativelibs_', lib))

  for out in ['_out.parsed.pb', '_out.checked.pb', "_out.o", "_out.s"]:
    paths[out] =  mkpath(options.tmpdir, os.path.basename(inputfile) + out[4:])

  if options.me != 'fostercheck':
    paths['fostercheck'] = mkpath(bindir, options.me)

  # compiler spits out foster.ll in current directory
  paths['foster.ll'] = join(os.path.dirname(paths['fosterparse']), 'foster.ll')
  return paths

def get_fosterc_parser():
  parser = OptionParser(usage="""usage: %prog [options] <test_path>

   Notes:
     * If using ./gotest.sh or runfoster...
                --me-arg=--verbose       will print (Ann)ASTs
                --me-arg=--dump-ir=kn    will print k-normalized IR
                --me-arg=--dump-ir=cfg   will print closure-conv IR
                --me-arg=--dump-ir=mono  will print monomo. IR
                --be-arg=--gc-track-alloc-sites
                --be-arg=--unsafe-disable-array-bounds-checks
                --optc-arg=-no-coalesce-loads
                --optc-arg=--help        will display optimization flags
                --prog-arg=--hallooooo
                --profileme              will enable profiling of the middle-end; then do `hp2ps -e8in -c me.hp`
                --backend-optimize       enables LLVM optimizations
                --asm
                -o <path>                copies generated executable to <path>
                                            but does not run it
                --show-cmdlines
""")
  parser.add_option("--bindir", dest="bindir", action="store", default=None,
                    help="Use bindir as default place to find the foster compiler binaries")
  parser.add_option("--me", dest="me", action="store", default="me",
                    help="Relative (from bindir) or absolute path to binary to use for type checking.")
  parser.add_option("--show-cmdlines", action="store_true", dest="show_cmdlines", default=False,
                    help="Show more information about programs being run.")
  parser.add_option("--asm", action="store_true", dest="asm", default=False,
                    help="Compile to assembly rather than object file.")
  parser.add_option("--interpret", action="store_true", dest="interpret", default=False,
                    help="Run using interpreter instead of compiling via LLVM")
  parser.add_option("--backend-optimize", dest="backend_optimize", action="store_true", default=False,
                    help="Enable optimizations in fosteroptc")
  parser.add_option("--profileme", dest="profileme", action="store_true", default=False,
                    help="Enable detailed profiling of compiler middle-end")
  parser.add_option("--no_bytes_per_sec", dest="print_bytes_per_sec", action="store_false", default=True,
                    help="Disable printing of bytes-per-second for input protobuf and output executable")
  parser.add_option("--no_extra_bitcode", dest="extrabitcode", action="store_false", default=True,
                    help="Disable dumping of extra bitcode files (prelinked/postopt)")
  parser.add_option("--profile", dest="profile", action="store_true", default=False,
                    help="Enable profiling of generated executable")
  parser.add_option("--me-arg", action="append", dest="meargs", default=[],
                    help="Pass through arg to middle-end.")
  parser.add_option("--be-arg", action="append", dest="beargs", default=[],
                    help="Pass through arg to back-end (lowering).")
  parser.add_option("--optc-arg", action="append", dest="optcargs", default=[],
                    help="Pass through arg to back-end (optc).")
  parser.add_option("--prog-arg", action="append", dest="progargs", default=[],
                    help="Pass through command line arguments to program")
  parser.add_option("--with-stdin", action="store", dest="prog_stdin", default="",
                    help="Provide explicit redirection for compiled program's stdin.")
  parser.add_option("--foster-runtime", action="append", dest="progrtargs", default=[],
                    help="Pass through command line arguments to program runtime")
  parser.add_option("--standalone", action="store_true", dest="standalone", default=False,
                    help="Just compile, don't link...")
  parser.add_option("--stacktraces", action="store_true", dest="stacktraces", default=False,
                    help="Have the middle-end produce stack traces on error")
  parser.add_option("--cxxpath", dest="cxxpath", action="store", default="g++",
                    help="Set C++ compiler/linker path")
  parser.add_option("--tmpdir", dest="tmpdir", action="store", default=".",
                    help="Directory for storing intermediate results")
  parser.add_option("-I", dest="importpaths", action="append", default=[],
                    help="Add import path")
  parser.add_option("-o", dest="exepath", action="store", default=None,
                    help="Set path for output result (executable, etc)")
  return parser

def fosterc_set_options(opts):
  global options
  options = opts

def fosterc_parser_parse_and_fixup(parser):
  (options, args) = parser.parse_args()

  if options.bindir is None:
    scriptdir = sys.path[0]
    fosterroot = os.path.join(scriptdir, '..')
    options.bindir = os.path.join(fosterroot, '_obj')

  return (options, args)

if __name__ == "__main__":
  parser = get_fosterc_parser()
  (options, args) = fosterc_parser_parse_and_fixup(parser)


  if len(args) != 1:
    print args
    print options
    print parser.print_help()
    sys.exit(1)

  inputfile = args[0]

  compile_foster_code(inputfile)