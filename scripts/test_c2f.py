#!/usr/bin/env python2

from __future__ import with_statement

import os.path
import subprocess
import threading
import fnmatch
import hashlib
import shutil

from run_cmd import walltime, elapsed_since

csmith_dir = os.path.expanduser("~/sw/local/csmith-2.3.0")
csmith_inc = os.path.join(csmith_dir, 'include', 'csmith-2.3.0')

# returns status
def run_cmd(cmd, stdout=None, stderr=None, stdin=None, timeout=2):
  if type(cmd) == str:
    cmd = cmd.strip().split(' ')

  class mut:
      proc = None

  try:
    #print ' '.join(cmd)
    def runner():
        
         mut.proc = subprocess.Popen(cmd, stdout=stdout, stderr=stderr, stdin=stdin)
         mut.proc.communicate()

    thread = threading.Thread(target=runner)
    thread.start()
    thread.join(timeout) # seconds
    if thread.is_alive():
        mut.proc.terminate()
        thread.join()
        return 99
  except OSError:
    print ": error: Unable to execute ", cmd
    raise
  return mut.proc.returncode

#############################

def files_differ(a, b):
  "Returns True if diff finds a difference between file a and file b."
  with open(os.devnull, 'w') as devnull:
    rv = run_cmd(['diff', '--brief', a, b], stdout=devnull)
    if rv == 0:
        return False
    else:
        return True

def fail_reason(foster_compile_rv):
  if foster_compile_rv == 0:
    return "wrong output"
  elif foster_compile_rv == 99:
    return "compilation timeout"
  else:
    return "couldn't compile"

def attempt_test_named(filename, failing, copy_here_if_ok=None):
    print "Attempting test", filename

    c_code = filename
    assert c_code[-2:] == ".c"
    x = c_code[:-2] # strip the ".c" from the filename

    f_code  = "%s.foster" % x
    c_warn  = "%s.clang.warn.txt" % x
    cf_warn = "%s.c2f.warn.txt" % x
    c_out   = "%s.clang.out.txt" % x
    f_out   = "%s.foster.out.txt" % x

    c_rv = run_cmd("runclang %s -I %s" % (c_code, csmith_inc), stdout=open(c_out, 'w'), stderr=open(c_warn, 'w'))

    if c_rv == 0:
      c_linecount = len(open(c_code, 'r').readlines())
      print "Compiling", c_code, "to Foster... (%d lines)" % c_linecount
      run_cmd("c2foster %s -I %s" % (c_code, csmith_inc), stdout=open(f_code, 'w'), stderr=open(cf_warn, 'w'))

      print "Compiling and running the generated Foster code..."
      f_c_st = walltime()
      f_c_rv = run_cmd("runfoster %s" % f_code, stdout=open(f_out, 'w'), timeout=30)
      f_c_ms = elapsed_since(f_c_st)
      f_linecount = len(open(f_code, 'r').readlines())
      print "fosterc ran @ %d lines / %.1f s (%d l/s)" % (f_linecount, (f_c_ms / 1000.0), int(f_linecount / (f_c_ms / 1000.0)) )

      linecount = len(open(c_out, 'r').readlines())
      print "Diffing... (%d lines)" % linecount 

      if files_differ(c_out, f_out):
          print "Test case", c_code, "            FAILED (%s)" % fail_reason(f_c_rv)
          failing.append(filename)
      else:
          print "Test case", c_code, "passed"
          if copy_here_if_ok is not None:
            filename = hashlib.md5(open(c_code, 'r').read()).hexdigest() + ".c"
            shutil.copyfile(c_code, os.path.join(copy_here_if_ok, filename))
    elif c_rv == 99:
          print "Test case", c_code, "skipped because the C code was (probably) non-terminating."
    else:
          print "Test case", c_code, "skipped because the C code exited under murky circumstances."

    print "--------------------------------------------------"

def run_on_test_c2f():
  failing = []
  for root, d, files in os.walk("../test/c2f"):
    for cfile in fnmatch.filter(files, "*.c"):
      if not 'csmith' in root:
        attempt_test_named(os.path.join(root, cfile), failing)

  if len(failing) > 0:
    print "Failing testcases:"
    for f in failing:
      print "\t", f

def run_on_csf_files():
  for root, d, files in os.walk("."):
    for cfile in fnmatch.filter(files, "csf_*.c"):
      attempt_test_named(os.path.join(root, cfile), failing)

if __name__ == '__main__':
  #run_on_test_c2f()
  run_on_csf_files()

