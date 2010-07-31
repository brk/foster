from __future__ import with_statement
import time
import os
import re
import os.path
import subprocess
import sys
import shutil
import traceback

tests_passed = set()
tests_failed = set()

if os.name == 'nt':
  walltime = time.clock
else:
  walltime = time.time

def ensure_dir_exists(dirname):
  if not os.path.exists(dirname):
    return os.mkdir(dirname)
  return True

def extract_expected_input(path):
  """Reads lines from the start of the file at the given path,
     until it sees a line that is not a commented key/value pair."""
  inlines = []
  with open(path, 'r') as f:
    for line in f:
      #print "testing line ", line
      m = re.match(r"//\s*(.+?):\s*(.+)", line)
      if m == None:
        break

      label = m.group(1)
      value = m.group(2)
      if label == "IN":
        inlines.append(value) 

  tmpname = 'tmp.input.txt'
  with open(tmpname, 'w') as f:
    f.writelines(inlines)
  return open(tmpname, 'r')

def default_lookup(word, table):
  if word in table:
    return table[word]
  else:
    return word

def elapsed(start, end):
  return int( (end - start) * 1000 )

def elapsed_since(start):
  return elapsed(start, walltime())

def get_static_libs():
  return "libfoster_main.o libchromium_base.a libcpuid.a"

def get_link_flags():
  import platform
  flags = {
    'Darwin': lambda: ['-lpthread', '-framework', 'CoreFoundation'],
    'Linux': lambda: ['-lrt', '-lpthread']
  }[platform.system()]()
  return ' '.join(flags)

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
  return elapsed(start, end)

def testname(testpath):
  """Given '/path/to/some/test.foster', returns 'test'"""
  return os.path.basename(testpath).replace('.foster', '')

def run_one_test(testpath, paths, tmpdir):
  start = walltime()
  exp_filename = os.path.join(tmpdir, "expected.txt")
  act_filename = os.path.join(tmpdir, "actual.txt")
  with open(exp_filename, 'w') as expected:
    with open(act_filename, 'w') as actual:
      with open(os.path.join(tmpdir, "compile.log.txt"), 'w') as compilelog:
        infile = extract_expected_input(paths['code'])

        fosterc_cmdline = [ paths['fosterc'], paths['code'], '-O0' ]

        #print ' '.join(fosterc_cmdline)
        fc_elapsed = run_command(fosterc_cmdline, paths, testpath, stdout=compilelog, stderr=compilelog)

        cc_elapsed = run_command('g++ out.s %s %s -o a.out' % (get_static_libs(), get_link_flags()),
                                    paths, testpath)
        rn_elapsed = run_command('a.out',  paths, testpath, stdout=actual, stderr=expected, stdin=infile, strictrv=False)

        df_rv = subprocess.call(['diff', '-u', exp_filename, act_filename])
        if df_rv == 0:
          tests_passed.add(testpath)
        else:
          tests_failed.add(testpath)

        total_elapsed = elapsed_since(start)
        print "foc:%4d | gcc:%4d | run:%4d | py:%3d | tot:%5d | %s" % (fc_elapsed,
			cc_elapsed, rn_elapsed, (total_elapsed - (fc_elapsed + cc_elapsed + rn_elapsed)),
                        total_elapsed, testname(testpath))
        infile.close()

def main(bootstrap_dir, paths, tmpdir):
  run_one_test(testpath, paths, os.path.join(tmpdir, testname(testpath)))

def get_paths(bindir):
  join = os.path.join
  paths = {
      'fosterc': join(bindir, 'fosterc'),
      'out.s':     join(bindir, 'fc-output', 'out.s'),
      'a.out':     join(bindir, 'fc-output', 'a.out'),
      'libfoster.bc': join(bindir, 'libfoster.bc'),
      'libcpuid.o':   join(bindir, 'libcpuid.o'),
      'libfoster_main.o': join(bindir, 'libfoster_main.o'),
  }
  # compiler spits out foster.ll in current directory
  paths['foster.ll'] = join(os.path.dirname(paths['fosterc']), 'foster.ll')
  return paths

if __name__ == "__main__":
  if not len(sys.argv) in [2, 3]:
    print "Usage: %s <test_path> [project_bin_dir = .]"
    sys.exit(1)

  testpath = sys.argv[1]
  bindir = os.getcwd()
  if len(sys.argv) == 3:
    bindir = sys.argv[2]

  tmpdir = os.path.join(bindir, 'test-tmpdir')
  ensure_dir_exists(tmpdir)

  main(testpath, get_paths(), tmpdir)
