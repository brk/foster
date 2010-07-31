from __future__ import with_statement
import time
import os
import re
import os.path
import subprocess
import sys
import shutil
import traceback

if os.name == 'nt':
  walltime = time.clock
else:
  walltime = time.time

tests_passed = set()
tests_failed = set()

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

  #if len(inlines) == 0:
  #  return None

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
    raise Exception(str(rv) + '; Failed to run: ' + ' '.join(arglist) + "\n\tfor test " + testpath)
  return elapsed(start, end)

def run_one_test(dir_prefix, basename, paths, tmpdir):
  start = walltime()
  exp_filename = os.path.join(tmpdir, "expected.txt")
  act_filename = os.path.join(tmpdir, "actual.txt")
  with open(exp_filename, 'w') as expected:
    with open(act_filename, 'w') as actual:
      with open(os.path.join(tmpdir, "compile.log.txt"), 'w') as compilelog:
        testpath = os.path.join(dir_prefix, basename)
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
                        total_elapsed, basename)
        infile.close()


def run_all_tests(bootstrap_dir, paths, tmpdir):
  for root, dirs, files in os.walk(bootstrap_dir, topdown=False):
    base = os.path.basename(root)

    code_path = os.path.join(root, base + ".foster")
    have_code = os.path.exists(code_path)

    if have_code:
      teststart = walltime()
      paths['code'] = code_path
      test_tmpdir = os.path.join(tmpdir, base)
      ensure_dir_exists(test_tmpdir)
      try:
        run_one_test(root, base, paths, test_tmpdir)
      except KeyboardInterrupt:
        return
      except:
	tests_failed.add(os.path.join(root, base))
      testend = walltime()

def main(bootstrap_dir, paths, tmpdir):
  walkstart = walltime()
  run_all_tests(bootstrap_dir, paths, tmpdir)
  walkend = walltime()
  print "Total time: %d ms" % elapsed(walkstart, walkend)

  print len(tests_passed), " tests passed"

  print len(tests_failed), " tests failed"
  if len(tests_failed) > 0:
    for test in tests_failed:
      print test
  sys.exit(len(tests_failed))

if __name__ == "__main__":
  if not len(sys.argv) in [2, 3]:
    print "Usage: %s <bootstrap_test_dir> [project_bin_dir = .]"
    sys.exit(1)

  join = os.path.join

  bootstrap_dir = sys.argv[1]
  bindir = os.getcwd()
  if len(sys.argv) == 3:
    bindir = sys.argv[2]

  tmpdir = join(bindir, 'test-tmpdir')
  ensure_dir_exists(tmpdir)

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

  main(bootstrap_dir, paths, tmpdir)
