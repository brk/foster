from __future__ import with_statement
import time
import os
import re
import os.path
import subprocess
import sys
import shutil

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

# returns (status, elapsed-time-ms)
def run_command(cmd, paths, testpath, stdout=None, stderr=None, stdin=None, strictrv=True):
  if type(cmd) == str:
    cmd = cmd.split(' ')
  arglist = [default_lookup(arg, paths) for arg in cmd]

  start = walltime()
  rv = subprocess.call( arglist, stdout=stdout, stderr=stderr, stdin=stdin)
  end = walltime()

  if strictrv and rv != 0:
    raise Exception(str(rv) + '; Failed to run: ' +
	' '.join(arglist) + '\n\tfor test ' + testpath)
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

        # Hack for now, since this option is baked in to the compiler.
        compile_separately = False
        fosterc_cmdline = [ paths['fosterc'], paths['code'] ]
        if compile_separately:
          fosterc_cmdline.insert(1, "-c")

        #print ' '.join(fosterc_cmdline)
        fc_elapsed = run_command(fosterc_cmdline, paths, testpath, stdout=compilelog, stderr=compilelog)


        llvm_asm_path = os.path.join(tmpdir, basename + ".ll")
        shutil.copyfile(paths['foster.ll'], llvm_asm_path)
	as_elapsed = run_command('llvm-as foster.ll -f', paths, testpath)
        
        if compile_separately:
          cc_elapsed = 0
          ld_elapsed = run_command('llvm-ld foster.bc libfoster.bc -o ll-foster', paths, testpath)
	  lc_elapsed = 0
          op_elapsed = 0
          rn_elapsed = run_command('ll-foster',  paths, testpath, stdout=actual, stderr=expected, stdin=infile, strictrv=False)
        else:
          ld_elapsed = 0
	  op_elapsed = 0
          lc_elapsed = run_command('llc -O1 foster.bc -f -o foster.s',  paths, testpath, stdout=actual, stderr=expected, stdin=infile)
          cc_elapsed = run_command('g++ foster.s libfoster_main.o libchromium_base.a libcpuid.a -lrt -lpthread',  paths, testpath, stdout=actual, stderr=expected, stdin=infile)
	  rn_elapsed = run_command('a.out',  paths, testpath, stdout=actual, stderr=expected, stdin=infile, strictrv=False)

        df_rv = subprocess.call(['diff', '-u', exp_filename, act_filename])
        if df_rv == 0:
          tests_passed.add(testpath)
        else:
          tests_failed.add(testpath)

        total_elapsed = elapsed_since(start)
	print "foc:%4d | las:%4d | opt:%4d | llc:%4d | gcc:%4d | run:%4d | all:%5d | %s" % (fc_elapsed, as_elapsed,
				op_elapsed, lc_elapsed, cc_elapsed, rn_elapsed, total_elapsed, basename)
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
      except:
        pass
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
  if len(sys.argv) != 5:
    print "Usage: %s <bootstrap_test_dir> <project_bin_dir> <tmpdir> <llvm_config_path>"
    sys.exit(1)
  join = os.path.join
  progname, bootstrap_dir, bindir, tmpdir, llvm_config_path = sys.argv
  llvmdir = os.path.dirname(llvm_config_path)
  paths = {
      # Haven't renamed the binary from foster to fosterc yet
      'fosterc': join(bindir, 'fosterc'),
      'llvm-as': join(llvmdir, 'llvm-as'),
      'llvm-ld': join(llvmdir, 'llvm-ld'),
      'lli'    : join(llvmdir, 'lli'),
      'llc'    : join(llvmdir, 'llc'),
      'opt'    : join(llvmdir, 'opt'),
      'foster.bc':    join(bindir, 'foster.bc'),
      'foster.s':     join(bindir, 'foster.s'),
      'a.out':        join(bindir, 'a.out'),
      'libfoster.bc': join(bindir, 'libfoster.bc'),
      'libfoster_main.o': join(bindir, 'libfoster_main.o'),
      'll-foster':    join(bindir, 'll-foster'),
  }
  # compiler spits out foster.ll in current directory
  paths['foster.ll'] = os.path.join(os.path.dirname(paths['fosterc']), 'foster.ll')

  ensure_dir_exists(tmpdir)

  main(bootstrap_dir, paths, tmpdir)
