from __future__ import with_statement
import os
import os.path
import subprocess
import sys
import shutil

tests_passed = set()
tests_failed = set()

def ensure_dir_exists(dirname):
  if not os.path.exists(dirname):
    return os.mkdir(dirname)
  return True

def run_one_test(dir_prefix, basename, paths, tmpdir):
  exp_filename = os.path.join(tmpdir, "expected.txt")
  act_filename = os.path.join(tmpdir, "actual.txt")
  with open(exp_filename, 'w') as expected:
    with open(act_filename, 'w') as actual:
      with open(os.path.join(tmpdir, "compile.log.txt"), 'w') as compilelog:
        testpath = os.path.join(dir_prefix, basename)
       
        fc_rv = subprocess.call([ paths['fosterc'], paths['code'] ], stdout=compilelog, stderr=compilelog)
        if fc_rv != 0:
          tests_failed.add(testpath)
          return

        llvm_asm_path = os.path.join(tmpdir, basename + ".ll")
        shutil.copyfile(paths['foster.ll'], llvm_asm_path)
        as_rv = subprocess.call([ paths['llvm-as'], llvm_asm_path, '-f' ])
        if as_rv != 0:
          tests_failed.add(testpath)
          return

        ld_rv = subprocess.call([ paths['llvm-ld'], paths['foster.bc'], paths['libfoster.bc'], '-o', paths['ll-foster'] ])
        if ld_rv != 0:
          tests_failed.add(testpath)
          return

        rn_rv = subprocess.call([ paths['ll-foster'] ], stdout=actual, stderr=expected)

        df_rv = subprocess.call(['diff', '-u', exp_filename, act_filename])
        if df_rv == 0:
          tests_passed.add(testpath)
        else:
          tests_failed.add(testpath)

def run_all_tests(bootstrap_dir, paths, tmpdir):
  for root, dirs, files in os.walk(bootstrap_dir, topdown=False):
    base = os.path.basename(root)

    code_path = os.path.join(root, base + ".foster")
    have_code = os.path.exists(code_path)

    if have_code:
      paths['code'] = code_path
      test_tmpdir = os.path.join(tmpdir, base)
      ensure_dir_exists(test_tmpdir)
      run_one_test(root, base, paths, test_tmpdir)

def main(bootstrap_dir, paths, tmpdir):
  run_all_tests(bootstrap_dir, paths, tmpdir)

  print len(tests_passed), " tests passed"
  for test in tests_passed:
    print test

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
      'fosterc': join(bindir, 'foster'),
      'llvm-as': join(llvmdir, 'llvm-as'),
      'llvm-ld': join(llvmdir, 'llvm-ld'),
      'foster.bc': join(bindir, 'foster.bc'),
      'libfoster.bc': join(bindir, 'libfoster.bc'),
      'll-foster': join(bindir, 'll-foster'),
  }
  # compiler spits out foster.ll in current directory
  paths['foster.ll'] = os.path.join(os.path.dirname(paths['fosterc']), 'foster.ll')

  ensure_dir_exists(tmpdir)

  main(bootstrap_dir, paths, tmpdir)
