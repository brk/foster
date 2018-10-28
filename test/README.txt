Tests in the bootstrap/ directory are pseudo-unit tests.
  Each subdirectory bootstrap/<x>/ should contain <x>.foster (at minimum).
  The run_all.py script will iterate through the subdirectories, compile and run each test,
  and compare the output to the expected output.
  Any discrepancies will be noted, and results summarized at the end of the run.
