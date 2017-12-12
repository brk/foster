============================= Usage ========================================

$ # Run through "Installation" steps below, then:

$ hg clone https://bitbucket.org/b/foster foster
$ cd foster
$ mkdir _obj        # Separate directory for compilation results and such
$ cd _obj           # The name can be whatever you'd like, but it should
                    # be located outside of the foster source directory.
$ ccmake .. -G "Unix Makefiles"
        # Press 'c' to configure; if CMake cannot find the listed paths,
        #                         please set them by hand.
        # Press 'g' to generate Makefiles and exit once paths are OK

Once the first-time steps are done:

$ make            # Recompile any updated files.
$ make regress    # Run regression tests

After running regression tests, you can look for trace messages
from the middle-end with a command like this:

$ cat test-tmpdir/*/compile.log.txt | grep '...' | sort | uniq

Other commands of interest, from _obj:

$ make hs_clean    # Delete just the Haskell-generated .o files
$ make list_regression_tests

From project root:

$ scripts/countlines.sh  # Give an overview of where code is, volume-wise.

============================= Installation =================================
Paths:
  You'll want to append $PATH_TO_FOSTER/scripts to $PATH and $PYTHONPATH,
  probably in .bashrc or equivalent.

Dependencies (non-exhaustive):
  CMake, ANTLR + ANTLR3 C runtime, LLVM, Protocol Buffers, Z3
  Python (and several 3rd party Python libraries)
  Pin (optional, for benchmarking analysis)

Ubuntu 17.10:
  See   scripts/ubuntu-17.10.sh

  The lines in the above script related to installing ANTLR
  also apply to Mac OS X.

Mac OS X:
  You'll want to install the GNU time binary:
     brew install gnu-time       # or
     sudo port install gtime

  Also, SWIG for building LLDB:
     sudo port install swig swig-python

  # For CSmith:
  git clone https://github.com/csmith-project/csmith ~/sw/local/csmith.git
  cd ~/sw/local/csmith.git
  ./configure --prefix=$HOME/sw/local
  make


  # For Ott:
  #         sudo apt-get install  coq texlive-latex-base
  #         wget http://www.cl.cam.ac.uk/~pes20/ott/ott_distro_0.25.tar.gz
  #         tar xf ott_distro_0.25.tar.gz
  #         ...etc...

  # For emscripten:
  #         sudo apt-get install python-software-properties
  #         sudo apt-get update
  #         sudo add-apt-repository ppa:chris-lea/node.js
  #         sudo apt-get install nodejs npm

  # For CVC4, add the following lines to /etc/apt/sources.list::
  #
  #     deb http://cvc4.cs.nyu.edu/debian/ unstable/
  #     deb-src http://cvc4.cs.nyu.edu/debian/ unstable/
  #
  # Then::
  #
  #     $ sudo apt-get update
  #     $ sudo apt-get install cvc4 libcvc4-dev



Other libraries/tools:
        gperftools: https://code.google.com/p/gperftools/
        	If you install via deb, you'll need to install both...
        kcachegrind: http://kcachegrind.sourceforge.net/html/Home.html
        valgrind
        pin:        http://software.intel.com/en-us/articles/pin-a-dynamic-binary-instrumentation-tool
        leveldb:    https://code.google.com/p/leveldb/
        leveldb-go: https://code.google.com/p/leveldb-go/
        snappy:     https://code.google.com/p/snappy/
        cityhash:   https://code.google.com/p/cityhash/
        ocaml-core: https://bitbucket.org/janestreet/core

        hprotoc:    http://hackage.haskell.org/package/hprotoc


Networking
==========

On Linux:

        sudo ip tuntap add tun8 mode tun  # For IP-format frames
        sudo ip link   set tun8 up
        sudo ip addr   add 192.168.6.6/24 dev tun8
        Process open()s /dev/net/tun, then calls ioctl() with TUNSETIFF
                to get a fd for tun8
        (once a process is blocked reading from tun8:)
        ping 192.168.6.42 # if we ping 6.6 the kernel delivers packets to lo

On Mac OS X, first install tuntaposx <http://tuntaposx.sourceforge.net/>, then:

        Process open()s /dev/tun8
        Process calls system(sudo ifconfig tun8 192.168.6.41 192.168.6.42)
        ping 192.168.6.42

Then, once the appropriate network interfaces are up,
run (from the _obj) directory:

   $ fosterc ../test/speed/foster-posix/foster-net/foster-net.foster
   $ ../test/speed/foster-posix/foster-net/foster-net.foster.exe

   (and ping as above, from a separate terminal window)


Benchmarks
==========

Make sure that the foster/ directory is in your $PYTHONPATH,
then execute scripts/bench-all.py. The script will churn through
a few benchmarks (of both Foster code and reference non-Foster implementations).
After a few minutes, the script will spit out a path like
        data/2017-06-01@16.37.12/all_timings.json
which we'll call $ALLTIMINGS.

The bench-ize.py script will munge this data for display, in various ways.

        $ bench-ize.py --overview $ALLTIMINGS
        ...
        third_party/shootout/fannkuchredux [LLVMopt=O0,sse=no,lang=other,date=2017-06-01@16.37.12] {'inputs': ['10']}
                                        [LLVMopt=O2,sse=no,lang=other,date=2017-06-01@16.37.12] {'inputs': ['10']}
                                        [LLVMopt=O3,sse=yes,lang=other,date=2017-06-01@16.37.12] {'inputs': ['10']}
        speed/shootout/fannkuchredux [inline=yes,LLVMopt=O2,abc=unsafe,donate=yes,lang=foster,date=2017-06-01@16.37.12] {'inputs': ['10']}
                                [inline=no,LLVMopt=O0,abc=safe,donate=yes,lang=foster,date=2017-06-01@16.37.12] {'inputs': ['10']}
                                [inline=yes,LLVMopt=O2,abc=safe,donate=yes,lang=foster,date=2017-06-01@16.37.12] {'inputs': ['10']}
        speed/shootout/nbody [inline=yes,LLVMopt=O2,abc=unsafe,donate=yes,lang=foster,date=2017-06-01@16.37.12] {'inputs': ['350000']}
                        [inline=no,LLVMopt=O0,abc=safe,donate=yes,lang=foster,date=2017-06-01@16.37.12] {'inputs': ['350000']}
                        [inline=yes,LLVMopt=O2,abc=safe,donate=yes,lang=foster,date=2017-06-01@16.37.12] {'inputs': ['350000']}
        ...


        $ bench-ize.py --test spectralnorm $ALLTIMINGS
        ...
        Output written to 'bench-ized.html'



        $ bench-ize.py --test spectralnorm --tags LLVMopt=O2 $ALLTIMINGS



CSmith
======

We have a tool to translate a subset of C code into Foster.

The scripts/ directory includes a few wrappers to generate random C programs
using CSmith, translate the resulting code into Foster, and compare whether
the compiled C and Foster code produce the same output.

Running  csmith2foster.py  will generate twenty random C programs in the
current directory, translate and compile each one, and report the diff status.

Most of the time you'll see output like

        --------------------------------------------------
        Attempting test csf_003.c
        Test case csf_003.c skipped because the C code exited under murky circumstances.
        --------------------------------------------------
        Attempting test csf_004.c
        Compiling csf_004.c to Foster... (71 lines)
        Compiling and running the generated Foster code...
        Diffing... (1 lines)
        Test case csf_004.c passed
        --------------------------------------------------

Many of the programs generated by CSmith will fail at runtime,
usually with a floating point exception.

If we tickle a bug in the Foster compiler, it'll look like this:

        --------------------------------------------------
        Attempting test csf_001.c
        Compiling csf_001.c to Foster... (233 lines)
        Compiling and running the generated Foster code...
        Diffing... (1 lines)
        Test case csf_001.c             FAILED (wrong output)
        --------------------------------------------------

test_c2f.py will re-run tests on saved programs in the  test/c2f/  directory,
        or re-run tests on residual csmith2foster-generated programs
        (depending on how you edit the last few lines of the file).

You can run  c2foster  to translate a C file to Foster (on stdout).
Be aware that you'll need to provide search paths for #include files
explicitly. In particular, for CSmith-generated programs, you'll need
something like

        $ c2foster csf_001.c -I $HOME/sw/local/csmith-2.3.0/include/csmith-2.3.0 > csf_001.foster

c2foster will dump Clang's warning to stderr, but those can be ignored.

Running an individual C file can be done with  runclang  .
Note as before that you'll need to provide search paths explicitly.

Individual Foster programs can be run with  runfoster  .

You can see a (colorized) output of Clang's AST for a given C program
with   clang -fsyntax-only -Xclang -ast-dump  <includes> <program>

