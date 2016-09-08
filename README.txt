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

Mac OS X:
  You'll want to install the GNU time binary:
     brew install gnu-time       # or
     sudo port install gtime

Ubuntu 16.04 (x64):
  # Mercurial
  sudo apt-get install mercurial

  # Compilers, build tools,
  sudo apt-get install build-essential g++ g++-multilib git gnuplot \
                       python-pygments python-matplotlib  python-scipy python-sphinx \
                       python-pandas python-pip python-numpy python-qt4 \
                       python-qscintilla2 libqscintilla2-dev swig

  sudo apt-get install vim vim-gnome ack-grep \
              curl ctags aptitude libpng12-dev libcairo2-dev libc6-dev default-jdk

  sudo apt-get install m4 ministat meld \
         linux-tools-virtual linux-tools-generic \
         libffi-dev libedit-dev cmake cmake-curses-gui

  # TortoiseHG from source, since the PPA packages have been taken down.
  hg clone https://bitbucket.org/tortoisehg/thg ~/.local/tortoisehg
  # Assuming ~/.local/bin is on $PATH, which it was in Ubuntu MATE 16.04
  mkir -p ~/.local/bin
  ln -l ~/.local/tortoisehg/thg ~/.local/bin/thg

  # GMP is needed for GHC to build Cabal from source.
  sudo apt-get install libgmp3-dev libgmp-dev

  # Python packages, mostly used by benchmarking infrastructure
  pip install pyyaml jinja2 statsmodels mpld3 seaborn

  # If you want jEdit and the ninja build tool...

  wget http://downloads.sourceforge.net/project/jedit/jedit/5.3.0/jedit_5.3.0_all.deb
  sudo dpkg -i jedit_5.3.0_all.deb

  git clone git://github.com/ninja-build/ninja.git
  cd ninja
  ./configure.py --bootstrap
  mv ninja ~/sw/local/bin



  # For GHC, to get profiling libraries, do not use apt-get;
  # instead, download a generic binary tarball directly from
  #    http://www.haskell.org/ghc/download
  # and cabal-install from
  #    http://www.haskell.org/cabal/download.html
  #
  # For example:

  wget http://downloads.haskell.org/~ghc/8.0.1/ghc-8.0.1-x86_64-deb8-linux.tar.xz
  tar xf ghc-*-linux.tar.xz
  cd ghc-* && ./configure --prefix=$HOME/.local/ghc-8.0.1 && make install && cd ..

  wget https://hackage.haskell.org/package/cabal-install-1.24.0.0/cabal-install-1.24.0.0.tar.gz
  tar xf cabal-install-*.tar.gz
  cd cabal-install-* && ./bootstrap.sh && cd ..

  cabal install happy alex

  # Ubuntu 16.10 has a recent-enough version of CMake, but on
  # Ubuntu 14.10, the CMake version available via apt-get is outdated.
  # To build from source (might want to pass --prefix to configure!):

  wget http://www.cmake.org/files/v3.6/cmake-3.6.1.tar.gz
  tar xf cmake-*.tar.gz
  cd cmake-*
  ./configure
  make

  # You can install binutils-gold but it needs to be disabled for some Haskell packages.

  You can install llvm by executing   bash scripts/install-llvm.sh

  Assuming you already have LLVM installed, in $PATH and $PKG_CONFIG_PATH...




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


ANTLR on Linux and OS X:

	ANTLR_VERSION=3.4
	ANTLR_DIR=~/antlr/${ANTLR_VERSION}
	mkdir tmp
	cd tmp
		wget http://antlr3.org/download/C/libantlr3c-${ANTLR_VERSION}.tar.gz
		tar xzvf libantlr3c-${ANTLR_VERSION}.tar.gz
                cd libantlr3c-${ANTLR_VERSION}
		./configure --prefix=${ANTLR_DIR} --enable-64bit && make && make install
                cd ..
	cd ..
	rm -rf ./tmp
	pushd ${ANTLR_DIR}
	wget http://antlr3.org/download/antlr-${ANTLR_VERSION}-complete.jar
        mv antlr-${ANTLR_VERSION}-complete.jar antlr-${ANTLR_VERSION}.jar
	popd

Haskell:
   To enable profiling, add    library-profiling: True   to   ~/.cabal/config
   before installing any further packages.

   Set up a Cabal sandbox within the ``compiler/me`` directory via::

        $ cd ~/foster/compiler/me ; cabal sandbox init

   Now, install minuproto somewhere:

        $ cd ~/sw/local
        $ hg clone https://bitbucket.org/b/minuproto
        $ cd minuproto
        $ cabal --sandbox-config-file=$HOME/foster/compiler/me/cabal.sandbox.config install

        $ cd ~/foster/compiler/me ; cabal install --only-dependencies


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
