============================= Usage ========================================

$ # Run through "Installation" steps below, then:

$ hg clone https://foster.googlecode.com/hg/ foster
$ mkdir fxc         # Separate directory for compilation results and such
$ cd fxc            # The name can be whatever you'd like, but it should
                    # be located outside of the foster source directory.
$ ccmake ../foster -G "Unix Makefiles"
        # Press 'c' to configure; if CMake cannot find the listed paths,
        #                         please set them by hand.
        # Press 'g' to generate Makefiles and exit once paths are OK

Once the first-time steps are done:

$ make        # Recompile any updated files.
$ ctest       # Run tests in mostly-quiet mode; test details will not be shown
$ ctest -V    # Run tests in verbose mode; output from tests will be printed.

============================= Installation =================================
Ubuntu:
	Dependencies: CMake, ANTLR3 C runtime, Java, Google glog, LLVM (including llvm-gcc)
	Assuming you already have LLVM installed, in $PATH and $PKG_CONFIG_PATH...
	
	Interesting packages:
		cmake		llvm-dev	llvm-doc	libgmp3c2
	(universe)
		binutils-gold	cmake-curses-gui	llvm-gcc-4.2	mercurial
		clang		codeblocks		g++	libffi-dev

	If you need Java on Ubuntu 9.10,
	sudo apt-get install sun-java6-jdk

	on 10.04, install default-jdk


	ANTLR_VERSION=3.2
	ANTLR_DIR=~/antlr/${ANTLR_VERSION}
	GLOG_VERSION=0.3.0
	GLOG_DIR=~/glog/${GLOG_VERSION}
	sudo apt-get install cmake cmake-curses-gui
	mkdir tmp
	cd tmp
		wget http://antlr.org/download/C/libantlr3c-${ANTLR_VERSION}.tar.gz
		tar xzvf libantlr3c-${ANTLR_VERSION}.tar.gz
                cd libantlr3c-${ANTLR_VERSION}
		./configure --prefix=${ANTLR_DIR} && make && make install
                cd ..

		wget http://google-glog.googlecode.com/files/glog-${GLOG_VERSION}.tar.gz
		tar xzvf glog-${GLOG_VERSION}.tar.gz
		cd glog-${GLOG_VERSION}
		./configure --prefix=${GLOG_DIR} && make && make install
                cd ..
	cd ..
	rm -rf ./tmp
	pushd ${ANTLR_DIR}
	wget http://antlr.org/download/antlr-${ANTLR_VERSION}.jar
	popd
