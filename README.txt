Ubuntu (9.10):
	Dependencies: CMake, ANTLR3 C runtime, Java, Google glog, LLVM
	Assuming you already have LLVM installed, in $PATH and $PKG_CONFIG_PATH...

	If you need Java,
	sudo apt-get install sun-java6-jdk

	ANTLR_VERSION=3.2
	ANTLR_DIR=~/antlr/${ANTLR_VERSION}
	GLOG_VERSION=0.3.0
	GLOG_DIR=~/glog/${GLOG_VERSION}
	sudo apt-get install cmake cmake-curses-gui
	mkdir tmp
	cd tmp
		wget http://antlr.org/download/C/libantlr3c-${ANTLR_VERSION}.tar.gz
		tar xzvf libantlr3c-${ANTLR_VERSION}.tar.gz
		mkdir -p
		./configure --prefix=${ANTLR_DIR}
		make
		make install

		wget http://google-glog.googlecode.com/files/glog-${GLOG_VERSION}.tar.gz
		tar xzvf glog-${GLOG_VERSION}.tar.gz
		cd glog-${GLOG_VERSION}
		./configure --prefix=${GLOG_DIR}
	cd ..
	rm -rf ./tmp
	pushd ${ANTLR_DIR}
	wget http://antlr.org/download/antlr-${ANTLR_VERSION}.jar
	popd
