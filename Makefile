LLVM_DIR ?= $(HOME)/llvm/2.6
ANTLR_VERSION ?= 3.2
ANTLR_DIR ?= $(HOME)/antlr/$(ANTLR_VERSION)
GLOG_VERSION ?= 0.3.0
GLOG_DIR ?= $(HOME)/glog/$(GLOG_VERSION)
OUTPUT ?= output

PROJ = foster
ANTLR_JAR = $(ANTLR_DIR)/antlr-$(ANTLR_VERSION).jar

CXXFLAGS += -g -I $(OUTPUT)

ANTLR_CFLAGS = -I $(ANTLR_DIR)/include
ANTLR_LDFLAGS = -L $(ANTLR_DIR)/lib -l antlr3c
LLVM_CFLAGS := $(shell $(LLVM_DIR)/bin/llvm-config --cppflags)
LLVM_LDFLAGS := $(shell $(LLVM_DIR)/bin/llvm-config --ldflags --libs core jit native)
GLOG_CONFIG := $(shell PKG_CONFIG_PATH=$(GLOG_DIR)/lib/pkgconfig pkg-config --cflags --libs libglog)

default: $(OUTPUT)/foster

clean:
	rm -f output/foster.o $(OUTPUT)/ANTLRtoFosterAST.o $(OUTPUT)/FosterAST.o

$(OUTPUT)/ANTLRtoFosterAST.o: compiler/ANTLRtoFosterAST.cpp
	$(CXX) $(CXXFLAGS) $(ANTLR_CFLAGS) $(LLVM_CFLAGS) $(GLOG_CONFIG) $? -c -o $@

$(OUTPUT)/FosterAST.o: compiler/FosterAST.cpp
	$(CXX) $(CXXFLAGS) $(LLVM_CFLAGS) $(GLOG_CONFIG) $? -c -o $@

$(OUTPUT)/foster.o: compiler/foster.cpp
	$(CXX) $(CXXFLAGS) $(ANTLR_CFLAGS) $(LLVM_CFLAGS) $(GLOG_CONFIG) $? -c -o $@

foster_DEPS = $(OUTPUT)/foster.o \
	      $(OUTPUT)/FosterAST.o \
	      $(OUTPUT)/ANTLRtoFosterAST.o \
	      $(OUTPUT)/$(PROJ)Parser.o \
	      $(OUTPUT)/$(PROJ)Lexer.o \
	      $(NULL)

$(OUTPUT)/foster: $(foster_DEPS)
	$(CXX) $(CXXFLAGS) $? $(ANTLR_LDFLAGS) $(LLVM_LDFLAGS) $(GLOG_CONFIG) -o $(OUTPUT)/foster

$(OUTPUT)/$(PROJ)Parser.o: $(OUTPUT)/$(PROJ)Parser.c
	$(CXX) $(CXXFLAGS) $? -c -o $@

$(OUTPUT)/$(PROJ)Lexer.o: $(OUTPUT)/$(PROJ)Lexer.c
	$(CXX) $(CXXFLAGS) $? -c -o $@

# and Lexer.c, implicitly
$(OUTPUT)/$(PROJ)Parser.c: grammar/foster.g
	python run_antlr.py $(ANTLR_JAR) $(OUTPUT) grammar/foster.g


jrefresh:
	javac -cp $(ANTLR_JAR) grammar/output/$(PROJ)Lexer.java
	javac -cp $(ANTLR_JAR) grammar/output/$(PROJ)Parser.java

testg:
	java -cp "$(ANTLR_JAR):grammar/output" org.antlr.gunit.Interp grammar/foster.gunit

