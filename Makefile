LLVM_DIR ?= $(HOME)/llvm/2.6
ANTLR_VERSION ?= 3.2
ANTLR_DIR ?= $(HOME)/antlr/$(ANTLR_VERSION)
GLOG_VERSION ?= 0.3.0
GLOG_DIR ?= $(HOME)/glog/$(GLOG_VERSION)
OUTPUT ?= output

PROJ = foster

CXXFLAGS += -g -I $(OUTPUT) -I $(ANTLR_DIR)/include -L $(ANTLR_DIR)/lib -l antlr3c
LLVM_CONFIG := $(shell $(LLVM_DIR)/bin/llvm-config --cppflags --ldflags --libs core jit native)
GLOG_CONFIG := $(shell PKG_CONFIG_PATH=$(GLOG_DIR)/lib/pkgconfig pkg-config --cflags --libs libglog)

default: $(OUTPUT)/foster

$(OUTPUT)/foster: compiler/foster.cpp $(OUTPUT)/$(PROJ)Parser.o $(OUTPUT)/$(PROJ)Lexer.o
	$(CXX) $(CXXFLAGS) $(LLVM_CONFIG) $(GLOG_CONFIG) $? -o $(OUTPUT)/foster

$(OUTPUT)/$(PROJ)Parser.o: $(OUTPUT)/$(PROJ)Parser.c
	$(CXX) $(CXXFLAGS) $? -c -o $@

$(OUTPUT)/$(PROJ)Lexer.o: $(OUTPUT)/$(PROJ)Lexer.c
	$(CXX) $(CXXFLAGS) $? -c -o $@

$(OUTPUT)/$(PROJ)Parser.c:
	python run_antlr.py $(ANTLR_DIR)/antlr-$(ANTLR_VERSION).jar $(OUTPUT) grammar/foster.g 

$(OUTPUT)/$(PROJ)Lexer.c: grammar/foster.g
	python run_antlr.py $(ANTLR_DIR)/antlr-$(ANTLR_VERSION).jar $(OUTPUT) grammar/foster.g 
