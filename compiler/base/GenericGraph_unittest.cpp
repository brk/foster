// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/GenericGraph.h"
#include "dot/GenericGraphTraits.h"
#include "gtest/gtest.h"

#include "llvm/Support/raw_ostream.h"
#include "llvm/ADT/DepthFirstIterator.h"
#include "llvm/ADT/SCCIterator.h"

#include <string>

using namespace foster;

namespace {
  
std::string dfsNodes(GenericGraph<std::string>& g) {
  typedef llvm::df_iterator< GenericGraph<std::string>* > DFI;
  
  std::string s;
  llvm::raw_string_ostream ss(s);

  for (DFI it = llvm::df_begin(&g),
           e  = llvm::df_end(&g); it != e; ++it) {
    if (!(*it)->isVirtualRoot()) {
      ss << (*it)->getValue() << " ";
    }
  }

  return ss.str();
}

std::string sccNodes(GenericGraph<std::string>& g) {
  typedef GenericGraph<std::string>::Node Node; 
  typedef std::vector< Node* > SCC;
  //std::vector<SCC>
  typedef llvm::scc_iterator< GenericGraph<std::string>* > SCI;
  
  std::string s;
  llvm::raw_string_ostream ss(s);
  
  for (SCI it = llvm::scc_begin(&g),
           e  = llvm::scc_end(&g); it != e; ++it) {
    SCC& scc = *it;
    bool didOutput = false;
    for (size_t i = 0; i < scc.size(); ++i) {
      if (!scc[i]->isVirtualRoot()) {
        ss << (scc[i])->getValue() << " ";
        didOutput = true;
      }
    }
    if (didOutput) {
      ss << "\n";
    }
  }
  return ss.str();
}

TEST(GenericGraphTest, depth_first_iteration) {
  GenericGraph<std::string> g;
  typedef GenericGraph<std::string>::Node Node; 

  Node* b = g.addNode("b");
  Node* a = g.addNode("a");
  Node* c = g.addNode("c");
  Node* d = g.addNode("d");

  g.addDirectedEdge(a, b, NULL);
  g.addDirectedEdge(b, c, NULL);
  g.addDirectedEdge(c, d, NULL);
  g.addDirectedEdge(d, c, NULL);
  
  // Before setting an entry node, we use a virtual entry node to ensure
  // that we see the entire graph.
  
  // Note: this matches the order of insertion, not the view from "a".
  EXPECT_EQ("b c d a ", dfsNodes(g));
  
  EXPECT_EQ("d c \n"
            "b \n"
            "a \n", sccNodes(g));
  
  // After setting an entry node, we don't "see" the whole graph.
  
  g.setEntryNode(b);
  
  EXPECT_EQ("b c d ", dfsNodes(g));
  
  EXPECT_EQ("d c \n"
            "b \n", sccNodes(g));
  
  // Until we set an entry node as the "root" of the graph.
  
  g.setEntryNode(a);
    
  // Note: this matches the view from "a", not the
  // order of insertion.
  EXPECT_EQ("a b c d ", dfsNodes(g));
  
  EXPECT_EQ("d c \n"
            "b \n"
            "a \n", sccNodes(g));
}

/////////////////////////////////



} // unnamed namespace

