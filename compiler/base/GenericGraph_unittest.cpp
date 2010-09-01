// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/GenericGraph.h"
#include "dot/GenericGraphTraits.h"
#include "gtest/gtest.h"

#include "llvm/Support/raw_ostream.h"
#include "llvm/ADT/DepthFirstIterator.h"
#include "llvm/ADT/PostOrderIterator.h"
#include "llvm/ADT/SCCIterator.h"

#include <string>

using namespace foster;

namespace {

template <typename T>
std::string dfsNodes(GenericGraph<T>& g) {
  typedef llvm::df_iterator< GenericGraph<T>* > DFI;
  
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

template <typename T>
std::string poNodes(GenericGraph<T>& g) {
  typedef llvm::po_iterator< GenericGraph<T>* > POI;
  
  std::string s;
  llvm::raw_string_ostream ss(s);

  for (POI it = llvm::po_begin(&g),
           e  = llvm::po_end(&g); it != e; ++it) {
    if (!(*it)->isVirtualRoot()) {
      ss << (*it)->getValue() << " ";
    }
  }

  return ss.str();
}

template <typename T>
std::string sccNodes(GenericGraph<T>& g) {

  typedef llvm::scc_iterator< GenericGraph<T>* > SCI;
  
  typedef std::vector< typename GenericGraph<T>::Node* > SCC;
  //std::vector<SCC>
  
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
    
  
  EXPECT_EQ("d c \n"
            "b \n"
            "a \n", sccNodes(g));
}

/////////////////////////////////

// Example graph from the wikipedia article on tsort:
// http://en.wikipedia.org/wiki/Tsort_(Unix)
//
//        5       7      3
//        |    /  |    / |
//        v  /    v  /   |
//        11      8      |
//        | \ \--\|      |
//        v   \   v\----\|
//        2       9      10
TEST(GenericGraphTest, postorder_iteration) {
  typedef GenericGraph<int> Graph;
  Graph g;
  typedef Graph::Node Node; 

  Node* n2  = g.addNode(2);
  Node* n9  = g.addNode(9);
  Node* n10 = g.addNode(10);
  Node* n11 = g.addNode(11);
  Node* n8  = g.addNode(8);
  Node* n3  = g.addNode(3);
  Node* n7  = g.addNode(7);
  Node* n5  = g.addNode(5);

  g.addDirectedEdge(n11, n2, NULL);
  g.addDirectedEdge(n11, n9, NULL);
  g.addDirectedEdge(n11, n10, NULL);
  g.addDirectedEdge(n8, n9, NULL);
  g.addDirectedEdge(n5, n11, NULL);
  g.addDirectedEdge(n7, n11, NULL);
  g.addDirectedEdge(n7, n8, NULL);
  g.addDirectedEdge(n3, n8, NULL);
  g.addDirectedEdge(n3, n10, NULL);
  
  //EXPECT_EQ("3 8 9 10 7 11 2 5 ", dfsNodes(g));
  //EXPECT_EQ("7 11 2 9 10 8 5 3 ", dfsNodes(g));
  
  //EXPECT_EQ("9 8 10 3 2 11 7 5 ", poNodes(g));
  //EXPECT_EQ("2 9 10 11 8 7 5 3 ", poNodes(g));
}

/////////////////////////////////

} // unnamed namespace

