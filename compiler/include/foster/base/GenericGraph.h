// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_GENERIC_GRAPH_H
#define FOSTER_GENERIC_GRAPH_H

#include "llvm/ADT/UniqueVector.h"

#include <set>
#include <utility>

namespace foster {

// In order to deal with graphs that don't resemble CFGs,
// which is to say those without designated entry nodes,
// this graph class maintains a virtual entry node which
// points to every added node.
//
template <typename NodePayload>
class GenericGraph {
public:  
  typedef void* EdgeLabel;
  
  class Node {
    GenericGraph* g;
    unsigned id;
    
    unsigned getPayloadIndex() { return id; }
  public:
    Node(GenericGraph* g, unsigned i) : g(g), id(i) {}
    
    unsigned getIndex() { return id; }
    bool isVirtualRoot() { return id == 0; }
    const NodePayload& getValue() { return g->payloads[getPayloadIndex()]; }
    
    typedef typename std::vector< Node* >::iterator iterator;
    
    iterator succ_begin() { return g->adjList[getIndex()].begin(); }
    iterator succ_end() {   return g->adjList[getIndex()].end(); }
    
    bool operator<(const Node& other) { return id < other.id; }
  };
  
  typedef typename std::vector< Node >::iterator nodes_iterator;
  // Note that we return an iterator that ignores the virtual root...
  nodes_iterator nodes_begin() { nodes_iterator it = nodes.begin(); return ++it; }
  nodes_iterator nodes_end()   { return nodes.end(); }
  
  typedef Node* NodePtr;
  
  NodePtr addNode(const NodePayload& payload) {
    size_t orig = payloads.size();
    unsigned n = payloads.insert(payload);
    NodePtr node = new Node(this, n);
    if (orig < payloads.size()) {
      nodes.push_back(node);
      std::vector<Node*> v;
      adjList.push_back(v);
      
      // Until we see an edge to this node, we'll assume
      // it could be a source.
      possibleSources.insert(node);
    }
    return node;
  }
  
  void addDirectedEdge(NodePtr a, NodePtr b, EdgeLabel label) {
    adjList[a->getIndex()].push_back(b);
    edgeLabels[ std::make_pair(a, b) ]  = label;
    
    // If we have an edge from a to b, then we know
    // that b cannot be a source in the graph.
    possibleSources.erase(b);
  }
  
  // Setting to NULL restores the virtual root node.
  NodePtr setEntryNode(NodePtr nu) {
    NodePtr old = entryNode;
    entryNode = nu;
    return old;
  }
  
  NodePtr getEntryNode() {
    if (payloads.empty()) {
      return NULL;
    } else if (entryNode) {
      return entryNode;
    } else {
      resetVirtualRootEdges();
      entryNode = nodes[0];
      return entryNode;
    }
  }
  
  GenericGraph() : entryNode(NULL) {
    nodes.push_back(new Node(this, 0)); // virtual "root"
    std::vector<Node*> v;
    adjList.push_back(v);
  }
  
private:
  NodePtr entryNode;
  llvm::UniqueVector<NodePayload> payloads;
  std::vector< NodePtr > nodes;
  std::map< std::pair<NodePtr, NodePtr>, EdgeLabel > edgeLabels;
  std::vector< std::vector< NodePtr > > adjList;

  void resetVirtualRootEdges() {
    adjList[0].clear();
    for (typename std::set< NodePtr >::iterator it = possibleSources.begin();
                                            it != possibleSources.end(); ++it) {
      adjList[0].push_back(*it);
    }
  }
  std::set< NodePtr > possibleSources;
};

} // namespace foster

#endif // include guard
