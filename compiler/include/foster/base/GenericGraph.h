// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_GENERIC_GRAPH_H
#define FOSTER_GENERIC_GRAPH_H

#include "base/Assert.h"

#include "llvm/ADT/UniqueVector.h"

#include "llvm/ADT/PostOrderIterator.h"
#include "llvm/ADT/SCCIterator.h"
#include "llvm/ADT/PointerIntPair.h"

#include "llvm/Support/raw_ostream.h"

#include <algorithm>
#include <set>
#include <utility>

#include "llvm/Support/GraphWriter.h"

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
    const NodePayload& getValue() {
      ASSERT(!isVirtualRoot());
      return g->payloads[getPayloadIndex()];
    }

    typedef typename std::vector< Node* >::iterator iterator;

    iterator succ_begin() { return g->adjList[getIndex()].begin(); }
    iterator succ_end() {   return g->adjList[getIndex()].end(); }

    // Computed SCC ids start at 1, while 0 means an uncomputed id.
    unsigned getSCCId() { return g->sccIds[getIndex()]; }

    bool operator<(const Node& other) { return id < other.id; }
  };

  typedef typename std::vector< Node* >::iterator nodes_iterator;
  // Note that we return an iterator that ignores the virtual root...
  nodes_iterator nodes_begin() { nodes_iterator it = nodes.begin(); return ++it; }
  nodes_iterator nodes_end()   { return nodes.end(); }

  typedef Node* NodePtr;
  typedef std::pair< NodePtr, NodePtr > Edge;

  std::vector< NodePtr > getSources() {
    resetVirtualRootEdges();
    return adjList[0];
  }

  std::vector< NodePtr > getTopologicalSort() {
    std::vector< NodePtr > rv;
    typedef llvm::po_iterator< GenericGraph* > POI;
    for (POI it = llvm::po_begin(this), e = llvm::po_end(this); it != e; ++it) {
      if (!(*it)->isVirtualRoot()) {
        rv.push_back(*it);
      }
    }
    std::reverse(rv.begin(), rv.end());
    return rv;
  }

  NodePtr addNode(const NodePayload& payload) {
    size_t orig = payloads.size();
    // n is a one-based index corresponding to the index of the payload
    // in the payloads vector, which happens to correpond with the contents
    // of the nodes vectors.
    unsigned n = payloads.insert(payload);
    NodePtr node = NULL;
    if (orig < payloads.size()) {
      node = new Node(this, n);
      nodes.push_back(node);
      std::vector<Node*> v;
      adjList.push_back(v);

      // Until we see an edge to this node, we'll assume
      // it could be a source.
      possibleSources.insert(node);

      // We only compute SCC information as requested
      sccIds.push_back(0);
    } else {
      node = nodes[n];
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
    if (!entryNode) {
      resetVirtualRootEdges();
      ASSERT(!nodes.empty());
      entryNode = nodes[0];
    }
    return entryNode;
  }

  // Returns the number of components identified.
  unsigned computeSCCs() {
    typedef llvm::scc_iterator<GenericGraph*> SCI;
    typedef std::vector<NodePtr> SCC;

    // Note: by starting actual SCC ids at 1 (and initializing to zero
    // before computing SCCs) it's easy for graphviz to tell whether we've
    // computed SCCs without needing to query the graph.
    unsigned sccId = 1;
    for (SCI it = llvm::scc_begin(this), e = llvm::scc_end(this); it != e; ++it) {
      SCC& scc = *it;
      for (typename SCC::iterator cit = scc.begin(); cit != scc.end(); ++cit) {
        Node* node = *cit;
        sccIds[node->getIndex()] = sccId;
      }
      ++sccId;
    }
    return sccId - 1;
  }

  struct SCCSubgraph {
    std::vector<NodePtr> nodes;
    std::vector<Edge> incomingEdges;
    std::vector<Edge> outgoingEdges;
    std::vector<Edge> internalEdges;
  };

  // Clears the given output parameters, computes the SCCs of
  // the current graph, and copies information about the identified
  // subgraphs to the given output parameters.
  //
  // The |subgraphs| output parameter will contain a subgraph for every
  // identified SCC, with edges separated into internal, incoming,
  // and outgoing. (External edges do not appear in the subgraph).
  //
  // The |dagOfSCCs| output parameter will have one node per SCC
  // identified, with one or more edges between SCCs implying the presence
  // of exactly one edge between nodes representing SCCs.
  // The dagOfSCCs will have its edges classified as a side effect
  // of this function verifying that it does, in fact, form a DAG.
  //
  // Calls computeSCCs internally, so the caller need not bother.
  void decomposeIntoStronglyConnectedSubgraphs(
              std::vector<SCCSubgraph>& subgraphs,
              GenericGraph<unsigned>& dagOfSCCs) {
    subgraphs.clear();
    unsigned numSCCs = computeSCCs();
    subgraphs.resize(numSCCs);

    // Add each node pointer to the appropriate SCC subgraph.
    for (size_t i = 0; i < nodes.size(); ++i) {
      Node* node = nodes[i];
      if (node->getSCCId() > 0) {
        subgraphs[node->getSCCId() - 1].nodes.push_back(node);
      }
    }

    typedef std::set< std::pair<unsigned, unsigned> > DagEdgeSet;
    DagEdgeSet dagEdges;

    // Add each edge to the subgraphs it connects.
    for (typename std::map< std::pair<NodePtr, NodePtr>, EdgeLabel >::iterator
          it = edgeLabels.begin(); it != edgeLabels.end(); ++it) {
      std::pair<NodePtr, NodePtr> edge = (*it).first;
      int tailComponent = edge.first->getSCCId()  - 1;
      int headComponent = edge.second->getSCCId() - 1;
      if (tailComponent < 0 || headComponent < 0) {
        continue; // ignore edges to or from the virtual root.
      }
      if (tailComponent == headComponent) {
        subgraphs[tailComponent].internalEdges.push_back(edge);
      } else {
        subgraphs[tailComponent].outgoingEdges.push_back(edge);
        subgraphs[headComponent].incomingEdges.push_back(edge);
        dagEdges.insert( std::make_pair(tailComponent, headComponent) );
      }
    }

    dagOfSCCs.reset();
    // Add edges to the SCC-DAG graph corresponding to the edges
    // beween SCCs in the original graph.
    for (DagEdgeSet::iterator it = dagEdges.begin();
                              it != dagEdges.end(); ++it) {
      typedef GenericGraph<unsigned>::NodePtr DagNode;
      DagNode t = dagOfSCCs.addNode((*it).first);
      DagNode h = dagOfSCCs.addNode((*it).second);
      dagOfSCCs.addDirectedEdge(t, h, NULL);
    }

    bool dagOfSCCsWasActualDAG = dagOfSCCs.classifyEdgesDFSFrom(
                                          dagOfSCCs.getEntryNode());
    ASSERT(dagOfSCCsWasActualDAG) << "numSCCs identified: " << numSCCs;
  }

  GenericGraph() {
    init_();
  }

  void reset() {
    nodes.clear();
    sccIds.clear();
    adjList.clear();
    payloads.reset();
    edgeLabels.clear();
    possibleSources.clear();
    edgeClassifications.clear();

    init_();
  }
private:
  void init_() {
    entryNode = NULL;
    nodes.push_back(new Node(this, 0)); // virtual "root"

    std::vector<NodePtr> v;
    adjList.push_back(v);
    sccIds.push_back(0);
  }
public:

  unsigned getNodeCount() const {
    return nodes.size() - 1; // Don't include the virtual root node.
  }

  enum EdgeKind { eUnknowneEdge, eTreeEdge, eBackEdge, eCrossEdge, eDownEdge };

  // Should be called after calling classifyEdgesFrom(somenode)
  EdgeKind getEdgeClassification(NodePtr head, NodePtr tail) {
    return edgeClassifications[Edge(head, tail)];
  }

  // Returns true if the graph DOES form a DAG.
  //
  // Pre/post marking algorithm adapted from Program 19.2 of Sedgewick's
  // Graph Algorithms with C, "DFS of a digraph".
  bool classifyEdgesDFSFrom(NodePtr start) {
    std::vector<Edge> worklist;

    // The nodes in a subgraph are sparsely numbered, so we use
    // maps instead of vectors and index by node pointers instead of node ids.
    std::map<NodePtr, int> pre;
    std::map<NodePtr, int> post;
    for (size_t i = 0; i < nodes.size(); ++i) {
      pre[nodes[i]] = -1; post[nodes[i]] = -1;
    }
    int cntPre = 0;
    int cntPost = 0;
    bool sawBackEdges = false;

    // Computing post-order numbering is trivial in a recursive DFS
    // implementation, but trickier with an explicit stack, because the
    // postorder number needs to be assigned after the last descendent has
    // been processed, whereas we can only "directly" see immediate children.
    //
    // My solution is to stick a marker on the DFS stack before processing
    // child nodes; when we see the marker again, we can assign a postorder
    // number. In this case, the marker is an edge from NULL to a given node.
    worklist.push_back(Edge(NULL, start));
    pre[start] = cntPre++;
    // Initialize the worklist with the outgoing edges of the start node.
    // This is basically a duplication of the body of the worklist loop,
    // except we don't do any edge classification.
    for (typename Node::iterator it = start->succ_begin();
                                 it != start->succ_end(); ++it) {
      worklist.push_back(Edge(start, *it));
    }

    while (!worklist.empty()) {
      Edge ht = worklist.back(); worklist.pop_back();
      NodePtr from = ht.first;
      NodePtr node = ht.second;
      if (from == NULL) {
        post[node] = cntPost++; // Finished visiting children of the given node.
        continue;
      }

      // Add marker to stack before visiting children.
      worklist.push_back(Edge(NULL, node));

      if (pre[node] == -1) {
        pre[node] = cntPre++; // Starting to visit children of the given node.

        for (typename Node::iterator it = node->succ_begin();
                                     it != node->succ_end(); ++it) {
          worklist.push_back(Edge(node, *it));
        }

        edgeClassifications[ht] = eTreeEdge;
      } else {
        if (post[node] == -1) { edgeClassifications[ht] = eBackEdge;
          sawBackEdges = true;
        } else if (pre[node] > pre[from]) { edgeClassifications[ht] = eDownEdge;
        } else { edgeClassifications[ht] = eCrossEdge; }
      }
    }
    return !sawBackEdges;
  }

private:
  NodePtr                             entryNode;
  llvm::UniqueVector<NodePayload>     payloads;
  std::vector<NodePtr>                nodes;
  std::map<Edge, EdgeLabel>           edgeLabels;
  std::vector< std::vector<NodePtr> > adjList;

  std::map<Edge, EdgeKind> edgeClassifications;

  std::vector<unsigned>    sccIds;

  std::set<NodePtr>        possibleSources;

  void resetVirtualRootEdges() {
    adjList[0].clear();
    if (possibleSources.empty()) {
      // Not dealing with a DAG! Thus the virtual entry node has
      // no designated source nodes to which it should solely point,
      // and so we keep the virtual root pointing at all the other nodes.
      // This ensures that SCC iteration will find every SCC, for example.
      //
      // This will of course give garbage for iterators that expect a
      // "reasonable" entry node, but unless the user provides one explicitly,
      // this is the best we can do under the circumstances.
      for (size_t i = 1; i < nodes.size(); ++i) {
        adjList[0].push_back(nodes[i]);
      }
    } else {
      for (typename std::set< NodePtr >::iterator it = possibleSources.begin();
                                              it != possibleSources.end(); ++it) {
        adjList[0].push_back(*it);
      }
    }
  }
};

} // namespace foster

#include "dot/GenericGraphTraits.h"

#endif // include guard
