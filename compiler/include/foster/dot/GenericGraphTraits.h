// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_GENERIC_GRAPH_TRAITS_H
#define FOSTER_GENERIC_GRAPH_TRAITS_H

#include "llvm/IR/CFG.h"
#include "llvm/Support/GraphWriter.h"

// Implicitly included by base/GenericGraph.h

namespace llvm {

template <typename NodePayload>
struct GraphTraits<foster::GenericGraph<NodePayload> *> {
  typedef typename foster::GenericGraph<NodePayload>::Node           NodeType;
  typedef typename foster::GenericGraph<NodePayload>::Node::iterator ChildIteratorType;
  typedef typename foster::GenericGraph<NodePayload>::nodes_iterator nodes_iterator;

  static NodeType* getEntryNode(foster::GenericGraph<NodePayload>* g) { return g->getEntryNode(); }
  static inline ChildIteratorType child_begin(NodeType* n) { return n->succ_begin(); }
  static inline ChildIteratorType child_end(NodeType* n) {   return n->succ_end(); }
  
  static inline nodes_iterator nodes_begin(foster::GenericGraph<NodePayload>* g) { return g->nodes_begin(); }
  static inline nodes_iterator nodes_end(foster::GenericGraph<NodePayload>* g) {   return g->nodes_end(); }
};

////////////////////////////////////////////////////////////////////

namespace {
  static const char* staticGraphvizColors[] = {
    "black",
    "blue",
    "gold",
    "cornflowerblue",
    "forestgreen",
    "darkorchid1",
    "firebrick4"
  };
}

#define ARRAY_SIZE(a) (sizeof(a)/sizeof(a[0]))

template <typename NodePayload>
struct DOTGraphTraits< foster::GenericGraph<NodePayload>* > : public DefaultDOTGraphTraits {
                                                                   
  DOTGraphTraits(bool isSimple=true) : DefaultDOTGraphTraits(isSimple) {}

  static std::string getGraphName(foster::GenericGraph<NodePayload>* g) {
    std::string s;
    llvm::raw_string_ostream ss(s);
    ss << "Generic Graph (" << g->getNodeCount() << " nodes)";
    return ss.str();
  }

  std::string getNodeLabel(typename foster::GenericGraph<NodePayload>::Node* node,
                           foster::GenericGraph<NodePayload>* g) {                
    std::string s;
    llvm::raw_string_ostream ss(s);
    ss << node->getValue();
    if (node->getSCCId() != 0) {
      ss << " (:" << node->getSCCId() << ")";
    }
    return ss.str();
  }
  
  static std::string getNodeAttributes(
            typename foster::GenericGraph<NodePayload>::Node* node,
            foster::GenericGraph<NodePayload>* g) {
    return "color=" + std::string(staticGraphvizColors[
                          node->getSCCId() % ARRAY_SIZE(staticGraphvizColors)
                              ]);
  }
};

} // namespace llvm

#endif
