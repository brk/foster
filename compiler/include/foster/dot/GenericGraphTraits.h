// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_GENERIC_GRAPH_TRAITS_H
#define FOSTER_GENERIC_GRAPH_TRAITS_H

#include "llvm/Support/CFG.h"
#include "llvm/Support/GraphWriter.h"

#include "base/GenericGraph.h"

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

template <typename NodePayload>
struct DOTGraphTraits< foster::GenericGraph<NodePayload>* > : public DefaultDOTGraphTraits {

  DOTGraphTraits(bool isSimple=true) : DefaultDOTGraphTraits(isSimple) {}

  static std::string getGraphName(const foster::GenericGraph<NodePayload>* g) {
    return std::string("Generic Graph");
  }

  std::string getNodeLabel(const typename foster::GenericGraph<NodePayload>::Node* node,
                           const foster::GenericGraph<NodePayload>* g) {
    std::string s;
    llvm::raw_string_ostream ss(s);
    ss << *node;
    return ss.str();
  }
};

} // namespace llvm

#endif
