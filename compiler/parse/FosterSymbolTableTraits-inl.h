// gScope : SymbolTable<foster::SymbolInfo>

#include <sstream>
#include <iostream>
#include "llvm/Support/raw_ostream.h"

namespace foster {
std::string
getFullSymbolInfoNodeLabel(
    const foster::SymbolTable<foster::SymbolInfo>::LexicalScope* node,
    const foster::SymbolTable<foster::SymbolInfo>* graph);
}
namespace foster {
std::string
getFullTypeASTNodeLabel(
    const foster::SymbolTable<TypeAST>::LexicalScope* node,
    const foster::SymbolTable<TypeAST>* graph);
}


#define FOSTER_SYMTAB foster::SymbolTable<foster::SymbolInfo>

namespace llvm {

template <>
struct GraphTraits<FOSTER_SYMTAB::LexicalScope*> {
  typedef FOSTER_SYMTAB::LexicalScope          NodeType;
  typedef llvm::SuccIterator<NodeType*,
              NodeType >                  ChildIteratorType;

  static NodeType* getEntryNode(NodeType* fls) { return fls; }
  static inline ChildIteratorType child_begin(NodeType* n) {
    return ChildIteratorType(n);
  }
  static inline ChildIteratorType child_end(NodeType* n) {
    return ChildIteratorType(n, true);
  }
};


template <>
struct GraphTraits<FOSTER_SYMTAB*>
      : public GraphTraits<FOSTER_SYMTAB::LexicalScope*> {

  static NodeType* getEntryNode(FOSTER_SYMTAB* f) {
    return f->_private_getCurrentScope();
  }

  typedef std::vector<FOSTER_SYMTAB::LexicalScope*>::iterator
                                                     nodes_iterator;
  static nodes_iterator    nodes_begin(FOSTER_SYMTAB* f) {
    return f->_private_allScopes.begin(); }
  static nodes_iterator    nodes_end  (FOSTER_SYMTAB* f) {
    return f->_private_allScopes.end(); }
};


template <>
struct DOTGraphTraits<FOSTER_SYMTAB*>
      : public DefaultDOTGraphTraits {

  DOTGraphTraits(bool isSimple=false) : DefaultDOTGraphTraits(isSimple) {}

  static std::string getGraphName(const FOSTER_SYMTAB*) {
    return string("Foster varScope Table");
  }

  std::string
  getNodeLabel(const FOSTER_SYMTAB::LexicalScope* node,
               const FOSTER_SYMTAB* graph) {
    return isSimple() ? getSimpleNodeLabel(node, graph)
                      : getFullNodeLabel(node, graph);
  }

  static std::string
  getSimpleNodeLabel(const FOSTER_SYMTAB::LexicalScope* node,
                     const FOSTER_SYMTAB* graph) {
    std::stringstream ss;
    ss << node->getName() << "(@ " << node << ")";
    return ss.str();
  }

  static std::string
  getFullNodeLabel(const FOSTER_SYMTAB::LexicalScope* node,
                   const FOSTER_SYMTAB* graph) {
    return std::string(foster::getFullSymbolInfoNodeLabel(node, graph));
  }

  static std::string
  getEdgeSourceLabel(const FOSTER_SYMTAB::LexicalScope* node,
                     llvm::SuccIterator<
                           FOSTER_SYMTAB::LexicalScope*,
                           FOSTER_SYMTAB::LexicalScope > I) {
    return "";
  }
};

} // namespace llvm

#undef FOSTER_SYMTAB

////////////////////////////////////////////////////////////////////

// gTypeScope    : SymbolTable<TypeAST>

#define FOSTER_SYMTAB foster::SymbolTable<TypeAST>

namespace llvm {

template <>
struct GraphTraits<FOSTER_SYMTAB::LexicalScope*> {
  typedef FOSTER_SYMTAB::LexicalScope          NodeType;
  typedef llvm::SuccIterator<NodeType*,
                    NodeType >                  ChildIteratorType;

  static NodeType* getEntryNode(NodeType* fls) { return fls; }
  static inline ChildIteratorType child_begin(NodeType* n) {
    return ChildIteratorType(n);
  }
  static inline ChildIteratorType child_end(NodeType* n) {
    return ChildIteratorType(n, true);
  }
};

template <>
struct GraphTraits<FOSTER_SYMTAB*>
      : public GraphTraits<FOSTER_SYMTAB::LexicalScope*> {

  static NodeType* getEntryNode(FOSTER_SYMTAB* f) {
    return f->_private_getCurrentScope();
  }

  typedef std::vector<FOSTER_SYMTAB::LexicalScope*>::iterator
                                                     nodes_iterator;
  static nodes_iterator    nodes_begin(FOSTER_SYMTAB* f) {
    return f->_private_allScopes.begin(); }
  static nodes_iterator    nodes_end  (FOSTER_SYMTAB* f) {
    return f->_private_allScopes.end(); }
};


template <>
struct DOTGraphTraits<FOSTER_SYMTAB*>
      : public DefaultDOTGraphTraits {

  DOTGraphTraits(bool isSimple=false) : DefaultDOTGraphTraits(isSimple) {}

  static std::string getGraphName(const FOSTER_SYMTAB*) {
    return string("Foster Value scope");
  }

  std::string
  getNodeLabel(const FOSTER_SYMTAB::LexicalScope* node,
               const FOSTER_SYMTAB* graph) {
    return isSimple() ? getSimpleNodeLabel(node, graph)
                      : getFullNodeLabel(node, graph);
  }

  static std::string
  getSimpleNodeLabel(const FOSTER_SYMTAB::LexicalScope* node,
                     const FOSTER_SYMTAB* graph) {
    std::stringstream ss;
    ss << node->getName() << "(@ " << node << ")";
    return ss.str();
  }

  static std::string
  getFullNodeLabel(const FOSTER_SYMTAB::LexicalScope* node,
                   const FOSTER_SYMTAB* graph) {
    return std::string(foster::getFullTypeASTNodeLabel(node, graph));
  }

  static std::string
  getEdgeSourceLabel(const FOSTER_SYMTAB::LexicalScope* node,
                     llvm::SuccIterator<
                           FOSTER_SYMTAB::LexicalScope*,
                           FOSTER_SYMTAB::LexicalScope > I) {
    return "";
  }
};

} // namespace llvm

#undef FOSTER_SYMTAB
