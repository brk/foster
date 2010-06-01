#include <inttypes.h>

/// @brief The map for a single function's stack frame. One of these is
///        compiled as constant data into the executable for each function.
/// 
/// Storage of metadata values is elided if the %metadata parameter to
/// @llvm.gcroot is null.
struct FrameMap {
  int32_t NumRoots;    //< Number of roots in stack frame.
  int32_t NumMeta;     //< Number of metadata entries. May be < NumRoots.
  const void *Meta[0]; //< Metadata for each root.
};

/// @brief A link in the dynamic shadow stack. One of these is embedded in the
///        stack frame of each function on the call stack.
struct StackEntry {
  StackEntry *Next;    //< Link to next stack entry (the caller's).
  const FrameMap *Map; //< Pointer to constant FrameMap.
  void *Roots[0];      //< Stack roots (in-place array).
};

/// @brief The head of the singly-linked list of StackEntries. Functions push
///        and pop onto this in their prologue and epilogue.
/// 
/// Since there is only a global list, this technique is not threadsafe.
extern StackEntry *llvm_gc_root_chain;

void visitGCRoots(void (*Visitor)(void **Root, const void *Meta));

