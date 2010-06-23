#include <inttypes.h>
#include <string>

namespace foster {
namespace runtime {
namespace gc {

void initialize();
void cleanup();
std::string format_ref(void*);

//void visitGCRoots(void (*Visitor)(void **Root, const void *Meta));

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

} } } // namespace foster::runtime::gc

extern foster::runtime::gc::StackEntry *llvm_gc_root_chain;
