/*BEGIN_LEGAL 
Intel Open Source License 

Copyright (c) 2002-2016 Intel Corporation. All rights reserved.
 
Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are
met:

Redistributions of source code must retain the above copyright notice,
this list of conditions and the following disclaimer.  Redistributions
in binary form must reproduce the above copyright notice, this list of
conditions and the following disclaimer in the documentation and/or
other materials provided with the distribution.  Neither the name of
the Intel Corporation nor the names of its contributors may be used to
endorse or promote products derived from this software without
specific prior written permission.
 
THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
``AS IS'' AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE INTEL OR
ITS CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
END_LEGAL */

#include "pin.H"
#include "xed-get-time.h"
#include <iostream>
#include <fstream>
#include <map>

// Expect slowdown of 10x (.6s -> 3s) for 64-microsecond resolution
// and logfiles of roughly 1 MB / s of original program runtime.

namespace LEVEL_PINCLIENT { extern VOID RTN_InsertFillBuffer(RTN rtn, IPOINT action, BUFFER_ID id, ...); }

// When targeting Mac, need to prefix "_" in front of symbols.

/* ===================================================================== */
/* Global Variables */
/* ===================================================================== */

std::ofstream TraceFile;

UINT64 tsc0;
UINT64 gNumCalls;
bool gDoTrackStackPointer;
bool gDoTrackOCaml;

struct alloc_record {
  UINT64 tsc;
  ADDRINT size;
  UINT32 typ;
};

BUFFER_ID bufid;
PIN_LOCK lock;

// Assuming tsc = cycles, a 2 GHz processor generates 41 tsc bits per second.
//  In practice, it's maybe 10 million "events" per second (33 bps, 112 MB * 1.3)
// So shifting off 12 bits means 29 bits per second; about 2 microsecond resolution.
//  In practice, 150 K events/s (27 bps, 34 MB * 1.3)
//    With histogram encoding [Event Size Count]: 8 MB * 1.3          gzipped 950 KB
//    With histogram encoding [Event SumSize SumCount Max]: 6 MB * 1.3          gzipped 900 KB
//                                                     JSON 8 MB                gzipped 1.4 MB
//
// Shifting off 16 bits would be 25 bits per second, about 64 microsecond resolution.
//  Estimate: 25 bps, 9 MB * 1.3
//  Actual with histogram encoding (E SS SC Max]: 18 K events, 600 KB
//                                                  JSON 730 KB, gzipped 150 KB
//
// Shifting off 20 bits would be 21 bits per second, about 500 microsecond resolution.
#define TSC_TRIM_BITS 16
UINT64 tsc_trim(UINT64 t) { return t >> TSC_TRIM_BITS; }

// TODO histogram encoding:
// Bucket StartTimeStamp EndTimeStamp
//    [Event Size Count]

/* ===================================================================== */
/* Commandline Switches */
/* ===================================================================== */

KNOB<string> KnobOutputFile(KNOB_MODE_WRITEONCE, "pintool",
    "o", "heapstacktrace.out", "specify trace file name");

/* ===================================================================== */

VOID AllocPinHook_2(UINT64 tsc, ADDRINT size) { // memalloc cell
    PIN_GetLock(&lock, 1);
    TraceFile << dec << 2 << " " << hex << tsc_trim(tsc - tsc0) << " " << dec << size << endl;
    PIN_ReleaseLock(&lock);
}

VOID AllocPinHook_3(UINT64 tsc, ADDRINT size) { // memalloc array
    PIN_GetLock(&lock, 1);
    TraceFile << dec << 3 << " " << hex << tsc_trim(tsc - tsc0) << " " << dec << size << endl;
    PIN_ReleaseLock(&lock);
}


VOID BeforeMain(UINT64 tsc) {
    PIN_GetLock(&lock, 1);
    TraceFile << "main-ish " << hex << tsc_trim(tsc - tsc0) << endl;
    PIN_ReleaseLock(&lock);
}

VOID AfterMain(UINT64 tsc) {
    PIN_GetLock(&lock, 1);
    TraceFile << "main-end " << hex << tsc_trim(tsc - tsc0) << endl;
    PIN_ReleaseLock(&lock);
}

UINT64 correct_for_pin_overhead(UINT64 tsc_d) {
  if (tsc_d < 0xdbad) return 0x40;
  return tsc_d - 0xdbad;
}

VOID* CallocWrapper( CONTEXT * context, AFUNPTR orgFuncptr, ADDRINT nelt, ADDRINT eltsz)
{
    VOID * ret;
    UINT64 tsc_begin = xed_get_time();
    PIN_CallApplicationFunction( context, PIN_ThreadId(),
                                 CALLINGSTD_DEFAULT, orgFuncptr,
                                 NULL, PIN_PARG(void *), &ret,
                                 PIN_PARG_END() );
    UINT64 tsc_end = xed_get_time();
    UINT64 tsc_d = correct_for_pin_overhead(tsc_end - tsc_begin);
    PIN_GetLock(&lock, 1);
    TraceFile << "calloc " << dec << (nelt * eltsz) << " " << hex << tsc_trim(tsc_begin - tsc0) << " " << tsc_d << endl;
    PIN_ReleaseLock(&lock);
    return ret;
}

VOID* MallocWrapper( CONTEXT * context, AFUNPTR orgFuncptr, ADDRINT size)
{
    VOID * ret;
    UINT64 tsc_begin = xed_get_time();
    PIN_CallApplicationFunction( context, PIN_ThreadId(),
                                 CALLINGSTD_DEFAULT, orgFuncptr,
                                 NULL, PIN_PARG(void *), &ret,
                                 PIN_PARG_END() );
    UINT64 tsc_end = xed_get_time();
    UINT64 tsc_d = correct_for_pin_overhead(tsc_end - tsc_begin);
    PIN_GetLock(&lock, 1);
    TraceFile << "malloc " << dec << size << " " << hex << tsc_trim(tsc_begin - tsc0) << " " << tsc_d << endl;
    PIN_ReleaseLock(&lock);
    return ret;
}

VOID* FreeWrapper( CONTEXT * context, AFUNPTR orgFuncptr)
{
    VOID * ret;
    UINT64 tsc_begin = xed_get_time();
    PIN_CallApplicationFunction( context, PIN_ThreadId(),
                                 CALLINGSTD_DEFAULT, orgFuncptr,
                                 NULL, PIN_PARG(void *), &ret,
                                 PIN_PARG_END() );
    UINT64 tsc_end = xed_get_time();
    UINT64 tsc_d = correct_for_pin_overhead(tsc_end - tsc_begin);
    PIN_GetLock(&lock, 1);
    TraceFile << "free " << hex << tsc_trim(tsc_begin - tsc0) << " " << tsc_d << endl;
    PIN_ReleaseLock(&lock);
    return ret;
}

VOID* MehWrapper( CONTEXT * context, AFUNPTR orgFuncptr)
{
    VOID * ret;
    UINT64 tsc_begin = xed_get_time();
    PIN_CallApplicationFunction( context, PIN_ThreadId(),
                                 CALLINGSTD_DEFAULT, orgFuncptr,
                                 NULL, PIN_PARG(void *), &ret,
                                 PIN_PARG_END() );
    UINT64 tsc_end = xed_get_time();
    UINT64 tsc_d = correct_for_pin_overhead(tsc_end - tsc_begin);
    PIN_GetLock(&lock, 1);
    TraceFile << "meh " << hex << tsc_trim(tsc_begin - tsc0) << " " << tsc_d << endl;
    PIN_ReleaseLock(&lock);
    return ret;
}

VOID* MmapWrapper( CONTEXT * context, AFUNPTR orgFuncptr)
{
    VOID * ret;
    UINT64 tsc_begin = xed_get_time();
    PIN_CallApplicationFunction( context, PIN_ThreadId(),
                                 CALLINGSTD_DEFAULT, orgFuncptr,
                                 NULL, PIN_PARG(void *), &ret,
                                 PIN_PARG_END() );
    UINT64 tsc_end = xed_get_time();
    UINT64 tsc_d = correct_for_pin_overhead(tsc_end - tsc_begin);
    PIN_GetLock(&lock, 1);
    TraceFile << "mmap " << hex << tsc_trim(tsc_begin - tsc0) << " " << tsc_d << endl;
    PIN_ReleaseLock(&lock);
    return ret;
}

VOID* MremapWrapper( CONTEXT * context, AFUNPTR orgFuncptr)
{
    VOID * ret;
    UINT64 tsc_begin = xed_get_time();
    PIN_CallApplicationFunction( context, PIN_ThreadId(),
                                 CALLINGSTD_DEFAULT, orgFuncptr,
                                 NULL, PIN_PARG(void *), &ret,
                                 PIN_PARG_END() );
    UINT64 tsc_end = xed_get_time();
    UINT64 tsc_d = correct_for_pin_overhead(tsc_end - tsc_begin);
    PIN_GetLock(&lock, 1);
    TraceFile << "mremap " << hex << tsc_trim(tsc_begin - tsc0) << " " << tsc_d << endl;
    PIN_ReleaseLock(&lock);
    return ret;
}

VOID* MprotectWrapper( CONTEXT * context, AFUNPTR orgFuncptr)
{
    VOID * ret;
    UINT64 tsc_begin = xed_get_time();
    PIN_CallApplicationFunction( context, PIN_ThreadId(),
                                 CALLINGSTD_DEFAULT, orgFuncptr,
                                 NULL, PIN_PARG(void *), &ret,
                                 PIN_PARG_END() );
    UINT64 tsc_end = xed_get_time();
    UINT64 tsc_d = correct_for_pin_overhead(tsc_end - tsc_begin);
    PIN_GetLock(&lock, 1);
    TraceFile << "mprotect " << hex << tsc_trim(tsc_begin - tsc0) << " " << tsc_d << endl;
    PIN_ReleaseLock(&lock);
    return ret;
}

VOID* ReallocWrapper( CONTEXT * context, AFUNPTR orgFuncptr, ADDRINT size)
{
    VOID * ret;
    UINT64 tsc_begin = xed_get_time();
    PIN_CallApplicationFunction( context, PIN_ThreadId(),
                                 CALLINGSTD_DEFAULT, orgFuncptr,
                                 NULL, PIN_PARG(void *), &ret,
                                 PIN_PARG_END() );
    UINT64 tsc_end = xed_get_time();
    UINT64 tsc_d = correct_for_pin_overhead(tsc_end - tsc_begin);
    PIN_GetLock(&lock, 1);
    if (size == 0) {
      TraceFile << "free " << hex << tsc_trim(tsc_begin - tsc0) << " " << tsc_d << endl;
    } else {
      TraceFile << "realloc " << dec << size << " " << hex << tsc_trim(tsc_begin - tsc0) << " " << tsc_d << endl;
    }
    PIN_ReleaseLock(&lock);
    return ret;
}

typedef std::map< int, std::map<int, int> >  histmap;

/* ===================================================================== */
/* Analysis routines                                                     */
/* ===================================================================== */

/*!
 * Called when a buffer fills up, or the thread exits, so we can process it or pass it off
 * as we see fit.
 * @param[in] id		buffer handle
 * @param[in] tid		id of owning thread
 * @param[in] ctxt		application context when the buffer filled
 * @param[in] buf		actual pointer to buffer
 * @param[in] numElements	number of records
 * @param[in] v			callback value
 * @return  A pointer to the buffer to resume filling.
 */
VOID * BufferFull(BUFFER_ID id, THREADID tid, const CONTEXT *ctxt, VOID *buf,
                  UINT64 numElements, VOID *v)
{
    UINT64 tsc_begin = xed_get_time();

    PIN_GetLock(&lock, 1);

    struct alloc_record* rc =(struct alloc_record*)buf;

    UINT64 prev_tsc_d_trimmed = 0;

    TraceFile << endl << "A " << hex << rc[0].tsc;

    histmap hist;
    for(UINT64 i = 0; i < numElements; i++) {
      UINT64 tsc_d = (rc[i].tsc - tsc0);
      UINT64 tsc_d_trimmed = tsc_trim(tsc_d);
      if (tsc_d_trimmed == prev_tsc_d_trimmed) {
        hist[ rc[i].typ ][ rc[i].size ]++;
      } else {
        prev_tsc_d_trimmed = tsc_d_trimmed;

        TraceFile << "B " << hex << tsc_d_trimmed << dec;
        for (histmap::iterator t_m = hist.begin(); t_m != hist.end(); ++t_m) {
          int sum_size = 0;
          int sum_count = 0;
          int max_size = 0;
          for (std::map<int,int>::iterator s_c = t_m->second.begin(); s_c != t_m->second.end(); ++s_c) {
            int sz = s_c->first;
            int cnt = s_c->second;
            max_size = (max_size < sz) ? sz : max_size;
            sum_size += (sz * cnt);
            sum_count += cnt;
          }
          // event, sum(size), count, min, max
          TraceFile << " " << t_m->first << " " << sum_size << " " << sum_count << " " << max_size;
        }
        hist.clear();
        TraceFile << endl;

        // dump hist
        //TraceFile << endl << "B " << hex << tsc_d_trimmed;
        //TraceFile << " " << dec << rc[i].typ << " " << rc[i].size;
      }
    }

    UINT64 tsc_end = xed_get_time();
    TraceFile << endl << "BufferFull " << hex << tsc_trim(tsc_end - tsc_begin) << endl;

    PIN_ReleaseLock(&lock);
    return buf;
}

/* ===================================================================== */
/* Instrumentation routines                                              */
/* ===================================================================== */

VOID FindAndInstrument(IMG img, const char* name, AFUNPTR hook) {
    RTN rtn = RTN_FindByName(img, name);
    if (RTN_Valid(rtn))
    {
        RTN_Open(rtn);
        RTN_InsertCall(rtn, IPOINT_BEFORE, hook, IARG_TSC, IARG_FUNCARG_ENTRYPOINT_VALUE, 0, IARG_END);
        RTN_Close(rtn);
    }
}

VOID Image(IMG img, VOID *v)
{
    FindAndInstrument(img, "foster_pin_hook_memalloc_cell", (AFUNPTR) AllocPinHook_2);
    FindAndInstrument(img, "foster_pin_hook_memalloc_array", (AFUNPTR) AllocPinHook_3);

    RTN mmapRtn = RTN_FindByName(img, "mmap");
    if (RTN_Valid(mmapRtn))
    {
      //if (!RTN_IsSafeForProbedReplacementEx(mmapRtn, PROBE_MODE_ALLOW_RELOCATION)) {
      //  TraceFile << "X NoProbedReplace mmap" << endl;
      //}
      PROTO proto = PROTO_Allocate( PIN_PARG(void *), CALLINGSTD_DEFAULT, "mmap", PIN_PARG_END() );

      RTN_ReplaceSignature(mmapRtn, AFUNPTR( MmapWrapper ),
          IARG_PROTOTYPE, proto,
          IARG_CONTEXT,
          IARG_ORIG_FUNCPTR,
          IARG_END);
    }

    RTN mprotectRtn = RTN_FindByName(img, "mprotect");
    if (RTN_Valid(mprotectRtn))
    {
      PROTO proto = PROTO_Allocate( PIN_PARG(void *), CALLINGSTD_DEFAULT, "mprotect", PIN_PARG_END() );

      RTN_ReplaceSignature(mprotectRtn, AFUNPTR( MprotectWrapper ),
          IARG_PROTOTYPE, proto,
          IARG_CONTEXT,
          IARG_ORIG_FUNCPTR,
          IARG_END);
    }

    RTN mremapRtn = RTN_FindByName(img, "mremap");
    if (RTN_Valid(mremapRtn))
    {
      PROTO proto = PROTO_Allocate( PIN_PARG(void *), CALLINGSTD_DEFAULT, "mremap", PIN_PARG_END() );

      RTN_ReplaceSignature(mremapRtn, AFUNPTR( MremapWrapper ),
          IARG_PROTOTYPE, proto,
          IARG_CONTEXT,
          IARG_ORIG_FUNCPTR,
          IARG_END);
    }

    RTN freeRtn = RTN_FindByName(img, "free");
    if (RTN_Valid(freeRtn))
    {
      //if (!RTN_IsSafeForProbedReplacementEx(freeRtn, PROBE_MODE_ALLOW_RELOCATION)) {
      //  TraceFile << "X NoProbedReplace free" << endl;
      //}
      PROTO proto = PROTO_Allocate( PIN_PARG(void *), CALLINGSTD_DEFAULT, "free", PIN_PARG_END() );

      RTN_ReplaceSignature(freeRtn, AFUNPTR( FreeWrapper ),
          IARG_PROTOTYPE, proto,
          IARG_CONTEXT,
          IARG_ORIG_FUNCPTR,
          IARG_END);
    }

    RTN mehRtn = RTN_FindByName(img, "meh");
    if (RTN_Valid(mehRtn))
    {
      PROTO proto = PROTO_Allocate( PIN_PARG(void *), CALLINGSTD_DEFAULT, "meh", PIN_PARG_END() );

      RTN_ReplaceSignature(mehRtn, AFUNPTR( MehWrapper ),
          IARG_PROTOTYPE, proto,
          IARG_CONTEXT,
          IARG_ORIG_FUNCPTR,
          IARG_END);
    }

    RTN mallocRtn = RTN_FindByName(img, "malloc");
    if (RTN_Valid(mallocRtn))
    {
      //if (!RTN_IsSafeForProbedReplacementEx(mallcRtn, PROBE_MODE_ALLOW_RELOCATION)) {
      //  TraceFile << "X NoProbedReplace malloc" << endl;
      //}
      PROTO proto = PROTO_Allocate( PIN_PARG(void *), CALLINGSTD_DEFAULT, "malloc", PIN_PARG_END() );

      RTN_ReplaceSignature(mallocRtn, AFUNPTR( MallocWrapper ),
          IARG_PROTOTYPE, proto,
          IARG_CONTEXT,
          IARG_ORIG_FUNCPTR,
          IARG_FUNCARG_ENTRYPOINT_VALUE, 0,
          IARG_END);
    }

    RTN reallocRtn = RTN_FindByName(img, "realloc");
    if (RTN_Valid(reallocRtn))
    {
      PROTO proto = PROTO_Allocate( PIN_PARG(void *), CALLINGSTD_DEFAULT, "realloc", PIN_PARG_END() );

      RTN_ReplaceSignature(reallocRtn, AFUNPTR( ReallocWrapper ),
          IARG_PROTOTYPE, proto,
          IARG_CONTEXT,
          IARG_ORIG_FUNCPTR,
          IARG_FUNCARG_ENTRYPOINT_VALUE, 1,
          IARG_END);
    }

    // I tried the following routine to instrument calls to calloc but couldn't make it work;
    // the third function parameter was always garbage. Also tried instrumenting calls
    // to calloc, but couldn't make that work either... Maybe explicit interpositioning
    // would work better??
    RTN callocRtn = RTN_FindByName(img, "calloc");
    if (RTN_Valid(callocRtn))
    {
      PROTO proto = PROTO_Allocate( PIN_PARG(void *), CALLINGSTD_DEFAULT, "calloc", PIN_PARG_END() );

      RTN_ReplaceSignature(callocRtn, AFUNPTR( CallocWrapper ),
          IARG_PROTOTYPE, proto,
          IARG_CONTEXT,
          IARG_ORIG_FUNCPTR,
          IARG_FUNCARG_ENTRYPOINT_VALUE, 0,
          IARG_FUNCARG_ENTRYPOINT_VALUE, 1,
          IARG_END);
    }

    RTN mainRtn = RTN_FindByName(img, "main");
    if (RTN_Valid(mainRtn))
    {
        RTN_Open(mainRtn);
        RTN_InsertCall(mainRtn, IPOINT_BEFORE, (AFUNPTR) BeforeMain, IARG_TSC, IARG_END);
        RTN_InsertCall(mainRtn, IPOINT_AFTER,  (AFUNPTR) AfterMain,  IARG_TSC, IARG_END);
        RTN_Close(mainRtn);
    }

    { RTN rtn = RTN_FindByName(img, "exit");
      if (RTN_Valid(rtn))
      {
          RTN_Open(rtn);
          RTN_InsertCall(rtn, IPOINT_BEFORE,  (AFUNPTR) AfterMain,  IARG_TSC, IARG_END);
          RTN_Close(rtn);
      }
    }

    { RTN rtn = RTN_FindByName(img, "caml_sys_exit");
      if (RTN_Valid(rtn))
      {
          RTN_Open(rtn);
          RTN_InsertCall(rtn, IPOINT_BEFORE,  (AFUNPTR) AfterMain,  IARG_TSC, IARG_END);
          RTN_Close(rtn);
      }
    }

    RTN fmainRtn = RTN_FindByName(img, "foster__main");
    if (RTN_Valid(fmainRtn))
    {
        RTN_Open(fmainRtn);
        RTN_InsertCall(fmainRtn, IPOINT_BEFORE, (AFUNPTR) BeforeMain, IARG_TSC, IARG_END);
        RTN_InsertCall(fmainRtn, IPOINT_AFTER,  (AFUNPTR) AfterMain,  IARG_TSC, IARG_END);
        RTN_Close(fmainRtn);
    }
}

VOID PIN_FAST_ANALYSIS_CALL do_incr_by(UINT64* counter, UINT64 amount)
{
    (*counter) += amount;
}

int HandleStackPointerMunge(INS ins) {
  if (INS_IsSub(ins)) {
    if (INS_OperandIsImmediate(ins, 1)) {
      if (INS_OperandImmediate(ins, 1) > 516) {
        TraceFile << endl << "X " << RTN_Name(INS_Rtn(ins)) << " " << dec << INS_OperandImmediate(ins, 1) << endl;
      } else if (INS_OperandImmediate(ins, 1) > 32000) {
        // Ignore very large stack munging
      } else {
        INS_InsertFillBuffer(ins, IPOINT_BEFORE, bufid,
            IARG_TSC, offsetof(struct alloc_record, tsc),
            IARG_ADDRINT, INS_OperandImmediate(ins, 1),
            offsetof(struct alloc_record, size),
            IARG_UINT32, 4, offsetof(struct alloc_record, typ),
            IARG_END);
      }
    } else {
      INS_InsertFillBuffer(ins, IPOINT_BEFORE, bufid,
          IARG_TSC, offsetof(struct alloc_record, tsc),
          IARG_ADDRINT, INS_OperandReg(ins, 1),
          offsetof(struct alloc_record, size),
          IARG_UINT32, 7, offsetof(struct alloc_record, typ),
          IARG_END);
    }
  } else if (INS_Opcode(ins) == XED_ICLASS_ADD) {
    if (INS_OperandIsImmediate(ins, 1)) {
      if (INS_OperandImmediate(ins, 1) < 0) {
        INS_InsertFillBuffer(ins, IPOINT_BEFORE, bufid,
            IARG_TSC, offsetof(struct alloc_record, tsc),
            IARG_ADDRINT, -INS_OperandImmediate(ins, 1),
            offsetof(struct alloc_record, size),
            IARG_UINT32, 8, offsetof(struct alloc_record, typ),
            IARG_END);
      }
    }
  } else if (INS_Opcode(ins) == XED_ICLASS_AND
        ||   INS_Opcode(ins) == XED_ICLASS_LEA
        ||   INS_Opcode(ins) == XED_ICLASS_MOV) {
    /// do nothing
  } else if (INS_Opcode(ins) == XED_ICLASS_PUSH) {
    if (INS_OperandIsReg(ins, 0) && INS_OperandReg(ins, 0) == REG_GBP) {
      // skip 'push ebp'
    } else {
      return 1;
    }
  } else {
    //xed_decoded_inst_t* xdi = INS_XedDec(ins);
    //TraceFile << "non-sub/push insn writing stack ptr, opcode is " << INS_Opcode(ins)
    //		  << " with mnemonic " << INS_Mnemonic(ins) << "; nops = " << nops << endl;
  }
  return 0;
}

// Pin calls this function every time a new rtn is executed
VOID Trace(TRACE tr, VOID *v)
{
  int numStackPushes = 0;
  UINT64 numCalls = 0;
  for (BBL bbl = TRACE_BblHead(tr); BBL_Valid(bbl); bbl = BBL_Next(bbl)) {
    for (INS ins = BBL_InsHead(bbl); INS_Valid(ins); ins = INS_Next(ins)) {
      if (gDoTrackStackPointer && INS_IsCall(ins)) {
        numCalls++;
      }

      if (INS_RegW(ins, 0) == REG_STACK_PTR) {
        if (gDoTrackStackPointer) {
          numStackPushes += HandleStackPointerMunge(ins);
        }
      } else if (INS_RegW(ins, 0) == REG_R15 && gDoTrackOCaml) {
        // OCaml open-coded allocation(?)
        if (INS_Opcode(ins) == XED_ICLASS_SUB) {
          if (INS_OperandIsImmediate(ins, 1)) {
            INS_InsertFillBuffer(ins, IPOINT_BEFORE, bufid,
                IARG_TSC, offsetof(struct alloc_record, tsc),
                IARG_ADDRINT,  INS_OperandImmediate(ins, 1),
                offsetof(struct alloc_record, size),
                IARG_UINT32, 9, offsetof(struct alloc_record, typ),
                IARG_END);
          }
        }
      }
    }
  }

  if (numStackPushes > 0) {
    INS ins = BBL_InsHead(TRACE_BblHead(tr));
    INS_InsertFillBuffer(ins, IPOINT_BEFORE, bufid,
        IARG_TSC, offsetof(struct alloc_record, tsc),
        IARG_ADDRINT, 8 * numStackPushes,
        offsetof(struct alloc_record, size),
        IARG_UINT32, 6, offsetof(struct alloc_record, typ),
        IARG_END);
  }

  if (numCalls > 0) {
    INS ins = BBL_InsHead(TRACE_BblHead(tr));
    INS_InsertCall(ins, IPOINT_BEFORE, AFUNPTR(do_incr_by), IARG_FAST_ANALYSIS_CALL,
                        IARG_PTR, &gNumCalls,
                        IARG_UINT64, numCalls,
                        IARG_END);
  }
}

UINT64 measureTSC_backtoback() {
  UINT64 tsc_begin = xed_get_time();
  UINT64 mn = xed_get_time() - tsc_begin;
  for (int i = 0; i < 100; ++i) {
    UINT64 tsc_begin = xed_get_time();
    UINT64 val = xed_get_time() - tsc_begin;
    mn = (val < mn) ? val : mn;
  }
  return mn;
}

/* ===================================================================== */

VOID Fini(INT32 code, VOID *v)
{
    PIN_GetLock(&lock, 1);
    TraceFile << endl << "C " << dec << gNumCalls << endl;
    TraceFile.close();
    PIN_ReleaseLock(&lock);
}

/* ===================================================================== */
/* Print Help Message                                                    */
/* ===================================================================== */

INT32 Usage()
{
    cerr << "This tool produces a trace of calls to malloc, "
         << "and also stack allocation." << endl;
    cerr << endl << KNOB_BASE::StringKnobSummary() << endl;
    return -1;
}

/* ===================================================================== */
/* Main                                                                  */
/* ===================================================================== */

int main(int argc, char *argv[])
{
    // Initialize pin & symbol manager
    PIN_InitSymbols();
    if( PIN_Init(argc,argv) )
    {
        return Usage();
    }
    
    // Write to a file since cout and cerr maybe closed by the application
    TraceFile.open(KnobOutputFile.Value().c_str());
    TraceFile << hex;
    TraceFile.setf(ios::showbase);

    gDoTrackStackPointer = true;
    gDoTrackOCaml = true;

    PIN_InitLock(&lock);

    const int numBufPages = 64;
    bufid = PIN_DefineTraceBuffer(sizeof(struct alloc_record), numBufPages,
                                  BufferFull, 0);
    if(bufid == BUFFER_ID_INVALID){
        cerr << "Error allocating initial buffer" << endl;
        return 1;
    }

    gNumCalls = 0;
    tsc0 = xed_get_time();

    TraceFile << "T " << hex << tsc0 << " " << dec << TSC_TRIM_BITS << endl;
    TraceFile << "X " << "TSC-backtoback " << measureTSC_backtoback() << endl;
    TraceFile << "X " << "TSC-preinstrument " << tsc_trim(xed_get_time()) << endl;

    // Register Image to be called to instrument functions.
    IMG_AddInstrumentFunction(Image, 0);

    if (gDoTrackStackPointer || gDoTrackOCaml) {
      TRACE_AddInstrumentFunction(Trace, 0);
    }

    PIN_AddFiniFunction(Fini, 0);

    TraceFile << "X " << "TSC-startprog " << tsc_trim(xed_get_time()) << endl;

    // Never returns
    PIN_StartProgram();
    
    return 0;
}

/* ===================================================================== */
/* eof */
/* ===================================================================== */
