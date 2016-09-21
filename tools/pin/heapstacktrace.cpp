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

// Expect slowdown of 240x (1s -> 4m)
// and logfiles of roughly 200 MB / minute

namespace LEVEL_PINCLIENT { extern VOID RTN_InsertFillBuffer(RTN rtn, IPOINT action, BUFFER_ID id, ...); }

/* ===================================================================== */
/* Names of malloc and free */
/* ===================================================================== */
#if defined(TARGET_MAC)
#define MALLOC "_malloc"
#else
#define MALLOC "malloc"
#endif

/* ===================================================================== */
/* Global Variables */
/* ===================================================================== */

std::ofstream TraceFile;

UINT64 tsc0;
UINT64 gNumCalls;

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
//    With histogram encoding:
// Shifting off 16 bits would be 25 bits per second, about 64 microsecond resolution.
//  Estimate: 25 bps, 9 MB * 1.3
//    Est w/ histogram encoding:
// Shifting off 20 bits would be 21 bits per second, about 500 microsecond resolution.
UINT64 tsc_trim(UINT64 t) { return t >> 12; }

// TODO histogram encoding:
// Bucket StartTimeStamp EndTimeStamp
//    [Event Size Count]

/* ===================================================================== */
/* Commandline Switches */
/* ===================================================================== */

KNOB<string> KnobOutputFile(KNOB_MODE_WRITEONCE, "pintool",
    "o", "heapstacktrace.out", "specify trace file name");

/* ===================================================================== */

VOID AllocPinHook_1(UINT64 tsc, ADDRINT size) {
    PIN_GetLock(&lock, 1);
    TraceFile << dec << 1 << " " << hex << tsc_trim(tsc - tsc0) << " " << dec << size << endl;
    PIN_ReleaseLock(&lock);
}

VOID AllocPinHook_2(UINT64 tsc, ADDRINT size) {
    PIN_GetLock(&lock, 1);
    TraceFile << dec << 2 << " " << hex << tsc_trim(tsc - tsc0) << " " << dec << size << endl;
    PIN_ReleaseLock(&lock);
}

VOID AllocPinHook_3(UINT64 tsc, ADDRINT size) {
    PIN_GetLock(&lock, 1);
    TraceFile << dec << 3 << " " << hex << tsc_trim(tsc - tsc0) << " " << dec << size << endl;
    PIN_ReleaseLock(&lock);
}


VOID BeforeMain(UINT64 tsc) {
    PIN_GetLock(&lock, 1);
    TraceFile << dec << 5 << " " << hex << tsc_trim(tsc - tsc0) << " " << 0 << endl;
    PIN_ReleaseLock(&lock);
}

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
    for(UINT64 i = 0; i < numElements; i++) {
      UINT64 tsc_d = (rc[i].tsc - tsc0);
      UINT64 tsc_d_trimmed = tsc_trim(tsc_d);
      if (tsc_d_trimmed != prev_tsc_d_trimmed) {
        prev_tsc_d_trimmed = tsc_d_trimmed;
        TraceFile << endl << "B " << hex << tsc_d_trimmed;
      }

      TraceFile << " " << dec << rc[i].typ << " " << rc[i].size;
    }


    UINT64 tsc_end = xed_get_time();
    TraceFile << endl << "BufferFull " << hex << tsc_trim(tsc_end - tsc_begin) << endl;

    PIN_ReleaseLock(&lock);
    return buf;
}

/* ===================================================================== */
/* Instrumentation routines                                              */
/* ===================================================================== */

VOID Image(IMG img, VOID *v)
{
    RTN mcellRtn = RTN_FindByName(img, "foster_pin_hook_memalloc_cell");
    if (RTN_Valid(mcellRtn))
    {
        RTN_Open(mcellRtn);
        RTN_InsertCall(mcellRtn, IPOINT_BEFORE, (AFUNPTR) AllocPinHook_2,
                       IARG_TSC,
                       IARG_FUNCARG_ENTRYPOINT_VALUE, 0,
                       IARG_END);
        RTN_Close(mcellRtn);
    }

    RTN marrRtn = RTN_FindByName(img, "foster_pin_hook_memalloc_array");
    if (RTN_Valid(marrRtn))
    {
        RTN_Open(marrRtn);
        RTN_InsertCall(marrRtn, IPOINT_BEFORE, (AFUNPTR) AllocPinHook_3,
                       IARG_TSC,
                       IARG_FUNCARG_ENTRYPOINT_VALUE, 0,
                       IARG_END);
        RTN_Close(marrRtn);
    }

    RTN mallocRtn = RTN_FindByName(img, MALLOC);
    if (RTN_Valid(mallocRtn))
    {
        RTN_Open(mallocRtn);
        RTN_InsertCall(mallocRtn, IPOINT_BEFORE, (AFUNPTR) AllocPinHook_1,
                       IARG_TSC,
                       IARG_FUNCARG_ENTRYPOINT_VALUE, 0,
                       IARG_END);
        RTN_Close(mallocRtn);
    }

    RTN mainRtn = RTN_FindByName(img, "main");
    if (RTN_Valid(mainRtn))
    {
        RTN_Open(mainRtn);
        RTN_InsertCall(mainRtn, IPOINT_BEFORE, (AFUNPTR) BeforeMain, IARG_TSC, IARG_END);
        RTN_Close(mainRtn);
    }

    RTN fmainRtn = RTN_FindByName(img, "foster__main");
    if (RTN_Valid(fmainRtn))
    {
        RTN_Open(fmainRtn);
        RTN_InsertCall(fmainRtn, IPOINT_BEFORE, (AFUNPTR) BeforeMain, IARG_TSC, IARG_END);
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
      if (INS_IsCall(ins)) numCalls++;

      if (INS_RegW(ins, 0) == REG_STACK_PTR) {
        numStackPushes += HandleStackPointerMunge(ins);
      } else if (INS_RegW(ins, 0) == REG_R15) {
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

    TraceFile << "T " << hex << tsc0 << endl;

    // Register Image to be called to instrument functions.
    IMG_AddInstrumentFunction(Image, 0);
    TRACE_AddInstrumentFunction(Trace, 0);

    PIN_AddFiniFunction(Fini, 0);

    // Never returns
    PIN_StartProgram();
    
    return 0;
}

/* ===================================================================== */
/* eof */
/* ===================================================================== */
