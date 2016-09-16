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

struct alloc_record {
  UINT64 tsc;
  ADDRINT size;
  UINT32 typ;
};

BUFFER_ID bufid;
PIN_LOCK lock;

/* ===================================================================== */
/* Commandline Switches */
/* ===================================================================== */

KNOB<string> KnobOutputFile(KNOB_MODE_WRITEONCE, "pintool",
    "o", "heapstacktrace.out", "specify trace file name");

/* ===================================================================== */

VOID AllocPinHook_1(UINT64 tsc, ADDRINT size) {
    PIN_GetLock(&lock, 1);
    TraceFile << dec << 1 << " "  << size << " " << hex << (tsc - tsc0) << endl;
    PIN_ReleaseLock(&lock);
}

VOID AllocPinHook_2(UINT64 tsc, ADDRINT size) {
    PIN_GetLock(&lock, 1);
    TraceFile << dec << 2 << " "  << size << " " << hex << (tsc - tsc0) << endl;
    PIN_ReleaseLock(&lock);
}

VOID AllocPinHook_3(UINT64 tsc, ADDRINT size) {
    PIN_GetLock(&lock, 1);
    TraceFile << dec << 3 << " "  << size << " " << hex << (tsc - tsc0) << endl;
    PIN_ReleaseLock(&lock);
}


VOID BeforeMain(UINT64 tsc) {
    PIN_GetLock(&lock, 1);
    TraceFile << dec << 5 << " "  << 0 << " " << hex << (tsc - tsc0) << endl;
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
    PIN_GetLock(&lock, 1);

    struct alloc_record* rc =(struct alloc_record*)buf;
    for(UINT64 i=0; i<numElements; i++){
      TraceFile << dec << rc[i].typ << " " << rc[i].size << " " << hex << (rc[i].tsc - tsc0) << endl;
    }

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

VOID HandleStackPointerMunge(INS ins) {
  if (INS_IsSub(ins)) {
    if (INS_OperandIsImmediate(ins, 1)) {
      if (INS_OperandImmediate(ins, 1) == 8016) {
        TraceFile << "X " << RTN_Name(INS_Rtn(ins)) << endl;
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
    // skip 'push ebp'
    if (INS_OperandIsReg(ins, 0) && INS_OperandReg(ins, 0) == REG_EBP) {
      // do nothing
    } else {
      INS_InsertFillBuffer(ins, IPOINT_BEFORE, bufid,
          IARG_TSC, offsetof(struct alloc_record, tsc),
          IARG_ADDRINT, 8,
          offsetof(struct alloc_record, size),
          IARG_UINT32, 6, offsetof(struct alloc_record, typ),
          IARG_END);
    }
  } else {
    //xed_decoded_inst_t* xdi = INS_XedDec(ins);
    //TraceFile << "non-sub/push insn writing stack ptr, opcode is " << INS_Opcode(ins)
    //		  << " with mnemonic " << INS_Mnemonic(ins) << "; nops = " << nops << endl;
  }

}

// Pin calls this function every time a new rtn is executed
VOID Insn(INS ins, VOID *v)
{
  if (INS_RegW(ins, 0) == REG_STACK_PTR) {
    HandleStackPointerMunge(ins);
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

/* ===================================================================== */

VOID Fini(INT32 code, VOID *v)
{
    PIN_GetLock(&lock, 1);
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
    
    tsc0 = xed_get_time();

    TraceFile << "T " << hex << tsc0 << endl;

    // Register Image to be called to instrument functions.
    IMG_AddInstrumentFunction(Image, 0);
    INS_AddInstrumentFunction(Insn, 0);

    PIN_AddFiniFunction(Fini, 0);

    // Never returns
    PIN_StartProgram();
    
    return 0;
}

/* ===================================================================== */
/* eof */
/* ===================================================================== */
