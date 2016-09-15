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
/* footprint.H
   
Measures the number of references to unique chunks of memory.
Breaks down workings sets in terms of 16-byte granules,
64-byte cache lines, and 4096-byte pages.
Provides separate statistics for loads and stores.

With a small tweak, I can count references to the chunks if one wants to
know where all the action is, from a chunk referencing perspective.
 */
#include "pin.H"
#include <map>
#include <iostream>
#include <sstream>
#include <iomanip>
#include <fstream>
#include <string>

const unsigned int  FOOTPRINT_LOAD=1;
const unsigned int  FOOTPRINT_STORE=2;
const unsigned int  FOOTPRINT_CODE=4;

std::string fmtH(unsigned val) {
  std::string s;
  std::stringstream ss(s);
  const char* suffixes[] = { ".", "K", "M", "G", "T" };
  unsigned suffix = 0;
  while (suffix < 4) {
    if (val < 10000) { ss << val << suffixes[suffix]; break; }
    suffix += 1;
    val /= 1000;
  }
  if (suffix == 4) { ss << val << suffixes[suffix]; }
  return ss.str();
}

class footprint_thread_data_t {
    map<ADDRINT,unsigned int> memG_L;
    map<ADDRINT,unsigned int> memG_S;
    map<ADDRINT,unsigned int> memL_L;
    map<ADDRINT,unsigned int> memL_S;
    map<ADDRINT,unsigned int> memP_L;
    map<ADDRINT,unsigned int> memP_S;
    UINT64 block_total[8]; // 8 combinations of load, store, code
  public:
    
    footprint_thread_data_t() {
    }
    
    void loadG(ADDRINT ea) { memG_L[ea]++; }
    void storeG(ADDRINT ea) { memG_S[ea]++; }
    void loadL(ADDRINT ea) { memL_L[ea]++; }
    void storeL(ADDRINT ea) { memL_S[ea]++; }
    void loadP(ADDRINT ea) { memP_L[ea]++; }
    void storeP(ADDRINT ea) { memP_S[ea]++; }

    void summary(std::ofstream* out) {
        unsigned total_L = 0;
        unsigned total_S = 0;

        unsigned loads_G  = 0;
        unsigned stores_G = 0;

        unsigned loads_L  = 0;
        unsigned stores_L = 0;

        unsigned loads_P  = 0;
        unsigned stores_P = 0;

        map<ADDRINT,unsigned int>::iterator it =  memG_L.begin();
        for( ; it != memG_L.end() ; it++ ) {
            loads_G++;
            total_L += it->second;
        }

        it = memG_S.begin();
        for( ; it != memG_S.end() ; it++ ) {
            stores_G++;
            total_S += it->second;
        }

        it = memL_L.begin();
        for( ; it != memL_L.end() ; it++ ) { loads_L++; }

        it =  memL_S.begin();
        for( ; it != memL_S.end() ; it++ ) { stores_L++; }

        unsigned loads_P_le10eX[10] = { 0 };
        it =  memP_L.begin();
        for( ; it != memP_L.end() ; it++ ) { loads_P++;

          unsigned idx = 0;
          unsigned val = it->second;
          while(1) {
            if (val <= 10 || idx == 8) {
              loads_P_le10eX[idx + 1]++;
              break;
            }
            idx++;
            val = val / 10;
          }
        }

        it =  memP_S.begin();
        for( ; it != memP_S.end() ; it++ ) { stores_P++; }

        *out << std::setw(30) <<    "granules (16-byte) loaded:" << "  "  << std::setw(12) << fmtH(loads_G) << endl;
        *out << std::setw(30) <<    "granules (16-byte) stored:" << "  "  << std::setw(12) << fmtH(stores_G) << endl;
        *out << std::setw(30) <<  "cachelines (64-byte) loaded:" << "  "  << std::setw(12) << fmtH(loads_L) << endl;
        *out << std::setw(30) <<  "cachelines (64-byte) stored:" << "  "  << std::setw(12) << fmtH(stores_L) << endl;
        *out << std::setw(30) << "small pgs (4096-byte) loaded:" << "  "  << std::setw(12) << fmtH(loads_P) << endl;
        *out << std::setw(30) << "small pgs (4096-byte) stored:" << "  "  << std::setw(12) << fmtH(stores_P) << endl;
        *out << std::setw(30) <<                  "total loads:" << "  "  << std::setw(12) << fmtH(total_L) << endl;
        *out << std::setw(30) <<                 "total stores:" << "  "  << std::setw(12) << fmtH(total_S) << endl;
        *out << std::setw(30) <<   "small pgs with <= 10 loads:" << "  "  << std::setw(12) << fmtH(loads_P_le10eX[1]) << endl;
        *out << std::setw(30) <<   "small pgs w/   ..100 loads:" << "  "  << std::setw(12) << fmtH(loads_P_le10eX[2]) << endl;
        *out << std::setw(30) <<   "small pgs w/ .. 10e3 loads:" << "  "  << std::setw(12) << fmtH(loads_P_le10eX[3]) << endl;
        *out << std::setw(30) <<   "small pgs w/ .. 10e4 loads:" << "  "  << std::setw(12) << fmtH(loads_P_le10eX[4]) << endl;
        *out << std::setw(30) <<   "small pgs w/ .. 10e5 loads:" << "  "  << std::setw(12) << fmtH(loads_P_le10eX[5]) << endl;
        *out << std::setw(30) <<   "small pgs w/ .. 10e6 loads:" << "  "  << std::setw(12) << fmtH(loads_P_le10eX[6]) << endl;
        *out << std::setw(30) <<   "small pgs w/ .. 10e7 loads:" << "  "  << std::setw(12) << fmtH(loads_P_le10eX[7]) << endl;
        *out << std::setw(30) <<   "small pgs w/ .. 10e8 loads:" << "  "  << std::setw(12) << fmtH(loads_P_le10eX[8]) << endl;
        *out << std::setw(30) <<   "small pgs w/ >= 10e8 loads:" << "  "  << std::setw(12) << fmtH(loads_P_le10eX[9]) << endl;
    }
};

class footprint_t 
{
    KNOB<string> knob_output_file;
    std::ofstream* out;
    TLS_KEY tls_key;
    unsigned int num_threads;

    footprint_thread_data_t* get_tls(THREADID tid)    {
        footprint_thread_data_t* tdata =
            static_cast<footprint_thread_data_t*>(PIN_GetThreadData(tls_key, tid));
        return tdata;
    }

    void summary() {
        for(unsigned int i=0;i<num_threads;i++) {
            footprint_thread_data_t* tdata = get_tls(i);
            *out << "# FINI TID " << i << endl;
            tdata->summary(out);
        }
    }

  public:


    footprint_t()
        :  knob_output_file(KNOB_MODE_WRITEONCE, "pintool",
                            "o", "memfootprint.out", "specify output file name")  {
        num_threads = 0;
        string file_name = knob_output_file.Value();
        out = new std::ofstream(file_name.c_str());
    }
    
    void activate() {
        tls_key = PIN_CreateThreadDataKey(0);
        TRACE_AddInstrumentFunction(reinterpret_cast<TRACE_INSTRUMENT_CALLBACK>(instrument_trace), this);
        PIN_AddThreadStartFunction(reinterpret_cast<THREAD_START_CALLBACK>(thread_start), this);
        PIN_AddFiniFunction(reinterpret_cast<FINI_CALLBACK>(fini), this);
    }

    static ADDRINT maskG(ADDRINT ea)  {
        const ADDRINT mask = ~static_cast<ADDRINT>(16 - 1);
        return ea & mask;
    }
    static ADDRINT maskL(ADDRINT ea)  {
        const ADDRINT mask = ~static_cast<ADDRINT>(64 - 1);
        return ea & mask;
    }
    static ADDRINT maskP(ADDRINT ea)  {
        const ADDRINT mask = ~static_cast<ADDRINT>(4096 -1);
        return ea & mask;
    }

    static void load(footprint_t* xthis, THREADID tid, ADDRINT memea, UINT32 length) {
        footprint_thread_data_t* tdata = xthis->get_tls(tid);
        ADDRINT startG = maskG(memea);
        ADDRINT endG   = maskG(memea+length-1);
        for(ADDRINT addr = startG ; addr <= endG ; addr += 16) {
            tdata->loadG(addr);
        }

        ADDRINT startL = maskL(memea);
        ADDRINT endL   = maskL(memea+length-1);
        for(ADDRINT addr = startL ; addr <= endL ; addr += 64) {
            tdata->loadL(addr);
        }

        ADDRINT startP = maskP(memea);
        ADDRINT endP   = maskP(memea+length-1);
        for(ADDRINT addr = startP ; addr <= endP ; addr += 4096) {
            tdata->loadP(addr);
        }
    }
    static void store(footprint_t* xthis, THREADID tid, ADDRINT memea, UINT32 length) {
        footprint_thread_data_t* tdata = xthis->get_tls(tid);
        ADDRINT startG = maskG(memea);
        ADDRINT endG   = maskG(memea+length-1);
        for(ADDRINT addr = startG ; addr <= endG ; addr += 16) {
            tdata->storeG(addr);
        }

        ADDRINT startL = maskL(memea);
        ADDRINT endL   = maskL(memea+length-1);
        for(ADDRINT addr = startL ; addr <= endL ; addr += 64) {
            tdata->storeL(addr);
        }

        ADDRINT startP = maskP(memea);
        ADDRINT endP   = maskP(memea+length-1);
        for(ADDRINT addr = startP ; addr <= endP ; addr += 4096) {
            tdata->storeP(addr);
        }
    }
    /*
    static void code(footprint_t* xthis, THREADID tid, ADDRINT memea, UINT32 length) {
        ADDRINT start = mask(memea);
        ADDRINT end   = mask(memea+length-1);
        footprint_thread_data_t* tdata = xthis->get_tls(tid);
        for(ADDRINT addr = start ; addr <= end ; addr += chunk_size) {
            tdata->code(addr);
        }
    }
    */

    static void thread_start(THREADID tid, CONTEXT* ctxt, INT32 flags, footprint_t* xthis) {
        footprint_thread_data_t* tdata = new footprint_thread_data_t;
        PIN_SetThreadData(xthis->tls_key, tdata, tid);
        xthis->num_threads++;
    }

    void instrument_instruction(INS ins, ADDRINT pc, unsigned int ins_bytes) {
        // instrument the code reference
        /*
        INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR) code,
                       IARG_PTR, this,
                       IARG_THREAD_ID,
                       IARG_INST_PTR,
                       IARG_UINT32, ins_bytes,
                       IARG_END);
                       */

        // instrument the load(s)
        if (INS_IsMemoryRead(ins) && INS_IsStandardMemop(ins)) {
            INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR) load,
                           IARG_PTR, this,
                           IARG_THREAD_ID,
                           IARG_MEMORYREAD_EA,
                           IARG_MEMORYREAD_SIZE,
                           IARG_END);

        }
        if (INS_HasMemoryRead2(ins) && INS_IsStandardMemop(ins)) {
            INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR) load,
                           IARG_PTR, this,
                           IARG_THREAD_ID,
                           IARG_MEMORYREAD2_EA,
                           IARG_MEMORYREAD_SIZE,
                           IARG_END);

        }
        // instrument the store
        if (INS_IsMemoryWrite(ins) && INS_IsStandardMemop(ins)) {
            INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR) store,
                           IARG_PTR, this,
                           IARG_THREAD_ID,
                           IARG_MEMORYWRITE_EA,
                           IARG_MEMORYWRITE_SIZE,
                           IARG_END);

        }

    }

    static void instrument_trace(TRACE trace, footprint_t* xthis) {
        ADDRINT pc = TRACE_Address(trace);
        for (BBL bbl = TRACE_BblHead(trace); BBL_Valid(bbl); bbl = BBL_Next(bbl))    {
            const INS head = BBL_InsHead(bbl);
            if (! INS_Valid(head)) continue;
            for (INS ins = head; INS_Valid(ins); ins = INS_Next(ins)) {
                if (!INS_IsStandardMemop(ins))
                    continue;
                unsigned int instruction_size = INS_Size(ins);
                xthis->instrument_instruction(ins, pc, instruction_size);
                pc = pc + instruction_size;
            }
        }
    }

    static void fini(int, footprint_t* xthis) {
        xthis->summary();
        *(xthis->out) << endl;
        xthis->out->close();
    }

    
}; 
