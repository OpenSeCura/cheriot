/*
 * Copyright 2026 Google LLC
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

`include "GuruLibrary.sv"
`include "SimRtl.sv"

module Tb();
  logic clk_core;
  logic rst_n_core;

  // =========================================================================
  // External RAM Parameters & Storage (256 KB, 64-bit lines, 1 tag bit/line)
  // =========================================================================
  localparam int RamSizeBytes = 256 * 1024;
  localparam int LineBits     = 64;
  localparam int LineBytes    = LineBits / 8;
  localparam int NumLines     = (RamSizeBytes * 8) / LineBits;
  localparam int LineIdxBits  = $clog2(NumLines);

  logic [LineBits - 1 : 0] ramData [0 : NumLines - 1];
  logic                    ramTag  [0 : NumLines - 1];

  // =========================================================================
  // External RAM & UART Emulation State
  // =========================================================================
  logic [31 : 0] ramFetchReadAddr;
  logic          ramFetchReadRpValid;
  logic [31 : 0] ramDataReadAddr;
  logic          ramDataReadRpValid;

  logic [31 : 0] uartReadAddr;
  logic          uartReadRpValid;
  logic          dlab;
  logic [7 : 0]  ie;
  logic          rxBufValid;
  logic [7 : 0]  rxBuf;

  logic [31 : 0]   tohostAddr;
  longint unsigned cycleCount;
  longint unsigned maxCycles;

  // =========================================================================
  // Virtual Method Overrides for Spec (specSysTreeInst)
  // =========================================================================
  class tb_io_t extends sim_io_t;
    virtual function void sys_core_mem_ram_fetch_lineReadRq_Send_31(input logic [31 : 0] val);
      ramFetchReadAddr    = val;
      ramFetchReadRpValid = 1'b1;
    endfunction

    virtual function struct packed {
      logic [7 : 0][7 : 0] data;
      logic [0 : 0] tag;
    } sys_core_mem_ram_fetch_lineReadRp_Recv_32();
      struct packed {
        logic [7 : 0][7 : 0] data;
        logic [0 : 0] tag;
      } rp;
      logic [LineIdxBits - 1 : 0] fetchIdx;
      fetchIdx            = ramFetchReadAddr[LineIdxBits + 2 : 3];
      rp.data             = ramData[fetchIdx];
      rp.tag[0]           = ramTag[fetchIdx];
      ramFetchReadRpValid = 1'b0;
      return rp;
    endfunction

    virtual function void sys_core_mem_ram_lineReadRq_Send_33(input logic [31 : 0] val);
      ramDataReadAddr    = val;
      ramDataReadRpValid = 1'b1;
    endfunction

    virtual function struct packed {
      logic [7 : 0][7 : 0] data;
      logic [0 : 0] tag;
    } sys_core_mem_ram_lineReadRp_Recv_34();
      struct packed {
        logic [7 : 0][7 : 0] data;
        logic [0 : 0] tag;
      } rp;
      logic [LineIdxBits - 1 : 0] dataIdx;
      dataIdx            = ramDataReadAddr[LineIdxBits + 2 : 3];
      rp.data            = ramData[dataIdx];
      rp.tag[0]          = ramTag[dataIdx];
      ramDataReadRpValid = 1'b0;
      return rp;
    endfunction

    virtual function void sys_core_mem_ram_lineWriteRq_Send_35(input struct packed {
      logic [31 : 0] addr;
      logic [7 : 0][7 : 0] data;
      logic [7 : 0] dataMask;
      logic [0 : 0] tag;
      logic [0 : 0] tagMask;
    } val);
      logic [31 : 0]              wrAddr;
      logic [LineIdxBits - 1 : 0] wrIdx;
      logic [31 : 0]              tohostLineAddr;
      logic [2 : 0]               tohostByteOff;
      logic [31 : 0]              tohostVal;

      wrAddr = val.addr;
      wrIdx  = wrAddr[LineIdxBits + 2 : 3];

      for (int b = 0; b < LineBytes; b++) begin
        if (val.dataMask[b]) begin
          ramData[wrIdx][b*8 +: 8] = val.data[b];
        end
      end
      if (val.tagMask[0]) begin
        ramTag[wrIdx] = val.tag[0];
      end

      tohostLineAddr = {tohostAddr[31 : 3], 3'b000};
      tohostByteOff  = tohostAddr[2 : 0];
      if ((tohostAddr != 32'h0) &&
          (wrAddr == tohostLineAddr) &&
          val.dataMask[tohostByteOff]) begin
        for (int b = 0; b < 4; b++) begin
          tohostVal[b*8 +: 8] = ramData[wrIdx][(int'(tohostByteOff) + b)*8 +: 8];
        end
        if (tohostVal != 32'h0) begin
          if (tohostVal == 32'h1) begin
            $display("TEST PASSED!");
            $finish;
          end else begin
            $display("TEST FAILED at test case: %0d", tohostVal);
            $finish;
          end
        end
      end
    endfunction

    virtual function logic sys_core_mem_mem_mem_mem_mem_plic_UartIrq_Recv_68();
      return ie[0] ? (rxBufValid | ie[1]) : ie[1];
    endfunction

    virtual function void sys_core_mem_mem_mem_mem_mem_mem_extMem_lineReadRq_Send_69(input logic [31 : 0] val);
      uartReadAddr    = val;
      uartReadRpValid = 1'b1;
    endfunction

    virtual function struct packed {
      logic [15 : 0][7 : 0] data;
      logic [1 : 0] tag;
    } sys_core_mem_mem_mem_mem_mem_mem_extMem_lineReadRp_Recv_70();
      struct packed {
        logic [15 : 0][7 : 0] data;
        logic [1 : 0] tag;
      } rp;
      rp = '0;
      if (uartReadAddr == 32'h1000_0000) begin
        rp.data[0] = rxBufValid ? rxBuf : 8'h00;
        if (rxBufValid) begin
          rxBufValid = 1'b0;
        end
      end else if (uartReadAddr == 32'h1000_0010) begin
        rp.data[4] = rxBufValid ? 8'h21 : 8'h20;
      end
      uartReadRpValid = 1'b0;
      return rp;
    endfunction

    virtual function void sys_core_mem_mem_mem_mem_mem_mem_extMem_lineWriteRq_Send_71(input struct packed {
      logic [31 : 0] addr;
      logic [15 : 0][7 : 0] data;
      logic [15 : 0] dataMask;
      logic [1 : 0] tag;
      logic [1 : 0] tagMask;
    } val);
      if (val.addr == 32'h1000_0000) begin
        if (val.dataMask[12]) begin
          dlab = val.data[12][7];
        end
        if (val.dataMask[0] && !dlab) begin
          $write("%c", val.data[0]);
          $fflush(32'h8000_0001);
        end
        if (val.dataMask[4] && !dlab) begin
          ie = val.data[4];
        end
      end
    endfunction
  endclass

  // =========================================================================
  // Instantiate Guru Generated Top Module
  // =========================================================================
  top top_inst (
    .clk_default(clk_core),
    .rst_n_default(rst_n_core)
  );

  // =========================================================================
  // Sequential Reset & Cycle Updates
  // =========================================================================
  always_ff @(posedge clk_core or negedge rst_n_core) begin
    if (!rst_n_core) begin
      cycleCount <= 64'd0;
    end else begin
      if ((cycleCount % 64'd250000) == 64'd0) begin
        $display("[Cycle %0d]", cycleCount);
        $fflush(32'h8000_0001);
      end
      if (cycleCount + 64'd1 >= maxCycles) begin
        $finish;
      end
      cycleCount <= cycleCount + 64'd1;
    end
  end

  // =========================================================================
  // Memory Initialization, Plusargs & Clock/Reset Generation
  // =========================================================================
  initial begin
    string binFile;
    tb_io_t tb_io;

    tb_io  = new;
    sim_io = tb_io;

    ramFetchReadAddr    = 32'h0;
    ramFetchReadRpValid = 1'b0;
    ramDataReadAddr     = 32'h0;
    ramDataReadRpValid  = 1'b0;
    uartReadAddr        = 32'h0;
    uartReadRpValid     = 1'b0;
    dlab                = 1'b0;
    ie                  = 8'h0;
    rxBufValid          = 1'b0;
    rxBuf               = 8'h0;

    for (int i = 0; i < NumLines; i++) begin
      ramData[i] = '0;
      ramTag[i]  = 1'b0;
    end

    if ($value$plusargs("bin=%s", binFile)) begin
      $readmemh(binFile, ramData);
    end

    if (!$value$plusargs("tohost=%h", tohostAddr)) begin
      tohostAddr = 32'h0;
    end

    if (!$value$plusargs("cycles=%d", maxCycles)) begin
      maxCycles = 64'd50000000;
    end

    clk_core   = 1'b0;
    rst_n_core = 1'b0;
    #40;
    rst_n_core = 1'b1;
  end

  always begin
    #10;
    clk_core = 1'b1;
    #10;
    clk_core = 1'b0;
  end

endmodule
