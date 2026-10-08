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
`include "Rtl.sv"

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
  // 1. External RAM Ports (implConcreteRegions[0]: ramRegion)
  // =========================================================================
  logic [31 : 0] decl_sys_core_mem_mem_ram_ram_fetch_lineReadRq_Send_57;
  logic decl_sys_core_mem_mem_ram_ram_fetch_lineReadRq_SendEn_57;
  struct packed {
    logic [7 : 0][7 : 0] data;
    logic [0 : 0] tag;
  } sys_core_mem_mem_ram_ram_fetch_lineReadRp_Recv_58;

  logic [31 : 0] decl_sys_core_mem_mem_ram_ram_lineReadRq_Send_59;
  logic decl_sys_core_mem_mem_ram_ram_lineReadRq_SendEn_59;
  struct packed {
    logic [7 : 0][7 : 0] data;
    logic [0 : 0] tag;
  } sys_core_mem_mem_ram_ram_lineReadRp_Recv_60;

  struct packed {
    logic [31 : 0] addr;
    logic [7 : 0][7 : 0] data;
    logic [7 : 0] dataMask;
    logic [0 : 0] tag;
    logic [0 : 0] tagMask;
  } decl_sys_core_mem_mem_ram_ram_lineWriteRq_Send_61;
  logic decl_sys_core_mem_mem_ram_ram_lineWriteRq_SendEn_61;

  logic sys_core_mem_mem_ram_fetch_lineReadRqReady_Recv_62;
  logic sys_core_mem_mem_ram_fetch_lineReadRpValid_Recv_63;
  logic sys_core_mem_mem_ram_lineReadRqReady_Recv_69;
  logic sys_core_mem_mem_ram_lineWriteRqReady_Recv_70;
  logic sys_core_mem_mem_ram_lineReadRpValid_Recv_71;

  // =========================================================================
  // 2. Revocation Table Target Port Signals (implConcreteRegions[1]: revTableRegion)
  // =========================================================================
  logic decl_sys_core_mem_mem_mem_revTable_lineReadRqReady_Send_92;
  logic decl_sys_core_mem_mem_mem_revTable_lineReadRqReady_SendEn_92;
  logic decl_sys_core_mem_mem_mem_revTable_lineWriteRqReady_Send_93;
  logic decl_sys_core_mem_mem_mem_revTable_lineWriteRqReady_SendEn_93;
  logic sys_core_mem_mem_mem_revTable_lineReadRpReady_Recv_94;

  // =========================================================================
  // 3. PLIC UART Interrupt Signal (implConcreteRegions[4]: plicMemRegion)
  // =========================================================================
  logic sys_core_mem_mem_mem_mem_mem_mem_plic_plic_UartIrq_Recv_127;

  // =========================================================================
  // 4. External Memory / UART MMIO Signals (implConcreteRegions[5]: extMemRegion)
  // =========================================================================
  logic [31 : 0] decl_sys_core_mem_mem_mem_mem_mem_mem_mem_extMem_extMem_lineReadRq_Send_130;
  logic decl_sys_core_mem_mem_mem_mem_mem_mem_mem_extMem_extMem_lineReadRq_SendEn_130;
  struct packed {
    logic [15 : 0][7 : 0] data;
    logic [1 : 0] tag;
  } sys_core_mem_mem_mem_mem_mem_mem_mem_extMem_extMem_lineReadRp_Recv_131;
  struct packed {
    logic [31 : 0] addr;
    logic [15 : 0][7 : 0] data;
    logic [15 : 0] dataMask;
    logic [1 : 0] tag;
    logic [1 : 0] tagMask;
  } decl_sys_core_mem_mem_mem_mem_mem_mem_mem_extMem_extMem_lineWriteRq_Send_132;
  logic decl_sys_core_mem_mem_mem_mem_mem_mem_mem_extMem_extMem_lineWriteRq_SendEn_132;
  logic sys_core_mem_mem_mem_mem_mem_mem_mem_extMem_lineReadRqReady_Recv_133;
  logic sys_core_mem_mem_mem_mem_mem_mem_mem_extMem_lineWriteRqReady_Recv_134;
  logic sys_core_mem_mem_mem_mem_mem_mem_mem_extMem_lineReadRpValid_Recv_135;

  // =========================================================================
  // Instantiate Guru Generated Top Module
  // =========================================================================
  top top_inst (
    .decl_sys_core_mem_mem_ram_ram_fetch_lineReadRq_Send_57(decl_sys_core_mem_mem_ram_ram_fetch_lineReadRq_Send_57),
    .decl_sys_core_mem_mem_ram_ram_fetch_lineReadRq_SendEn_57(decl_sys_core_mem_mem_ram_ram_fetch_lineReadRq_SendEn_57),
    .sys_core_mem_mem_ram_ram_fetch_lineReadRp_Recv_58(sys_core_mem_mem_ram_ram_fetch_lineReadRp_Recv_58),
    .decl_sys_core_mem_mem_ram_ram_lineReadRq_Send_59(decl_sys_core_mem_mem_ram_ram_lineReadRq_Send_59),
    .decl_sys_core_mem_mem_ram_ram_lineReadRq_SendEn_59(decl_sys_core_mem_mem_ram_ram_lineReadRq_SendEn_59),
    .sys_core_mem_mem_ram_ram_lineReadRp_Recv_60(sys_core_mem_mem_ram_ram_lineReadRp_Recv_60),
    .decl_sys_core_mem_mem_ram_ram_lineWriteRq_Send_61(decl_sys_core_mem_mem_ram_ram_lineWriteRq_Send_61),
    .decl_sys_core_mem_mem_ram_ram_lineWriteRq_SendEn_61(decl_sys_core_mem_mem_ram_ram_lineWriteRq_SendEn_61),
    .sys_core_mem_mem_ram_fetch_lineReadRqReady_Recv_62(sys_core_mem_mem_ram_fetch_lineReadRqReady_Recv_62),
    .sys_core_mem_mem_ram_fetch_lineReadRpValid_Recv_63(sys_core_mem_mem_ram_fetch_lineReadRpValid_Recv_63),
    .sys_core_mem_mem_ram_lineReadRqReady_Recv_69(sys_core_mem_mem_ram_lineReadRqReady_Recv_69),
    .sys_core_mem_mem_ram_lineWriteRqReady_Recv_70(sys_core_mem_mem_ram_lineWriteRqReady_Recv_70),
    .sys_core_mem_mem_ram_lineReadRpValid_Recv_71(sys_core_mem_mem_ram_lineReadRpValid_Recv_71),
    .decl_sys_core_mem_mem_mem_revTable_lineReadRqReady_Send_92(decl_sys_core_mem_mem_mem_revTable_lineReadRqReady_Send_92),
    .decl_sys_core_mem_mem_mem_revTable_lineReadRqReady_SendEn_92(decl_sys_core_mem_mem_mem_revTable_lineReadRqReady_SendEn_92),
    .decl_sys_core_mem_mem_mem_revTable_lineWriteRqReady_Send_93(decl_sys_core_mem_mem_mem_revTable_lineWriteRqReady_Send_93),
    .decl_sys_core_mem_mem_mem_revTable_lineWriteRqReady_SendEn_93(decl_sys_core_mem_mem_mem_revTable_lineWriteRqReady_SendEn_93),
    .sys_core_mem_mem_mem_revTable_lineReadRpReady_Recv_94(sys_core_mem_mem_mem_revTable_lineReadRpReady_Recv_94),
    .sys_core_mem_mem_mem_mem_mem_mem_plic_plic_UartIrq_Recv_127(sys_core_mem_mem_mem_mem_mem_mem_plic_plic_UartIrq_Recv_127),
    .decl_sys_core_mem_mem_mem_mem_mem_mem_mem_extMem_extMem_lineReadRq_Send_130(decl_sys_core_mem_mem_mem_mem_mem_mem_mem_extMem_extMem_lineReadRq_Send_130),
    .decl_sys_core_mem_mem_mem_mem_mem_mem_mem_extMem_extMem_lineReadRq_SendEn_130(decl_sys_core_mem_mem_mem_mem_mem_mem_mem_extMem_extMem_lineReadRq_SendEn_130),
    .sys_core_mem_mem_mem_mem_mem_mem_mem_extMem_extMem_lineReadRp_Recv_131(sys_core_mem_mem_mem_mem_mem_mem_mem_extMem_extMem_lineReadRp_Recv_131),
    .decl_sys_core_mem_mem_mem_mem_mem_mem_mem_extMem_extMem_lineWriteRq_Send_132(decl_sys_core_mem_mem_mem_mem_mem_mem_mem_extMem_extMem_lineWriteRq_Send_132),
    .decl_sys_core_mem_mem_mem_mem_mem_mem_mem_extMem_extMem_lineWriteRq_SendEn_132(decl_sys_core_mem_mem_mem_mem_mem_mem_mem_extMem_extMem_lineWriteRq_SendEn_132),
    .sys_core_mem_mem_mem_mem_mem_mem_mem_extMem_lineReadRqReady_Recv_133(sys_core_mem_mem_mem_mem_mem_mem_mem_extMem_lineReadRqReady_Recv_133),
    .sys_core_mem_mem_mem_mem_mem_mem_mem_extMem_lineWriteRqReady_Recv_134(sys_core_mem_mem_mem_mem_mem_mem_mem_extMem_lineWriteRqReady_Recv_134),
    .sys_core_mem_mem_mem_mem_mem_mem_mem_extMem_lineReadRpValid_Recv_135(sys_core_mem_mem_mem_mem_mem_mem_mem_extMem_lineReadRpValid_Recv_135),

    .clk_core(clk_core),
    .rst_n_core(rst_n_core)
  );

  // =========================================================================
  // Tie Off Ready Signals
  // =========================================================================
  assign sys_core_mem_mem_ram_fetch_lineReadRqReady_Recv_62 = 1'b1;
  assign sys_core_mem_mem_ram_lineReadRqReady_Recv_69       = 1'b1;
  assign sys_core_mem_mem_ram_lineWriteRqReady_Recv_70      = 1'b1;
  assign sys_core_mem_mem_mem_revTable_lineReadRpReady_Recv_94 = 1'b1;

  assign sys_core_mem_mem_mem_mem_mem_mem_mem_extMem_lineReadRqReady_Recv_133  = 1'b1;
  assign sys_core_mem_mem_mem_mem_mem_mem_mem_extMem_lineWriteRqReady_Recv_134 = 1'b1;

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
  logic          next_dlab;
  logic [7 : 0]  ie;
  logic          rxBufValid;
  logic [7 : 0]  rxBuf;

  logic [31 : 0]   tohostAddr;
  longint unsigned cycleCount;
  longint unsigned maxCycles;

  assign sys_core_mem_mem_ram_fetch_lineReadRpValid_Recv_63 = ramFetchReadRpValid;
  assign sys_core_mem_mem_ram_lineReadRpValid_Recv_71       = ramDataReadRpValid;
  assign sys_core_mem_mem_mem_mem_mem_mem_mem_extMem_lineReadRpValid_Recv_135 = uartReadRpValid;

  // PLIC UartIrq
  assign sys_core_mem_mem_mem_mem_mem_mem_plic_plic_UartIrq_Recv_127 =
    ie[0] ? (rxBufValid | ie[1]) : ie[1];

  // Combinational RAM Fetch Read Response
  always_comb begin
    logic [LineIdxBits - 1 : 0] fetchIdx;
    fetchIdx = ramFetchReadAddr[LineIdxBits + 2 : 3];
    sys_core_mem_mem_ram_ram_fetch_lineReadRp_Recv_58.data   = ramData[fetchIdx];
    sys_core_mem_mem_ram_ram_fetch_lineReadRp_Recv_58.tag[0] = ramTag[fetchIdx];
  end

  // Combinational RAM Data Read Response
  always_comb begin
    logic [LineIdxBits - 1 : 0] dataIdx;
    dataIdx = ramDataReadAddr[LineIdxBits + 2 : 3];
    sys_core_mem_mem_ram_ram_lineReadRp_Recv_60.data   = ramData[dataIdx];
    sys_core_mem_mem_ram_ram_lineReadRp_Recv_60.tag[0] = ramTag[dataIdx];
  end

  // Combinational UART Read Response
  always_comb begin
    sys_core_mem_mem_mem_mem_mem_mem_mem_extMem_extMem_lineReadRp_Recv_131 = '0;
    if (uartReadAddr == 32'h1000_0000) begin
      sys_core_mem_mem_mem_mem_mem_mem_mem_extMem_extMem_lineReadRp_Recv_131.data[0] =
        rxBufValid ? rxBuf : 8'h00;
    end else if (uartReadAddr == 32'h1000_0010) begin
      sys_core_mem_mem_mem_mem_mem_mem_mem_extMem_extMem_lineReadRp_Recv_131.data[4] =
        rxBufValid ? 8'h21 : 8'h20;
    end
  end

  // Sequential RAM, UART & Cycle Updates
  always_ff @(posedge clk_core or negedge rst_n_core) begin
    if (!rst_n_core) begin
      ramFetchReadAddr    <= 32'h0;
      ramFetchReadRpValid <= 1'b0;
      ramDataReadAddr     <= 32'h0;
      ramDataReadRpValid  <= 1'b0;
      uartReadAddr        <= 32'h0;
      uartReadRpValid     <= 1'b0;
      dlab                <= 1'b0;
      ie                  <= 8'h0;
      rxBufValid          <= 1'b0;
      rxBuf               <= 8'h0;
      cycleCount          <= 64'd0;
    end else begin
      // 1. Cycle progress logging
      if ((cycleCount % 64'd250000) == 64'd0) begin
        $display("[Cycle %0d]", cycleCount);
        $fflush(32'h8000_0001);
      end
      if (cycleCount + 64'd1 >= maxCycles) begin
        $finish;
      end
      cycleCount <= cycleCount + 64'd1;

      // 2. RAM Fetch Read Request
      if (decl_sys_core_mem_mem_ram_ram_fetch_lineReadRq_SendEn_57) begin
        ramFetchReadAddr    <= decl_sys_core_mem_mem_ram_ram_fetch_lineReadRq_Send_57;
        ramFetchReadRpValid <= 1'b1;
      end else begin
        ramFetchReadRpValid <= 1'b0;
      end

      // 3. RAM Data Read Request
      if (decl_sys_core_mem_mem_ram_ram_lineReadRq_SendEn_59) begin
        ramDataReadAddr    <= decl_sys_core_mem_mem_ram_ram_lineReadRq_Send_59;
        ramDataReadRpValid <= 1'b1;
      end else begin
        ramDataReadRpValid <= 1'b0;
      end

      // 4. RAM Write Request & Dynamic tohost Check
      if (decl_sys_core_mem_mem_ram_ram_lineWriteRq_SendEn_61) begin
        logic [31 : 0]              wrAddr;
        logic [LineIdxBits - 1 : 0] wrIdx;
        logic [31 : 0]              tohostLineAddr;
        logic [2 : 0]               tohostByteOff;
        logic [31 : 0]              tohostVal;

        wrAddr = decl_sys_core_mem_mem_ram_ram_lineWriteRq_Send_61.addr;
        wrIdx  = wrAddr[LineIdxBits + 2 : 3];

        for (int b = 0; b < LineBytes; b++) begin
          if (decl_sys_core_mem_mem_ram_ram_lineWriteRq_Send_61.dataMask[b]) begin
            ramData[wrIdx][b*8 +: 8] <= decl_sys_core_mem_mem_ram_ram_lineWriteRq_Send_61.data[b];
          end
        end
        if (decl_sys_core_mem_mem_ram_ram_lineWriteRq_Send_61.tagMask[0]) begin
          ramTag[wrIdx] <= decl_sys_core_mem_mem_ram_ram_lineWriteRq_Send_61.tag[0];
        end

        tohostLineAddr = {tohostAddr[31 : 3], 3'b000};
        tohostByteOff  = tohostAddr[2 : 0];
        if ((tohostAddr != 32'h0) &&
            (wrAddr == tohostLineAddr) &&
            decl_sys_core_mem_mem_ram_ram_lineWriteRq_Send_61.dataMask[tohostByteOff]) begin
          for (int b = 0; b < 4; b++) begin
            if (decl_sys_core_mem_mem_ram_ram_lineWriteRq_Send_61.dataMask[int'(tohostByteOff) + b]) begin
              tohostVal[b*8 +: 8] = decl_sys_core_mem_mem_ram_ram_lineWriteRq_Send_61.data[int'(tohostByteOff) + b];
            end else begin
              tohostVal[b*8 +: 8] = ramData[wrIdx][(int'(tohostByteOff) + b)*8 +: 8];
            end
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
      end

      // 5. Consume rxBuf when a read response from 0x10000000 is delivered
      if (uartReadRpValid && (uartReadAddr == 32'h1000_0000) && rxBufValid) begin
        rxBufValid <= 1'b0;
      end

      // 6. UART Read Request
      if (decl_sys_core_mem_mem_mem_mem_mem_mem_mem_extMem_extMem_lineReadRq_SendEn_130) begin
        uartReadAddr    <= decl_sys_core_mem_mem_mem_mem_mem_mem_mem_extMem_extMem_lineReadRq_Send_130;
        uartReadRpValid <= 1'b1;
      end else begin
        uartReadRpValid <= 1'b0;
      end

      // 7. UART Write Request at 0x10000000
      if (decl_sys_core_mem_mem_mem_mem_mem_mem_mem_extMem_extMem_lineWriteRq_SendEn_132) begin
        if (decl_sys_core_mem_mem_mem_mem_mem_mem_mem_extMem_extMem_lineWriteRq_Send_132.addr == 32'h1000_0000) begin
          next_dlab = dlab;
          if (decl_sys_core_mem_mem_mem_mem_mem_mem_mem_extMem_extMem_lineWriteRq_Send_132.dataMask[12]) begin
            next_dlab = decl_sys_core_mem_mem_mem_mem_mem_mem_mem_extMem_extMem_lineWriteRq_Send_132.data[12][7];
          end
          dlab <= next_dlab;

          if (decl_sys_core_mem_mem_mem_mem_mem_mem_mem_extMem_extMem_lineWriteRq_Send_132.dataMask[0] && !next_dlab) begin
            $write("%c", decl_sys_core_mem_mem_mem_mem_mem_mem_mem_extMem_extMem_lineWriteRq_Send_132.data[0]);
            $fflush(32'h8000_0001);
          end

          if (decl_sys_core_mem_mem_mem_mem_mem_mem_mem_extMem_extMem_lineWriteRq_Send_132.dataMask[4] && !next_dlab) begin
            ie <= decl_sys_core_mem_mem_mem_mem_mem_mem_mem_extMem_extMem_lineWriteRq_Send_132.data[4];
          end
        end
      end
    end
  end

  // =========================================================================
  // Memory Initialization, Plusargs & Clock/Reset Generation
  // =========================================================================
  initial begin
    string binFile;

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
