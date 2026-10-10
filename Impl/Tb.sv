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

  `include "TbCommon.sv"

  // =========================================================================
  // 1. External RAM Ports (implConcreteRegions[0]: ramRegion)
  // =========================================================================
  logic [31 : 0] decl_sys_core_mem__ram_ram_fetch_lineReadRq_Send_57;
  logic          decl_sys_core_mem__ram_ram_fetch_lineReadRq_SendEn_57;
  ramReadRp_t    sys_core_mem__ram_ram_fetch_lineReadRp_Recv_58;

  logic [31 : 0] decl_sys_core_mem__ram_ram_lineReadRq_Send_59;
  logic          decl_sys_core_mem__ram_ram_lineReadRq_SendEn_59;
  ramReadRp_t    sys_core_mem__ram_ram_lineReadRp_Recv_60;

  ramWriteRq_t   decl_sys_core_mem__ram_ram_lineWriteRq_Send_61;
  logic          decl_sys_core_mem__ram_ram_lineWriteRq_SendEn_61;

  logic sys_core_mem__ram_fetch_lineReadRqReady_Recv_62;
  logic sys_core_mem__ram_fetch_lineReadRpValid_Recv_63;
  logic sys_core_mem__ram_lineReadRqReady_Recv_69;
  logic sys_core_mem__ram_lineWriteRqReady_Recv_70;
  logic sys_core_mem__ram_lineReadRpValid_Recv_71;

  // =========================================================================
  // 2. Revocation Table Target Port Signals (implConcreteRegions[1]: revTableRegion)
  // =========================================================================
  logic decl_sys_core_mem___revTable_lineReadRqReady_Send_92;
  logic decl_sys_core_mem___revTable_lineReadRqReady_SendEn_92;
  logic decl_sys_core_mem___revTable_lineWriteRqReady_Send_93;
  logic decl_sys_core_mem___revTable_lineWriteRqReady_SendEn_93;
  logic sys_core_mem___revTable_lineReadRpReady_Recv_94;

  // =========================================================================
  // 3. PLIC UART Interrupt Signal (implConcreteRegions[4]: plicMemRegion)
  // =========================================================================
  logic sys_core_mem______plic_plic_UartIrq_Recv_127;

  // =========================================================================
  // 4. External Memory / UART MMIO Signals (implConcreteRegions[5]: extMemRegion)
  // =========================================================================
  logic [31 : 0]  decl_sys_core_mem_______extMem_extMem_lineReadRq_Send_130;
  logic           decl_sys_core_mem_______extMem_extMem_lineReadRq_SendEn_130;
  extMemReadRp_t  sys_core_mem_______extMem_extMem_lineReadRp_Recv_131;
  extMemWriteRq_t decl_sys_core_mem_______extMem_extMem_lineWriteRq_Send_132;
  logic           decl_sys_core_mem_______extMem_extMem_lineWriteRq_SendEn_132;
  logic           sys_core_mem_______extMem_lineReadRqReady_Recv_133;
  logic           sys_core_mem_______extMem_lineWriteRqReady_Recv_134;
  logic           sys_core_mem_______extMem_lineReadRpValid_Recv_135;

  // =========================================================================
  // Instantiate Guru Generated Top Module
  // =========================================================================
  top top_inst (
    .decl_sys_core_mem__ram_ram_fetch_lineReadRq_Send_57(decl_sys_core_mem__ram_ram_fetch_lineReadRq_Send_57),
    .decl_sys_core_mem__ram_ram_fetch_lineReadRq_SendEn_57(decl_sys_core_mem__ram_ram_fetch_lineReadRq_SendEn_57),
    .sys_core_mem__ram_ram_fetch_lineReadRp_Recv_58(sys_core_mem__ram_ram_fetch_lineReadRp_Recv_58),
    .decl_sys_core_mem__ram_ram_lineReadRq_Send_59(decl_sys_core_mem__ram_ram_lineReadRq_Send_59),
    .decl_sys_core_mem__ram_ram_lineReadRq_SendEn_59(decl_sys_core_mem__ram_ram_lineReadRq_SendEn_59),
    .sys_core_mem__ram_ram_lineReadRp_Recv_60(sys_core_mem__ram_ram_lineReadRp_Recv_60),
    .decl_sys_core_mem__ram_ram_lineWriteRq_Send_61(decl_sys_core_mem__ram_ram_lineWriteRq_Send_61),
    .decl_sys_core_mem__ram_ram_lineWriteRq_SendEn_61(decl_sys_core_mem__ram_ram_lineWriteRq_SendEn_61),
    .sys_core_mem__ram_fetch_lineReadRqReady_Recv_62(sys_core_mem__ram_fetch_lineReadRqReady_Recv_62),
    .sys_core_mem__ram_fetch_lineReadRpValid_Recv_63(sys_core_mem__ram_fetch_lineReadRpValid_Recv_63),
    .sys_core_mem__ram_lineReadRqReady_Recv_69(sys_core_mem__ram_lineReadRqReady_Recv_69),
    .sys_core_mem__ram_lineWriteRqReady_Recv_70(sys_core_mem__ram_lineWriteRqReady_Recv_70),
    .sys_core_mem__ram_lineReadRpValid_Recv_71(sys_core_mem__ram_lineReadRpValid_Recv_71),
    .decl_sys_core_mem___revTable_lineReadRqReady_Send_92(decl_sys_core_mem___revTable_lineReadRqReady_Send_92),
    .decl_sys_core_mem___revTable_lineReadRqReady_SendEn_92(decl_sys_core_mem___revTable_lineReadRqReady_SendEn_92),
    .decl_sys_core_mem___revTable_lineWriteRqReady_Send_93(decl_sys_core_mem___revTable_lineWriteRqReady_Send_93),
    .decl_sys_core_mem___revTable_lineWriteRqReady_SendEn_93(decl_sys_core_mem___revTable_lineWriteRqReady_SendEn_93),
    .sys_core_mem___revTable_lineReadRpReady_Recv_94(sys_core_mem___revTable_lineReadRpReady_Recv_94),
    .sys_core_mem______plic_plic_UartIrq_Recv_127(sys_core_mem______plic_plic_UartIrq_Recv_127),
    .decl_sys_core_mem_______extMem_extMem_lineReadRq_Send_130(decl_sys_core_mem_______extMem_extMem_lineReadRq_Send_130),
    .decl_sys_core_mem_______extMem_extMem_lineReadRq_SendEn_130(decl_sys_core_mem_______extMem_extMem_lineReadRq_SendEn_130),
    .sys_core_mem_______extMem_extMem_lineReadRp_Recv_131(sys_core_mem_______extMem_extMem_lineReadRp_Recv_131),
    .decl_sys_core_mem_______extMem_extMem_lineWriteRq_Send_132(decl_sys_core_mem_______extMem_extMem_lineWriteRq_Send_132),
    .decl_sys_core_mem_______extMem_extMem_lineWriteRq_SendEn_132(decl_sys_core_mem_______extMem_extMem_lineWriteRq_SendEn_132),
    .sys_core_mem_______extMem_lineReadRqReady_Recv_133(sys_core_mem_______extMem_lineReadRqReady_Recv_133),
    .sys_core_mem_______extMem_lineWriteRqReady_Recv_134(sys_core_mem_______extMem_lineWriteRqReady_Recv_134),
    .sys_core_mem_______extMem_lineReadRpValid_Recv_135(sys_core_mem_______extMem_lineReadRpValid_Recv_135),

    .clk_core(clk_core),
    .rst_n_core(rst_n_core)
  );

  // =========================================================================
  // Sequential Port Dispatch via Shared tb_send / tb_recv
  // =========================================================================
  always_ff @(posedge clk_core or negedge rst_n_core) begin
    if (!rst_n_core) begin
      cycleCount <= 64'd0;
      sys_core_mem__ram_fetch_lineReadRqReady_Recv_62                    <= 1'b1;
      sys_core_mem__ram_fetch_lineReadRpValid_Recv_63                    <= 1'b0;
      sys_core_mem__ram_ram_fetch_lineReadRp_Recv_58                     <= '0;
      sys_core_mem__ram_lineReadRqReady_Recv_69                          <= 1'b1;
      sys_core_mem__ram_lineWriteRqReady_Recv_70                         <= 1'b1;
      sys_core_mem__ram_lineReadRpValid_Recv_71                          <= 1'b0;
      sys_core_mem__ram_ram_lineReadRp_Recv_60                           <= '0;
      sys_core_mem___revTable_lineReadRpReady_Recv_94                    <= 1'b1;
      sys_core_mem______plic_plic_UartIrq_Recv_127                       <= 1'b0;
      sys_core_mem_______extMem_lineReadRqReady_Recv_133                 <= 1'b1;
      sys_core_mem_______extMem_lineWriteRqReady_Recv_134                <= 1'b1;
      sys_core_mem_______extMem_lineReadRpValid_Recv_135                 <= 1'b0;
      sys_core_mem_______extMem_extMem_lineReadRp_Recv_131               <= '0;
    end else begin
      logic fetchRpValid;
      logic dataRpValid;
      logic extRpValid;

      if ((cycleCount % 64'd250000) == 64'd0) begin
        $display("[Cycle %0d]", cycleCount);
        $fflush(32'h8000_0001);
      end
      if (cycleCount + 64'd1 >= maxCycles) begin
        $finish;
      end
      cycleCount <= cycleCount + 64'd1;

      // 1. Process Send ports
      if (decl_sys_core_mem__ram_ram_fetch_lineReadRq_SendEn_57) begin
        tb_send("decl_sys_core_mem__ram_ram_fetch_lineReadRq_Send_57",
                tb_io_val_t'(decl_sys_core_mem__ram_ram_fetch_lineReadRq_Send_57));
      end
      if (decl_sys_core_mem__ram_ram_lineReadRq_SendEn_59) begin
        tb_send("decl_sys_core_mem__ram_ram_lineReadRq_Send_59",
                tb_io_val_t'(decl_sys_core_mem__ram_ram_lineReadRq_Send_59));
      end
      if (decl_sys_core_mem__ram_ram_lineWriteRq_SendEn_61) begin
        tb_send("decl_sys_core_mem__ram_ram_lineWriteRq_Send_61",
                tb_io_val_t'(decl_sys_core_mem__ram_ram_lineWriteRq_Send_61));
      end
      if (decl_sys_core_mem_______extMem_extMem_lineReadRq_SendEn_130) begin
        tb_send("decl_sys_core_mem_______extMem_extMem_lineReadRq_Send_130",
                tb_io_val_t'(decl_sys_core_mem_______extMem_extMem_lineReadRq_Send_130));
      end
      if (decl_sys_core_mem_______extMem_extMem_lineWriteRq_SendEn_132) begin
        tb_send("decl_sys_core_mem_______extMem_extMem_lineWriteRq_Send_132",
                tb_io_val_t'(decl_sys_core_mem_______extMem_extMem_lineWriteRq_Send_132));
      end

      // 2. Drive Recv ports for next cycle
      sys_core_mem__ram_fetch_lineReadRqReady_Recv_62 <=
        verilog_bits#(TbIoWidth, 0, 0)::extract(tb_recv("sys_core_mem__ram_fetch_lineReadRqReady_Recv_62"));
      fetchRpValid =
        verilog_bits#(TbIoWidth, 0, 0)::extract(tb_recv("sys_core_mem__ram_fetch_lineReadRpValid_Recv_63"));
      sys_core_mem__ram_fetch_lineReadRpValid_Recv_63 <= fetchRpValid;
      if (fetchRpValid) begin
        sys_core_mem__ram_ram_fetch_lineReadRp_Recv_58 <=
          verilog_bits#(TbIoWidth, $bits(ramReadRp_t) - 1, 0)::extract(tb_recv("sys_core_mem__ram_ram_fetch_lineReadRp_Recv_58"));
      end

      sys_core_mem__ram_lineReadRqReady_Recv_69 <=
        verilog_bits#(TbIoWidth, 0, 0)::extract(tb_recv("sys_core_mem__ram_lineReadRqReady_Recv_69"));
      sys_core_mem__ram_lineWriteRqReady_Recv_70 <=
        verilog_bits#(TbIoWidth, 0, 0)::extract(tb_recv("sys_core_mem__ram_lineWriteRqReady_Recv_70"));
      dataRpValid =
        verilog_bits#(TbIoWidth, 0, 0)::extract(tb_recv("sys_core_mem__ram_lineReadRpValid_Recv_71"));
      sys_core_mem__ram_lineReadRpValid_Recv_71 <= dataRpValid;
      if (dataRpValid) begin
        sys_core_mem__ram_ram_lineReadRp_Recv_60 <=
          verilog_bits#(TbIoWidth, $bits(ramReadRp_t) - 1, 0)::extract(tb_recv("sys_core_mem__ram_ram_lineReadRp_Recv_60"));
      end

      sys_core_mem___revTable_lineReadRpReady_Recv_94 <=
        verilog_bits#(TbIoWidth, 0, 0)::extract(tb_recv("sys_core_mem___revTable_lineReadRpReady_Recv_94"));
      sys_core_mem______plic_plic_UartIrq_Recv_127 <=
        verilog_bits#(TbIoWidth, 0, 0)::extract(tb_recv("sys_core_mem______plic_plic_UartIrq_Recv_127"));

      sys_core_mem_______extMem_lineReadRqReady_Recv_133 <=
        verilog_bits#(TbIoWidth, 0, 0)::extract(tb_recv("sys_core_mem_______extMem_lineReadRqReady_Recv_133"));
      sys_core_mem_______extMem_lineWriteRqReady_Recv_134 <=
        verilog_bits#(TbIoWidth, 0, 0)::extract(tb_recv("sys_core_mem_______extMem_lineWriteRqReady_Recv_134"));
      extRpValid =
        verilog_bits#(TbIoWidth, 0, 0)::extract(tb_recv("sys_core_mem_______extMem_lineReadRpValid_Recv_135"));
      sys_core_mem_______extMem_lineReadRpValid_Recv_135 <= extRpValid;
      if (extRpValid) begin
        sys_core_mem_______extMem_extMem_lineReadRp_Recv_131 <=
          verilog_bits#(TbIoWidth, $bits(extMemReadRp_t) - 1, 0)::extract(tb_recv("sys_core_mem_______extMem_extMem_lineReadRp_Recv_131"));
      end
    end
  end

  initial begin
    tb_init();

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
