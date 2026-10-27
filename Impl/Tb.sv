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
  logic [31 : 0] decl_Send_sys_core_mem___ram_ram_fetch_lineReadRq;
  logic          decl_SendEn_sys_core_mem___ram_ram_fetch_lineReadRq;
  ramReadRp_t    Recv_sys_core_mem___ram_ram_fetch_lineReadRp;
  logic          decl_SendEn_sys_core_mem___ram_ram_fetch_fenceIRq;
  logic          Recv_sys_core_mem___ram_ram_fetch_fenceIAck;

  logic [31 : 0] decl_Send_sys_core_mem___ram_ram_lineReadRq;
  logic          decl_SendEn_sys_core_mem___ram_ram_lineReadRq;
  ramReadRp_t    Recv_sys_core_mem___ram_ram_lineReadRp;

  ramWriteRq_t   decl_Send_sys_core_mem___ram_ram_lineWriteRq;
  logic          decl_SendEn_sys_core_mem___ram_ram_lineWriteRq;

  logic Recv_sys_core_mem___ram_fetch_lineReadRqReady;
  logic Recv_sys_core_mem___ram_fetch_lineReadRpValid;
  logic decl_SendEn_sys_core_mem___ram_fetch_lineReadRpReady;
  logic Recv_sys_core_mem___ram_lineReadRqReady;
  logic Recv_sys_core_mem___ram_lineWriteRqReady;
  logic Recv_sys_core_mem___ram_lineReadRpValid;
  logic decl_SendEn_sys_core_mem___ram_lineReadRpReady;

  // =========================================================================
  // 2. External Revocation Table Ports (implConcreteRegions[1]: revTableRegion)
  // =========================================================================
  logic [31 : 0]     decl_Send_sys_core_mem____revTable_revTable_fetch_lineReadRq;
  logic              decl_SendEn_sys_core_mem____revTable_revTable_fetch_lineReadRq;
  revTableReadRp_t   Recv_sys_core_mem____revTable_revTable_fetch_lineReadRp;
  logic              decl_SendEn_sys_core_mem____revTable_revTable_fetch_fenceIRq;
  logic              Recv_sys_core_mem____revTable_revTable_fetch_fenceIAck;

  logic [31 : 0]     decl_Send_sys_core_mem____revTable_revTable_lineReadRq;
  logic              decl_SendEn_sys_core_mem____revTable_revTable_lineReadRq;
  revTableReadRp_t   Recv_sys_core_mem____revTable_revTable_lineReadRp;

  revTableWriteRq_t  decl_Send_sys_core_mem____revTable_revTable_lineWriteRq;
  logic              decl_SendEn_sys_core_mem____revTable_revTable_lineWriteRq;

  logic Recv_sys_core_mem____revTable_fetch_lineReadRqReady;
  logic Recv_sys_core_mem____revTable_fetch_lineReadRpValid;
  logic decl_SendEn_sys_core_mem____revTable_fetch_lineReadRpReady;
  logic Recv_sys_core_mem____revTable_lineReadRqReady;
  logic Recv_sys_core_mem____revTable_lineWriteRqReady;
  logic Recv_sys_core_mem____revTable_lineReadRpValid;
  logic decl_SendEn_sys_core_mem____revTable_lineReadRpReady;

  // =========================================================================
  // 3. PLIC UART Interrupt Signal (implConcreteRegions[4]: plicMemRegion)
  // =========================================================================
  logic Recv_sys_core_mem_______plic_plic_UartIrq;

  // =========================================================================
  // 4. UART MMIO Signals (implConcreteRegions[5]: uartRegion)
  // =========================================================================
  logic [31 : 0] decl_Send_sys_core_mem________uart_uart_fetch_lineReadRq;
  logic          decl_SendEn_sys_core_mem________uart_uart_fetch_lineReadRq;
  uartReadRp_t   Recv_sys_core_mem________uart_uart_fetch_lineReadRp;
  logic          decl_SendEn_sys_core_mem________uart_uart_fetch_fenceIRq;
  logic          Recv_sys_core_mem________uart_uart_fetch_fenceIAck;

  logic [31 : 0] decl_Send_sys_core_mem________uart_uart_lineReadRq;
  logic          decl_SendEn_sys_core_mem________uart_uart_lineReadRq;
  uartReadRp_t   Recv_sys_core_mem________uart_uart_lineReadRp;
  uartWriteRq_t  decl_Send_sys_core_mem________uart_uart_lineWriteRq;
  logic          decl_SendEn_sys_core_mem________uart_uart_lineWriteRq;
  logic          Recv_sys_core_mem________uart_fetch_lineReadRqReady;
  logic          Recv_sys_core_mem________uart_fetch_lineReadRpValid;
  logic          decl_SendEn_sys_core_mem________uart_fetch_lineReadRpReady;
  logic          Recv_sys_core_mem________uart_lineReadRqReady;
  logic          Recv_sys_core_mem________uart_lineWriteRqReady;
  logic          Recv_sys_core_mem________uart_lineReadRpValid;
  logic          decl_SendEn_sys_core_mem________uart_lineReadRpReady;

  // =========================================================================
  // Instantiate Guru Generated Top Module
  // =========================================================================
  top top_inst (
    .decl_Send_sys_core_mem___ram_ram_fetch_lineReadRq(decl_Send_sys_core_mem___ram_ram_fetch_lineReadRq),
    .decl_SendEn_sys_core_mem___ram_ram_fetch_lineReadRq(decl_SendEn_sys_core_mem___ram_ram_fetch_lineReadRq),
    .Recv_sys_core_mem___ram_ram_fetch_lineReadRp(Recv_sys_core_mem___ram_ram_fetch_lineReadRp),
    .decl_SendEn_sys_core_mem___ram_ram_fetch_fenceIRq(decl_SendEn_sys_core_mem___ram_ram_fetch_fenceIRq),
    .Recv_sys_core_mem___ram_ram_fetch_fenceIAck(Recv_sys_core_mem___ram_ram_fetch_fenceIAck),
    .decl_Send_sys_core_mem___ram_ram_lineReadRq(decl_Send_sys_core_mem___ram_ram_lineReadRq),
    .decl_SendEn_sys_core_mem___ram_ram_lineReadRq(decl_SendEn_sys_core_mem___ram_ram_lineReadRq),
    .Recv_sys_core_mem___ram_ram_lineReadRp(Recv_sys_core_mem___ram_ram_lineReadRp),
    .decl_Send_sys_core_mem___ram_ram_lineWriteRq(decl_Send_sys_core_mem___ram_ram_lineWriteRq),
    .decl_SendEn_sys_core_mem___ram_ram_lineWriteRq(decl_SendEn_sys_core_mem___ram_ram_lineWriteRq),
    .Recv_sys_core_mem___ram_fetch_lineReadRqReady(Recv_sys_core_mem___ram_fetch_lineReadRqReady),
    .Recv_sys_core_mem___ram_fetch_lineReadRpValid(Recv_sys_core_mem___ram_fetch_lineReadRpValid),
    .decl_SendEn_sys_core_mem___ram_fetch_lineReadRpReady(decl_SendEn_sys_core_mem___ram_fetch_lineReadRpReady),
    .Recv_sys_core_mem___ram_lineReadRqReady(Recv_sys_core_mem___ram_lineReadRqReady),
    .Recv_sys_core_mem___ram_lineWriteRqReady(Recv_sys_core_mem___ram_lineWriteRqReady),
    .Recv_sys_core_mem___ram_lineReadRpValid(Recv_sys_core_mem___ram_lineReadRpValid),
    .decl_SendEn_sys_core_mem___ram_lineReadRpReady(decl_SendEn_sys_core_mem___ram_lineReadRpReady),

    .decl_Send_sys_core_mem____revTable_revTable_fetch_lineReadRq(decl_Send_sys_core_mem____revTable_revTable_fetch_lineReadRq),
    .decl_SendEn_sys_core_mem____revTable_revTable_fetch_lineReadRq(decl_SendEn_sys_core_mem____revTable_revTable_fetch_lineReadRq),
    .Recv_sys_core_mem____revTable_revTable_fetch_lineReadRp(Recv_sys_core_mem____revTable_revTable_fetch_lineReadRp),
    .decl_SendEn_sys_core_mem____revTable_revTable_fetch_fenceIRq(decl_SendEn_sys_core_mem____revTable_revTable_fetch_fenceIRq),
    .Recv_sys_core_mem____revTable_revTable_fetch_fenceIAck(Recv_sys_core_mem____revTable_revTable_fetch_fenceIAck),
    .decl_Send_sys_core_mem____revTable_revTable_lineReadRq(decl_Send_sys_core_mem____revTable_revTable_lineReadRq),
    .decl_SendEn_sys_core_mem____revTable_revTable_lineReadRq(decl_SendEn_sys_core_mem____revTable_revTable_lineReadRq),
    .Recv_sys_core_mem____revTable_revTable_lineReadRp(Recv_sys_core_mem____revTable_revTable_lineReadRp),
    .decl_Send_sys_core_mem____revTable_revTable_lineWriteRq(decl_Send_sys_core_mem____revTable_revTable_lineWriteRq),
    .decl_SendEn_sys_core_mem____revTable_revTable_lineWriteRq(decl_SendEn_sys_core_mem____revTable_revTable_lineWriteRq),
    .Recv_sys_core_mem____revTable_fetch_lineReadRqReady(Recv_sys_core_mem____revTable_fetch_lineReadRqReady),
    .Recv_sys_core_mem____revTable_fetch_lineReadRpValid(Recv_sys_core_mem____revTable_fetch_lineReadRpValid),
    .decl_SendEn_sys_core_mem____revTable_fetch_lineReadRpReady(decl_SendEn_sys_core_mem____revTable_fetch_lineReadRpReady),
    .Recv_sys_core_mem____revTable_lineReadRqReady(Recv_sys_core_mem____revTable_lineReadRqReady),
    .Recv_sys_core_mem____revTable_lineWriteRqReady(Recv_sys_core_mem____revTable_lineWriteRqReady),
    .Recv_sys_core_mem____revTable_lineReadRpValid(Recv_sys_core_mem____revTable_lineReadRpValid),
    .decl_SendEn_sys_core_mem____revTable_lineReadRpReady(decl_SendEn_sys_core_mem____revTable_lineReadRpReady),

    .Recv_sys_core_mem_______plic_plic_UartIrq(Recv_sys_core_mem_______plic_plic_UartIrq),

    .decl_Send_sys_core_mem________uart_uart_fetch_lineReadRq(decl_Send_sys_core_mem________uart_uart_fetch_lineReadRq),
    .decl_SendEn_sys_core_mem________uart_uart_fetch_lineReadRq(decl_SendEn_sys_core_mem________uart_uart_fetch_lineReadRq),
    .Recv_sys_core_mem________uart_uart_fetch_lineReadRp(Recv_sys_core_mem________uart_uart_fetch_lineReadRp),
    .decl_SendEn_sys_core_mem________uart_uart_fetch_fenceIRq(decl_SendEn_sys_core_mem________uart_uart_fetch_fenceIRq),
    .Recv_sys_core_mem________uart_uart_fetch_fenceIAck(Recv_sys_core_mem________uart_uart_fetch_fenceIAck),
    .decl_Send_sys_core_mem________uart_uart_lineReadRq(decl_Send_sys_core_mem________uart_uart_lineReadRq),
    .decl_SendEn_sys_core_mem________uart_uart_lineReadRq(decl_SendEn_sys_core_mem________uart_uart_lineReadRq),
    .Recv_sys_core_mem________uart_uart_lineReadRp(Recv_sys_core_mem________uart_uart_lineReadRp),
    .decl_Send_sys_core_mem________uart_uart_lineWriteRq(decl_Send_sys_core_mem________uart_uart_lineWriteRq),
    .decl_SendEn_sys_core_mem________uart_uart_lineWriteRq(decl_SendEn_sys_core_mem________uart_uart_lineWriteRq),
    .Recv_sys_core_mem________uart_fetch_lineReadRqReady(Recv_sys_core_mem________uart_fetch_lineReadRqReady),
    .Recv_sys_core_mem________uart_fetch_lineReadRpValid(Recv_sys_core_mem________uart_fetch_lineReadRpValid),
    .decl_SendEn_sys_core_mem________uart_fetch_lineReadRpReady(decl_SendEn_sys_core_mem________uart_fetch_lineReadRpReady),
    .Recv_sys_core_mem________uart_lineReadRqReady(Recv_sys_core_mem________uart_lineReadRqReady),
    .Recv_sys_core_mem________uart_lineWriteRqReady(Recv_sys_core_mem________uart_lineWriteRqReady),
    .Recv_sys_core_mem________uart_lineReadRpValid(Recv_sys_core_mem________uart_lineReadRpValid),
    .decl_SendEn_sys_core_mem________uart_lineReadRpReady(decl_SendEn_sys_core_mem________uart_lineReadRpReady),

    .clk_core(clk_core),
    .rst_n_core(rst_n_core)
  );

  // =========================================================================
  // Sequential Port Dispatch via Shared tb_send / tb_recv
  // =========================================================================
  always_ff @(posedge clk_core or negedge rst_n_core) begin
    if (!rst_n_core) begin
      cycleCount <= 64'd0;
      Recv_sys_core_mem___ram_fetch_lineReadRqReady         <= 1'b1;
      Recv_sys_core_mem___ram_fetch_lineReadRpValid         <= 1'b0;
      Recv_sys_core_mem___ram_ram_fetch_lineReadRp          <= '0;
      Recv_sys_core_mem___ram_ram_fetch_fenceIAck           <= 1'b0;
      Recv_sys_core_mem___ram_lineReadRqReady               <= 1'b1;
      Recv_sys_core_mem___ram_lineWriteRqReady              <= 1'b1;
      Recv_sys_core_mem___ram_lineReadRpValid               <= 1'b0;
      Recv_sys_core_mem___ram_ram_lineReadRp                <= '0;

      Recv_sys_core_mem____revTable_fetch_lineReadRqReady   <= 1'b1;
      Recv_sys_core_mem____revTable_fetch_lineReadRpValid   <= 1'b0;
      Recv_sys_core_mem____revTable_revTable_fetch_lineReadRp <= '0;
      Recv_sys_core_mem____revTable_revTable_fetch_fenceIAck  <= 1'b0;
      Recv_sys_core_mem____revTable_lineReadRqReady         <= 1'b1;
      Recv_sys_core_mem____revTable_lineWriteRqReady        <= 1'b1;
      Recv_sys_core_mem____revTable_lineReadRpValid         <= 1'b0;
      Recv_sys_core_mem____revTable_revTable_lineReadRp     <= '0;

      Recv_sys_core_mem_______plic_plic_UartIrq             <= 1'b0;

      Recv_sys_core_mem________uart_fetch_lineReadRqReady   <= 1'b1;
      Recv_sys_core_mem________uart_fetch_lineReadRpValid   <= 1'b0;
      Recv_sys_core_mem________uart_uart_fetch_lineReadRp   <= '0;
      Recv_sys_core_mem________uart_uart_fetch_fenceIAck    <= 1'b0;
      Recv_sys_core_mem________uart_lineReadRqReady         <= 1'b1;
      Recv_sys_core_mem________uart_lineWriteRqReady        <= 1'b1;
      Recv_sys_core_mem________uart_lineReadRpValid         <= 1'b0;
      Recv_sys_core_mem________uart_uart_lineReadRp         <= '0;
    end else begin
      logic fetchRpValid;
      logic dataRpValid;
      logic revTableFetchRpValid;
      logic revTableDataRpValid;
      logic uartFetchRpValid;
      logic uartRpValid;

      if ((cycleCount % 64'd250000) == 64'd0) begin
        $display("[Cycle %0d]", cycleCount);
        $fflush(32'h8000_0001);
      end
      if (cycleCount + 64'd1 >= maxCycles) begin
        $fatal(1, "Simulation timed out at %0d cycles", maxCycles);
      end
      cycleCount <= cycleCount + 64'd1;

      // 1. Process Send ports (RpReady before ReadRq so freed buffer can accept new Rq)
      if (decl_SendEn_sys_core_mem___ram_fetch_lineReadRpReady) begin
        tb_send("decl_Send_sys_core_mem___ram_fetch_lineReadRpReady", '0);
      end
      if (decl_SendEn_sys_core_mem___ram_ram_fetch_lineReadRq &&
          Recv_sys_core_mem___ram_fetch_lineReadRqReady) begin
        tb_send("decl_Send_sys_core_mem___ram_ram_fetch_lineReadRq",
                tb_io_val_t'(decl_Send_sys_core_mem___ram_ram_fetch_lineReadRq));
      end
      if (decl_SendEn_sys_core_mem___ram_lineReadRpReady) begin
        tb_send("decl_Send_sys_core_mem___ram_lineReadRpReady", '0);
      end
      if (decl_SendEn_sys_core_mem___ram_ram_lineReadRq &&
          Recv_sys_core_mem___ram_lineReadRqReady) begin
        tb_send("decl_Send_sys_core_mem___ram_ram_lineReadRq",
                tb_io_val_t'(decl_Send_sys_core_mem___ram_ram_lineReadRq));
      end
      if (decl_SendEn_sys_core_mem___ram_ram_lineWriteRq) begin
        tb_send("decl_Send_sys_core_mem___ram_ram_lineWriteRq",
                tb_io_val_t'(decl_Send_sys_core_mem___ram_ram_lineWriteRq));
      end
      if (decl_SendEn_sys_core_mem___ram_ram_fetch_fenceIRq) begin
        tb_send("decl_Send_sys_core_mem___ram_ram_fetch_fenceIRq", '0);
      end

      if (decl_SendEn_sys_core_mem____revTable_fetch_lineReadRpReady) begin
        tb_send("decl_Send_sys_core_mem____revTable_fetch_lineReadRpReady", '0);
      end
      if (decl_SendEn_sys_core_mem____revTable_revTable_fetch_lineReadRq &&
          Recv_sys_core_mem____revTable_fetch_lineReadRqReady) begin
        tb_send("decl_Send_sys_core_mem____revTable_revTable_fetch_lineReadRq",
                tb_io_val_t'(decl_Send_sys_core_mem____revTable_revTable_fetch_lineReadRq));
      end
      if (decl_SendEn_sys_core_mem____revTable_lineReadRpReady) begin
        tb_send("decl_Send_sys_core_mem____revTable_lineReadRpReady", '0);
      end
      if (decl_SendEn_sys_core_mem____revTable_revTable_lineReadRq &&
          Recv_sys_core_mem____revTable_lineReadRqReady) begin
        tb_send("decl_Send_sys_core_mem____revTable_revTable_lineReadRq",
                tb_io_val_t'(decl_Send_sys_core_mem____revTable_revTable_lineReadRq));
      end
      if (decl_SendEn_sys_core_mem____revTable_revTable_lineWriteRq) begin
        tb_send("decl_Send_sys_core_mem____revTable_revTable_lineWriteRq",
                tb_io_val_t'(decl_Send_sys_core_mem____revTable_revTable_lineWriteRq));
      end
      if (decl_SendEn_sys_core_mem____revTable_revTable_fetch_fenceIRq) begin
        tb_send("decl_Send_sys_core_mem____revTable_revTable_fetch_fenceIRq", '0);
      end

      if (decl_SendEn_sys_core_mem________uart_fetch_lineReadRpReady) begin
        tb_send("decl_Send_sys_core_mem________uart_fetch_lineReadRpReady", '0);
      end
      if (decl_SendEn_sys_core_mem________uart_uart_fetch_lineReadRq &&
          Recv_sys_core_mem________uart_fetch_lineReadRqReady) begin
        tb_send("decl_Send_sys_core_mem________uart_uart_fetch_lineReadRq",
                tb_io_val_t'(decl_Send_sys_core_mem________uart_uart_fetch_lineReadRq));
      end
      if (decl_SendEn_sys_core_mem________uart_lineReadRpReady) begin
        tb_send("decl_Send_sys_core_mem________uart_lineReadRpReady", '0);
      end
      if (decl_SendEn_sys_core_mem________uart_uart_lineReadRq &&
          Recv_sys_core_mem________uart_lineReadRqReady) begin
        tb_send("decl_Send_sys_core_mem________uart_uart_lineReadRq",
                tb_io_val_t'(decl_Send_sys_core_mem________uart_uart_lineReadRq));
      end
      if (decl_SendEn_sys_core_mem________uart_uart_lineWriteRq) begin
        tb_send("decl_Send_sys_core_mem________uart_uart_lineWriteRq",
                tb_io_val_t'(decl_Send_sys_core_mem________uart_uart_lineWriteRq));
      end
      if (decl_SendEn_sys_core_mem________uart_uart_fetch_fenceIRq) begin
        tb_send("decl_Send_sys_core_mem________uart_uart_fetch_fenceIRq", '0);
      end

      // 2. Drive Recv ports for next cycle
      Recv_sys_core_mem___ram_fetch_lineReadRqReady <=
        verilog_bits#(TbIoWidth, 0, 0)::extract(tb_recv("Recv_sys_core_mem___ram_fetch_lineReadRqReady"));
      fetchRpValid =
        verilog_bits#(TbIoWidth, 0, 0)::extract(tb_recv("Recv_sys_core_mem___ram_fetch_lineReadRpValid"));
      Recv_sys_core_mem___ram_fetch_lineReadRpValid <= fetchRpValid;
      if (fetchRpValid) begin
        Recv_sys_core_mem___ram_ram_fetch_lineReadRp <=
          verilog_bits#(TbIoWidth, $bits(ramReadRp_t) - 1, 0)::extract(tb_recv("Recv_sys_core_mem___ram_ram_fetch_lineReadRp"));
      end

      Recv_sys_core_mem___ram_ram_fetch_fenceIAck <=
        verilog_bits#(TbIoWidth, 0, 0)::extract(tb_recv("Recv_sys_core_mem___ram_ram_fetch_fenceIAck"));

      Recv_sys_core_mem___ram_lineReadRqReady <=
        verilog_bits#(TbIoWidth, 0, 0)::extract(tb_recv("Recv_sys_core_mem___ram_lineReadRqReady"));
      Recv_sys_core_mem___ram_lineWriteRqReady <=
        verilog_bits#(TbIoWidth, 0, 0)::extract(tb_recv("Recv_sys_core_mem___ram_lineWriteRqReady"));
      dataRpValid =
        verilog_bits#(TbIoWidth, 0, 0)::extract(tb_recv("Recv_sys_core_mem___ram_lineReadRpValid"));
      Recv_sys_core_mem___ram_lineReadRpValid <= dataRpValid;
      if (dataRpValid) begin
        Recv_sys_core_mem___ram_ram_lineReadRp <=
          verilog_bits#(TbIoWidth, $bits(ramReadRp_t) - 1, 0)::extract(tb_recv("Recv_sys_core_mem___ram_ram_lineReadRp"));
      end

      Recv_sys_core_mem____revTable_fetch_lineReadRqReady <=
        verilog_bits#(TbIoWidth, 0, 0)::extract(tb_recv("Recv_sys_core_mem____revTable_fetch_lineReadRqReady"));
      revTableFetchRpValid =
        verilog_bits#(TbIoWidth, 0, 0)::extract(tb_recv("Recv_sys_core_mem____revTable_fetch_lineReadRpValid"));
      Recv_sys_core_mem____revTable_fetch_lineReadRpValid <= revTableFetchRpValid;
      if (revTableFetchRpValid) begin
        Recv_sys_core_mem____revTable_revTable_fetch_lineReadRp <=
          verilog_bits#(TbIoWidth, $bits(revTableReadRp_t) - 1, 0)::extract(tb_recv("Recv_sys_core_mem____revTable_revTable_fetch_lineReadRp"));
      end

      Recv_sys_core_mem____revTable_revTable_fetch_fenceIAck <=
        verilog_bits#(TbIoWidth, 0, 0)::extract(tb_recv("Recv_sys_core_mem____revTable_revTable_fetch_fenceIAck"));

      Recv_sys_core_mem____revTable_lineReadRqReady <=
        verilog_bits#(TbIoWidth, 0, 0)::extract(tb_recv("Recv_sys_core_mem____revTable_lineReadRqReady"));
      Recv_sys_core_mem____revTable_lineWriteRqReady <=
        verilog_bits#(TbIoWidth, 0, 0)::extract(tb_recv("Recv_sys_core_mem____revTable_lineWriteRqReady"));
      revTableDataRpValid =
        verilog_bits#(TbIoWidth, 0, 0)::extract(tb_recv("Recv_sys_core_mem____revTable_lineReadRpValid"));
      Recv_sys_core_mem____revTable_lineReadRpValid <= revTableDataRpValid;
      if (revTableDataRpValid) begin
        Recv_sys_core_mem____revTable_revTable_lineReadRp <=
          verilog_bits#(TbIoWidth, $bits(revTableReadRp_t) - 1, 0)::extract(tb_recv("Recv_sys_core_mem____revTable_revTable_lineReadRp"));
      end

      Recv_sys_core_mem_______plic_plic_UartIrq <=
        verilog_bits#(TbIoWidth, 0, 0)::extract(tb_recv("Recv_sys_core_mem_______plic_plic_UartIrq"));

      Recv_sys_core_mem________uart_fetch_lineReadRqReady <=
        verilog_bits#(TbIoWidth, 0, 0)::extract(tb_recv("Recv_sys_core_mem________uart_fetch_lineReadRqReady"));
      uartFetchRpValid =
        verilog_bits#(TbIoWidth, 0, 0)::extract(tb_recv("Recv_sys_core_mem________uart_fetch_lineReadRpValid"));
      Recv_sys_core_mem________uart_fetch_lineReadRpValid <= uartFetchRpValid;
      if (uartFetchRpValid) begin
        Recv_sys_core_mem________uart_uart_fetch_lineReadRp <=
          verilog_bits#(TbIoWidth, $bits(uartReadRp_t) - 1, 0)::extract(tb_recv("Recv_sys_core_mem________uart_uart_fetch_lineReadRp"));
      end

      Recv_sys_core_mem________uart_uart_fetch_fenceIAck <=
        verilog_bits#(TbIoWidth, 0, 0)::extract(tb_recv("Recv_sys_core_mem________uart_uart_fetch_fenceIAck"));

      Recv_sys_core_mem________uart_lineReadRqReady <=
        verilog_bits#(TbIoWidth, 0, 0)::extract(tb_recv("Recv_sys_core_mem________uart_lineReadRqReady"));
      Recv_sys_core_mem________uart_lineWriteRqReady <=
        verilog_bits#(TbIoWidth, 0, 0)::extract(tb_recv("Recv_sys_core_mem________uart_lineWriteRqReady"));
      uartRpValid =
        verilog_bits#(TbIoWidth, 0, 0)::extract(tb_recv("Recv_sys_core_mem________uart_lineReadRpValid"));
      Recv_sys_core_mem________uart_lineReadRpValid <= uartRpValid;
      if (uartRpValid) begin
        Recv_sys_core_mem________uart_uart_lineReadRp <=
          verilog_bits#(TbIoWidth, $bits(uartReadRp_t) - 1, 0)::extract(tb_recv("Recv_sys_core_mem________uart_uart_lineReadRp"));
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
