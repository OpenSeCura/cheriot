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

  `include "TbCommon.sv"

  class tb_io_t extends sim_io_t;
    virtual function void send(string name, sim_io_val_t val);
      tb_send(name, tb_io_val_t'(val));
    endfunction

    virtual function sim_io_val_t recv(string name);
      return sim_io_val_t'(tb_recv(name));
    endfunction
  endclass

  top top_inst (
    .clk_default(clk_core),
    .rst_n_default(rst_n_core)
  );

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

  initial begin
    tb_io_t io;
    io     = new;
    sim_io = io;

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
