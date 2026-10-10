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

  // =========================================================================
  // External RAM Parameters & Storage (256 KB, 64-bit lines, 1 tag bit/line)
  // =========================================================================
  localparam int RamSizeBytes = 256 * 1024;
  localparam int LineBits     = 64;
  localparam int LineBytes    = LineBits / 8;
  localparam int NumLines     = (RamSizeBytes * 8) / LineBits;
  localparam int LineIdxBits  = $clog2(NumLines);

  typedef struct packed {
    logic [7 : 0][7 : 0] data;
    logic [0 : 0]        tag;
  } ramReadRp_t;

  typedef struct packed {
    logic [31 : 0]       addr;
    logic [7 : 0][7 : 0] data;
    logic [7 : 0]        dataMask;
    logic [0 : 0]        tag;
    logic [0 : 0]        tagMask;
  } ramWriteRq_t;

  typedef struct packed {
    logic [15 : 0][7 : 0] data;
    logic [1 : 0]         tag;
  } extMemReadRp_t;

  typedef struct packed {
    logic [31 : 0]        addr;
    logic [15 : 0][7 : 0] data;
    logic [15 : 0]        dataMask;
    logic [1 : 0]         tag;
    logic [1 : 0]         tagMask;
  } extMemWriteRq_t;

  localparam int TbIoWidth = $bits(extMemWriteRq_t);
  typedef logic [TbIoWidth - 1 : 0] tb_io_val_t;

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

  function automatic bit has_substr(string s, string sub);
    int sl = s.len();
    int bl = sub.len();
    for (int i = 0; i <= sl - bl; i++) begin
      if (s.substr(i, i + bl - 1) == sub) return 1'b1;
    end
    return 1'b0;
  endfunction

  function automatic bit has_suffix(string s, string suf);
    int sl = s.len();
    int bl = suf.len();
    if (sl < bl) return 1'b0;
    return (s.substr(sl - bl, sl - 1) == suf);
  endfunction

  function automatic void tb_send(string name, tb_io_val_t val);
    if (has_suffix(name, "_lineReadRq")) begin
      if (has_substr(name, "_fetch_")) begin
        ramFetchReadAddr    = val[31 : 0];
        ramFetchReadRpValid = 1'b1;
      end else if (has_substr(name, "_ram_")) begin
        ramDataReadAddr    = val[31 : 0];
        ramDataReadRpValid = 1'b1;
      end else if (has_substr(name, "_extMem_")) begin
        uartReadAddr    = val[31 : 0];
        uartReadRpValid = 1'b1;
      end
    end else if (has_suffix(name, "_lineWriteRq")) begin
      if (has_substr(name, "_ram_")) begin
        ramWriteRq_t                wr;
        logic [31 : 0]              wrAddr;
        logic [LineIdxBits - 1 : 0] wrIdx;
        logic [31 : 0]              tohostLineAddr;
        logic [2 : 0]               tohostByteOff;
        logic [31 : 0]              tohostVal;

        wr     = val[$bits(ramWriteRq_t) - 1 : 0];
        wrAddr = wr.addr;
        wrIdx  = wrAddr[LineIdxBits + 2 : 3];

        for (int b = 0; b < LineBytes; b++) begin
          if (wr.dataMask[b]) begin
            ramData[wrIdx][b*8 +: 8] = wr.data[b];
          end
        end
        if (wr.tagMask[0]) begin
          ramTag[wrIdx] = wr.tag[0];
        end

        tohostLineAddr = {tohostAddr[31 : 3], 3'b000};
        tohostByteOff  = tohostAddr[2 : 0];
        if ((tohostAddr != 32'h0) &&
            (wrAddr == tohostLineAddr) &&
            wr.dataMask[tohostByteOff]) begin
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
      end else if (has_substr(name, "_extMem_")) begin
        extMemWriteRq_t wr;
        wr = val[$bits(extMemWriteRq_t) - 1 : 0];
        if (wr.addr == 32'h1000_0000) begin
          if (wr.dataMask[12]) begin
            dlab = wr.data[12][7];
          end
          if (wr.dataMask[0] && !dlab) begin
            $write("%c", wr.data[0]);
            $fflush(32'h8000_0001);
          end
          if (wr.dataMask[4] && !dlab) begin
            ie = wr.data[4];
          end
        end
      end
    end
  endfunction

  function automatic tb_io_val_t tb_recv(string name);
    if (has_suffix(name, "_lineReadRqReady") ||
        has_suffix(name, "_lineWriteRqReady") ||
        has_suffix(name, "_lineReadRpReady")) begin
      return tb_io_val_t'(1'b1);
    end else if (has_suffix(name, "_lineReadRpValid")) begin
      if (has_substr(name, "_fetch_")) begin
        return tb_io_val_t'(ramFetchReadRpValid);
      end else if (has_substr(name, "_ram_")) begin
        return tb_io_val_t'(ramDataReadRpValid);
      end else begin
        return tb_io_val_t'(uartReadRpValid);
      end
    end else if (has_suffix(name, "_lineReadRp")) begin
      if (has_substr(name, "_ram_")) begin
        ramReadRp_t                 rp;
        logic [31 : 0]              addr;
        logic [LineIdxBits - 1 : 0] idx;
        if (has_substr(name, "_fetch_")) begin
          addr                = ramFetchReadAddr;
          ramFetchReadRpValid = 1'b0;
        end else begin
          addr               = ramDataReadAddr;
          ramDataReadRpValid = 1'b0;
        end
        idx       = addr[LineIdxBits + 2 : 3];
        rp.data   = ramData[idx];
        rp.tag[0] = ramTag[idx];
        return tb_io_val_t'(rp);
      end else begin
        extMemReadRp_t rp;
        rp              = '0;
        uartReadRpValid = 1'b0;
        if (uartReadAddr == 32'h1000_0000) begin
          rp.data[0] = rxBufValid ? rxBuf : 8'h00;
          if (rxBufValid) begin
            rxBufValid = 1'b0;
          end
        end else if (uartReadAddr == 32'h1000_0010) begin
          rp.data[4] = rxBufValid ? 8'h21 : 8'h20;
        end
        return tb_io_val_t'(rp);
      end
    end else if (has_suffix(name, "_UartIrq")) begin
      return tb_io_val_t'(1'(ie[0] ? (rxBufValid | ie[1]) : ie[1]));
    end else begin
      return '0;
    end
  endfunction

  function automatic void tb_init();
    string binFile;

    for (int i = 0; i < NumLines; i++) begin
      ramData[i] = '0;
      ramTag[i]  = 1'b0;
    end

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

    if ($value$plusargs("bin=%s", binFile)) begin
      $readmemh(binFile, ramData);
    end

    if (!$value$plusargs("tohost=%h", tohostAddr)) begin
      tohostAddr = 32'h0;
    end

    if (!$value$plusargs("cycles=%d", maxCycles)) begin
      maxCycles = 64'd50000000;
    end
  endfunction
