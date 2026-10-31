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
  // External RAM & RevTable Parameters & Storage
  // =========================================================================
  localparam int RamSizeBytes      = 256 * 1024;
  localparam int RevTableSizeBytes = 4 * 1024;
  // The line geometry: LgLineBytes must match LgLineBytes in SpecDefines.v
  localparam int LgLineBytes       = 5;
  localparam int LineBytes         = 1 << LgLineBytes;
  localparam int LineBits          = LineBytes * 8;
  localparam int NumLineTags       = LineBytes / 8;  // one tag per 8-byte capability
  localparam int NumLines          = RamSizeBytes / LineBytes;
  localparam int LineIdxBits       = $clog2(NumLines);
  localparam int RevTableNumLines    = RevTableSizeBytes / LineBytes;
  localparam int RevTableLineIdxBits = $clog2(RevTableNumLines);
  localparam int NumRamWords       = RamSizeBytes / 8;  // the 64-bit words of the +bin hex file

  // Every region uses the global line layout: LineBytes data bytes and one tag per capability
  typedef struct packed {
    logic [LineBytes - 1 : 0][7 : 0] data;
    logic [NumLineTags - 1 : 0]      tag;
  } lineReadRp_t;

  typedef struct packed {
    logic [31 : 0]                   addr;
    logic [LineBytes - 1 : 0][7 : 0] data;
    logic [LineBytes - 1 : 0]        dataMask;
    logic [NumLineTags - 1 : 0]      tag;
    logic [NumLineTags - 1 : 0]      tagMask;
  } lineWriteRq_t;

  typedef lineReadRp_t  ramReadRp_t;
  typedef lineWriteRq_t ramWriteRq_t;
  typedef lineReadRp_t  revTableReadRp_t;
  typedef lineWriteRq_t revTableWriteRq_t;
  typedef lineReadRp_t  uartReadRp_t;
  typedef lineWriteRq_t uartWriteRq_t;

  localparam int TbIoWidth = $bits(uartWriteRq_t);
  typedef logic [TbIoWidth - 1 : 0] tb_io_val_t;

  logic [LineBits - 1 : 0]    ramData      [0 : NumLines - 1];
  logic [NumLineTags - 1 : 0] ramTag       [0 : NumLines - 1];
  logic [LineBits - 1 : 0]    revTableData [0 : RevTableNumLines - 1];
  logic [63 : 0]              ramWords     [0 : NumRamWords - 1];

  // The UART registers, at byte offsets from the UART base; the one at offset `off` is byte
  // `uart_byte(off)` of the line at `uart_line(off)`
  localparam logic [31 : 0] UartBase      = 32'h1000_0000;
  localparam int            UartThrOffset = 'h0;   // THR (write), RBR (read)
  localparam int            UartIerOffset = 'h4;
  localparam int            UartLcrOffset = 'hc;   // DLAB is bit 7
  localparam int            UartLsrOffset = 'h14;

  function automatic logic [31 : 0] uart_line(int off);
    return UartBase + 32'(off & ~(LineBytes - 1));
  endfunction

  function automatic int uart_byte(int off);
    return off & (LineBytes - 1);
  endfunction

  // =========================================================================
  // External RAM, RevTable & UART Emulation State
  // =========================================================================
  logic [31 : 0] ramFetchReadAddr;
  logic          ramFetchReadRpValid;
  logic [31 : 0] ramDataReadAddr;
  logic          ramDataReadRpValid;

  logic [31 : 0] revTableFetchReadAddr;
  logic          revTableFetchReadRpValid;
  logic [31 : 0] revTableDataReadAddr;
  logic          revTableDataReadRpValid;

  logic [31 : 0] uartFetchReadAddr;
  logic          uartFetchReadRpValid;
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
      if (has_substr(name, "_ram_")) begin
        if (has_substr(name, "_fetch_")) begin
          ramFetchReadAddr    = val[31 : 0];
          ramFetchReadRpValid = 1'b1;
        end else begin
          ramDataReadAddr    = val[31 : 0];
          ramDataReadRpValid = 1'b1;
        end
      end else if (has_substr(name, "_revTable_")) begin
        if (has_substr(name, "_fetch_")) begin
          revTableFetchReadAddr    = val[31 : 0];
          revTableFetchReadRpValid = 1'b1;
        end else begin
          revTableDataReadAddr    = val[31 : 0];
          revTableDataReadRpValid = 1'b1;
        end
      end else if (has_substr(name, "_uart_")) begin
        if (has_substr(name, "_fetch_")) begin
          uartFetchReadAddr    = val[31 : 0];
          uartFetchReadRpValid = 1'b1;
        end else begin
          uartReadAddr    = val[31 : 0];
          uartReadRpValid = 1'b1;
        end
      end
    end else if (has_suffix(name, "_lineWriteRq")) begin
      if (has_substr(name, "_ram_")) begin
        ramWriteRq_t                wr;
        logic [31 : 0]              wrAddr;
        logic [LineIdxBits - 1 : 0] wrIdx;
        logic [31 : 0]              tohostLineAddr;
        logic [LgLineBytes - 1 : 0] tohostByteOff;
        logic [31 : 0]              tohostVal;

        wr     = val[$bits(ramWriteRq_t) - 1 : 0];
        wrAddr = wr.addr;
        wrIdx  = wrAddr[LineIdxBits + LgLineBytes - 1 : LgLineBytes];

        for (int b = 0; b < LineBytes; b++) begin
          if (wr.dataMask[b]) begin
            ramData[wrIdx][b*8 +: 8] = wr.data[b];
          end
        end
        for (int t = 0; t < NumLineTags; t++) begin
          if (wr.tagMask[t]) begin
            ramTag[wrIdx][t] = wr.tag[t];
          end
        end

        tohostLineAddr = tohostAddr & ~32'(LineBytes - 1);
        tohostByteOff  = tohostAddr[LgLineBytes - 1 : 0];
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
              $fatal(1, "TEST FAILED at test case: %0d", tohostVal);
            end
          end
        end
      end else if (has_substr(name, "_revTable_")) begin
        revTableWriteRq_t                   wr;
        logic [31 : 0]                      wrAddr;
        logic [RevTableLineIdxBits - 1 : 0] wrIdx;

        wr     = val[$bits(revTableWriteRq_t) - 1 : 0];
        wrAddr = wr.addr;
        wrIdx  = wrAddr[RevTableLineIdxBits + LgLineBytes - 1 : LgLineBytes];

        for (int b = 0; b < LineBytes; b++) begin
          if (wr.dataMask[b]) begin
            revTableData[wrIdx][b*8 +: 8] = wr.data[b];
          end
        end
      end else if (has_substr(name, "_uart_")) begin
        // THR and IER see DLAB before this write's LCR update
        uartWriteRq_t wr;
        wr = val[$bits(uartWriteRq_t) - 1 : 0];
        if (wr.addr == uart_line(UartThrOffset) && wr.dataMask[uart_byte(UartThrOffset)] && !dlab) begin
          $write("%c", wr.data[uart_byte(UartThrOffset)]);
          $fflush(32'h8000_0001);
        end
        if (wr.addr == uart_line(UartIerOffset) && wr.dataMask[uart_byte(UartIerOffset)] && !dlab) begin
          ie = wr.data[uart_byte(UartIerOffset)];
        end
        if (wr.addr == uart_line(UartLcrOffset) && wr.dataMask[uart_byte(UartLcrOffset)]) begin
          dlab = wr.data[uart_byte(UartLcrOffset)][7];
        end
      end
    end else if (has_suffix(name, "_lineReadRpReady")) begin
      if (has_substr(name, "_ram_")) begin
        if (has_substr(name, "_fetch_")) begin
          ramFetchReadRpValid = 1'b0;
        end else begin
          ramDataReadRpValid = 1'b0;
        end
      end else if (has_substr(name, "_revTable_")) begin
        if (has_substr(name, "_fetch_")) begin
          revTableFetchReadRpValid = 1'b0;
        end else begin
          revTableDataReadRpValid = 1'b0;
        end
      end else if (has_substr(name, "_uart_")) begin
        if (has_substr(name, "_fetch_")) begin
          uartFetchReadRpValid = 1'b0;
        end else begin
          uartReadRpValid = 1'b0;
        end
      end
    end
  endfunction

  function automatic tb_io_val_t tb_recv(string name);
    if (has_suffix(name, "_lineReadRqReady") ||
        has_suffix(name, "_lineWriteRqReady") ||
        has_suffix(name, "_lineReadRpReady") ||
        has_suffix(name, "_fenceIAck")) begin
      return tb_io_val_t'(1'b1);
    end else if (has_suffix(name, "_lineReadRpValid")) begin
      if (has_substr(name, "_ram_")) begin
        if (has_substr(name, "_fetch_")) begin
          return tb_io_val_t'(ramFetchReadRpValid);
        end else begin
          return tb_io_val_t'(ramDataReadRpValid);
        end
      end else if (has_substr(name, "_revTable_")) begin
        if (has_substr(name, "_fetch_")) begin
          return tb_io_val_t'(revTableFetchReadRpValid);
        end else begin
          return tb_io_val_t'(revTableDataReadRpValid);
        end
      end else begin
        if (has_substr(name, "_fetch_")) begin
          return tb_io_val_t'(uartFetchReadRpValid);
        end else begin
          return tb_io_val_t'(uartReadRpValid);
        end
      end
    end else if (has_suffix(name, "_lineReadRp")) begin
      if (has_substr(name, "_ram_")) begin
        ramReadRp_t                 rp;
        logic [31 : 0]              addr;
        logic [LineIdxBits - 1 : 0] idx;
        if (has_substr(name, "_fetch_")) begin
          addr = ramFetchReadAddr;
        end else begin
          addr = ramDataReadAddr;
        end
        idx     = addr[LineIdxBits + LgLineBytes - 1 : LgLineBytes];
        rp.data = ramData[idx];
        rp.tag  = ramTag[idx];
        return tb_io_val_t'(rp);
      end else if (has_substr(name, "_revTable_")) begin
        revTableReadRp_t                    rp;
        logic [31 : 0]                      addr;
        logic [RevTableLineIdxBits - 1 : 0] idx;
        if (has_substr(name, "_fetch_")) begin
          addr = revTableFetchReadAddr;
        end else begin
          addr = revTableDataReadAddr;
        end
        idx     = addr[RevTableLineIdxBits + LgLineBytes - 1 : LgLineBytes];
        rp      = '0;
        rp.data = revTableData[idx];
        return tb_io_val_t'(rp);
      end else begin
        uartReadRp_t rp;
        rp = '0;
        // A line read has no byte mask: reading RBR's line pops the RX buffer, after LSR (which
        // may share the line) has sampled it
        if (!has_substr(name, "_fetch_")) begin
          if (uartReadAddr == uart_line(UartLsrOffset)) begin
            rp.data[uart_byte(UartLsrOffset)] = rxBufValid ? 8'h21 : 8'h20;
          end
          if (uartReadAddr == uart_line(UartThrOffset)) begin
            rp.data[uart_byte(UartThrOffset)] = rxBufValid ? rxBuf : 8'h00;
            if (rxBufValid) begin
              rxBufValid = 1'b0;
            end
          end
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
      ramTag[i]  = '0;
    end
    for (int i = 0; i < RevTableNumLines; i++) begin
      revTableData[i] = '0;
    end

    ramFetchReadAddr         = 32'h0;
    ramFetchReadRpValid      = 1'b0;
    ramDataReadAddr          = 32'h0;
    ramDataReadRpValid       = 1'b0;
    revTableFetchReadAddr    = 32'h0;
    revTableFetchReadRpValid = 1'b0;
    revTableDataReadAddr     = 32'h0;
    revTableDataReadRpValid  = 1'b0;
    uartFetchReadAddr        = 32'h0;
    uartFetchReadRpValid     = 1'b0;
    uartReadAddr             = 32'h0;
    uartReadRpValid          = 1'b0;
    dlab                     = 1'b0;
    ie                       = 8'h0;
    rxBufValid               = 1'b0;
    rxBuf                    = 8'h0;

    // The +bin hex file has one little-endian 64-bit word per text line; pack the words into lines
    if ($value$plusargs("bin=%s", binFile)) begin
      for (int i = 0; i < NumRamWords; i++) begin
        ramWords[i] = '0;
      end
      $readmemh(binFile, ramWords);
      for (int i = 0; i < NumRamWords; i++) begin
        ramData[i / (LineBytes / 8)][(i % (LineBytes / 8)) * 64 +: 64] = ramWords[i];
      end
    end

    if (!$value$plusargs("tohost=%h", tohostAddr)) begin
      tohostAddr = 32'h0;
    end

    if (!$value$plusargs("cycles=%d", maxCycles)) begin
      maxCycles = 64'd50000000;
    end
  endfunction
