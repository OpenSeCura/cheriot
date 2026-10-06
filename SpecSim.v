(*
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
 *)

From Stdlib Require Import ZArith.
From Guru Require Import Extraction Simulator.
From Cheriot Require Import SpecInst.

Set Extraction Output Directory ".".

Extract Constant IoEnv => "(Data.IORef.IORef Prelude.Integer, Data.IORef.IORef Prelude.Bool, Data.IORef.IORef Prelude.Integer, Data.IORef.IORef (Prelude.Maybe Prelude.Integer))".

Extract Constant io_initEnv => "(do
  r1 <- Data.IORef.newIORef 0
  r2 <- Data.IORef.newIORef Prelude.False
  r3 <- Data.IORef.newIORef 0
  r4 <- Data.IORef.newIORef Prelude.Nothing
  Prelude.return (r1, r2, r3, r4))".

Extract Constant io_send => "(\(readAddrRef, dlabRef, ieRef, _) name k val ->
  if name Prelude.== ""lineReadRq""
  then Data.IORef.writeIORef readAddrRef (unsafeCoerce val :: Prelude.Integer)
  else if name Prelude.== ""lineWriteRq""
  then let (addr, (dataVec, (maskVec, _))) =
             unsafeCoerce val :: (Prelude.Integer, (Data.Vector.Vector Prelude.Integer, (Data.Vector.Vector Prelude.Bool, ())))
           b0  = dataVec Data.Vector.! 0
           m0  = maskVec Data.Vector.! 0
           b4  = dataVec Data.Vector.! 4
           m4  = maskVec Data.Vector.! 4
           b12 = dataVec Data.Vector.! 12
           m12 = maskVec Data.Vector.! 12
       in if addr Prelude.== 0x10000000 then do
            if m12
              then Data.IORef.writeIORef dlabRef (Data.Bits.testBit b12 7)
              else Prelude.return ()
            dlab <- Data.IORef.readIORef dlabRef
            if m0 Prelude.&& Prelude.not dlab
              then Prelude.putChar (Data.Char.chr (Prelude.fromIntegral (b0 Data.Bits..&. 0xff))) Prelude.>>
                   System.IO.hFlush System.IO.stdout
              else Prelude.return ()
            if m4 Prelude.&& Prelude.not dlab
              then Data.IORef.writeIORef ieRef (b4 Data.Bits..&. 0xff)
              else Prelude.return ()
          else Prelude.return ()
  else Prelude.return ())".

Extract Constant io_recv => "(\(readAddrRef, _, ieRef, rxBufRef) name k ->
  let pollRx = do
        cur <- Data.IORef.readIORef rxBufRef
        case cur of
          Prelude.Just _ -> Prelude.return Prelude.True
          Prelude.Nothing -> do
            rdy <- System.IO.hReady System.IO.stdin
            if rdy then do
              c <- System.IO.getChar
              Data.IORef.writeIORef rxBufRef (Prelude.Just (Prelude.toInteger (Data.Char.ord c Data.Bits..&. 0xff)))
              Prelude.return Prelude.True
            else Prelude.return Prelude.False
  in if name Prelude.== ""lineReadRqReady"" Prelude.|| name Prelude.== ""lineWriteRqReady"" Prelude.|| name Prelude.== ""lineReadRpValid"" Prelude.|| name Prelude.== ""lineReadRpReady"" then
       Prelude.return (unsafeCoerce Prelude.True)
     else if name Prelude.== ""lineReadRp"" then do
       addr <- Data.IORef.readIORef readAddrRef
       bytes <- if addr Prelude.== 0x10000000 then do
                  _ <- pollRx
                  cur <- Data.IORef.readIORef rxBufRef
                  b0 <- case cur of
                    Prelude.Just b -> Data.IORef.writeIORef rxBufRef Prelude.Nothing Prelude.>> Prelude.return b
                    Prelude.Nothing -> Prelude.return 0
                  Prelude.return (Data.Vector.fromList [b0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])
                else if addr Prelude.== 0x10000010 then do
                  hasRx <- pollRx
                  let b4 = if hasRx then 0x21 else 0x20
                  Prelude.return (Data.Vector.fromList [0, 0, 0, 0, b4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])
                else Prelude.return (Data.Vector.replicate 16 0)
       let tags = Data.Vector.replicate 2 Prelude.False
       Prelude.return (unsafeCoerce (bytes, (tags, ())))
     else if name Prelude.== ""UartIrq"" then do
       ie <- Data.IORef.readIORef ieRef
       if Data.Bits.testBit ie 0 then do
         hasRx <- pollRx
         Prelude.return (unsafeCoerce (hasRx Prelude.|| Data.Bits.testBit ie 1))
       else
         Prelude.return (unsafeCoerce (Data.Bits.testBit ie 1))
     else Prelude.return (unsafeCoerce (getDefault k)))".

Extract Constant io_stepCycle => "(\c ->
  if Prelude.rem (c :: Prelude.Integer) 250000 Prelude.== 0
  then Prelude.putStrLn (""[Cycle "" Prelude.++ Prelude.show (c :: Prelude.Integer) Prelude.++ ""]"") Prelude.>>
       System.IO.hFlush System.IO.stdout
  else Prelude.return ())".

Definition main : IO unit := evalModCyclesIO specSysTreeInst (Z.to_nat 50000000) specModInst.
Extraction "Simulate" main.
