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

Extract Constant IoEnv => "(Data.Vector.Unboxed.Mutable.IOVector Data.Word.Word64, Data.Vector.Unboxed.Mutable.IOVector Prelude.Bool, Prelude.Integer, Data.IORef.IORef (Prelude.Maybe Prelude.Integer), Data.IORef.IORef (Prelude.Maybe Prelude.Integer), Data.IORef.IORef (Prelude.Maybe Prelude.Integer), Data.IORef.IORef Prelude.Bool, Data.IORef.IORef Prelude.Integer, Data.IORef.IORef (Prelude.Maybe Prelude.Integer))".

Extract Constant io_initEnv => "(do
  let numLines = Prelude.div (256 Prelude.* 1024) 8
  ramData <- Data.Vector.Unboxed.Mutable.replicate numLines (0 :: Data.Word.Word64)
  ramTag  <- Data.Vector.Unboxed.Mutable.replicate numLines Prelude.False
  args    <- System.Environment.getArgs
  let findArg pfx = Data.List.find (Data.List.isPrefixOf pfx) args
  case findArg ""+bin="" of
    Prelude.Just arg -> do
      let binFile = Prelude.drop 5 arg
      lns <- Prelude.lines Prelude.<$> Prelude.readFile binFile
      let loadLine (idx, ln) =
            case Numeric.readHex ln of
              (w, _) : _ -> Data.Vector.Unboxed.Mutable.unsafeWrite ramData idx (Prelude.fromIntegral (w :: Prelude.Integer))
              []         -> Prelude.return ()
      Prelude.mapM_ loadLine (Prelude.zip [0 .. numLines Prelude.- 1] lns)
    Prelude.Nothing -> Prelude.return ()
  let tohostAddr =
        case findArg ""+tohost="" of
          Prelude.Just arg ->
            let s0 = Prelude.drop 8 arg
                s1 = if Data.List.isPrefixOf ""0x"" s0 Prelude.|| Data.List.isPrefixOf ""0X"" s0 then Prelude.drop 2 s0 else s0
            in case Numeric.readHex s1 of
                 (w, _) : _ -> w
                 []         -> 0
          Prelude.Nothing -> 0
  ramFetchRqRef <- Data.IORef.newIORef Prelude.Nothing
  ramDataRqRef  <- Data.IORef.newIORef Prelude.Nothing
  extMemRqRef   <- Data.IORef.newIORef Prelude.Nothing
  dlabRef       <- Data.IORef.newIORef Prelude.False
  ieRef         <- Data.IORef.newIORef 0
  rxBufRef      <- Data.IORef.newIORef Prelude.Nothing
  Prelude.return (ramData, ramTag, tohostAddr, ramFetchRqRef, ramDataRqRef, extMemRqRef, dlabRef, ieRef, rxBufRef))".

Extract Constant io_send => "(\(ramData, ramTag, tohostAddr, ramFetchRqRef, ramDataRqRef, extMemRqRef, dlabRef, ieRef, _) name k val ->
  if Data.List.isSuffixOf ""_lineReadRq"" name
  then let addr = unsafeCoerce val :: Prelude.Integer
       in if Data.List.isInfixOf ""_fetch_"" name
          then Data.IORef.writeIORef ramFetchRqRef (Prelude.Just addr)
          else if Data.List.isInfixOf ""_ram_"" name
          then Data.IORef.writeIORef ramDataRqRef (Prelude.Just addr)
          else if Data.List.isInfixOf ""_extMem_"" name
          then Data.IORef.writeIORef extMemRqRef (Prelude.Just addr)
          else Prelude.return ()
  else if Data.List.isSuffixOf ""_lineWriteRq"" name
  then let (addr, (dataVec, (maskVec, (tagVec, (tagMaskVec, _))))) =
             unsafeCoerce val :: (Prelude.Integer, (Data.Vector.Vector Prelude.Integer, (Data.Vector.Vector Prelude.Bool, (Data.Vector.Vector Prelude.Bool, (Data.Vector.Vector Prelude.Bool, ())))))
       in if Data.List.isInfixOf ""_ram_"" name then do
            let idx      = Prelude.fromIntegral (Data.Bits.shiftR (addr Prelude.- 0x80000000) 3)
                numLines = Data.Vector.Unboxed.Mutable.length ramData
            if idx Prelude.>= 0 Prelude.&& idx Prelude.< numLines then do
              oldW <- Data.Vector.Unboxed.Mutable.unsafeRead ramData idx
              let updByte w b =
                    if maskVec Data.Vector.! b
                    then let maskB = Data.Bits.shiftL (0xff :: Data.Word.Word64) (8 Prelude.* b)
                             valB  = Data.Bits.shiftL (Prelude.fromIntegral (dataVec Data.Vector.! b) Data.Bits..&. (0xff :: Data.Word.Word64)) (8 Prelude.* b)
                         in (w Data.Bits..&. Data.Bits.complement maskB) Data.Bits..|. valB
                    else w
                  newW = Data.List.foldl' updByte oldW [0 .. 7]
              Data.Vector.Unboxed.Mutable.unsafeWrite ramData idx newW
              if tagMaskVec Data.Vector.! 0
                then Data.Vector.Unboxed.Mutable.unsafeWrite ramTag idx (tagVec Data.Vector.! 0)
                else Prelude.return ()
              let tohostLine = tohostAddr Data.Bits..&. Data.Bits.complement 7
                  tohostOff  = Prelude.fromIntegral (tohostAddr Data.Bits..&. 7)
              if tohostAddr Prelude./= 0 Prelude.&& addr Prelude.== tohostLine Prelude.&& (maskVec Data.Vector.! tohostOff)
                then let tohostVal = Prelude.toInteger ((Data.Bits.shiftR newW (8 Prelude.* tohostOff)) Data.Bits..&. (0xffffffff :: Data.Word.Word64))
                     in if tohostVal Prelude./= 0
                        then if tohostVal Prelude.== 1
                             then Prelude.putStrLn ""TEST PASSED!"" Prelude.>> System.IO.hFlush System.IO.stdout Prelude.>> System.Exit.exitSuccess
                             else Prelude.putStrLn (""TEST FAILED at test case: "" Prelude.++ Prelude.show tohostVal) Prelude.>> System.IO.hFlush System.IO.stdout Prelude.>> System.Exit.exitFailure
                        else Prelude.return ()
                else Prelude.return ()
            else Prelude.return ()
          else if Data.List.isInfixOf ""_extMem_"" name then
            let b0  = dataVec Data.Vector.! 0
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
          else Prelude.return ()
  else Prelude.return ())".

Extract Constant io_recv => "(\(ramData, ramTag, _, ramFetchRqRef, ramDataRqRef, extMemRqRef, _, ieRef, rxBufRef) name k ->
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
  in if Data.List.isSuffixOf ""_lineReadRqReady"" name Prelude.|| Data.List.isSuffixOf ""_lineWriteRqReady"" name Prelude.|| Data.List.isSuffixOf ""_lineReadRpReady"" name then
       Prelude.return (unsafeCoerce Prelude.True)
     else if Data.List.isSuffixOf ""_lineReadRpValid"" name then do
       let rqRef = if Data.List.isInfixOf ""_fetch_"" name then ramFetchRqRef
                   else if Data.List.isInfixOf ""_ram_"" name then ramDataRqRef
                   else extMemRqRef
       mAddr <- Data.IORef.readIORef rqRef
       case mAddr of
         Prelude.Just _  -> Prelude.return (unsafeCoerce Prelude.True)
         Prelude.Nothing -> Prelude.return (unsafeCoerce Prelude.False)
     else if Data.List.isSuffixOf ""_lineReadRp"" name then
       if Data.List.isInfixOf ""_ram_"" name then do
         let rqRef = if Data.List.isInfixOf ""_fetch_"" name then ramFetchRqRef else ramDataRqRef
         mAddr <- Data.IORef.readIORef rqRef
         Data.IORef.writeIORef rqRef Prelude.Nothing
         let addr     = case mAddr of { Prelude.Just a -> a ; Prelude.Nothing -> 0 }
             idx      = Prelude.fromIntegral (Data.Bits.shiftR (addr Prelude.- 0x80000000) 3)
             numLines = Data.Vector.Unboxed.Mutable.length ramData
         if idx Prelude.>= 0 Prelude.&& idx Prelude.< numLines then do
           w <- Data.Vector.Unboxed.Mutable.unsafeRead ramData idx
           t <- Data.Vector.Unboxed.Mutable.unsafeRead ramTag idx
           let bytes = Data.Vector.generate 8 (\b -> Prelude.toInteger ((Data.Bits.shiftR w (8 Prelude.* b)) Data.Bits..&. 0xff))
               tags  = Data.Vector.singleton t
           Prelude.return (unsafeCoerce (bytes, (tags, ())))
         else
           Prelude.return (unsafeCoerce (Data.Vector.replicate 8 0, (Data.Vector.singleton Prelude.False, ())))
       else do
         mAddr <- Data.IORef.readIORef extMemRqRef
         Data.IORef.writeIORef extMemRqRef Prelude.Nothing
         let addr = case mAddr of { Prelude.Just a -> a ; Prelude.Nothing -> 0 }
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
     else if Data.List.isSuffixOf ""_UartIrq"" name then do
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
