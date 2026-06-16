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

From Stdlib Require Import String List ZArith Bool.
Require Import Guru.Library Guru.Syntax Guru.Notations Guru.Compiler Guru.Extraction.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Local Open Scope Z_scope.
Definition Xlen := 32.
Definition Addr := Bit Xlen.

Definition NumChannels := 4%nat.

Definition PhyAddrSz := 22. (* 2-MB physical memory *)
Definition PseudoAddrSz := 25.  (* AXI address width kindSize *)
Definition LgClutSz := Eval compute in (PseudoAddrSz - PhyAddrSz). (* Log of number of entries in the Clut *)

Definition PhyAddr := Bit PhyAddrSz.
Definition PseudoAddr := Bit PseudoAddrSz.
Definition ClutIdx := Bit LgClutSz.
Definition ClutSz := Eval compute in (Z.shiftl 1 LgClutSz).

Section Clut.
  Variable ty: Kind -> Type.

  Local Open Scope guru.
  Local Open Scope string.

  Definition ClutEntry := STRUCT_TYPE {
                              "top" :: PhyAddr ;
                              "base" :: PhyAddr ;
                              "ReadPerm" :: Bool ;
                              "WritePerm" :: Bool }.

  Definition DmaReq := STRUCT_TYPE {
                           "addr" :: PseudoAddr ;
                           "size" :: PhyAddr ;
                           "isWrite" :: Bool }.

  Goal (kindSize ClutEntry >= LgClutSz).
  Proof.
    cbv.
    discriminate.
  Qed.

  Goal (LgClutSz >= 1).
  Proof.
    cbv.
    discriminate.
  Qed.

  (* Command from Processor to insert or remove *)
  Definition Command := STRUCT_TYPE {
                            "clutEntry" :: ClutEntry ;
                            "isInsert"  :: Bool }.

  Definition ConfigReq := STRUCT_TYPE {
                              "offset"  :: Bit 2;
                              "value"   :: Bit Xlen;
                              "isWrite" :: Bool }.

  Definition LeftOverCommandSize := Eval compute in (kindSize (Option Command) - Xlen).
  Definition RespToProcSize := Eval compute in kindSize (Option (Bit (LgClutSz + 1))).

  Definition clutIfc : Tree Elem :=
    Node "" [
      (* Keeps track if entry is used *)
      Leaf "valids" (EReg {| regKind := Array (Z.to_nat ClutSz) Bool; regInit := Some (getDefault _) |});
      (* Keeps track of outstanding transactions *)
      Leaf "busys" (EReg {| regKind := Array (Z.to_nat ClutSz) Bool; regInit := Some (getDefault _) |});
      (* Command from processor split into two registers *)
      Leaf "procCommand1" (EReg {| regKind := Bit Xlen; regInit := Some (getDefault _) |});
      Leaf "procCommand2" (EReg {| regKind := Bit LeftOverCommandSize; regInit := Some (getDefault _) |});
      (* Response to processor *)
      Leaf "respToProc" (EReg {| regKind := Option (Bit (LgClutSz + 1)); regInit := Some (getDefault _) |});
      (* All the entries *)
      Leaf "entries" (EReg {| regKind := Array (Z.to_nat ClutSz) ClutEntry; regInit := None |});
      (* Response to processor send *)
      Leaf "respToProc_out" (ESend (Bit Xlen));
      (* Response to DMA if it can access the request received for DMA check access *)
      Node "dmaCanAccess" (repeat (Leaf "dmaCanAccess" (ESend Bool)) NumChannels);
      (* Config from processor *)
      Leaf "config" (ERecv (Option ConfigReq));
      (* Return from a read memory transaction to clear busy bit *)
      Leaf "readMemResults" (ERecv (Array NumChannels (Option ClutIdx)));
      (* Request from DMA to check validity of access *)
      Leaf "dmaCheckAccess" (ERecv (Array NumChannels DmaReq))
    ].

  Definition cl := clutIfc.

  Definition dmaCanAccessPath (i: FinType NumChannels) : SendPath clutIfc.
  Proof.
    refine (Build_SendPath clutIfc (inr (inr (inr (inr (inr (inr (inr (inl (FinType_to_sumUnit i))))))))) _).
    destruct i as [inum ilt].
    unfold NumChannels in *.
    repeat (destruct inum; [reflexivity | ]).
    contradiction.
  Defined.

  Lemma dmaCanAccessKind i : Bool = getSendKind (dmaCanAccessPath i).
  Proof.
    destruct i as [inum ilt].
    unfold NumChannels in *.
    repeat (destruct inum; [reflexivity | ]).
    contradiction.
  Qed.

  Definition commandFromProc: Action ty cl (Bit 0) :=
    ( RegRead valids <- ".valids" in cl;
      RegRead busys <- ".busys" in cl;
      RegRead procCommand1 <- ".procCommand1" in cl;
      RegRead procCommand2 <- ".procCommand2" in cl;
      RegRead optResp <- ".respToProc" in cl;
      RegRead entries <- ".entries" in cl;
      Let optCommand : Option Command <- FromBit (Option Command) {< #procCommand2, #procCommand1 >};

      (* Find an empty slot in freeIndex. Highest bit of freeIndex is 1 if no empty slot is found *)
      Let optFreeIndex: Bit (LgClutSz + 1) <- countTrailingZerosArray (Not #valids) (LgClutSz + 1);
      Let freeIndex: ClutIdx <- TruncLsb 1 LgClutSz #optFreeIndex;
      Let freeIndexValid: Bool <- Not (FromBit Bool (TruncMsb 1 LgClutSz #optFreeIndex));

      Let rmIndex: ClutIdx <- TruncLsb (kindSize ClutEntry - LgClutSz) LgClutSz (ToBit ((getData #optCommand)`"clutEntry"));

      LetIf dummy <- If (And [isValid #optCommand; Not (isValid #optResp)]) Then (
          RegWrite ".procCommand1" in cl <- ConstDef;
          LetIf dummy <- If ((getData #optCommand)`"isInsert") Then (
              RegWrite ".respToProc" in cl <- mkSome #optFreeIndex;
              LetIf dummy <- If (#freeIndexValid) Then (
                  RegWrite ".entries" in cl <- #entries@[ #freeIndex <- (getData ##optCommand)`"clutEntry"];
                  RegWrite ".valids" in cl <- #valids@[ #freeIndex <- ConstBool true ];
                  Return ConstDef );
              Return #dummy )
            Else (
              LetIf dummy <- If (Not (#busys@[#rmIndex])) Then (
                  RegWrite ".valids" in cl <- #valids@[ #freeIndex <- ConstBool false ];
                  RegWrite ".respToProc" in cl <- mkSome $1;
                  Return ConstDef )
                Else (
                  RegWrite ".respToProc" in cl <- mkSome $0;
                  Return ConstDef);
              Return #dummy
            );
          Return #dummy );
      Return #dummy).

  (* This is the interface to configure the Clut from the processor, and to read the Clut responses to insert/delete*)
  Definition configFromProc: Action ty cl (Bit 0) :=
    ( RegRead procCommand1 <- ".procCommand1" in cl;
      RegRead procCommand2 <- ".procCommand2" in cl;
      RegRead respToProc <- ".respToProc" in cl;
      Let optCommand : Option Command <- FromBit (Option Command) {< #procCommand2, #procCommand1 >};
      Get config <- ".config" in cl;
      Let configData <- getData #config;
      Let configOffset <- #configData`"offset";
      Let configValue <- #configData`"value";
      LetIf dummy <- If (isValid #config) Then (
          LetIf dummy <- If (#configData`"isWrite") Then (
              LetIf dummy <- If (And [Not (isValid #optCommand); isZero #configOffset]) Then (
                  RegWrite ".procCommand1" in cl <- #configValue;
                  Return ConstDef )
                Else (
                  LetIf dummy <- If (And [Not (isValid #optCommand); Eq #configOffset $1]) Then (
                      RegWrite ".procCommand2"
                      in cl <- TruncLsb (Xlen - LeftOverCommandSize) LeftOverCommandSize #configValue;
                      Return ConstDef)
                    Else (
                      LetIf dummy <- If (isValid #respToProc) Then (
                          RegWrite ".respToProc"
                          in cl <- FromBit (Option (Bit (LgClutSz + 1)))
                               (TruncLsb (Xlen - RespToProcSize) RespToProcSize #configValue);
                          Return ConstDef );
                      Return #dummy);
                  Return #dummy);
              Return #dummy)
            Else (
              Put ".respToProc_out" in cl <- (ITE (isZero #configOffset)
                                           #procCommand1
                                           (ITE (Eq #configOffset $1)
                                               (ZeroExtendTo Xlen (##procCommand2))
                                               (ZeroExtendTo Xlen (ToBit (##respToProc)))));
              Return ConstDef
            );
          Return #dummy);
      Return #dummy).

  Section PerChannel.
    Variable channelIdA: FinType NumChannels.

    Definition dmaCanAccessPathS := dmaCanAccessPath channelIdA.
    Definition dmaCanAccessKindS := dmaCanAccessKind channelIdA.

    (* DMA checks if it can access a particular pseudo-address *)
    (* On read checks, it outputs true only if the there's no pending read transaction for the same entry *)
    Definition dmaCheckAccess: Action ty cl (Bit 0) :=
      ( Get dmaReqs <- ".dmaCheckAccess" in cl;
        Let dmaReq : DmaReq <- ReadArrayConst #dmaReqs channelIdA;
        (* Split the incoming address into Clut index and Physical address *)
        Let clutIdx: ClutIdx <- TruncMsb LgClutSz PhyAddrSz (#dmaReq`"addr");
        Let phyAddr: PhyAddr <- TruncLsb LgClutSz PhyAddrSz (#dmaReq`"addr");
        
        (* Read corresponding Clut Entry using Clut index *)
        RegRead entries <- ".entries" in cl;
        RegRead valids <- ".valids" in cl;
        RegRead busys <- ".busys" in cl;
        Let entry: ClutEntry <- #entries@[#clutIdx];
        Let valid: Bool <- #valids@[#clutIdx];

        (* Check for bounds: base <= addr <= top and perms *)
        Let bounds: Bool <- And [Sle (#entry`"base") #phyAddr; Sle (Add [#phyAddr; (#dmaReq`"size")]) (#entry`"top")];
        Let perms: Bool <- ITE (#dmaReq`"isWrite") (#entry`"WritePerm") (##entry`"ReadPerm");

        Let validAccess <- And [#valid; #bounds; #perms];
        LetIf dummy <- If #validAccess Then (
            (* If it's a read transaction, then it must not be already busy *)
            Send dmaCanAccessPathS (match dmaCanAccessKindS in _ = Y return Expr ty Y with
                                   | eq_refl => Or [#dmaReq`"isWrite"; Not #busys@[#clutIdx]]
                                   end) (
                (* If it's a read transaction, mark as busy *)
                LetIf dummy <- If (Not (#dmaReq`"isWrite")) Then (
                    RegWrite ".busys" in cl <- #busys@[#clutIdx <- ConstBool true];
                    Return ConstDef
                  );
                Return #dummy ));
        Return #dummy ).

    (* When a read from the bus returns, mark entry as not-busy *)
    Definition finishRead: Action ty cl (Bit 0) :=
      ( Get readResults <- ".readMemResults" in cl;
        Let optReadResult : Option ClutIdx <- ReadArrayConst #readResults channelIdA;
        Let readResult: ClutIdx <- getData #optReadResult;
        RegRead valids <- ".valids" in cl;
        RegRead busys <- ".busys" in cl;

        LetIf dummy <- If (And [isValid #optReadResult; #valids@[#readResult]]) Then (
            RegWrite ".busys" in cl <- #busys@[#readResult <- ConstBool false];
            Return ConstDef
          );
        Return #dummy).
  End PerChannel.
End Clut.

Definition clut: Mod clutIfc :=
  fun ty => commandFromProc ty :: configFromProc ty ::
              map (dmaCheckAccess ty) (genFinType NumChannels) ++
              map (finishRead ty) (genFinType NumChannels).

Definition compiledMod := compile clut.

Set Extraction Output Directory "./Clut".
Extraction "Compile" kindSize Z.log2_up compiledMod.
