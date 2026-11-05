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

From Stdlib Require Import String List ZArith Zmod Lia Bool.
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics Composition Theorems HelperLemmas.
From Cheriot.Proof Require Import TreeLemmas StateRel SimDevices SimFetchDecode SimExecute GhostListLemmas.
From Cheriot.Proof Require Import RefRel RefRegion RefGhost RefFetch FifoGen RefMemRel.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Asymmetric Patterns.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

(* ===========================================================================
 * THE REFINEMENT RELATION: CORE COMPONENTS
 * ===========================================================================
 * `RefRelG g s1 s2` relates an impl state `s1` and a spec state `s2` under ghost
 * state `g`. This file holds the accessors, the ghost state and the components
 * that do not depend on the pipeline's control flow:
 * - the register file chain (executed, not committed instructions);
 * - the memory (RefMemRel.v) and the interrupt latches;
 * - what each pending ghost entry needs to be replayed by the spec. *)

Local Abbreviation TS t := (TreeState ElemState t).

(* --- 1. Tagged-Union and Struct Field Helpers --- *)

Definition msIdle (st : type MemState) : bool := evalExpr ((Var type MemState st) `? "Idle").
Definition msReadRq (st : type MemState) : bool := evalExpr ((Var type MemState st) `? "ReadRq").
Definition msReadRqSent (st : type MemState) : bool := evalExpr ((Var type MemState st) `? "ReadRqSent").
Definition msReadRpReady (st : type MemState) : bool := evalExpr ((Var type MemState st) `? "ReadRpReady").
Definition msWriteRq (st : type MemState) : bool := evalExpr ((Var type MemState st) `? "WriteRq").
Definition msReadRqV (st : type MemState) : type MemStepOp := evalExpr ((Var type MemState st) `! "ReadRq").
Definition msReadRqSentV (st : type MemState) : type MemReadRqSent := evalExpr ((Var type MemState st) `! "ReadRqSent").
Definition msWriteRqV (st : type MemState) : type MemStepOp := evalExpr ((Var type MemState st) `! "WriteRq").

Definition dmLoadRq (st : type DataMemState) : bool := evalExpr ((Var type DataMemState st) `? "LoadRq").
Definition dmLoadRp (st : type DataMemState) : bool := evalExpr ((Var type DataMemState st) `? "LoadRp").
Definition dmRevRq (st : type DataMemState) : bool := evalExpr ((Var type DataMemState st) `? "RevRq").
Definition dmRevRp (st : type DataMemState) : bool := evalExpr ((Var type DataMemState st) `? "RevRp").
Definition dmLoadRpV (st : type DataMemState) : type LoadCmd := evalExpr ((Var type DataMemState st) `! "LoadRp").
Definition dmRevRqV (st : type DataMemState) : type RevCmd := evalExpr ((Var type DataMemState st) `! "RevRq").
Definition dmRevRpV (st : type DataMemState) : type RevCmd := evalExpr ((Var type DataMemState st) `! "RevRp").

Definition isReqDataMem (r : type Requester) : bool := evalExpr ((Var type Requester r) `? "DataMem").
Definition isReqRevoker (r : type Requester) : bool := evalExpr ((Var type Requester r) `? "Revoker").

Definition rpIdle (p : type RevPhase) : bool := evalExpr ((Var type RevPhase p) `? "Idle").
Definition rpWaitCapRp (p : type RevPhase) : bool := evalExpr ((Var type RevPhase p) `? "WaitCapRp").
Definition rpWaitRevBitRq (p : type RevPhase) : bool := evalExpr ((Var type RevPhase p) `? "WaitRevBitRq").
Definition rpWaitRevBitRp (p : type RevPhase) : bool := evalExpr ((Var type RevPhase p) `? "WaitRevBitRp").
Definition rpWriteCap (p : type RevPhase) : bool := evalExpr ((Var type RevPhase p) `? "WriteCap").
Definition rpCheck (p : type RevPhase) : bool :=
  orb (rpWaitRevBitRq p) (orb (rpWaitRevBitRp p) (rpWriteCap p)).

Definition slIsLoad (sl : type SecondLine) : bool := evalExpr ((Var type SecondLine sl) `? "Load").
Definition slIsStore (sl : type SecondLine) : bool := evalExpr ((Var type SecondLine sl) `? "Store").
Definition slLoadV (sl : type SecondLine) : type SecondLineLoad := evalExpr ((Var type SecondLine sl) `! "Load").
Definition slStoreV (sl : type SecondLine) : type SecondLineStore := evalExpr ((Var type SecondLine sl) `! "Store").

Definition prIsRead (p : type PortRq) : bool := evalExpr ((Var type PortRq p) `? "Read").
Definition prIsWrite (p : type PortRq) : bool := evalExpr ((Var type PortRq p) `? "Write").
Definition prReadV (p : type PortRq) : type Addr := evalExpr ((Var type PortRq p) `! "Read").
Definition prWriteV (p : type PortRq) : type LineWriteRq := evalExpr ((Var type PortRq p) `! "Write").

(* Option fields *)
Definition optValid {k : Kind} (o : type (Option k)) : bool := o.(Snd).(Fst).
Definition optData {k : Kind} (o : type (Option k)) : type k := o.(Fst).

(* FetchBufEntry = { pcAddr; predPc; exitParcel; execEpoch; predEpoch; fetchExc } *)
Definition fbPcAddr (e : type FetchBufEntry) : type Addr := e.(Fst).
Definition fbPredPc (e : type FetchBufEntry) : type Addr := e.(Snd).(Fst).
Definition fbExitParcel (e : type FetchBufEntry) : type (Bit LgFetchParcels) := e.(Snd).(Snd).(Fst).
Definition fbExecEpoch (e : type FetchBufEntry) : type Epoch := e.(Snd).(Snd).(Snd).(Fst).
Definition fbPredEpoch (e : type FetchBufEntry) : type Epoch := e.(Snd).(Snd).(Snd).(Snd).(Fst).
Definition fbFetchExc (e : type FetchBufEntry) : type FetchException := e.(Snd).(Snd).(Snd).(Snd).(Snd).(Fst).

(* AssembledInst = { fetchOut; predPc; execEpoch } *)
Definition aiFetchOut (e : type AssembledInst) : type FetchOut := e.(Fst).
Definition aiPredPc (e : type AssembledInst) : type Addr := e.(Snd).(Fst).
Definition aiExecEpoch (e : type AssembledInst) : type Epoch := e.(Snd).(Snd).(Fst).

(* DecodeToAluEntry = { aluIn; predPc; execEpoch } *)
Definition daAluIn (e : type DecodeToAluEntry) : type AluInInstGroup := e.(Fst).
Definition daPredPc (e : type DecodeToAluEntry) : type Addr := e.(Snd).(Fst).
Definition daExecEpoch (e : type DecodeToAluEntry) : type Epoch := e.(Snd).(Snd).(Fst).

(* MemFenceReq = { dstIdx; addr; op } *)
Definition mrDst (q : type MemFenceReq) : bits RegIdxSzReal := q.(Fst).
Definition mrAddr (q : type MemFenceReq) : type Addr := q.(Snd).(Fst).
Definition mrOp (q : type MemFenceReq) : type MemFenceUnion := q.(Snd).(Snd).(Fst).

(* FetchOut = { hasAsr; inst; fetchExc } and FetchException = { tag; seal; perm; bounds } *)
Definition foInst (fo : type FetchOut) : type Inst := fo.(Snd).(Fst).
Definition foExc (fo : type FetchOut) : type FetchException := fo.(Snd).(Snd).(Fst).
Definition excAny (x : type FetchException) : bool :=
  orb x.(Fst) (orb x.(Snd).(Fst) (orb x.(Snd).(Snd).(Fst) x.(Snd).(Snd).(Snd).(Fst))).
Definition foFault (fo : type FetchOut) : bool := excAny (foExc fo).

(* Kinds of memory/fence operations *)
Definition opIsMem (op : type MemFenceUnion) : bool := evalExpr ((Var type MemFenceUnion op) `? "Mem").
Definition opMemPayload (op : type MemFenceUnion) : type MemPayload :=
  evalExpr ((Var type MemFenceUnion op) `! "Mem").
Definition opFenceV (op : type MemFenceUnion) : type FenceOp :=
  evalExpr ((Var type MemFenceUnion op) `! "Fence").
Definition opIsLoad (op : type MemFenceUnion) : bool :=
  andb (opIsMem op)
       (let p := opMemPayload op in evalExpr ((##p`"memOp") `? "Load")).
Definition opIsStore (op : type MemFenceUnion) : bool :=
  andb (opIsMem op)
       (let p := opMemPayload op in evalExpr ((##p`"memOp") `? "Store")).
Definition opIsFenceI (op : type MemFenceUnion) : bool :=
  andb (negb (opIsMem op))
       (let f := opFenceV op in evalExpr (##f`"FenceI")).

(* --- 2. Ghost Description of the Access in Flight in the Impl Memory --- *)

(* Progress of the line being read: `second` tells which line of the access *)
Inductive RdStage :=
| RdPend (second : bool)                          (* `state` = ReadRq *)
| RdStaged (second : bool)                        (* request staged in the region's portRq *)
| RdOut (second : bool)                           (* request accepted, response not arrived *)
| RdArrived (second : bool) (rp : type LineReadRp) (* response in the data response buffer *)
| RdReady (res : type FullCapWithTag).            (* `state` = ReadRpReady, `res` in rpReady *)

(* Progress of the line being written *)
Inductive WrStage :=
| WrPend (second : bool)                          (* `state` = WriteRq *)
| WrStaged (second : bool).                       (* line staged in the region's portRq *)

Inductive Access :=
| AccNone
| AccStore (addr : type Addr) (size : type (Bit LgLgNumBytesFullCapSz)) (pkt : type CapPacket) (st : WrStage)
| AccLoad (ld : type LoadCmd) (pkt0 : type CapPacket) (st : RdStage)
| AccDmRev (rc : type RevCmd) (st : RdStage)
| AccRevCap (st : RdStage)
| AccRevBit (st : RdStage)
| AccRevWrite (addr : type Addr) (pkt : type CapPacket) (st : WrStage).

(* --- 3. The Relation's Parameters --- *)

(* A list with an extra last item, split at an earlier item *)
Lemma chain_snoc_split :
  forall {A : Type} (l G1 G2 : list A) (x y : A),
    (l ++ [x] = G1 ++ y :: G2)%list -> y <> x ->
    exists G2', G2 = (G2' ++ [x])%list /\ l = (G1 ++ y :: G2')%list.
Proof.
  intros A l G1 G2 x y H Hne.
  destruct (rev G2) as [| z R] eqn:Er.
  - apply (f_equal (@rev A)) in Er; rewrite rev_involutive in Er; cbn in Er; subst G2.
    apply (f_equal (@rev A)) in H; rewrite !rev_app_distr in H; cbn [rev app] in H.
    injection H as E _; exfalso; exact (Hne (eq_sym E)).
  - apply (f_equal (@rev A)) in Er; rewrite rev_involutive in Er; cbn [rev] in Er; subst G2.
    rewrite app_comm_cons, app_assoc in H.
    apply app_inj_tail in H as [H1 H2]; subst z.
    exists (rev R); split; [reflexivity | rewrite H1; reflexivity].
Qed.

Section CoreRel.
  Variable pcAddrInit : Z.
  Variable fetchCapacity instCapacity decodeCapacity dataMemCapacity : nat.
  Variable mulCapacity divCapacity mulStages divStages : nat.
  Variable mulDivMode : MulDivMode.
  Variable bp : WithInstPredIfc.
  Variable config : RevConfig.
  Variables pre post : list MemRegion.
  Variable revBase : Z.
  Variable revPfB : Is_true ((0 <=? revBase) && (revBase + RevokerSizeBytes <=? Z.shiftl 1 AddrSz))%Z.
  Variable revPfA : Is_true (revBase mod (2 ^ LgLineBytes) =? 0)%Z.

  Local Abbreviation specRegions := (specRegionsOf pre post revBase revPfB revPfA).
  Local Abbreviation implRegions := (implRegionsOf pre post revBase revPfB revPfA).

  Variable clintS : @ClintInstance specRegions.
  Variable clint : @ClintInstance implRegions.
  Variable plicS : @PlicInstance (S (S (length (collectIrqActions specRegions)))) specRegions.
  Variable plic : @PlicInstance (S (S (length (collectIrqActions implRegions)))) implRegions.
  Variable initLine : forall r : MemRegion, bits AddrSz -> type LineReadRp.
  Variable fwcs : nat -> nat -> nat.

  Local Abbreviation IState :=
    (ImplState pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
               mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions).
  Local Abbreviation SState := (SpecState pcAddrInit specRegions).
  Local Abbreviation RfSt := (RfState pcAddrInit).
  Local Abbreviation GEntryT := (GEntry).
  Local Abbreviation GItemT := (GItem).

  (* --- 3. Accessors --- *)

  Definition iRf (s1 : IState) : RfSt :=
    impl_rf pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
            mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions s1.
  Definition iFlush (s1 : IState) : RfSt :=
    flushMulDiv pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions s1.
  Definition iWb (s1 : IState) :=
    impl_waitBits pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                  mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions s1.
  Definition iMem (s1 : IState) :=
    impl_mem pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
             mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions s1.
  Definition iFetch (s1 : IState) :=
    impl_fetch pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
               mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions s1.
  Definition iDecode (s1 : IState) :=
    impl_decode pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions s1.
  Definition iExec (s1 : IState) :=
    impl_execute pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                 mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions s1.
  Definition iDm (s1 : IState) :=
    impl_dataMem pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                 mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions s1.

  Definition iRegions (s1 : IState) : TS (implRegionsTree implRegions) := (iMem s1).(Fst).
  Definition iMemSt (s1 : IState) : type MemState := (iMem s1).(Snd).(Fst).
  Definition iRequester (s1 : IState) : type Requester := (iMem s1).(Snd).(Snd).(Fst).
  Definition iReadRp (s1 : IState) : type (Option LineReadRp) := (iMem s1).(Snd).(Snd).(Snd).(Fst).
  Definition iRpReady (s1 : IState) : type (Option FullCapWithTag) := (iMem s1).(Snd).(Snd).(Snd).(Snd).(Fst).
  (* the two read buffers: `readRp` and `rpReady` *)
  Definition iRdBufs (s1 : IState) := (iMem s1).(Snd).(Snd).(Snd).

  Definition iFetchPc (s1 : IState) : type Addr :=
    fetch_pc pcAddrInit fetchCapacity instCapacity (iFetch s1).
  Definition iPredEpoch (s1 : IState) : type Epoch :=
    fetch_predEpoch pcAddrInit fetchCapacity instCapacity (iFetch s1).
  Definition iCurParcel (s1 : IState) : type (Option (Bit LgFetchParcels)) :=
    fetch_curParcelOpt pcAddrInit fetchCapacity instCapacity (iFetch s1).
  Definition iStraddle (s1 : IState) : type (Option StraddleHalf) :=
    fetch_straddleOpt pcAddrInit fetchCapacity instCapacity (iFetch s1).
  Definition iFetchBuf (s1 : IState) : list (type FetchBufEntry) :=
    fifo_to_list (fetch_fetchBufFifo pcAddrInit fetchCapacity instCapacity (iFetch s1)).
  Definition iInstBuf (s1 : IState) : list (type AssembledInst) :=
    fifo_to_list (fetch_instFifo pcAddrInit fetchCapacity instCapacity (iFetch s1)).
  Definition iD2a (s1 : IState) : list (type DecodeToAluEntry) :=
    fifo_to_list (decode_toAluFifo decodeCapacity (iDecode s1)).
  Definition iExecEpoch (s1 : IState) : type Epoch := exec_epoch (iExec s1).
  Definition iFenceIPending (s1 : IState) : bool := exec_fenceIPending (iExec s1).
  Definition iDmBuf (s1 : IState) : list (type MemFenceReq) :=
    fifo_to_list (dataMem_fifo dataMemCapacity (iDm s1)).
  Definition iDmSt (s1 : IState) : type DataMemState := dataMem_state dataMemCapacity (iDm s1).
  Definition iPcc (s1 : IState) : type FullECapWithTag := readPcc pcAddrInit (iRf s1).

  Definition sRf (s2 : SState) : RfSt := spec_rf pcAddrInit specRegions s2.
  Definition sMem (s2 : SState) : TS (specMemTree specRegions) := spec_mem pcAddrInit specRegions s2.
  Definition sSecond (s2 : SState) : type (Option SecondLine) :=
    (spec_core pcAddrInit specRegions s2).(Snd).(Snd).(Fst).

  (* Devices *)
  Definition sClint (s2 : SState) := specClintState pre post revBase revPfB revPfA clintS (sMem s2).
  Definition iClint (s1 : IState) := implClintState pre post revBase revPfB revPfA clint (iRegions s1).
  Definition sPlic (s2 : SState) := specPlicState pre post revBase revPfB revPfA plicS (sMem s2).
  Definition iPlic (s1 : IState) := implPlicState pre post revBase revPfB revPfA plic (iRegions s1).
  Definition sRev (s2 : SState) := specRevState pre post revBase revPfB revPfA (sMem s2).
  Definition iRev (s1 : IState) := implRevState pre post revBase revPfB revPfA (iRegions s1).

  (* Impl revoker: [ base; top; control; epoch; intStatus; intReq; scanAddr; sweepTop; revPhase;
   * revScanCap; revScanBase; revStoreSnoopHit ] *)
  Definition iRevPhase (s1 : IState) : type RevPhase :=
    (iRev s1).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst).
  Definition iRevScanCap (s1 : IState) : type FullCapWithTag :=
    (iRev s1).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst).
  Definition iRevScanBase (s1 : IState) : type (Bit (AddrSz + 1)) :=
    (iRev s1).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst).
  Definition iRevSnoopHit (s1 : IState) : bool :=
    (iRev s1).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst).

  (* --- 4. Ghost State --- *)

  (* A committed load whose value the impl has not written back yet *)
  Definition cnwbApply (c : option (bits RegIdxSzReal * type FullECapWithTag)) (rf : RfSt) : RfSt :=
    match c with
    | Some (d, v) => writeGprVal pcAddrInit d v rf
    | None => rf
    end.

  Record Ghost := mkGhost {
    (* executed, not committed instructions and the mcycle ticks between them *)
    g_chain  : list GItemT ;
    (* the spec register file without the committed, not written back load *)
    g_rf0    : RfSt ;
    g_cnwb   : option (bits RegIdxSzReal * type FullECapWithTag) ;
    (* the impl revoker's scanAddr against the spec's (`RevRel`) *)
    g_revOff : RevOff ;
    (* the fetch outputs of the decode-to-ALU entries (oldest first) *)
    g_d2aFo  : list (type FetchOut) ;
    (* the access in flight in the impl memory *)
    g_acc    : Access
  }.

  (* --- 5. Register File Chain --- *)

  Definition entryReq (e : GEntryT) : option (type MemFenceReq) :=
    if optValid (ge_dm e)
    then Some (aluDstIdx (ge_aluOut e) ,,
               ((aluDstVal (ge_aluOut e)).(Snd).(Snd).(Fst) ,,
                (optData (ge_dm e) ,, tt)))
    else None.

  Definition entryIsLoad (e : GEntryT) : bool :=
    match entryReq e with Some q => opIsLoad (mrOp q) | None => false end.

  (* Every instruction after a load avoids the load's destination register *)
  Definition LoadsAvoided (G : list GItemT) : Prop :=
    forall G1 e G2, G = (G1 ++ GInst e :: G2)%list ->
      entryIsLoad e = true ->
      ChainAvoids G2 (aluDstIdx (ge_aluOut e)).

  Definition RfRel (g : Ghost) (s1 : IState) (s2 : SState) : Prop :=
    sRf s2 = cnwbApply (g_cnwb g) (g_rf0 g) /\
    GChain pcAddrInit (g_rf0 g) (g_chain g) (iFlush s1) /\
    (forall d v, g_cnwb g = Some (d, v) -> ChainAvoids (g_chain g) d) /\
    LoadsAvoided (g_chain g).

  (* --- 6. Memory and Interrupt Latches --- *)

  Definition MemRelC (g : Ghost) (s1 : IState) (s2 : SState) : Prop :=
    MemRel pre post revBase revPfB revPfA clintS clint plicS plic (g_revOff g) (sMem s2) (iRegions s1) /\
    DevInv pre post revBase revPfB revPfA clint plic (iRegions s1) /\
    SnapshotOK fwcs specRegions (sMem s2).

  (* While entries are pending, the spec's latches do not exceed any entry's *)
  Definition LatchRel (g : Ghost) (s2 : SState) : Prop :=
    forall e, In (GInst e) (g_chain g) ->
      (clintSampled (sClint s2) = true -> ge_mtip e = true) /\
      (plicMeipOf (sPlic s2) = true -> ge_meip e = true).

  (* --- 7. Replay Facts of Pending Entries --- *)

  (* The spec can fetch each pending instruction at its chain PCC *)
  Definition ReplayRel (g : Ghost) (s2 : SState) : Prop :=
    forall G1 e G2 rfe,
      g_chain g = (G1 ++ GInst e :: G2)%list ->
      GChain pcAddrInit (g_rf0 g) G1 rfe ->
      FetchAllowedInst initLine fwcs specRegions (sMem s2) (readPcc pcAddrInit rfe)
        (ge_fetchOut e).

  (* --- 8. Ports of the Impl Regions --- *)

  Definition extPortRq (r : MemRegion) (y : TS (implExternalMemRegionTree r)) : type (Option PortRq) :=
    y.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst).

  (* all data reads accepted by the region have been answered / all but one *)
  Definition extDataQuiet (r : MemRegion) (y : TS (implExternalMemRegionTree r)) : Prop :=
    length (implDataAccRqs r y) = length y.(Fst).(Snd).(Snd).(Fst).
  Definition extDataOut (r : MemRegion) (y : TS (implExternalMemRegionTree r)) : Prop :=
    length (implDataAccRqs r y) = S (length y.(Fst).(Snd).(Snd).(Fst)).

  Definition RegionPort (P : forall r, TS (implExternalMemRegionTree r) -> Prop) (r : MemRegion)
    : TS (implMemRegionTree r) -> Prop :=
    match r.(regionKind) as k return TS (implMemRegionKindTree r k) -> Prop with
    | ExternalMem => fun y => P r y
    | CustomMem _ _ _ _ => fun _ => True
    end.

  Fixpoint AllPorts (P : forall r, TS (implExternalMemRegionTree r) -> Prop) (l : list MemRegion)
    : TS (implRegionsTree l) -> Prop :=
    match l as l0 return TS (implRegionsTree l0) -> Prop with
    | [] => fun _ => True
    | r :: l' => fun mi => RegionPort P r mi.(Fst) /\ AllPorts P l' mi.(Snd).(Fst)
    end.

  Definition isRegionAddrB (r : MemRegion) (L : type Addr) : bool := evalExpr (isRegionAddr r (Var type Addr L)).

  (* Some true: ExternalMem; Some false: CustomMem; None: unmapped *)
  Fixpoint lineKind (l : list MemRegion) (L : type Addr) : option bool :=
    match l with
    | [] => None
    | r :: l' =>
        if isRegionAddrB r L
        then Some (match r.(regionKind) with ExternalMem => true | CustomMem _ _ _ _ => false end)
        else lineKind l' L
    end.

  Definition someRead (L : type Addr) : type (Option PortRq) :=
    evalExpr (mkSome (UNION (PortRqList, "Read" ::= Var type Addr L))).
  Definition someWrite (w : type LineWriteRq) : type (Option PortRq) :=
    evalExpr (mkSome (UNION (PortRqList, "Write" ::= Var type LineWriteRq w))).

  (* no staged request and every data read answered *)
  Definition PortsQuiet (s1 : IState) : Prop :=
    AllPorts (fun r y => optValid (extPortRq r y) = false /\ extDataQuiet r y) implRegions (iRegions s1).

  Definition PortsReadStaged (L : type Addr) (s1 : IState) : Prop :=
    AllPorts (fun r y => extDataQuiet r y /\
                (if isRegionAddrB r L then extPortRq r y = someRead L else optValid (extPortRq r y) = false))
      implRegions (iRegions s1).

  (* the read of line `L` accepted by its region and not answered yet: the region's newest accepted
   * read is `L` *)
  Definition PortsReadOut (L : type Addr) (s1 : IState) : Prop :=
    AllPorts (fun r y => optValid (extPortRq r y) = false /\
                (if isRegionAddrB r L then extDataOut r y /\ hd Zmod.zero (implDataAccRqs r y) = L
                 else extDataQuiet r y))
      implRegions (iRegions s1).

  (* the write `rq` of line `L` staged in that region's portRq *)
  Definition PortsWriteStaged (L : type Addr) (rq : type LineWriteRq) (s1 : IState) : Prop :=
    AllPorts (fun r y => extDataQuiet r y /\
                (if isRegionAddrB r L then extPortRq r y = someWrite rq
                 else optValid (extPortRq r y) = false))
      implRegions (iRegions s1).

  Definition NoFenceIWait (s1 : IState) : Prop :=
    AllPorts (fun r y => y.(Fst).(Fst).(Snd).(Snd).(Fst) = false) implRegions (iRegions s1).

  (* --- 9. The Access in Flight --- *)

  (* Whether the stage is that of the second line of an access *)
  Definition rdSecond (st : RdStage) : bool :=
    match st with RdPend b | RdStaged b | RdOut b | RdArrived b _ => b | RdReady _ => false end.
  Definition wrSecond (st : WrStage) : bool :=
    match st with WrPend b | WrStaged b => b end.

  Definition capSz : type (Bit LgLgNumBytesFullCapSz) := evalExpr ($LgNumBytesFullCapSz : Expr type (Bit LgLgNumBytesFullCapSz)).
  Definition byteSz : type (Bit LgLgNumBytesFullCapSz) := Zmod.zero.

  Definition stepOf (second : bool) (addr : type Addr) (size : type (Bit LgLgNumBytesFullCapSz))
    (pkt : type CapPacket) : type MemStepOp :=
    (second ,, ((addr ,, (size ,, (pkt ,, tt))) ,, tt)).

  Definition crossesB (addr : type Addr) (size : type (Bit LgLgNumBytesFullCapSz)) : bool :=
    evalExpr (memCrossesLine (Var type Addr addr) (Var type (Bit LgLgNumBytesFullCapSz) size)).

  Definition lineOf (second : bool) (addr : type Addr) : type Addr :=
    if second then evalExpr (memNextLineAddr (Var type Addr addr)) else evalExpr (memLineAddr (Var type Addr addr)).

  Definition buildW (second : bool) (addr : type Addr) (pkt : type CapPacket)
    (size : type (Bit LgLgNumBytesFullCapSz)) : type LineWriteRq :=
    evalLetExpr (memBuildLineWriteRq (Const type Bool second) (Var type Addr addr) (Var type CapPacket pkt)
                   (Var type (Bit LgLgNumBytesFullCapSz) size)).

  Definition disassembleW (addr : type Addr) (stVal : type FullCapWithTag)
    (size : type (Bit LgLgNumBytesFullCapSz)) : type CapPacket :=
    evalLetExpr (memDisassembleCapWrite (Var type Addr addr) (Var type FullCapWithTag stVal)
                   (Var type (Bit LgLgNumBytesFullCapSz) size)).

  (* The impl memory while line `second` of a read of `size` bytes at `addr` progresses *)
  Definition RdStageRel (addr : type Addr) (size : type (Bit LgLgNumBytesFullCapSz)) (pkt0 : type CapPacket)
    (st : RdStage) (s1 : IState) : Prop :=
    let sent (b : bool) := msReadRqSent (iMemSt s1) = true /\
                            msReadRqSentV (iMemSt s1) = (crossesB addr size ,, (stepOf b addr size pkt0 ,, tt)) in
    match st with
    | RdPend b =>
        msReadRq (iMemSt s1) = true /\ msReadRqV (iMemSt s1) = stepOf b addr size pkt0 /\
        optValid (iReadRp s1) = false /\ optValid (iRpReady s1) = false /\ PortsQuiet s1
    | RdStaged b =>
        sent b /\ optValid (iReadRp s1) = false /\ optValid (iRpReady s1) = false /\
        lineKind implRegions (lineOf b addr) = Some true /\ PortsReadStaged (lineOf b addr) s1
    | RdOut b =>
        sent b /\ optValid (iReadRp s1) = false /\ optValid (iRpReady s1) = false /\
        lineKind implRegions (lineOf b addr) = Some true /\ PortsReadOut (lineOf b addr) s1
    | RdArrived b rp =>
        sent b /\ iReadRp s1 = (rp ,, (true ,, tt)) /\ optValid (iRpReady s1) = false /\ PortsQuiet s1
    | RdReady res =>
        msReadRpReady (iMemSt s1) = true /\ iRpReady s1 = (res ,, (true ,, tt)) /\
        optValid (iReadRp s1) = false /\ PortsQuiet s1
    end.

  (* The impl memory while line `second` of a write of `size` bytes at `addr` progresses *)
  Definition WrStageRel (addr : type Addr) (size : type (Bit LgLgNumBytesFullCapSz)) (pkt : type CapPacket)
    (st : WrStage) (s1 : IState) : Prop :=
    optValid (iReadRp s1) = false /\ optValid (iRpReady s1) = false /\
    match st with
    | WrPend b =>
        msWriteRq (iMemSt s1) = true /\ msWriteRqV (iMemSt s1) = stepOf b addr size pkt /\ PortsQuiet s1
    | WrStaged b =>
        (if andb (negb b) (crossesB addr size)
         then msWriteRq (iMemSt s1) = true /\ msWriteRqV (iMemSt s1) = stepOf true addr size pkt
         else msIdle (iMemSt s1) = true) /\
        lineKind implRegions (lineOf b addr) = Some true /\
        PortsWriteStaged (lineOf b addr) (buildW b addr pkt size) s1
    end.

  (* Content of line `L` of the spec memory as a data read returns it (ExternalMem lines) *)
  Definition RegionLineContent (r : MemRegion) : TS (memRegionTree r) -> type Addr -> type LineReadRp :=
    match r.(regionKind) as k return TS (memRegionKindTree r k) -> type Addr -> type LineReadRp with
    | ExternalMem => fun x L =>
        evalLineWriteRqTrace (initLine r) x.(Snd).(Snd).(Snd).(Fst) L
    | CustomMem _ _ _ _ => fun _ _ => getDefault LineReadRp
    end.

  Fixpoint lineContent (l : list MemRegion) : TS (specMemTree l) -> type Addr -> type LineReadRp :=
    match l as l0 return TS (specMemTree l0) -> type Addr -> type LineReadRp with
    | [] => fun _ _ => getDefault LineReadRp
    | r :: l' => fun m L =>
        if isRegionAddrB r L then RegionLineContent r m.(Fst) L else lineContent l' m.(Snd).(Fst) L
    end.

  (* A single-line read of `size` bytes at `addr` from spec memory `m` *)
  Definition memValAt (m : TS (specMemTree specRegions)) (addr : type Addr)
    (size : type (Bit LgLgNumBytesFullCapSz)) : type FullCapWithTag :=
    evalLetExpr (memAssembleCapRead (Var type Addr addr) (Var type (Bit LgLgNumBytesFullCapSz) size)
                   (Var type CapPacket (specPkt addr (lineContent specRegions m (lineOf false addr))))).

  Definition revByteAddrOf (base : type (Bit (AddrSz + 1))) : type Addr :=
    let lookup := evalLetExpr (@computeRevBitAddr config type base) in
    evalExpr (##lookup`"revByteAddr").

  (* What `readRevBit` returns on spec memory `m` *)
  Definition revBitOf (m : TS (specMemTree specRegions)) (base : type (Bit (AddrSz + 1))) : bool :=
    let lookup := evalLetExpr (@computeRevBitAddr config type base) in
    let v := memValAt m (revByteAddrOf base) byteSz in
    evalExpr (extractRevBit lookup (TruncLsb (AddrSz - 8) 8 (##v`"addr"))).

  (* The register write of a completed load (`specCompleteLoad`) on spec memory `m` *)
  Definition specLoadWb (m : TS (specMemTree specRegions)) (pending : type PendingLoad)
    (memVal : type FullCapWithTag) : bits RegIdxSzReal * type FullECapWithTag :=
    let outcome := evalLetExpr (dispatchLoadResponse config pending memVal) in
    if evalExpr ((Var type LoadOutcome outcome) `? "RevLookup")
    then
      let revInfo : type RevCmd := evalExpr ((Var type LoadOutcome outcome) `! "RevLookup") in
      let pr : type PendingRev := evalExpr (##revInfo`"pendingRev") in
      let wb := evalLetExpr (dispatchRevResponse pr (revBitOf m (evalExpr (##revInfo`"base")))) in
      (evalExpr (##wb`"dstIdx"), evalExpr (##wb`"dstVal"))
    else
      let wb : type WbCmd := evalExpr ((Var type LoadOutcome outcome) `! "Writeback") in
      (evalExpr (##wb`"dstIdx"), evalExpr (##wb`"dstVal")).

  Definition revWb (m : TS (specMemTree specRegions)) (rc : type RevCmd) : bits RegIdxSzReal * type FullECapWithTag :=
    let pr : type PendingRev := evalExpr (##rc`"pendingRev") in
    let wb := evalLetExpr (dispatchRevResponse pr (revBitOf m (evalExpr (##rc`"base")))) in
    (evalExpr (##wb`"dstIdx"), evalExpr (##wb`"dstVal")).

  (* The load command dataMem builds for a request *)
  Definition loadCmdOf (q : type MemFenceReq) : type LoadCmd :=
    let mf := evalLetExpr (dispatchMemFence (mrDst q) (mrAddr q) (mrOp q)) in
    let ma : type MemAction := evalExpr ((Var type MemFenceAction mf) `! "Mem") in
    evalExpr ((Var type MemAction ma) `! "Load").
  Definition storeCmdOf (q : type MemFenceReq) : type StoreCmd :=
    let mf := evalLetExpr (dispatchMemFence (mrDst q) (mrAddr q) (mrOp q)) in
    let ma : type MemAction := evalExpr ((Var type MemFenceAction mf) `! "Mem") in
    evalExpr ((Var type MemAction ma) `! "Store").

  Definition ldAddr (ld : type LoadCmd) : type Addr := ld.(Fst).
  Definition ldPending (ld : type LoadCmd) : type PendingLoad := ld.(Snd).(Fst).
  Definition plSize (pl : type PendingLoad) : type (Bit LgLgNumBytesFullCapSz) := pl.(Snd).(Fst).
  Definition stAddrOf (st : type StoreCmd) : type Addr := st.(Fst).
  Definition stValOf (st : type StoreCmd) : type FullCapWithTag := st.(Snd).(Fst).
  Definition stSizeOf (st : type StoreCmd) : type (Bit LgLgNumBytesFullCapSz) := st.(Snd).(Snd).(Fst).
  Definition rcBase (rc : type RevCmd) : type (Bit (AddrSz + 1)) := rc.(Fst).

  (* The head of the chain is the uncommitted entry of request `q` *)
  Definition HeadReq (g : Ghost) (q : type MemFenceReq) : Prop :=
    exists e G', g_chain g = GInst e :: G' /\ entryReq e = Some q.

  (* The spec's record of the second line of a crossing store: its whole write request *)
  Definition secondStoreOf (addr : type Addr) (pkt : type CapPacket) (size : type (Bit LgLgNumBytesFullCapSz))
    : type (Option SecondLine) :=
    let rq1 := buildW true addr pkt size in
    let sl : type SecondLineStore :=
      (rq1.(Fst) ,, (rq1.(Snd).(Fst) ,, (rq1.(Snd).(Snd).(Fst) ,, (rq1.(Snd).(Snd).(Snd).(Fst) ,,
       (rq1.(Snd).(Snd).(Snd).(Snd).(Fst) ,, tt))))) in
    evalExpr (mkSome (UNION (SecondLineType, "Store" ::= Var type SecondLineStore sl))).

  (* The spec's record of a crossing load after its first line: the first line's packet *)
  Definition secondLoadOf (ld : type LoadCmd) (pkt0 : type CapPacket) : type (Option SecondLine) :=
    let sl : type SecondLineLoad := (ldAddr ld ,, (ldPending ld ,, (pkt0 ,, tt))) in
    evalExpr (mkSome (UNION (SecondLineType, "Load" ::= Var type SecondLineLoad sl))).

  Definition revNotReading (s1 : IState) : Prop :=
    rpWaitCapRp (iRevPhase s1) = false /\ rpWaitRevBitRp (iRevPhase s1) = false.

  Definition dmNotAccessing (s1 : IState) : Prop :=
    dmLoadRp (iDmSt s1) = false /\ dmRevRp (iDmSt s1) = false.

  (* The scan position of the impl revoker (a capability slot index) *)
  Definition iScanMsb (s1 : IState) : bits TagAddrWidth :=
    revScanAddr (projImplRevokerArchState (iRev s1)).

  (* The store snoop (`implRevokerSnoopStore`): a store of `2^memSize` bytes at `addr` touches the
   * capability slot `scanAddrMsb` (its own slot, or the next one when it spills into it) *)
  Definition snoopHitsB (addr : type Addr) (memSize : type (Bit LgLgNumBytesFullCapSz))
    (scanAddrMsb : bits TagAddrWidth) : bool :=
    let stAddrMsb : type (Bit TagAddrWidth) :=
      evalExpr (TruncMsb TagAddrWidth LgNumBytesFullCapSz (Var type Addr addr)) in
    let capOffset : type (Bit LgNumBytesFullCapSz) :=
      evalExpr (TruncLsb TagAddrWidth LgNumBytesFullCapSz (Var type Addr addr)) in
    let numBytesDXlen : type (Bit (LgNumBytesFullCapSz + 1)) :=
      evalExpr (Sll ($1 : Expr type (Bit (LgNumBytesFullCapSz + 1)))
                    (ZeroExtend (LgNumBytesFullCapSz + 1 - LgLgNumBytesFullCapSz)
                                (Var type (Bit LgLgNumBytesFullCapSz) memSize))) in
    let endOffsetDXlen : type (Bit (LgNumBytesFullCapSz + 1)) :=
      evalExpr (Add [ ZeroExtend 1 (Var type (Bit LgNumBytesFullCapSz) capOffset) ;
                      Var type (Bit (LgNumBytesFullCapSz + 1)) numBytesDXlen ]) in
    let crossesDXlen : bool :=
      evalExpr (FromBit Bool (TruncMsb 1 LgNumBytesFullCapSz
                                (Sub (Var type (Bit (LgNumBytesFullCapSz + 1)) endOffsetDXlen) $1))) in
    let nextStAddrMsb : type (Bit TagAddrWidth) :=
      evalExpr (Add [ Var type (Bit TagAddrWidth) stAddrMsb ; $1 ]) in
    evalExpr (Or [ Eq (Var type (Bit TagAddrWidth) stAddrMsb) (Var type (Bit TagAddrWidth) scanAddrMsb) ;
                   And [ Var type Bool crossesDXlen ;
                         Eq (Var type (Bit TagAddrWidth) nextStAddrMsb) (Var type (Bit TagAddrWidth) scanAddrMsb) ] ]).

  (* A capability base the revocation table covers (`isRevokableAddr`) *)
  Definition baseRevokable (b : type (Bit (AddrSz + 1))) : bool :=
    evalExpr (isRevokableAddr config (Var type (Bit (AddrSz + 1)) b)).

  (* The scan address of the impl revoker as a full address *)
  Definition iScanAddr (s1 : IState) : type Addr :=
    evalExpr ({< Var type (Bit TagAddrWidth) (revScanAddr (projImplRevokerArchState (iRev s1))),
                 Const type (Bit LgNumBytesFullCapSz) Zmod.zero >}).

  (* The merged value of a crossing load: the first line's packet `pkt0` merged with the second
   * line's response `rp1` (`implMemReadRpStep`, `specSecondLineStep`) *)
  Definition mergedLoadVal (ld : type LoadCmd) (pkt0 : type CapPacket) (rp1 : type LineReadRp)
    : type FullCapWithTag :=
    let a := ldAddr ld in
    let pkt : type CapPacket :=
      evalExpr (memMergeCapPacket (Var type Addr a) (Var type CapPacket pkt0) (Var type CapPacket (specPkt a rp1))) in
    evalLetExpr (memAssembleCapRead (Var type Addr a) (Var type (Bit LgLgNumBytesFullCapSz) (plSize (ldPending ld)))
                   (Var type CapPacket pkt)).

  (* The value a single-line read of `sz` bytes at `a` gets from line response `rp` *)
  Definition lineVal (a : type Addr) (sz : type (Bit LgLgNumBytesFullCapSz)) (rp : type LineReadRp)
    : type FullCapWithTag :=
    evalLetExpr (memAssembleCapRead (Var type Addr a) (Var type (Bit LgLgNumBytesFullCapSz) sz)
                   (Var type CapPacket (specPkt a rp))).

  Definition singleLoadVal (ld : type LoadCmd) (rp0 : type LineReadRp) : type FullCapWithTag :=
    let a := ldAddr ld in
    evalLetExpr (memAssembleCapRead (Var type Addr a) (Var type (Bit LgLgNumBytesFullCapSz) (plSize (ldPending ld)))
                   (Var type CapPacket (specPkt a rp0))).

  Definition AccessRel (g : Ghost) (s1 : IState) (s2 : SState) : Prop :=
    match g_acc g with
    | AccNone =>
        msIdle (iMemSt s1) = true /\ optValid (iReadRp s1) = false /\ optValid (iRpReady s1) = false /\
        PortsQuiet s1 /\ g_revOff g = RevEq /\ dmNotAccessing s1 /\ revNotReading s1 /\ optValid (sSecond s2) = false
    | AccStore addr size pkt st =>
        WrStageRel addr size pkt st s1 /\ dmLoadRq (iDmSt s1) = true /\ revNotReading s1 /\ g_revOff g = RevEq /\
        (snoopHitsB addr size (iScanMsb s1) = true -> iRevSnoopHit s1 = true) /\
        match st with
        | WrPend false | WrStaged false =>
            optValid (sSecond s2) = false /\
            exists q, HeadReq g q /\ opIsStore (mrOp q) = true /\
              stAddrOf (storeCmdOf q) = addr /\ stSizeOf (storeCmdOf q) = size /\
              pkt = disassembleW addr (stValOf (storeCmdOf q)) size
        | WrPend true | WrStaged true =>
            crossesB addr size = true /\ sSecond s2 = secondStoreOf addr pkt size
        end
    | AccLoad ld pkt0 st =>
        RdStageRel (ldAddr ld) (plSize (ldPending ld)) pkt0 st s1 /\ isReqDataMem (iRequester s1) = true /\
        dmLoadRp (iDmSt s1) = true /\ dmLoadRpV (iDmSt s1) = ld /\ revNotReading s1 /\ g_revOff g = RevEq /\
        let crosses := crossesB (ldAddr ld) (plSize (ldPending ld)) in
        match st with
        | RdPend false | RdStaged false | RdOut false =>
            optValid (sSecond s2) = false /\ pkt0 = getDefault CapPacket /\ g_cnwb g = None /\
            exists q, HeadReq g q /\ opIsLoad (mrOp q) = true /\ loadCmdOf q = ld
        | RdArrived false rp =>
            pkt0 = getDefault CapPacket /\
            if crosses
            then sSecond s2 = secondLoadOf ld (specPkt (ldAddr ld) rp) /\ g_cnwb g = None
            else optValid (sSecond s2) = false /\
                 g_cnwb g = Some (specLoadWb (sMem s2) (ldPending ld) (singleLoadVal ld rp))
        | RdPend true | RdStaged true | RdOut true =>
            crosses = true /\ g_cnwb g = None /\ sSecond s2 = secondLoadOf ld pkt0
        | RdArrived true rp1 =>
            crosses = true /\ optValid (sSecond s2) = false /\
            g_cnwb g = Some (specLoadWb (sMem s2) (ldPending ld) (mergedLoadVal ld pkt0 rp1))
        | RdReady res =>
            optValid (sSecond s2) = false /\ g_cnwb g = Some (specLoadWb (sMem s2) (ldPending ld) res)
        end
    | AccDmRev rc st =>
        RdStageRel (revByteAddrOf (rcBase rc)) byteSz (getDefault CapPacket) st s1 /\
        isReqDataMem (iRequester s1) = true /\
        dmRevRp (iDmSt s1) = true /\ dmRevRpV (iDmSt s1) = rc /\ revNotReading s1 /\ g_revOff g = RevEq /\
        optValid (sSecond s2) = false /\ g_cnwb g = Some (revWb (sMem s2) rc) /\
        rdSecond st = false /\ baseRevokable (rcBase rc) = true /\
        (* the value of the rev byte once it has been read *)
        match st with
        | RdArrived _ rp =>
            lineVal (revByteAddrOf (rcBase rc)) byteSz rp = memValAt (sMem s2) (revByteAddrOf (rcBase rc)) byteSz
        | RdReady res => res = memValAt (sMem s2) (revByteAddrOf (rcBase rc)) byteSz
        | _ => True
        end
    | AccRevCap st =>
        RdStageRel (iScanAddr s1) capSz (getDefault CapPacket) st s1 /\ isReqRevoker (iRequester s1) = true /\
        rpWaitCapRp (iRevPhase s1) = true /\ dmNotAccessing s1 /\
        (match st with
         | RdArrived _ _ | RdReady _ => g_revOff g <> RevImplAhead
         | _ => g_revOff g = RevEq
         end) /\
        optValid (sSecond s2) = false /\ rdSecond st = false
    | AccRevBit st =>
        RdStageRel (revByteAddrOf (iRevScanBase s1)) byteSz (getDefault CapPacket) st s1 /\
        isReqRevoker (iRequester s1) = true /\
        rpWaitRevBitRp (iRevPhase s1) = true /\ dmNotAccessing s1 /\ g_revOff g = RevEq /\
        optValid (sSecond s2) = false /\ rdSecond st = false
    | AccRevWrite addr pkt st =>
        WrStageRel addr capSz pkt st s1 /\ rpIdle (iRevPhase s1) = true /\ dmNotAccessing s1 /\
        g_revOff g = RevImplAhead /\ optValid (sSecond s2) = false /\ wrSecond st = false
    end.

  (* whether the head memory entry of the chain has left dataMem's queue *)
  Definition accTakesHead (a : Access) : bool :=
    match a with
    | AccStore _ _ _ (WrPend false) | AccStore _ _ _ (WrStaged false) => true
    | AccLoad _ _ (RdPend false) | AccLoad _ _ (RdStaged false) | AccLoad _ _ (RdOut false) => true
    | _ => false
    end.

  (* The committed load the impl has not written back is dataMem's. Between the two lines of a
   * crossing load (its entry has left the chain, its value is not committed yet) the chain avoids
   * the load's destination, as `RfRel` demands of a committed load. *)
  Definition CnwbRel (g : Ghost) (s1 : IState) (s2 : SState) : Prop :=
    (dmLoadRq (iDmSt s1) = true -> g_cnwb g = None) /\
    (dmRevRq (iDmSt s1) = true -> g_cnwb g = Some (revWb (sMem s2) (dmRevRqV (iDmSt s1)))) /\
    (dmRevRq (iDmSt s1) = true -> baseRevokable (rcBase (dmRevRqV (iDmSt s1))) = true) /\
    (dmLoadRp (iDmSt s1) = true -> g_cnwb g = None -> accTakesHead (g_acc g) = false ->
       ChainAvoids (g_chain g) (ldPending (dmLoadRpV (iDmSt s1))).(Fst)).

  (* --- 9b. The Revoker (C8) --- *)

  (* An architectural revoker state: [ base; top; control; epoch; intStatus; intRequested;
   * scanAddr; sweepTop ] *)
  Local Abbreviation RevArch := (TS (Node "revoker" (revokerChildren []))).

  Definition revSweepTopOf (x : RevArch) : bits TagAddrWidth := x.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst).
  Definition revEpochOf (x : RevArch) : bits Xlen := x.(Snd).(Snd).(Snd).(Fst).
  Definition iRevArch (s1 : IState) : RevArch := projImplRevokerArchState (iRev s1).

  Definition scanFull (a : bits TagAddrWidth) : type Addr :=
    evalExpr ({< Var type (Bit TagAddrWidth) a, Const type (Bit LgNumBytesFullCapSz) Zmod.zero >}).

  (* The sweep is on (odd epoch) and position `sa` is below the sweep's copy of `top` *)
  Definition revSweepingAt (x : RevArch) (sa : bits TagAddrWidth) : Prop :=
    evalExpr (FromBit Bool (TruncLsb (Xlen - 1) 1 (Var type (Bit Xlen) (revEpochOf x)))) = true /\
    evalExpr (Uge (Var type (Bit TagAddrWidth) sa) (Var type (Bit TagAddrWidth) (revSweepTopOf x))) = false.

  (* A loaded capability: [ tag; cap; addr ] *)
  Definition capECap (c : type FullCapWithTag) : type ECap :=
    evalLetExpr (@DecodeCap type c.(Snd).(Fst) c.(Snd).(Snd).(Fst)).
  Definition capNeedsCheck (c : type FullCapWithTag) : bool :=
    evalExpr (@needsRevocationCheck type config (capECap c) c.(Fst)).
  Definition capBase (c : type FullCapWithTag) : type (Bit (AddrSz + 1)) :=
    evalExpr ((Var type ECap (capECap c))`"base").
  Definition untagCap (c : type FullCapWithTag) : type FullCapWithTag :=
    (false ,, (c.(Snd).(Fst) ,, (c.(Snd).(Snd).(Fst) ,, tt))).

  (* The revoker's write waiting in the memory is the spec revoker step's write at position `sa`
   * (the impl's scanAddr is one ahead) *)
  Definition RevWriteOK (s1 : IState) (s2 : SState) (addr : type Addr) (pkt : type CapPacket) : Prop :=
    exists sa, revScanAddr (iRevArch s1) = Zmod.add sa Zmod.one /\ addr = scanFull sa /\
      revSweepingAt (iRevArch s1) sa /\
      capNeedsCheck (memValAt (sMem s2) addr capSz) = true /\
      revBitOf (sMem s2) (capBase (memValAt (sMem s2) addr capSz)) = true /\
      pkt = disassembleW addr (untagCap (memValAt (sMem s2) addr capSz)) capSz /\
      lineKind implRegions (lineOf false addr) = Some true.

  (* The value of the revoker's cap read. For an ExternalMem line (the spec at the same position)
   * it is the spec memory's; a line that is not ExternalMem was a device read, where the spec
   * has already taken the position's step (`RevSpecAhead`): its value needs no check. *)
  Definition RevCapOK (g : Ghost) (s1 : IState) (s2 : SState) (v : type FullCapWithTag) : Prop :=
    match g_revOff g with
    | RevSpecAhead => capNeedsCheck v = false
    | _ => lineKind implRegions (lineOf false (iScanAddr s1)) = Some true /\
           v = memValAt (sMem s2) (iScanAddr s1) capSz
    end.

  (* The values of the revoker's reads in flight *)
  Definition RevAccRel (g : Ghost) (s1 : IState) (s2 : SState) : Prop :=
    match g_acc g with
    | AccRevCap (RdArrived _ rp) => RevCapOK g s1 s2 (lineVal (iScanAddr s1) capSz rp)
    | AccRevCap (RdReady res) => RevCapOK g s1 s2 res
    | AccRevBit (RdArrived _ rp) =>
        lineVal (revByteAddrOf (iRevScanBase s1)) byteSz rp =
          memValAt (sMem s2) (revByteAddrOf (iRevScanBase s1)) byteSz
    | AccRevBit (RdReady res) => res = memValAt (sMem s2) (revByteAddrOf (iRevScanBase s1)) byteSz
    | AccRevWrite addr pkt _ => RevWriteOK s1 s2 addr pkt
    | _ => True
    end.

  (* While a position is processed the sweep is on at scanAddr. From the cap read on, the saved
   * cap needs a check, scanAddr's line is ExternalMem, and the saved cap is the cap at scanAddr
   * unless a store hit it; at WriteCap its rev bit is set. *)
  Definition RevokerRel (g : Ghost) (s1 : IState) (s2 : SState) : Prop :=
    (rpIdle (iRevPhase s1) = false -> revSweepingAt (iRevArch s1) (revScanAddr (iRevArch s1))) /\
    (rpCheck (iRevPhase s1) = true ->
       capNeedsCheck (iRevScanCap s1) = true /\ iRevScanBase s1 = capBase (iRevScanCap s1) /\
       lineKind implRegions (lineOf false (iScanAddr s1)) = Some true) /\
    (rpCheck (iRevPhase s1) = true -> iRevSnoopHit s1 = false ->
       memValAt (sMem s2) (iScanAddr s1) capSz = iRevScanCap s1) /\
    (rpWriteCap (iRevPhase s1) = true -> iRevSnoopHit s1 = false ->
       revBitOf (sMem s2) (iRevScanBase s1) = true) /\
    RevAccRel g s1 s2.

  (* --- 10. dataMem's Queue --- *)

  Definition isPlainFence (q : type MemFenceReq) : bool :=
    andb (negb (opIsMem (mrOp q))) (negb (opIsFenceI (mrOp q))).

  Definition chainReqs (G : list GItemT) : list (type MemFenceReq) :=
    flat_map (fun it => match it with
                        | GInst e => match entryReq e with Some q => [q] | None => [] end
                        | GTick => []
                        end) G.

  Definition DmQueueRel (g : Ghost) (s1 : IState) : Prop :=
    let reqs := filter (fun q => negb (isPlainFence q)) (chainReqs (g_chain g)) in
    filter (fun q => negb (isPlainFence q)) (iDmBuf s1) = (if accTakesHead (g_acc g) then tl reqs else reqs).

  (* --- 11. Liveness, Fences and Eager Replay --- *)

  Definition daLive (s1 : IState) (j : type DecodeToAluEntry) : bool := Zmod.eqb (daExecEpoch j) (iExecEpoch s1).
  Definition aiLive (s1 : IState) (a : type AssembledInst) : bool := Zmod.eqb (aiExecEpoch a) (iExecEpoch s1).
  Definition fbLive (s1 : IState) (f : type FetchBufEntry) : bool :=
    andb (Zmod.eqb (fbExecEpoch f) (iExecEpoch s1)) (Zmod.eqb (fbPredEpoch f) (iPredEpoch s1)).

  Definition NoLive (s1 : IState) : Prop :=
    Forall (fun j => daLive s1 j = false) (iD2a s1) /\
    Forall (fun a => aiLive s1 a = false) (iInstBuf s1) /\
    Forall (fun f => fbLive s1 f = false) (iFetchBuf s1).

  Definition entryIsFenceI (e : GEntryT) : bool :=
    match entryReq e with Some q => opIsFenceI (mrOp q) | None => false end.

  Definition FenceRel (g : Ghost) (s1 : IState) : Prop :=
    (iFenceIPending s1 = true ->
       NoLive s1 /\ optValid (iStraddle s1) = false /\
       exists G1 e G2, g_chain g = (G1 ++ GInst e :: G2)%list /\ entryIsFenceI e = true /\
                       Forall (fun it => it = GTick) G2) /\
    (~ NoFenceIWait s1 ->
       iFenceIPending s1 = false /\ NoLive s1 /\ optValid (iStraddle s1) = false /\
       forall e, ~ In (GInst e) (g_chain g)) /\
    (* a fence.i in the chain is pending and is the last instruction (only ticks follow it) *)
    (forall G1 e G2, g_chain g = (G1 ++ GInst e :: G2)%list -> entryIsFenceI e = true ->
       iFenceIPending s1 = true /\ Forall (fun it => it = GTick) G2).

  Definition entryBlocking (e : GEntryT) : bool :=
    match entryReq e with Some q => negb (isPlainFence q) | None => false end.

  (* Ticks, ALU entries and plain fences are replayed as soon as they reach the head *)
  Definition EagerRel (g : Ghost) (s2 : SState) : Prop :=
    g_chain g = [] \/
    exists e G', g_chain g = GInst e :: G' /\ (optValid (sSecond s2) = true \/ entryBlocking e = true).

  (* --- 12. Scoreboard --- *)

  Definition RegAvoidAll (ws : list (bits RegIdxSzReal)) (x : bits RegIdxSzReal) : Prop :=
    forall d, In d ws -> RegAvoid d x.

  Definition aluInWritesCd (a : type AluInInstGroup) : bool := evalExpr (##a`"writesCd").
  Definition aluInInst (a : type AluInInstGroup) : type Inst := evalExpr (##a`"inst").
  Definition aluInCd (a : type AluInInstGroup) : bits RegIdxSzReal :=
    evalExpr (TruncLsb (RegIdxSz - RegIdxSzReal) RegIdxSzReal (@getCd type (aluInInst a))).

  (* the destination register of each pending writer, older writers first *)
  Definition dmInFlightDst (s1 : IState) : list (bits RegIdxSzReal) :=
    let st := iDmSt s1 in
    if dmLoadRp st then [ (ldPending (dmLoadRpV st)).(Fst) ]
    else if dmRevRq st then [ (dmRevRqV st).(Snd).(Fst).(Fst) ]
    else if dmRevRp st then [ (dmRevRpV st).(Snd).(Fst).(Fst) ]
    else [].

  Definition olderWriters (s1 : IState) : list (bits RegIdxSzReal) :=
    filter (fun d => negb (Zmod.eqb d Zmod.zero))
      (dmInFlightDst s1 ++
       map mrDst (filter (fun q => opIsLoad (mrOp q)) (iDmBuf s1)) ++
       map fst (extractMulDivEntries mulCapacity divCapacity mulStages divStages mulDivMode
                  (impl_mulDiv pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                     mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions s1)))%list.

  (* the register a decode-to-ALU entry writes (0: none); it is the ALU's `dstIdx` *)
  Definition d2aDst (j : type DecodeToAluEntry) : bits RegIdxSzReal :=
    if aluInWritesCd (daAluIn j) then aluInCd (daAluIn j) else Zmod.zero.

  (* x0 is never tracked: it has no wait bit (ImplCommon.v) *)
  Definition d2aWriters (l : list (type DecodeToAluEntry)) : list (bits RegIdxSzReal) :=
    filter (fun d => negb (Zmod.eqb d Zmod.zero)) (map d2aDst l).

  (* a register's wait bit is set exactly when a writer of it is pending (no stuck bits) *)
  Definition ScoreRel (g : Ghost) (s1 : IState) : Prop :=
    let W := (olderWriters s1 ++ d2aWriters (iD2a s1))%list in
    NoDup W /\
    (forall r, readWaitBit r (iWb s1) = true <-> In r W) /\
    length (g_d2aFo g) = length (iD2a s1) /\
    (* each live decode-to-ALU entry read registers no older writer writes *)
    (forall l1 j l2 fo,
       iD2a s1 = (l1 ++ j :: l2)%list -> nth_error (g_d2aFo g) (length l1) = Some fo ->
       daLive s1 j = true ->
       daAluIn j = evalRegRead pcAddrInit (evalDecode fo) (iFlush s1) /\
       RegAvoidAll (olderWriters s1 ++ d2aWriters l1) (decCs1 fo) /\
       RegAvoidAll (olderWriters s1 ++ d2aWriters l1) (decCs2 fo)).

  (* --- 13. Frontend --- *)

  Definition pccWithAddr (pcc : type FullECapWithTag) (a : type Addr) : type FullECapWithTag :=
    (pcc.(Fst) ,, (pcc.(Snd).(Fst) ,, (a ,, tt))).

  Definition needsPredOf (inst : type Inst) : bool :=
    let pb := evalLetExpr (@preDecodeBranch type inst) in
    evalExpr (Or [ ##pb`"isCjal" ; ##pb`"isBranch" ; ##pb`"isCjalr" ; ##pb`"isCall" ; ##pb`"isReturn" ]).

  Definition seqPcOf (pc : type Addr) (inst : type Inst) : type Addr :=
    evalExpr (Add [ Var type Addr pc ;
                    ITE (@isCompressed type inst) ($(CompInstSz / 8) : Expr type Addr) $(InstSz / 8) ]).

  Definition lineAddrOf (pc : type Addr) : type Addr := evalExpr (memLineAddr (Var type Addr pc)).
  Definition parcelAddrOf (aligned : type Addr) (k : type (Bit LgFetchParcels)) : type Addr :=
    evalExpr (@getParcelAddr type aligned k).
  Definition fetchPktOf (rp : type LineReadRp) : type FetchPacket := evalExpr (@memExtractFetchPacket type rp).
  Definition pktParcel (pkt : type FetchPacket) (k : type (Bit LgFetchParcels)) : type (Bit CompInstSz) :=
    evalExpr (ReadArray (Var type FetchPacket pkt) (Var type (Bit LgFetchParcels) k)).
  Definition lastParcel : type (Bit LgFetchParcels) := evalExpr (Const type (Bit LgFetchParcels) (InvDefault _)).

  (* The pre-fault flags fetchRq computes at `pc` with PCC `pcc` *)
  Definition preExcAt (pcc : type FullECapWithTag) (pc : type Addr) : type FetchException :=
    let pccECap : type ECap := evalExpr (##pcc`"ecap") in
    (evalExpr (Not (##pcc`"tag")) ,,
     (evalExpr (@isSealed type pccECap) ,,
      (evalExpr (Not (##pccECap`"perms"`"EX")) ,,
       (evalExpr (Ult (ZeroExtendTo (AddrSz + 1) (Var type Addr pc)) (##pccECap`"base")) ,, tt)))).

  (* The fetch top check of a compressed (`isComp`) or full instruction at `pc` under PCC `pcc`,
   * as fetchAssemble and `specMemFetchRead` compute it (`specTopExc`) *)
  Definition topExcAt (pcc : type FullECapWithTag) (pc : type Addr) (isComp : bool) : bool :=
    let instLgBytes : type (Bit LgLgNumBytesFullCapSz) :=
      evalExpr (ITE (Var type Bool isComp)
                    ($(Z.log2 (CompInstSz / 8)) : Expr type (Bit LgLgNumBytesFullCapSz))
                    $(Z.log2 (InstSz / 8))) in
    let instEnd : type (Bit (AddrSz + 2)) := evalLetExpr (@AdderAccessEnd type pc instLgBytes) in
    evalExpr (memFetchTopExc (Var type (Bit (AddrSz + 2)) instEnd) (Var type (Bit (AddrSz + 2)) (pccTopOf pcc))).

  Lemma topExcAt_ecap :
    forall (p1 p2 : type FullECapWithTag) pc c, p1.(Snd).(Fst) = p2.(Snd).(Fst) -> topExcAt p1 pc c = topExcAt p2 pc c.
  Proof. intros [t1 [e1 [a1 []]]] [t2 [e2 [a2 []]]] pc c E; cbn in E; subst e2; reflexivity. Qed.

  (* Live instructions: each with its fetch output and predicted next PC, oldest first *)
  Definition liveInsts (g : Ghost) (s1 : IState) : list (type FetchOut * type Addr) :=
    (map (fun jf => (snd jf, daPredPc (fst jf)))
         (filter (fun jf => daLive s1 (fst jf)) (combine (iD2a s1) (g_d2aFo g))) ++
     map (fun a => (aiFetchOut a, aiPredPc a)) (filter (aiLive s1) (iInstBuf s1)))%list.

  (* Live fetchBuf entries form a chain ending at fetchPc *)
  Fixpoint FbChain (l : list (type FetchBufEntry)) (fetchPc : type Addr) : Prop :=
    match l with
    | [] => True
    | [f] => fbPredPc f = fetchPc
    | f :: (f' :: _) as l' => fbPredPc f = fbPcAddr f' /\ FbChain l' fetchPc
    end.

  (* `a` is even (bit 0 is clear) *)
  Definition pcAligned (a : type Addr) : Prop :=
    evalExpr (TruncLsb (AddrSz - 1) 1 (Var type Addr a)) = Zmod.zero.

  (* Where fetch continues, given the PC `fp` of the next instruction to assemble. A live fetchBuf
   * head being assembled from parcel `curParcelOpt` has the pre-fault flags of `fp`; `fp` is even.
   * A saved straddle is the uncompressed low parcel of a 4-byte instruction at `fp` that passes
   * the pre-fault and top checks of the current PCC. *)
  Definition FrontierRel (s1 : IState) (s2 : SState) (fp : type Addr) : Prop :=
    let fb := iFetchBuf s1 in
    let live := filter (fbLive s1) fb in
    let pcc := iPcc s1 in
    FbChain live (iFetchPc s1) /\
    Forall (fun f => fbFetchExc f = preExcAt pcc (fbPcAddr f)) live /\
    (if optValid (iStraddle s1)
     then
       let sh := optData (iStraddle s1) in
       lineAddrOf fp <> fp /\ (* the straddle sits in the last parcel of its line *)
       evalExpr (@getPacketParcel type fp) = lastParcel /\
       sh.(Snd).(Fst) = preExcAt pcc fp /\
       excAny (preExcAt pcc fp) = false /\
       topExcAt pcc fp false = false /\
       evalExpr (@isParcelCompressed type sh.(Fst)) = false /\
       (exists rpPrev,
          LineAllowed initLine fwcs specRegions (sMem s2) (lineAddrOf fp) rpPrev /\
          sh.(Fst) = pktParcel (fetchPktOf rpPrev) lastParcel) /\
       match live with
       | [] => iFetchPc s1 = evalExpr (memNextLineAddr (Var type Addr fp))
       | f :: _ => fbPcAddr f = evalExpr (memNextLineAddr (Var type Addr fp))
       end
     else
       match live with
       | [] => iFetchPc s1 = fp
       | f :: _ =>
           if andb (match fb with f0 :: _ => fbLive s1 f0 | [] => false end) (optValid (iCurParcel s1))
           then parcelAddrOf (lineAddrOf (fbPcAddr f)) (optData (iCurParcel s1)) = fp /\
                fbFetchExc f = preExcAt pcc fp
           else fbPcAddr f = fp
       end) /\
    pcAligned fp.

  (* The chain of live instructions from PC `pc`: each can be fetched by the spec, and
   * predicts the sequential PC unless it needs prediction; after a faulting instruction
   * anything may follow (it traps and redirects). `LiveChainG` takes only the pieces it
   * reads (PCC, spec memory, frontier), so steps that keep them keep it by conversion. *)
  Fixpoint LiveChainG (pcc : type FullECapWithTag) (m : TS (specMemTree specRegions))
    (frontier : type Addr -> Prop) (pc : type Addr) (l : list (type FetchOut * type Addr)) : Prop :=
    match l with
    | [] => frontier pc
    | (fo, pp) :: l' =>
        FetchAllowedInst initLine fwcs specRegions m (pccWithAddr pcc pc) fo /\
        (if foFault fo then True
         else (needsPredOf (foInst fo) = false -> pp = seqPcOf pc (foInst fo)) /\ LiveChainG pcc m frontier pp l')
    end.

  Definition LiveChain (s1 : IState) (s2 : SState) (pc : type Addr) (l : list (type FetchOut * type Addr)) : Prop :=
    LiveChainG (iPcc s1) (sMem s2) (FrontierRel s1 s2) pc l.


  (* Fetch responses of an ExternalMem region match the non-prefaulted fetchBuf entries of
   * its lines, in order; a response waiting in `readRp` is for the oldest one *)
  Definition fbInRegion (s1 : IState) (r : MemRegion) : list (type FetchBufEntry) :=
    filter (fun f => andb (negb (excAny (fbFetchExc f))) (isRegionAddrB r (lineAddrOf (fbPcAddr f)))) (iFetchBuf s1).

  Definition FetchRespRel (s1 : IState) (s2 : SState) : Prop :=
    AllPorts (fun r y =>
      let E := fbInRegion s1 r in
      let rcv := y.(Fst).(Fst).(Snd).(Fst) in
      let rdRp := y.(Snd).(Fst).(Snd).(Snd).(Snd).(Fst) in
      exists C, implFetchAccRqs r y = (rev (map (fun f => lineAddrOf (fbPcAddr f)) E) ++ C)%list /\
                (length C + (if optValid rdRp then 1 else 0))%nat = length rcv /\
                (optValid rdRp = true ->
                   exists f E', E = f :: E' /\
                     (fbLive s1 f = true ->
                        LineAllowed initLine fwcs specRegions (sMem s2) (lineAddrOf (fbPcAddr f)) (optData rdRp))))
      implRegions (iRegions s1).

  Definition StalePrefix {A : Type} (live : A -> bool) (l : list A) : Prop :=
    exists l1 l2, l = (l1 ++ l2)%list /\ Forall (fun x => live x = false) l1 /\ Forall (fun x => live x = true) l2.

  Definition FrontRel (g : Ghost) (s1 : IState) (s2 : SState) : Prop :=
    StalePrefix (daLive s1) (iD2a s1) /\
    StalePrefix (aiLive s1) (iInstBuf s1) /\
    StalePrefix (fbLive s1) (iFetchBuf s1) /\
    (Exists (fun j => daLive s1 j = true) (iD2a s1) -> Forall (fun a => aiLive s1 a = true) (iInstBuf s1)) /\
    ((Exists (fun j => daLive s1 j = true) (iD2a s1) \/ Exists (fun a => aiLive s1 a = true) (iInstBuf s1)) ->
       Forall (fun f => Zmod.eqb (fbExecEpoch f) (iExecEpoch s1) = true) (iFetchBuf s1)) /\
    LiveChain s1 s2 (iPcc s1).(Snd).(Snd).(Fst) (liveInsts g s1) /\
    FetchRespRel s1 s2.

  (* --- 14. Well-Formedness --- *)

  (* The mulDiv request FIFOs are well-formed. The engines' result FIFOs and the multiplier's stage
   * FIFOs have capacity 1, so they are well-formed by construction. *)
  Definition MulDivReqWf
    (smd : TS (implMulDivTree mulCapacity divCapacity (Z.to_nat Xlen) mulStages divStages mulDivMode)) : Prop :=
    match mulDivMode as m
      return TS (implMulDivTree mulCapacity divCapacity (Z.to_nat Xlen) mulStages divStages m) -> Prop
    with
    | PipelinedMul_IterDiv => fun s => fifo_wf s.(Fst).(Fst) /\ fifo_wf s.(Snd).(Fst).(Fst)
    | IterMul_SeparateIterDiv => fun s => fifo_wf s.(Fst).(Fst) /\ fifo_wf s.(Snd).(Fst).(Fst)
    | IterMul_SharedIterDiv => fun s => fifo_wf s.(Fst)
    end smd.

  (* An iterative engine is busy exactly when its destination FIFO holds an entry *)
  Definition IterBusyRel {K : Kind} (busy : bool) (dst : list (type K)) : Prop := busy = true <-> dst <> [].

  (* Each engine computes for exactly the destinations in its destination FIFO *)
  Definition MulDivEngWf
    (smd : TS (implMulDivTree mulCapacity divCapacity (Z.to_nat Xlen) mulStages divStages mulDivMode)) : Prop :=
    match mulDivMode as m
      return TS (implMulDivTree mulCapacity divCapacity (Z.to_nat Xlen) mulStages divStages m) -> Prop
    with
    | PipelinedMul_IterDiv => fun s =>
        length (@extractPipeStageStates (MulStageState (dataLen (Z.to_nat Xlen))) mulStages s.(Fst).(Snd).(Fst).(Fst)) = length (@fifo_to_list MulDivFifoCapacity RegIdx s.(Fst).(Snd).(Fst).(Snd).(Fst)) /\
        IterBusyRel s.(Snd).(Fst).(Snd).(Fst).(Fst).(Fst) (@fifo_to_list MulDivFifoCapacity RegIdx s.(Snd).(Fst).(Snd).(Fst).(Snd).(Fst))
    | IterMul_SeparateIterDiv => fun s =>
        IterBusyRel s.(Fst).(Snd).(Fst).(Fst).(Fst) (@fifo_to_list MulDivFifoCapacity RegIdx s.(Fst).(Snd).(Fst).(Snd).(Fst)) /\
        IterBusyRel s.(Snd).(Fst).(Snd).(Fst).(Fst).(Fst) (@fifo_to_list MulDivFifoCapacity RegIdx s.(Snd).(Fst).(Snd).(Fst).(Snd).(Fst))
    | IterMul_SharedIterDiv => fun s =>
        IterBusyRel s.(Snd).(Fst).(Fst).(Fst) (@fifo_to_list MulDivFifoCapacity RegIdx s.(Snd).(Fst).(Snd).(Fst))
    end smd.

  Definition MulDivWf
    (smd : TS (implMulDivTree mulCapacity divCapacity (Z.to_nat Xlen) mulStages divStages mulDivMode)) : Prop :=
    MulDivReqWf smd /\ MulDivEngWf smd.

  Lemma init_pipe_states :
    forall K n (s : TS (stagedStagesTree K n)),
      InitStateConsistent (stagedStagesTree K n) s -> extractPipeStageStates n s = [].
  Proof.
    intros K n; induction n as [| n IH]; intros [f rest] H.
    - destruct H as [Hf _]; cbn [extractPipeStageStates Fst].
      rewrite (InitStateConsistent_fifo_to_list 1 K f Hf); reflexivity.
    - destruct rest as [sub []]; destruct H as [Hf [Hsub _]]; cbn [extractPipeStageStates Fst Snd].
      rewrite (IH sub Hsub), (InitStateConsistent_fifo_to_list 1 K f Hf); reflexivity.
  Qed.

  Lemma init_iter_busy :
    forall K n (w : TS (stagedIterTree K n)), InitStateConsistent (stagedIterTree K n) w -> w.(Fst) = false.
  Proof. intros K n w H; cbn in H; subst w; reflexivity. Qed.

  Lemma MulDivWf_init :
    forall smd,
      InitStateConsistent (implMulDivTree mulCapacity divCapacity (Z.to_nat Xlen) mulStages divStages mulDivMode) smd ->
      MulDivWf smd.
  Proof.
    unfold MulDivWf, MulDivReqWf, MulDivEngWf; destruct mulDivMode; intros smd Hinit.
    - destruct smd as [[mulReqF [[mulPipe [mulDstF []]] []]] [[divReqF [[divIter [divDstF []]] []]] []]].
      cbn [InitStateConsistent Fst Snd] in Hinit |- *.
      destruct Hinit as [[HmulReq [[HmulPipe [HmulDst _]] _]] [[HdivReq [[HdivIter [HdivDst _]] _]] _]].
      split; [exact (conj (InitStateConsistent_fifo_wf _ _ _ HmulReq) (InitStateConsistent_fifo_wf _ _ _ HdivReq)) |].
      rewrite (init_pipe_states _ _ mulPipe HmulPipe), (InitStateConsistent_fifo_to_list _ _ mulDstF HmulDst),
              (InitStateConsistent_fifo_to_list _ _ divDstF HdivDst), (init_iter_busy _ _ divIter HdivIter).
      split; [reflexivity | split; [discriminate | intros H; exfalso; exact (H eq_refl)]].
    - destruct smd as [[mulReqF [[mulIter [mulDstF []]] []]] [[divReqF [[divIter [divDstF []]] []]] []]].
      cbn [InitStateConsistent Fst Snd] in Hinit |- *.
      destruct Hinit as [[HmulReq [[HmulIter [HmulDst _]] _]] [[HdivReq [[HdivIter [HdivDst _]] _]] _]].
      split; [exact (conj (InitStateConsistent_fifo_wf _ _ _ HmulReq) (InitStateConsistent_fifo_wf _ _ _ HdivReq)) |].
      rewrite (InitStateConsistent_fifo_to_list _ _ mulDstF HmulDst), (InitStateConsistent_fifo_to_list _ _ divDstF HdivDst),
              (init_iter_busy _ _ mulIter HmulIter), (init_iter_busy _ _ divIter HdivIter).
      split; (split; [discriminate | intros H; exfalso; exact (H eq_refl)]).
    - destruct smd as [reqF [[sharedIter [dstF []]] []]].
      cbn [InitStateConsistent Fst Snd] in Hinit |- *.
      destruct Hinit as [Hreq [[Hiter [Hdst _]] _]].
      split; [exact (InitStateConsistent_fifo_wf _ _ _ Hreq) |].
      rewrite (InitStateConsistent_fifo_to_list _ _ dstF Hdst), (init_iter_busy _ _ sharedIter Hiter).
      split; [discriminate | intros H; exfalso; exact (H eq_refl)].
  Qed.

  (* fetchBuf is well-formed and non-empty while a parcel of its head is being assembled; the PC
   * and all predicted PCs in the frontend are even *)
  Definition WfRel (g : Ghost) (s1 : IState) (s2 : SState) : Prop :=
    (fifo_wf (fetch_fetchBufFifo pcAddrInit fetchCapacity instCapacity (iFetch s1)) /\
     (optValid (iCurParcel s1) = true -> iFetchBuf s1 <> []) /\
     pcAligned (iPcc s1).(Snd).(Snd).(Fst) /\
     Forall (fun j => pcAligned (daPredPc j)) (iD2a s1) /\
     Forall (fun a => pcAligned (aiPredPc a)) (iInstBuf s1) /\
     Forall (fun f => pcAligned (fbPredPc f)) (iFetchBuf s1)) /\
    fifo_wf (fetch_instFifo pcAddrInit fetchCapacity instCapacity (iFetch s1)) /\
    fifo_wf (decode_toAluFifo decodeCapacity (iDecode s1)) /\
    fifo_wf (dataMem_fifo dataMemCapacity (iDm s1)) /\
    MulDivWf (impl_mulDiv pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions s1) /\
    AllPorts (fun r y => ImplExternalRegionHandshakeInv r y /\ RegionFenceICountInv r y.(Fst))
      implRegions (iRegions s1).

  (* --- 15. The Relation --- *)

  Record RefRelG (g : Ghost) (s1 : IState) (s2 : SState) : Prop := {
    rr_rf     : RfRel g s1 s2 ;
    rr_mem    : MemRelC g s1 s2 ;
    rr_latch  : LatchRel g s2 ;
    rr_replay : ReplayRel g s2 ;
    rr_eager  : EagerRel g s2 ;
    rr_acc    : AccessRel g s1 s2 ;
    rr_cnwb   : CnwbRel g s1 s2 ;
    rr_dmq    : DmQueueRel g s1 ;
    rr_fence  : FenceRel g s1 ;
    rr_score  : ScoreRel g s1 ;
    rr_front  : FrontRel g s1 s2 ;
    rr_wf     : WfRel g s1 s2 ;
    rr_rev    : RevokerRel g s1 s2
  }.

  Definition RefRel (s1 : IState) (s2 : SState) : Prop := exists g, RefRelG g s1 s2.

  (* --- 16. Frame Lemmas --- *)

  Lemma RegionPort_impl :
    forall (P Q : forall r, TS (implExternalMemRegionTree r) -> Prop) r (y : TS (implMemRegionTree r)),
      (forall r y, P r y -> Q r y) -> RegionPort P r y -> RegionPort Q r y.
  Proof.
    intros P Q r; unfold RegionPort, implMemRegionTree.
    destruct (regionKind r); intros y HPQ H; [exact (HPQ r y H) | exact I].
  Qed.

  Lemma AllPorts_impl :
    forall (P Q : forall r, TS (implExternalMemRegionTree r) -> Prop) l (mi : TS (implRegionsTree l)),
      (forall r y, P r y -> Q r y) -> AllPorts P l mi -> AllPorts Q l mi.
  Proof.
    intros P Q l; induction l as [| r l IH]; intros mi HPQ H; cbn [AllPorts] in *; [exact I |].
    destruct H as [H0 H1]; split; [exact (RegionPort_impl P Q r _ HPQ H0) | exact (IH _ HPQ H1)].
  Qed.

  Lemma memValAt_ext :
    forall m m' a sz,
      (forall L, lineContent specRegions m' L = lineContent specRegions m L) ->
      memValAt m' a sz = memValAt m a sz.
  Proof.
    intros m m' a sz H; unfold memValAt; rewrite H; reflexivity.
  Qed.

  Lemma revBitOf_ext :
    forall m m' b,
      (forall L, lineContent specRegions m' L = lineContent specRegions m L) ->
      revBitOf m' b = revBitOf m b.
  Proof.
    intros m m' b H; unfold revBitOf; cbv zeta; rewrite (memValAt_ext m m' _ _ H); reflexivity.
  Qed.

  Lemma specLoadWb_ext :
    forall m m' pl v,
      (forall L, lineContent specRegions m' L = lineContent specRegions m L) ->
      specLoadWb m' pl v = specLoadWb m pl v.
  Proof.
    intros m m' pl v H; unfold specLoadWb; cbv zeta.
    rewrite (revBitOf_ext m m' _ H); reflexivity.
  Qed.

  Lemma revWb_ext :
    forall m m' rc,
      (forall L, lineContent specRegions m' L = lineContent specRegions m L) ->
      revWb m' rc = revWb m rc.
  Proof.
    intros m m' rc H; unfold revWb; cbv zeta.
    rewrite (revBitOf_ext m m' _ H); reflexivity.
  Qed.

  Lemma FrontierRel_mono :
    forall s1 s2 s2' fp,
      SnapshotOK fwcs specRegions (sMem s2) ->
      FetchViewExt specRegions (sMem s2) (sMem s2') ->
      FrontierRel s1 s2 fp -> FrontierRel s1 s2' fp.
  Proof.
    intros s1 s2 s2' fp Hsnap Hext H; unfold FrontierRel in *; cbv zeta in *.
    destruct H as [H1 [H2 [H3 H4]]]; split; [exact H1 | split; [exact H2 | split; [| exact H4]]].
    destruct (optValid (iStraddle s1)); [| exact H3].
    destruct H3 as [Ha [Hb [Hc [Hx [Ht [Hu [[rpPrev [Hal Hsh]] Hd]]]]]]].
    split; [exact Ha | split; [exact Hb | split; [exact Hc | split; [exact Hx |]]]].
    split; [exact Ht | split; [exact Hu | split; [| exact Hd]]].
    exists rpPrev; split; [| exact Hsh].
    exact (LineAllowed_fetchViewExt initLine specRegions fwcs _ _ _ _ Hsnap Hext Hal).
  Qed.

  Lemma LiveChainG_mono :
    forall pcc m m' (F F' : type Addr -> Prop) l pc,
      SnapshotOK fwcs specRegions m -> FetchViewExt specRegions m m' ->
      (forall p, F p -> F' p) ->
      LiveChainG pcc m F pc l -> LiveChainG pcc m' F' pc l.
  Proof.
    intros pcc m m' F F' l; induction l as [| [fo pp] l IH]; intros pc Hsnap Hext HF H; cbn [LiveChainG] in *.
    - exact (HF pc H).
    - destruct H as [Hfa Hrest]; split.
      + exact (FetchAllowedInst_fetchViewExt initLine fwcs specRegions m m' _ _ Hsnap Hext Hfa).
      + destruct (foFault fo); [exact I |].
        destruct Hrest as [Hp Hl]; split; [exact Hp | exact (IH pp Hsnap Hext HF Hl)].
  Qed.

  (* The access in flight only reads these observations of the two states *)
  Lemma AccessRel_frame :
    forall g (s1 s1' : IState) (s2 s2' : SState),
      (forall P, AllPorts P implRegions (iRegions s1') = AllPorts P implRegions (iRegions s1)) ->
      iRev s1' = iRev s1 -> iMemSt s1' = iMemSt s1 -> iRdBufs s1' = iRdBufs s1 ->
      iRequester s1' = iRequester s1 -> iDmSt s1' = iDmSt s1 -> sSecond s2' = sSecond s2 ->
      (forall L, lineContent specRegions (sMem s2') L = lineContent specRegions (sMem s2) L) ->
      AccessRel g s1 s2 -> AccessRel g s1' s2'.
  Proof.
    intros g s1 s1' s2 s2' HP HR Emst Ebuf Ereq Edm Esec Hlc Ha.
    assert (Erp : iReadRp s1' = iReadRp s1) by exact (f_equal (fun b => b.(Fst)) Ebuf).
    assert (Erdy : iRpReady s1' = iRpReady s1) by exact (f_equal (fun b => b.(Snd).(Fst)) Ebuf).
    assert (Hslw : forall pl v, specLoadWb (sMem s2') pl v = specLoadWb (sMem s2) pl v)
      by (intros pl v; apply specLoadWb_ext; exact Hlc).
    assert (Hrw : forall rc, revWb (sMem s2') rc = revWb (sMem s2) rc)
      by (intros rc; apply revWb_ext; exact Hlc).
    assert (Hmv : forall a sz, memValAt (sMem s2') a sz = memValAt (sMem s2) a sz)
      by (intros a sz; apply memValAt_ext; exact Hlc).
    unfold AccessRel in *.
    revert Ha.
    destruct (g_acc g) as [| addr size pkt [[|]|[|]] | ld pkt0 [[|]|[|]|[|]|[|] rp|res]
                          | rc [[|]|[|]|[|]|[|] rp|res] | [[|]|[|]|[|]|[|] rp|res]
                          | [[|]|[|]|[|]|[|] rp|res] | addr pkt [[|]|[|]]];
      intros Ha.
    (* one step per sentence over the 45 cases (compile speed) *)
    all: unfold WrStageRel, RdStageRel, PortsQuiet, PortsReadStaged, PortsReadOut, PortsWriteStaged,
           revNotReading, dmNotAccessing, iRevPhase, iScanAddr, iRevScanBase, iScanMsb, iRevSnoopHit in *.
    all: cbv beta iota zeta in *.
    all: rewrite ?HP, ?HR, ?Hrw, ?Hmv, ?Emst, ?Erp, ?Erdy, ?Ereq, ?Edm, ?Esec.
    all: try (lazymatch goal with |- context [specLoadWb] => setoid_rewrite Hslw end).
    all: exact Ha.
  Qed.

  (* A valid `rpReady` means `state` = ReadRpReady *)
  Lemma AccessRel_rpReady :
    forall g (s1 : IState) (s2 : SState),
      AccessRel g s1 s2 -> optValid (iRpReady s1) = true -> msReadRpReady (iMemSt s1) = true.
  Proof.
    intros g s1 s2 Ha Hv.
    unfold AccessRel in Ha.
    destruct (g_acc g) as [| addr size pkt [b|b] | ld pkt0 [b|b|b|b rp|res]
                          | rc [b|b|b|b rp|res] | [b|b|b|b rp|res]
                          | [b|b|b|b rp|res] | addr pkt [b|b]];
      unfold WrStageRel, RdStageRel in Ha; cbv beta iota zeta in Ha;
      repeat match goal with H : _ /\ _ |- _ => destruct H end;
      first [ assumption
            | exfalso; match goal with H : optValid (iRpReady s1) = false |- _ => rewrite H in Hv; discriminate Hv end ].
  Qed.

  (* The revoker facts read only the revoker state, the access in flight and the line contents *)
  Lemma RevokerRel_frame :
    forall g g' (s1 s1' : IState) (s2 s2' : SState),
      g_acc g' = g_acc g -> g_revOff g' = g_revOff g -> iRev s1' = iRev s1 ->
      (forall L, lineContent specRegions (sMem s2') L = lineContent specRegions (sMem s2) L) ->
      RevokerRel g s1 s2 -> RevokerRel g' s1' s2'.
  Proof.
    intros g g' s1 s1' s2 s2' Eacc Eoff HR Hlc H.
    assert (Hmv : forall a sz, memValAt (sMem s2') a sz = memValAt (sMem s2) a sz)
      by (intros a sz; apply memValAt_ext; exact Hlc).
    assert (Hrb : forall b, revBitOf (sMem s2') b = revBitOf (sMem s2) b)
      by (intros b; apply revBitOf_ext; exact Hlc).
    unfold RevokerRel, RevAccRel, RevCapOK, RevWriteOK in *; rewrite Eacc, Eoff.
    revert H.
    destruct (g_acc g) as [| addr size pkt [[|]|[|]] | ld pkt0 [[|]|[|]|[|]|[|] rp|res]
                          | rc [[|]|[|]|[|]|[|] rp|res] | [[|]|[|]|[|]|[|] rp|res]
                          | [[|]|[|]|[|]|[|] rp|res] | addr pkt [[|]|[|]]];
      intros H; cbv beta iota in *;
      unfold iRevArch, iRevPhase, iRevScanCap, iRevScanBase, iRevSnoopHit, iScanAddr in *;
      rewrite HR, ?Hmv, ?Hrb; exact H.
  Qed.

  (* A step that changes only the region states (impl) and the spec memory, keeping the
   * ports, the impl revoker, the line contents and (monotonically) the fetch view *)
  Lemma RefRelG_regions_frame :
    forall g (s1 s1' : IState) (s2 s2' : SState) mi' ms',
      s1' = writeSubTreeState (Impl.np_mem pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions)
              s1 (mi' ,, (iMem s1).(Snd)) ->
      s2' = writeSubTreeState (Spec.np_mem pcAddrInit specRegions) s2 ms' ->
      (forall P, AllPorts P implRegions (iRegions s1') = AllPorts P implRegions (iRegions s1)) ->
      iRev s1' = iRev s1 ->
      (forall L, lineContent specRegions (sMem s2') L = lineContent specRegions (sMem s2) L) ->
      FetchViewExt specRegions (sMem s2) (sMem s2') ->
      MemRelC g s1' s2' -> LatchRel g s2' ->
      RefRelG g s1 s2 -> RefRelG g s1' s2'.
  Proof.
    intros g s1 s1' s2 s2' mi' ms' E1 E2 HP HR Hlc Hext Hmem Hlat H.
    destruct H as [Hrf Hm Hl Hrp He Ha Hc Hd Hf Hs Hfr Hw Hrk].
    pose proof (proj2 (proj2 Hm)) as Hsnap.
    assert (Hrw : forall rc, revWb (sMem s2') rc = revWb (sMem s2) rc)
      by (intros rc; apply revWb_ext; exact Hlc).
    assert (Edm : iDmSt s1' = iDmSt s1) by (rewrite E1; reflexivity).
    constructor.
    - rewrite E1, E2; exact Hrf.
    - exact Hmem.
    - exact Hlat.
    - unfold ReplayRel in *; intros G1 e G2 rfe Hg Hch.
      exact (FetchAllowedInst_fetchViewExt initLine fwcs specRegions _ _ _ _ Hsnap Hext (Hrp G1 e G2 rfe Hg Hch)).
    - rewrite E2; exact He.
    - refine (AccessRel_frame g s1 s1' s2 s2' HP HR _ _ _ Edm _ Hlc Ha);
        [rewrite E1 | rewrite E1 | rewrite E1 | rewrite E2]; reflexivity.
    - unfold CnwbRel in *; destruct Hc as [Hc1 Hc2]; rewrite Edm, Hrw; exact (conj Hc1 Hc2).
    - rewrite E1; exact Hd.
    - unfold FenceRel, NoFenceIWait in *; rewrite HP; rewrite E1; exact Hf.
    - rewrite E1; exact Hs.
    - unfold FrontRel in *.
      destruct Hfr as [F1 [F2 [F3 [F4 [F5 [F6 F7]]]]]].
      split; [rewrite E1; exact F1 |]; split; [rewrite E1; exact F2 |]; split; [rewrite E1; exact F3 |].
      split; [rewrite E1; exact F4 |]; split; [rewrite E1; exact F5 |].
      split.
      + unfold LiveChain in *.
        refine (LiveChainG_mono _ _ _ (FrontierRel s1 s2) _ _ _ Hsnap Hext _ _).
        * intros p Hp; rewrite E1; exact (FrontierRel_mono _ _ _ p Hsnap Hext Hp).
        * rewrite E1; exact F6.
      + unfold FetchRespRel in *; rewrite HP.
        revert F7; apply AllPorts_impl; intros r y HC; cbv zeta in HC |- *.
        destruct HC as [C [HC1 [HC2 HC3]]].
        exists C; split; [rewrite E1; exact HC1 | split; [exact HC2 |]].
        intros Hv; destruct (HC3 Hv) as [f [E' [HE Hl']]].
        exists f, E'; split; [rewrite E1; exact HE |].
        intros Hlive; rewrite E1 in Hlive.
        exact (LineAllowed_fetchViewExt initLine specRegions fwcs _ _ _ _ Hsnap Hext (Hl' Hlive)).
    - unfold WfRel in *; rewrite HP; rewrite E1; exact Hw.
    - exact (RevokerRel_frame g g s1 s1' s2 s2' eq_refl eq_refl HR Hlc Hrk).
  Qed.

  (* --- 16b. Steps While a fence.i Waits --- *)

  (* A region's spec part with its fetch subtree's fenceIWait and fenceIAck trace replaced *)
  Definition setAcksS (r : MemRegion) (x : TS (externalMemRegionTree r)) (w : bool) (a : list bool)
    : TS (externalMemRegionTree r) :=
    ((x.(Fst).(Fst) ,, (x.(Fst).(Snd).(Fst) ,, (w ,, (x.(Fst).(Snd).(Snd).(Snd).(Fst) ,,
       (a ,, x.(Fst).(Snd).(Snd).(Snd).(Snd).(Snd)))))) ,, x.(Snd)).

  Definition setAcksI (r : MemRegion) (y : TS (implExternalMemRegionTree r)) (w : bool) (a : list bool)
    : TS (implExternalMemRegionTree r) :=
    (setAcksS r y.(Fst) w a ,, y.(Snd)).

  (* A port predicate that reads neither fenceIWait nor the fenceIAck trace *)
  Definition AckInsensitive (P : forall r, TS (implExternalMemRegionTree r) -> Prop) : Prop :=
    forall r y w a, P r (setAcksI r y w a) = P r y.

  Lemma RegionPort_conj :
    forall (P Q : forall r, TS (implExternalMemRegionTree r) -> Prop) r (y : TS (implMemRegionTree r)),
      RegionPort P r y -> RegionPort Q r y -> RegionPort (fun r y => P r y /\ Q r y) r y.
  Proof.
    intros P Q r; unfold RegionPort, implMemRegionTree.
    destruct (regionKind r); intros y H1 H2; [exact (conj H1 H2) | exact I].
  Qed.

  Lemma AllPorts_conj :
    forall (P Q : forall r, TS (implExternalMemRegionTree r) -> Prop) l (mi : TS (implRegionsTree l)),
      AllPorts P l mi -> AllPorts Q l mi -> AllPorts (fun r y => P r y /\ Q r y) l mi.
  Proof.
    intros P Q l; induction l as [| r l IH]; intros mi HP HQ; cbn [AllPorts] in *; [exact I |].
    destruct HP as [HP0 HP1], HQ as [HQ0 HQ1].
    exact (conj (RegionPort_conj P Q r _ HP0 HQ0) (IH _ HP1 HQ1)).
  Qed.

  Lemma filter_all_false :
    forall {A : Type} (p : A -> bool) (l : list A), Forall (fun a => p a = false) l -> filter p l = [].
  Proof.
    intros A p l; induction l as [| a l IH]; intros H; [reflexivity |].
    inversion H as [| ? ? Ha Hl]; subst; cbn [filter]; rewrite Ha; exact (IH Hl).
  Qed.

  Lemma filter_combine_all_false :
    forall {A B : Type} (p : A -> bool) (l1 : list A) (l2 : list B),
      Forall (fun a => p a = false) l1 -> filter (fun ab => p (fst ab)) (combine l1 l2) = [].
  Proof.
    intros A B p l1; induction l1 as [| a l1 IH]; intros l2 H; [reflexivity |].
    destruct l2 as [| b l2]; [reflexivity |].
    inversion H as [| ? ? Ha Hl]; subst; cbn [combine filter fst]; rewrite Ha; exact (IH l2 Hl).
  Qed.

  Lemma liveInsts_noLive : forall g s1, NoLive s1 -> liveInsts g s1 = [].
  Proof.
    intros g s1 [N1 [N2 _]]; unfold liveInsts.
    rewrite (filter_combine_all_false (daLive s1) (iD2a s1) (g_d2aFo g) N1), (filter_all_false (aiLive s1) _ N2).
    reflexivity.
  Qed.

  Lemma FrontierRel_noStraddle :
    forall s1 s2 s2' fp, optValid (iStraddle s1) = false -> FrontierRel s1 s2 fp -> FrontierRel s1 s2' fp.
  Proof.
    intros s1 s2 s2' fp Hs H; unfold FrontierRel in *; cbv zeta in *; rewrite Hs in *; exact H.
  Qed.

  (* `AccessRel_frame` with only the four port views it reads *)
  Lemma AccessRel_frame_ports :
    forall g (s1 s1' : IState) (s2 s2' : SState),
      PortsQuiet s1' = PortsQuiet s1 ->
      (forall L, PortsReadStaged L s1' = PortsReadStaged L s1) ->
      (forall L, PortsReadOut L s1' = PortsReadOut L s1) ->
      (forall L rq, PortsWriteStaged L rq s1' = PortsWriteStaged L rq s1) ->
      iRev s1' = iRev s1 -> iMemSt s1' = iMemSt s1 -> iRdBufs s1' = iRdBufs s1 ->
      iRequester s1' = iRequester s1 -> iDmSt s1' = iDmSt s1 -> sSecond s2' = sSecond s2 ->
      (forall L, lineContent specRegions (sMem s2') L = lineContent specRegions (sMem s2) L) ->
      AccessRel g s1 s2 -> AccessRel g s1' s2'.
  Proof.
    intros g s1 s1' s2 s2' Q1 Q2 Q3 Q4 HR Emst Ebuf Ereq Edm Esec Hlc Ha.
    assert (Erp : iReadRp s1' = iReadRp s1) by exact (f_equal (fun b => b.(Fst)) Ebuf).
    assert (Erdy : iRpReady s1' = iRpReady s1) by exact (f_equal (fun b => b.(Snd).(Fst)) Ebuf).
    assert (Hslw : forall pl v, specLoadWb (sMem s2') pl v = specLoadWb (sMem s2) pl v)
      by (intros pl v; apply specLoadWb_ext; exact Hlc).
    assert (Hrw : forall rc, revWb (sMem s2') rc = revWb (sMem s2) rc)
      by (intros rc; apply revWb_ext; exact Hlc).
    assert (Hmv : forall a sz, memValAt (sMem s2') a sz = memValAt (sMem s2) a sz)
      by (intros a sz; apply memValAt_ext; exact Hlc).
    unfold AccessRel in *.
    revert Ha.
    destruct (g_acc g) as [| addr size pkt [[|]|[|]] | ld pkt0 [[|]|[|]|[|]|[|] rp|res]
                          | rc [[|]|[|]|[|]|[|] rp|res] | [[|]|[|]|[|]|[|] rp|res]
                          | [[|]|[|]|[|]|[|] rp|res] | addr pkt [[|]|[|]]];
      intros Ha.
    (* one step per sentence over the 45 cases (compile speed) *)
    all: unfold WrStageRel, RdStageRel, revNotReading, dmNotAccessing, iRevPhase, iScanAddr, iRevScanBase,
           iScanMsb, iRevSnoopHit in *.
    all: cbv beta iota zeta in *.
    all: rewrite ?Q1, ?Q2, ?Q3, ?Q4, ?HR, ?Hrw, ?Hmv, ?Emst, ?Erp, ?Erdy, ?Ereq, ?Edm, ?Esec.
    all: try (lazymatch goal with |- context [specLoadWb] => setoid_rewrite Hslw end).
    all: exact Ha.
  Qed.

  (* A step that changes only the region states (impl) and the spec memory while some
   * fenceIWait is set: then no instruction is live or pending and no straddle waits
   * (`FenceRel`), so the fetch view of the spec memory is not read *)
  Lemma RefRelG_wait_frame :
    forall g (s1 s1' : IState) (s2 s2' : SState) mi' ms',
      s1' = writeSubTreeState (Impl.np_mem pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions)
              s1 (mi' ,, (iMem s1).(Snd)) ->
      s2' = writeSubTreeState (Spec.np_mem pcAddrInit specRegions) s2 ms' ->
      ~ NoFenceIWait s1 ->
      (forall P, AckInsensitive P -> AllPorts P implRegions (iRegions s1') = AllPorts P implRegions (iRegions s1)) ->
      iRev s1' = iRev s1 ->
      (forall L, lineContent specRegions (sMem s2') L = lineContent specRegions (sMem s2) L) ->
      AllPorts (fun r y => RegionFenceICountInv r y.(Fst)) implRegions (iRegions s1') ->
      MemRelC g s1' s2' -> LatchRel g s2' ->
      RefRelG g s1 s2 -> RefRelG g s1' s2'.
  Proof.
    intros g s1 s1' s2 s2' mi' ms' E1 E2 Hq HP HR Hlc Hfc Hmem Hlat H.
    destruct H as [Hrf Hm Hl Hrp He Ha Hc Hd Hf Hs Hfr Hw Hrk].
    destruct (proj1 (proj2 Hf) Hq) as [Hpend [Hnl [Hstr Hnone]]].
    assert (Hrw : forall rc, revWb (sMem s2') rc = revWb (sMem s2) rc)
      by (intros rc; apply revWb_ext; exact Hlc).
    assert (Edm : iDmSt s1' = iDmSt s1) by (rewrite E1; reflexivity).
    constructor.
    - rewrite E1, E2; exact Hrf.
    - exact Hmem.
    - exact Hlat.
    - unfold ReplayRel; intros G1 e G2 rfe Hg _.
      exfalso; apply (Hnone e); rewrite Hg; apply in_or_app; right; left; reflexivity.
    - rewrite E2; exact He.
    - refine (AccessRel_frame_ports g s1 s1' s2 s2' _ _ _ _ HR _ _ _ Edm _ Hlc Ha).
      + unfold PortsQuiet; apply HP; intros r y w a; reflexivity.
      + intros L; unfold PortsReadStaged; apply HP; intros r y w a; reflexivity.
      + intros L; unfold PortsReadOut; apply HP; intros r y w a; reflexivity.
      + intros L rq; unfold PortsWriteStaged; apply HP; intros r y w a; reflexivity.
      + rewrite E1; reflexivity.
      + rewrite E1; reflexivity.
      + rewrite E1; reflexivity.
      + rewrite E2; reflexivity.
    - unfold CnwbRel in *; destruct Hc as [Hc1 Hc2]; rewrite Edm, Hrw; exact (conj Hc1 Hc2).
    - rewrite E1; exact Hd.
    - unfold FenceRel; split; [| split].
      + rewrite E1; exact (proj1 Hf).
      + intros _; rewrite E1; exact (conj Hpend (conj Hnl (conj Hstr Hnone))).
      + rewrite E1; exact (proj2 (proj2 Hf)).
    - rewrite E1; exact Hs.
    - unfold FrontRel in *.
      destruct Hfr as [F1 [F2 [F3 [F4 [F5 [F6 F7]]]]]].
      split; [rewrite E1; exact F1 |]; split; [rewrite E1; exact F2 |]; split; [rewrite E1; exact F3 |].
      split; [rewrite E1; exact F4 |]; split; [rewrite E1; exact F5 |].
      split.
      + unfold LiveChain in *.
        assert (Hlv' : liveInsts g s1' = []) by (rewrite E1; exact (liveInsts_noLive g s1 Hnl)).
        rewrite Hlv'; rewrite (liveInsts_noLive g s1 Hnl) in F6; cbn [LiveChainG] in F6 |- *.
        pose proof (FrontierRel_noStraddle s1 s2 s2' _ Hstr F6) as F6'.
        rewrite E1; exact F6'.
      + unfold FetchRespRel in *.
        rewrite HP by (intros r y w a; reflexivity).
        revert F7; apply AllPorts_impl; intros r y HC; cbv zeta in HC |- *.
        destruct HC as [C [HC1 [HC2 HC3]]].
        exists C; split; [rewrite E1; exact HC1 | split; [exact HC2 |]].
        intros Hv; destruct (HC3 Hv) as [f [E' [HE _]]].
        exists f, E'; split; [rewrite E1; exact HE |].
        intros Hlv; exfalso.
        assert (Hin : In f (iFetchBuf s1)).
        { assert (Hin0 : In f (fbInRegion s1 r)) by (rewrite HE; left; reflexivity).
          unfold fbInRegion in Hin0; apply filter_In in Hin0; exact (proj1 Hin0). }
        destruct Hnl as [_ [_ Hfb]]; rewrite Forall_forall in Hfb.
        rewrite E1 in Hlv; change (fbLive s1 f = true) in Hlv.
        rewrite (Hfb f Hin) in Hlv; discriminate Hlv.
    - unfold WfRel in *.
      destruct Hw as [W1 [W2 [W3 [W4 [Wmd W5]]]]].
      split; [rewrite E1; exact W1 |]; split; [rewrite E1; exact W2 |]; split; [rewrite E1; exact W3 |].
      split; [rewrite E1; exact W4 |]; split; [rewrite E1; exact Wmd |].
      refine (AllPorts_conj (fun r y => ImplExternalRegionHandshakeInv r y) _ _ _ _ Hfc).
      rewrite HP by (intros r y w a; reflexivity).
      revert W5; apply AllPorts_impl; intros r y [Hy _]; exact Hy.
    - exact (RevokerRel_frame g g s1 s1' s2 s2' eq_refl eq_refl HR Hlc Hrk).
  Qed.

  (* A step that changes only the impl memory subtree, the spec memory, the access in flight and
   * the revoker offset, keeping the ports, the line contents and (monotonically) the fetch view.
   * The caller re-establishes the components that read what changed. *)
  Lemma RefRelG_mem_frame :
    forall g g' (s1 s1' : IState) (s2 s2' : SState) mi' ms',
      s1' = writeSubTreeState (Impl.np_mem pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions) s1 mi' ->
      s2' = writeSubTreeState (Spec.np_mem pcAddrInit specRegions) s2 ms' ->
      g_chain g' = g_chain g -> g_rf0 g' = g_rf0 g -> g_cnwb g' = g_cnwb g -> g_d2aFo g' = g_d2aFo g ->
      accTakesHead (g_acc g') = accTakesHead (g_acc g) ->
      (forall P, AllPorts P implRegions (iRegions s1') = AllPorts P implRegions (iRegions s1)) ->
      (forall L, lineContent specRegions (sMem s2') L = lineContent specRegions (sMem s2) L) ->
      FetchViewExt specRegions (sMem s2) (sMem s2') ->
      MemRelC g' s1' s2' -> LatchRel g' s2' -> AccessRel g' s1' s2' -> RevokerRel g' s1' s2' ->
      RefRelG g s1 s2 -> RefRelG g' s1' s2'.
  Proof.
    intros g g' s1 s1' s2 s2' mi' ms' E1 E2 Ech Erf Ecn Ed2a Eacc HP Hlc Hext Hmem Hlat Hacc Hrev H.
    destruct H as [Hrf Hm Hl Hrp He Ha Hc Hd Hf Hs Hfr Hw Hrk].
    pose proof (proj2 (proj2 Hm)) as Hsnap.
    assert (Hrw : forall rc, revWb (sMem s2') rc = revWb (sMem s2) rc)
      by (intros rc; apply revWb_ext; exact Hlc).
    assert (Edm : iDmSt s1' = iDmSt s1) by (rewrite E1; reflexivity).
    constructor.
    - unfold RfRel in *; rewrite Ech, Erf, Ecn; rewrite E1, E2; exact Hrf.
    - exact Hmem.
    - exact Hlat.
    - unfold ReplayRel in *; rewrite Ech, Erf; intros G1 e G2 rfe Hg Hch.
      exact (FetchAllowedInst_fetchViewExt initLine fwcs specRegions _ _ _ _ Hsnap Hext (Hrp G1 e G2 rfe Hg Hch)).
    - unfold EagerRel in *; rewrite Ech; rewrite E2; exact He.
    - exact Hacc.
    - unfold CnwbRel in *; rewrite Ecn, Ech, Eacc; destruct Hc as [Hc1 Hc2]; rewrite Edm, Hrw; exact (conj Hc1 Hc2).
    - unfold DmQueueRel in *; rewrite Ech, Eacc; rewrite E1; exact Hd.
    - unfold FenceRel, NoFenceIWait in *; rewrite Ech, HP; rewrite E1; exact Hf.
    - unfold ScoreRel in *; rewrite Ed2a; rewrite E1; exact Hs.
    - unfold FrontRel in *.
      destruct Hfr as [F1 [F2 [F3 [F4 [F5 [F6 F7]]]]]].
      split; [rewrite E1; exact F1 |]; split; [rewrite E1; exact F2 |]; split; [rewrite E1; exact F3 |].
      split; [rewrite E1; exact F4 |]; split; [rewrite E1; exact F5 |].
      split.
      + unfold LiveChain, liveInsts in *; rewrite Ed2a.
        refine (LiveChainG_mono _ _ _ (FrontierRel s1 s2) _ _ _ Hsnap Hext _ _).
        * intros p Hp; rewrite E1; exact (FrontierRel_mono _ _ _ p Hsnap Hext Hp).
        * rewrite E1; exact F6.
      + unfold FetchRespRel in *; rewrite HP.
        revert F7; apply AllPorts_impl; intros r y HC; cbv zeta in HC |- *.
        destruct HC as [C [HC1 [HC2 HC3]]].
        exists C; split; [rewrite E1; exact HC1 | split; [exact HC2 |]].
        intros Hv; destruct (HC3 Hv) as [f [E' [HE Hl']]].
        exists f, E'; split; [rewrite E1; exact HE |].
        intros Hlive; rewrite E1 in Hlive.
        exact (LineAllowed_fetchViewExt initLine specRegions fwcs _ _ _ _ Hsnap Hext (Hl' Hlive)).
    - unfold WfRel in *; rewrite HP; rewrite E1; exact Hw.
    - exact Hrev.
  Qed.

  (* A port predicate that reads neither the data requests, their readies, the writes nor
   * `portRq`: the request ports leave it unchanged *)
  Definition RqInsensitive (P : forall r, TS (implExternalMemRegionTree r) -> Prop) : Prop :=
    forall r (y y' : TS (implExternalMemRegionTree r)),
      y'.(Fst).(Fst) = y.(Fst).(Fst) -> y'.(Fst).(Snd).(Snd).(Fst) = y.(Fst).(Snd).(Snd).(Fst) ->
      y'.(Snd).(Fst) = y.(Snd).(Fst) ->
      y'.(Snd).(Snd).(Snd).(Snd).(Fst) = y.(Snd).(Snd).(Snd).(Snd).(Fst) ->
      y'.(Snd).(Snd).(Snd).(Snd).(Snd).(Fst) = y.(Snd).(Snd).(Snd).(Snd).(Snd).(Fst) ->
      P r y' = P r y.

  Local Ltac rqins_tac :=
    let r0 := fresh "r" in let y0 := fresh "y" in let y1 := fresh "y" in
    intros r0 y0 y1 Q1 Q2 Q3 Q4 Q5; cbv beta zeta;
    unfold implFetchAccRqs, ImplExternalRegionHandshakeInv, RegionFenceICountInv;
    rewrite ?Q1, ?Q2, ?Q3, ?Q4, ?Q5; reflexivity.

  (* `RefRelG_mem_frame` for the request ports: only the port predicates that ignore the data
   * requests and `portRq` must be unchanged *)
    Lemma RefRelG_rq_frame :
    forall g g' (s1 s1' : IState) (s2 s2' : SState) mi' ms',
      s1' = writeSubTreeState (Impl.np_mem pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                                 mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions) s1 mi' ->
      s2' = writeSubTreeState (Spec.np_mem pcAddrInit specRegions) s2 ms' ->
      g_chain g' = g_chain g -> g_rf0 g' = g_rf0 g -> g_cnwb g' = g_cnwb g -> g_d2aFo g' = g_d2aFo g ->
      accTakesHead (g_acc g') = accTakesHead (g_acc g) ->
      (forall P, RqInsensitive P -> AllPorts P implRegions (iRegions s1') = AllPorts P implRegions (iRegions s1)) ->
      (forall L, lineContent specRegions (sMem s2') L = lineContent specRegions (sMem s2) L) ->
      FetchViewExt specRegions (sMem s2) (sMem s2') ->
      MemRelC g' s1' s2' -> LatchRel g' s2' -> AccessRel g' s1' s2' -> RevokerRel g' s1' s2' ->
      RefRelG g s1 s2 -> RefRelG g' s1' s2'.
  Proof.
    intros g g' s1 s1' s2 s2' mi' ms' E1 E2 Ech Erf Ecn Ed2a Eacc HP Hlc Hext Hmem Hlat Hacc Hrev H.
    destruct H as [Hrf Hm Hl Hrp He Ha Hc Hd Hf Hs Hfr Hw Hrk].
    pose proof (proj2 (proj2 Hm)) as Hsnap.
    assert (Hrw : forall rc, revWb (sMem s2') rc = revWb (sMem s2) rc)
      by (intros rc; apply revWb_ext; exact Hlc).
    assert (Edm : iDmSt s1' = iDmSt s1) by (rewrite E1; reflexivity).
    constructor.
    - unfold RfRel in *; rewrite Ech, Erf, Ecn; rewrite E1, E2; exact Hrf.
    - exact Hmem.
    - exact Hlat.
    - unfold ReplayRel in *; rewrite Ech, Erf; intros G1 e G2 rfe Hg Hch.
      exact (FetchAllowedInst_fetchViewExt initLine fwcs specRegions _ _ _ _ Hsnap Hext (Hrp G1 e G2 rfe Hg Hch)).
    - unfold EagerRel in *; rewrite Ech; rewrite E2; exact He.
    - exact Hacc.
    - unfold CnwbRel in *; rewrite Ecn, Ech, Eacc; destruct Hc as [Hc1 Hc2]; rewrite Edm, Hrw; exact (conj Hc1 Hc2).
    - unfold DmQueueRel in *; rewrite Ech, Eacc; rewrite E1; exact Hd.
    - unfold FenceRel, NoFenceIWait in *; rewrite Ech, HP by rqins_tac; rewrite E1; exact Hf.
    - unfold ScoreRel in *; rewrite Ed2a; rewrite E1; exact Hs.
    - unfold FrontRel in *.
      destruct Hfr as [F1 [F2 [F3 [F4 [F5 [F6 F7]]]]]].
      split; [rewrite E1; exact F1 |]; split; [rewrite E1; exact F2 |]; split; [rewrite E1; exact F3 |].
      split; [rewrite E1; exact F4 |]; split; [rewrite E1; exact F5 |].
      split.
      + unfold LiveChain, liveInsts in *; rewrite Ed2a.
        refine (LiveChainG_mono _ _ _ (FrontierRel s1 s2) _ _ _ Hsnap Hext _ _).
        * intros p Hp; rewrite E1; exact (FrontierRel_mono _ _ _ p Hsnap Hext Hp).
        * rewrite E1; exact F6.
      + unfold FetchRespRel in *; rewrite HP by rqins_tac.
        revert F7; apply AllPorts_impl; intros r y HC; cbv zeta in HC |- *.
        destruct HC as [C [HC1 [HC2 HC3]]].
        exists C; split; [rewrite E1; exact HC1 | split; [exact HC2 |]].
        intros Hv; destruct (HC3 Hv) as [f [E' [HE Hl']]].
        exists f, E'; split; [rewrite E1; exact HE |].
        intros Hlive; rewrite E1 in Hlive.
        exact (LineAllowed_fetchViewExt initLine specRegions fwcs _ _ _ _ Hsnap Hext (Hl' Hlive)).
    - unfold WfRel in *; rewrite HP by rqins_tac; rewrite E1; exact Hw.
    - exact Hrev.
  Qed.

  (* --- 17. The mcycle Tick --- *)

  Lemma flushMulDivCaps_incr :
    forall entries rf,
      flushMulDivCaps pcAddrInit entries (evalIncrementMcycle pcAddrInit rf) =
      evalIncrementMcycle pcAddrInit (flushMulDivCaps pcAddrInit entries rf).
  Proof.
    induction entries as [| [m c] rest IH]; intros rf; cbn [flushMulDivCaps]; [reflexivity |].
    rewrite <- evalIncrementMcycle_writeGprVal; apply IH.
  Qed.

  Lemma evalRegRead_incr :
    forall regReadIn rf,
      evalRegRead pcAddrInit regReadIn (evalIncrementMcycle pcAddrInit rf) =
      evalRegRead pcAddrInit regReadIn rf.
  Proof.
    intros regReadIn rf; unfold evalRegRead.
    pose proof (fun i => readGpr_evalIncrementMcycle pcAddrInit i rf) as H; unfold readGpr in H.
    rewrite !H; reflexivity.
  Qed.

  Lemma readPcc_incr :
    forall rf, readPcc pcAddrInit (evalIncrementMcycle pcAddrInit rf) = readPcc pcAddrInit rf.
  Proof.
    intros rf; unfold readPcc; apply readGpr_evalIncrementMcycle.
  Qed.

  Lemma cnwbApply_incr :
    forall c rf, evalIncrementMcycle pcAddrInit (cnwbApply c rf) = cnwbApply c (evalIncrementMcycle pcAddrInit rf).
  Proof.
    intros [[d v] |] rf; cbn [cnwbApply]; [apply evalIncrementMcycle_writeGprVal | reflexivity].
  Qed.

  Lemma snoc_tick_split :
    forall (G G1 G2 : list GItemT) e,
      (G ++ [GTick])%list = (G1 ++ GInst e :: G2)%list ->
      exists G2', G2 = (G2' ++ [GTick])%list /\ G = (G1 ++ GInst e :: G2')%list.
  Proof.
    intros G G1 G2 e H.
    induction G2 as [| x G2 _] using rev_ind.
    - apply app_inj_tail in H as [_ H]; discriminate H.
    - rewrite app_comm_cons, app_assoc in H.
      apply app_inj_tail in H as [H1 H2]; subst x.
      exists G2; split; [reflexivity | exact H1].
  Qed.

  Lemma chainReqs_snoc_tick : forall G, chainReqs (G ++ [GTick]) = chainReqs G.
  Proof.
    intros G; unfold chainReqs; rewrite flat_map_app; cbn [flat_map]; rewrite app_nil_r; reflexivity.
  Qed.

  (* The access in flight depends on the ghost only through these fields and the head *)
  Lemma AccessRel_ghost :
    forall g g' (s1 : IState) (s2 : SState),
      g_acc g' = g_acc g -> g_revOff g' = g_revOff g -> g_cnwb g' = g_cnwb g ->
      (forall q, HeadReq g q -> HeadReq g' q) ->
      AccessRel g s1 s2 -> AccessRel g' s1 s2.
  Proof.
    intros g g' s1 s2 Eacc Erev Ecnwb HH Ha.
    unfold AccessRel in *; rewrite Eacc, Erev, Ecnwb.
    revert Ha.
    destruct (g_acc g) as [| addr size pkt [[|]|[|]] | ld pkt0 [[|]|[|]|[|]|[|] rp|res]
                          | rc [[|]|[|]|[|]|[|] rp|res] | [[|]|[|]|[|]|[|] rp|res]
                          | [[|]|[|]|[|]|[|] rp|res] | addr pkt [[|]|[|]]];
      intros Ha; cbv beta iota zeta in *;
      (let rec go H :=
         lazymatch type of H with
         | _ /\ _ =>
             let H1 := fresh "H" in let H2 := fresh "H" in
             destruct H as [H1 H2]; split; [go H1 | go H2]
         | exists q, HeadReq _ q /\ _ =>
             let q := fresh "q" in let Hq := fresh "Hq" in
             destruct H as [q Hq]; exists q; go Hq
         | HeadReq _ ?q => exact (HH q H)
         | _ => exact H
         end in
       go Ha).
  Qed.

  Local Abbreviation NPRF :=
    (Impl.np_rf pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
                mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions).

  (* Common part of the two tick cases: everything but the chain-dependent components *)
  Lemma tick_impl_facts :
    forall (s1 s1' : IState),
      s1' = writeSubTreeState NPRF s1 (evalIncrementMcycle pcAddrInit (iRf s1)) ->
      iFlush s1' = evalIncrementMcycle pcAddrInit (iFlush s1) /\ iPcc s1' = iPcc s1.
  Proof.
    intros s1 s1' E1; split.
    - rewrite E1; unfold iFlush, flushMulDiv, flushMulDivOn; apply flushMulDivCaps_incr.
    - rewrite E1; unfold iPcc; exact (readPcc_incr (iRf s1)).
  Qed.

  Lemma ScoreRel_tick :
    forall g g' (s1 s1' : IState),
      s1' = writeSubTreeState NPRF s1 (evalIncrementMcycle pcAddrInit (iRf s1)) ->
      g_d2aFo g' = g_d2aFo g ->
      ScoreRel g s1 -> ScoreRel g' s1'.
  Proof.
    intros g g' s1 s1' E1 Ed Hs.
    destruct (tick_impl_facts s1 s1' E1) as [Hflush _].
    unfold ScoreRel in *; rewrite Ed; cbv zeta in *.
    destruct Hs as [S1 [S2 [S3 S4]]].
    split; [rewrite E1; exact S1 |]; split; [rewrite E1; exact S2 |]; split; [rewrite E1; exact S3 |].
    intros l1 j l2 fo Hd2a Hnth Hlive.
    rewrite Hflush, evalRegRead_incr.
    rewrite E1 in Hd2a, Hlive |- *.
    exact (S4 l1 j l2 fo Hd2a Hnth Hlive).
  Qed.

  Lemma FrontRel_tick :
    forall g g' (s1 s1' : IState) (s2 : SState),
      s1' = writeSubTreeState NPRF s1 (evalIncrementMcycle pcAddrInit (iRf s1)) ->
      g_d2aFo g' = g_d2aFo g ->
      SnapshotOK fwcs specRegions (sMem s2) ->
      FrontRel g s1 s2 -> FrontRel g' s1' s2.
  Proof.
    intros g g' s1 s1' s2 E1 Ed Hsnap Hfr.
    destruct (tick_impl_facts s1 s1' E1) as [_ Hpcc].
    unfold FrontRel in *.
    destruct Hfr as [F1 [F2 [F3 [F4 [F5 [F6 F7]]]]]].
    split; [rewrite E1; exact F1 |]; split; [rewrite E1; exact F2 |]; split; [rewrite E1; exact F3 |].
    split; [rewrite E1; exact F4 |]; split; [rewrite E1; exact F5 |].
    split.
    - unfold LiveChain in *; rewrite Hpcc.
      unfold liveInsts in *; rewrite Ed.
      refine (LiveChainG_mono _ _ _ (FrontierRel s1 s2) _ _ _ Hsnap (FetchViewExt_refl _ _) _ _).
      + intros p Hp; unfold FrontierRel in *; cbv zeta in *; rewrite Hpcc; rewrite E1; exact Hp.
      + rewrite E1; exact F6.
    - rewrite E1; exact F7.
  Qed.

  (* Tick with entries pending: the spec stutters and the chain records the tick *)
  Lemma RefRelG_tick_ghost :
    forall g (s1 s1' : IState) (s2 : SState),
      s1' = writeSubTreeState NPRF s1 (evalIncrementMcycle pcAddrInit (iRf s1)) ->
      g_chain g <> [] ->
      RefRelG g s1 s2 ->
      RefRelG (mkGhost (g_chain g ++ [GTick]) (g_rf0 g) (g_cnwb g) (g_revOff g) (g_d2aFo g) (g_acc g)) s1' s2.
  Proof.
    intros g s1 s1' s2 E1 Hne H.
    destruct (tick_impl_facts s1 s1' E1) as [Hflush Hpcc].
    destruct H as [Hrf Hm Hl Hrp He Ha Hc Hd Hf Hs Hfr Hw Hrk].
    constructor.
    - unfold RfRel in *; cbn [g_chain g_rf0 g_cnwb] in *.
      destruct Hrf as [R1 [R2 [R3 R4]]].
      split; [exact R1 |].
      split; [rewrite Hflush; exact (GChain_snoc_tick pcAddrInit _ _ _ R2) |].
      split.
      + intros d v Hcn; apply ChainAvoids_app; [exact (R3 d v Hcn) |].
        intros e [Hin | []]; discriminate Hin.
      + intros G1 e G2 HG Hld.
        destruct (snoc_tick_split _ _ _ _ HG) as [G2' [-> HG']].
        apply ChainAvoids_app; [exact (R4 G1 e G2' HG' Hld) |].
        intros e' [Hin | []]; discriminate Hin.
    - rewrite E1; exact Hm.
    - unfold LatchRel in *; cbn [g_chain]; intros e Hin; apply Hl.
      apply in_app_or in Hin as [Hin | [Hin | []]]; [exact Hin | discriminate Hin].
    - unfold ReplayRel in *; cbn [g_chain g_rf0]; intros G1 e G2 rfe HG Hch.
      destruct (snoc_tick_split _ _ _ _ HG) as [G2' [_ HG']].
      exact (Hrp G1 e G2' rfe HG' Hch).
    - unfold EagerRel in *; cbn [g_chain].
      destruct He as [He | [e [G' [HG Hb]]]]; [contradiction |].
      right; exists e, (G' ++ [GTick])%list; split; [rewrite HG; reflexivity | exact Hb].
    - eapply AccessRel_ghost with (g := g); [reflexivity | reflexivity | reflexivity | | rewrite E1; exact Ha].
      intros q [e [G' [HG Hq]]]; exists e, (G' ++ [GTick])%list; split; [cbn [g_chain]; rewrite HG; reflexivity | exact Hq].
    - unfold CnwbRel in *; cbn [g_chain g_cnwb g_acc]; rewrite E1.
      destruct Hc as [C1 [C2 [C3 C4]]]; split; [exact C1 | split; [exact C2 | split; [exact C3 |]]].
      intros Hlr Hcn Hat; apply ChainAvoids_app; [exact (C4 Hlr Hcn Hat) |].
      intros e [Hin | []]; discriminate Hin.
    - unfold DmQueueRel in *; cbn [g_chain g_acc]; rewrite chainReqs_snoc_tick; rewrite E1; exact Hd.
    - unfold FenceRel in *; cbn [g_chain].
      destruct Hf as [Hf1 [Hf2 Hf3]]; split; [| split].
      + intros Hp; rewrite E1 in Hp; destruct (Hf1 Hp) as [Hnl [Hst [G1 [e [G2 [HG [Hfi HF]]]]]]].
        rewrite E1; split; [exact Hnl | split; [exact Hst |]].
        exists G1, e, (G2 ++ [GTick])%list; split; [rewrite HG, <- app_assoc; reflexivity |].
        split; [exact Hfi | apply Forall_app; split; [exact HF | constructor; [reflexivity | constructor]]].
      + intros Hw'; rewrite E1 in Hw'; destruct (Hf2 Hw') as [Hp [Hnl [Hst Hno]]].
        rewrite E1; split; [exact Hp | split; [exact Hnl | split; [exact Hst |]]].
        intros e Hin; apply in_app_or in Hin as [Hin | [Hin | []]]; [exact (Hno e Hin) | discriminate Hin].
      + intros G1 e G2 HG Hfi; rewrite E1.
        destruct (chain_snoc_split _ G1 G2 GTick (GInst e) HG ltac:(discriminate)) as [G2' [-> HG']].
        destruct (Hf3 G1 e G2' HG' Hfi) as [Hp HF]; split; [exact Hp |].
        apply Forall_app; split; [exact HF | constructor; [reflexivity | constructor]].
    - eapply ScoreRel_tick; [exact E1 | reflexivity | exact Hs].
    - eapply FrontRel_tick; [exact E1 | reflexivity | exact (proj2 (proj2 Hm)) | exact Hfr].
    - rewrite E1; exact Hw.
    - refine (RevokerRel_frame g _ s1 s1' s2 s2 eq_refl eq_refl _ (fun L => eq_refl) Hrk); rewrite E1; reflexivity.
  Qed.

  Local Abbreviation NPRFS := (Spec.np_rf pcAddrInit specRegions).

  (* Tick with no entry pending: lockstep with the spec tick *)
  Lemma RefRelG_tick_lockstep :
    forall g (s1 s1' : IState) (s2 s2' : SState),
      s1' = writeSubTreeState NPRF s1 (evalIncrementMcycle pcAddrInit (iRf s1)) ->
      s2' = writeSubTreeState NPRFS s2 (evalIncrementMcycle pcAddrInit (sRf s2)) ->
      g_chain g = [] ->
      RefRelG g s1 s2 ->
      RefRelG (mkGhost [] (evalIncrementMcycle pcAddrInit (g_rf0 g)) (g_cnwb g) (g_revOff g) (g_d2aFo g) (g_acc g))
        s1' s2'.
  Proof.
    intros g s1 s1' s2 s2' E1 E2 Hnil H.
    destruct (tick_impl_facts s1 s1' E1) as [Hflush Hpcc].
    destruct H as [Hrf Hm Hl Hrp He Ha Hc Hd Hf Hs Hfr Hw Hrk].
    assert (Hsec : sSecond s2' = sSecond s2) by (rewrite E2; reflexivity).
    assert (Hsm : sMem s2' = sMem s2) by (rewrite E2; reflexivity).
    constructor.
    - unfold RfRel in *; cbn [g_chain g_rf0 g_cnwb] in *.
      destruct Hrf as [R1 [R2 [R3 R4]]].
      rewrite Hnil in R2; apply GChain_nil_inv in R2.
      split; [rewrite E2; change (evalIncrementMcycle pcAddrInit (sRf s2) =
                                   cnwbApply (g_cnwb g) (evalIncrementMcycle pcAddrInit (g_rf0 g)));
              rewrite R1; apply cnwbApply_incr |].
      split; [rewrite Hflush, R2; apply GChainNil |].
      split; [intros d v _ e [] |].
      intros G1 e G2 HG; destruct G1; discriminate HG.
    - rewrite E1, E2; exact Hm.
    - unfold LatchRel; cbn [g_chain]; intros e [].
    - unfold ReplayRel; cbn [g_chain]; intros G1 e G2 rfe HG; destruct G1; discriminate HG.
    - left; reflexivity.
    - eapply AccessRel_ghost with (g := g); [reflexivity | reflexivity | reflexivity | |].
      + intros q [e [G' [HG _]]]; rewrite Hnil in HG; discriminate HG.
      + refine (AccessRel_frame g s1 s1' s2 s2' _ _ _ _ _ _ Hsec _ Ha);
          [intros P | | | | | | intros L; rewrite Hsm]; rewrite ?E1; reflexivity.
    - unfold CnwbRel in *; cbn [g_chain g_cnwb g_acc]; rewrite E1, E2.
      destruct Hc as [C1 [C2 [C3 _]]]; split; [exact C1 | split; [exact C2 | split; [exact C3 |]]].
      intros _ _ _ e [].
    - unfold DmQueueRel in *; cbn [g_chain g_acc]; rewrite Hnil in Hd; rewrite E1; exact Hd.
    - unfold FenceRel in *; cbn [g_chain]; rewrite Hnil in Hf; rewrite E1; exact Hf.
    - eapply ScoreRel_tick; [exact E1 | reflexivity | exact Hs].
    - rewrite E2; eapply FrontRel_tick; [exact E1 | reflexivity | exact (proj2 (proj2 Hm)) | exact Hfr].
    - rewrite E1; exact Hw.
    - refine (RevokerRel_frame g _ s1 s1' s2 s2' eq_refl eq_refl _ _ Hrk);
        [rewrite E1; reflexivity | intros L; rewrite Hsm; reflexivity].
  Qed.

  (* --- 18. Replaying the Head of the Chain --- *)

  (* The relation without `EagerRel`: it holds while the spec replays the head items of the chain
   * (one `specTickCycle` or `specStep` each) until `EagerRel` holds again *)
  Record RefRelNE (g : Ghost) (s1 : IState) (s2 : SState) : Prop := {
    ne_rf     : RfRel g s1 s2 ;
    ne_mem    : MemRelC g s1 s2 ;
    ne_latch  : LatchRel g s2 ;
    ne_replay : ReplayRel g s2 ;
    ne_acc    : AccessRel g s1 s2 ;
    ne_cnwb   : CnwbRel g s1 s2 ;
    ne_dmq    : DmQueueRel g s1 ;
    ne_fence  : FenceRel g s1 ;
    ne_score  : ScoreRel g s1 ;
    ne_front  : FrontRel g s1 s2 ;
    ne_wf     : WfRel g s1 s2 ;
    ne_rev    : RevokerRel g s1 s2
  }.

  Lemma RefRelNE_of_G : forall g s1 s2, RefRelG g s1 s2 -> RefRelNE g s1 s2.
  Proof. intros g s1 s2 []; constructor; assumption. Qed.

  Lemma RefRelG_of_NE : forall g s1 s2, RefRelNE g s1 s2 -> EagerRel g s2 -> RefRelG g s1 s2.
  Proof. intros g s1 s2 [] He; constructor; assumption. Qed.

  (* One item of the chain: a tick or an instruction step *)
  Definition ItemStep (rf0 rf1 : RfSt) (it : GItemT) : Prop :=
    match it with
    | GTick => rf1 = evalIncrementMcycle pcAddrInit rf0
    | GInst e => GInstStep pcAddrInit rf0 rf1 e
    end.

  Lemma GChain_cons_inv :
    forall rf0 it G rf', GChain pcAddrInit rf0 (it :: G) rf' ->
      exists rf1, ItemStep rf0 rf1 it /\ GChain pcAddrInit rf1 G rf'.
  Proof.
    intros rf0 it G rf' H.
    inversion H as [| rf G0 rf'' Ht | rf0' rf1 e G0 rf'' Hs Hr]; subst.
    - exists (evalIncrementMcycle pcAddrInit rf0); split; [reflexivity | exact Ht].
    - exists rf1; split; [exact Hs | exact Hr].
  Qed.

  Lemma GChain_cons :
    forall rf0 rf1 it G rf',
      ItemStep rf0 rf1 it -> GChain pcAddrInit rf1 G rf' -> GChain pcAddrInit rf0 (it :: G) rf'.
  Proof.
    intros rf0 rf1 [| e] G rf' Hs H; cbn [ItemStep] in Hs.
    - subst rf1; apply GChainTick; exact H.
    - eapply GChainInst; [exact Hs | exact H].
  Qed.

  (* The items the spec replays as soon as they reach the head: ticks, ALU entries, plain fences *)
  Definition itemNonBlocking (it : GItemT) : bool :=
    match it with GTick => true | GInst e => negb (entryBlocking e) end.

  Lemma nonBlocking_noMem :
    forall e q, entryBlocking e = false -> entryReq e = Some q ->
      opIsMem (mrOp q) = false /\ opIsFenceI (mrOp q) = false.
  Proof.
    intros e q Hb Hq; unfold entryBlocking in Hb; rewrite Hq in Hb; unfold isPlainFence in Hb.
    revert Hb; destruct (opIsMem (mrOp q)), (opIsFenceI (mrOp q)); cbn; intros Hb;
      first [discriminate Hb | split; reflexivity].
  Qed.

  Lemma nonBlocking_dm :
    forall e, entryBlocking e = false -> optValid (ge_dm e) = true ->
      opIsMem (optData (ge_dm e)) = false /\ opIsFenceI (optData (ge_dm e)) = false.
  Proof.
    intros e Hb Hv.
    assert (Hq : entryReq e = Some (aluDstIdx (ge_aluOut e) ,,
                                    ((aluDstVal (ge_aluOut e)).(Snd).(Snd).(Fst) ,, (optData (ge_dm e) ,, tt))))
      by (unfold entryReq; rewrite Hv; reflexivity).
    exact (nonBlocking_noMem e _ Hb Hq).
  Qed.

  (* The ghost after the spec replayed the head item, ending in register file `rf1` *)
  Definition gPop (g : Ghost) (G' : list GItemT) (rf1 : RfSt) : Ghost :=
    mkGhost G' rf1 (g_cnwb g) (g_revOff g) (g_d2aFo g) (g_acc g).

  (* `AccessRel_ghost` when only memory heads move: `AccessRel` names the head only for loads and
   * stores *)
  Lemma AccessRel_ghost_mem :
    forall g g' (s1 : IState) (s2 : SState),
      g_acc g' = g_acc g -> g_revOff g' = g_revOff g -> g_cnwb g' = g_cnwb g ->
      (forall q, HeadReq g q -> opIsMem (mrOp q) = true -> HeadReq g' q) ->
      AccessRel g s1 s2 -> AccessRel g' s1 s2.
  Proof.
    intros g g' s1 s2 Eacc Erev Ecnwb HH Ha.
    unfold AccessRel in *; rewrite Eacc, Erev, Ecnwb.
    revert Ha.
    destruct (g_acc g) as [| addr size pkt [[|]|[|]] | ld pkt0 [[|]|[|]|[|]|[|] rp|res]
                          | rc [[|]|[|]|[|]|[|] rp|res] | [[|]|[|]|[|]|[|] rp|res]
                          | [[|]|[|]|[|]|[|] rp|res] | addr pkt [[|]|[|]]];
      intros Ha; cbv beta iota zeta in *;
      (let rec go H :=
         lazymatch type of H with
         | exists q, HeadReq _ q /\ _ =>
             let q := fresh "q" in let Hh := fresh "Hh" in let Hr := fresh "Hr" in let Hop := fresh "Hop" in
             destruct H as [q [Hh Hr]]; exists q; split; [| exact Hr];
             apply HH; [exact Hh |];
             destruct Hr as [Hop _]; unfold opIsStore, opIsLoad in Hop; apply andb_prop in Hop; exact (proj1 Hop)
         | _ /\ _ =>
             let H1 := fresh "H" in let H2 := fresh "H" in
             destruct H as [H1 H2]; split; [go H1 | go H2]
         | _ => exact H
         end in
       go Ha).
  Qed.

  Lemma filterReqs_pop :
    forall it G, itemNonBlocking it = true ->
      filter (fun q => negb (isPlainFence q)) (chainReqs (it :: G)) =
      filter (fun q => negb (isPlainFence q)) (chainReqs G).
  Proof.
    intros [| e] G Hnb; [reflexivity |].
    cbn [itemNonBlocking] in Hnb; apply negb_true_iff in Hnb.
    unfold chainReqs; cbn [flat_map]; rewrite filter_app.
    destruct (entryReq e) as [q |] eqn:Eq; [| reflexivity].
    destruct (nonBlocking_noMem e q Hnb Eq) as [H1 H2].
    cbn [filter]; unfold isPlainFence; rewrite H1, H2; reflexivity.
  Qed.

  (* The spec replayed the head item `it` (a tick, or a non-blocking entry): its register file is
   * now `cnwbApply (g_cnwb g) rf1`, its memory changed only by reads, and `secondLine` is as
   * before *)
  Lemma RefRelNE_pop :
    forall g it G' rf1 (s1 : IState) (s2 s2' : SState),
      g_chain g = it :: G' ->
      ItemStep (g_rf0 g) rf1 it ->
      GChain pcAddrInit rf1 G' (iFlush s1) ->
      itemNonBlocking it = true ->
      sRf s2' = cnwbApply (g_cnwb g) rf1 ->
      sSecond s2' = sSecond s2 ->
      (forall L, lineContent specRegions (sMem s2') L = lineContent specRegions (sMem s2) L) ->
      FetchViewExt specRegions (sMem s2) (sMem s2') ->
      MemRelC g s1 s2' ->
      sClint s2' = sClint s2 -> sPlic s2' = sPlic s2 ->
      RefRelNE g s1 s2 -> RefRelNE (gPop g G' rf1) s1 s2'.
  Proof.
    intros g it G' rf1 s1 s2 s2' Hch Hst Hgc Hnb Erf Esec Hlc Hext Hmem Ecl Epl H.
    destruct H as [Hrf Hm Hl Hrp Ha Hc Hd Hf Hs Hfr Hw Hrk].
    pose proof (proj2 (proj2 Hm)) as Hsnap.
    assert (Hhead : forall e, it = GInst e -> entryBlocking e = false)
      by (intros e ->; cbn [itemNonBlocking] in Hnb; apply negb_true_iff in Hnb; exact Hnb).
    constructor.
    - unfold RfRel in *; unfold gPop; cbn [g_chain g_rf0 g_cnwb].
      destruct Hrf as [R1 [R2 [R3 R4]]]; rewrite Hch in R3, R4.
      split; [exact Erf |]; split; [exact Hgc |]; split.
      + intros d v Hcn e Hin; exact (R3 d v Hcn e (or_intror Hin)).
      + intros G1 e G2 HG Hld; apply (R4 (it :: G1) e G2); [rewrite HG; reflexivity | exact Hld].
    - exact Hmem.
    - unfold LatchRel in *; unfold gPop; cbn [g_chain].
      intros e Hin; rewrite Ecl, Epl; apply Hl; rewrite Hch; right; exact Hin.
    - unfold ReplayRel in *; unfold gPop; cbn [g_chain g_rf0].
      intros G1 e G2 rfe HG Hc1.
      apply (FetchAllowedInst_fetchViewExt initLine fwcs specRegions (sMem s2) (sMem s2') _ _ Hsnap Hext).
      apply (Hrp (it :: G1) e G2 rfe); [rewrite Hch, HG; reflexivity | exact (GChain_cons _ _ _ _ _ Hst Hc1)].
    - apply (AccessRel_ghost_mem g); [reflexivity | reflexivity | reflexivity | |].
      + intros q [e [G'' [HG Hq]]] Hmq.
        rewrite Hch in HG; injection HG as E1 _.
        destruct (nonBlocking_noMem e q (Hhead e E1) Hq) as [Hm' _].
        rewrite Hm' in Hmq; discriminate Hmq.
      + exact (AccessRel_frame g s1 s1 s2 s2' (fun P => eq_refl) eq_refl eq_refl eq_refl eq_refl eq_refl Esec Hlc Ha).
    - unfold CnwbRel in *; unfold gPop; cbn [g_cnwb g_chain g_acc].
      destruct Hc as [C1 [C2 [C3 C4]]].
      split; [exact C1 | split; [| split; [exact C3 |]]].
      + intros Hq; rewrite (revWb_ext (sMem s2) (sMem s2') _ Hlc); exact (C2 Hq).
      + intros Hlr Hcn Hat e Hin; rewrite Hch in C4; exact (C4 Hlr Hcn Hat e (or_intror Hin)).
    - unfold DmQueueRel in *; unfold gPop; cbn [g_chain g_acc]; cbv zeta in *.
      rewrite Hch, (filterReqs_pop it G' Hnb) in Hd; exact Hd.
    - unfold FenceRel in *; unfold gPop; cbn [g_chain].
      destruct Hf as [Hf1 [Hf2 Hf3]]; split; [| split].
      3: { intros G1 e G2 HG Hfi; apply (Hf3 (it :: G1) e G2); [rewrite Hch, HG; reflexivity | exact Hfi]. }
      + intros Hp; destruct (Hf1 Hp) as [Hnl [Hst' [G1 [e [G2 [HG [Hfi HF]]]]]]].
        split; [exact Hnl | split; [exact Hst' |]].
        rewrite Hch in HG.
        destruct G1 as [| x G1]; cbn [app] in HG; injection HG as E1 E2.
        * exfalso.
          unfold entryIsFenceI in Hfi; revert Hfi; destruct (entryReq e) as [q |] eqn:Eq; intros Hfi;
            [| discriminate Hfi].
          destruct (nonBlocking_noMem e q (Hhead e E1) Eq) as [_ H2]; rewrite H2 in Hfi; discriminate Hfi.
        * exists G1, e, G2; split; [exact E2 | split; [exact Hfi | exact HF]].
      + intros Hw'; destruct (Hf2 Hw') as [Hp [Hnl [Hst' Hno]]].
        split; [exact Hp | split; [exact Hnl | split; [exact Hst' |]]].
        intros e Hin; apply (Hno e); rewrite Hch; right; exact Hin.
    - exact Hs.
    - unfold FrontRel in *; destruct Hfr as [F1 [F2 [F3 [F4 [F5 [F6 F7]]]]]].
      split; [exact F1 |]; split; [exact F2 |]; split; [exact F3 |]; split; [exact F4 |]; split; [exact F5 |].
      split.
      + unfold LiveChain in *.
        refine (LiveChainG_mono _ _ _ (FrontierRel s1 s2) _ _ _ Hsnap Hext _ F6).
        intros p Hp; exact (FrontierRel_mono s1 s2 s2' p Hsnap Hext Hp).
      + unfold FetchRespRel in *.
        refine (AllPorts_impl _ _ implRegions (iRegions s1) _ F7).
        intros r y HP; cbv beta zeta in HP |- *.
        destruct HP as [C [HC1 [HC2 HC3]]]; exists C; split; [exact HC1 | split; [exact HC2 |]].
        intros Hv; destruct (HC3 Hv) as [f [E' [HE Hla]]]; exists f, E'; split; [exact HE |].
        intros Hlv; exact (LineAllowed_fetchViewExt initLine specRegions fwcs _ _ _ _ Hsnap Hext (Hla Hlv)).
    - exact Hw.
    - exact (RevokerRel_frame g (gPop g G' rf1) s1 s1 s2 s2' eq_refl eq_refl eq_refl Hlc Hrk).
  Qed.

End CoreRel.

