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

From Stdlib Require Import String List ZArith Zmod Bool Nat.
Import ListNotations.
Open Scope string_scope.
From Guru Require Import Syntax Notations Semantics Library Composition MergeFold.
From Cheriot Require Import SpecDefines SpecDevice.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Local Open Scope guru_scope.

(* ===========================================================================
 * PLIC Register Offsets & Memory Sizing
 * =========================================================================== *)

Definition PLIC_PRIORITY_BASE    : Z := 0x000000.
Definition PLIC_PENDING_OFFSET   : Z := 0x001000.
Definition PLIC_ENABLE_OFFSET    : Z := 0x002000.
Definition PLIC_THRESHOLD_OFFSET : Z := 0x200000.
Definition PLIC_CLAIM_OFFSET     : Z := 0x200004.
Definition PlicSizeBytes         : Z := 0x400000. (* 4 MB *)
Definition PlicOffsetSz          : Z := Eval compute in Z.log2_up PlicSizeBytes.
Definition PlicLineConfig        : LineConfig := RawLine (Z.to_nat LgNumBytesXlen).
Definition plicNumBytes (n : nat) : nat := Nat.div (n + 7) 8.

(* ===========================================================================
 * Tree Structure (Ordered by MMIO Offset)
 * =========================================================================== *)

Definition priorityLeaves (n : nat) : list (Tree Elem) :=
  map (fun idx =>
    Leaf ("prio_" ++ hex_string_of_Z (Z.of_nat idx))%string
         (EReg (Build_Reg (Bit Xlen) (Some Zmod.zero)))
  ) (seq 0 n).

Definition pendingLeaves (n : nat) : list (Tree Elem) :=
  map (fun idx =>
    Leaf ("pend_" ++ hex_string_of_Z (Z.of_nat idx))%string
         (EReg (Build_Reg Bool (Some false)))
  ) (seq 0 n).

Definition enableLeaves (n : nat) : list (Tree Elem) :=
  map (fun idx =>
    Leaf ("en_" ++ hex_string_of_Z (Z.of_nat idx))%string
         (EReg (Build_Reg Bool (Some false)))
  ) (seq 0 n).

Definition inServiceLeaves (n : nat) : list (Tree Elem) :=
  map (fun idx =>
    Leaf ("insv_" ++ hex_string_of_Z (Z.of_nat idx))%string
         (EReg (Build_Reg Bool (Some false)))
  ) (seq 0 n).

Definition plicChildren (n : nat) : list (Tree Elem) :=
  [ Node "priorities" (priorityLeaves n) ;
    Node "pending"    (pendingLeaves n) ;
    Node "enables"    (enableLeaves n) ;
    Leaf "threshold"  (EReg (Build_Reg (Bit Xlen) (Some Zmod.zero))) ;
    Leaf "claim"      (EReg (Build_Reg (Bit Xlen) (Some Zmod.zero))) ;
    Node "in_service" (inServiceLeaves n) ].

Definition plicTree (n : nat) : Tree Elem :=
  Node "plic" (plicChildren n).

Section PlicPaths.
  Variable n : nat.
  Local Notation tPlic := (plicTree n).

  Definition plicPrioritiesNodePath : NodePath tPlic :=
    getNodePath tPlic "plic.priorities".
  Definition plicPendingNodePath : NodePath tPlic :=
    getNodePath tPlic "plic.pending".
  Definition plicEnablesNodePath : NodePath tPlic :=
    getNodePath tPlic "plic.enables".
  Definition plicInServiceNodePath : NodePath tPlic :=
    getNodePath tPlic "plic.in_service".
  Definition plicThresholdPath : RegPath tPlic :=
    getChildRegPathTree tPlic "threshold".
  Definition plicClaimPath : RegPath tPlic :=
    getChildRegPathTree tPlic "claim".

  Definition priorityPathsWithKind : list (RegOfKind (t:=tPlic) (Bit Xlen)) :=
    map (embedRegOfKind plicPrioritiesNodePath)
        (getTreeRegsOfKind (Bit Xlen) (getNode plicPrioritiesNodePath)).

  Definition pendingPathsWithKind : list (RegOfKind (t:=tPlic) Bool) :=
    map (embedRegOfKind plicPendingNodePath)
        (getTreeRegsOfKind Bool (getNode plicPendingNodePath)).

  Definition enablesPathsWithKind : list (RegOfKind (t:=tPlic) Bool) :=
    map (embedRegOfKind plicEnablesNodePath)
        (getTreeRegsOfKind Bool (getNode plicEnablesNodePath)).

  Definition inServicePathsWithKind : list (RegOfKind (t:=tPlic) Bool) :=
    map (embedRegOfKind plicInServiceNodePath)
        (getTreeRegsOfKind Bool (getNode plicInServiceNodePath)).
End PlicPaths.

(* ===========================================================================
 * Core Combinational & Sequential Logic
 * =========================================================================== *)

Record PlicState (ty : Kind -> Type) (n : nat) := {
  st_thresh : Expr ty (Bit Xlen) ;
  st_prios  : Expr ty (Array n (Bit Xlen)) ;
  st_pends  : Expr ty (Array n Bool) ;
  st_ens    : Expr ty (Array n Bool) ;
  st_insvs  : Expr ty (Array n Bool)
}.
Arguments st_thresh {ty n} p.
Arguments st_prios {ty n} p.
Arguments st_pends {ty n} p.
Arguments st_ens {ty n} p.
Arguments st_insvs {ty n} p.

Definition PlicResType : Kind :=
  STRUCT_TYPE { "id" :: Bit Xlen ; "prio" :: Bit Xlen }.

Definition plicResEmpty {ty : Kind -> Type} : Expr ty PlicResType :=
  STRUCT { "id" ::= ($(0) : Expr ty (Bit Xlen)) ; "prio" ::= ($(0) : Expr ty (Bit Xlen)) }.

Definition mkPlicRes {ty : Kind -> Type} (id prio : Expr ty (Bit Xlen)) : Expr ty PlicResType :=
  STRUCT { "id" ::= id ; "prio" ::= prio }.

Definition plicResComb {ty : Kind -> Type} (a b : ty PlicResType) : LetExpr ty PlicResType :=
  LetE a_id   : Bit Xlen <- ##a`"id" ;
  LetE a_prio : Bit Xlen <- ##a`"prio" ;
  LetE b_id   : Bit Xlen <- ##b`"id" ;
  LetE b_prio : Bit Xlen <- ##b`"prio" ;
  LetE a_wins : Bool <- Or [Sgt #a_prio #b_prio; And[Eq #a_prio #b_prio; Sle #a_id #b_id]];
  RetE (ITE #a_wins #a #b).

Section PlicCoreLogic.
  Variable n : nat.
  Local Notation tPlic := (plicTree n).
  Variable ty : Kind -> Type.

  Definition listToExprArray {k : Kind} {n : nat}
    (ls : list (Expr ty k)) (def : Expr ty k) : Expr ty (Array n k) :=
    ArrayBuilder (fun (i : FinType n) => nth (finNum i) ls def).

  Fixpoint readAllSources
           (prios : list (RegOfKind (t:=tPlic) (Bit Xlen)))
           (pends : list (RegOfKind (t:=tPlic) Bool))
           (ens   : list (RegOfKind (t:=tPlic) Bool))
           (insvs : list (RegOfKind (t:=tPlic) Bool))
           {ans : Kind}
           (k : list (Expr ty (Bit Xlen)) ->
                list (Expr ty Bool) ->
                list (Expr ty Bool) ->
                list (Expr ty Bool) ->
                Action ty tPlic ans)
           : Action ty tPlic ans :=
    match prios, pends, ens, insvs with
    | rPrio :: rPrios', rPend :: rPends', rEn :: rEns', rInsv :: rInsvs' =>
        ReadReg "val_prio" rPrio.(rk_path) (fun val_prio =>
        ReadReg "val_pend" rPend.(rk_path) (fun val_pend =>
        ReadReg "val_en"   rEn.(rk_path)   (fun val_en =>
        ReadReg "val_insv" rInsv.(rk_path) (fun val_insv =>
          let pf_prio := Kind_eqb_eq _ _ rPrio.(rk_pf) in
          let pf_pend := Kind_eqb_eq _ _ rPend.(rk_pf) in
          let pf_en   := Kind_eqb_eq _ _ rEn.(rk_pf) in
          let pf_insv := Kind_eqb_eq _ _ rInsv.(rk_pf) in
          let c_prio := eq_rect (regKind (getRegFromPath rPrio.(rk_path))) (fun K => ty K) val_prio _ pf_prio in
          let c_pend := eq_rect (regKind (getRegFromPath rPend.(rk_path))) (fun K => ty K) val_pend _ pf_pend in
          let c_en   := eq_rect (regKind (getRegFromPath rEn.(rk_path)))   (fun K => ty K) val_en   _ pf_en in
          let c_insv := eq_rect (regKind (getRegFromPath rInsv.(rk_path))) (fun K => ty K) val_insv _ pf_insv in
          readAllSources rPrios' rPends' rEns' rInsvs' (fun pList dList eList iList =>
            k (Var _ _ c_prio :: pList)
              (Var _ _ c_pend :: dList)
              (Var _ _ c_en   :: eList)
              (Var _ _ c_insv :: iList)
          )
        ))))
    | _, _, _, _ => k nil nil nil nil
    end.

  Definition readPlicState {ans : Kind}
             (k : PlicState ty n -> Action ty tPlic ans) : Action ty tPlic ans :=
    LetA thresh : Bit Xlen <- ReadReg "threshold" (plicThresholdPath n) (fun v => Return #v) ;
    readAllSources (priorityPathsWithKind n)
                   (pendingPathsWithKind n)
                   (enablesPathsWithKind n)
                   (inServicePathsWithKind n)
                   (fun prioList pendList enList insvList =>
      let prios := listToExprArray prioList ($0 : Expr ty (Bit Xlen)) in
      let pends := listToExprArray pendList (ConstBool false) in
      let ens   := listToExprArray enList   (ConstBool false) in
      let insvs := listToExprArray insvList (ConstBool false) in
      k {| st_thresh := #thresh ;
           st_prios  := prios ;
           st_pends  := pends ;
           st_ens    := ens ;
           st_insvs  := insvs |}
    ).

  Definition makeClaimLeaf
             (thresh : Expr ty (Bit Xlen))
             (prios : Expr ty (Array n (Bit Xlen)))
             (pends : Expr ty (Array n Bool))
             (ens : Expr ty (Array n Bool))
             (insvs : Expr ty (Array n Bool))
             (i : nat) : LetExpr ty PlicResType :=
    match i with
    | 0%nat => RetE plicResEmpty
    | S _ =>
        let idx := ($(Z.of_nat i) : Expr ty (Bit Xlen)) in
        LetE pend : Bool       <- pends @[ idx ] ;
        LetE en : Bool         <- ens @[ idx ] ;
        LetE insv : Bool       <- insvs @[ idx ] ;
        LetE prio : Bit Xlen   <- prios @[ idx ] ;
        LetE active : Bool     <- And [ #pend ; #en ; Not #insv ; Sgt #prio thresh ] ;
        RetE (ITE #active (mkPlicRes idx #prio) plicResEmpty)
    end.

  (* Combinational claim search using merge_fold_list tournament tree *)
  Definition findMaxActive
             (thresh : Expr ty (Bit Xlen))
             (prios : Expr ty (Array n (Bit Xlen)))
             (pends : Expr ty (Array n Bool))
             (ens : Expr ty (Array n Bool))
             (insvs : Expr ty (Array n Bool))
             : LetExpr ty PlicResType :=
    let leaves := map (makeClaimLeaf thresh prios pends ens insvs) (seq 0 n) in
    merge_fold_list (liftLet plicResComb) (RetE plicResEmpty) leaves.

  Definition updateClaim : Action ty tPlic (Bit 0) :=
    readPlicState (fun st =>
      LetL bestRes : PlicResType <-
        findMaxActive st.(st_thresh) st.(st_prios) st.(st_pends) st.(st_ens) st.(st_insvs) ;
      Act (WriteReg (plicClaimPath n) (##bestRes`"id") Retv) ;
      Retv
    ).

  Definition plicMeip : Action ty tPlic Bool :=
    ReadReg "claim" (plicClaimPath n) (fun val_claim =>
      Return (isNotZero (Var _ _ val_claim))
    ).

  Definition plicClaim : Action ty tPlic (Bit Xlen) :=
    ReadReg "claim" (plicClaimPath n) (fun val_claim =>
      let claimedId := Var _ _ val_claim in
      If (isNotZero claimedId) Then (
        Act (writeRegsList (pendingPathsWithKind n) claimedId (ConstBool false)) ;
        Act (writeRegsList (inServicePathsWithKind n) claimedId (ConstBool true)) ;
        Act (WriteReg (plicClaimPath n) $0 Retv) ;
        Retv
      ) ;
      Return claimedId
    ).

  Definition plicComplete (completedId : Expr ty (Bit Xlen)) : Action ty tPlic (Bit 0) :=
    If (isNotZero completedId) Then (
      Act (writeRegsList (inServicePathsWithKind n) completedId (ConstBool false)) ;
      Retv
    ) ;
    Retv.

  (* Latch pending IRQs from external wires into leaf registers (skipping source 0) *)
  Fixpoint updatePendingLeaves
           (pends : list (RegOfKind (t:=tPlic) Bool))
           (insvs : list (RegOfKind (t:=tPlic) Bool))
           (irqs  : list (Expr ty Bool))
           : Action ty tPlic (Bit 0) :=
    match pends, insvs, irqs with
    | pendRk :: pendsRest, insvRk :: insvsRest, irqVal :: irqsRest =>
        let pf_pend := Kind_eqb_eq _ _ pendRk.(rk_pf) in
        let pf_insv := Kind_eqb_eq _ _ insvRk.(rk_pf) in
        ReadReg "" pendRk.(rk_path) (fun val_pend =>
        ReadReg "" insvRk.(rk_path) (fun val_insv =>
          let c_pend := eq_rect (regKind (getRegFromPath pendRk.(rk_path))) (fun K => ty K) val_pend _ pf_pend in
          let c_insv := eq_rect (regKind (getRegFromPath insvRk.(rk_path))) (fun K => ty K) val_insv _ pf_insv in
          let newPend := Or [ Var _ _ c_pend ; And [ irqVal ; Not (Var _ _ c_insv) ] ] in
          let c_newPend := eq_rect Bool (fun K => Expr ty K) newPend _ (eq_sym pf_pend) in
          Act (WriteReg pendRk.(rk_path) c_newPend Retv) ;
          updatePendingLeaves pendsRest insvsRest irqsRest
        ))
    | _, _, _ => Retv
    end.

  Definition updatePendings (irqs : list (Expr ty Bool)) : Action ty tPlic (Bit 0) :=
    match pendingPathsWithKind n, inServicePathsWithKind n with
    | _ :: devPends, _ :: devInsvs => updatePendingLeaves devPends devInsvs irqs
    | _, _ => Retv
    end.
End PlicCoreLogic.

(* ===========================================================================
 * MMIO Interface
 * =========================================================================== *)

Section PlicMmio.
  Variable n : nat.
  Variable base : Z.
  Variable ty : Kind -> Type.
  Local Notation tPlic := (plicTree n).

  Definition boolArrayToByteArray
             (arr : Expr ty (Array n Bool))
             : Expr ty (Array (plicNumBytes n) (Bit 8)) :=
    FromBit (Array (plicNumBytes n) (Bit 8))
            (castBits (add_sub_cancel (kindSize (Array (plicNumBytes n) (Bit 8)))
                                      (kindSize (Array n Bool)))
                      (ZeroExtendTo (kindSize (Array (plicNumBytes n) (Bit 8)))
                                    (ToBit arr))).

  Definition plicLineReadAction
             (addr : Expr ty Addr)
             : Action ty tPlic (LineReadRp PlicLineConfig) :=
    Let offset <- getMemOffset base PlicSizeBytes addr ;
    Let isClaim     : Bool <- Eq #offset $(PLIC_CLAIM_OFFSET) ;
    Let isThreshold : Bool <- Eq #offset $(PLIC_THRESHOLD_OFFSET) ;
    Let isEnable    : Bool <- Sge #offset $(PLIC_ENABLE_OFFSET) ;
    Let isPending   : Bool <- Sge #offset $(PLIC_PENDING_OFFSET) ;
    readPlicState (fun st =>
      Let prioOffset <- Sub #offset $(PLIC_PRIORITY_BASE) ;
      Let prioIdx : Bit Xlen <- ZeroExtendTo Xlen (TruncMsb (PlicOffsetSz - LgNumBytesXlen) LgNumBytesXlen #prioOffset) ;
      Let prioVal : Bit Xlen <- st.(st_prios) @[ #prioIdx ] ;
      Let pendOffset <- Sub #offset $(PLIC_PENDING_OFFSET) ;
      Let pendSlice : Array (Z.to_nat NumBytesXlen) (Bit 8) <-
        Syntax.slice (boolArrayToByteArray st.(st_pends)) #pendOffset (Z.to_nat NumBytesXlen) ;
      Let pendVal : Bit Xlen <- ToBit #pendSlice ;
      Let enOffset <- Sub #offset $(PLIC_ENABLE_OFFSET) ;
      Let enSlice : Array (Z.to_nat NumBytesXlen) (Bit 8) <-
        Syntax.slice (boolArrayToByteArray st.(st_ens)) #enOffset (Z.to_nat NumBytesXlen) ;
      Let enVal : Bit Xlen <- ToBit #enSlice ;
      LetIf claimedId : Bit Xlen <- If #isClaim Then (@plicClaim n ty) ;
      Let rVal : Bit Xlen <-
        Or [ #prioVal ;
             ITE0 #isPending #pendVal ;
             ITE0 #isEnable #enVal ;
             ITE0 #isThreshold st.(st_thresh) ;
             #claimedId ] ;
      Let dataArr : Array (Z.to_nat NumBytesXlen) (Bit 8) <-
        FromBit (Array (Z.to_nat NumBytesXlen) (Bit 8)) #rVal ;
      @Return ty tPlic (LineReadRp PlicLineConfig) (STRUCT {
        "data" ::= #dataArr ;
        "tag"  ::= Const ty (Array (cfgNumLineTags PlicLineConfig) Bool) (getDefault _)
      })
    ).

  (* Write a list of values to a list of leaf registers *)
  Fixpoint writeRegs
           {k : Kind}
           (vals : list (Expr ty k))
           (paths : list (RegOfKind (t:=tPlic) k))
           : Action ty tPlic (Bit 0) :=
    match vals, paths with
    | val :: valsRest, rk :: pathsRest =>
        let pf := Kind_eqb_eq _ _ rk.(rk_pf) in
        let c_val := eq_rect k (fun K => Expr ty K) val _ (eq_sym pf) in
        Act (WriteReg rk.(rk_path) c_val Retv) ;
        writeRegs valsRest pathsRest
    | _, _ => Retv
    end.

  Definition plicLineWriteAction
             (rq : Expr ty (LineWriteRq PlicLineConfig))
             : Action ty tPlic (Bit 0) :=
    Let offset <- getMemOffset base PlicSizeBytes (rq`"addr") ;
    Let writeWord : Bit Xlen <- ToBit (rq`"data") ;
    Let isComplete  : Bool <- Eq #offset $(PLIC_CLAIM_OFFSET) ;
    Let isThreshold : Bool <- Eq #offset $(PLIC_THRESHOLD_OFFSET) ;
    Let isEnable    : Bool <- Sge #offset $(PLIC_ENABLE_OFFSET) ;
    Let isPrio      : Bool <- ConstBool true ;
    If #isComplete Then (
      @plicComplete n ty #writeWord
    ) ;
    If #isThreshold Then (
      Act (WriteReg (plicThresholdPath n) #writeWord Retv) ;
      Retv
    ) ;
    If #isEnable Then (
      Let bits : Array (Z.to_nat Xlen) Bool <-
        FromBit (Array (Z.to_nat Xlen) Bool) #writeWord ;
      let allBits := map (fun i => ReadArrayConst #bits i) (genFinType (Z.to_nat Xlen)) in
      match allBits, enablesPathsWithKind n with
      | _ :: devBits, _ :: devEnables => writeRegs devBits devEnables
      | _, _ => Retv
      end
    ) ;
    If #isPrio Then (
      Let prioOffset <- Sub #offset $(PLIC_PRIORITY_BASE) ;
      Let prioWord : Bit Xlen <- ZeroExtendTo Xlen (TruncMsb (PlicOffsetSz - LgNumBytesXlen) LgNumBytesXlen #prioOffset) ;
      If (isNotZero #prioWord) Then (
        Act (writeRegsList (priorityPathsWithKind n) #prioWord #writeWord) ;
        Retv
      ) ;
      Retv
    ) ;
    Retv.

End PlicMmio.

Arguments plicLineReadAction n base ty addr : clear implicits.
Arguments plicLineWriteAction n base ty rq : clear implicits.

(* ===========================================================================
 * MemRegion Constructor
 * =========================================================================== *)

Definition plicMemRegion
           (n : nat)
           (base : Z)
           (pfBound : Is_true ((0 <=? base) && (base + PlicSizeBytes <=? Z.shiftl 1 AddrSz))%Z)
           (pfAligned : Is_true (base mod (2 ^ Z.of_nat (cfgLgLineBytes PlicLineConfig)) =? 0)%Z)
           : MemRegion := {|
  regionName        := "plic" ;
  regionBase        := base ;
  regionSize        := PlicSizeBytes ;
  regionLineCfg     := PlicLineConfig ;
  isReadOnly        := false ;
  regionKind        := @CustomMem "plic" PlicSizeBytes PlicLineConfig
                                  (plicChildren n)
                                  (plicLineReadAction n base)
                                  (plicLineWriteAction n base)
                                  None ;
  regionInMemory    := pfBound ;
  regionBaseAligned := pfAligned ;
  regionSizeAligned := I
|}.

Arguments plicMemRegion n base pfBound pfAligned : clear implicits.

(* ===========================================================================
 * System Integration Helpers
 * =========================================================================== *)

Record PlicInstance (n : nat) (regions : list MemRegion) := {
  plicIdx      : nat ;
  plicBaseAddr : Z ;
  pfBound      : Is_true ((0 <=? plicBaseAddr) && (plicBaseAddr + PlicSizeBytes <=? Z.shiftl 1 AddrSz))%Z ;
  pfAligned    : Is_true (plicBaseAddr mod (2 ^ Z.of_nat (cfgLgLineBytes PlicLineConfig)) =? 0)%Z ;
  pfNumSources : Is_true (n <=? 1024)%nat ;
  pfPlic       : nth_error regions plicIdx = Some (plicMemRegion n plicBaseAddr pfBound pfAligned)
}.

Definition plicRegion {n regions} (plic : PlicInstance n regions) : MemRegion :=
  plicMemRegion n plic.(plicBaseAddr) plic.(pfBound) plic.(pfAligned).

Section PlicSystem.
  Variable n : nat.
  Variable regions : list MemRegion.
  Variable plic : PlicInstance n regions.
  Variable ty : Kind -> Type.

  Local Notation memTree := (specMemTree regions).

  Definition plicAction {k : Kind} (act : Action ty (plicTree n) k) : Action ty memTree k :=
    nthRegionAction plic.(plicIdx) regions (plicRegion plic) plic.(pfPlic) act.

  Definition plicMeipSystem : Action ty memTree Bool :=
    plicAction (@plicMeip n ty).

  Fixpoint sampleIrqsCPS
           (acts : list (forall ty, Action ty memTree Bool))
           (k : forall (irqs : list (Expr ty Bool)), length irqs = length acts -> Action ty memTree (Bit 0))
           : Action ty memTree (Bit 0) :=
    match acts as acts' return (forall (irqs : list (Expr ty Bool)), length irqs = length acts' -> Action ty memTree (Bit 0)) -> Action ty memTree (Bit 0) with
    | [] => fun k => k [] eq_refl
    | act :: rest => fun k =>
        LetA irqVal : Bool <- act ty ;
        @sampleIrqsCPS rest (fun restIrqs Hlen =>
          k (#irqVal :: restIrqs) (f_equal S Hlen)
        )
    end k.

  Definition plicPendingsStep
             (pfCount : S (length (collectIrqActions regions)) = n)
             : Action ty memTree (Bit 0) :=
    @sampleIrqsCPS (collectIrqActions regions) (fun irqs Hlen =>
      plicAction (@updatePendings n ty irqs)
    ).

  Definition plicClaimStep : Action ty memTree (Bit 0) :=
    plicAction (@updateClaim n ty).

End PlicSystem.
