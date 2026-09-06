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

From Stdlib Require Import String List ZArith Zmod Bool.
Import ListNotations.
Open Scope string_scope.
From Guru Require Import Syntax Notations Semantics Library Composition MergeFold.
From Cheriot Require Import SpecDefines SpecDevice.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Local Open Scope guru_scope.

(* ===========================================================================
 * 1. PLIC Register Offsets & Memory Sizing
 * =========================================================================== *)

Definition PLIC_PRIORITY_BASE    : Z := 0x000000.
Definition PLIC_PENDING_OFFSET   : Z := 0x001000.
Definition PLIC_ENABLE_OFFSET    : Z := 0x002000.
Definition PLIC_THRESHOLD_OFFSET : Z := 0x200000.
Definition PLIC_CLAIM_OFFSET     : Z := 0x200004.
Definition PlicSizeBytes         : Z := 0x400000. (* 4 MB *)
Definition PlicLineConfig        : LineConfig := RawLine (Z.to_nat LgNumBytesXlen).

(* ===========================================================================
 * 2. Tree Structure (Ordered by MMIO Offset)
 * =========================================================================== *)

Definition priorityLeaves (n : nat) : list (Tree Elem) :=
  map (fun idx =>
    Leaf ("prio_" ++ hex_string_of_Z (Z.of_nat idx))%string
         (EReg (Build_Reg (Bit Xlen) (Some Zmod.zero)))
  ) (seq 0 n).

Definition plicChildren (n : nat) : list (Tree Elem) :=
  [ Node "priorities" (priorityLeaves n) ;
    Leaf "pending"    (EReg (Build_Reg (Array n Bool) (Some (getDefault _)))) ;
    Leaf "enables"    (EReg (Build_Reg (Array n Bool) (Some (getDefault _)))) ;
    Leaf "threshold"  (EReg (Build_Reg (Bit Xlen) (Some Zmod.zero))) ;
    Leaf "in_service" (EReg (Build_Reg (Array n Bool) (Some (getDefault _)))) ].

Definition plicTree (n : nat) : Tree Elem :=
  Node "plic" (plicChildren n).

Section PlicPaths.
  Variable n : nat.
  Local Notation tPlic := (plicTree n).

  Definition plicPrioritiesNodePath : NodePath tPlic :=
    getNodePath tPlic "plic.priorities".

  Definition priorityPathsWithKind : list (RegOfKind (t:=tPlic) (Bit Xlen)) :=
    map (embedRegOfKind plicPrioritiesNodePath)
        (getTreeRegsOfKind (Bit Xlen) (getNode plicPrioritiesNodePath)).

  Definition plicPendingPath    : RegPath tPlic := getChildRegPathTree tPlic "pending".
  Definition plicEnablesPath    : RegPath tPlic := getChildRegPathTree tPlic "enables".
  Definition plicThresholdPath  : RegPath tPlic := getChildRegPathTree tPlic "threshold".
  Definition plicInServicePath  : RegPath tPlic := getChildRegPathTree tPlic "in_service".
End PlicPaths.

(* ===========================================================================
 * 3. Core Combinational & Sequential Logic
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
  LetE a_wins : Bool <-
    Or [ Eq #b_id ($0 : Expr ty (Bit Xlen)) ;
         And [ Not (Eq #a_id ($0 : Expr ty (Bit Xlen))) ;
               Or [ Sgt #a_prio #b_prio ;
                    And [ Eq #a_prio #b_prio ; Slt #a_id #b_id ] ] ] ] ;
  RetE (ITE #a_wins #a #b).

Section PlicCoreLogic.
  Variable n : nat.
  Local Notation tPlic := (plicTree n).
  Variable ty : Kind -> Type.

  Definition listToExprArray {k : Kind} {n : nat}
    (ls : list (Expr ty k)) (def : Expr ty k) : Expr ty (Array n k) :=
    ArrayBuilder (fun (i : FinType n) => nth (finNum i) ls def).

  Fixpoint readAllPriorities
           (paths : list (RegOfKind (t:=tPlic) (Bit Xlen)))
           {ans : Kind}
           (k : list (Expr ty (Bit Xlen)) -> Action ty tPlic ans)
           : Action ty tPlic ans :=
    match paths with
    | nil => k nil
    | rk :: rest =>
        ReadReg "" rk.(rk_path) (fun val_ty =>
          let pf_eq := Kind_eqb_eq _ _ rk.(rk_pf) in
          let casted_ty := eq_rect (regKind (getRegFromPath rk.(rk_path))) (fun K => ty K) val_ty _ pf_eq in
          readAllPriorities rest (fun vals => k (Var _ _ casted_ty :: vals))
        )
    end.

  Definition readPlicState {ans : Kind}
             (k : PlicState ty n -> Action ty tPlic ans) : Action ty tPlic ans :=
    LetA thresh : Bit Xlen           <- ReadReg "threshold"  (plicThresholdPath n)  (fun v => Return #v) ;
    LetA pends  : Array n Bool       <- ReadReg "pending"    (plicPendingPath n)    (fun v => Return #v) ;
    LetA ens    : Array n Bool       <- ReadReg "enables"    (plicEnablesPath n)    (fun v => Return #v) ;
    LetA insvs  : Array n Bool       <- ReadReg "in_service" (plicInServicePath n)  (fun v => Return #v) ;
    readAllPriorities (priorityPathsWithKind n) (fun prioList =>
      let prios := listToExprArray prioList ($0 : Expr ty (Bit Xlen)) in
      k {| st_thresh := #thresh ;
           st_prios  := prios ;
           st_pends  := #pends ;
           st_ens    := #ens ;
           st_insvs  := #insvs |}
    ).

  Definition makeMeipLeaf
             (thresh : Expr ty (Bit Xlen))
             (prios : Expr ty (Array n (Bit Xlen)))
             (pends : Expr ty (Array n Bool))
             (ens : Expr ty (Array n Bool))
             (insvs : Expr ty (Array n Bool))
             (i : nat) : LetExpr ty Bool :=
    let idx := ($(Z.of_nat i) : Expr ty (Bit Xlen)) in
    LetE pend : Bool       <- pends @[ idx ] ;
    LetE en : Bool         <- ens @[ idx ] ;
    LetE insv : Bool       <- insvs @[ idx ] ;
    LetE prio : Bit Xlen   <- prios @[ idx ] ;
    LetE active : Bool     <- And [ #pend ; #en ; Not #insv ; Sgt #prio thresh ] ;
    RetE #active.

  (* Combinational MEIP evaluation using merge_fold_list *)
  Definition meipExpr
             (thresh : Expr ty (Bit Xlen))
             (prios : Expr ty (Array n (Bit Xlen)))
             (pends : Expr ty (Array n Bool))
             (ens : Expr ty (Array n Bool))
             (insvs : Expr ty (Array n Bool)) : LetExpr ty Bool :=
    let leaves := map (makeMeipLeaf thresh prios pends ens insvs) (seq 0 n) in
    merge_fold_list (liftLet (fun (a b : ty Bool) => RetE (Or [ #a ; #b ])))
                    (RetE (ConstBool false))
                    leaves.

  Definition plicMeip : Action ty tPlic Bool :=
    readPlicState (fun st =>
      LetL meipVal : Bool <- meipExpr st.(st_thresh) st.(st_prios) st.(st_pends) st.(st_ens) st.(st_insvs) ;
      Return #meipVal
    ).

  Definition makeClaimLeaf
             (thresh : Expr ty (Bit Xlen))
             (prios : Expr ty (Array n (Bit Xlen)))
             (pends : Expr ty (Array n Bool))
             (ens : Expr ty (Array n Bool))
             (insvs : Expr ty (Array n Bool))
             (i : nat) : LetExpr ty PlicResType :=
    let idx := ($(Z.of_nat i) : Expr ty (Bit Xlen)) in
    let srcId := ($(Z.of_nat (i + 1)) : Expr ty (Bit Xlen)) in
    LetE pend : Bool       <- pends @[ idx ] ;
    LetE en : Bool         <- ens @[ idx ] ;
    LetE insv : Bool       <- insvs @[ idx ] ;
    LetE prio : Bit Xlen   <- prios @[ idx ] ;
    LetE active : Bool     <- And [ #pend ; #en ; Not #insv ; Sgt #prio thresh ] ;
    RetE (ITE #active (mkPlicRes srcId #prio) plicResEmpty).

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

  Definition plicClaim : Action ty tPlic (Bit Xlen) :=
    readPlicState (fun st =>
      LetL bestRes : PlicResType <-
        findMaxActive st.(st_thresh) st.(st_prios) st.(st_pends) st.(st_ens) st.(st_insvs) ;
      Let claimedId : Bit Xlen <- ##bestRes`"id" ;
      If (isNotZero #claimedId) Then (
        Let claimIdx : Bit Xlen <- Sub #claimedId $1 ;
        Let updPends : Array n Bool <- st.(st_pends) @[ #claimIdx <- ConstBool false ] ;
        Let updInsvs : Array n Bool <- st.(st_insvs) @[ #claimIdx <- ConstBool true ] ;
        Act (WriteReg (plicPendingPath n) #updPends Retv) ;
        Act (WriteReg (plicInServicePath n) #updInsvs Retv) ;
        Retv
      ) ;
      Return #claimedId
    ).

  Definition plicComplete (completedId : Expr ty (Bit Xlen)) : Action ty tPlic (Bit 0) :=
    If (isNotZero completedId) Then (
      Let compIdx : Bit Xlen <- Sub completedId $1 ;
      LetA insvs : Array n Bool <- ReadReg "in_service" (plicInServicePath n) (fun v => Return #v) ;
      Let updInsvs : Array n Bool <- #insvs @[ #compIdx <- ConstBool false ] ;
      Act (WriteReg (plicInServicePath n) #updInsvs Retv) ;
      Retv
    ) ;
    Retv.

  (* Latch pending IRQs from external wires *)
  Fixpoint updatePendingWithIrqs
           (curr : nat)
           (pends : Expr ty (Array n Bool))
           (irqs : Expr ty (Array n Bool)) : Expr ty (Array n Bool) :=
    match curr with
    | 0%nat => pends
    | S rest =>
        let idx := ($(Z.of_nat rest) : Expr ty (Bit Xlen)) in
        let newPend := Or [ pends @[ idx ] ; irqs @[ idx ] ] in
        updatePendingWithIrqs rest (pends @[ idx <- newPend ]) irqs
    end.

  Definition plicStepWithIrqs (irqs : Expr ty (Array n Bool)) : Action ty tPlic (Bit 0) :=
    LetA curPends : Array n Bool <- ReadReg "pending" (plicPendingPath n) (fun v => Return #v) ;
    Let newPends : Array n Bool <- updatePendingWithIrqs n #curPends irqs ;
    WriteReg (plicPendingPath n) #newPends Retv.

  Definition plicStepWithIrqList
             (irqList : list (Expr ty Bool))
             : Action ty tPlic (Bit 0) :=
    plicStepWithIrqs (listToExprArray irqList (ConstBool false)).

End PlicCoreLogic.

(* ===========================================================================
 * 4. MMIO Interface
 * =========================================================================== *)

Section PlicMmio.
  Variable n : nat.
  Variable base : Z.
  Variable ty : Kind -> Type.
  Local Notation tPlic := (plicTree n).

  (* Pack Array n Bool into Bit Xlen (for pending and enables registers) *)
  Fixpoint packArrayBoolToWord (curr : nat) (arr : Expr ty (Array n Bool)) (acc : Expr ty (Bit Xlen)) : Expr ty (Bit Xlen) :=
    match curr with
    | 0%nat => acc
    | S rest =>
        let idx := ($(Z.of_nat rest) : Expr ty (Bit Xlen)) in
        let bitVal := ITE (arr @[ idx ]) (Const ty (Bit Xlen) (bits.of_Z Xlen (Z.shiftl 1 (Z.of_nat rest)))) $0 in
        packArrayBoolToWord rest arr (Or [ acc ; bitVal ])
    end.

  (* Unpack Bit Xlen into Array n Bool (for enables register write) *)
  Fixpoint unpackWordToArrayBool (curr : nat) (word : Expr ty (Bit Xlen)) (arr : Expr ty (Array n Bool)) : Expr ty (Array n Bool) :=
    match curr with
    | 0%nat => arr
    | S rest =>
        let idx := ($(Z.of_nat rest) : Expr ty (Bit Xlen)) in
        let bitSet := isNotZero (And [ word ; Const ty (Bit Xlen) (bits.of_Z Xlen (Z.shiftl 1 (Z.of_nat (rest + 1)))) ]) in
        unpackWordToArrayBool rest word (arr @[ idx <- bitSet ])
    end.

  Definition plicLineReadAction
             (addr : Expr ty Addr)
             : Action ty tPlic (LineReadRp PlicLineConfig) :=
    Let rawOffset : Addr <- Sub addr $(base) ;
    Let offset : Addr <- {< TruncMsb (AddrSz - 2) 2 #rawOffset, Const ty (Bit 2) Zmod.zero >} ;
    Let isClaim     : Bool <- Eq #offset $(PLIC_CLAIM_OFFSET) ;
    Let isThreshold : Bool <- Eq #offset $(PLIC_THRESHOLD_OFFSET) ;
    Let isEnable    : Bool <- Eq #offset $(PLIC_ENABLE_OFFSET) ;
    Let isPending   : Bool <- Eq #offset $(PLIC_PENDING_OFFSET) ;
    Let isPrio      : Bool <- Slt #offset $(PLIC_PENDING_OFFSET) ;
    LetIf rVal : Bit Xlen <-
      If #isClaim Then (
        @plicClaim n ty
      ) Else (
        readPlicState (fun st =>
          Let prioWord : Bit Xlen <- ZeroExtendTo Xlen (TruncMsb (AddrSz - 2) 2 #rawOffset) ;
          Let isSrcPrio : Bool <- And [ #isPrio ; Sge #prioWord $1 ; Slt #prioWord $(Z.of_nat (n + 1)) ] ;
          Let prioIdx : Bit Xlen <- Sub #prioWord $1 ;
          Let prioVal : Bit Xlen <- ITE #isSrcPrio (st.(st_prios) @[ #prioIdx ]) $0 ;
          Let nonClaimVal : Bit Xlen <-
            ITE #isThreshold st.(st_thresh) (
            ITE #isEnable (packArrayBoolToWord n st.(st_ens) $0) (
            ITE #isPending (packArrayBoolToWord n st.(st_pends) $0) (
            ITE #isPrio #prioVal $0))) ;
          Return #nonClaimVal
        )
      ) ;
    Let dataArr : Array (cfgLineBytes PlicLineConfig) (Bit 8) <-
      FromBit (Array (cfgLineBytes PlicLineConfig) (Bit 8)) #rVal ;
    @Return ty tPlic (LineReadRp PlicLineConfig) (STRUCT {
      "data" ::= #dataArr ;
      "tag"  ::= Const ty (Array (cfgNumLineTags PlicLineConfig) Bool) (getDefault _)
    }).

  Definition plicLineWriteAction
             (rq : Expr ty (LineWriteRq PlicLineConfig))
             : Action ty tPlic (Bit 0) :=
    Let rawOffset : Addr <- Sub (rq`"addr") $(base) ;
    Let offset : Addr <- {< TruncMsb (AddrSz - 2) 2 #rawOffset, Const ty (Bit 2) Zmod.zero >} ;
    Let writeWord : Bit Xlen <- ToBit (rq`"data") ;
    Let isComplete  : Bool <- Eq #offset $(PLIC_CLAIM_OFFSET) ;
    Let isThreshold : Bool <- Eq #offset $(PLIC_THRESHOLD_OFFSET) ;
    Let isEnable    : Bool <- Eq #offset $(PLIC_ENABLE_OFFSET) ;
    Let isPrio      : Bool <- Slt #offset $(PLIC_PENDING_OFFSET) ;
    If #isComplete Then (
      @plicComplete n ty #writeWord
    ) ;
    If #isThreshold Then (
      Act (WriteReg (plicThresholdPath n) #writeWord Retv) ;
      Retv
    ) ;
    If #isEnable Then (
      LetA curEns : Array n Bool <- ReadReg "enables" (plicEnablesPath n) (fun v => Return #v) ;
      Let newEns : Array n Bool <- unpackWordToArrayBool n #writeWord #curEns ;
      Act (WriteReg (plicEnablesPath n) #newEns Retv) ;
      Retv
    ) ;
    If #isPrio Then (
      Let prioWord : Bit Xlen <- ZeroExtendTo Xlen (TruncMsb (AddrSz - 2) 2 #rawOffset) ;
      If (And [ Sge #prioWord $1 ; Slt #prioWord $(Z.of_nat (n + 1)) ]) Then (
        Let prioIdx : Bit Xlen <- Sub #prioWord $1 ;
        Act (writeRegsList (priorityPathsWithKind n) #prioIdx #writeWord) ;
        Retv
      ) ;
      Retv
    ) ;
    Retv.

End PlicMmio.

Arguments plicLineReadAction n base ty addr : clear implicits.
Arguments plicLineWriteAction n base ty rq : clear implicits.

(* ===========================================================================
 * 5. MemRegion Constructor
 * =========================================================================== *)

Definition plicMemRegion
           (n : nat)
           (base : Z)
           (pfBound : Is_true ((0 <=? base) && (base + PlicSizeBytes <=? Z.shiftl 1 AddrSz))%Z)
           (pfAligned : Is_true (base mod (2 ^ Z.of_nat (cfgLgLineBytes PlicLineConfig)) =? 0)%Z)
           : MemRegion := {|
  regionName        := "plic" ;
  regionBase        := base ;
  regionSize        := Z.to_nat PlicSizeBytes ;
  regionLineCfg     := PlicLineConfig ;
  isReadOnly        := false ;
  regionKind        := @CustomMem "plic" (Z.to_nat PlicSizeBytes) PlicLineConfig
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
 * 6. System Integration Helpers
 * =========================================================================== *)

Record PlicInstance (n : nat) (regions : list MemRegion) := {
  plicIdx      : nat ;
  plicBaseAddr : Z ;
  pfBound      : Is_true ((0 <=? plicBaseAddr) && (plicBaseAddr + PlicSizeBytes <=? Z.shiftl 1 AddrSz))%Z ;
  pfAligned    : Is_true (plicBaseAddr mod (2 ^ Z.of_nat (cfgLgLineBytes PlicLineConfig)) =? 0)%Z ;
  pfNumSources : Is_true (n <? 1024)%nat ;
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

  Definition plicSampleAndStep
             (pfCount : length (collectIrqActions regions) = n)
             : Action ty memTree (Bit 0) :=
    @sampleIrqsCPS (collectIrqActions regions) (fun irqs Hlen =>
      plicAction (@plicStepWithIrqs n ty (listToExprArray irqs (ConstBool false)))
    ).

End PlicSystem.
