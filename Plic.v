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
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics Composition MergeFold.
From Cheriot Require Import SpecDefines SpecDevice.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Local Open Scope guru_scope.

Local Abbreviation ByteSz := 8%Z.

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
Definition PlicLineConfig        : LineConfig := {|
  cfgLgLineBytes := Z.to_nat LgNumBytesFullCapSz ;
  cfgHasTags     := false ;
  cfgLinePf      := I
|}.

(* ===========================================================================
 * Tree Structure (Ordered by MMIO Offset)
 * =========================================================================== *)

Section Plic.
  Variable dom : string.

  Definition priorityLeaves (n : nat) : list (Tree DomainElem) :=
    map (fun idx =>
      Leaf ("prio_" ++ hex_string_of_Z (Z.of_nat idx))%string
           (dom, EReg (Build_Reg (Bit Xlen) (Some Zmod.zero) false))
    ) (seq 0 n).

  Definition pendingLeaves (n : nat) : list (Tree DomainElem) :=
    map (fun idx =>
      Leaf ("pend_" ++ hex_string_of_Z (Z.of_nat idx))%string
           (dom, EReg (Build_Reg Bool (Some false) false))
    ) (seq 0 n).

  Definition plicNumEnableWords (n : nat) : nat :=
    Nat.div (n + Z.to_nat (Xlen - 1)) (Z.to_nat Xlen).

  Definition enableLeaves (n : nat) : list (Tree DomainElem) :=
    map (fun idx =>
      Leaf ("en_" ++ hex_string_of_Z (Z.of_nat idx))%string
           (dom, EReg (Build_Reg (Bit Xlen) (Some Zmod.zero) false))
    ) (seq 0 (plicNumEnableWords n)).

  Definition inServiceLeaves (n : nat) : list (Tree DomainElem) :=
    map (fun idx =>
      Leaf ("insv_" ++ hex_string_of_Z (Z.of_nat idx))%string
           (dom, EReg (Build_Reg Bool (Some false) false))
    ) (seq 0 n).

  Definition plicChildren (n : nat) : list (Tree DomainElem) :=
    [ Node "priorities" (priorityLeaves n) ;
      Node "pending"    (pendingLeaves n) ;
      Node "enables"    (enableLeaves n) ;
      Leaf "threshold"  (dom, EReg (Build_Reg (Bit Xlen) (Some Zmod.zero) false)) ;
      Leaf "claim"      (dom, EReg (Build_Reg (Bit Xlen) (Some Zmod.zero) false)) ;
      Leaf "meip"       (dom, EReg (Build_Reg Bool       (Some false)     false)) ;
      Node "in_service" (inServiceLeaves n) ;
      Leaf "UartIrq"    (dom, ERecv Bool) ].

  Definition plicTree (n : nat) : Tree DomainElem :=
    Node "plic" (plicChildren n).

  Section PlicPaths.
    Variable n : nat.
    Local Abbreviation tPlic := (plicTree n).

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
    Definition plicMeipPath : RegPath tPlic :=
      getChildRegPathTree tPlic "meip".
    Definition plicUartIrqPath : RecvPath tPlic :=
      getChildRecvPathTree tPlic "UartIrq".

    Definition priorityPathsWithKind : list (RegOfKind (t:=tPlic) (Bit Xlen)) :=
      map (embedRegOfKind plicPrioritiesNodePath)
          (getTreeRegsOfKind (Bit Xlen) (getNode plicPrioritiesNodePath)).

    Definition pendingPathsWithKind : list (RegOfKind (t:=tPlic) Bool) :=
      map (embedRegOfKind plicPendingNodePath)
          (getTreeRegsOfKind Bool (getNode plicPendingNodePath)).

    Definition enablesPathsWithKind : list (RegOfKind (t:=tPlic) (Bit Xlen)) :=
      map (embedRegOfKind plicEnablesNodePath)
          (getTreeRegsOfKind (Bit Xlen) (getNode plicEnablesNodePath)).

    Definition inServicePathsWithKind : list (RegOfKind (t:=tPlic) Bool) :=
      map (embedRegOfKind plicInServiceNodePath)
          (getTreeRegsOfKind Bool (getNode plicInServiceNodePath)).
  End PlicPaths.

  (* ===========================================================================
   * Core Combinational & Sequential Logic
   * =========================================================================== *)

  Record PlicState (ty : Kind -> Type) (n : nat) := {
    st_thresh  : ty (Bit Xlen) ;
    st_claim   : ty (Bit Xlen) ;
    st_prios   : ty (Array n (Bit Xlen)) ;
    st_pends   : ty (Array n Bool) ;
    st_enWords : ty (Array (plicNumEnableWords n) (Bit Xlen)) ;
    st_ens     : ty (Array n Bool) ;
    st_insvs   : ty (Array n Bool)
  }.
  Arguments st_thresh {ty n} p.
  Arguments st_claim {ty n} p.
  Arguments st_prios {ty n} p.
  Arguments st_pends {ty n} p.
  Arguments st_enWords {ty n} p.
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
    LetE a_wins : Bool <- Or [Ugt #a_prio #b_prio; And[Eq #a_prio #b_prio; Ule #a_id #b_id]];
    RetE (ITE #a_wins #a #b).

  Section PlicCoreLogic.
    Variable n : nat.
    Local Abbreviation tPlic := (plicTree n).
    Variable ty : Kind -> Type.

    Definition listToExprArray {k : Kind} {n : nat}
      (ls : list (ty k)) (def : Expr ty k) : Expr ty (Array n k) :=
      ArrayBuilder (fun (i : FinType n) => nth (finNum i) (map (Var _ _) ls) def).

    Fixpoint readRegs
             {k : Kind}
             (paths : list (RegOfKind (t:=tPlic) k))
             {ans : Kind}
             (k_cont : list (ty k) -> Action ty tPlic ans)
             : Action ty tPlic ans :=
      match paths with
      | nil => k_cont nil
      | rk :: rest =>
          ReadReg "" rk.(rk_path) (fun val =>
            let pf := Kind_eqb_eq _ _ rk.(rk_pf) in
            let c_val := eq_rect (regKind (getRegFromPath rk.(rk_path))) (fun K => ty K) val _ pf in
            readRegs rest (fun vals => k_cont (c_val :: vals))
          )
      end.

    Fixpoint readAllSources
             (prios : list (RegOfKind (t:=tPlic) (Bit Xlen)))
             (pends : list (RegOfKind (t:=tPlic) Bool))
             (insvs : list (RegOfKind (t:=tPlic) Bool))
             {ans : Kind}
             (k : list (ty (Bit Xlen)) ->
                  list (ty Bool) ->
                  list (ty Bool) ->
                  Action ty tPlic ans)
             : Action ty tPlic ans :=
      match prios, pends, insvs with
      | rPrio :: rPrios', rPend :: rPends', rInsv :: rInsvs' =>
          ReadReg "val_prio" rPrio.(rk_path) (fun val_prio =>
          ReadReg "val_pend" rPend.(rk_path) (fun val_pend =>
          ReadReg "val_insv" rInsv.(rk_path) (fun val_insv =>
            let pf_prio := Kind_eqb_eq _ _ rPrio.(rk_pf) in
            let pf_pend := Kind_eqb_eq _ _ rPend.(rk_pf) in
            let pf_insv := Kind_eqb_eq _ _ rInsv.(rk_pf) in
            let c_prio := eq_rect (regKind (getRegFromPath rPrio.(rk_path))) (fun K => ty K) val_prio _ pf_prio in
            let c_pend := eq_rect (regKind (getRegFromPath rPend.(rk_path))) (fun K => ty K) val_pend _ pf_pend in
            let c_insv := eq_rect (regKind (getRegFromPath rInsv.(rk_path))) (fun K => ty K) val_insv _ pf_insv in
            readAllSources rPrios' rPends' rInsvs' (fun pList dList iList =>
              k (c_prio :: pList)
                (c_pend :: dList)
                (c_insv :: iList)
            )
          )))
      | _, _, _ => k nil nil nil
      end.

    Definition readPlicState {ans : Kind}
               (k : PlicState ty n -> Action ty tPlic ans) : Action ty tPlic ans :=
      LetA thresh : Bit Xlen <- ReadReg "threshold" (plicThresholdPath n) (fun v => Return #v) ;
      LetA claim  : Bit Xlen <- ReadReg "claim" (plicClaimPath n) (fun v => Return #v) ;
      readRegs (enablesPathsWithKind n) (fun enList =>
        readAllSources (priorityPathsWithKind n)
                       (pendingPathsWithKind n)
                       (inServicePathsWithKind n)
                       (fun prioList pendList insvList =>
          Let prios   : Array n (Bit Xlen) <- listToExprArray prioList ($0 : Expr ty (Bit Xlen)) ;
          Let pends   : Array n Bool       <- listToExprArray pendList (ConstBool false) ;
          Let insvs   : Array n Bool       <- listToExprArray insvList (ConstBool false) ;
          Let enWords : Array (plicNumEnableWords n) (Bit Xlen) <-
            listToExprArray enList ($0 : Expr ty (Bit Xlen)) ;
          Let ens     : Array n Bool       <-
            ArrayBuilder (fun (i : FinType n) =>
              let wordExpr := nth (finNum i / Z.to_nat Xlen)%nat (map (Var _ _) enList) ($0 : Expr ty (Bit Xlen)) in
              let wordBits := FromBit (Array (Z.to_nat Xlen) Bool) wordExpr in
              readNatToFinType (ConstBool false) (ReadArrayConst wordBits) (finNum i mod Z.to_nat Xlen)%nat
            ) ;
          k {| st_thresh  := thresh ;
               st_claim   := claim ;
               st_prios   := prios ;
               st_pends   := pends ;
               st_enWords := enWords ;
               st_ens     := ens ;
               st_insvs   := insvs |}
        )
      ).

    Definition makeClaimLeaf
               (thresh : ty (Bit Xlen))
               (prios : ty (Array n (Bit Xlen)))
               (pends : ty (Array n Bool))
               (ens : ty (Array n Bool))
               (insvs : ty (Array n Bool))
               (i : nat) : LetExpr ty PlicResType :=
      let idx := ($(Z.of_nat i) : Expr ty (Bit Xlen)) in
      LetE pend   : Bool     <- #pends @[ idx ] ;
      LetE en     : Bool     <- #ens @[ idx ] ;
      LetE insv   : Bool     <- #insvs @[ idx ] ;
      LetE prio   : Bit Xlen <- #prios @[ idx ] ;
      LetE active : Bool     <- And [ #pend ; #en ; Not #insv ; Ugt #prio #thresh ] ;
      RetE (ITE #active (mkPlicRes idx #prio) plicResEmpty).

    (* Combinational claim search using merge_fold_list tournament tree *)
    Definition findMaxActive
               (thresh : ty (Bit Xlen))
               (prios : ty (Array n (Bit Xlen)))
               (pends : ty (Array n Bool))
               (ens : ty (Array n Bool))
               (insvs : ty (Array n Bool))
               : LetExpr ty PlicResType :=
      let leaves := map (makeClaimLeaf thresh prios pends ens insvs) (seq 0 n) in
      merge_fold_list (liftLet plicResComb) (RetE plicResEmpty) leaves.

    Definition updateClaim : Action ty tPlic (Bit 0) :=
      readPlicState (fun st =>
        LetL bestRes : PlicResType <-
          findMaxActive st.(st_thresh) st.(st_prios) st.(st_pends) st.(st_ens) st.(st_insvs) ;
        Let  bestId  : Bit Xlen    <- ##bestRes`"id" ;
        Act (WriteReg (plicClaimPath n) #bestId Retv) ;
        If (isZero #bestId) Then (
          WriteReg (plicMeipPath n) (ConstBool false) Retv
        ) ;
        Retv
      ).

    Definition plicSampleMeip : Action ty tPlic (Bit 0) :=
      ReadReg "claim" (plicClaimPath n) (fun val_claim =>
        If (isNotZero (Var _ _ val_claim)) Then (
          WriteReg (plicMeipPath n) (ConstBool true) Retv
        ) ;
        Retv
      ).

    Definition plicMeip : Action ty tPlic Bool :=
      ReadReg "meip" (plicMeipPath n) (fun val_meip =>
        Return (Var _ _ val_meip)
      ).

    Definition plicClaim (claimedId : ty (Bit Xlen)) : Action ty tPlic (Bit 0) :=
      If (isNotZero #claimedId) Then (
        Act (writeRegsList (pendingPathsWithKind n) #claimedId (ConstBool false)) ;
        Act (writeRegsList (inServicePathsWithKind n) #claimedId (ConstBool true)) ;
        Act (WriteReg (plicClaimPath n) $0 Retv) ;
        Act (WriteReg (plicMeipPath n) (ConstBool false) Retv) ;
        Retv
      ) ;
      Retv.

    Definition plicComplete (completedId : ty (Bit Xlen)) : Action ty tPlic (Bit 0) :=
      If (isNotZero #completedId) Then (
        Act (writeRegsList (inServicePathsWithKind n) #completedId (ConstBool false)) ;
        Retv
      ) ;
      Retv.

    Definition updatePendingLeaf
               (pendRk : RegOfKind (t:=tPlic) Bool)
               (insvRk : RegOfKind (t:=tPlic) Bool)
               (irqVal : ty Bool)
               : Action ty tPlic (Bit 0) :=
      let pf_pend := Kind_eqb_eq _ _ pendRk.(rk_pf) in
      let pf_insv := Kind_eqb_eq _ _ insvRk.(rk_pf) in
      ReadReg "" pendRk.(rk_path) (fun val_pend =>
      ReadReg "" insvRk.(rk_path) (fun val_insv =>
        let c_pend := eq_rect (regKind (getRegFromPath pendRk.(rk_path))) (fun K => ty K) val_pend _ pf_pend in
        let c_insv := eq_rect (regKind (getRegFromPath insvRk.(rk_path))) (fun K => ty K) val_insv _ pf_insv in
        let newPend := Or [ Var _ _ c_pend ; And [ #irqVal ; Not (Var _ _ c_insv) ] ] in
        let c_newPend := eq_rect Bool (fun K => Expr ty K) newPend _ (eq_sym pf_pend) in
        Act (WriteReg pendRk.(rk_path) c_newPend Retv) ;
        Retv
      )).

  End PlicCoreLogic.

  (* ===========================================================================
   * MMIO Interface
   * =========================================================================== *)

  Section PlicMmio.
    Variable n : nat.
    Variable base : Z.
    Variable ty : Kind -> Type.
    Local Abbreviation tPlic := (plicTree n).
    Local Abbreviation numLineWords := (Z.to_nat (NumBytesFullCapSz / NumBytesXlen)).

    Definition boolArrayToWordArray
               (arr : Expr ty (Array n Bool))
               : Expr ty (Array (plicNumEnableWords n) (Bit Xlen)) :=
      FromBit (Array (plicNumEnableWords n) (Bit Xlen))
              (castBits (add_sub_cancel (kindSize (Array (plicNumEnableWords n) (Bit Xlen)))
                                        (kindSize (Array n Bool)))
                        (ZeroExtendTo (kindSize (Array (plicNumEnableWords n) (Bit Xlen)))
                                      (ToBit arr))).

    Record PlicLineDecode := {
      dec_isThreshClaim : Expr ty Bool ;
      dec_isEnable      : Expr ty Bool ;
      dec_isPending     : Expr ty Bool ;
      dec_isPrio        : Expr ty Bool ;
      dec_prioWordIdx   : Expr ty (Bit (PlicOffsetSz - LgNumBytesXlen)) ;
      dec_pendWordIdx   : Expr ty (Bit (PlicOffsetSz - LgNumBytesXlen)) ;
      dec_enWordIdx     : Expr ty (Bit (PlicOffsetSz - LgNumBytesXlen)) ;
      dec_touchesClaim  : Expr ty Bool ;
      dec_touchesConfig : Expr ty Bool
    }.

    Definition getWordIdx (offset : ty (Bit PlicOffsetSz)) (regionOffset : Z)
               : Expr ty (Bit (PlicOffsetSz - LgNumBytesXlen)) :=
      TruncMsb (PlicOffsetSz - LgNumBytesXlen) LgNumBytesXlen (Sub #offset $(regionOffset)).

    Definition decodePlicLine {ans : Kind}
               (addr : Expr ty Addr)
               (dataMask : Expr ty (Array (cfgLineBytes PlicLineConfig) Bool))
               (k : PlicLineDecode -> Action ty tPlic ans)
               : Action ty tPlic ans :=
      Let offset        <- getMemOffset base PlicSizeBytes addr ;
      Let isThreshClaim : Bool <- Eq  #offset $(PLIC_THRESHOLD_OFFSET) ;
      Let isEnable      : Bool <- Uge #offset $(PLIC_ENABLE_OFFSET) ;
      Let isPending     : Bool <- Uge #offset $(PLIC_PENDING_OFFSET) ;
      Let isPrio        : Bool <- ConstBool true ;
      Let prioWordIdx   <- getWordIdx offset PLIC_PRIORITY_BASE ;
      Let pendWordIdx   <- getWordIdx offset PLIC_PENDING_OFFSET ;
      Let enWordIdx     <- getWordIdx offset PLIC_ENABLE_OFFSET ;
      Let maskBits      <- ToBit dataMask ;
      Let hasLo         : Bool <- isNotZero (TruncLsb NumBytesXlen NumBytesXlen #maskBits) ;
      Let hasHi         : Bool <- isNotZero (TruncMsb NumBytesXlen NumBytesXlen #maskBits) ;
      Let touchesClaim  : Bool <- And [ #isThreshClaim ; #hasHi ] ;
      Let touchesConfig : Bool <- Or [ #hasLo ; And [ #hasHi ; Not #isThreshClaim ] ] ;
      k {| dec_isThreshClaim := #isThreshClaim ;
           dec_isEnable      := #isEnable ;
           dec_isPending     := #isPending ;
           dec_isPrio        := #isPrio ;
           dec_prioWordIdx   := #prioWordIdx ;
           dec_pendWordIdx   := #pendWordIdx ;
           dec_enWordIdx     := #enWordIdx ;
           dec_touchesClaim  := #touchesClaim ;
           dec_touchesConfig := #touchesConfig |}.

    Definition sliceLineWords {m : nat} {sz : Z}
               (arr : Expr ty (Array m (Bit Xlen)))
               (wordIdx : Expr ty (Bit sz))
               : Expr ty (Bit FullCapSz) :=
      ToBit (Combinators.slice arr wordIdx numLineWords).

    Definition writeLineWords {sz : Z}
               (paths : list (RegOfKind (t:=tPlic) (Bit Xlen)))
               (wordIdx : Expr ty (Bit sz))
               (words : Expr ty (Array numLineWords (Bit Xlen)))
               : Action ty tPlic (Bit 0) :=
      fold_right (fun (i : FinType numLineWords) acc =>
        Act (writeRegsList paths (Add [ wordIdx ; $(Z.of_nat (finNum i)) ]) (ReadArrayConst words i)) ;
        acc
      ) Retv (genFinType numLineWords).

    Definition readPlicLine
               (st : PlicState ty n)
               (d : PlicLineDecode)
               : Expr ty (Array (cfgLineBytes PlicLineConfig) (Bit ByteSz)) :=
      let thresh         := st.(st_thresh) in
      let claim          := st.(st_claim) in
      let prios          := st.(st_prios) in
      let pends          := st.(st_pends) in
      let enWords        := st.(st_enWords) in
      let prioVal        := sliceLineWords #prios d.(dec_prioWordIdx) in
      let pendVal        := sliceLineWords (boolArrayToWordArray #pends) d.(dec_pendWordIdx) in
      let enVal          := sliceLineWords #enWords d.(dec_enWordIdx) in
      let threshClaimVal := {< #claim, #thresh >} in
      FromBit (Array (cfgLineBytes PlicLineConfig) (Bit ByteSz))
              (Or [ ITE0 d.(dec_isPrio)        prioVal ;
                    ITE0 d.(dec_isPending)     pendVal ;
                    ITE0 d.(dec_isEnable)      enVal ;
                    ITE0 d.(dec_isThreshClaim) threshClaimVal ]).

    Definition plicLineReadAction
               (_ : ReadPortSel false)
               (addr : ty Addr)
               (dataMask : ty (Array (cfgLineBytes PlicLineConfig) Bool))
               : Action ty tPlic (LineReadRp PlicLineConfig false) :=
      decodePlicLine #addr #dataMask (fun d =>
      readPlicState (fun st =>
        Let readBytes : Array (cfgLineBytes PlicLineConfig) (Bit ByteSz) <- readPlicLine st d ;
        If d.(dec_touchesClaim) Then (
          @plicClaim n ty st.(st_claim)
        ) ;
        @Return ty tPlic (LineReadRp PlicLineConfig false) (STRUCT {
          "data" ::= #readBytes ;
          "tag"  ::= Const ty (Array (cfgNumLineTags PlicLineConfig false) Bool) (getDefault _)
        })
      )).

    Definition plicLineWriteAction
               (rq : ty (LineWriteRq PlicLineConfig false))
               : Action ty tPlic (Bit 0) :=
      decodePlicLine (##rq`"addr") (##rq`"dataMask") (fun d =>
      readPlicState (fun st =>
        Let oldBytes : Array (cfgLineBytes PlicLineConfig) (Bit ByteSz) <- readPlicLine st d ;
        Let newBytes : Array (cfgLineBytes PlicLineConfig) (Bit ByteSz) <-
          ArrayBuilder (fun i =>
            ITE (ReadArrayConst (##rq`"dataMask") i)
                (ReadArrayConst (##rq`"data") i)
                (ReadArrayConst #oldBytes i)) ;
        Let newWords : Array numLineWords (Bit Xlen) <-
          FromBit (Array numLineWords (Bit Xlen)) (ToBit ##newBytes) ;
        Let cleanEnWords : Array numLineWords (Bit Xlen) <-
          ITE (isZero d.(dec_enWordIdx))
              ((##newWords) $[ 0%nat <- {< TruncMsb (Xlen - 1) 1 ((##newWords) $[0%nat]), Const ty (Bit 1) Zmod.zero >} ])
              #newWords ;
        Let cleanPrioWords : Array numLineWords (Bit Xlen) <-
          ITE (isZero d.(dec_prioWordIdx))
              ((##newWords) $[ 0%nat <- $0 ])
              #newWords ;
        If d.(dec_isThreshClaim) Then (
          Act (WriteReg (plicThresholdPath n) ((##newWords) $[0%nat]) Retv) ;
          If d.(dec_touchesClaim) Then (
            Let completedId : Bit Xlen <- (##newWords) $[1%nat] ;
            @plicComplete n ty completedId
          ) ;
          Retv
        ) ;
        If d.(dec_isEnable) Then (
          writeLineWords (enablesPathsWithKind n) d.(dec_enWordIdx) #cleanEnWords
        ) ;
        If d.(dec_isPrio) Then (
          writeLineWords (priorityPathsWithKind n) d.(dec_prioWordIdx) #cleanPrioWords
        ) ;
        If d.(dec_touchesConfig) Then (
          Act (WriteReg (plicClaimPath n) $0 Retv) ;
          Act (WriteReg (plicMeipPath n) (ConstBool false) Retv) ;
          Retv
        ) ;
        Retv
      )).

  End PlicMmio.

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
    regionDom         := dom ;
    regionBase        := base ;
    regionSize        := PlicSizeBytes ;
    regionLineCfg     := PlicLineConfig ;
    isReadOnly        := false ;
    hasExtraFetchPort := false ;
    regionKind        := @CustomMem "plic" PlicSizeBytes PlicLineConfig false
                                    (plicChildren n)
                                    (@plicLineReadAction n base)
                                    (@plicLineWriteAction n base)
                                    None ;
    regionInMemory    := pfBound ;
    regionBaseAligned := pfAligned ;
    regionSizeAligned := I
  |}.

  (* ===========================================================================
   * System Integration Helpers
   * =========================================================================== *)

  Record PlicInstance (n : nat) (regions : list MemRegion) := {
    plicIdx      : nat ;
    plicBaseAddr : Z ;
    pfBound      : Is_true ((0 <=? plicBaseAddr) && (plicBaseAddr + PlicSizeBytes <=? Z.shiftl 1 AddrSz))%Z ;
    pfAligned    : Is_true (plicBaseAddr mod (2 ^ Z.of_nat (cfgLgLineBytes PlicLineConfig)) =? 0)%Z ;
    pfNumSources : Is_true (n <=? 1024)%nat ;
    pfPlic       : nth_error regions plicIdx = Some (@plicMemRegion n plicBaseAddr pfBound pfAligned)
  }.

  Definition plicRegion {n regions} (plic : PlicInstance n regions) : MemRegion :=
    @plicMemRegion n plic.(plicBaseAddr) plic.(pfBound) plic.(pfAligned).

  Section PlicSystem.
    Variable n : nat.
    Variable regions : list MemRegion.
    Variable plic : PlicInstance n regions.
    Variable ty : Kind -> Type.

    Local Abbreviation memTree := (specMemTree regions).

    Definition plicAction {k : Kind} (act : Action ty (plicTree n) k) : Action ty memTree k :=
      nthRegionAction plic.(plicIdx) regions (plicRegion plic) plic.(pfPlic) act.

    Definition plicMeipSystem : Action ty memTree Bool :=
      plicAction (@plicMeip n ty).

    Definition plicUartIrqAction : Action ty memTree Bool :=
      plicAction (Recv "uartIrq" (plicUartIrqPath n) (fun v => Return #v)).

    Fixpoint plicPendingStepsHelper
             (acts : list (Action ty memTree Bool))
             (pends : list (RegOfKind (t:=plicTree n) Bool))
             (insvs : list (RegOfKind (t:=plicTree n) Bool))
             : list (Action ty memTree (Bit 0)) :=
      match acts, pends, insvs with
      | act :: restActs, pendRk :: restPends, insvRk :: restInsvs =>
          (LetA irqVal : Bool <- act ;
           plicAction (@updatePendingLeaf n ty pendRk insvRk irqVal))
          :: plicPendingStepsHelper restActs restPends restInsvs
      | _, _, _ => []
      end.

    Definition plicPendingsSteps
               (pfCount : S (S (length (collectIrqActions regions))) = n)
               : list (Action ty memTree (Bit 0)) :=
      match pendingPathsWithKind n, inServicePathsWithKind n with
      | _ :: devPends, _ :: devInsvs =>
          plicPendingStepsHelper
            (map (fun f => f ty) (collectIrqActions regions) ++ [plicUartIrqAction])
            devPends
            devInsvs
      | _, _ => []
      end.

    Definition plicClaimStep : Action ty memTree (Bit 0) :=
      plicAction (@updateClaim n ty).

    Definition plicSampleMeipStep : Action ty memTree (Bit 0) :=
      plicAction (@plicSampleMeip n ty).

  End PlicSystem.

End Plic.
