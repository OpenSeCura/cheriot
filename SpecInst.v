From Stdlib Require Import List String ZArith Zmod.
From Guru Require Import Library Syntax Notations.
From Cheriot Require Import Alu Spec Binary.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

(* Configurations *)
Definition mainMemConfigVal : MainMemConfig := {|
  mainMemStartAddr := MemStartAddr;
  mainMemSize := 262144; (* 256 KiB *)
  mainMemBoundProof := I;
  lgMainMemSize_ge_binary := I
|}.

Definition revBitsConfigVal : RevBitsConfig := {|
  revStartAddr := 0x00001000;
  revSizeBytes := 4096; (* covers 256 KiB *)
  revBoundProof := I;
  heapStartAddr := MemStartAddr;
  lgRevGranularity := 3; (* for 64 bytes *)
  heapBoundProof := I
|}.

Definition revokerConfigVal : RevokerConfig := {|
  revokerStartAddr := 0x00002000;
  revokerBoundProof := I;
  revokerStateInit := STRUCT_CONST {
    "start" ::= (bits.of_Z (AddrSz - LgNumBytesFullCapSz) 0);
    "end" ::= (bits.of_Z (AddrSz - LgNumBytesFullCapSz) 0);
    "epoch" ::= (bits.of_Z Xlen 0);
    "kick" ::= false
  };
  revokeAddrInit := bits.of_Z (AddrSz - LgNumBytesFullCapSz) 0
|}.

(* Instantiate the memory tree and interface *)
Definition uncoreStateInst := uncoreState mainMemConfigVal revBitsConfigVal revokerConfigVal.

Definition uncoreInstVal := uncoreInst mainMemConfigVal revBitsConfigVal revokerConfigVal.

(* Initial register state *)
Definition pccInitVal : type FullECapWithTag :=
  STRUCT_CONST {
    "tag" ::= true;
    "ecap" ::= (createRootCap ExecRootPerms);
    "addr" ::= bits.of_Z Xlen PcAddrInit
  }.

Definition regsInitVal : type (Array NumRegs FullECapWithTag) :=
  Build_SameTuple (tupleElems := pccInitVal :: List.repeat (Default FullECapWithTag) (NumRegs - 1))
    (Is_true_Nat_eq_implies eq_refl).

Definition scrsInitVal : type Scrs :=
  STRUCT_CONST {
    "mtcc" ::= ExecRoot;
    "mtdc" ::= MemRoot;
    "mscratchc" ::= SealRoot;
    "mepcc" ::= ExecRoot
  }.

Definition csrsInitVal : type Csrs := Default _.
Definition interruptsInitVal : type Interrupts := Default _.
Definition tohostAddrVal : type Addr := bits.of_Z Xlen tohostAddr.

(* The fully instantiated Spec *)
Definition specInstTree :=
  specTree uncoreStateInst regsInitVal scrsInitVal csrsInitVal interruptsInitVal.

Definition specInst : Mod specInstTree :=
  spec uncoreInstVal regsInitVal scrsInitVal csrsInitVal interruptsInitVal tohostAddrVal.
