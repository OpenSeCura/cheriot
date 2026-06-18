From Stdlib Require Import List String ZArith Zmod.
From Guru Require Import Library Syntax Notations Compiler.
From Cheriot Require Import Alu Spec Binary.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

Definition MainMemSize : Z := 256 * 2^10.
Definition LgRevGranularity := 3.
Definition RevSizeBytes := Z.to_nat (MainMemSize / (8 * 2^LgRevGranularity)).

(* Configurations *)
Definition mainMemConfigVal : MainMemConfig := {|
  mainMemStartAddr := MemStartAddr;
  mainMemSize := Z.to_nat MainMemSize;
  mainMemBoundProof := I;
  lgMainMemSize_ge_binary := I
|}.

Definition revBitsConfigVal : RevBitsConfig := {|
  revStartAddr := 0x00001000;
  revSizeBytes := RevSizeBytes;
  revBoundProof := I;
  heapStartAddr := MemStartAddr;
  lgRevGranularity := LgRevGranularity;
  heapBoundProof := I
|}.

Definition revokerConfigVal : RevokerConfig := {|
  revokerStartAddr := 0x00002000;
  revokerBoundProof := I;
  revokerStateInit := STRUCT_CONST {
    "start" ::= (bits.of_Z (AddrSz - LgNumBytesFullCapSz) 0);
    "endAddr" ::= (bits.of_Z (AddrSz - LgNumBytesFullCapSz) 0);
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
  Build_SameTuple (tupleElems := pccInitVal :: List.repeat (getDefault FullECapWithTag) (NumRegs - 1))
    (Is_true_Nat_eq_implies eq_refl).

Definition scrsInitVal : type Scrs :=
  STRUCT_CONST {
    "mtcc" ::= ExecRoot;
    "mtdc" ::= MemRoot;
    "mscratchc" ::= SealRoot;
    "mepcc" ::= ExecRoot
  }.

Definition csrsInitVal : type Csrs := getDefault _.
Definition interruptsInitVal : type Interrupts := getDefault _.
Definition tohostAddrVal : type Addr := bits.of_Z Xlen tohostAddr.

(* The fully instantiated Spec *)
Definition specInstTree :=
  specTree uncoreStateInst regsInitVal scrsInitVal csrsInitVal interruptsInitVal.

Definition specInst : Mod specInstTree :=
  spec uncoreInstVal regsInitVal scrsInitVal csrsInitVal interruptsInitVal tohostAddrVal.

From Guru Require Import Simulator Extraction.

Definition main : IO unit :=
  evalModCyclesIO specInstTree 100 specInst.

Set Extraction Output Directory ".".
Extraction "Simulate" main.
