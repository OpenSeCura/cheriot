From Stdlib Require Import String List ZArith Zmod.
Require Import Guru.Library Guru.Syntax Guru.Notations.
Require Import Cheriot.Alu Cheriot.Spec.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.

Section Pipeline.
  Local Open Scope guru_scope.
  Definition NumIssue := 1.

  Variable mtccVal : type Addr.
  
  Local Open Scope string_scope.

  Definition FetchOutElem := STRUCT_TYPE {
                                 "pcAluOut" ::= PcAluOut ;
                                 "inst" ::= Inst }.
  Definition FetchOut := STRUCT_TYPE {
                             "pcTag" :: Bool ;
                             "pcCap" :: ECap ;
                             "elems" :: Array NumIssue FetchOutElem }.

  Definition allRegs : Tree Elem :=
    Node "" [
      Leaf "predPcVal" (EReg (Build_Reg Addr (Some (Default _))));
      Leaf "predPcCap" (EReg (Build_Reg ECap (Some (Default _))));
      Leaf "predPcTag" (EReg (Build_Reg Bool (Some (Default _))));
      Leaf "waits" (EReg (Build_Reg (Array NumRegs Bool) (Some (Default _))));
      Leaf "regs" (EReg (Build_Reg (Array NumRegs FullECapWithTag) (Some (Default _))));
      Leaf "csrs" (EReg (Build_Reg Csrs (Some (Default _))));
      Leaf "scrs" (EReg (Build_Reg Scrs (Some (STRUCT_CONST { "mtcc" ::= ExecRoot;
                                                              "mtdc" ::= MemRoot;
                                                              "mscratchc" ::= SealRoot;
                                                              "mepcc" ::= ExecRoot}))));
      Leaf "interruptsReg" (EReg (Build_Reg Interrupts (Some (Default _))))
    ].
End Pipeline.
