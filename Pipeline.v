From Stdlib Require Import String List ZArith Zmod.
Require Import Guru.Library Guru.Syntax Guru.Notations.
Require Import Cheriot.Alu Cheriot.BankedMem Cheriot.Spec.

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

  Definition allRegs :=
    [ ("predPcVal", Build_Reg Addr (Default _));
      ("predPcCap", Build_Reg ECap (Default _));
      ("predPcTag", Build_Reg Bool (Default _));
      ("waits", Build_Reg (Array NumRegs Bool) (Default _));
      ("regs", Build_Reg (Array NumRegs FullECapWithTag) (Default _));
      ("csrs", Build_Reg Csrs (Default _));
      ("scrs", Build_Reg Scrs (STRUCT_CONST { "mtcc" ::= ExecRoot;
                                              "mtdc" ::= MemRoot;
                                              "mscratchc" ::= SealRoot;
                                              "mepcc" ::= ExecRoot}));
      ("interruptsReg", Build_Reg Interrupts (Default _))].
End Pipeline.
