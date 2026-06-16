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
      Leaf "predPcVal" (EReg (Build_Reg Addr (Some (getDefault _))));
      Leaf "predPcCap" (EReg (Build_Reg ECap (Some (getDefault _))));
      Leaf "predPcTag" (EReg (Build_Reg Bool (Some (getDefault _))));
      Leaf "waits" (EReg (Build_Reg (Array NumRegs Bool) (Some (getDefault _))));
      Leaf "regs" (EReg (Build_Reg (Array NumRegs FullECapWithTag) (Some (getDefault _))));
      Leaf "csrs" (EReg (Build_Reg Csrs (Some (getDefault _))));
      Leaf "scrs" (EReg (Build_Reg Scrs (Some (STRUCT_CONST { "mtcc" ::= ExecRoot;
                                                              "mtdc" ::= MemRoot;
                                                              "mscratchc" ::= SealRoot;
                                                              "mepcc" ::= ExecRoot}))));
      Leaf "interruptsReg" (EReg (Build_Reg Interrupts (Some (getDefault _))))
    ].
End Pipeline.
