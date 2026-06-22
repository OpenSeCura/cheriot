(*
 * Copyright 2026 Google LLC (Cherified Team)
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

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.

Local Open Scope Z_scope.

Definition Xlen : Z := 32.

Local Open Scope guru_scope.

Definition LgXlen   := Eval compute in Z.log2_up Xlen.
Definition Data     := Eval compute in Bit Xlen.
Definition AddrSz   := Eval compute in Xlen.
Definition Addr     := Eval compute in Bit AddrSz.
Definition LgAddrSz := Eval compute in Z.log2_up AddrSz.
Definition ExpSz    := Eval compute in LgAddrSz.
Definition NumBytesXlen := Eval compute in (Xlen / 8).

Definition CapBSz   := 9.
Definition CapOTypeSz := 3.

Definition CapPerms := STRUCT_TYPE { "U0" :: Bool ;
                                     "SE" :: Bool ;
                                     "US" :: Bool ;
                                     "EX" :: Bool ;
                                     "SR" :: Bool ;
                                     "MC" :: Bool ;
                                     "LD" :: Bool ;
                                     "SL" :: Bool ;
                                     "LM" :: Bool ;
                                     "SD" :: Bool ;
                                     "LG" :: Bool ;
                                     "GL" :: Bool }.

Definition ECap := STRUCT_TYPE { "R"     :: Bool;
                                 "perms" :: CapPerms;
                                 "oType" :: Bit CapOTypeSz;
                                 "E"     :: Bit ExpSz;
                                 "top"   :: Bit (AddrSz + 1);
                                 "base"  :: Bit (AddrSz + 1) }.

Definition FullECapWithTag := STRUCT_TYPE { "tag" :: Bool;
                                            "ecap" :: ECap;
                                            "addr" :: Addr }.

Definition isSealed ty (ecap: ty ECap) : Expr ty Bool := isNotZero (##ecap`"oType").

Definition fixPerms ty (perms: ty CapPerms) : Expr ty CapPerms :=
  (ITE (And [##perms`"EX"; ##perms`"LD"; ##perms`"MC"])
     (##perms
        `{ "U0" <- ConstTBool false }
        `{ "SE" <- ConstTBool false }
        `{ "US" <- ConstTBool false }
        `{ "SL" <- ConstTBool false }
        `{ "SD" <- ConstTBool false })
     (ITE (And [##perms`"LD"; ##perms`"MC"; ##perms`"SD"])
        (##perms
           `{ "U0" <- ConstTBool false }
           `{ "SE" <- ConstTBool false }
           `{ "US" <- ConstTBool false }
           `{ "EX" <- ConstTBool false }
           `{ "SR" <- ConstTBool false })
        (ITE (And [##perms`"LD"; ##perms`"MC"])
           (##perms
              `{ "U0" <- ConstTBool false }
              `{ "SE" <- ConstTBool false }
              `{ "US" <- ConstTBool false }
              `{ "EX" <- ConstTBool false }
              `{ "SR" <- ConstTBool false }
              `{ "SL" <- ConstTBool false }
              `{ "SD" <- ConstTBool false })
           (ITE (And [##perms`"SD"; ##perms`"MC"])
              (##perms
                 `{ "U0" <- ConstTBool false }
                 `{ "SE" <- ConstTBool false }
                 `{ "US" <- ConstTBool false }
                 `{ "EX" <- ConstTBool false }
                 `{ "SR" <- ConstTBool false }
                 `{ "LD" <- ConstTBool false }
                 `{ "SL" <- ConstTBool false }
                 `{ "LM" <- ConstTBool false }
                 `{ "LG" <- ConstTBool false })
              (ITE (Or [##perms`"LD"; ##perms`"SD"])
                 (##perms
                 `{ "U0" <- ConstTBool false }
                 `{ "SE" <- ConstTBool false }
                 `{ "US" <- ConstTBool false }
                 `{ "EX" <- ConstTBool false }
                 `{ "SR" <- ConstTBool false }
                 `{ "MC" <- ConstTBool false }
                 `{ "SL" <- ConstTBool false }
                 `{ "LM" <- ConstTBool false }
                 `{ "LG" <- ConstTBool false })
                 (##perms
                 `{ "EX" <- ConstTBool false }
                 `{ "SR" <- ConstTBool false }
                 `{ "MC" <- ConstTBool false }
                 `{ "LD" <- ConstTBool false }
                 `{ "SL" <- ConstTBool false }
                 `{ "LM" <- ConstTBool false }
                 `{ "SD" <- ConstTBool false }
                 `{ "LG" <- ConstTBool false })))))).
