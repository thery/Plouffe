From mathcomp Require Import ssreflect.
Require Import NPeano ZArith.
From Coquelicot Require Import Coquelicot.
Require Import Reals Field Psatz Plouffe CPlouffe Billion0.

(*
Time Eval native_compute in sumV cprecision cdigit 1.
*)

Definition comp1 := lift 65325685244.

Lemma comp1_def : comp1 = sumV cprecision cdigit 1.
Proof.
native_cast_no_check (refl_equal comp1).
Time Qed.
*)
