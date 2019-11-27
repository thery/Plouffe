From mathcomp Require Import ssreflect.
Require Import NPeano ZArith.
From Coquelicot Require Import Coquelicot.
Require Import Reals Field Psatz Plouffe CPlouffe Billion0.

(*
Time Eval native_compute in sumV cprecision cdigit 4.
*)

Definition comp2 := 560355596508377.

Lemma comp2_def : comp2 = sumV cprecision cdigit 4.
Proof.
native_cast_no_check (refl_equal comp2).
Time Qed.
