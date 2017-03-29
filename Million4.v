From mathcomp Require Import ssreflect.
Require Import NPeano ZArith.
From Coquelicot Require Import Coquelicot.
Require Import Reals Field Psatz Plouffe CPlouffe Million0.

(*
Time Eval native_compute in sumV cprecision cdigit 6.
*)

Definition comp4 := 89215754417.

Lemma comp4_def : comp4 = sumV cprecision cdigit 6.
Proof.
native_cast_no_check (refl_equal comp4).
Time Qed.

