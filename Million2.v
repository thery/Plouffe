From mathcomp Require Import ssreflect.
From Stdlib Require Import PeanoNat ZArith.
From Coquelicot Require Import Coquelicot.
From Stdlib Require Import Reals Field Psatz.
Require Import Plouffe CPlouffe Million0.

(*
Time Eval native_compute in sumV cprecision cdigit 4.
*)

Definition comp2 := 113185819.

Lemma comp2_def : comp2 = sumV cprecision cdigit 4.
Proof.
native_cast_no_check (refl_equal comp2).
Time Qed.

