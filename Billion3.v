From mathcomp Require Import ssreflect.
Require Import PeanoNat ZArith.
From Coquelicot Require Import Coquelicot.
Require Import Reals Field Psatz Plouffe CPlouffe Billion0.
From Bignums Require Import BigN.

(*
Time Eval native_compute in sumV cprecision cdigit 5.
*)

Definition comp3 := (159961702696527 + bzero)%bigN.

Lemma comp3_def : comp3 = sumV cprecision cdigit 5.
Proof.
native_cast_no_check (refl_equal comp3).
Time Qed.
