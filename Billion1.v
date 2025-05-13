From mathcomp Require Import ssreflect.
From Stdlib Require Import PeanoNat ZArith.
From Coquelicot Require Import Coquelicot.
From Stdlib  Require Import Reals Field Psatz.
Require Import Plouffe CPlouffe Billion0.
From Bignums Require Import BigN.
(*
Time Eval native_compute in sumV cprecision cdigit 1.
*)

Definition comp1 := (539243349047133 + bzero)%bigN.

Lemma comp1_def : comp1 = sumV cprecision cdigit 1.
Proof.
native_cast_no_check (refl_equal comp1).
Time Qed.
