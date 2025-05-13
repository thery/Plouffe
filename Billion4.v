From mathcomp Require Import ssreflect.
From Stdlib Require Import PeanoNat ZArith.
From Coquelicot Require Import Coquelicot.
From mathcomp Require Import all_ssreflect.
From Stdlib Require Import Reals Field Psatz.
Require Import Plouffe CPlouffe Billion0.
From Bignums Require Import BigN.

(*
Time Eval native_compute in sumV cprecision cdigit 6.
*)

Definition comp4 := (289000933264774 + bzero)%bigN.

Lemma comp4_def : comp4 = sumV cprecision cdigit 6.
Proof.
native_cast_no_check (refl_equal comp4).
Time Qed.
