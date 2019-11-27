From mathcomp Require Import ssreflect.
Require Import NPeano ZArith.
From Coquelicot Require Import Coquelicot.
Require Import Reals Field Psatz Plouffe CPlouffe Million0.

Definition comp1 := 119979218.

Lemma comp1_def : comp1 = sumV cprecision cdigit 1.
Proof.
native_cast_no_check (refl_equal comp1).
Time Qed.

