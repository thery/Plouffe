From mathcomp Require Import ssreflect.
Require Import NPeano ZArith.
From Coquelicot Require Import Coquelicot.
Require Import Reals Field Psatz Plouffe CPlouffe.
Require Import Million0 Million1 Million2 Million3 Million4.

From Bignums Require Import BigN.

Section Compute.

Definition cd := BigN.of_N cdigit.
Definition cp := BigN.of_N cprecision.
Definition cpS := BigN.shiftl 1 cp.

Definition cpiDigit :=
  let delta := cd + cp / 4 + 1 in
  if 3 <? cp then
    if (8 * delta <? 2 ^ (cp - 4)) then
      let Y := (4 * comp1 + 
             (9 * cpS - (2 * comp2 + comp3 + comp4 + 4 * delta))) in
      let v1 := (Y + 8 * delta) mod 2 ^ cp / 2 ^ (cp - 4) in
      let v2 := Y mod 2 ^ cp / 2 ^ (cp - 4) in
      if v1 =? v2 then Some v2 else
      None
    else None
  else None.

Time Let ucpiDigit := Eval native_compute in
 match cpiDigit with Some k => k | None => 0 end.

Lemma ucpiDigitE : cpiDigit = Some ucpiDigit.
Proof.
native_cast_no_check (refl_equal cpiDigit).
Qed.

Let vcpiDigit := Eval native_compute in [[ucpiDigit]].

Lemma vcpiDigitE : vcpiDigit = [[ucpiDigit]].
Proof.
native_cast_no_check (refl_equal vcpiDigit).
Qed.

Let dd := Eval compute in cdigit.

Lemma piDigit_1000000 : 
  Rdigit 16 (N.to_nat dd) PI = vcpiDigit.
Proof.
rewrite vcpiDigitE.
apply: (piDigit_correct cprecision cdigit).
rewrite -ucpiDigitE.
rewrite /piDigit /cpiDigit.
rewrite - comp1_def  - comp2_def - comp3_def - comp4_def.
apply refl_equal.
Qed.

End Compute.

Check piDigit_1000000.
