From mathcomp Require Import ssreflect.
From Stdlib Require Import PeanoNat ZArith.
From Coquelicot Require Import Coquelicot.
From Stdlib Require Import Reals Field Psatz.
Require Import Plouffe CPlouffe.
From Bignums Require Import BigN.
From Stdlib Require Import Int63.Uint63.

Definition cprecision := 50%N.
Definition cdigit := 1000000000%N.

Definition bzero := 
  (BigN.BigN.N1
    (@DoubleType.WW Cyclic63.Uint63Cyclic.t 0x0%uint63 0x0%uint63)).


