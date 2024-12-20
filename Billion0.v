From mathcomp Require Import ssreflect.
Require Import PeanoNat ZArith.
From Coquelicot Require Import Coquelicot.
Require Import Reals Field Psatz Plouffe CPlouffe.
From Bignums Require Import BigN.
Require Import Int63.Uint63.

Definition cprecision := 50%N.
Definition cdigit := 1000000000%N.

Definition bzero := 
  (BigN.BigN.N1
    (@DoubleType.WW Cyclic63.Uint63Cyclic.t 0x0%uint63 0x0%uint63)).


