From mathcomp Require Import ssreflect.
Require Import NPeano ZArith.
From Coquelicot Require Import Coquelicot.
Require Import Reals Field Psatz Plouffe CPlouffe Billion0.


Time Definition val4 := 
Eval native_compute in sumV cprecision cdigit 6.

Unset Printing All.

Print val4.

Set Printing All.

Print val4.
