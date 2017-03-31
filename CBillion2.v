From mathcomp Require Import ssreflect.
Require Import NPeano ZArith.
From Coquelicot Require Import Coquelicot.
Require Import Reals Field Psatz Plouffe CPlouffe Billion0.


Time Definition val2 := 
Eval native_compute in sumV cprecision cdigit 4.

Unset Printing All.

Print val2.

Set Printing All.

Print val1.
