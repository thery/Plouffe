From mathcomp Require Import ssreflect.
Require Import NPeano ZArith.
From Coquelicot Require Import Coquelicot.
Require Import Reals Field Psatz Plouffe CPlouffe Billion0.


Time Definition val3 := 
Eval native_compute in sumV cprecision cdigit 5.

Unset Printing All.

Print val3.

Set Printing All.

Print val3.

