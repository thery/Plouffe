From mathcomp Require Import ssreflect.
Require Import NPeano ZArith.
From Coquelicot Require Import Coquelicot.
Require Import Reals Field Psatz Plouffe CPlouffe.

Definition cprecision := 28%N.
Definition cdigit := 1000000%N.

(* hack to go around the non unicity of bigN : to fix *)
Definition lift x := 
match x with 
  BigN.BigN.N0 X => BigN.BigN.N1 (DoubleType.WW BigN.BigN.zero0 X) 
| _ => x
end.
