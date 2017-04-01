From mathcomp Require Import ssreflect.
Require Import NPeano ZArith.
From Coquelicot Require Import Coquelicot.
Require Import Reals Field Psatz Plouffe.
Require Export String.

(******************************************************************************)
(*                                                                            *)
(*     COMPUTING HEXADECIMAL DIGITS OF PI WITH THE PLOUFFE FORMULA            *)
(*                                                                            *)
(******************************************************************************)

Ltac tlra := try lra.
Ltac tlia := try lia.

Notation "a %:R " := (INR a) (at level 10).

Open Scope nat_scope.

(******************************************************************************)
(* Some theorems for nat                                                      *)

Lemma le_minus_0 a b : a <= b -> a - b = 0.
Proof.  by elim: a b => //= n IH [|b] //; tlia. Qed.

Lemma Ndiv_minus a b c : 0 < c -> (a - b * c) / c = a / c - b.
Proof.
move=> Pc.
case: (le_lt_dec (b * c) a) => Labc; last first.
  rewrite !le_minus_0; tlia.
    by rewrite Nat.div_0_l; lia.
  by apply: Nat.div_le_upper_bound; lia.
by rewrite -{2}(Nat.sub_add (b * c) a) // Nat.div_add; lia.
Qed.

Lemma mod_minus_mult a b c : 0 < c -> b * c <= a -> (a - b * c) mod c = a mod c.
Proof.
move=> Pp Lbca.
by rewrite -{2}(Nat.sub_add (b * c) a) // Nat.mod_add; lia.
Qed.

Lemma pow_mod a b n :
  (0 < n -> (a ^ b) mod n = (a mod n) ^ b mod n)%nat.
Proof.
move=> Pn; elim: b => //= b IH.
rewrite Nat.mul_mod ?IH; tlia.
by rewrite Nat.mul_mod_idemp_r; lia.
Qed.

Lemma mod_between (a b c1 c2 m n : nat) :
 (0 <= c1 <= c2  -> m < n -> c2 < b ^ m -> 1 < b ->
  ((a + c2) mod (b ^n) / (b ^ m) = a mod (b ^n) / (b ^ m)) ->
  ((a + c1) mod (b ^n) / (b ^ m) = a mod (b ^n) / (b ^ m))).
Proof.
move=> Lc1c2 Lmn Ldbm Pb Eac2ab.
have F0 : b ^ m < b ^ n by apply: Nat.pow_lt_mono_r .
have F1 : 2 * b ^ m <= b ^ n.
  apply: le_trans (_ : b ^ (1 + m) <= b ^ n).
    rewrite Nat.pow_add_r Nat.pow_1_r.
    by apply: mult_le_compat_r; lia.
  by apply: Nat.pow_le_mono_r; lia.
pose x := a mod (b ^ n).
have F2 : x < b ^ n by apply: Nat.mod_upper_bound; lia.
case: (le_lt_dec (b ^ n) (x + c2)) => Lbnxc2.
  have F3 : (a + c2) mod b ^ n = x + c2 - b ^ n.
    rewrite Nat.add_mod -/x; tlia.
    rewrite [c2 mod _]Nat.mod_small; tlia.
    rewrite -(Nat.sub_add (b ^ n) (x + c2)) //.
    rewrite Nat.add_mod ?Nat.mod_same; tlia.
    rewrite plus_0_r Nat.mod_mod; tlia.
    rewrite Nat.mod_small; lia.
  have F4 : a mod b ^ n / b ^ m = 0.
    by rewrite -Eac2ab F3 Nat.div_small //; lia.
  have: b ^ m / b ^ m <= x / b ^ m.
    apply: Nat.div_le_mono; lia.
  by rewrite F4 Nat.div_same; lia.
have ->: (a + c1) mod b ^ n  = x + c1.
  rewrite Nat.add_mod -/x; tlia.
  rewrite [c1 mod _]Nat.mod_small; tlia.
  by rewrite Nat.mod_small; lia.
rewrite -/x; apply: le_antisym.
  rewrite -Eac2ab.
  have ->: (a + c2) mod b ^ n  = x + c2.
    rewrite Nat.add_mod -/x; tlia.
    rewrite [c2 mod _]Nat.mod_small; tlia.
    by rewrite Nat.mod_small; lia.
  by apply: Nat.div_le_mono; lia.
by apply: Nat.div_le_mono; lia.
Qed.

(******************************************************************************)

Open Scope Z_scope.

(* Some theorems from Z *)

Require Import ZArith.

Lemma pow_Zpower a b : 
   Z.of_nat (a ^ b) =  Z.of_nat a ^ Z.of_nat b.
Proof.
rewrite -Zpower_nat_Z.
elim: b => //= n IH.
by rewrite -IH Nat2Z.inj_mul.
Qed.


(******************************************************************************)

Open Scope R_scope.

(* Some theorems from R *)

Lemma Rinv_le_0_compat x : 0 < x -> 0 <= / x.
Proof.
move=> Px.
have->: / x = 1 / x by rewrite /Rdiv Rmult_1_l.
apply: Rdiv_le_0_compat; lra.
Qed.

Lemma sum_f_R0_plus_r (f : nat -> R) m n :
  sum_f_R0 f (S (m +  n)) = 
      sum_f_R0 f m + sum_f_R0 (fun n => f (S m + n)%nat) n. 
Proof.
elim: n m f => [m f | n IH m f]; first by rewrite /= plus_0_r.
rewrite Nat.add_succ_r decomp_sum; tlia.
rewrite [pred _]/= IH -Rplus_assoc -(decomp_sum _ (S m)); tlia.
rewrite [sum_f_R0 _ (S n)]decomp_sum; tlia.
rewrite /= plus_0_r -!Rplus_assoc.
congr (_ + _ + _).
by apply: sum_eq => i _;rewrite Nat.add_succ_r.
Qed.

Lemma approx_divR a b : (0 < b)%nat -> 0 <= a%:R / b%:R - (a / b)%:R < 1.
Proof.
move=> bP.
have bPR : 0 < b%:R by apply: lt_0_INR.
have ->: 1 = (/ b%:R) * b%:R by field; lra.
have ->: a%:R / (b) %:R - (a / b) %:R = (/ b%:R) * (a%:R - (a / b * b)%:R).
  rewrite mult_INR; field; lra.
have ibPR : 0 < /b%:R by apply: Rinv_0_lt_compat.
split.
  apply: Rmult_le_pos; tlra.
  suff: (a / b * b) %:R <= a%:R by lra.
  apply: le_INR.
  rewrite mult_comm {2}(Nat.div_mod a b); lia.
apply: Rmult_lt_compat_l; tlra.
suff: a%:R < (a / b * b + b) %:R by rewrite plus_INR; lra.
apply: lt_INR.
rewrite {1}(Nat.div_mod a b); tlia.
rewrite mult_comm.
suff :  (a mod b < b)%nat by lia.
apply: Nat.mod_upper_bound; lia.
Qed.

Lemma pow_INR a n : (a ^ n)%:R = a%:R ^ n.
Proof. by elim: n => //= n; rewrite mult_INR => ->. Qed.

Lemma Int_part_IZR z : Int_part (IZR z) = z.
Proof.
suff : (z + 1 = up (IZR z))%Z by rewrite /Int_part; lia.
by apply: tech_up; rewrite plus_IZR /=; lra.
Qed.

Lemma frac_part_IZR z : frac_part (IZR z) = 0.
Proof. by rewrite /frac_part Int_part_IZR; lra. Qed.

Lemma le_Int_part a b : a <= b -> (Int_part a <= Int_part b)%Z.
Proof.
move=> aLb.
have Fa := base_Int_part a.
have Fb := base_Int_part b.
have : IZR(Int_part a) < IZR(Int_part b) + 1; tlra.
by rewrite -(plus_IZR _ 1) => /lt_IZR; lia.
Qed.

Lemma le_Int_part_pos a : 0 <= a -> (0 <= Int_part a)%Z.
Proof.
move=> aLb; rewrite -(Int_part_IZR 0).
by apply: le_Int_part.
Qed.

Lemma Int_part_INR b c : (0 < c)%nat ->
  (Int_part (b * c%:R) / (Z.of_nat c) = Int_part b)%Z.
Proof.
move=> Pc.
have ZPc : (0 < Z.of_nat c)%Z by apply: (inj_lt 0).
rewrite {1}[b](_ : b = IZR (Int_part b) + frac_part b); last first.
  by rewrite /frac_part; lra.
rewrite Rmult_plus_distr_r {1}INR_IZR_INZ -mult_IZR  plus_Int_part2; last first.
  by rewrite frac_part_IZR; have := base_fp (frac_part b * c %:R); lra.
rewrite Int_part_IZR Z.div_add_l; tlia.
rewrite Z.div_small; tlia; split.
  change 0%Z with (Z.of_nat 0).
  rewrite -Int_part_INR; apply: le_Int_part.
  apply: Rmult_le_pos; first by have := base_fp b; lra.
  by apply: (le_INR 0); lia.
apply: lt_IZR; rewrite -INR_IZR_INZ.
have [Fa _] := base_Int_part (frac_part b * c %:R).
apply: Rle_lt_trans Fa _.
rewrite -{2}[_%:R]Rmult_1_l.
apply: Rmult_lt_compat_r; first by apply: (lt_INR 0).
by have [] := base_fp b.
Qed.


Definition Rdigit (b : nat) (d : nat) (r : R) :=
   (Z.to_nat (Int_part ((Rabs r) * (b%:R ^ d))) mod b)%nat.

Lemma RdigitS b d r : Rdigit b d (r * b%:R) = Rdigit b (S d) r.
Proof.
rewrite /Rdigit Rabs_mult (Rabs_pos_eq _ (pos_INR _)) /=.
by rewrite Rmult_assoc.
Qed.

Lemma Rdigit_shift b d r n :
  Rdigit b d (r * (b%:R ^ n)) = Rdigit b (n + d) r.
Proof.
elim: n r => [r | n IH r] /=; first by rewrite Rmult_1_r.
by rewrite -Rmult_assoc IH RdigitS.
Qed.

Lemma Rdigit_mod_div b r k n : (0 < b)%nat ->
   Rdigit (b ^ n) 1 r  = 
   ((Z.to_nat (Int_part ((Rabs r) * b%:R ^ (k + n)))) 
         mod (b ^ (k + n)) / (b ^ k))%nat.
Proof.
move=> Pb.
have F0 m : (0 < b ^ m)%nat.
  suff : (1 ^ m <= b ^ m)%nat by rewrite Nat.pow_1_l; lia.
  apply: Nat.pow_le_mono_l; lia.
have F1 m : (0 <= Int_part (Rabs r * b %:R ^ m))%Z.
  apply: le_Int_part_pos.
  by repeat (apply: Rmult_le_pos || apply: Rabs_pos || apply: pow_le
             || apply: pos_INR).
have F2 := inj_lt  _ _ (F0 (k + n)%nat).
rewrite -[(_ mod _)%nat]Nat2Z.id Zdiv.mod_Zmod; last first.
  have := F0 (k + n)%nat; lia.
rewrite Z2Nat.id //.
rewrite Zdiv.Zmod_eq; tlia.
rewrite Z2Nat.inj_sub; last first.
  apply: Zmult_gt_0_le_0_compat; tlia.
  by apply: Z_div_pos; tlia.
rewrite Z2Nat.inj_mul; tlia; last first.
  by apply: Z_div_pos; tlia.
rewrite Nat2Z.id -pow_INR Int_part_INR; tlia.
rewrite (_ : (b ^ (k + n) = b ^ n * b ^ k)%nat) //; last first.
  by rewrite Nat.pow_add_r mult_comm.
rewrite Nat.mul_assoc Ndiv_minus //.
rewrite mult_INR -Rmult_assoc.
rewrite -(Int_part_INR (Rabs r) (b ^ n)) //.
rewrite -[X in (_ = X - _)%nat]Nat2Z.id.
rewrite Zdiv.div_Zdiv; last by have := F0 k; lia.
rewrite Z2Nat.id; last first.
  by rewrite Rmult_assoc -mult_INR mult_comm -Nat.pow_add_r pow_INR.
rewrite Int_part_INR //.
rewrite -{2}[Int_part _]Z2Nat.id //; last by rewrite pow_INR.
rewrite -Zdiv.div_Zdiv ?Nat2Z.id; last by have := F0 n; lia.
rewrite mult_comm -Nat.mod_eq //; last by have := F0 n; lia.
by rewrite /Rdigit /= Rmult_1_r.
Qed.

Lemma Rdigit_mod_div16 r d p : (3 < p)%nat ->
   Rdigit 16 d r  = 
   ((Z.to_nat (Int_part ((Rabs r) * 16 ^ d / 16 * 2 ^ p )))
        mod (2 ^ p) / (2 ^ p / 16))%nat.
Proof.
move=> Pp.
have ->: (p = (p - 4) + 4)%nat by lia.
have ->: (2 ^ (p - 4 + 4) / 16 = 2 ^ (p - 4))%nat.
  by rewrite Nat.pow_add_r Nat.div_mul.
have F : Rabs r * 16 ^ d / 16 = Rabs (r * 16 ^ d / 16).
  rewrite !Rabs_mult [Rabs (16 ^ _)]Rabs_pos_eq; last first.
    by apply: pow_le; lra.
  by rewrite [Rabs (/_)]Rabs_pos_eq; lra.
rewrite F -Rdigit_mod_div; tlia.
rewrite -RdigitS.
have ->: (2 ^ 4) %:R = 16 by rewrite /=; lra.
have ->: r * 16 ^ d / 16 * 16 = r * 16%:R ^ d.
  have ->: 16 %:R = 16 by rewrite /=; lra.
  by field.
by rewrite Rdigit_shift plus_0_r.
Qed.

(******************************************************************************)
(*                                                                            *)
(*                              COMPUTATION in NAT                            *)
(*                                                                            *)
(******************************************************************************)

Open Scope nat_scope.

Section NComputePi.

(* Precision *)
Variable p : nat.
Let pS := 2 ^ p.

Let PpS : 0 < 2 ^ p.
Proof.
suff : 2 ^ 0 <= 2 ^ p by rewrite /=; lia.
by apply: Nat.pow_le_mono_r; lia.
Qed.

(* Digit position *)
Variable d : nat.

Section power.

Variable m : nat.

(* a ^ b mod m *)
Definition NpowerMod a b m := (a ^ b) mod m.
Lemma NpowerModE a b : 0 < m -> 
 exists u, a ^ b = u * m + NpowerMod a b m.
Proof.
by exists (a ^ b / m); rewrite Mult.mult_comm; apply: Nat.div_mod; lia.
Qed.

End power.

Let f k i := (((16 ^ d / 16) * 2 ^ p) / (16 ^ i * (8 * i + k)%:R))%R.
Let g k i := (/ (16 ^ i * (8 * i + k)%:R))%R.

Lemma fgE k : (Series (f k) = (16 ^ d / 16) * 2 ^ p * Series (g k))%R.
Proof. by exact: Series_scal_l. Qed.

Lemma PigE : ((16 ^ d / 16) * 2 ^ p * PI = 
               4 * (Series (f 1)) - 2 * (Series (f 4)) 
                       - (Series (f 5)) - (Series (f 6)))%R.
Proof. by rewrite Plouffe_PI /Sk /a !fgE /g; lra. Qed.

(* Iterative state : counter kN = k and result *) 
Inductive NstateF := NStateF (i : nat) (res : nat).

(* Un pas : i = i + 1
            res = ress + (16^(d - 1 - k)) * 2^p / (8 * k + j) *)
Definition NiterF (k : nat) (st : NstateF) :=
  let (i, res) := st in
  let r := 8 * i + k in
  let res := res + (pS * (NpowerMod 16 (d - 1 - i) r)) / r in
  let res := if res <? pS then res else res - pS in
  NStateF (S i) res.

Lemma NiterF_mod k i res : 0 < k ->
  let (_, res1) := NiterF k (NStateF i res) in res < pS -> res1 < pS.
Proof.
rewrite /NiterF => Pj sLpS.
set x := _ / _.
have : x < pS.
  apply: Nat.div_lt_upper_bound; tlia.
  rewrite mult_comm.
  apply: mult_lt_compat_r; tlia .
  by apply: Nat.mod_upper_bound; tlia.
case E : (_ <? _); tlia.
by move: E; rewrite Nat.ltb_lt; lia.
Qed.

Lemma base_sum_approxL k i (v := 8 * i + k) (po := NpowerMod 16 (d - 1 - i) v) :
 0 < k -> i < d -> 
   exists u, (0 <= f k i - (pS * po / v)%:R - u%:R * 2 ^ p < 1)%R.
Proof.
move=> Pj iLd.
have Pv : 0 < v by rewrite /v; lia.
have [u1 Hu1] := NpowerModE _ 16 (d - 1 - i) Pv.
have F1 := approx_divR (pS * po) v Pv.
have F2 : (0 < v%:R)%R by apply: (lt_INR 0).
have F3 : (0 < 16 ^ i)%R by apply: pow_lt; lra.
have ->: f k i = ((2 ^ p * 16 ^ (d - 1 - i))%:R / v%:R)%R.
  rewrite /f -/v mult_INR !pow_INR.
  have->: (2%:R = 2)%R by rewrite /=; lra.
  have->: (16%:R = 16)%R by rewrite /=; lra.
  have {1}->: d = (d - 1 - i) + i + 1 by lia.
  rewrite !pow_add; field; lra.
exists u1.
rewrite Hu1 mult_plus_distr_l plus_INR.
rewrite ![(2 ^ p * _)%:R]mult_INR [(u1 * _)%:R]mult_INR.
rewrite [(_ / _)%R]Rmult_plus_distr_r.
rewrite !Rmult_assoc Rinv_r ?Rmult_1_r; tlra.
rewrite pow_INR.
have->: (2%:R = 2)%R by rewrite /=; lra.
have ->: forall a b c d,  a = c -> (a + b - d - c = b - d)%R; last by lra.
  by move=> a1 b1 c1 d1 ->; ring.
have ->: (2 ^ p = pS %:R)%R.
  by rewrite /pS; rewrite pow_INR /=; lra.
by rewrite -Rmult_assoc -mult_INR -/po; lra.
Qed.

Notation nat_iter n A f x := (nat_rect (fun _ => A) x (fun _ => f) n).

(* Compute \sum_{i = 0 to d - 1} (16^(d - 1 - i)) * 2^p / (8 * i + k) *)
Definition NiterL k :=
   nat_iter d _ (NiterF k) (NStateF 0 0).

Lemma NiterL_mod j : 0 < j ->
  let (_, s1) := NiterL j in s1 < pS.
Proof.
rewrite /NiterL => Pj.
have F : 0 < pS.
  suff: 1 <= pS by lia.
  by apply: (Nat.pow_le_mono_r 2 0 p); lia.
elim: d => //= n.
case: (nat_iter _ _  _ _) => k s sLp.
by apply: NiterF_mod.
Qed.

Lemma sumLE k : 0 < k -> 0 < d ->
  let (_, res) := NiterL k in 
  exists u, 
  (0 <= sum_f_R0 (f k) (d - 1) - res%:R - u%:R * 2 ^ p < d%:R)%R.
Proof.
move=> Pk; rewrite /NiterL.
have F n m s :
     exists s1, nat_iter n _ (NiterF k) (NStateF m s) = (NStateF (m + n) s1).
  elim: n  => //= [|n [s1->]]; first by exists s; congr NStateF; lia.
  by rewrite Nat.add_succ_r; eexists; refine (refl_equal _).
rewrite /NiterL.
elim: {-2}d (Nat.le_refl d) => // [dP dV| [|n] IH nLd _].
- by contradict dV; lia.
- rewrite /=.
  suff ->: pS * NpowerMod 16 (d - 1 - 0) k / k <? pS = true.
    rewrite {-1 4}(_ : k = 8 * 0 + k); tlia.
    by apply:  base_sum_approxL; lia.
  rewrite Nat.ltb_lt; apply: Nat.div_lt_upper_bound; tlia.
  rewrite mult_comm; apply: mult_lt_compat_r.
    by apply: Nat.mod_upper_bound; lia.
  suff : 1 ^ 0 <= pS by rewrite Nat.pow_0_r; lia.
  by apply: Nat.pow_le_mono; lia.
have F1 : S n <= d by lia.
have F2 : 0 < S n by lia.
rewrite (nat_rect_plus 1 (S n)).
have {IH} := IH F1 F2.
have {F}[s->]:= F (S n) 0 0 => [[u]].
rewrite nat_rect_succ_r /nat_rect.
change (0 + S n) with (S n).
replace  (S n - 1) with n by lia.
replace  (S (S n - 1)) with (S n) by lia.
replace  (S (S n) - 1) with (S n) by lia.
rewrite /NiterF.
set sum := sum_f_R0 _ _.
set v := 8 * S n + k.
set po := NpowerMod _ _ _.
have [u1 Hu1] := base_sum_approxL k (S n) Pk nLd.
rewrite -/po -/v in Hu1 => Hu.
have F3 :
   (0 <=
          sum + f k (S n) - (s + pS * po / v) %:R - 
                      (u %:R * 2 ^ p + u1 %:R * 2 ^ p) < (S (S n)) %:R)%R.
  have ->: forall a b c d e f, (((a + b - (c + d)%:R) - (e + f)) = 
                             (a - c%:R - e + (b - f - d%:R)))%R.
    by move=> *; rewrite plus_INR; ring.
  by rewrite S_INR; lra.
case E : (_ <? _).
  exists (u + u1).
  rewrite [(u + _)%:R]plus_INR Rmult_plus_distr_r sum_N_predN; tlia.
  by rewrite [pred _]/= -/sum.
exists (u + S u1).
rewrite minus_INR; last first.
  by rewrite -Nat.nlt_ge -Nat.ltb_lt E.
rewrite [(u + _)%:R]plus_INR Rmult_plus_distr_r; tlia.
rewrite sum_N_predN -/sum; tlia.
rewrite S_INR Rmult_plus_distr_r Rmult_1_l.
have ->: (pS%:R = 2 ^ p)%R by rewrite pow_INR /=.
by lra.
Qed.

(* Iterative state : counter kN = index shift and result *) 
Inductive NstateG := NStateG (i : nat) (s : nat) (res : nat).

(* Un pas : i = i + 1, s = s / 16,
            res = res + (d / (8 * i + k)) *)
Definition NiterG (k : nat) (st : NstateG) :=
  let (i, s, res) := st in
  let r := 8 * i + k in
  let res := res + (s / r) in
  NStateG (S i) (s / 16) res.

(* Compute \sum_{i = d to infinity} (16^(d - 1 - i)) / (8 * i + j) *)
Definition NiterR k :=
  nat_iter (p / 4) _ (NiterG k) (NStateG d (pS / 16) 0).

Lemma sumRE k : 0 < k -> 0 < p / 4 ->
  let (_,_, s1) := NiterR k in 
  (0 <= sum_f_R0 (fun i => (f k (d + i))) (p / 4 - 1) - s1%:R < (p / 4)%:R)%R.
Proof.
move=> Pk.
have F n m i s :
     exists s1, nat_iter n _ (NiterG k) (NStateG m (pS / (16 ^ i)) s)
                              = (NStateG (m + n)(pS / (16 ^ (i + n))) s1).
  elim: n  => //= [|n [s1->]].
    by exists s; congr NStateG; rewrite ?plus_0_r; tlia.
  rewrite !Nat.add_succ_r.
  rewrite Nat.pow_succ_r; tlia.
  have F : 16 ^ 0 <= 16 ^(i + n) by apply: Nat.pow_le_mono_r; lia.
  rewrite Nat.pow_0_r in F; tlia. 
  rewrite mult_comm -Nat.div_div; tlia.
  by eexists; refine (refl_equal _).
have G j : 
    (0 <= f k (d + j) - (pS / 16 ^ (1 + j) / (8 * (d + j) + k)) %:R < 1 %:R)%R.
  have F2 j1 : 0 < 16 ^ j1.
    have : 16 ^ 0 <= 16 ^ j1 by apply: Nat.pow_le_mono_r; lia.
    by rewrite Nat.pow_0_r; lia.
  have F3 j1 : (0 < 16 ^ j1)%R.
    have<-: (16%:R = 16)%R by rewrite /=; lra.
    rewrite -(pow_INR 16).
    by apply: (lt_INR 0).
  have F4 : 0 < (16 ^ (1 + j) * (8 * (d + j) + k)).
    by apply: Nat.mul_pos_pos; try apply: F2; tlia.
  rewrite /f Nat.div_div; tlia; last by have := F2 (1 + j); lia.
  have := approx_divR pS _ F4.
  rewrite /pS mult_INR !pow_INR.
  have->: (2%:R = 2)%R by rewrite /=; lra.
  have->: (16%:R = 16)%R by rewrite /=; lra.
  set u := (_ / _)%R.
  set v := (_ / _)%R.
  replace u with v; first by [].
  rewrite /v /u !pow_add pow_1; field; tlra.
  have : (0 < (8 * (d + j) + k) %:R)%R.
    apply: (lt_INR 0); lia.
  by have := F3 j; have := F3 d; lra. 
rewrite /NiterR.
elim: (p/4) => [H|[|n] IH _].
- contradict H; lia.
- rewrite nat_rect_succ_r /nat_rec /NiterG.
  change (1 - 1) with 0.
  rewrite /sum_f_R0 plus_0_l.
  change 16 with (16 ^(1 + 0)).
  by rewrite (_ : 8 * d = 8 * (d + 0)); tlia.
rewrite (nat_rect_plus 1 (S n)).
have F1 : 0 < S n by lia.
have {IH} := IH F1.
have := F (S n) d 1 0.
rewrite Nat.pow_1_r => [[s ->]]. 
rewrite nat_rect_succ_r /nat_rect.
replace  (S n - 1) with n by lia.
replace  (S (S n) - 1) with (S n) by lia.
rewrite /NiterG.
set sum := sum_f_R0 _ _.
set v := 8 * (d + S n) + k.
rewrite /sum_f_R0 -/sum_f_R0 -/sum.
have := G (S n).
rewrite -/v.
rewrite [((S (S _))%:R)%R]S_INR plus_INR.
change (1%:R)%R with 1%R.
lra.
Qed.

Lemma NiterR_mod k : 0 < k ->
  let (_, _, res) := NiterR k in 15 * res < pS.
Proof.
move=> Pk.
case: (lt_dec 0 (p / 4))=> Pp; last first.
  rewrite /NiterR /nat_rect; replace (p / 4) with 0; tlia. 
  by rewrite mult_0_r.
have F0 : (0 < 16 ^ d)%R by apply: pow_lt; lra. 
have F1 j N :
       j <> 1%R ->
       sum_f_R0 (fun i : nat => (j ^ i)%R) N = ((1 - j ^ S N) / (1 - j))%R.
  by move=> kD; elim: N => /= [|n ->]; field; lra. 
have F2 N : (sum_f_R0 (fun i => (f k (d + i))) N <= 
    (16 ^ d / 16 * 2 ^ p) * (1/16)^d *
         (sum_f_R0 (fun i : nat => ((1/16)^ i)%R) N))%R.
  have F j : (f k (d + j) <= 16 ^ d / 16 * 2 ^ p * (1 / 16) ^ (d + j))%R.
    have FF1 : (0 < 16 ^ (d + j))%R by apply: pow_lt; lra.  
    have FF2 : (1 <= (8 * (d + j) + k)%:R)%R by apply: (le_INR 1); lia.
    rewrite /f  [((_ / _)^ _)%R]Rpow_mult_distr -Rinv_pow; tlra.
    rewrite -{2}[(16 ^ (d + j))%R]Rmult_1_r.
    rewrite pow1 Rmult_1_l /Rdiv !Rmult_assoc.
    rewrite ![(/(_ ^ _ * _))%R]Rinv_mult_distr; tlra.
    repeat apply: Rmult_le_compat_l; try by apply: pow_le; lra.
    - by apply: Rinv_le_0_compat; lra.
    - by apply: Rinv_le_0_compat; lra.
    by apply: Rle_Rinv; lra.
  elim: N => /= [|n IH]; first by  have := F 0; rewrite plus_0_r; lra.
  by have := F (S n); rewrite Nat.add_succ_r /= pow_add; lra.
have F3 N : (sum_f_R0 (fun i => (f k (d + i))) N < 2 ^ p / 15)%R.
  apply: Rle_lt_trans (F2 _) _.
  rewrite F1; tlra.
  have-> : (16 ^ d / 16 * 2 ^ p * (1 / 16) ^ d = 2 ^ p / 16)%R.
    rewrite [((_ / _)^ _)%R]Rpow_mult_distr -Rinv_pow; tlra.
    by rewrite pow1; field; lra.
  rewrite !Rmult_assoc; apply: Rmult_lt_compat_l; tlra.
    by apply: pow_lt; lra. 
  have ->: (/15 = /16 * (1 / (1 - 1/16)))%R by lra.
  apply: Rmult_lt_compat_l; tlra.
  apply: Rmult_lt_compat_r; tlra.
  suff : (0 < (1/16) ^S N )%R by lra.
  apply: pow_lt; lra.
have :=  sumRE _ Pk Pp; case: NiterR => _ _ s Hs.
apply: INR_lt.
rewrite pow_INR mult_INR.
have->: (15 %:R = 15)%R by rewrite /=; lra.
have->: (2 %:R = 2)%R by rewrite /=; lra.
by have := F3 (p / 4 - 1); lra.
Qed.

Lemma ex_series_f k : 0 < k -> @ex_series R_AbsRing R_NormedModule (f k).
Proof.
move=> Pj; rewrite /f.
assert (F : ex_series (fun i => (16 ^ d / 16 * 2 ^ p) * (1 / 16) ^ i)%R).
  apply: ex_series_scal_l.
  apply: ex_series_geom.
  by split_Rabs; lra.
apply: ex_series_le F => n.
have F1 : (0 < 16 ^ n)%R by apply: pow_lt; lra.
have F2 : (0 < (8 * n + k) %:R)%R   by apply: (lt_INR 0); lia.
have H1: (0 <= 16 ^ d / 16 * 2 ^ p)%R.
  repeat (apply: Rcomplements.Rdiv_le_0_compat || apply: Rmult_le_pos);
    (try by apply: pow_le; lra); lra.
apply:(Rle_trans _ (16 ^ d / 16 * 2 ^ p / (16 ^ n * (8 * n + k) %:R))); last first.
  apply: Rmult_le_compat_l.
    by apply H1.
rewrite Rinv_mult_distr; tlra.
have ->: ((1 / 16) ^ n = / (16 ^ n) * 1)%R.
  rewrite /Rdiv Rmult_1_l Rinv_pow; lra.
apply: Rmult_le_compat_l.
  by apply: Rinv_le_0_compat.
have ->: (1 = 1 / 1)%R by field.
rewrite /Rdiv Rmult_1_l.
apply: Rle_Rinv; tlra.
by apply: (le_INR 1); lia.
set gg := (16 ^ d / 16 * 2 ^ p / (16 ^ n * (8 * n + k) %:R))%R.
  rewrite  /Hierarchy.norm /= /abs /= Rabs_right.
    by apply: Req_le. 
apply: Rle_ge; apply: Rdiv_le_0_compat=>//.
by apply:Rmult_lt_0_compat.
Qed.

Lemma series_bound k : 0 < k -> 
  (0 <= Series (fun i : nat => f k (d + (p / 4 + i))) < 1)%R.
Proof.
move => Pj; split.
  suff <-: Series (fun i => (0 * 0)%R) = 0%R.
    apply: Series_le => [n|]; last first.
      apply: (ex_series_ext (fun i : nat => f k ((d + p / 4) + i))).
        by move=> n; rewrite Plus.plus_assoc.
      by rewrite -ex_series_incr_n; apply: ex_series_f.
    split; tlra.
    rewrite Rmult_0_l.
    repeat (apply: Rcomplements.Rdiv_le_0_compat || apply: Rmult_le_pos);
    (try by apply: pow_le; lra); tlra.
    apply: Rmult_lt_0_compat; first by apply: pow_lt; lra.
    by apply: (lt_INR 0); lia.
  by rewrite Series_scal_l; lra.
pose f1 k := ((16 ^ d / 16 * 2 ^ p) / (16 ^ (d + (p / 4))) * (/16) ^ k)%R.
rewrite /f.
apply: Rle_lt_trans (Series_le _ f1 _ _) _.
- move=> n; rewrite /f1; split.
    repeat (apply: Rcomplements.Rdiv_le_0_compat || apply: Rmult_le_pos);
    (try by apply: pow_le; lra); tlra.
    apply: Rmult_lt_0_compat; first by apply: pow_lt; lra.
    by apply: (lt_INR 0); lia.
  set x := (16 ^ d / 16 * 2 ^ p)%R.
  set y := (_ * _)%R.
  rewrite -Rinv_pow; tlra.
  rewrite Rmult_assoc.
  apply: Rmult_le_compat_l.
    by repeat (apply: Rcomplements.Rdiv_le_0_compat || apply: Rmult_le_pos);
      (try by apply: pow_le; lra); lra.
  rewrite -Rinv_mult_distr.
  - rewrite -Rdef_pow_add.
    apply: Rle_Rinv; first by apply: pow_lt; lra.
      apply: Rmult_lt_0_compat; first by apply: pow_lt; lra.
      by apply: (lt_INR 0); lia.
    rewrite -Plus.plus_assoc -[X in (X <= _)%R]Rmult_1_r.
    apply: Rmult_le_compat_l; first by apply: pow_le; lra.
    by apply: (le_INR 1); lia.
  - suff: (0 < 16 ^ (d + p / 4))%R by lra.
    by apply: pow_lt; lra.
  suff: (0 < 16 ^ n)%R by lra.
  by apply: pow_lt; lra.
- apply: ex_series_scal_l.
  apply: ex_series_geom.
  by split_Rabs; lra.
rewrite Series_scal_l.
rewrite Series_geom; last by split_Rabs; lra.
set x := (_ * _)%R.
have ->: x = ((16 ^ d * 2 ^ p * 16) / (15 * 16 ^ (d + p / 4 + 1)))%R.
  rewrite /x !Rdef_pow_add pow_1.
  field.
  have : (0 < 16 ^ (p / 4))%R by apply: pow_lt; lra.
  have : (0 < 16 ^ d)%R by apply: pow_lt; lra.
  by lra.
rewrite Rcomplements.Rlt_div_l; last first.
  apply: Rmult_lt_0_compat; tlra.
  by apply: pow_lt; lra.
have ->: (1 * (15 * 16 ^ (d + p / 4 + 1)) = 
             16  ^ d * (2 ^ (4 * (p / 4 + 1)) * 15))%R.
  rewrite pow_mult (_ : (2 ^ 4 = 16)%R); last by ring.
  by rewrite !pow_add; ring.
rewrite !Rmult_assoc.
apply: Rmult_lt_compat_l.
  by apply: pow_lt; lra.
apply: Rlt_le_trans (_ : (2 ^ (p + 1) *  15 <= _)%R).
  rewrite pow_add Rmult_assoc.
  apply: Rmult_lt_compat_l; last by lra.
  by apply: pow_lt; lra.
apply: Rmult_le_compat_r; tlra.
apply: Rle_pow; tlra.
rewrite {1}(NPeano.Nat.div_mod p 4); tlia.
have := NPeano.Nat.mod_bound_pos p 4.
by lia.
Qed.

Lemma bound k : 0 < k ->  
  exists u, 
  let (_, res1) := NiterL k in
  let (_, _, res2) := NiterR k in
  (0 <= Series (f k) - res1%:R - res2%:R - u %:R * 2 ^ p  < (d + p / 4 + 1)%:R)%R.
Proof.
move=> Pk.
have F := ex_series_f _ Pk.
case: (lt_dec 0 d) => Pd.
  rewrite (Series_incr_n _ d) //.
  replace (pred d) with (d - 1); tlia.
  have := sumLE _ Pk Pd.
  case: NiterL => _ s1 [u Hs1]; exists u.
  case: (lt_dec 0 (p / 4)) => Pp.
    rewrite (Series_incr_n _ (p/4)) //; last first.
      by rewrite -ex_series_incr_n.
    replace (pred (p / 4)) with (p / 4 - 1); tlia.
    have := sumRE _ Pk Pp.
    case: NiterR => _ _ s2.
    move: Hs1.
    have := series_bound _ Pk.
    rewrite !plus_INR.
    change (1%:R)%R with 1%R.
    by lra.
  have := series_bound _ Pk.
  rewrite /NiterR; replace (p / 4) with 0 by lia.
  rewrite /nat_rect /=.
  rewrite !plus_INR.
  change (1%:R)%R with 1%R.
  change (0%:R)%R with 0%R.
  by lra.
exists 0.
case: (lt_dec 0 (p / 4)) => Pp.
  rewrite (Series_incr_n _ (p/4)) //.
  replace (pred (p / 4)) with (p / 4 - 1); tlia.
  have := sumRE _ Pk Pp.
  rewrite /NiterL.
  have := series_bound _ Pk.
  replace d with 0 by lia.
  rewrite /nat_rect /=.
  case: NiterR => _ _ s2.
  rewrite !plus_INR.
  change (1%:R)%R with 1%R.
  change (0%:R)%R with 0%R.
  set xxx := Series _.
  set yyy := sum_f_R0 _ _.
  by lra.
have := series_bound _ Pk.
rewrite /NiterL /NiterR.
replace d with 0 by lia.
replace (p / 4) with 0 by lia.
rewrite /nat_rect /=.
set xxx := Series _.
lra.
Qed.

(* Compute \sum_{i = 0 to infinity} (16^(d - 1 - i)) / (8 * i + j) *)
Definition NsumV k :=
  let: NStateF _ res1 := NiterL k in
  let: NStateG _ _ res2 := NiterR k in res1 + res2.

Lemma NsumV_mod k :  0 < k -> NsumV k < 2 * pS.
Proof.
move=> Pk.
rewrite /NsumV.
have := NiterL_mod _ Pk.
have := NiterR_mod _ Pk.
case: NiterL; case: NiterR => _ _ t _ s; lia.
Qed.
  
Lemma bound_NsumV k : 0 < k ->  
  exists u, 
  (0 <= Series (f k) - (NsumV k)%:R - u %:R * 2 ^ p  < (d + p / 4 + 1)%:R)%R.
Proof.
move=> Pj.
have [u] := bound _ Pj.
rewrite /NsumV; case: NiterL; case: NiterR => _ _ t _ s Hu.
exists u; move : Hu.
rewrite !plus_INR; lra.
Qed.

Lemma main_thm (delta := d + p / 4 + 1)
          (X :=  (4 * Series (f 1) - 2 * Series (f 4) 
                       - Series (f 5) - Series (f 6))%R)
          (Y := (4 * (NsumV 1) + 
             (9 * pS - (2 * NsumV 4 + NsumV 5 + NsumV 6 + 4 * delta)))%nat)
   : 3 < p -> 8 * delta < 2 ^ (p - 4) -> 
      (Y + 8 * delta) mod 2 ^ p / 2 ^ (p - 4) = Y mod 2 ^ p / 2 ^ (p - 4)
  -> Rdigit 16 d PI = Y mod 2 ^ p / 2 ^ (p - 4).
Proof.
move=> Pp Hdelta HmodEq.
have PX : (0 <= X)%R.
  rewrite /X -PigE.
  have PIp:= PI2_1.
  by repeat ((apply: Rmult_le_pos || apply: Rabs_pos || apply: pow_le
             || apply: pos_INR); tlra).
have FE : (4%:R = 4)%R by rewrite /=; lra.
have TE : (2%:R = 2)%R by rewrite /=; lra.
have NE : (9%:R = 9)%R by rewrite /=; lra.
have PSE : (pS%:R = 2 ^ p)%R.
  by rewrite pow_INR TE /=; lra.
pose NNE := (FE, TE, NE, PSE).
have F1 : (0 < 1)%nat by lia.
have pS1 := NsumV_mod _ F1.
have {F1}[u1 Hu1] := bound_NsumV _ F1.
have F4 : (0 < 4)%nat by lia.
have pS4 := NsumV_mod _ F4.
have {F4}[u4 Hu4] := bound_NsumV _ F4.
have F5 : (0 < 5)%nat by lia.
have pS5 := NsumV_mod _ F5.
have {F5}[u5 Hu5] := bound_NsumV _ F5.
have F6 : (0 < 6)%nat by lia.
have pS6 := NsumV_mod _ F6.
have {F6}[u6 Hu6] := bound_NsumV _ F6.
rewrite -/delta in Hu1 Hu4 Hu5 Hu6.
have Pd : 4 * delta < pS.
  rewrite /pS.
  have ->: p = 4 + (p - 4) by lia.
  by rewrite /=; lia.
have {u1 Hu1}[v1 Hv1] : exists u,
   (0 <= 4 * Series (f 1) - 4 * (NsumV 1) %:R 
           - u %:R * 2 ^ p < 4 * delta %:R)%R.
  exists (4 * u1); rewrite mult_INR.
  have ->: (4%:R = 4)%R by rewrite /=; lra.
  by lra.
have {u4 u5 u6 Hu4 Hu5 Hu6}[v2 Hv2] : exists u,
   (0 <= 2 * Series (f 4) + Series (f 5) + Series (f 6)  - 
        (2 * NsumV 4 + NsumV 5 +  NsumV 6) %:R 
         - u %:R * 2 ^ p < 4 * delta %:R)%R.
  exists (2 * u4 + u5 + u6); rewrite 4!plus_INR !mult_INR.
  have ->: (2%:R = 2)%R by rewrite /=; lra.
  by lra.
have  YE: Y%:R =  (4 * (NsumV 1)%:R + 
             (9 * 2 ^ p - (2 * NsumV 4 + NsumV 5 + NsumV 6)%:R 
                        - 4 * delta%:R))%R.
  rewrite /Y /delta !(mult_INR, plus_INR).
  rewrite minus_INR; last by rewrite -/delta; lia.
  by rewrite !(mult_INR, plus_INR) !NNE; lra.
have P1 :
  (Y%:R + v1%:R * 2 ^ p < X + v2%:R * 2 ^ p + 9 * 2 ^ p <
   Y%:R + v1%:R * 2 ^ p + 8 * delta %:R)%R.
  by rewrite YE /X; lra.
set xx := (X + v2 %:R * 2 ^ p + 9 * 2 ^ p)%R.
set yy := (Y %:R + v1 %:R * 2 ^ p)%R.
set zz := (xx - yy)%R.
have Fc1 : (0 < zz < 8 * delta %:R)%R.
  by rewrite /zz /xx /yy; lra.
have GG : (0 <= xx - (v1 %:R * 2 ^ p))%R.
  rewrite /zz /yy in Fc1.
  suff: (0 <= Y%:R)%R by lra.
  by apply: pos_INR.
pose c1 := Z.to_nat (Int_part zz).
have F2 : 0 <= c1 <= 8 * delta.
  have F2 : (0 <= zz)%R by lra.
  have F3 : (0 <= Int_part zz)%Z.
    rewrite -[0%Z](R_Ifp.Int_part_INR 0).
    by apply: le_Int_part.
  have := F3.
  rewrite Z2Nat.inj_le ?Nat2Z.id -/c1 ; tlia.
  have F4 : (zz <= (8 * delta)%:R)%R.
    rewrite mult_INR; have ->: (8%:R = 8)%R by rewrite /=; lra.
    by lra.
  have := le_Int_part _ _ F4.
  rewrite R_Ifp.Int_part_INR.
  by rewrite Z2Nat.inj_le ?Nat2Z.id -/c1 ; lia.
have F3 : p - 4 < p by lia.
have F5 : 1 < 2 by lia.
have := mod_between Y 2 c1 (8 * delta) (p - 4) p F2 F3 Hdelta F5 HmodEq.
rewrite /c1 /zz /yy.
rewrite -{1}[Y]Nat2Z.id.
rewrite -Z2Nat.inj_add; tlia; last first.
  apply: le_Int_part_pos. 
  have := pos_INR Y.
  by rewrite /zz /yy in Fc1; lra.
rewrite -R_Ifp.Int_part_INR.
rewrite -plus_Int_part2; last first.
  set V := (_ - _)%R.
  have := base_fp V.
  by rewrite INR_IZR_INZ frac_part_IZR; lra.
set U := (_ + _)%R.
have ->: U = (X + ((v2 + 9) * 2  ^p ) %:R - (v1 * 2 ^ p)%:R)%R.
  by rewrite !mult_INR !plus_INR pow_INR !NNE /U /xx; lra.
rewrite Rminus_Int_part1; last first.
  set V := (_ + _)%R.
  have := base_fp V.
  by rewrite INR_IZR_INZ frac_part_IZR; lra.
rewrite plus_Int_part2; last first.
  have := base_fp X.
  by rewrite INR_IZR_INZ frac_part_IZR; lra.
rewrite !R_Ifp.Int_part_INR.
rewrite Z2Nat.inj_sub; tlia.
rewrite Z2Nat.inj_add; tlia; last first.
  by apply: le_Int_part_pos; lra.
rewrite !Nat2Z.id mod_minus_mult; tlia; last first.
  have FF x : x * 2 ^ p = Z.to_nat (Int_part (x%:R * 2 ^ p)).
    by rewrite -PSE -mult_INR R_Ifp.Int_part_INR Nat2Z.id.
  rewrite !{}FF -Z2Nat.inj_add; try apply: le_Int_part_pos; tlra; last first.
    by rewrite -PSE -mult_INR; apply: pos_INR.
  rewrite -Z2Nat.inj_le.
  - rewrite -plus_Int_part2; last first.
      rewrite -PSE -mult_INR.
      have := base_fp X.
      by rewrite INR_IZR_INZ frac_part_IZR; lra.
    apply: le_Int_part.
    rewrite /xx in GG.
    by rewrite plus_INR NE; lra.
  - apply: le_Int_part_pos.
    rewrite -PSE -mult_INR.
    by apply: pos_INR.
  rewrite -PSE -mult_INR.
  rewrite R_Ifp.Int_part_INR .
  suff : (0 <= Int_part X)%Z by lia.
  by apply: le_Int_part_pos.
rewrite Nat.mod_add; tlia.
rewrite /X -PigE.
have ->: (16 ^ d / 16 * 2 ^ p * PI = Rabs PI * 16 ^ d / 16 * 2 ^ p)%R.
  rewrite Rabs_pos_eq; tlra.
  by have := PI2_1; lra.
have {1}->: 2 ^ (p - 4) = 2 ^ p / 16.
  have {2}->: p = 4 + (p - 4) by lia.
  by rewrite Nat.pow_add_r mult_comm Nat.div_mul.
rewrite -Rdigit_mod_div16 //; lia.
Qed.

(* Extra the first digit from Plouffe formula *)
Definition NpiDigit :=
  let delta := d + p / 4 + 1 in
  if (3 <? p) then
    if (8 * delta <? 2 ^ (p - 4)) then
      let Y := (4 * (NsumV 1) + 
             (9 * pS - (2 * NsumV 4 + NsumV 5 + NsumV 6 + 4 * delta))) in
      let v1 := (Y + 8 * delta) mod 2 ^ p / 2 ^ (p - 4) in
      let v2 := Y mod 2 ^ p / 2 ^ (p - 4) in
      if beq_nat v1 v2 then Some v2 else
      None
    else None
  else None.

Lemma NpiDigit_correct k : 
  NpiDigit = Some k -> Rdigit 16 d PI = k.
Proof.
rewrite /NpiDigit.
case E1 : Nat.ltb => //.
move: E1; rewrite Nat.ltb_lt => E1.
case E2 : Nat.ltb => //.
move: E2; rewrite Nat.ltb_lt => E2.
case: Nat.eqb_spec => // E3 [<-].
by apply: main_thm.
Qed.

End NComputePi.

(* Hexa conversion *)
Definition nToS n :=
  let v := n in  
  match v with
  | 0%nat => "0"%string 
  | 1%nat => "1"%string
  | 2%nat => "2"%string
  | 3%nat => "3"%string
  | 4%nat => "4"%string
  | 5%nat => "5"%string
  | 6%nat => "6"%string
  | 7%nat => "7"%string
  | 8%nat => "8"%string
  | 9%nat => "9"%string
  | 10%nat => "A"%string
  | 11%nat => "B"%string
  | 12%nat => "C"%string
  | 13%nat => "D"%string
  | 14%nat => "E"%string
  | 15%nat => "F"%string
  | _ => "?"%string
end. 
 
(* How many bits of the fixed-point like computation *)
Definition Nprecision := 14.

Definition NpiDigitF k :=
  match NpiDigit Nprecision k with Some v => v | _ => 16 end.

Fixpoint rNpi k n :=
  match n with 
  | S n1 => String.append (nToS (NpiDigitF k)) (rNpi (S k) n1)
  | _ =>  (nToS (NpiDigitF k))
end.

(* Compute string of the hexa representation of pi *)
Definition Npi := rNpi 0.

(* Pi in hexa 

3243F6A8885A308D313198A2E03707344A4093822299F31D00
82EFA98EC4E6C89452821E638D01377BE5466CF34E90C6CC0A
C29B7C97C50DD3F84D5B5B54709179216D5D98979FB1BD1310
BA698DFB5AC2FFD72DBD01ADFB7B8E1AFED6A267E96BA7C904
5F12C7F9924A19947B3916CF70801F2E2858EFC16636920D87
1574E69A458FEA3F4933D7E0D95748F728EB658718BCD58821
54AEE7B54A41DC25A59B59C30D5392AF26013C5D1B02328608
5F0CA417918B8DB38EF8E79DCB0603A180E6C9E0E8BB01E8A3
ED71577C1BD314B2778AF2FDA55605C60E65525F3AA55AB945
748986263E8144055CA396A2AAB10B6B4CC5C341141E8CEA15
*)

(* First 5 digits of Pi *)
Time Compute Npi 5.

Definition Ndigit n := nToS (NpiDigitF n).

(* 6^th decimal of Pi *)
Time Compute Ndigit 5.

(******************************************************************************)
(*                               Turning from N to BigN                       *)
(******************************************************************************)

Require Import BigN.

Open Scope bigN_scope.

Notation " [[ n ]] " := (Z.to_nat [n]).

Lemma specN_add m n : [[m + n]] = ([[m]] + [[n]])%nat.
Proof.
by rewrite BigN.spec_add Z2Nat.inj_add //; apply: BigN.spec_pos.
Qed.

Lemma specN_sub m n : [[m - n]] = ([[m]] - [[n]])%nat.
Proof.
rewrite BigN.spec_sub.
case: (Zmax_spec 0 ([m] - [n])) => [] [H1 ->] /=.
  rewrite le_minus_0 // -Z2Nat.inj_le; tlia.
    by apply: BigN.spec_pos.
  by apply: BigN.spec_pos.
rewrite Z2Nat.inj_sub //.
by apply: BigN.spec_pos.
Qed.

Lemma specN_mul m n : [[m * n]] = ([[m]] * [[n]])%nat.
Proof.
by rewrite BigN.spec_mul Z2Nat.inj_mul //; apply: BigN.spec_pos.
Qed.

Lemma specN_pow m n : ([[m ^ n]] = [[m]] ^ [[n]])%nat.
Proof.
rewrite BigN.spec_pow -[X in _ = X]Nat2Z.id pow_Zpower.
by rewrite !Z2Nat.id //; apply: BigN.spec_pos.
Qed.

Lemma specN_mod m n : 
  (0 < [[n]])%nat -> [[m mod n]] = ([[m]] mod [[n]])%nat.
Proof.
move=> Pn.
rewrite BigN.spec_modulo -[X in _ = X]Nat2Z.id.
by rewrite mod_Zmod  ?Z2Nat.id //; tlia; try by apply: BigN.spec_pos.
Qed.

Lemma specN_cmp m n : m <? n = ([[m]] <? [[n]])%nat.
Proof.
rewrite BigN.spec_ltb.
case E : (_ <? _)%nat.
  move: E; rewrite Nat.ltb_lt -Z2Nat.inj_lt; try by apply: BigN.spec_pos.
  by rewrite -Zlt_is_lt_bool.
have : ~ ([m] < [n])%Z.
  rewrite Z2Nat.inj_lt; try by apply: BigN.spec_pos.
  by rewrite -Nat.ltb_lt E.
by rewrite Zlt_is_lt_bool; case: (_ <? _)%Z.
Qed.

Lemma specN_if_cmp m n p q : 
  [[if m <? n then p else q]] = 
  (if [[m]] <? [[n]] then [[p]] else [[q]])%nat.
Proof. by rewrite specN_cmp; case: (_ <? _)%nat. Qed.

Lemma specN_eqb m n : m =? n = (beq_nat [[m]] [[n]])%nat.
Proof.
rewrite BigN.spec_eqb.
case: Nat.eqb_spec.
  rewrite Z.eqb_eq.
  by apply: Z2Nat.inj; apply: BigN.spec_pos.
case E: (_ =? _)%Z => // [] [].
by move: E; rewrite Z.eqb_eq => ->.
Qed.

Lemma specN_if_eqp m n p q : 
  [[if m =? n then p else q]] = 
  (if beq_nat [[m]] [[n]] then [[p]] else [[q]])%nat.
Proof. by rewrite specN_eqb; case: beq_nat. Qed.

Lemma specN_shiftl m n : 
  ([[BigN.shiftl m n]] = (2 ^ [[n]]) * [[m]])%nat.
Proof.
rewrite BigN.spec_shiftl Z.shiftl_mul_pow2; last first.
  by apply: BigN.spec_pos.
rewrite Z2Nat.inj_mul; last 2 first.
- by apply: BigN.spec_pos.
- by apply: Z.pow_nonneg.
rewrite -[(_ ^ _)%nat]Nat2Z.id pow_Zpower !Z2Nat.id.
  by rewrite mult_comm.
by apply: BigN.spec_pos.
Qed.

Lemma specN_shiftr m n : 
  [[BigN.shiftr m n]] = ([[m]] / (2 ^ [[n]]))%nat.
Proof.
rewrite BigN.spec_shiftr.
  rewrite Z.shiftr_div_pow2; last first.
  by apply: BigN.spec_pos.
rewrite -[(_ / _)%nat]Nat2Z.id.
rewrite div_Zdiv ?pow_Zpower ?Z2Nat.id //.
- by apply: BigN.spec_pos.
- by apply: BigN.spec_pos.
suff : (2 ^ 0 <= 2 ^ [[n]])%nat by rewrite /=; lia.
by apply: Nat.pow_le_mono_r; lia.
Qed.

Lemma specN_div m n : 
  (0 < [[n]] -> [[m / n]] = [[m]] / [[n]])%nat.
Proof.
move=> Pn.
rewrite BigN.spec_div.
rewrite -[(_ / _)%nat]Nat2Z.id div_Zdiv ?Z2Nat.id; tlia.
  by apply: BigN.spec_pos.
by apply: BigN.spec_pos.
Qed.

(******************************************************************************)

Section ComputePi.

(* Precision *)
Variable p : N.
Definition pN := BigN.of_N p.
Definition pS := BigN.shiftl 1 pN.

(* Digit position *)
Variable d : N.
Definition dN := BigN.of_N d.

Section power.

Variable m : bigN.

Fixpoint powerModc a (b : positive) (c : bigN) :=
match b with 
  xH => (a * c) mod m
| xO b1 => powerModc ((a * a) mod m) b1 c
| xI b1 => powerModc ((a * a) mod m) b1 ((a * c) mod m)
end.

Lemma specN_powerModc a b c : (0 < [[m]])%nat ->
  [[powerModc a b c]] = (([[a]] ^ (Pos.to_nat b) * [[c]]) mod [[m]])%nat.
Proof.
move=> mP; elim: b a c => // [b1 IH a c|b1 IH a c|a c]; last first.
- by rewrite /= specN_mod // specN_mul mult_1_r.
- rewrite IH Pos2Nat.inj_xO.
  rewrite Nat.pow_mul_r.
  rewrite specN_mod //.
  rewrite -[X in X = _]Nat.mul_mod_idemp_l; tlia.
  rewrite -[X in _ = X]Nat.mul_mod_idemp_l; tlia.
  congr (_ * _ mod _)%nat.
  rewrite -pow_mod; tlia.
  congr (_ ^ _ mod _)%nat.
  by rewrite specN_mul /=; lia.
rewrite IH Pos2Nat.inj_xI.
rewrite Nat.pow_succ_r; tlia.
rewrite Nat.pow_mul_r.
rewrite !specN_mod //.
rewrite Nat.mul_mod_idemp_r; tlia.
rewrite !specN_mul // Mult.mult_assoc.
rewrite -[X in X = _]Nat.mul_mod_idemp_l; tlia.
rewrite -[X in _ = X]Nat.mul_mod_idemp_l; tlia.
congr (_ * _ mod _)%nat.
rewrite [X in (_ = X mod _)%nat]mult_comm.
rewrite -[X in _ = X]Nat.mul_mod_idemp_l; tlia.
rewrite pow_mod; tlia.
rewrite [X in _ = X]Nat.mul_mod_idemp_l /= ; tlia.
by congr ((_ mod _) ^ _ * _ mod _)%nat; lia.
Qed.

End power.

(* a ^ b mod m *)
Definition powerMod a (b : N) m := 
  match b with Npos b1 => powerModc m a b1 1 | _ => 
                  if m <? 2 then 0 else 1 end.

Lemma specN_powerMod a b m:  (0 < [[m]])%nat ->
  [[powerMod a b m]] = (([[a]] ^ (N.to_nat b)) mod [[m]])%nat.
Proof.
move=> Pm.
case: b => [|b ] /=.
  rewrite specN_cmp.
  case E : (_ <? _)%nat.
    move: E; rewrite Nat.ltb_lt.
    have ->: [[2]] = 2%nat by [].
    by case: [[_]] Pm => //= [] [|n]; lia.
  rewrite Nat.mod_small //.
  suff : ~([[m]] < 2)%nat by lia.
  by rewrite -Nat.ltb_lt; case: (_ <? _)%nat E.
rewrite specN_powerModc; tlia.
by rewrite mult_1_r.
Qed.

Compute powerMod 2 123939 1239393331.
Compute powerMod 17 262626 1239393331.

(* Iterative state : counter iN = i and result *) 
Inductive stateF := StateF (iN : bigN) (i : N) (s : bigN).

(* Un pas : i = i + 1, iN = iN + 1,
            ress = res + (16^(d - 1 - k)) * 2^p / (8 * i + k) *)
Definition iterF (k : bigN) (st : stateF) :=
  let: StateF iN i res := st in
  let r := 8 * iN + k in
  let res := res + (BigN.shiftl (powerMod 16 (d - 1 - i)%N r) pN) / r in
  let res := if res <? pS then res else res - pS in
  StateF (iN + 1) (i + 1)%N res.

Definition eq_StateF (s1 : stateF) (s2 : NstateF) :=
  let: StateF i1 i1N res1 := s1 in
  let: NStateF i2 res2 := s2 in
  [[i1]] = i2 /\ N.to_nat i1N = i2 /\ [[res1]] = res2.

Lemma specN_iterF s1 s2 k : (0 < [[k]])%nat ->
  eq_StateF s1 s2 ->
  eq_StateF (iterF k s1) (NiterF (N.to_nat p) (N.to_nat d) [[k]] s2).
Proof.
move=> Pk.
case: s1; case: s2.
rewrite /NiterF /iterF. 
move=> k2 s2 k1 l1 s1 [<- [k1E <-] ].
have F : (0 < [[8]] * [[k1]] + [[k]])%nat.
  set x := (_ * _)%nat; lia.
repeat split.
- by rewrite specN_add /= Plus.plus_comm.
- by rewrite -k1E Nnat.N2Nat.inj_add Plus.plus_comm.
rewrite !(specN_if_cmp, specN_add, specN_sub, specN_mul, 
          specN_div, specN_shiftl, specN_powerMod) //.
have ->: [[16]] = 16%nat by [].
have ->: [[8]] = 8%nat by [].
rewrite /pS /NpowerMod !Nnat.N2Nat.inj_sub k1E.
have ->: N.to_nat 1 = 1%nat by [].
have ->: N.to_nat p = [[pN]].
  by rewrite BigN.spec_of_N -Z_N_nat N2Z.id.
by rewrite mult_1_r.
Qed.

(* Compute \sum_{i = 0 to d - 1} (16^(d - 1 - i)) * 2^p / (8 * i + k) *)
Definition iterL k :=
   N.iter d (iterF k) (StateF 0 0%N 0).

Lemma specN_iterL k : (0 < [[k]])%nat ->
  eq_StateF (iterL k) (NiterL (N.to_nat p) (N.to_nat d) [[k]]).
Proof.
move=> Pk.
rewrite /iterL /NiterL.
rewrite -{1}[d]Nnat.N2Nat.id -Nnat.Nat2N.inj_iter.
elim: {1 3}N.to_nat => //= n IH.
by apply: specN_iterF.
Qed.

(* Iterative state : counter iN = i shift s and result *) 
Inductive stateG := StateG (iN : bigN) (i : N) (s : bigN) (res : bigN).

Definition eq_StateG (st1 : stateG) (st2 : NstateG) :=
  let: StateG i1N i1 s1 res1 := st1 in
  let: NStateG i2 s2 res2 := st2 in
  [[i1N]] = i2 /\ N.to_nat i1 = i2 /\ [[s1]] = s2 /\ [[res1]] = res2.

(* Un pas : iN = iN + 1, i = i + 1, s = s / 16,
            res = res + (s / (8 * i + k)) *)
Definition iterG (k : bigN) (st : stateG) :=
  let: StateG iN i s res := st in
  let r := 8 * iN + k in
  let res := res + (s / r) in
  StateG (iN + 1) (i + 1)%N (BigN.shiftr s 4) res.

Lemma specN_iterG st1 st2 k : (0 < [[k]])%nat ->
  eq_StateG st1 st2 ->
  eq_StateG (iterG k st1) (NiterG [[k]] st2).
Proof.
move=> Pj.
case: st1; case: st2.
rewrite /NiterG /iterG. 
move=> k2 d2 n2 k1 l1 d1 n1 [<- [k1E [<- <-] ] ].
repeat split.
- by rewrite specN_add /= Plus.plus_comm.
- by rewrite -k1E Nnat.N2Nat.inj_add Plus.plus_comm.
- by rewrite specN_shiftr.
rewrite !(specN_if_cmp, specN_add, specN_sub, specN_mul, 
          specN_div, specN_shiftl, specN_powerMod) //.
set x := (_ * _)%nat; lia.
Qed.

(* Compute \sum_{i = d to infinity} (16^(d - 1 - i)) / (8 * i + k) *)
Definition iterR k :=
  N.iter (p / 4) (iterG k) (StateG dN d (BigN.shiftr pS 4) 0).

Lemma specN_iterR k : (0 < [[k]])%nat ->
  eq_StateG (iterR k) (NiterR (N.to_nat p) (N.to_nat d) [[k]]).
Proof.
move=> Pk.
rewrite /iterR /NiterR.
have -> : (p / 4)%N = (N.of_nat (N.to_nat p / 4)).
  apply: N2Z.inj.
  by rewrite N2Z.inj_div nat_N_Z div_Zdiv ?N_nat_Z; lia.
rewrite -Nnat.Nat2N.inj_iter.
elim: (_ / _)%nat => [|n IH].
  repeat split.
    by rewrite -Z_N_nat BigN.spec_of_N N2Z.id.
  rewrite /pS specN_shiftr /pS specN_shiftl.
  rewrite Nat.mul_1_r.
  by rewrite -Z_N_nat BigN.spec_of_N N2Z.id.
by apply: specN_iterG.
Qed.

(* Compute \sum_{i = 0 to infinity} (16^(d - 1 - i)) / (8 * i + k) *)
Definition sumV k :=
  let: StateF _ _ res1 := iterL k in
  let: StateG _ _ _ res2 := iterR k in res1 + res2.

Lemma specN_sumV k : (0 < [[k]])%nat ->
  [[sumV k]] = NsumV (N.to_nat p) (N.to_nat d) [[k]].
Proof.
move=> Pk.
rewrite /sumV /NsumV.
have := specN_iterL _ Pk.
have := specN_iterR _ Pk.
case: iterL => /= k1 l1 s1.
case: NiterL => /= k2 l2.
case: iterR => /= k3 l3 d3 s3.
case: NiterR => /= k4 l4 s4.
move=> [_ [_ [_] <-] ] [_ [_] <-].
by rewrite specN_add.
Qed.

(* Extra the first digit from Plouffe formula *)
Definition piDigit :=
  let delta := dN + pN / 4 + 1 in
  if (3 <? pN) then
    if (8 * delta <? 2 ^ (pN - 4)) then
      let Y := (4 * (sumV 1) + 
             (9 * pS - (2 * sumV 4 + sumV 5 + sumV 6 + 4 * delta))) in
      let v1 := (Y + 8 * delta) mod 2 ^ pN / 2 ^ (pN - 4) in
      let v2 := Y mod 2 ^ pN / 2 ^ (pN - 4) in
      if v1 =? v2 then Some v2 else
      None
    else None
  else None.

Lemma specN_piDigit :
  match piDigit with 
  | Some x =>  NpiDigit (N.to_nat p) (N.to_nat d) = Some [[x]]
  | None => NpiDigit (N.to_nat p) (N.to_nat d) = None
  end.
Proof.
have F1 : (0 < [[2]] ^ [[pN]])%nat.
  set x := (_ ^ _)%nat.
  suff : (2 ^ 0 <= x)%nat by rewrite /=; lia.
  by apply: Nat.pow_le_mono_r; lia.
have F2 : (0 < [[2]] ^ ([[pN]] - [[4]]))%nat.
  set x := (_ ^ _)%nat.
  suff : (2 ^ 0 <= x)%nat by rewrite /=; lia.
  by apply: Nat.pow_le_mono_r; lia.
have F3 : (0 < [[4]])%nat.
  by have ->: [[4]] = 4%nat by []; lia.
have F5 : (0 < [[5]])%nat.
  by have ->: [[5]] = 5%nat by []; lia.
have F6 : (0 < [[6]])%nat.
  by have ->: [[6]] = 6%nat by []; lia.
rewrite /piDigit /NpiDigit.
rewrite !(specN_cmp, specN_eqb, specN_add, specN_sub, specN_mul, 
          specN_div, specN_shiftl, specN_pow, specN_mod, specN_sumV) //.
have-> : [[pN]] = N.to_nat p.
  by rewrite -Z_N_nat BigN.spec_of_N N2Z.id.
case: (_ <? _)%nat => //.
have-> : [[dN]] = N.to_nat d.
  by rewrite -Z_N_nat BigN.spec_of_N N2Z.id.
case: (_ <? _)%nat => //.
rewrite Nat.mul_1_r.
case: beq_nat => //.
rewrite !(specN_cmp, specN_eqb, specN_add, specN_sub, specN_mul, 
          specN_div, specN_shiftl, specN_pow, specN_mod, specN_sumV) //.
have-> : [[pN]] = N.to_nat p.
  by rewrite -Z_N_nat BigN.spec_of_N N2Z.id.
have-> : [[dN]] = N.to_nat d.
  by rewrite -Z_N_nat BigN.spec_of_N N2Z.id.
by rewrite Nat.mul_1_r.
Qed.

Lemma piDigit_correct k : 
  piDigit = Some k -> Rdigit 16 (N.to_nat d) PI = [[k]].
Proof.
have := specN_piDigit.
case: piDigit => // n H [<-].
by apply: NpiDigit_correct H.
Qed.

End ComputePi.

 
(* How many bits of the fixed-point like computation *)
Definition precision := 36%N.

Definition piDigitF d :=
  match piDigit precision d with Some k => k | _ => 16 end.

Definition NToS n := nToS (Z.to_nat (BigN.to_Z n)).


Fixpoint rpi k n :=
  let v := NToS (piDigitF (N.of_nat k)) in
  match n with 
  | S n1 => String.append v (rpi (S k) n1)
  | _ =>  v
end.

(* Compute string of the hexa representation of pi *)
Definition pi := rpi 0.

Definition digit n := NToS (piDigitF n).

(* 1 000 000^th decimal of Pi *)
Time Compute digit 1000000000.


(* Pi in hexa 

3243F6A8885A308D313198A2E03707344A4093822299F31D00
82EFA98EC4E6C89452821E638D01377BE5466CF34E90C6CC0A
C29B7C97C50DD3F84D5B5B54709179216D5D98979FB1BD1310
BA698DFB5AC2FFD72DBD01ADFB7B8E1AFED6A267E96BA7C904
5F12C7F9924A19947B3916CF70801F2E2858EFC16636920D87
1574E69A458FEA3F4933D7E0D95748F728EB658718BCD58821
54AEE7B54A41DC25A59B59C30D5392AF26013C5D1B02328608
5F0CA417918B8DB38EF8E79DCB0603A180E6C9E0E8BB01E8A3
ED71577C1BD314B2778AF2FDA55605C60E65525F3AA55AB945
748986263E8144055CA396A2AAB10B6B4CC5C341141E8CEA15
*)

(* First 500 digits of Pi by blocks of 50 *)
Time Compute rpi 0 49.
Time Compute rpi 50 49.
Time Compute rpi 100 49.
Time Compute rpi 150 49.
Time Compute rpi 200 49.
Time Compute rpi 250 49.
Time Compute rpi 300 49.
Time Compute rpi 350 49.
Time Compute rpi 400 49.
Time Compute rpi 450 49.


