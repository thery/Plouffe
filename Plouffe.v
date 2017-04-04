(* Require ssreflect tactics *)
From mathcomp Require Import ssreflect.
(* working with Coq Reals *)
Require Import NPeano Psatz Reals.
(* Using Coquelicot for Series, Power Series and Integrals *)
Require Import Coquelicot.Coquelicot.


(******************************************************************************)
(*                                                                            *)
(*                          PROOF OF THE PLOUFFE FORMULA                      *)
(*                                                                            *)
(******************************************************************************)

Notation "a %:R " := (INR a) (at level 10).

Open Scope R_scope.

(* try psatz R or Z *)
Ltac tlia := try lia.
Ltac tlra := try lra.

(* lrg: link between Coquelicot structure and R ?? *)

Ltac Rcotpatch := 
 change (NormedModule.sort R_AbsRing R_NormedModule) with R; repeat
  match goal with 
    |- context[scal ?X ?Y] => change (scal X Y) with (X * Y)
  end.

(* lrg: pow_lt_1_compat with Rabs RPow_abs *)
Lemma pow_lt_1 x n (xL1 : Rabs x < 1) : Rabs (x ^ (S n)) < 1.
Proof.
have axpos:= (Rabs_pos x).
by rewrite  -RPow_abs; case: (pow_lt_1_compat (Rabs x) (S n)); tlra; tlia.
Qed.


Section Hole.
(* mimic some properties of the ssreflect bigop library:
 we do not use this bigop library because we need to add eqType and choice type on R
and we need Series and PSeries from Coquelicot *)

(* needed to define the S_k of Plouffe proof: S_k = \sum 1/(16^i(8i + k )) *)


Definition hole (k : nat) (a : nat -> R) (n : nat) :=
  if n mod k =? 0 then a (n / k)%nat else 0.

(* the sum from the Coq R library, with small indexes *)

Lemma sum_f_R0_holes_small a g k n 
        (trm := fun i => hole k a i * g i) l :
 (S l < k)%nat
    -> sum_f_R0 (fun i => trm (S(k * n) + i)%nat) l = 0.
Proof.
elim: l => [|l IHl] lk.
  rewrite /= /trm /hole (_ : (_ mod _ = 1)%nat) /=; tlra.  
  by rewrite plus_n_Sm Plus.plus_comm mult_comm Nat.mod_add ?Nat.mod_small;lia.
rewrite /=; set s := sum_f_R0 _ _.
rewrite plus_n_Sm Plus.plus_comm mult_comm /trm /hole Nat.mod_add;tlia.
by rewrite  Nat.mod_small /= ?Rmult_0_l ?Rplus_0_r /s ?IHl;tlia.
Qed.

(* same result for coquelicot sum *)
Lemma sum_n_holes_small a g k n 
        (trm := fun i => hole k a i * g i) l :
 (S l < k)%nat
    -> sum_n (fun i => trm (S(k * n) + i)%nat) l = 0.
Proof.
by move=> Hlk; rewrite sum_n_Reals sum_f_R0_holes_small.
Qed.

(* cut the sum into 2 parts *)

Lemma sumf_f_R0_add_r f m n : (n <> 0)%nat ->
  sum_f_R0 f (m + n) =
      sum_f_R0 f m + sum_f_R0 (fun i => f (S m + i)%nat) (pred n).
Proof.
case: n => // n _.
elim: n => [|n IH]; first by rewrite Plus.plus_comm /= plus_0_r.
by rewrite Nat.add_succ_r /= IH /=; lra.
Qed.


Lemma sum_f_R0_holes k a g n :
  (k <> 0)%nat -> sum_f_R0 (fun i => hole k a i * g i) (k * n) =
     sum_f_R0 (fun i => a i * g (k * i)%nat) n.
Proof.
set trm := (fun _ =>  _).
move => kn0; elim: n => [| n IH].
  rewrite /trm /= mult_0_r /hole /= Nat.mod_0_l /=; tlia.
  by rewrite Nat.div_0_l; tlia.
rewrite mult_succ_r sumf_f_R0_add_r // {}IH {}/trm.
congr (_ + _).
case: k kn0 => //= [] [|k] _ /=.
  by rewrite !plus_0_r /hole Nat.mod_1_r Nat.div_1_r.
rewrite  sum_f_R0_holes_small //.
rewrite /hole plus_n_Sm Nat.add_mod ?Nat.mod_same; tlia.
change (n + (n + k * n))%nat with (S (S k) * n)%nat.
rewrite mult_comm Nat.mod_mul ?Nat.mod_0_l; tlia.
rewrite Rplus_0_l.
congr (a _ * g _); tlia.
by rewrite -mult_succ_l Nat.div_mul.
Qed.

(* same result for coquelicot sum *)
Lemma sum_n_holes k a g n :
  (k <> 0)%nat -> sum_n (fun i => hole k a i * g i) (k * n) =
     sum_n (fun i => a i * g (k * i)%nat) n.
Proof.
by move=> kpos; rewrite !sum_n_Reals sum_f_R0_holes.
Qed.


Lemma fill_holes k a x : 
  (k <> 0)%nat -> ex_pseries a (x ^ k) ->
  PSeries (hole k a) x = Series (fun n => a n * x ^ (k * n)).
Proof.
move=> kn0 exs; rewrite /PSeries /Series.
rewrite -(Lim_seq_subseq (sum_n _) (fun n => k * n)%nat).
- set u := fun _ => _; set v:= sum_n _.
  rewrite (Lim_seq_ext u v) /u /v // => n.
  by apply: sum_n_holes.
- apply: eventually_subseq => n.
  by rewrite mult_succ_r; lia.
case: exs => l il.
exists l; move => eps Heps.
case (il eps Heps) => // N Pn; exists (k * N)%nat => n nN.
rewrite [n](Nat.div_mod _ _ kn0).
set trm := (fun _ =>  _).
case: (eq_nat_dec (n mod k) 0) => [->|Dk].
  rewrite plus_0_r sum_n_holes //.
  rewrite  (sum_n_ext  _ (fun i => (x ^ k) ^ i * a i)); last first.
    by move => i; rewrite Rmult_comm; congr (_ * _); rewrite pow_mult.
  apply: Pn.
  by apply: Nat.div_le_lower_bound; lia.
move: (sumf_f_R0_add_r trm (k * (n / k)) (n mod k)).
rewrite -!sum_n_Reals=> -> //.
rewrite (_ : sum_n _ (pred _) = 0) ?Rplus_0_r; last first.
  apply: sum_n_holes_small.
  have := Nat.mod_upper_bound n _ kn0.
  by case: (_ mod _)%nat Dk => [|u] /=; tlia.
rewrite sum_n_holes //.
rewrite (sum_n_ext _ (fun i => (x ^ k) ^ i * a i)); last first.
  by move => i; rewrite Rmult_comm; congr (_ * _); rewrite pow_mult.
apply: Pn.
by apply: Nat.div_le_lower_bound; lia.
Qed.

End Hole.

Section Radius.

Variable a : nat -> R.
Hypothesis aP : forall n, 0 <= a n <= 1.

Lemma PS_cv x : 0 <= x -> x < 1 ->
 Rbar.Rbar_lt (Rbar.Finite (Rabs x)) (CV_radius a) .
Proof.
move=> Px xL1.
have [F1 F2] := CV_radius_bounded a.
suff F : Rbar.Rbar_le (Rbar.Finite ((x + 1) / 2)) (CV_radius a).
  apply: Rbar.Rbar_lt_le_trans F.
  by rewrite Rabs_pos_eq /Rbar.Rbar_lt; lra.
apply: F1.
exists 1 => n.
have [H1 H2] := aP n.
rewrite Rabs_pos_eq; last first.
  apply: Rmult_le_pos; tlra.
  by apply: pow_le; lra.
rewrite -{4}(Rmult_1_r 1).
apply: Rmult_le_compat; tlra; first by apply: pow_le; lra.  
by rewrite -{4}(pow1 n); apply: pow_incr; lra.
Qed.

End Radius.


Section Plouffe.

Lemma PSerie_pow_add x k f a:
  Series (fun i => (a i ) * x ^ (k + f i)) = 
          x ^ k * Series (fun i => (a i) * x ^ f i).
Proof.
rewrite -Series_scal_l; apply: Series_ext => u.
by rewrite -Rmult_assoc pow_add; lra.
Qed.

(* Pseries with holes : coeff i = 0 except for 8*i , needs to use hole *)
Lemma PSeries_hole x a d k :  0 <= x < 1 ->  
                  Series (fun i : nat => (a * x ^ (d + (S k) * i))) =
                       PSeries (PS_incr_n (hole (S k) (fun _ => a)) d) x.
Proof.
move=> [Hx0 Hx1].
rewrite PSerie_pow_add.
rewrite -fill_holes //;first by rewrite PSeries_incr_n.
apply: (ex_series_ext (fun i =>  a * (x ^ (S k)) ^ i)) => [i|].
  rewrite pow_n_pow /scal /= /mult /=; lra.
apply: ex_series_scal; apply/ex_series_geom/pow_lt_1.
by rewrite Rabs_pos_eq.
Qed.

Lemma RInt_Series_hole n x : 0 <= x -> x < 1 -> (0 < n)%nat ->
      RInt (fun x => Series (fun i => x ^ (n - 1 + 8 * i))) 0 x = 
            PSeries (PS_Int (PS_incr_n (hole 8 (fun _ => 1)) (n - 1))) x.
Proof.
move=> xpos xlt1 npos.
set h8 := hole _ _.
rewrite (RInt_ext _ (fun x => PSeries (PS_incr_n h8 (n - 1)) x)).
(* exchange integral and power_series *)
  rewrite  RInt_PSeries //.
  apply: PS_cv=> // i; rewrite PS_incr_n_simplify /= /zero /=.
  case: (le_lt_dec (n - 1) i); tlra.
  rewrite /h8 /hole.
  by case: Nat.eqb; lra.
move=> y Hy.
rewrite -PSeries_hole ; first by apply: Series_ext=>i; lra.
by move: Hy;rewrite Rmin_left ?Rmax_right; lra.
Qed.


Section Sk.
  
Variable k : nat.
Definition a (i : nat) := / (16 ^ i * (8 * i + k)%:R).
Definition Sk := Series a.

Lemma Sk_Rint  : 
 (0 < k)%nat ->
  Sk = sqrt 2 ^ k  * RInt (fun x => x ^ (k - 1) / (1 - x ^ 8)) 0 (/ sqrt 2). 
Proof.
move=> kpos.
(* have hr2:=  sqrt2_neq_0.*)
have sqrtp:= Rlt_sqrt2_0.
have h16:  (/ sqrt 2) ^ 8 = /16.
  have -> : (8 = 2 * 4)%nat by [].
  by rewrite pow_sqr -Rinv_mult_distr ?sqrt_sqrt; lra.
have h16i i: (16 ^ i) <> 0 by apply: pow_nonzero; lra.
have hn0 i : (8 * i + k) %:R <> 0 by apply: not_0_INR; lia.
have H1 i:  / (16 ^ i * (8 * i + k)%:R) = sqrt 2 ^ k *
     (fun x => (x ^ (k + 8*i) / ((8  * i) + k)%:R)) (/ sqrt 2).
  rewrite pow_add; field_simplify => //.
  rewrite -Rpow_mult_distr Rinv_r ?pow1; tlra;  field_simplify => //.
  by rewrite pow_mult h16 -Rinv_pow; tlra; field.
rewrite /Sk (Series_ext _ _ H1) Series_scal_l  {H1}.
congr (_ * _).
have sqrtip: (0 < / (sqrt 2)) by apply:Rinv_0_lt_compat.
have sqrt2_1 : 1 < sqrt 2.
  by rewrite -{1}sqrt_1; apply: sqrt_lt_1; lra.
have sqrt2i_1 : / sqrt 2 < 1.
  by rewrite -[X in _ < X]Rinv_1; apply: Rinv_1_lt_contravar; lra.
pose g x i := x ^ (k - 1 + 8 * i).
rewrite (RInt_ext _ (fun x => ( Series (g x)))); last first.
  move=> x; rewrite Rmin_left ?Rmax_right //; tlra; move=> [hx0 hx1].
  rewrite /g. 
  rewrite (Series_ext _ (fun i : nat => 1 * x ^ (k - 1 + 8 * i))); last first.
    by move => i ; lra.
  rewrite PSerie_pow_add.     
  rewrite (Series_ext _ (fun i => (x ^ 8) ^ i))=>[|i];last first.
    by rewrite pow_mult; lra.
  by rewrite Series_geom //; apply: pow_lt_1; rewrite Rabs_pos_eq;lra.
rewrite RInt_Series_hole //; tlra.
rewrite (Series_ext _ 
         (fun n0 => (/(sqrt 2)) ^ k / (8 * n0 +k)%:R * 
              (/(sqrt 2)) ^ (ssrnat.muln 8 n0))); last first.
  move=> i.
  have <- : ( 8 * i)%nat = ssrnat.muln 8 i by [].
  by rewrite pow_add; lra.
rewrite -fill_holes; tlia; last first.
  apply: (ex_pseries_ext  
          (fun i => (/(sqrt 2)) ^ k / (8 * i + k) %:R)) => [i|]; Rcotpatch; tlra.
  apply: CV_radius_inside.
  apply: PS_cv => //; tlra.
  move=> n.
  have F1 : 1 <= (8 * n + k)%:R by apply: (le_INR 1); lia.
  split. 
    apply:Rdiv_le_0_compat; tlra.
    by apply: pow_le; lra.
  apply (Rdiv_le_1 ((/ sqrt 2) ^ k) (INR (8 * n + k)%nat)).
    by apply: lt_0_INR; lia.
  apply Rle_trans with 1; tlra.
  by apply Rlt_le, pow_lt_1_compat; tlra. 
case: k {  g hn0} kpos => [| n _]; first by move: (lt_irrefl 0).
set PSL := PSeries _ _.
rewrite (PSeries_decr_n_aux _ (n + 1) (/ (sqrt 2))); last first.
  case=> //= i Hi;rewrite PS_incr_n_simplify.
  case: (le_lt_dec (S n - 1) i)=> e; tlia.
  by rewrite /Rdiv Rmult_0_l.
rewrite /PSL -PSeries_scal.
apply: PSeries_ext=> i.
rewrite /hole.
case Nat.eqb_spec => e; last first.
  rewrite /PS_scal /PS_decr_n.
  have -> : (n + 1 + i = S (n + i))%nat by lia.
  rewrite /PS_Int PS_incr_n_simplify.
  have->: (n + i - (S n - 1) = i)%nat by lia.
  rewrite (iffRL (beq_nat_false_iff _ _) e).
  by case: le_lt_dec; Rcotpatch; rewrite /= /Rdiv Rmult_0_l Rmult_0_r.
rewrite /PS_scal.
rewrite (_ : PS_decr_n _ _ _ = /(i + n + 1)%:R).
  suff -> : (8 * (i / 8) +  S n = i + n + 1)%nat.
    rewrite /= Rmult_comm /= pow_add pow_1; Rcotpatch; lra.
  by rewrite {2}(Nat.div_mod i 8); lia.
rewrite /PS_decr_n.
have -> : (n + 1 + i = S (n + i))%nat by lia.
rewrite /PS_Int PS_incr_n_simplify.
case: (le_lt_dec (S n - 1) (n + i)) => Hi; tlia.
have-> : (n + i - (S n - 1) = i)%nat by lia.
by rewrite e /Rdiv Rmult_1_l; congr (/_%:R); tlia.
Qed.

Lemma ex_RInt_Sk  n (f := fun x =>  (x ^ n/ (1 - x ^ 8))) :
  ex_RInt f 0  (/ sqrt 2).
Proof.
  have pK m  x : continuity_pt (fun x : R => x ^ m) x.
  elim: m => /=[|m IH]; first by apply: continuity_pt_const.  
  apply: continuity_pt_mult => //.
  by apply: continuity_pt_id.
apply: ex_RInt_continuous=> x Hx.
apply: continuous_mult; apply:ex_derive_continuous; auto_derive=>//.
suff : 0 < 1 - x ^ 8 by lra.
have sqrtp:= Rlt_sqrt2_0.
have sqrtip: (0 < / (sqrt 2)) by apply: (Rinv_0_lt_compat (sqrt 2) sqrtp).
have sqrt2_1 : 1 < sqrt 2.
  by move: (sqrt_lt_1 1 2); rewrite sqrt_1; apply;lra.
have sqrt2i_1 : / sqrt 2 < 1. 
  by move: (Rinv_1_lt_contravar 1); rewrite Rinv_1;apply;lra.
move:Hx; rewrite Rmin_left ?Rmax_right; tlra; move=>[hx0 hxr2].
move:(pow_lt_1 x 7); rewrite !Rabs_pos_eq; tlra.
by apply: pow_le.
Qed.

End Sk.


Lemma is_RInt_pow n b: is_RInt (fun x => (x ^ n)) 0 b (b ^ (S n)/ (S n)%:R).
Proof.
pose f x := (x ^ S n) / (S n)%:R.
have der_xSn x : is_derive f x (x ^ n).
rewrite /f {f}; auto_derive => //; case:n =>[//| n]; Rcotpatch; field.
  by move: (INRp1_pos (S n)); lra.
apply is_RInt_ext with (Derive f); first by move=> x Hx; apply/is_derive_unique. 
have -> : b ^ S n / (S n) %:R = f b - f 0.
  by rewrite /f pow_ne_zero //; field; apply:not_0_INR.
apply:is_RInt_derive=>  x Hx; rewrite /f.
   by apply: Derive_correct; auto_derive.
apply: (continuous_ext (fun x => x ^ n) (Derive f)).
  by move=> y; rewrite /f; apply eq_sym; apply/is_derive_unique.
by apply: ex_derive_continuous; auto_derive.
Qed.

Lemma RInt_pow n b : RInt (fun x => x ^ n) 0 b = b ^ (S n)/ (S n)%:R.
Proof. by apply/is_RInt_unique/is_RInt_pow. Qed.

Fact x2p1 x : 0 < x ^ 2 - 2 * x + 2.
Proof.
have->: x ^ 2 - 2 * x + 2 = (x - 1)^2 + 1 by ring.
by have := pow2_ge_0 (x - 1); lra.
Qed.

Lemma RInt_Spart1 :
  RInt (fun x => (4 - 4 * x) / (x ^ 2 - 2 * x + 2)) 0 1 = 2 * (ln 2 - ln 1).
Proof.
have D_part1 x:    Derive (fun x => -2 * ln (x ^ 2 - 2 * x + 2)) x  = 
         (4 - 4 * x) / (x ^ 2 - 2 * x + 2).
  have hx := x2p1 x.
  by apply: is_derive_unique; auto_derive; Rcotpatch;   tlra; try   field;tlra.
rewrite (RInt_ext _ (Derive (fun x => -2 * ln (x ^ 2 - 2 * x + 2))))=> 
    [|x _]; last by rewrite D_part1.
set f := fun x => _.
have ->: 2 * (ln 2 - ln 1) = f 1 - f 0.
  rewrite /f pow1 Rmult_1_r  pow_ne_zero; tlia.
by ring_simplify (1 - 2 + 2); ring_simplify (0 - 2 * 0 + 2); ring.
apply: RInt_Derive => x _.
  rewrite /f;auto_derive.
  by have := x2p1 x; lra.
apply:  (continuous_ext (fun x => (4 - 4 * x) / (x ^ 2 - 2 * x + 2))).
  by move=> z; rewrite D_part1 .
apply:ex_derive_continuous; auto_derive.
by have hx := x2p1 x; lra.
Qed.

Fact  btwnsqrt2  x : -sqrt 2 < x < sqrt 2 -> 0 < 2 - x ^ 2.
Proof.
move=> [xP xL1].
have->: 2 - x ^ 2 = (sqrt 2 - x) * (sqrt 2 + x).
  suff {1}->: 2 = (sqrt 2) ^ 2 by ring.
  by rewrite (pow_add _ 1) pow_1 sqrt_sqrt; auto with real.
by apply: Rmult_lt_0_compat; lra.
Qed.

Fact sqrt2m1_pos : 0 < sqrt 2 - 1.
Proof.
by rewrite -{3}sqrt_1; apply: Rlt_Rminus; apply: sqrt_lt_1; lra.
Qed.

Fact x_between x : 0 <= x <= 1 -> - sqrt 2 < x < sqrt 2.
by  have := sqrt2m1_pos; lra.
Qed.
 
Lemma Derive_ln_x2 x :  
  -sqrt 2 < x < sqrt 2 -> 
   Derive (fun x => 2 * ln (2 - x ^ 2)) x  = (4 * x) / (x ^ 2 - 2).
Proof.
move=> xL1.
have hx := btwnsqrt2 x xL1; tlra.
by apply: is_derive_unique; auto_derive; Rcotpatch; tlra;field; lra.
Qed.

Lemma cont_Spart3 x (Hx : 0 <= x <= 1) : 
  continuous(fun x0 : R => 4 * x0 / (x0 ^ 2 - 2)) x.
Proof.
have hx := (x_between x Hx).
have hx2 := ( btwnsqrt2 x hx). 
have hx2': x^2 -2 < 0; tlra.
by apply:ex_derive_continuous; auto_derive; lra.
Qed.

Lemma RInt_Spart3 : 
  RInt (fun x => (4 * x) / (x ^ 2 - 2)) 0 1 = 2 * (ln 1 - ln 2).
Proof.
rewrite (RInt_ext _ (Derive (fun x => 2 * ln (2 - x ^ 2))))
     => [|x Hx]; last first.
  rewrite Rmin_left in Hx; auto with real.
  rewrite Rmax_right in Hx; auto with real.
  by rewrite Derive_ln_x2 //; apply: x_between; lra.
set f := fun x => _.
have ->: 2 * (ln 1 - ln 2) = f 1 - f 0.
  rewrite /f.
  set x := 2 - _; have {x}->: x = 1 by rewrite /x; ring.
  set x := 2 - _; have {x}->: x = 2 by rewrite /x; ring.
  by ring.
apply: RInt_Derive => x Hx; 
    rewrite Rmin_left in Hx; auto with real;
    rewrite Rmax_right in Hx; auto with real.
  rewrite /f; auto_derive.
  by apply: btwnsqrt2; apply: x_between.
apply:  (continuous_ext_loc _ (fun x => (4 * x) / (x ^ 2 - 2))).
  exists (mkposreal _ sqrt2m1_pos) => z Hz.
  rewrite /=  in Hz.
  rewrite Derive_ln_x2 //.
  have : Rabs (z + - x) < sqrt 2 - 1 by [].
  split_Rabs; tlra.
exact: cont_Spart3.
Qed.

Lemma Derive_4atan x :  
  Derive (fun x => 4 * atan (x - 1)) x  = 4 / (1 + (x - 1)^2).
Proof.
apply: is_derive_unique; auto_derive =>//.
Rcotpatch; field.
by have := x2p1 x; lra.
Qed.

Lemma RInt_Spart2 : RInt (fun x => 4 / (1 + (x  - 1)^ 2)) 0 1 = PI.
Proof.
rewrite (RInt_ext _ (Derive (fun x => 4 * atan (x - 1))))
        =>  [|x _]; last first.
  by rewrite Derive_4atan.
set f := fun x => _.
have ->: PI = f 1 - f 0.
  by rewrite /f Rminus_eq_0 atan_0 Rminus_0_l atan_opp atan_1; lra.
apply: RInt_Derive => x _.
  by rewrite /f; auto_derive.
apply:  (continuous_ext (fun x => 4 / (1 + (x - 1)^2))).
 by move=> z; rewrite Derive_4atan.
apply:ex_derive_continuous; auto_derive.
by have := x2p1 x;tlra.
Qed.

(* The Plouffe formula *)
Lemma Plouffe_PI  : 
  PI = 4 * (Sk 1) - 2 * (Sk 4) - (Sk 5) -(Sk 6).
Proof.
rewrite  !Sk_Rint; tlia.
have Rth1 := @RInt_scal R_CompleteNormedModule.
rewrite /scal /= /mult /= in Rth1.
have Rth2 := @RInt_minus R_CompleteNormedModule.
  rewrite /minus /= /plus [AbelianGroup.plus _ _ ]/= in Rth2.
  rewrite /opp [AbelianGroup.opp _ _]/= in Rth2.
rewrite /Rminus -!{}Rth1 -?Rth2;
    repeat  (apply: ex_RInt_Sk || (apply: ex_RInt_minus || apply: ex_RInt_scal 
          || apply: ex_RInt_opp)).
(* integrating by variable substitution *)
pose g x := /sqrt 2 * x + 0.
replace 0 with (g 0) by (rewrite /g; ring).
replace (/sqrt 2) with (g 1); last by rewrite /g; lra.
have Rth1 := @RInt_comp_lin R_CompleteNormedModule.
rewrite /scal /= /mult /= in Rth1.
rewrite -{}Rth1; last first.
  have hm1 : 0 < / sqrt 2 < 1.
    split; first by apply/Rinv_0_lt_compat/sqrt_lt_R0; lra.
    have hsqrt2m1_pos := sqrt2m1_pos.
    by rewrite -[X in _ < X]Rinv_1; apply: Rinv_1_lt_contravar; lra.
  have H x : 0 <= x < 1 -> 1 - x ^ 8 <> 0.
    move=> Hx.
    suff : 0 <= x ^ 8 < 1 by lra.
    by apply: pow_lt_1_compat; tlia.
  repeat (apply: ex_RInt_minus || apply: ex_RInt_scal 
          || apply: ex_RInt_opp);
  apply: ex_RInt_continuous => x hx;
  apply:ex_derive_continuous; auto_derive; apply H;
  rewrite !(Rmin_left, Rmax_right) in hx; tlra.
rewrite (RInt_ext _ (fun y => (16 * (y -1)) / (y^4 -2 * y^3 + 4* y -4))); last first.
  move=> x ; rewrite Rmin_left ?Rmax_right ; tlra=>-[hx0 hx1].
  have hsqrt20 := sqrt2_neq_0.
  rewrite ![(_ - _)%nat]/= Rplus_0_r pow_O pow_1 !Rpow_mult_distr -!Rinv_pow //.
  set s2 := sqrt 2.
  have xm1pos := (pow2_ge_0 (x -1)).
  have hxm1 : 1 + (x -1)^2 <> 0 by apply/not_eq_sym/Rlt_not_eq; lra.
  have hx2m2 : x^2 -2 <>0.
    apply/Rlt_not_eq.
    have hsqrt2m1_pos := sqrt2m1_pos.
    suff : 0 < 2 - x^2 by lra.
    by apply/btwnsqrt2; tlra.
  have hx4 : x^4 -2 * x^3 + 4*x - 4 <> 0.
    have -> : x ^ 4 - 2 * x ^ 3 + 4 * x - 4 = (1+ (x - 1)^2) *( x^2 -2) by field.
    by apply: Rmult_integral_contrapositive.
  have hx8: (sqrt 2) ^ 8 - x ^ 8 <> 0.
    apply/not_eq_sym/Rlt_not_eq/Rlt_Rminus.
    have hsqrt2m1_pos:=  sqrt2m1_pos.
    apply:(Rle_lt_trans _  1); tlra.
      have -> : 1 = 1^8 by lra.
      by apply: pow_incr; lra.
    by apply:Rlt_pow_R1 ; tlra; tlia.
  field_simplify => //.
  have ->: s2 ^9  = 16 * s2.
    replace 9%nat  with ( 2* 4  +1)%nat by lia.
    by rewrite pow_add pow_1 pow_sqr sqrt_sqrt; lra.
  have h16s2:  16 * s2 - s2 * x ^ 8 <> 0.
    have -> : 16 * s2 - s2 * x ^ 8 = s2 * (16 - x^8) by ring.
    have -> : 16 = sqrt 2 ^ 8.
      have -> : (8 = 2 * 4)%nat by [].
      by rewrite pow_sqr  ?sqrt_sqrt; lra.
    by apply: Rmult_integral_contrapositive; split;  tlra.
  by apply: Rminus_diag_uniq; field.
rewrite (RInt_ext _ (fun x =>  (4 - 4*x)/(x^2 -2* x +2) + (4 / (1 + (x -1)^2) + ((4* x)/(x^2 -2))))); last first.
  move=> x ; rewrite Rmin_left ?Rmax_right ; tlra=>-[hx0 hx1].
  have ->: (1 + (x - 1) ^ 2) = (x ^ 2 - 2 * x + 2) by ring.
  have -> : (x ^ 4 - 2 * x ^ 3 + 4 * x - 4) = (x ^ 2 - 2 * x + 2) * (x ^ 2 - 2) by ring.
  apply: Rminus_diag_uniq; field.
  have xm1pos := (pow2_ge_0 (x -1)).
  have hxm1 : 1 + (x -1)^2 <> 0 by apply/not_eq_sym/Rlt_not_eq; lra.
  have hx2m2 : x^2 -2 <>0.
    apply/Rlt_not_eq.
    have hsqrt2m1_pos := sqrt2m1_pos.
    suff : 0 < 2 - x^2 by lra.
    by apply/btwnsqrt2; tlra.
  move:hxm1.
  by have <-:  1 + (x - 1) ^ 2 = x^2 -2 *x +2 by ring.
have ex_RI1: ex_RInt (fun y : R => / (1 + (y - 1) ^ 2)) 0 1.
  apply: ex_RInt_continuous => x _.
  apply:ex_derive_continuous; auto_derive.
  by have := x2p1 x;tlra.
have exRI2:  ex_RInt (fun x : R => 4 * x / (x ^ 2 - 2)) 0 1.
  apply: ex_RInt_continuous => x hx.
  apply:ex_derive_continuous; auto_derive.
  rewrite !(Rmin_left, Rmax_right) in hx; tlra.
  have Hx := (x_between x hx).
  have hx2 := ( btwnsqrt2 x Hx).
  by lra.
have exRI3:  ex_RInt (fun x : R => (4 - 4 * x) / (x ^ 2 - 2 * x + 2)) 0 1.  
  apply: ex_RInt_continuous => x _;  apply:ex_derive_continuous; auto_derive.
  by have hx := x2p1 x; lra.
rewrite !RInt_plus; (repeat  (apply: ex_RInt_plus|| apply: ex_RInt_scal))=> //.
rewrite RInt_Spart1 RInt_Spart2 RInt_Spart3.
rewrite /plus [AbelianGroup.plus _ _ ]/=.
by lra.
Qed.
End Plouffe.
