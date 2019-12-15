(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

Require Export ZArith.
Require Export Zcomplements.
Require Export Reals.
Require Export Omega.
Require Export Arith.
Require Export ZArith.
Require Export Zmisc.
Require Export Zpower. 
Require Export Zmax.

Definition Reelc := Z -> Z.

Parameter B : nat.

Definition nearest_Int (x : R) : Z := up (x - / 2).

Definition gauss_z_sur_B (x : Z) := nearest_Int (IZR x / INR B).

Definition B_powerRZ (z : Z) : R := powerRZ (INR B) z.

Definition gauss_z_sur_B_pow x n := nearest_Int (IZR x / B_powerRZ n).

Lemma nearest_Int_correct (x : R) :
  (x - / 2 < IZR (nearest_Int x) <= x + / 2)%R.
Proof.
unfold nearest_Int.
destruct (archimed (x - / 2)) as [above below].
split;[now apply above | ].
apply (Rplus_le_reg_r (- (x - / 2))).
replace (x + (/ 2) + - (x - /2))%R with 1%R by field.
now apply below.
Qed.

Lemma gauss_correct :
   forall z : Z,
    (IZR z * / INR B - 1 * / 2 < IZR (gauss_z_sur_B z) <=
     IZR z * / INR B + 1 * / 2)%R.
Proof.
intros z.
rewrite !Rmult_1_l.
now apply nearest_Int_correct.
Qed.

Lemma gauss_correct_pow :
    forall z n : Z,
    (IZR z * / B_powerRZ n - 1 * / 2 < IZR (gauss_z_sur_B_pow z n) <=
     IZR z * / B_powerRZ n + 1 * / 2)%R.
Proof.
intros z n.
rewrite !Rmult_1_l.
apply nearest_Int_correct.
Qed.

Definition B_powerZ (z : Z) : Z := (Z_of_nat B ^ z)%Z.

Definition encadrement (xc : Reelc) (x : R) : Prop :=
  forall n : Z, (IZR (xc n) - 1 < x * B_powerRZ n < IZR (xc n) + 1)%R.

Definition encadrement_bis (p n : Z) (x : R) : Prop :=
  (IZR p - 1 < x * B_powerRZ n < IZR p + 1)%R.

Parameter le_nat : R -> nat.

Definition oppose_reelc (xc : Reelc) : Reelc := fun n : Z => (- xc n)%Z.

Definition absolue_reelc (xc : Reelc) : Reelc := fun n : Z => Z.abs (xc n).

Definition addition_reelc (xc yc : Reelc) : Reelc :=
  fun n : Z => gauss_z_sur_B (xc (n + 1)%Z + yc (n + 1)%Z).

Fixpoint compute_msd_N (xc : Reelc) (n current stop : Z) (fuel : nat) : Z :=
  match fuel with
  | 0 => stop
  | S fuel' =>
    let Vxc := xc current in
    if (1 <? Z.abs Vxc)%Z then
      current
    else
      compute_msd_N xc n (current + 1)%Z stop fuel'
  end.

(* This a rather naive way to compute the logarithm of x relative to B,
  when B is a power of 2, there is a much more efficient way to do so. *)
Fixpoint ZlogBr (x : Z) (fuel : nat) (candidate : Z) :=
  match fuel with
  | 0 => (candidate - 1)%Z
  | S p =>
    if (x <? (Z.of_nat B) ^ candidate)%Z then
      (candidate - 1)%Z
    else
      (ZlogBr x p (candidate + 1))%Z
  end. 

Definition ZlogB (x : Z) :=
  ZlogBr x (Z.to_nat x) 0.
  
Definition compute_msd (xc : Reelc) (n stop : Z) : Z :=
  if (1 <? Z.abs (xc 0%Z))%Z then
    let v := ZlogB (Z.abs (xc 0%Z)) in
    if (1 <? Z.abs (xc v))%Z then v else (v - 1)
  else
    compute_msd_N xc n 0 stop (Z.to_nat (n +3 - Z.quot2 n)).

(* If the most significant digit (msd) of x is not yet known, this function
   will attempt to compute it with a limited amount of recursive calls
   (as described in compute_pmax_N). 
   If this computation attempt succeeds, the value should be stored for xc,
   but the side-effect infrastructure required for this is not part of
   the current model.

   This limited computation of the most significant digit is described in
   page 25 of V. Ménissier-Morain article in JLAP, Vol. 64 (2005), page 24
*)
Definition p_max (xc : Reelc) (msd_x : option Z) (n : Z) : Z :=
  let stop := Z.quot2 (n + 2) in
  let v_msd :=
    match msd_x with
    | Some v => v
    | None => compute_msd_N xc n 0 stop (Z.to_nat (n + 3 -Z.quot2 n))
    end in
    Zmax (n - v_msd + 3) stop.

Definition multiplication_reelc (xc yc : Reelc)
  (msd_x msd_y : option Z): Reelc :=
  fun n : Z =>
  (Z.sgn (xc (p_max yc msd_y n)) * Z.sgn (yc (p_max xc msd_x n)) *
   gauss_z_sur_B_pow (1 + Z.abs (xc (p_max yc msd_y n) * yc (p_max xc msd_x n)))
     (p_max yc msd_y n + p_max xc msd_x n - n))%Z.

Require Import Zdiv.

Definition Zdiv_sup (a b : Z) :=
  match Z_zerop (a mod b) with
  | left _ => (a / b)%Z
  | right _ => Z.succ (a / b)
  end.

(* In the original paper, msd is described as a function that may not
  terminate when the argument xc represents zero.  Here, we prefer
  to describe the inverse_reelc function as taking as extra argument
  which expresses the order of magnitude of the input.  It is actually
  a witness that the input is non-zero. *)
Definition inverse_reelc (xc : Reelc) (msdx : Z) : Reelc :=
  fun n : Z =>
  match Z_le_gt_dec n (- msdx) with
  | left _ => 0%Z
  | right _ =>
     (B_powerZ (2 * n + 2 * msdx + 1) / (xc (n + 2 * msdx + 1) + 1) + 1)%Z
  end.    

Definition racine_reelc (xc : Reelc) : Reelc :=
  fun n : Z => Z.sqrt (xc (Z.succ (Z.succ 0) * n)%Z).
