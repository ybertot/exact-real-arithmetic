(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

Require Import definition. 
Require Import Tactiques.
Require Import Rbase_doubles_inegalites.

Axiom B_sup_4 : 4 <= B.

Definition msd_prop (xc : Reelc) (msdx : Z) : Prop :=
    (forall n : Z, (n < msdx)%Z -> (Z.abs (xc n) <= 1)%Z) /\
    (Z.abs (xc msdx) > 1)%Z.
  
Lemma msd_c_bis :
 forall (xc : Reelc) (msdx m : Z),
 msd_prop xc msdx ->
 (forall n : Z, (n < m)%Z -> (Z.abs (xc n) <= 1)%Z) /\ (Z.abs (xc m) > 1)%Z ->
 msdx = m. 
Proof.
intros xc msdx m msdx_p (H1, H2).
unfold msd_prop in msdx_p.
assert (cmp : (m < msdx)%Z \/ m = msdx \/ (msdx < m)%Z) by omega.
intuition.
generalize (H m H3); omega.
generalize (H1 (msdx) H4); intro; omega.
Qed.

(* TODO: remove this lemma. *)
Lemma msd_c_ter : forall (xc : Reelc) msdx, 
  msd_prop xc msdx ->
  (1 < Z.abs (xc msdx))%Z.
Proof.
intros xc msdx [h1 h2]; apply Z.gt_lt; auto.
Qed.


Lemma msd_c_4 : forall (xc : Reelc) msdx,
  msd_prop xc msdx ->
  (IZR (Z.abs (xc (Z.pred msdx))) <= 1)%R.
Proof.
intros xc msdx [h1 h2].
RingReplace 1%R (IZR (Z.succ 0)); apply IZR_le.
generalize (h1 (Z.pred msdx)); auto with zarith.
Qed.


Lemma xc_nul :
 forall (x : R) (xc : Reelc) (n : Z),
 x = 0%R -> encadrement xc x -> xc n = 0%Z.
Proof.
intros.
generalize (H0 n); clear H0.
rewrite H.
RingReplace (0 * B_powerRZ n)%R 0%R.
intro.
apply one_IZR_lt1.
apply Rlt_2_minus_r with (IZR (xc n)).
RingReplace (-1 - IZR (xc n))%R (- (IZR (xc n) + 1))%R.
RingReplace (1 - IZR (xc n))%R (- (IZR (xc n) - 1))%R.
RingReplace (IZR (xc n) - IZR (xc n))%R (-0)%R.
apply Rlt_2_Ropp_r.
auto.
Qed.