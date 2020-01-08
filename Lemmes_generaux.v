(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

Require Import definition. 
Require Import Psatz.
Require Import Tactiques.
Require Import Axiomes.
Require Import Rbase_doubles_inegalites.
Require Import Rlog.
Require Import Zind_complements.
Require Import Rbase_inegalites.
Require Import powerRZ_complements.
Require Import Absolue.
Require Import Zpower.
Require Import Zarith_operations.
Require Import sg.
Require Import Lemmes.
Require Import Rind_complements.
Require Import Classical_Prop.

Lemma ZlogB_pos (b' x : Z) : (1 <= x)%Z -> (0 <= ZlogB b' x)%Z.
Proof.
unfold ZlogB.
intros xge1.
assert (xge1_nat : (1 <= Z.to_nat x)%nat).
  replace 1%nat with (Z.to_nat 1) by reflexivity.
  rewrite <- Z2Nat.inj_le; try lia.
enough (forall k, (0 <= k)%Z -> 0 <= ZlogBr b' x (Z.to_nat x) k)%Z.
  apply H; lia.
induction xge1_nat as [| m mge1 IH].
  simpl.
  intros k.
  case (Z.eq_dec k 0).
    intros k0; rewrite k0; intros _; simpl.
    destruct (Z.ltb_spec x 1); try lia.
  intros kn0; destruct (x <? b' ^ k)%Z; lia.
intros k.
simpl.
case (Z.eq_dec k 0).
  intros k0 kge0.
  rewrite k0; simpl.
  destruct (Z.ltb_spec x 1); try lia.
  apply IH; lia.
intros kn0 kge0.
destruct (x <? b' ^ k)%Z.
  lia.
apply IH.
lia.
Qed.

Lemma ZlogBr_correct (b' : Z) (x : Z)(n: nat) (candidate : Z) :
  (b' ^ (candidate - 1) <= x)%Z ->
  (x < b' ^ (candidate + Z.of_nat n))%Z ->
  (b' ^ (ZlogBr b' x n candidate) <= x < 
   b' ^ ((ZlogBr b' x n candidate) + 1))%Z.
Proof.
revert candidate.
induction n as [ | p].
  now intros c; simpl; rewrite Z.add_0_r, Z.sub_add; intros; split; auto.
intros c.
rewrite Nat2Z.inj_succ; simpl ZlogBr.
destruct (Z.ltb_spec x (b' ^ c)%Z) as [v1 | v2].
  intros it _; split; auto.
  now rewrite Z.sub_add; auto.
replace (c + (Z.succ (Z.of_nat p)))%Z with ((c + 1) + Z.of_nat p)%Z by ring.
intros _ it; apply IHp; auto.
now rewrite Z.add_simpl_r; auto.
Qed.

Lemma ZlogB_correct (b' x : Z) :
  (2 <= b')%Z ->
  (0 < x)%Z -> (b' ^ ZlogB b' x <= x < b' ^ (ZlogB b' x + 1))%Z.
Proof.
intros b'sup4 xgt0. (* ; assert (tmp := ZlogBr b' x (Z.to_nat x) 1). *)
apply ZlogBr_correct.
  now simpl; apply Z.lt_le_incl.
rewrite Z.add_0_l, Z2Nat.id; cycle 1.
  now apply Z.lt_le_incl.
replace x with ((x - 1) + 1)%Z by ring.
assert (xm1ge0 : (0 <= x - 1)%Z) by lia.
  generalize xm1ge0; apply
  (natlike_ind (fun u => (u + 1 < b' ^ (u + 1)))%Z).
  rewrite Z.add_0_l, Z.pow_1_r; lia.
intros y yge0 IH.
replace (Z.succ y) with (y + 1)%Z by ring.
rewrite (Z.pow_add_r); try lia.
rewrite Z.pow_1_r.
apply Z.le_lt_trans with ((y + 1) * 2)%Z; try lia.
rewrite (Zmult_comm (y + 1)), <- (Zmult_comm b').
apply Zmult_lt_compat2; lia.
Qed.

Lemma gauss_sur_B_O :
 forall z n : Z,
 0 < IZR (gauss_z_sur_B_pow z n) < 1 * / 2 -> gauss_z_sur_B_pow z n = 0%Z.

Proof.
intros.
apply one_IZR_lt1.
apply Rlt_2_trans with 0 (1 * / 2).
auto.
lra.
lra.
Qed.

Hint Resolve gauss_sur_B_O: real.


Definition pre_msd (x : R) := (- (Int_part (Rlog (Rabs x) (INR B))))%Z.

Definition msd (x : R) (xc : Reelc) :=
  if Z.eq_dec (Z.abs (xc (pre_msd x))) 1 then
    (pre_msd x + 1)%Z
  else
    pre_msd x.

Lemma B_INR_1 : forall B, (4<=B)%nat -> 1 <= INR B.
Proof.
  intros.
  replace 1 with (INR 1).
  apply le_INR; omega.
  reflexivity.
Qed.

Lemma B_INR_1' : forall B, (4<=B)%nat -> 1 < INR B.
Proof.
  intros.
  replace 1 with (INR 1).
  apply lt_INR; omega.
  reflexivity.
Qed.

Lemma powerRZ_Int_part_Rabs : forall x:R,
    x<>0 ->
    powerRZ (INR B) (Int_part (Rlog (Rabs x) (INR B))) <= Rabs x.
Proof.
  intros.
  rewrite powerRZ_Rpower.
  apply Rle_trans with (Rpower (INR B) ( (Rlog (Rabs x) (INR B)))).
  apply Rle_Rpower.
  apply B_INR_1; apply B_sup_4.
  destruct (base_Int_part (Rlog (Rabs x) (INR B))) as [b1 b2]; assumption.
  unfold Rpower, Rlog.
  replace (ln (Rabs x) / ln (INR B) * ln (INR B)) with (ln (Rabs x)).
  rewrite exp_ln.
  apply Rle_refl.
  apply Rabs_pos_lt; assumption.
  field.
  rewrite <- ln_1.
  apply Rgt_not_eq.
  apply ln_increasing.
  apply Rlt_0_1.
  apply B_INR_1'; apply B_sup_4.
  apply INR_B_non_nul.
Qed.

Lemma powerRZ_Int_part_Rabs2 : forall x:R,
    x<>0 ->
    Rabs x < powerRZ (INR B) (Int_part (Rlog (Rabs x) (INR B)) + Z.succ 0).
Proof.
  intros.
  rewrite powerRZ_Rpower.
  apply Rle_lt_trans with (Rpower (INR B) ( (Rlog (Rabs x) (INR B)))).
  unfold Rpower, Rlog.
  replace (ln (Rabs x) / ln (INR B) * ln (INR B)) with (ln (Rabs x)).
  rewrite exp_ln.
  apply Rle_refl.
  apply Rabs_pos_lt; assumption.
  field.
  rewrite <- ln_1.
  apply Rgt_not_eq.
  apply ln_increasing.
  apply Rlt_0_1.
  apply B_INR_1'; apply B_sup_4.
  apply Rpower_lt.
  apply B_INR_1'; apply B_sup_4.
  destruct (base_Int_part (Rlog (Rabs x) (INR B))) as [b1 b2].
  rewrite plus_IZR.
  apply Rgt_lt in b2.
  apply Rplus_lt_reg_l with (- 1 - Rlog (Rabs x) (INR B)).
  simpl;ring_simplify.
  rewrite Rplus_comm.
  assumption.
  apply INR_B_non_nul.
Qed.

(*Probleme :reecrire toutes les ingalites dans R *)

Lemma msd_prop1 :
 forall (x : R) (xc : Reelc) (msdx : Z),
 x <> 0 ->
 encadrement xc x ->
 msd_prop xc msdx ->
 {msdx = (- Int_part (Rlog (Rabs x) (INR B)))%Z} +
 {msdx = (- Int_part (Rlog (Rabs x) (INR B)) + 1)%Z}.  
Proof.
intros x xc msdx H H0 msd_p.
cut
 (forall n : Z,
  (n < - Int_part (Rlog (Rabs x) (INR B)))%Z -> (Z.abs (xc n) <= 1)%Z).
intro.
cut
 ({(1 < Z.abs (xc (- Int_part (Rlog (Rabs x) (INR B)))))%Z} +
  {1%Z = Z.abs (xc (- Int_part (Rlog (Rabs x) (INR B)))%Z)}).
intro.
elim H2.
intro.
left.
eapply (msd_c_bis xc msdx (- Int_part (Rlog (Rabs x) (INR B))) msd_p).
split.
apply H1.
auto with zarith.
intros.
right.
eapply (msd_c_bis xc msdx (- Int_part (Rlog (Rabs x) (INR B)) + 1) msd_p).
split.
intros.
pattern n in |- *.
apply Zind_plus_1 with (- Int_part (Rlog (Rabs x) (INR B)))%Z; auto.
intro.
rewrite H4; auto.
rewrite b; auto with zarith.
apply Z.lt_gt; apply Z.lt_le_trans with (Z_of_nat B).
idtac.
RingReplace 1%Z (Z_of_nat 1); apply Znat.inj_lt.
generalize B_sup_4; omega.
apply Zlt_succ_le.
apply lt_IZR; rewrite <- INR_IZR_INZ.
unfold Z.succ in |- *; rewrite plus_IZR; simpl in |- *.
apply
 Rle_lt_trans
  with
    (Rabs x * powerRZ (INR B) (- Int_part (Rlog (Rabs x) (INR B)) + Z.succ 0)).
rewrite Rmult_comm;
 apply
  Rmult_le_reg_l
   with (/ powerRZ (INR B) (- Int_part (Rlog (Rabs x) (INR B)) + Z.succ 0)).
apply Rinv_0_lt_compat; apply powerRZ_lt.
apply lt_INR_0; generalize B_sup_4; omega.
rewrite <- Rmult_assoc.
replace
 (/ powerRZ (INR B) (- Int_part (Rlog (Rabs x) (INR B)) + Z.succ 0) *
  powerRZ (INR B) (- Int_part (Rlog (Rabs x) (INR B)) + Z.succ 0)) with 1;
 [ rewrite Rmult_1_l
 | apply Rinv_l_sym; apply Rgt_not_eq; apply Rlt_gt; apply powerRZ_lt;
    apply lt_INR_0; generalize B_sup_4; omega ].
replace (/ powerRZ (INR B) (- Int_part (Rlog (Rabs x) (INR B)) + Z.succ 0))
 with (powerRZ (INR B) (- (- Int_part (Rlog (Rabs x) (INR B)) + Z.succ 0)));
 [ idtac
 | symmetry  in |- *; apply Rinv_powerRZ; apply Rgt_not_eq; apply Rlt_gt;
    apply lt_INR_0; generalize B_sup_4; omega ].
replace
 (powerRZ (INR B) (- (- Int_part (Rlog (Rabs x) (INR B)) + Z.succ 0)) * INR B)
 with
 (powerRZ (INR B) (Z.succ (- (- Int_part (Rlog (Rabs x) (INR B)) + Z.succ 0))));
 [ idtac
 | apply powerRZ_Zs; apply Rgt_not_eq; apply Rlt_gt; apply lt_INR_0;
    generalize B_sup_4; omega ].
rewrite Zopp_plus_distr; rewrite Zplus_comm; rewrite <- Zplus_succ_l;
 rewrite Z.opp_involutive; simpl in |- *.
apply powerRZ_Int_part_Rabs; assumption.
cut (encadrement (absolue_reelc xc) (Rabs x)).
unfold encadrement in |- *.
intro.
generalize (H3 (- Int_part (Rlog (Rabs x) (INR B)) + Z.succ 0)%Z).
intro.
elim H4.
unfold B_powerRZ in |- *; intros; auto.
apply absolue_correct; auto.
apply Z_le_lt_eq_dec.
apply Zlt_succ_le.
apply lt_IZR.
apply
 Rle_lt_trans
  with (Rabs x * powerRZ (INR B) (- Int_part (Rlog (Rabs x) (INR B)))).
rewrite Rmult_comm;
 apply
  Rmult_le_reg_l
   with (/ powerRZ (INR B) (- Int_part (Rlog (Rabs x) (INR B)))).
apply Rinv_0_lt_compat; apply powerRZ_lt.
apply lt_INR_0; generalize B_sup_4; omega.
rewrite <- Rmult_assoc.
replace
 (/ powerRZ (INR B) (- Int_part (Rlog (Rabs x) (INR B))) *
  powerRZ (INR B) (- Int_part (Rlog (Rabs x) (INR B)))) with 1;
 [ rewrite Rmult_1_l
 | apply Rinv_l_sym; apply Rgt_not_eq; apply Rlt_gt; apply powerRZ_lt;
    apply lt_INR_0; generalize B_sup_4; omega ].
replace (/ powerRZ (INR B) (- Int_part (Rlog (Rabs x) (INR B)))) with
 (powerRZ (INR B) (- - Int_part (Rlog (Rabs x) (INR B))));
 [ idtac
 | symmetry  in |- *; apply Rinv_powerRZ; apply Rgt_not_eq; apply Rlt_gt;
    apply lt_INR_0; generalize B_sup_4; omega ].
rewrite Z.opp_involutive; simpl in |- *; rewrite Rmult_1_r.
apply powerRZ_Int_part_Rabs; assumption.
unfold Z.succ in |- *; rewrite plus_IZR.
cut (encadrement (absolue_reelc xc) (Rabs x)).
unfold encadrement in |- *.
intro.
generalize (H2 (- Int_part (Rlog (Rabs x) (INR B)))%Z); clear H2. 
intro.
elim H2.
unfold B_powerRZ in |- *; intros; auto.
apply absolue_correct; auto.
intros.
replace (Z.abs (xc n)) with (Z.succ (Z.abs (xc n) - 1));
 [ apply Zlt_le_succ | unfold Z.succ in |- *; simpl in |- *; ring ].
apply lt_IZR.
rewrite <- Z_R_minus.
apply
 Rlt_le_trans
  with (powerRZ (INR B) (n + Int_part (Rlog (Rabs x) (INR B)) + Z.succ 0)).
apply Rlt_trans with (Rabs x * powerRZ (INR B) n). 
cut (encadrement (absolue_reelc xc) (Rabs x));
 [ unfold encadrement in |- *; unfold B_powerRZ in |- *; intro
 | apply absolue_correct; auto ].
generalize (H2 n); clear H2.
intros.
elim H2; intro; auto.
replace (powerRZ (INR B) (n + Int_part (Rlog (Rabs x) (INR B)) + Z.succ 0))
 with
 (powerRZ (INR B) (Int_part (Rlog (Rabs x) (INR B)) + Z.succ 0) *
  powerRZ (INR B) n).
apply Rmult_lt_compat_r;
 [ apply powerRZ_lt; apply lt_INR_0; generalize B_sup_4; omega | idtac ].
apply powerRZ_Int_part_Rabs2; assumption.
rewrite <- Zplus_assoc; rewrite Rmult_comm; symmetry  in |- *;
 apply powerRZ_add.
apply Rgt_not_eq; apply Rlt_gt; apply lt_INR_0; generalize B_sup_4; omega.
replace (IZR 1) with (powerRZ (INR B) 0).
apply Rle_powerRZ.
apply Rlt_le.
RingReplace 1 (INR 1).
apply lt_INR; generalize B_sup_4; omega.
rewrite <- Zplus_succ_r; apply Zgt_le_succ; rewrite <- Zplus_0_r_reverse.
apply Z.lt_gt; auto with zarith.
apply powerRZ_O.
Qed.

Lemma msd_prop_unique x xc v1 v2 :
  x <> 0 ->
  encadrement xc x ->
  msd_prop xc v1 -> msd_prop xc v2 -> v1 = v2.
Proof.
intros xn0 xcx mp1 mp2.
generalize mp1; intros mp1'; generalize mp2; intros mp2'.
destruct mp1 as [p1 p2]; destruct mp2 as [p3 p4].
destruct (msd_prop1 x xc v1 xn0 xcx mp1') as [atl | atl1].
  destruct (msd_prop1 x xc v2 xn0 xcx mp2') as [atl' | atl1'].
    now rewrite atl, atl'.
  enough (Z.abs (xc v1) <= 1)%Z by lia.
  now apply p3; lia.
destruct (msd_prop1 x xc v2 xn0 xcx mp2') as [atl' | atl1'].
  enough (Z.abs (xc v2) <= 1)%Z by lia.
  now apply p1; lia.
now rewrite atl1, atl1'.
Qed.

Lemma trial xc : encadrement xc (1/99) ->
  B = 10%nat ->
  msd_prop xc 2 \/ msd_prop xc 3.
Proof.
intros enc.
intros B10.
case (Z.eq_dec (xc 2%Z) 1).
  right.
  split.
    intros n; destruct (enc n) as [enc1 enc2].
    intros n3.
    rewrite Z.abs_le; split; apply le_IZR.
      rewrite opp_IZR; enough (0 <= IZR (xc n) + 1) by lra.
      apply Rlt_le; apply Rle_lt_trans with (2 := enc2).
      enough (0 <= B_powerRZ n) by lra.
      now apply powerRZ_le, INR_B_non_nul.
    apply IZR_le, Zlt_succ_le; unfold Z.succ.
    enough (xc n - 1 < 1)%Z by lia.
    apply lt_IZR; rewrite minus_IZR.
    destruct (Z.eq_dec n 2) as [nis2 | nn2].
      rewrite nis2, e; lra.
    assert (n1 : (n < 2)%Z) by lia.
    apply Rlt_trans with (1 := enc1).
    rewrite <- Z.le_succ_l in n3.
    apply Rle_lt_trans with (1/99 * 10).
      apply Rmult_le_compat_l;[lra | ].
      replace 10 with (B_powerRZ 1);
        [|unfold B_powerRZ; rewrite B10;simpl; lra].
      apply Rle_powerRZ;[ | lia].
      rewrite B10; simpl; lra.
    lra.
  destruct (enc 3%Z) as [enc1 enc2].
  assert (step : 1/99 * B_powerRZ 3 - 1 < IZR (xc 3%Z)) by lra.
  assert (0 <= xc 3)%Z.
    apply le_IZR.
    apply Rlt_le; apply Rle_lt_trans with (2 := step).
    unfold B_powerRZ; rewrite B10; simpl; lra.
    rewrite Z.abs_eq; auto.
    apply Z.lt_gt, lt_IZR; apply Rle_lt_trans with (2:= step).
  unfold B_powerRZ; rewrite B10; simpl; lra.
intros xc2n1; left.
split.
  intros n n2; destruct (enc n) as [enc1 enc2].
    rewrite Z.abs_le; split; apply le_IZR.
    rewrite opp_IZR; enough (0 <= IZR (xc n) + 1) by lra.
    apply Rlt_le; apply Rle_lt_trans with (2 := enc2).
      enough (0 <= B_powerRZ n) by lra.
      now apply powerRZ_le, INR_B_non_nul.
  apply IZR_le, Zlt_succ_le; unfold Z.succ.
  enough (xc n - 1 < 1)%Z by lia.
  apply lt_IZR; rewrite minus_IZR.
  apply Rlt_trans with (1 := enc1).
  apply Rle_lt_trans with (1 / 99 * B_powerRZ 1).
     apply Rmult_le_compat_l;[lra |].
     apply Rle_powerRZ;[rewrite B10; simpl; lra | lia].
  unfold B_powerRZ; rewrite B10; simpl; lra.
destruct (enc 2%Z) as [enc1 enc2].
assert (step : 1/99 * B_powerRZ 2 - 1 < IZR(xc 2%Z)) by lra.
assert (0 < 1/99 * B_powerRZ 2 - 1).
  unfold B_powerRZ; rewrite B10; simpl; lra.
assert (0 <= xc 2)%Z.
  apply le_IZR; lra.
rewrite Z.abs_eq; try lia.
assert (xc 2%Z <> 0%Z).
  intros abs; revert enc2; rewrite abs, Rplus_0_l.
  unfold B_powerRZ; rewrite B10; simpl; lra.
lia.
Qed.

Lemma trial2 : B = 10%nat -> -2 < Rlog (1/99) (INR B) < -1.
Proof.
intros B10.
assert (ln10pos : 0 < ln 10).
  now rewrite <- ln_1; apply ln_increasing; lra.
unfold Rlog, Rdiv; rewrite Rmult_1_l.
replace (INR B) with 10 by (rewrite B10; simpl; lra).
replace (-2) with (ln(/100) * /ln 10).
  replace (-1) with (ln(/10) * /ln 10).
    split.
      apply Rmult_lt_compat_r.
        now apply Rinv_0_lt_compat.
      now apply ln_increasing; lra.
    apply Rmult_lt_compat_r.
      now apply Rinv_0_lt_compat.
    now apply ln_increasing; lra.
  rewrite ln_Rinv;[ | lra].
  now field; apply Rgt_not_eq.
replace 100 with (10 * 10) by ring.
rewrite ln_Rinv; try lra.
rewrite ln_mult; try lra.
now field; apply Rgt_not_eq.
Qed.

Lemma trial3 : B = 10%nat -> pre_msd (1 /99) = 2%Z.
Proof.
intros B10.
unfold pre_msd, Int_part.
assert (main : (-2 + 1)%Z = up (Rlog (Rabs (1 /99)) (INR B))).
  apply up_tech.
    now destruct (trial2 B10); rewrite Rabs_pos_eq; lra.
  rewrite plus_IZR, Rabs_pos_eq; destruct (trial2 B10); lra.
lia.
Qed.

Lemma trial4 xc : B = 10%nat -> encadrement xc (1 / 99) ->
  msd_prop xc (msd (1 / 99) xc).
Proof.
intros B10 enc; assert (tmp := trial xc enc B10).
unfold msd.
destruct (Z.eq_dec (Z.abs (xc (pre_msd (1/99)))) 1) as [eq1 | neq1].
  destruct tmp as [[any abs] | it].
    now revert eq1 abs; rewrite (trial3 B10); intros tmp; rewrite tmp; lia.
  now rewrite (trial3 B10).
assert (xn0 : 1 / 99 <> 0) by lra.
assert (vv := powerRZ_Int_part_Rabs2 _ xn0).
revert vv; rewrite <-(Z.opp_involutive (Int_part _)).
fold (pre_msd (1 / 99)); rewrite (trial3 B10) in neq1 |- *.
replace (- (2) + Z.succ 0)%Z with (-1)%Z by ring.
intros fact.
destruct tmp as [ it | abs]; auto.
destruct abs as [abs1 _].
assert (abs2 := abs1 2%Z eq_refl).
destruct (enc 2%Z) as [enc1 enc2].
assert (abp := Z.abs_nonneg (xc 2%Z)).  
assert (ab0 : Z.abs (xc 2%Z) = 0%Z) by lia.
rewrite Z.abs_0_iff in ab0.
unfold B_powerRZ in enc2; rewrite ab0, B10 in enc2; simpl in enc2; lra.
Qed.

Lemma msd_prop2 (x : R) (xc : Reelc) :
  x <> 0 -> encadrement xc x ->
  msd_prop xc (msd x xc).
Proof.
assert (INR B <> 0).
  now apply Rgt_not_eq, INR_B_non_nul.
assert (Bpgt0 : forall k, 0 < B_powerRZ k).
  now intros; apply powerRZ_lt, INR_B_non_nul.
revert x xc.
assert (main : forall x xc, x <> 0 -> x > 0 -> encadrement xc x ->
           msd_prop xc (msd x xc)).
  intros x xc xn0 xpos xcx.
  assert (xcp : forall k, (0 <= xc k)%Z).
    intros k; destruct (Z.lt_total (xc k) 0) as [neg | [at0 | pos]]; try lia.
    now apply Z.lt_gt, (sg_Zsgn_2 x) in neg; auto; lra.
  split.
    intros n nl; destruct (xcx n) as [enc1 enc2].
    rewrite Z.abs_le; split; apply le_IZR.
      rewrite opp_IZR.
      enough (0 <= IZR (xc n) + 1) by lra.
      apply Rlt_le.
      apply Rle_lt_trans with (2 := enc2).
      now apply Rmult_le_pos;[lra | apply Rlt_le; auto].
    assert (main : (n < pre_msd x)%Z -> IZR (xc n) <= 1).
      intros strong.
      enough (IZR (xc n) - 1 <= 0) by lra.
      rewrite <- minus_IZR; apply IZR_le.
      apply Zlt_succ_le; cbv [Z.succ Z.add].
      apply lt_IZR; rewrite minus_IZR.
      apply Rlt_le_trans with (1 := enc1).
      apply Rmult_le_reg_r with (/B_powerRZ n).
        apply Rinv_0_lt_compat.
        now apply powerRZ_lt; apply INR_B_non_nul.
      rewrite Rmult_assoc.
      rewrite Rinv_r;[|apply not_eq_sym, Rlt_not_eq, Bpgt0 ].
      rewrite Rmult_1_l, Rmult_1_r.
      assert (xrabs : x = Rabs x).
        now rewrite Rabs_pos_eq; lra.
      rewrite xrabs.    
      unfold B_powerRZ; rewrite Rinv_powerRZ;
      [|apply Rgt_not_eq, INR_B_non_nul].
      assert (strong' : (n <= pre_msd x - 1)%Z) by lia.
      apply Rle_trans with (1 := (Rlt_le _ _ (powerRZ_Int_part_Rabs2 _ xn0))).
      rewrite Z.le_lteq in strong'; destruct strong' as [it | valn].
        apply Rlt_le, powerRZ_croissance.
          replace 1 with (INR 1) by reflexivity; apply lt_INR.
          now apply le_trans with (2 := B_sup_4); lia.
        rewrite Z.opp_lt_mono, Z.opp_involutive.
        rewrite Z.opp_add_distr; fold (pre_msd x); exact it.
      now apply Req_le, f_equal; rewrite valn; unfold pre_msd; ring.
    revert nl; unfold msd; destruct (Z.eq_dec _ _) as [eq1 | neq1].
      rewrite Z.abs_eq in eq1; auto.
      intros cnd; assert (cnd' : (n < Z.succ (pre_msd x))%Z) by lia.
      rewrite Z.lt_succ_r, Z.le_lteq in cnd'.
      destruct cnd' as [usem | useq]; cycle 1.
        now rewrite useq, eq1; lra.
      now apply main.
    exact main.
  destruct (xcx (pre_msd x)) as [enc1 enc2].
  unfold msd; destruct (Z.eq_dec _ _) as [xcl1 | xcln1]. 
    rewrite !Z.abs_eq in xcl1 |- *; auto.
    destruct (xcx (pre_msd x + 1)%Z) as [enc3 enc4].
    enough (2 < xc (pre_msd x + 1) + 1)%Z by lia.
    apply lt_IZR; rewrite plus_IZR.
    apply Rle_lt_trans with (2 := enc4).
    assert (tmp1 : B_powerRZ (pre_msd x + 1) =
                 INR B * B_powerRZ (pre_msd x)).
      unfold B_powerRZ; rewrite powerRZ_add, Rmult_comm; auto.
      now rewrite powerRZ_1.
    assert (bpx1 : B_powerRZ (pre_msd x + 1) <> 0).
      now apply Rgt_not_eq, Bpgt0.
    assert (tmp2 : 2 = (2 / B_powerRZ (pre_msd x + 1))
                 * B_powerRZ (pre_msd x + 1)) by (field; auto).
    rewrite tmp2; clear tmp2.
    apply Rmult_le_compat_r;[now apply Rlt_le; auto |].
    generalize (powerRZ_Int_part_Rabs _ xn0); rewrite Rabs_pos_eq; try lra.
    intros tmp3; apply Rle_trans with (2 := tmp3); clear tmp3.
    rewrite tmp1; rewrite <- (Z.opp_involutive (Int_part _)).
    rewrite <- (Rabs_pos_eq x) at 2; fold (pre_msd x); try lra.
    replace (2 / ((INR B) * B_powerRZ (pre_msd x))) with
      ((2 /INR B) * /(B_powerRZ (pre_msd x))); cycle 1.
      now field; split; apply Rgt_not_eq;[apply Bpgt0 | apply INR_B_non_nul].
    unfold B_powerRZ; rewrite Rinv_powerRZ; try lra.
    rewrite <- (Rmult_1_l (powerRZ _ _)) at 2.
    apply Rmult_le_compat_r;[apply powerRZ_le, INR_B_non_nul |].
    apply Rmult_le_reg_r with (INR B);[apply INR_B_non_nul | ].
    unfold Rdiv; rewrite Rmult_1_l, Rmult_assoc, Rinv_l; auto.
    replace (2 * 1) with (INR 2) by (simpl; ring).
    now apply le_INR; assert (tmp:= B_sup_4); lia.
  generalize (powerRZ_Int_part_Rabs _ xn0); rewrite Rabs_pos_eq; try lra.
  intros tmp;
  apply (Rmult_le_compat_r
            (powerRZ (INR B) (- (Int_part (Rlog x (INR B)))))) in tmp; cycle 1.
    now apply powerRZ_le, INR_B_non_nul.
  rewrite <- powerRZ_add in tmp;[|apply Rgt_not_eq, INR_B_non_nul].
  rewrite Z.add_opp_diag_r, powerRZ_O in tmp.
  rewrite <- (Rabs_pos_eq _ (Rlt_le _ _ xpos)) in tmp at 2.
  fold (pre_msd x) in tmp.
  assert (tmp2 := Rle_lt_trans _ _ _ tmp enc2).
  assert (tmp3 : 0 < IZR (xc (pre_msd x))) by lra.
  apply lt_IZR in tmp3.
  rewrite Z.abs_eq; auto; lia.
intros x xc xn0 xcx.
assert (tmp := Rdichotomy _ _ xn0); rewrite or_comm in tmp.
destruct tmp as [xpos | xneg].
  now apply main.
assert (msd_prop (fun z => - (xc z))%Z
                      (msd (- (x)) (fun z => - (xc z))%Z)) as [oppP1 oppP2].
  apply main; auto; try lra.
  intros n; destruct (xcx n) as [enc1 enc2].
  split.
    rewrite opp_IZR; replace (- IZR (xc n) - 1) with (- (IZR (xc n) + 1))
      by ring.
    now rewrite <- Ropp_mult_distr_l; apply Ropp_lt_contravar.
  rewrite opp_IZR; replace (- (IZR (xc n)) + 1) with (- (IZR (xc n) - 1))
    by ring.
  now rewrite <- Ropp_mult_distr_l; apply Ropp_lt_contravar.
assert (pre_msd_same : pre_msd (-x) = pre_msd x).
  now unfold pre_msd; rewrite Rabs_Ropp.
assert (msd_same : msd (- x) (fun z => -xc z)%Z = msd x xc).
  now unfold msd; rewrite pre_msd_same, Z.abs_opp.
rewrite <- msd_same.
split.
  now intros n nlt; generalize (oppP1 n nlt); rewrite Z.abs_opp.
now revert oppP2; rewrite Z.abs_opp.
Qed.

Lemma msd_ax1 :
 forall x (xc : Reelc) k,
 x <> 0 ->
 encadrement xc x ->
 (1 < Z.abs (xc k))%Z -> (msd x xc <= k)%Z.
Proof.
intros x xc k xn0 xcx bnd.
destruct (msd_prop2 x xc xn0 xcx) as [it _].
destruct (Z_le_gt_dec (msd x xc) k) as [found | abs]; auto.
enough (Z.abs (xc k) <= 1)%Z by lia.
apply it; lia.
Qed.

Lemma msd_ax2 :
 forall (x : R) (xc yc : Reelc) (msdx : Z) (msdy : option Z) (n : Z),
 x <> 0 ->
 encadrement xc x ->
 msd_prop xc msdx ->
 (msdx <= p_max yc msdy n)%Z ->
 IZR (Z.abs (xc (p_max yc msdy n))) <=
   2 * INR B * B_powerRZ (p_max yc msdy n - msdx).
Proof.
intros x xc yc msdx msdy n H H0 msdp H1.
replace (2 * INR B * B_powerRZ (p_max yc msdy n - msdx)) with
 (IZR (Z.succ (Z.succ 0) * Z_of_nat B * Z_of_nat B ^ (p_max yc msdy n - msdx))).
apply IZR_le.
apply Zlt_succ_le.
apply lt_IZR.
unfold Z.succ in |- *; rewrite plus_IZR; rewrite mult_IZR.
replace (IZR (Z_of_nat B ^ (p_max yc msdy n - msdx))) with
 (B_powerRZ (p_max yc msdy n - msdx)).
unfold B_powerRZ in |- *.
rewrite mult_IZR.
rewrite <- INR_IZR_INZ; auto.
RingReplace (IZR (0 + 1 + 1)) 2.
RingReplace (IZR 1) 1.
rewrite Rmult_assoc.
replace (INR B * powerRZ (INR B) (p_max yc msdy n - msdx)) with
 (powerRZ (INR B) (Z.succ (p_max yc msdy n - msdx)));
 [ idtac
 | rewrite Rmult_comm; apply powerRZ_Zs; apply Rgt_not_eq; apply Rlt_gt;
    apply lt_INR_0; generalize B_sup_4; omega ].
apply Rlt_add_compatibility2.
apply Rmult_lt_reg_l with (powerRZ (INR B) (- Z.succ (p_max yc msdy n - msdx))).
apply powerRZ_lt; apply lt_INR_0; generalize B_sup_4; omega.
apply Rgt_lt; rewrite Rmult_comm; rewrite Rmult_assoc;
 apply Rlt_gt.
replace
 (powerRZ (INR B) (Z.succ (p_max yc msdy n - msdx)) *
  powerRZ (INR B) (- Z.succ (p_max yc msdy n - msdx))) with 1;
 [ rewrite Rmult_1_r | idtac ].
rewrite Rmult_comm;
 apply Rlt_le_trans with (Rabs x * powerRZ (INR B) (Z.pred msdx)).
replace (powerRZ (INR B) (- Z.succ (p_max yc msdy n - msdx))) with
 (powerRZ (INR B) (- p_max yc msdy n) * powerRZ (INR B) (Z.pred msdx));
 [ rewrite <- Rmult_assoc; apply Rmult_lt_compat_r | idtac ].
apply powerRZ_lt; apply lt_INR_0; generalize B_sup_4; omega.
apply Rmult_lt_reg_l with (powerRZ (INR B) (p_max yc msdy n)).
apply powerRZ_lt; apply lt_INR_0; generalize B_sup_4; omega.
rewrite Rmult_comm; rewrite Rmult_assoc.
replace (powerRZ (INR B) (- p_max yc msdy n) * powerRZ (INR B) (p_max yc msdy n)) with
 1.
rewrite Rmult_1_r.
cut (encadrement (absolue_reelc xc) (Rabs x));
 [ intro | apply absolue_correct; auto ].
generalize H2.
unfold encadrement in |- *.
intro.
generalize (H3 (p_max yc msdy n)).
intro.
elim H4.
unfold B_powerRZ in |- *; intros; rewrite Rmult_comm; auto.
rewrite Rmult_comm; apply powerRZ_Zopp.
apply Rgt_not_eq; apply Rlt_gt; apply lt_INR_0; generalize B_sup_4; omega.
unfold Z.pred in |- *.
unfold Z.succ in |- *.
rewrite Zopp_plus_distr.
transitivity (powerRZ (INR B) (- p_max yc msdy n + (msdx + -1))).
symmetry  in |- *; apply powerRZ_add.
apply Rgt_not_eq; apply Rlt_gt; apply lt_INR_0; generalize B_sup_4; omega.
apply powerRZ_trivial.
ring.
apply Rle_trans with (IZR (Z.abs (xc (Z.pred msdx))) + 1).
apply Rlt_le.
cut (encadrement (absolue_reelc xc) (Rabs x));
 [ intro | apply absolue_correct; auto ].
generalize H2.
unfold encadrement in |- *.
intro.
generalize (H3 (Z.pred msdx)).
intro.
elim H4.
unfold B_powerRZ in |- *; intros; auto.
RingReplace 2 2; apply Rplus_le_compat_r.
apply msd_c_4; auto.
apply powerRZ_Zopp.
apply Rgt_not_eq; apply Rlt_gt; apply lt_INR_0; generalize B_sup_4; omega.
unfold B_powerRZ in |- *.
transitivity (IZR (Zpower_nat (Z_of_nat B) (Z.abs_nat (p_max yc msdy n - msdx)))).
rewrite INR_IZR_INZ.
symmetry  in |- *; apply Zpower_nat_powerRZ_absolu.
auto with zarith.
apply IZR_trivial.
unfold Z.abs_nat in |- *.
cut (p_max yc msdy n - msdx >= 0)%Z.
case (p_max yc msdy n - msdx)%Z; intro.
simpl in |- *.
auto with zarith.
simpl in |- *.
intro.
symmetry  in |- *; apply Zpower_pos_nat.
intro; absurd (Zneg p >= 0)%Z; auto with *.
omega.
do 2 rewrite mult_IZR.
unfold B_powerRZ in |- *.
rewrite INR_IZR_INZ.
RingReplace (IZR (Z.succ (Z.succ 0))) 2.
apply Rmult_eq_compat_l.
transitivity (IZR (Zpower_nat (Z_of_nat B) (Z.abs_nat (p_max yc msdy n - msdx)))).
2: apply Zpower_nat_powerRZ_absolu; auto with zarith.
apply IZR_trivial.
unfold Z.abs_nat in |- *.
cut (p_max yc msdy n - msdx >= 0)%Z.
case (p_max yc msdy n - msdx)%Z; intro.
simpl in |- *.
auto with zarith.
simpl in |- *.
intro.
apply Zpower_pos_nat.
intro; absurd (Zneg p >= 0)%Z; auto with *.
omega.
Qed.

(* TODO: check whether this lemma can be removed, as it is a direct
  application of msd_prop2. *)
Lemma msd_ax3 :
 forall (x : R)(xc : Reelc) k,
 x <> 0 ->
 encadrement xc x ->
 (k < msd x xc)%Z -> (Z.abs (xc k) <= 1)%Z.

Proof.
intros x xc k xn0 xcx km.
destruct (msd_prop2 x xc xn0 xcx) as [it _].
now apply it.
Qed.

Lemma encadrement_bis_prop1 :
 forall (p n : Z) (x : R),
 encadrement_bis p n (Rabs x) -> (0 <= p)%Z -> encadrement_bis (sg x * p) n x.

Proof.
intros.
pattern p in |- *.
apply Zind_le_ZERO; auto; intros.
generalize H.
rewrite <- H1; rewrite <- Zmult_0_r_reverse. 
unfold encadrement_bis in |- *.
simpl in |- *.
RingReplace (0 - 1) (-1); RingReplace (0 + 1) 1.
intro.
apply Rbase_doubles_inegalites.Rabsolu_def3.
rewrite Rabs_mult.
replace (Rabs (B_powerRZ n)) with (B_powerRZ n).
elim H2; auto.
symmetry  in |- *; apply Rabs_pos_eq.
unfold B_powerRZ in |- *.
apply powerRZ_le.
apply INR_B_non_nul.

unfold encadrement_bis in |- *.
pattern x in |- *.
apply Rind_complements.Rabsolu_not_0_ind; intros.
replace (sg x) with 1%Z; [ idtac | symmetry  in |- *; apply sg_pos; auto ].
rewrite Zmult_comm; rewrite Zmult_1_r.
replace x with (Rabs x).
auto.
apply Rabs_right.
apply Rgt_ge; auto.
replace (sg x) with (-1)%Z; [ idtac | symmetry  in |- *; apply sg_neg; auto ].
replace x with (- Rabs x).
rewrite Zmult_comm; rewrite <- Zopp_eq_mult_neg_1.
rewrite Ropp_Ropp_IZR.
RingReplace (- IZR p - 1) (- (IZR p + 1)).
RingReplace (- IZR p + 1) (- (IZR p - 1)).
rewrite Ropp_mult_distr_l_reverse.
apply Rlt_2_Ropp_r.
auto.
apply Rmult_eq_reg_l with (-1).
RingReplace (-1 * - Rabs x) (Rabs x).
RingReplace (-1 * x) (- x).
apply Rabs_left; auto.
apply Rlt_not_eq.
lra.
apply Rlt_gt.
apply Rmult_lt_reg_l with (B_powerRZ n).
unfold B_powerRZ in |- *; apply powerRZ_lt; apply INR_B_non_nul.
rewrite Rmult_0_r.
apply Rle_lt_trans with (IZR p - 1).
apply Rle_add_compatibility.
RingReplace (0 + 1) 1.
RingReplace 1 (IZR (Z.succ 0)).
apply IZR_le.
apply Zlt_le_succ.
auto.
unfold encadrement_bis in H.
rewrite Rmult_comm.
elim H.
auto.
Qed.



Lemma encadrement_bis_prop2 :
 forall (p n : Z) (x : R),
 x <> 0 ->
 encadrement_bis p n (/ Rabs x) ->
 (0 <= p)%Z -> encadrement_bis (sg x * p) n (/ x).

Proof.
intros.
pattern p in |- *.
apply Zind_le_ZERO; auto; intros.
generalize H0.
rewrite <- H2; rewrite <- Zmult_0_r_reverse. 
unfold encadrement_bis in |- *.
simpl in |- *.
RingReplace (0 - 1) (-1); RingReplace (0 + 1) 1.
intro.
apply Rbase_doubles_inegalites.Rabsolu_def3.
rewrite Rabs_mult.
replace (Rabs (B_powerRZ n)) with (B_powerRZ n).
replace (Rabs (/ x)) with (/ Rabs x).
elim H3; auto.
symmetry  in |- *; apply Rabs_Rinv.
auto.
symmetry  in |- *; apply Rabs_pos_eq.
unfold B_powerRZ in |- *.
apply powerRZ_le.
apply INR_B_non_nul.

unfold encadrement_bis in |- *.
pattern x in |- *.
apply Rind_complements.Rabsolu_not_0_ind; intros.
replace (sg x) with 1%Z; [ idtac | symmetry  in |- *; apply sg_pos; auto ].
rewrite Zmult_comm; rewrite Zmult_1_r.
replace x with (Rabs x).
auto.
apply Rabs_right.
apply Rgt_ge; auto.
replace (sg x) with (-1)%Z; [ idtac | symmetry  in |- *; apply sg_neg; auto ].
replace x with (- Rabs x).
rewrite Zmult_comm; rewrite <- Zopp_eq_mult_neg_1.
rewrite Ropp_Ropp_IZR.
RingReplace (- IZR p - 1) (- (IZR p + 1)).
RingReplace (- IZR p + 1) (- (IZR p - 1)).
rewrite <- Ropp_inv_permute.
rewrite Ropp_mult_distr_l_reverse.
apply Rlt_2_Ropp_r.
auto.
apply Rabs_no_R0.
auto.
apply Rmult_eq_reg_l with (-1).
RingReplace (-1 * - Rabs x) (Rabs x).
RingReplace (-1 * x) (- x).
apply Rabs_left; auto.
apply Rlt_not_eq.
lra.
apply Rlt_gt.
apply Rabs_pos_lt.
auto.
Qed.


Lemma Rabsolu_01 : forall x a : R, x <= a -> a < Rabs x -> x < 0.
Proof.
intros x a H.
unfold Rabs in |- *.
case (Rcase_abs x); intros.
auto.
lra.
Qed.

Hint Resolve Rabsolu_01: real.

Lemma Zsqrt_non_negative : forall z : Z, (0 <= z)%Z -> (0 <= Z.sqrt z)%Z.
Proof.
intros. apply Z.sqrt_nonneg.
Qed.

Lemma Zsqr_cond :
 forall z : Z,
 (0 <= z)%Z ->
 exists p : Z,
   (z = (p * p)%Z \/ z = (p * p + 1)%Z \/ z = (p * p - 1)%Z) \/
   (p * p < z < (p + 1) * (p + 1))%Z /\
   (p * p < z - 1 < (p + 1) * (p + 1))%Z /\
   (p * p < z + 1 < (p + 1) * (p + 1))%Z. 
Proof.
intros.
cut (z = 0%Z \/ z = 1%Z \/ (2 <= z)%Z); [ intuition | omega ].
exists 0%Z; omega.
exists 1%Z; omega.
generalize (Z.sqrt_spec z H); cbv zeta; intro.
generalize (Zsqrt_non_negative z H); intro.
set (r := Z.sqrt z) in *. unfold Z.succ in *.
cut
 ((z < r * r - 1)%Z \/
  z = (r * r - 1)%Z \/
  z = (r * r)%Z \/ z = (r * r + 1)%Z \/ (r * r + 1 < z)%Z);
 [ intuition | omega ].
exists (r - 1)%Z; right.
intuition; omega.
exists r; omega.
exists r; omega.
exists r; omega.
cut (z = ((r + 1) * (r + 1) - 1)%Z \/ (z < (r + 1) * (r + 1) - 1)%Z);
 [ intuition | omega ]. 
exists (r + 1)%Z; omega.
exists r; omega.
Qed.

Lemma Bexpos : forall n : Z,
B_powerRZ n > 0.

Proof.
  intros n.
unfold B_powerRZ.
apply powerRZ_lt.
apply INR_B_non_nul.
Qed.

Lemma inverseB_power : forall z : Z, (z >= 0)%Z ->
IZR(B_powerZ z)=B_powerRZ z.
Proof. intros z H. unfold B_powerRZ. unfold B_powerZ. 
unfold powerRZ.
destruct z; try solve[now case H| reflexivity].
now rewrite <- positive_nat_Z, <- pow_IZR, INR_IZR_INZ.
Qed. 

Lemma Bge4 : B_powerRZ 1 >= 4.
Proof. 
unfold B_powerRZ, powerRZ; rewrite pow_1; apply Rle_ge.
replace 4 with (INR 4) by (simpl; ring); apply le_INR, B_sup_4.
Qed.

Lemma nltmsd : forall (xc :Reelc) (msdx : Z) (n : Z),
  msd_prop xc msdx ->
  (n < msdx)%Z ->
  (absolue_reelc xc n <= 1)%Z.
Proof. intros xc msdx n msd_p H.  
unfold absolue_reelc. 
apply msd_p. assumption. Qed.


Lemma xcrangmsd : forall (xc :Reelc) (msdx : Z)(x : R),
encadrement xc x -> 
msd_prop xc msdx ->
(absolue_reelc xc msdx > 1)%Z.
Proof. intros xc msdx x H msd_p. unfold absolue_reelc.
apply msd_p. Qed.

Lemma msd_d:
  forall (xc :Reelc)(msdx : Z)
  (n :Z) (x : R),
      x <> 0 -> (n >= msdx)%Z ->
      encadrement xc x ->
      msd_prop xc msdx ->
      (B_powerZ (n - msdx) <= (Z.abs (xc n)) <= (2*(Z_of_nat B)+1)*(B_powerZ (n-msdx)))%Z.
Proof. 
intros xc msdx n x H1 H2 H3 msd_p. 
assert (Bn0 : INR B <> 0).
apply Rgt_not_eq, Rlt_gt, (lt_INR 0); generalize B_sup_4; lia.
  assert (H4 :{msdx = (- Int_part (Rlog (Rabs x) (INR B)))%Z} +
 {msdx = (- Int_part (Rlog (Rabs x) (INR B)) + 1)%Z}  ).
   apply (msd_prop1 _ _ _ H1 H3 msd_p).

 assert (H5:True) by (exact I).
assert (H6 : B_powerRZ (Int_part (Rlog (Rabs x) (INR B))) <= Rabs x).
apply powerRZ_Int_part_Rabs; assumption.
assert (H7 : Rabs x < B_powerRZ (Int_part (Rlog (Rabs x) (INR B)) + 1)).
apply powerRZ_Int_part_Rabs2; assumption.

assert (encdrementrabsx : B_powerRZ (Int_part (Rlog (Rabs x) (INR B))) <= Rabs x
< B_powerRZ (Int_part (Rlog (Rabs x) (INR B)) + 1)).
split. assumption. assumption. clear H6. clear H7.
assert (encadrementbis : forall n, encadrement_bis (absolue_reelc xc n) n (Rabs x)).
unfold encadrement_bis; apply absolue_correct; assumption.
assert (encadrementordrelog : encadrement_bis (absolue_reelc xc (- Int_part (Rlog (Rabs x) (INR B)))%Z) 
(- Int_part (Rlog (Rabs x) (INR B)))%Z (Rabs x) ).
apply encadrementbis. unfold encadrement_bis in encadrementordrelog.
inversion encadrementordrelog.
assert (H7 : ((Rabs x) * B_powerRZ (- Int_part (Rlog (Rabs x) (INR B)))) * /
 B_powerRZ (- Int_part (Rlog (Rabs x) (INR B))) < 
(IZR (absolue_reelc xc (- Int_part (Rlog (Rabs x) (INR B)))%Z) + 1) * 
/ B_powerRZ (- Int_part (Rlog (Rabs x) (INR B))) ).

apply Rmult_lt_compat_r. apply Rinv_0_lt_compat.
apply Rgt_lt. apply Bexpos. assumption. 
assert (H8 : (IZR (absolue_reelc xc (- Int_part (Rlog (Rabs x) (INR B)))%Z) - 1) *
 / B_powerRZ (- Int_part (Rlog (Rabs x) (INR B))) < 
((Rabs x) * B_powerRZ (- Int_part (Rlog (Rabs x) (INR B)))) * / B_powerRZ (- Int_part (Rlog (Rabs x) (INR B))) ).
apply Rmult_lt_compat_r. apply Rinv_0_lt_compat.
apply Rgt_lt. apply Bexpos. assumption. clear H0. 

unfold B_powerRZ in H7.

rewrite Rinv_powerRZ in H7.
replace ((Rabs x) * powerRZ (INR B) (- Int_part (Rlog (Rabs x) (INR B))) *
     powerRZ (INR B) (- - Int_part (Rlog (Rabs x) (INR B)))) with
(Rabs x) in H7.
replace ((- - Int_part (Rlog (Rabs x) (INR B)))%Z) with
((Int_part (Rlog (Rabs x) (INR B)))) in H7.
replace ((Rabs x) * B_powerRZ (- Int_part (Rlog (Rabs x) (INR B))) * 
/ B_powerRZ (- Int_part (Rlog (Rabs x) (INR B))))
with (Rabs x) in H8.
replace (powerRZ (INR B) (Int_part (Rlog (Rabs x) (INR B)))) with
(/ B_powerRZ (- Int_part (Rlog (Rabs x) (INR B)))) in H8.
clear encadrementordrelog.

assert (H9 : (IZR (absolue_reelc xc (- Int_part (Rlog (Rabs x) (INR B)))%Z) - 1) *
     / B_powerRZ (- Int_part (Rlog (Rabs x) (INR B))) < 
B_powerRZ (Int_part (Rlog (Rabs x) (INR B)) + 1) ).
apply Rgt_lt. apply Rgt_trans with (Rabs x). 
inversion encdrementrabsx. apply Rlt_gt in H6. assumption.
apply Rlt_gt. assumption. inversion encdrementrabsx.
assert (H10 : B_powerRZ (Int_part (Rlog (Rabs x) (INR B))) <
(IZR (absolue_reelc xc (- Int_part (Rlog (Rabs x) (INR B)))%Z) + 1) *
     powerRZ (INR B) (Int_part (Rlog (Rabs x) (INR B))) ).
apply Rle_lt_trans with (Rabs x). assumption. assumption.
clear H0. clear H6. clear H7. clear H8.
assert (H11 : ((IZR (absolue_reelc xc (- Int_part (Rlog (Rabs x) (INR B)))%Z) - 1) *
     / B_powerRZ (- Int_part (Rlog (Rabs x) (INR B)))) * B_powerRZ (- Int_part (Rlog (Rabs x) (INR B)))
 < B_powerRZ (Int_part (Rlog (Rabs x) (INR B)) + 1) * B_powerRZ (- Int_part (Rlog (Rabs x) (INR B)))).
apply Rmult_lt_compat_r. apply Rgt_lt. apply Bexpos. assumption.
replace (B_powerRZ (Int_part (Rlog (Rabs x) (INR B)) + 1) * B_powerRZ (- Int_part (Rlog (Rabs x) (INR B))))
with (B_powerRZ 1) in H11.
replace ((IZR (absolue_reelc xc (- Int_part (Rlog (Rabs x) (INR B)))%Z) - 1) *
      / B_powerRZ (- Int_part (Rlog (Rabs x) (INR B))) * B_powerRZ (- Int_part (Rlog (Rabs x) (INR B))))
with ((IZR (absolue_reelc xc (- Int_part (Rlog (Rabs x) (INR B)))%Z) - 1)) in H11.
clear H9.

assert (H12 : (B_powerRZ (Int_part (Rlog (Rabs x) (INR B)))) * B_powerRZ (-Int_part (Rlog (Rabs x) (INR B))) <
      ((IZR (absolue_reelc xc (- Int_part (Rlog (Rabs x) (INR B)))%Z) + 1) *
      powerRZ (INR B) (Int_part (Rlog (Rabs x) (INR B)))) * B_powerRZ (-Int_part (Rlog (Rabs x) (INR B))) ).
apply Rmult_lt_compat_r. apply Rgt_lt. apply Bexpos. assumption.
replace (B_powerRZ (Int_part (Rlog (Rabs x) (INR B))) * B_powerRZ (- Int_part (Rlog (Rabs x) (INR B))))
with (1) in H12.
replace ((IZR (absolue_reelc xc (- Int_part (Rlog (Rabs x) (INR B)))%Z) + 1) *
      powerRZ (INR B) (Int_part (Rlog (Rabs x) (INR B))) * B_powerRZ (- Int_part (Rlog (Rabs x) (INR B))))
with (IZR (absolue_reelc xc (- Int_part (Rlog (Rabs x) (INR B)))%Z) + 1) in H12.
clear H10. rewrite <- plus_IZR in H12.
apply lt_IZR in H12.
apply Z.lt_succ_r in H12.
rewrite <- minus_IZR in H11. rewrite <- inverseB_power in H11.
apply lt_IZR in H11.  apply Z.lt_pred_le in H11.
apply IZR_le in H12. apply IZR_le in H11.
assert (encadrementxlog : 
1 <= IZR (absolue_reelc xc (- Int_part (Rlog (Rabs x) (INR B)))%Z)
<= IZR (B_powerZ 1) ).
split. assumption. assumption. clear H11. clear H12.
assert (suppos : 1 = IZR (absolue_reelc xc (- Int_part (Rlog (Rabs x) (INR B)))%Z) ->
 IZR (absolue_reelc xc (- Int_part (Rlog (Rabs x) (INR B)) + 1)%Z) >  1).
intros hypo. 
assert (encadrementxlogplus1 : 
encadrement_bis (absolue_reelc xc ((- Int_part (Rlog (Rabs x) (INR B)) + 1)%Z) ) 
((- Int_part (Rlog (Rabs x) (INR B)) + 1)%Z) (Rabs x) ).
apply encadrementbis. unfold encadrement_bis in encadrementxlogplus1.
inversion encadrementxlogplus1.
assert ((IZR (absolue_reelc xc (- Int_part (Rlog (Rabs x) (INR B)) + 1)%Z) - 1) * /
 B_powerRZ (- Int_part (Rlog (Rabs x) (INR B)) + 1) <
     (Rabs x * B_powerRZ (- Int_part (Rlog (Rabs x) (INR B)) + 1))
* / B_powerRZ (- Int_part (Rlog (Rabs x) (INR B)) + 1) ).
apply Rmult_lt_compat_r. apply Rinv_0_lt_compat.
apply Rgt_lt. apply Bexpos. assumption.
replace (Rabs x * B_powerRZ (- Int_part (Rlog (Rabs x) (INR B)) + 1) *
     / B_powerRZ (- Int_part (Rlog (Rabs x) (INR B)) + 1)) with
(Rabs x) in H7. clear H0.
assert (H8 : (Rabs x * B_powerRZ (- Int_part (Rlog (Rabs x) (INR B)) + 1)) * /
B_powerRZ (- Int_part (Rlog (Rabs x) (INR B)) + 1) <
     (IZR (absolue_reelc xc (- Int_part (Rlog (Rabs x) (INR B)) + 1)%Z) + 1) * /
B_powerRZ (- Int_part (Rlog (Rabs x) (INR B)) + 1) ).
apply Rmult_lt_compat_r. apply Rinv_0_lt_compat.
apply Rgt_lt. apply Bexpos. assumption. clear H6.
replace (Rabs x * B_powerRZ (- Int_part (Rlog (Rabs x) (INR B)) + 1) *
     / B_powerRZ (- Int_part (Rlog (Rabs x) (INR B)) + 1)) with
(Rabs x) in H8.
assert (H9 :B_powerRZ (Int_part (Rlog (Rabs x) (INR B))) <
     (IZR (absolue_reelc xc (- Int_part (Rlog (Rabs x) (INR B)) + 1)%Z) + 1) *
     / B_powerRZ (- Int_part (Rlog (Rabs x) (INR B)) + 1) ).
inversion encdrementrabsx.
apply Rle_lt_trans with (Rabs x). assumption. assumption.
assert (H10 : (IZR (absolue_reelc xc (- Int_part (Rlog (Rabs x) (INR B)) + 1)%Z) - 1) *
     / B_powerRZ (- Int_part (Rlog (Rabs x) (INR B)) + 1) < 
B_powerRZ (Int_part (Rlog (Rabs x) (INR B)) + 1)).
apply Rgt_lt. apply Rgt_trans with (Rabs x). apply Rlt_gt.
inversion encdrementrabsx.
assumption. apply Rlt_gt. assumption.
clear H7. clear H8.
assert (H11 : B_powerRZ (Int_part (Rlog (Rabs x) (INR B))) * 
B_powerRZ (- Int_part (Rlog (Rabs x) (INR B)) + 1) <
     ((IZR (absolue_reelc xc (- Int_part (Rlog (Rabs x) (INR B)) + 1)%Z) + 1) *
     / B_powerRZ (- Int_part (Rlog (Rabs x) (INR B)) + 1)) *
B_powerRZ (- Int_part (Rlog (Rabs x) (INR B)) + 1) ).
apply Rmult_gt_compat_r. apply Bexpos. assumption. clear H9.

replace ((IZR (absolue_reelc xc (- Int_part (Rlog (Rabs x) (INR B)) + 1)%Z) + 1) *
      / B_powerRZ (- Int_part (Rlog (Rabs x) (INR B)) + 1) *
 B_powerRZ (- Int_part (Rlog (Rabs x) (INR B)) + 1)) 
with ((IZR (absolue_reelc xc (- Int_part (Rlog (Rabs x) (INR B)) + 1)%Z) + 1)) in H11.
replace (B_powerRZ (Int_part (Rlog (Rabs x) (INR B))) *
 B_powerRZ (- Int_part (Rlog (Rabs x) (INR B)) + 1))
with (B_powerRZ 1) in H11.

assert (H12 : ((IZR (absolue_reelc xc (- Int_part (Rlog (Rabs x) (INR B)) + 1)%Z) - 1) *
      / B_powerRZ (- Int_part (Rlog (Rabs x) (INR B)) + 1))
* B_powerRZ (- Int_part (Rlog (Rabs x) (INR B)) + 1) < 
B_powerRZ (Int_part (Rlog (Rabs x) (INR B)) + 1) * 
B_powerRZ (- Int_part (Rlog (Rabs x) (INR B)) + 1) ).
apply Rmult_lt_compat_r. apply Rgt_lt. apply Bexpos. 
assumption.
replace ((IZR (absolue_reelc xc (- Int_part (Rlog (Rabs x) (INR B)) + 1)%Z) - 1) *
      / B_powerRZ (- Int_part (Rlog (Rabs x) (INR B)) + 1) * 
B_powerRZ (- Int_part (Rlog (Rabs x) (INR B)) + 1))
with ((IZR (absolue_reelc xc (- Int_part (Rlog (Rabs x) (INR B)) + 1)%Z) - 1)) in H12.
replace (B_powerRZ (Int_part (Rlog (Rabs x) (INR B)) + 1) *
 B_powerRZ (- Int_part (Rlog (Rabs x) (INR B)) + 1))
with (B_powerRZ 2) in H12. clear H10.
rewrite <- plus_IZR in H11. rewrite <- inverseB_power in H11.
apply lt_IZR in H11.
apply Z.lt_succ_r in H11.
rewrite <- minus_IZR in H12. rewrite <- inverseB_power in H12.
apply lt_IZR in H12.
apply Z.lt_pred_le in H12.
apply IZR_le in H11. apply IZR_le in H12.
apply Rge_gt_trans with (IZR (B_powerZ 1)).
apply Rle_ge; assumption.
rewrite inverseB_power. 
apply Rge_gt_trans with (4). apply Bge4. lra. omega. omega. omega.
unfold B_powerRZ; rewrite <- powerRZ_add; auto. 
apply f_equal; ring.
replace (IZR (absolue_reelc xc (- Int_part (Rlog (Rabs x) (INR B)) + 1)%Z) - 1) with
((IZR (absolue_reelc xc (- Int_part (Rlog (Rabs x) (INR B)) + 1)%Z) - 1) * 1).
replace ((IZR (absolue_reelc xc (- Int_part (Rlog (Rabs x) (INR B)) + 1)%Z) - 1) * 1 *
/ B_powerRZ (- Int_part (Rlog (Rabs x) (INR B)) + 1) * 
B_powerRZ (- Int_part (Rlog (Rabs x) (INR B)) + 1))
with ((IZR (absolue_reelc xc (- Int_part (Rlog (Rabs x) (INR B)) + 1)%Z) - 1) *
(/ B_powerRZ (- Int_part (Rlog (Rabs x) (INR B)) + 1) * 
B_powerRZ (- Int_part (Rlog (Rabs x) (INR B)) + 1))).
apply Rmult_eq_compat_l. rewrite <- Rinv_l_sym. reflexivity.
now apply Rgt_not_eq; apply Bexpos.
ring. ring. unfold B_powerRZ. rewrite <- powerRZ_add; auto.
apply f_equal; ring.
replace (IZR (absolue_reelc xc (- Int_part (Rlog (Rabs x) (INR B)) + 1)%Z) + 1) with
((IZR (absolue_reelc xc (- Int_part (Rlog (Rabs x) (INR B)) + 1)%Z) + 1) * 1).
replace ((IZR (absolue_reelc xc (- Int_part (Rlog (Rabs x) (INR B)) + 1)%Z) + 1) * 1 *
/ B_powerRZ (- Int_part (Rlog (Rabs x) (INR B)) + 1) * 
B_powerRZ (- Int_part (Rlog (Rabs x) (INR B)) + 1))
with ((IZR (absolue_reelc xc (- Int_part (Rlog (Rabs x) (INR B)) + 1)%Z) + 1) *
(/ B_powerRZ (- Int_part (Rlog (Rabs x) (INR B)) + 1) * 
B_powerRZ (- Int_part (Rlog (Rabs x) (INR B)) + 1))).
apply Rmult_eq_compat_l. rewrite <- Rinv_l_sym. reflexivity.
apply Rgt_not_eq. apply Bexpos. ring. ring. 
replace (Rabs x) with (Rabs x * 1).
replace (Rabs x * 1 * B_powerRZ (- Int_part (Rlog (Rabs x * 1) (INR B)) + 1) *
/ B_powerRZ (- Int_part (Rlog (Rabs x * 1) (INR B)) + 1)) with
(Rabs x * (B_powerRZ (- Int_part (Rlog (Rabs x * 1) (INR B)) + 1) *
/ B_powerRZ (- Int_part (Rlog (Rabs x * 1) (INR B)) + 1))).
apply Rmult_eq_compat_l. rewrite  Rinv_r. reflexivity.
apply Rgt_not_eq. apply Bexpos. ring. ring.
replace (Rabs x) with (Rabs x * 1).
replace (Rabs x * 1 * B_powerRZ (- Int_part (Rlog (Rabs x * 1) (INR B)) + 1) *
/ B_powerRZ (- Int_part (Rlog (Rabs x * 1) (INR B)) + 1)) with
(Rabs x * (B_powerRZ (- Int_part (Rlog (Rabs x * 1) (INR B)) + 1) *
/ B_powerRZ (- Int_part (Rlog (Rabs x * 1) (INR B)) + 1))).
apply Rmult_eq_compat_l. rewrite  Rinv_r. reflexivity.
apply Rgt_not_eq. apply Bexpos. ring. ring.

assert (nltmoinslog : (n < - Int_part (Rlog (Rabs x) (INR B)))%Z -> 
(absolue_reelc xc n <= 1)%Z).
intros nlt. 
assert (encadrementxn : encadrement_bis (absolue_reelc xc n) n (Rabs x)).
apply encadrementbis. unfold encadrement_bis in encadrementxn.
inversion encadrementxn. clear H6.
assert (H6 : (IZR (absolue_reelc xc n) - 1) * / B_powerRZ n
 < (Rabs x * B_powerRZ n) * / B_powerRZ n ).
apply Rmult_lt_compat_r. apply Rinv_0_lt_compat.
apply Rgt_lt. apply Bexpos. assumption.
replace (Rabs x * B_powerRZ n * / B_powerRZ n) with (Rabs x) in H6. clear H0.
clear encadrementxn.
assert (H7 : (IZR (absolue_reelc xc n) - 1) * / B_powerRZ n < 
B_powerRZ (Int_part (Rlog (Rabs x) (INR B)) + 1) ).
apply Rgt_lt. apply Rgt_trans with (Rabs x).
inversion encdrementrabsx. apply Rlt_gt. assumption.
apply Rlt_gt. assumption. clear H6.
assert (H8 : ((IZR (absolue_reelc xc n) - 1) * / B_powerRZ n) * B_powerRZ n < 
B_powerRZ (Int_part (Rlog (Rabs x) (INR B)) + 1) * B_powerRZ n ).
apply Rmult_lt_compat_r. apply Rgt_lt. apply Bexpos. assumption.
clear H7.
replace ((IZR (absolue_reelc xc n) - 1) * / B_powerRZ n * B_powerRZ n) with
((IZR (absolue_reelc xc n) - 1)) in H8. 
assert (nlt2 : (n + Int_part (Rlog (Rabs x) (INR B)) <
 - Int_part (Rlog (Rabs x) (INR B)) + Int_part (Rlog (Rabs x) (INR B)))%Z ).
apply lt_IZR. 
rewrite plus_IZR. rewrite plus_IZR. apply Rplus_lt_compat_r.
apply IZR_lt. assumption. clear nlt.
replace ( (- Int_part (Rlog (Rabs x) (INR B)) + Int_part (Rlog (Rabs x) (INR B)))%Z) with
(0%Z) in nlt2.
apply Z.le_succ_l in nlt2; unfold Z.succ in nlt2.
assert (B_powerlt : B_powerRZ (Int_part (Rlog (Rabs x) (INR B)) + 1 + n) <= 1).
replace (1) with (B_powerRZ 0).
unfold B_powerRZ. apply Rle_powerRZ.
apply Rle_trans with (4). lra. replace 4 with (INR 4) by (simpl; ring).
apply le_INR; generalize B_sup_4; lia.
replace ((Int_part (Rlog (Rabs x) (INR B)) + 1 + n)%Z) with
((n + Int_part (Rlog (Rabs x) (INR B)) + 1)%Z). assumption.
ring. 
reflexivity. clear nlt2.
assert (encadrementxn : IZR (absolue_reelc xc n) - 1 < 1).
apply Rlt_le_trans with (B_powerRZ (Int_part (Rlog (Rabs x) (INR B)) + 1 + n)).
unfold B_powerRZ; rewrite powerRZ_add; auto.
assumption.
rewrite <- minus_IZR in encadrementxn.
apply lt_IZR in encadrementxn.
lia.
ring.
field.
apply Rgt_not_eq, Bexpos.
field.
apply Rgt_not_eq, Bexpos.
assert (msdegallog : msdx = (- Int_part (Rlog (Rabs x) (INR B)))%Z ->
(1 <= absolue_reelc xc msdx <= B_powerZ 1)%Z ).
intros ms.  rewrite ms. split. apply le_IZR. inversion encadrementxlog.
assumption. apply le_IZR. inversion encadrementxlog.
 assumption.
assert (msdegallogplus1 : 
msdx = (- Int_part (Rlog (Rabs x) (INR B)) + 1)%Z ->
 ( absolue_reelc xc (- Int_part (Rlog (Rabs x) (INR B))) = 1)%Z ).
intros msdxc.
inversion encadrementxlog. clear H6.
assert (H7 : 1 >= IZR (absolue_reelc xc (- Int_part (Rlog (Rabs x) (INR B)))%Z)).
apply Rle_ge. apply IZR_le. apply (nltmsd xc msdx); auto.
apply lt_IZR.
rewrite msdxc; apply IZR_lt; lia.

now apply Zle_antisym; [apply le_IZR, Rge_le | apply le_IZR].

assert (msdegallogplus2 : 
msdx = (- Int_part (Rlog (Rabs x) (INR B)) + 1)%Z ->
                  (absolue_reelc xc (- Int_part (Rlog (Rabs x) (INR B)))+ 1)%Z =
 (1 + 1)%Z ).
intros msdxc. apply eq_IZR. rewrite plus_IZR. rewrite plus_IZR.
apply Rplus_eq_compat_r. apply f_equal. apply msdegallogplus1.
assumption. clear msdegallogplus1.
assert (encadrementordrelog : encadrement_bis (absolue_reelc xc 
((- Int_part (Rlog (Rabs x) (INR B)))%Z)) 
((- Int_part (Rlog (Rabs x) (INR B)))%Z) (Rabs x) ).
apply encadrementbis. unfold encadrement_bis in encadrementordrelog.
inversion encadrementordrelog.
assert (H7 : (Rabs x * B_powerRZ (- Int_part (Rlog (Rabs x) (INR B))))*
B_powerRZ ( Int_part (Rlog (Rabs x) (INR B))) <
     (IZR (absolue_reelc xc (- Int_part (Rlog (Rabs x) (INR B)))%Z) + 1) * 
B_powerRZ (Int_part (Rlog (Rabs x) (INR B))) ). apply Rmult_lt_compat_r.
apply Rgt_lt. apply Bexpos. assumption. clear H6.
replace (Rabs x * B_powerRZ (- Int_part (Rlog (Rabs x) (INR B))) *
 B_powerRZ (Int_part (Rlog (Rabs x) (INR B))))
with (Rabs x) in H7.
clear encadrementordrelog.
assert (msdegallogplus3 : msdx = (- Int_part (Rlog (Rabs x) (INR B)) + 1)%Z 
-> Rabs x < 2 * B_powerRZ (Int_part (Rlog (Rabs x) (INR B))) ).
intros msdxc.
apply IZR_trivial in msdegallogplus2.
replace (2) with (IZR (1 + 1)).
rewrite <- msdegallogplus2. rewrite <- plus_IZR in H7. assumption.
apply IZR_trivial. ring. assumption. clear H7.
assert (encadrementlogplus1 : encadrement_bis (absolue_reelc xc 
((- Int_part (Rlog (Rabs x) (INR B)) + 1)%Z)) ((- Int_part (Rlog (Rabs x) (INR B)) + 1)%Z)
 (Rabs x) ). apply encadrementbis.
unfold encadrement_bis in encadrementlogplus1. inversion encadrementlogplus1.
clear encadrementlogplus1. clear H7.
assert (msdegallogplus4 : msdx = (- Int_part (Rlog (Rabs x) (INR B)) + 1)%Z ->
                  Rabs x * B_powerRZ (- Int_part (Rlog (Rabs x) (INR B)) + 1)
 < (2 * B_powerRZ (Int_part (Rlog (Rabs x) (INR B)))) *
 B_powerRZ (- Int_part (Rlog (Rabs x) (INR B)) + 1) ).
intros msdxc. apply Rmult_lt_compat_r. apply Rgt_lt. 
apply Bexpos. apply msdegallogplus3. assumption. clear msdegallogplus3.
replace (2 * B_powerRZ (Int_part (Rlog (Rabs x) (INR B))) *
                  B_powerRZ (- Int_part (Rlog (Rabs x) (INR B)) + 1)) 
with (2 * B_powerRZ 1) in msdegallogplus4.

assert (encadrementxlogplus1 : msdx = (- Int_part (Rlog (Rabs x) (INR B)) + 1)%Z ->
IZR (absolue_reelc xc msdx%Z) - 1 <
2 * B_powerRZ 1 ).

intros msdxc. rewrite msdxc.
apply Rgt_lt. apply Rgt_trans with 
(Rabs x * B_powerRZ (- Int_part (Rlog (Rabs x) (INR B)) + 1)).
apply Rlt_gt. apply msdegallogplus4. assumption.
apply Rlt_gt. assumption. clear H6. clear H0. clear msdegallogplus4.

assert (xcrangmsdgt1 : (absolue_reelc xc msdx > 1)%Z ).


apply xcrangmsd with x. assumption. auto.

assert (xrangmsdentre2et2b : msdx = (- Int_part (Rlog (Rabs x) (INR B)) + 1)%Z ->
 2 <= IZR (absolue_reelc xc msdx) <= 2 * B_powerRZ 1).

intros msdxc. 
split. 
apply IZR_le. rewrite <- Z.lt_pred_le; apply Z.gt_lt. assumption.
replace (IZR (absolue_reelc xc msdx)) with 
(IZR (absolue_reelc xc msdx) - 1 + 1).
rewrite <- minus_IZR. rewrite <- plus_IZR. rewrite <- inverseB_power. 
rewrite <- mult_IZR.
apply IZR_le. apply Z.le_succ_l.
apply lt_IZR. rewrite mult_IZR. rewrite inverseB_power. 
rewrite minus_IZR. apply encadrementxlogplus1. assumption. omega. omega.
ring. 

assert (encadrementordremsd : encadrement_bis (absolue_reelc xc msdx)
 msdx (Rabs x) ). apply encadrementbis. 
unfold encadrement_bis in encadrementordremsd.
inversion encadrementordremsd. clear encadrementordremsd.

assert (H7 : (IZR (absolue_reelc xc msdx) - 1) * B_powerRZ (n - msdx)
 < Rabs x * B_powerRZ msdx *  B_powerRZ (n - msdx) ).
apply Rmult_lt_compat_r. apply Rgt_lt. apply Bexpos. assumption.
clear H0.
replace (Rabs x * B_powerRZ msdx * B_powerRZ (n - msdx)) with
(Rabs x * B_powerRZ (n) ) in H7.

assert (H8 : Rabs x * B_powerRZ msdx * B_powerRZ ( n - msdx) < 
(IZR (absolue_reelc xc msdx) + 1) * B_powerRZ ( n - msdx) ).
apply Rmult_lt_compat_r. apply Rgt_lt. apply Bexpos. assumption. 
clear H6.

replace (Rabs x * B_powerRZ msdx * B_powerRZ (n - msdx))
with (Rabs x * B_powerRZ (n)) in H8.


assert (encadrementordren : encadrement_bis (absolue_reelc xc n)
 n (Rabs x) ). apply encadrementbis. 
unfold encadrement_bis in encadrementordren.
inversion encadrementordren. clear encadrementordren.

assert (encadrementfinal1 : (IZR (absolue_reelc xc msdx) - 1) *
 B_powerRZ (n - msdx) < IZR (absolue_reelc xc n) + 1 ).
apply Rgt_lt. apply Rgt_trans with (Rabs x * B_powerRZ n).
apply Rlt_gt. assumption.
apply Rlt_gt. assumption.

assert (encadrementfinal2 : IZR (absolue_reelc xc n) - 1 <
(IZR (absolue_reelc xc msdx) + 1) * B_powerRZ (n - msdx) ).
apply Rgt_lt. apply Rgt_trans with (Rabs x * B_powerRZ n).
apply Rlt_gt. assumption.
apply Rlt_gt. assumption.

clear H7. clear H8. clear H0. clear H6.

rewrite <- plus_IZR in encadrementfinal1. rewrite <- inverseB_power in 
encadrementfinal1. rewrite <- inverseB_power in encadrementfinal2.
rewrite <- minus_IZR in encadrementfinal1.
rewrite <- mult_IZR in encadrementfinal1.
rewrite <- minus_IZR in encadrementfinal2. 
rewrite <- plus_IZR in encadrementfinal2.
rewrite <- mult_IZR in encadrementfinal2.
apply lt_IZR in encadrementfinal1.
apply lt_IZR in encadrementfinal2.
apply Z.lt_succ_r in encadrementfinal1.
apply Z.lt_pred_le in encadrementfinal2.
apply IZR_le in encadrementfinal1.
apply IZR_le in encadrementfinal2.

assert (xcmsdcomprisentre : 2 <= IZR (absolue_reelc xc msdx) <= 2 * B_powerRZ 1).
inversion H4.

assert (H10 : (1 < absolue_reelc xc msdx <= B_powerZ 1)%Z ).

split. apply Z.gt_lt. apply xcrangmsd with x. assumption.
auto.
rewrite H0.

apply le_IZR. apply encadrementxlog.
inversion H10. clear H10. 
split. apply IZR_le; lia.
apply Rle_trans with (B_powerRZ 1). rewrite <- inverseB_power.
apply IZR_le. assumption. omega. replace (B_powerRZ 1) with (B_powerRZ 1 + 0).
 replace (2 * (B_powerRZ 1 + 0)) with
(B_powerRZ 1 + B_powerRZ 1). apply Rplus_le_compat_l. 
apply Rlt_le. apply Rgt_lt. apply Bexpos. ring.
ring.
apply xrangmsdentre2et2b. assumption.
clear xrangmsdentre2et2b. 

assert (encadrementfinal3 : B_powerRZ (n - msdx) <= 
IZR ((absolue_reelc xc msdx - 1) * B_powerZ (n - msdx)) ).
replace (B_powerRZ (n - msdx)) with (1 * B_powerRZ (n - msdx)).
rewrite mult_IZR. rewrite inverseB_power.
apply Rmult_le_compat_r.
apply Rlt_le. apply Rgt_lt. apply Bexpos.
apply Rplus_le_reg_r with (1). replace (1 + 1) with (2).
replace (IZR (absolue_reelc xc msdx - 1) + 1) with
(IZR (absolue_reelc xc msdx)). inversion xcmsdcomprisentre.  assumption.
rewrite minus_IZR. ring. ring. 
apply Z.le_ge. apply le_IZR. rewrite minus_IZR.
replace (IZR n - IZR msdx) with (IZR n + IZR (-msdx)).
replace (0) with (IZR msdx + IZR (- msdx)).
apply Rplus_le_compat_r. apply IZR_le. apply Z.ge_le. assumption.
rewrite <- plus_IZR. apply IZR_trivial. ring.
rewrite <- plus_IZR. rewrite <- minus_IZR. apply IZR_trivial.
ring. ring.
split. apply le_IZR. apply Rle_trans with 
(IZR ((absolue_reelc xc msdx - 1) * B_powerZ (n - msdx))).
rewrite inverseB_power. assumption. 
apply Z.le_ge. apply le_IZR. rewrite minus_IZR.
replace (IZR n - IZR msdx) with (IZR n + IZR (-msdx)).
replace (0) with (IZR msdx + IZR (- msdx)).
apply Rplus_le_compat_r. apply IZR_le. apply Z.ge_le. assumption.
rewrite <- plus_IZR. apply IZR_trivial. ring.
rewrite <- plus_IZR. rewrite <- minus_IZR. apply IZR_trivial.
ring.
unfold absolue_reelc in encadrementfinal1. unfold absolue_reelc.
assumption. clear encadrementfinal1. clear encadrementfinal3.
assert (encadrementfinal4 : 
IZR ((absolue_reelc xc msdx + 1) * B_powerZ (n - msdx)) <= 
(2 * B_powerRZ 1 + 1) * B_powerRZ (n - msdx) ).
rewrite mult_IZR. rewrite inverseB_power.
apply Rmult_le_compat_r. apply Rlt_le.
apply Rgt_lt. apply Bexpos. rewrite plus_IZR.
apply Rplus_le_compat_r. inversion xcmsdcomprisentre. assumption. 
apply Z.le_ge. apply le_IZR. rewrite minus_IZR.
replace (IZR n - IZR msdx) with (IZR n + IZR (-msdx)).
replace (0) with (IZR msdx + IZR (- msdx)).
apply Rplus_le_compat_r. apply IZR_le. apply Z.ge_le. assumption.
rewrite <- plus_IZR. apply IZR_trivial. ring.
rewrite <- plus_IZR. rewrite <- minus_IZR. apply IZR_trivial.
ring.
apply le_IZR. unfold absolue_reelc in encadrementfinal4.
unfold absolue_reelc in encadrementfinal2.
apply Rle_trans with (IZR ((Z.abs (xc msdx) + 1) * 
B_powerZ (n - msdx))). assumption. rewrite mult_IZR.
rewrite mult_IZR. rewrite plus_IZR. rewrite plus_IZR.
apply Rmult_le_compat_r.  apply Rlt_le.
rewrite inverseB_power. apply Rgt_lt. apply Bexpos. 
apply Z.le_ge. apply le_IZR. rewrite minus_IZR.
replace (IZR n - IZR msdx) with (IZR n + IZR (-msdx)).
replace (0) with (IZR msdx + IZR (- msdx)).
apply Rplus_le_compat_r. apply IZR_le. apply Z.ge_le. assumption.
rewrite <- plus_IZR. apply IZR_trivial. ring.
rewrite <- plus_IZR. rewrite <- minus_IZR. apply IZR_trivial.
ring.
rewrite mult_IZR. replace (IZR (Z.of_nat B)) with
(IZR (Z.of_nat B^1)).
apply Rplus_le_compat_r.
destruct xcmsdcomprisentre as [it1 it2].
unfold B_powerRZ in it2; rewrite powerRZ_1 in it2.
rewrite Z.pow_1_r, <- INR_IZR_INZ; assumption.
rewrite Z.pow_1_r; reflexivity.
apply Z.le_ge. apply le_IZR. rewrite minus_IZR.
replace (IZR n - IZR msdx) with (IZR n + IZR (-msdx)).
replace (0) with (IZR msdx + IZR (- msdx)).
apply Rplus_le_compat_r. apply IZR_le. apply Z.ge_le. assumption.
rewrite <- plus_IZR. apply IZR_trivial. ring.
rewrite <- plus_IZR. rewrite <- minus_IZR. apply IZR_trivial.
ring. 
apply Z.le_ge. apply le_IZR. rewrite minus_IZR.
replace (IZR n - IZR msdx) with (IZR n + IZR (-msdx)).
replace (0) with (IZR msdx + IZR (- msdx)).
apply Rplus_le_compat_r. apply IZR_le. apply Z.ge_le. assumption.
rewrite <- plus_IZR. apply IZR_trivial. ring.
rewrite <- plus_IZR. rewrite <- minus_IZR. apply IZR_trivial.
ring.

replace (Rabs x * B_powerRZ msdx * B_powerRZ (n - msdx))
with (Rabs x * (B_powerRZ msdx * B_powerRZ (n - msdx))).
apply Rmult_eq_compat_l.
unfold B_powerRZ; rewrite <- powerRZ_add; auto.
apply f_equal; ring.
ring.
rewrite Rmult_assoc; unfold B_powerRZ.
apply Rmult_eq_compat_l.
rewrite <- powerRZ_add; auto.
apply f_equal; ring.
rewrite Rmult_assoc.
apply Rmult_eq_compat_l. unfold B_powerRZ; rewrite <- powerRZ_add; auto.
apply f_equal; ring.
rewrite Rmult_assoc.
unfold B_powerRZ; rewrite <- powerRZ_add; auto.
replace (- Int_part (Rlog (Rabs x)(INR B)) + Int_part (Rlog (Rabs x)(INR B)))%Z
  with 0%Z by ring.
rewrite powerRZ_O; ring.
lia.
replace (powerRZ (INR B) (Int_part (Rlog (Rabs x) (INR B))))
with (B_powerRZ (Int_part (Rlog (Rabs x) (INR B)))).
replace (IZR (absolue_reelc xc (- Int_part (Rlog (Rabs x) (INR B)))%Z) + 1) with
((IZR (absolue_reelc xc (- Int_part (Rlog (Rabs x) (INR B)))%Z) + 1) * 1).
replace ((IZR (absolue_reelc xc (- Int_part (Rlog (Rabs x) (INR B)))%Z) + 1) * 1 *
B_powerRZ (Int_part (Rlog (Rabs x) (INR B))) *
 B_powerRZ (- Int_part (Rlog (Rabs x) (INR B))))
with ((IZR (absolue_reelc xc (- Int_part (Rlog (Rabs x) (INR B)))%Z) + 1) *
(B_powerRZ (Int_part (Rlog (Rabs x) (INR B))) *
 B_powerRZ (- Int_part (Rlog (Rabs x) (INR B))))).
apply Rmult_eq_compat_l. replace (1) with (B_powerRZ 0).
unfold B_powerRZ; rewrite <- powerRZ_add; auto.
apply f_equal; ring.
now unfold B_powerRZ; rewrite powerRZ_O.
ring.
ring.
reflexivity.
unfold B_powerRZ; rewrite <- powerRZ_add; auto.
replace
 (Int_part (Rlog (Rabs x) (INR B)) + - Int_part (Rlog (Rabs x) (INR B)))%Z
with 0%Z by ring.
now rewrite powerRZ_O.
rewrite Rmult_assoc, Rinv_l.
ring.
apply powerRZ_INR_B_non_nul.
unfold B_powerRZ.
rewrite <- powerRZ_add.
apply f_equal; ring.
apply Rgt_not_eq, Rlt_gt, (lt_INR 0); generalize B_sup_4; lia.
unfold B_powerRZ; rewrite Rinv_powerRZ.
apply f_equal; ring.
apply Rgt_not_eq, Rlt_gt, (lt_INR 0); generalize B_sup_4; lia.
field.
apply Rgt_not_eq, Bexpos.
ring.
rewrite Rmult_assoc; rewrite <- powerRZ_add.
replace (- Int_part (Rlog (Rabs x) (INR B)) + - - Int_part (Rlog (Rabs x) (INR B)))%Z with 0%Z by ring.
rewrite powerRZ_O; ring.
apply Rgt_not_eq, Rlt_gt, (lt_INR 0); generalize B_sup_4; lia.
apply Rgt_not_eq, Rlt_gt, (lt_INR 0); generalize B_sup_4; lia.
Qed.

Lemma compute_msd_up (x : R)(xc : Reelc)
 (max : Z) :
 x <> 0 -> encadrement xc x ->
 (max < msd x xc)%Z ->
 compute_msd (Z.of_nat B) xc max = max.
Proof.
intros xn0 xcx mm.
unfold compute_msd.
assert (msd_prop xc (msd x xc)) as [ple _] by now apply msd_prop2.
assert (ple' := ple max mm).
destruct (Z.ltb_spec 1 (Z.abs (xc max)))as [plt | _]; auto.
now destruct (Zlt_not_le _ _ plt); auto.
Qed.

Lemma powerRZ_pow x y : (0 <= y)%Z -> (IZR (x ^ y)) = powerRZ (IZR x) y.
intros ygt0.
unfold powerRZ.
destruct y; auto; try lia.
rewrite <- positive_nat_Z.
now rewrite <- pow_IZR.
Qed.

Lemma compute_msd_down_pos (x : R)(xc : Reelc)
 (max : Z) :
 x <> 0 -> 0 < x -> encadrement xc x ->
 (msd x xc <= max)%Z ->
 compute_msd (Z.of_nat B) xc max = (msd x xc).
Proof.
intros xn0 xgt0 xcx mm; unfold compute_msd.
assert (mp : msd_prop xc (msd x xc)) by now apply msd_prop2.
destruct (mp) as [ple _].
assert (mm' := Z.le_ge _ _ mm).
assert (main := msd_d xc (msd x xc) max x xn0 mm' xcx mp).
destruct (Z.ltb_spec 1 (Z.abs (xc max))) as [plt | ple']; cycle 1.
  assert (1 < Z.abs (xc max))%Z.
    destruct (Zle_lt_or_eq _ _ mm) as [mlt |meq].
      apply Z.lt_le_trans with (2 := proj1 main).
      unfold B_powerZ.
      apply Z.pow_gt_1.
        apply (inj_lt 1); generalize B_sup_4; lia.
      lia.
    now apply Z.gt_lt; rewrite <- meq; destruct mp as [mp1 mp2]; apply mp2.
  now generalize ple'; rewrite Z.le_ngt; intros abs; case abs.
assert (xcmpos' : 0 <= IZR (xc max)).
  destruct (Z_lt_le_dec (xc max) 0).
    enough (0 > x) by lra.
    apply (sg_Zsgn_2 x xc max); auto; lia.
  now apply (IZR_le 0).
assert (xcmpos : 0 < IZR (xc max)).
  apply IZR_lt; generalize plt; rewrite Z.abs_eq; [lia |].
  now apply le_IZR.
set (l := ZlogB _ _).
assert (0 <= l)%Z.
  unfold l; apply ZlogB_pos.
  apply Z.le_trans with (2 := proj1 main).
  assert (tmp := Bexpos (max - msd x xc)).
  rewrite <- Z.lt_pred_le; cbv[Z.pred Z.add Z.pos_sub].
  apply lt_IZR; rewrite inverseB_power;[lra | lia].
set (l' := (_ - 1)%Z).
set (w := Z.abs _).
assert (0 <= x) by lra.
assert (INR B <> 0).
  apply Rgt_not_eq, Rlt_gt, (lt_INR 0); generalize B_sup_4; lia.
assert (B_sup_4' : (4 <= Z.of_nat B)%Z).
  replace 4%Z with (Z.of_nat 4) by (simpl; ring).
  apply inj_le; exact B_sup_4.
assert (B_sup_2 : (2 <= Z.of_nat B)%Z) by lia.
assert (1 <= INR B).
  apply (le_INR 1); generalize B_sup_4; lia.
assert (sg_n : forall n, (0 <= xc n)%Z).
  intros n.
  destruct (Z_lt_le_dec (xc n) 0) as [abs | ?]; try lia.
  assert (tmp := sg_Zsgn_2 x xc n xcx (Z.lt_gt _ _ abs)); lra.
destruct (Z.ltb_spec 1 w) as [wbig | wsmall].
  apply (msd_prop_unique x xc); auto.
  split;[ | now apply Z.lt_gt; auto].
  intros n nl.
  assert (acmpb : Rabs x < B_powerRZ((l + 1) - max)).
    replace ((l + 1) - max)%Z with ((l + 1) + (- max))%Z by ring.
    unfold B_powerRZ; rewrite powerRZ_add; auto.
    rewrite <-Rinv_powerRZ; auto.
    rewrite Rabs_pos_eq; auto.
    apply Rmult_lt_reg_r with (B_powerRZ max).
      now apply Bexpos.
    rewrite Rmult_assoc, Rinv_l, Rmult_1_r; cycle 1.
      now apply Rgt_not_eq, Rlt_gt, Bexpos.
    apply Rlt_le_trans with (1 := proj2 (xcx max)).
    rewrite <- plus_IZR.
    rewrite INR_IZR_INZ, <- powerRZ_pow;[ | lia].
    apply IZR_le; enough (xc max < Z.of_nat B ^ (l + 1))%Z by lia.
    destruct (ZlogB_correct (Z.of_nat B) (xc max) B_sup_2
                (lt_IZR _ _ xcmpos)) as [_ it].
    now unfold l; rewrite Z.abs_eq; auto; apply le_IZR.
  assert (xbn: 0 < Rabs x * B_powerRZ n < 1).
    rewrite Rabs_pos_eq; auto.
    split.
      now apply Rmult_lt_0_compat; auto; apply Bexpos.
    apply Rmult_lt_reg_r with (B_powerRZ (- n)).
      now apply Bexpos.
    unfold B_powerRZ; rewrite Rmult_assoc, <- powerRZ_add; auto.
    rewrite Z.add_opp_diag_r, powerRZ_O, Rmult_1_l, Rmult_1_r.
    rewrite Rabs_pos_eq in acmpb; auto.
    apply Rlt_le_trans with (1 := acmpb).
    apply Rle_powerRZ; auto; lia.
  rewrite Z.abs_eq; auto.
  rewrite <- Z.lt_succ_r; unfold Z.succ.
  enough (xc n - 1 < 1)%Z by lia.
  apply lt_IZR; rewrite minus_IZR.
  apply Rlt_trans with (2 := proj2 xbn); rewrite Rabs_pos_eq; auto.
  assert (res := xcx n); tauto.
assert (common : forall n, (n < max - l)%Z -> (Z.abs (xc n) <= 1)%Z).
  intros n nl; assert (nl' : (n <= l')%Z) by lia.
  apply Zle_lt_or_eq in nl'; destruct nl' as [nl' | nl']; cycle 1.
    now rewrite nl'.
  rewrite Z.abs_eq; auto.
  rewrite <- Z.lt_succ_r; change (Z.succ 1) with (2%Z).
  apply lt_IZR.
  apply Rlt_le_trans with (x * B_powerRZ n + 1).
  destruct (xcx n); lra.
  enough (x * B_powerRZ n <= 1) by lra.
  apply Rmult_le_reg_r with (B_powerRZ (max - l - n - 1)).
    now apply Bexpos.
  unfold B_powerRZ; rewrite Rmult_assoc, <- powerRZ_add; auto.
  replace (n + (max - l - n - 1))%Z with (max - l - 1)%Z by lia.
  apply Rle_trans with 2.
    destruct (xcx (max - l - 1)%Z) as [_ it].
    unfold w in wsmall; rewrite Z.abs_eq in wsmall; auto.
    fold l' in it |- *; unfold B_powerRZ in it.
    assert (xcl' : (0 <= xc l')%Z) by auto.
    apply IZR_le in xcl'; apply IZR_le in wsmall.
    lra.
  apply Rle_trans with (B_powerRZ 1).
    unfold B_powerRZ; rewrite powerRZ_1; apply (le_INR 2).
    generalize B_sup_4; lia.
  rewrite Rmult_1_l.
  apply Rle_powerRZ; auto; lia.
destruct (Z.ltb_spec 1 (Z.abs (xc (max - l)))%Z) as [maxl | maxl].
  apply (msd_prop_unique x xc); auto.
  now split;[apply common | apply Z.lt_gt].
apply (msd_prop_unique x xc); auto.
split.
  intros n; rewrite (Z.lt_succ_r n (max - l)); intros tmp.
  destruct (Zle_lt_or_eq _ _ tmp) as [nlt | n_eq].
    now apply common.
  now rewrite n_eq.
rewrite Z.abs_eq; auto.
enough (2 < xc (max - l + 1) + 1)%Z by lia.
destruct (xcx (max - l + 1)%Z) as [_ cl'].
apply lt_IZR; rewrite plus_IZR.
apply Rle_lt_trans with (2 := cl').
assert (l <> 0%Z).
  intros abs; rewrite abs, Z.sub_0_r in maxl; lia.
replace (max - l + 1)%Z with (max + (- (l - 1)))%Z by ring.
unfold B_powerRZ; rewrite powerRZ_add; auto.
rewrite <- Rmult_assoc.
apply Rle_trans with
   ((IZR (xc max) - 1) * powerRZ (INR B) (- (l - 1))); cycle 1.
  apply Rmult_le_compat_r.
    now apply Rlt_le, Bexpos.
  destruct (xcx max) as [it _]; unfold B_powerRZ in it; lra.
apply Rmult_le_reg_r with (powerRZ (INR B) (l - 1)).
  now apply Bexpos.
rewrite Rmult_assoc, <- powerRZ_add, Z.add_opp_diag_l, powerRZ_O; auto.
enough (2 * powerRZ (INR B) (l - 1) + 1 <= IZR(xc max)) by lra.
apply Rle_trans with (powerRZ (INR B) l).
  pattern l at 2; replace l with (l - 1 + 1)%Z by ring.
  rewrite powerRZ_add; auto.
  rewrite INR_IZR_INZ, <- !powerRZ_pow;[ | lia | lia].
  rewrite <-mult_IZR, <- plus_IZR, <- !mult_IZR; apply IZR_le.
  apply Z.le_trans with ((2 + 1) * Z.of_nat B ^ (l - 1))%Z.
    rewrite Z.mul_add_distr_r, Zmult_1_l; apply Zplus_le_compat_l.
    enough (0 < Z.of_nat B ^ (l - 1))%Z by lia.
    now apply Z.pow_pos_nonneg; lia.
  rewrite Z.mul_comm, Z.pow_1_r; apply Zmult_le_compat_l; try lia.
  apply Z.pow_nonneg; lia.
unfold l; rewrite Z.abs_eq; auto.
destruct (ZlogB_correct (Z.of_nat B) (xc max) B_sup_2
                (lt_IZR _ _ xcmpos)) as [it _].
rewrite INR_IZR_INZ, <- powerRZ_pow;[ |]; cycle 1.
  now rewrite <- (Z.abs_eq (xc max)).
now apply IZR_le.
Qed.

Lemma compute_msd_opp b' xc max :
  compute_msd b' (fun z => - (xc z))%Z max = compute_msd b' xc max.
Proof.
now unfold compute_msd; rewrite !Z.abs_opp.
Qed.

Lemma compute_msd_down (x : R)(xc : Reelc)
 (max : Z) :
 x <> 0 -> encadrement xc x ->
 (msd x xc <= max)%Z ->
 compute_msd (Z.of_nat B) xc max = (msd x xc).
Proof.
intros xn0; destruct (Rlt_dec 0 x).
  now apply compute_msd_down_pos.
intros xcx mp.
assert (xcxo : encadrement (fun z => - (xc z))%Z (- x)).
  intros k; rewrite <- Ropp_mult_distr_l, opp_IZR; destruct (xcx k); lra.
assert (pmo: pre_msd (- x) = pre_msd x).
  now unfold pre_msd; rewrite Rabs_Ropp.
assert (mo : msd (-x) (fun z => - (xc z))%Z = msd x xc).
  now unfold msd; rewrite Z.abs_opp, pmo.
assert (cmo : compute_msd (Z.of_nat B) xc max =
        compute_msd (Z.of_nat B) (fun z => - (xc z))%Z max).
  now unfold compute_msd; rewrite !Z.abs_opp.
rewrite cmo, <- mo; apply compute_msd_down_pos; auto; try lra; lia.
Qed.