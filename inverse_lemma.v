Require Import Reals.
Require Export definition.
Require Import Tactiques.
Require Import Rbase_inegalites.
Require Import Rbase_doubles_inegalites.
Require Import Rabsolu_complements.
Require Import powerRZ_complements.
Require Import Axiomes.
Require Import Lemmes.
Require Import Absolue.
Require Import sg.
Require Import Rind_complements.
Require Import Lemmes_generaux.
Require Import Zabs_complements.
Require Import Zpower_complements.
Require Import Lra.
Require Import Zarith_operations.
Require Import Rbase_operations.

Lemma inversegeZ : forall z1 z2 : Z,
(z1 <= z2)%Z -> (z2 >= z1)%Z.
Proof. intros z1 z2 H. omega. Qed.

Lemma inversegtZ : forall z1 z2 : Z,
(z1 < z2)%Z -> (z2 > z1)%Z.
Proof. intros z1 z2 H. omega. Qed.

Lemma inverseltZ : forall z1 z2 : Z,
(z1 > z2)%Z -> (z2 < z1)%Z.
Proof. intros z1 z2 H. omega. Qed.

Lemma inverseleZ : forall z1 z2 : Z,
(z1 >= z2)%Z -> (z2 <= z1)%Z.
Proof. intros z1 z2 H. omega. Qed.


                              (* égalité sur Z : DEBUT *)

Lemma plus0Z : forall z : Z,
(z = 0 + z)%Z.
Proof. intros; omega. Qed.




                             (* égalité sur Z : FIN *)










                           (* égalité sur R : DEBUT *)






Lemma neqR : forall r : R,
r > 0 -> r <> 0 .
Proof.
intros r H. apply Rgt_not_eq. assumption. Qed.




Lemma trivialee : 1 * / 4 = 1 * / 2 * / 2.
Proof. replace (1 * / 4) with (1 * /(2 * 2)).
- rewrite Rinv_mult_distr.
+ ring. 
+ apply neqR. lra.
+ apply neqR. lra.
- replace ((2 * 2)) with (4). reflexivity. ring. Qed.


 Lemma divisionR3 : forall r1 r2 r3 r4 r5 : R,
r1 * r2 = r3 * r4 -> r5 * r1 * r2 = r5 * r3 * r4.
Proof. intros r1 r2 r3 r4 r5 H.  rewrite Rmult_assoc. rewrite H. rewrite Rmult_assoc.
reflexivity. Qed.

Lemma divisionR2 : forall r1 r2 r3  : R,
r1  = r2 -> r3 * r1 = r3 * r2.
Proof. intros r1 r2 r3 H. rewrite H. reflexivity. Qed.


Lemma soustractionIZR : forall z1 z2 : Z,
IZR (z1 - z2) = IZR z1 - IZR z2.
Proof. intros z1 z2. rewrite minus_IZR. reflexivity.
Qed.


Lemma commutativitedeR : forall r1 r2 : R,
r1 * r2 = r2 * r1.
Proof. intros r1 r2. ring. Qed.


Lemma trivial24 : forall r1 r2 : R,
r1 <> 0 -> r2 <> 0 ->r1 * / (r1 * r2) = 1 * / r2.
Proof. intros r1 r2 H1 H2. rewrite Rinv_mult_distr.
- rewrite <- Rmult_assoc. rewrite Rinv_r_simpl_r.
+ ring. 
+ assumption.  - assumption.
- assumption. Qed.


Lemma trivial23 : forall r1 r2 r3 : R,
r1 <> 0 -> r3 <> 0 ->r1 * r2 * / (r3 * r1) = r2 * / r3.
Proof. intros r1 r2 r3 H1 H2. rewrite Rinv_mult_distr. 
- rewrite commutativitedeR. rewrite <- Rmult_assoc. replace (/ r3 * / r1 * r1 * r2) with
(/ r3 * (/ r1 * r1) * r2). + rewrite Rinv_l.
{ replace (/ r3 * 1 * r2) with (/ r3 * (1 * r2)).
rewrite Rmult_1_l. rewrite commutativitedeR. reflexivity.
rewrite <- Rmult_assoc. reflexivity. } assumption.
+ ring. - assumption. - assumption. Qed.


Lemma trivial22 : forall z : Z,
IZR(z-1) = IZR(z) - 1.
Proof. intros z. rewrite soustractionIZR. reflexivity. Qed.


Lemma trivial13 : forall r1 : R,
(r1 - 1) * (1 + 2 * / r1)=r1 + 2 * r1 * / r1 - 1 * 1 - 1 * 2 * / r1.
Proof. intros; ring. Qed.

Lemma produitencroix : forall r1 r2 r3 r4 : R,
r2 <> 0 -> r4 <> 0 -> r1 * / r2 - r3 * / r4 = ((r1*r4)- (r3*r2)) * / (r2*r4).
Proof. intros r1 r2 r3 r4 H1 H2. 
replace ((r1 * r4 - r3 * r2) * / (r2 * r4)) with 
((r1 * r4 - r3 * r2) / (r2 * r4)).
- replace (r1 * / r2) with ((r1 * r4) / (r2 * r4)).
+ replace (r3 * / r4) with ((r3 * r2) / (r2 * r4)).
{rewrite <- Rdiv_minus_distr. reflexivity. }
replace (r3 * r2 / (r2 * r4)) with (r3 * r2 * / (r2 * r4)).
rewrite Rinv_mult_distr. 
{ replace (r3 * r2 * (/ r2 * / r4)) with (r3 * r2 * / r2 * / r4).
{ rewrite Rinv_r_simpl_l. reflexivity. assumption. }
ring. } assumption. assumption. reflexivity. 
+ replace (r1 * r4 / (r2 * r4)) with (r1 * r4 * / (r2 * r4)). rewrite Rinv_mult_distr.
{ replace (r1 * r4 * (/ r2 * / r4)) with (r1 * r4 * / r2 * / r4).
{ replace (r1 * r4 * / r2 * / r4) with (r1 * r4 * / r4 * / r2).
{rewrite Rinv_r_simpl_l. reflexivity. assumption. } 
ring. } ring. } assumption. assumption. reflexivity. 
- reflexivity. Qed.

Lemma trivial10 : - (1 * / 2) = -1 + 1 * / 2.
Proof. replace (-1) with (-1 * / 1). 
- replace (-1 * / 1 + 1 * / 2) with (1 * / 2 - 1 * / 1).
+ rewrite produitencroix.
{ replace (1 * 1 - 1 * 2) with (-1).
{ replace (2 * 1) with (2).
{ ring. } ring. } ring. } { apply neqR. lra. }
apply neqR. lra. 
+ ring. 
- replace (-1 * / 1) with (-( / 1 * 1)).
{ rewrite Rinv_l.
{ ring. } apply neqR. lra. }
ring. Qed.



Lemma fracdersurr : forall r : R,
r <> 0 -> r * / r = 1.
Proof. intros r H. symmetry. apply Rinv_r_sym. auto. Qed.

Lemma produitIZR : forall z1 z2 : Z,
IZR (z1) * IZR (z2) = IZR (z1 * z2).
Proof. intros z1 z2. rewrite mult_IZR. reflexivity.
Qed.



Lemma factorisationR2 : forall z1 z2 z3 z4 : Z,
IZR (z1 - z2)* IZR(z3 + z4)=IZR(z1 * z3 + z1 * z4 - z2 * z3 - z2 * z4).
Proof. intros z1 z2 z3 z4. rewrite produitIZR. simpl. 
apply IZR_trivial. ring. Qed.



Lemma simplificationIZR : forall z1 z2 z3 z4 : Z,
IZR (z1 + z2) - IZR (z3 - z4) = IZR (z1 + z2 - z3 + z4).
Proof. intros z1 z2 z3 z4.
rewrite <- soustractionIZR. apply IZR_trivial. omega. Qed.





Lemma factorisationR : forall r1 r2 r3 : R,
r1*r2 - r1*r3 = r1*(r2 - r3).
Proof. 
intros r1 r2 r3. ring. Qed.

Lemma fractionsurR : forall r1 r2 r3 : R,
r3 <> 0 -> r1 = r2 -> r1 * / r3 = r2 * / r3.
Proof.
intros r1 r2 r3 H1 H2.
rewrite H2. reflexivity. Qed.















                     (* égalite sur R : FIN *)











(*                    inégalité sur R : DEBUT *)








Lemma inversegtR : forall z1 z2 : R,
z1 < z2 -> z2 > z1.
Proof. intros z1 z2 H. lra. Qed.

Lemma inverseltR : forall z1 z2 : R,
z1 > z2 -> z2 < z1.
Proof. intros z1 z2 H. lra. Qed.

Lemma inverseleR : forall z1 z2 : R,
z1 >= z2 -> z2 <= z1.
Proof. intros z1 z2 H. lra. Qed.

Lemma inversegeR : forall z1 z2 : R,
z1 <= z2 -> z2 >= z1.
Proof. intros z1 z2 H. lra. Qed.

Lemma trivial28 : forall r : R,
r > 1 -> r > 0.
Proof. intros; lra. Qed.

Lemma produitdedeuxpositifsR : forall r1 r2 : R,
r1 > 0 -> r2 > 0 -> r1 * r2 > 0.
Proof. intros r1 r2 H1 H2. 
- apply inversegtR. apply Rmult_gt_0_compat. 
assumption. assumption. Qed.

Lemma carreplusgrandque1R : forall r1 r2 : R,
r1 > 1 -> r2 > 1 -> r1 * r2 > 1.
Proof. intros r1 r2 H1 H2. replace (1) with (1 * 1). apply Rlt_gt. 
apply Rmult_gt_0_lt_compat. - lra.
- apply trivial28. assumption.
- apply inverseltR. assumption.
- apply inverseltR. assumption.
- ring. Qed.

Lemma partieentièreinférieure : forall z1 z2 : Z,
(z2 > 0)%Z -> IZR ((z1 / z2)%Z) <= IZR (z1) * / IZR (z2).
Proof. intros z1 z2 H. 
apply Rmult_le_reg_l with (IZR z2). apply IZR_lt. apply inverseltZ.
assumption. rewrite <- Rmult_assoc.
rewrite Rinv_r_simpl_m. rewrite produitIZR. apply IZR_le.
apply Z_mult_div_ge. assumption. apply neqR. apply inversegtR.
apply IZR_lt. apply inverseltZ. assumption. Qed.

Lemma ZneqR : forall z : Z,
(z > 0)%Z -> (z <> 0)%Z.
Proof. intros; omega. Qed.

Lemma zdivsupge : forall z1 z2 : Z,
(z2 > 0)%Z -> IZR (Zdiv_sup z1 z2) >= IZR z1 * / IZR z2.
Proof. intros z1 z2.  unfold Zdiv_sup.
case (Z_zerop(z1 mod z2)). intros H1 H2.
rewrite Zmod_eq_full in H1.
assert (H3 : IZR (z1) = IZR (z1 / z2 * z2)).
replace (IZR (z1 / z2 * z2)) with (0 + IZR (z1 / z2 * z2)).
replace (IZR z1) with (IZR z1 - IZR (z1 / z2 * z2) + IZR (z1 / z2 * z2)).
apply Rplus_eq_compat_r. rewrite <- minus_IZR. apply IZR_trivial.
assumption. ring. ring. rewrite <- produitIZR in H3.
assert (H4 : IZR z1 * / IZR z2 = (IZR (z1 / z2) * IZR z2) * / IZR z2).
apply Rmult_eq_compat_r. assumption.
rewrite Rinv_r_simpl_l in H4. symmetry in H4. 
apply Req_ge. assumption. apply neqR.
apply inversegtR. apply IZR_lt. apply inverseltZ. assumption.
apply ZneqR. assumption.
intros H1 H2.  
assert (H3 : IZR (z1 mod z2) = IZR (z1 - z1 / z2 * z2)).
apply IZR_trivial. rewrite Zmod_eq_full. reflexivity.
apply ZneqR. assumption.
assert (H4 : IZR (z1 mod z2) + IZR (z1 / z2 * z2) = IZR (z1)).
replace (IZR z1) with (IZR z1 - IZR (z1 / z2 * z2) + IZR (z1 / z2 * z2)).
rewrite <- minus_IZR. apply Rplus_eq_compat_r. assumption. ring.
assert (H5 : IZR (z1 / z2 * z2) = IZR z1 - IZR (z1 mod z2)).
replace (IZR z1 - IZR (z1 mod z2)) with (IZR z1 + (- IZR (z1 mod z2))).
replace (IZR (z1 / z2 * z2)) with (IZR (z1 / z2 * z2) + IZR (z1 mod z2) + (- IZR (z1 mod z2))).
apply Rplus_eq_compat_r. rewrite Rplus_comm. assumption.
ring. ring. rewrite <- minus_IZR in H5. 
assert (H6 : IZR (z1 / z2) = (IZR (z1 - z1 mod z2)) * / IZR z2).
replace (IZR (z1 / z2)) with ((IZR (z1 / z2) * IZR z2) * / IZR z2).
apply Rmult_eq_compat_r. rewrite produitIZR. assumption.
apply Rinv_r_simpl_l. apply neqR. apply inversegtR. apply IZR_lt. 
apply inverseltZ. assumption.
replace (IZR (z1 - z1 mod z2) * / IZR z2) with
(IZR z1 * / IZR z2 - IZR (z1 mod z2) * / IZR z2) in H6.
assert (H7 : IZR (z1 mod z2) * / IZR z2 <= 1). 
replace (1) with (IZR z2 * / IZR z2). apply Rmult_le_compat_r.
apply Rlt_le.  apply Rinv_0_lt_compat. apply IZR_lt.
apply inverseltZ. assumption. apply Rlt_le.
apply IZR_lt. apply Z_mod_lt. assumption. 
rewrite <- Rinv_r_sym. reflexivity. apply neqR.
apply inversegtR. apply IZR_lt. apply inverseltZ. assumption.
assert (H8 :  - IZR (z1 mod z2) * / IZR z2 >=  -1).
rewrite <- Ropp_mult_distr_l. apply Ropp_le_ge_contravar. assumption.
assert (H9 : IZR (z1 / z2) + 1 = IZR z1 * / IZR z2 - IZR (z1 mod z2) * / IZR z2 + 1).
apply Rplus_eq_compat_r. assumption.
replace (IZR (z1 / z2) + 1) with (IZR (Z.succ (z1 / z2))) in H9.
assert (H10 : IZR z1 * / IZR z2 - IZR (z1 mod z2) * / IZR z2 + 1 >= IZR z1 * / IZR z2).
replace (IZR z1 * / IZR z2) with (0 + IZR z1 * / IZR z2).
replace (0 + IZR z1 * / IZR z2 - IZR (z1 mod z2) * / IZR z2 + 1) with
( - IZR (z1 mod z2) * / IZR z2 + 1 + IZR z1 * / IZR z2).
apply Rplus_ge_compat_r.
replace (0) with (- 1 + 1).
apply Rplus_ge_compat_r. assumption. ring. ring. ring.
rewrite H9. assumption. replace (Z.succ (z1 / z2)) with ((z1 / z2 + 1)%Z).
rewrite plus_IZR. reflexivity. ring. rewrite minus_IZR.
replace (IZR z1 - IZR (z1 mod z2)) with (IZR z1 + (- IZR (z1 mod z2))).
replace ((IZR z1 + - IZR (z1 mod z2)) * / IZR z2) with
(/ IZR z2 * (IZR z1 + - IZR (z1 mod z2))).
rewrite Rmult_plus_distr_l. rewrite Rmult_comm.
replace (/ IZR z2 * - IZR (z1 mod z2)) with (- IZR (z1 mod z2) * / IZR z2).
ring. ring. ring. ring. Qed.

Lemma additionlt : forall r1 r2 : R,
r1 - r2 > 0 -> r1 > r2.
Proof. intros r1 r2 H. lra. Qed.


Lemma Zdiv_inflt : forall z1 z2 : Z,
(z2 > 0)%Z -> IZR((z1 / z2)%Z) > IZR z1 * / IZR z2 - 1.
Proof. intros z1 z2 H. 
assert (H2 : (z1 mod z2)%Z = (z1 - z1/z2 * z2)%Z).
rewrite Zmod_eq_full. reflexivity. apply ZneqR. assumption.
assert (H3 : IZR (z1 / z2 * z2)= IZR z1 - IZR (z1 mod z2)).
replace (IZR (z1 / z2 * z2)) with (IZR (z1 / z2 * z2) + 0).
replace (IZR z1 - IZR (z1 mod z2)) with
(IZR (z1 / z2 * z2) + IZR z1 - IZR (z1 / z2 * z2) - IZR (z1 mod z2)).
replace (IZR (z1 / z2 * z2) + IZR z1 - IZR (z1 / z2 * z2) - IZR (z1 mod z2)) with
(IZR (z1 / z2 * z2) + (IZR z1 - IZR (z1 / z2 * z2) - IZR (z1 mod z2))).
apply Rplus_eq_compat_l. 
replace (IZR z1 - IZR (z1 / z2 * z2) - IZR (z1 mod z2)) with
(IZR z1 - IZR (z1 / z2 * z2)  + (- IZR (z1 mod z2))).
replace (0) with 
(IZR (z1 mod z2) + (- IZR (z1 mod z2))).
apply Rplus_eq_compat_r. rewrite <- minus_IZR. apply IZR_trivial. assumption.
ring. ring. ring. ring. ring. rewrite <- produitIZR in H3.
replace (IZR z1 - IZR (z1 mod z2)) with 
(((IZR z1 - IZR (z1 mod z2)) * / IZR z2) * IZR z2) in H3.
apply Rmult_eq_reg_r in H3. 
replace ((IZR z1 - IZR (z1 mod z2)) * / IZR z2) with
(IZR z1 * / IZR z2 - IZR (z1 mod z2) * / IZR z2) in H3.
assert (H4 : IZR (z1 mod z2) * / IZR z2 < 1).
replace (1) with (IZR z2 * / IZR z2). apply Rmult_lt_compat_r.
apply Rinv_0_lt_compat. apply IZR_lt.
apply inverseltZ. assumption. 
apply IZR_lt. apply Z_mod_lt. assumption. 
rewrite <- Rinv_r_sym. reflexivity. apply neqR.
apply inversegtR. apply IZR_lt. apply inverseltZ. assumption.
apply Ropp_lt_gt_contravar in H4.
rewrite H3. apply Rplus_gt_compat_l. assumption.
ring. apply neqR. apply inversegtR. apply IZR_lt.
apply inverseltZ. assumption.
replace ((IZR z1 - IZR (z1 mod z2)) * / IZR z2 * IZR z2) with
((IZR z1 - IZR (z1 mod z2)) * IZR z2 * / IZR z2).
rewrite Rinv_r_simpl_l. reflexivity. apply neqR.
apply inversegtR. apply IZR_lt. apply inverseltZ. assumption.
ring. Qed.




Lemma ZdivsupgtZdiv : forall z1 z2 z3 z4 : Z,
(z2 > 0)%Z -> (z4 > 0)%Z -> IZR (z1) * / IZR (z2) > IZR(z3) * / IZR (z4) ->
(Zdiv_sup z1 z2 > z3 / z4 )%Z.
Proof. intros z1 z2 z3 z4 H K P. 
unfold Zdiv_sup.
assert (H2 : (z1 mod z2)%Z = (z1 - z1/z2 * z2)%Z).
rewrite Zmod_eq_full. reflexivity. apply ZneqR. assumption.
assert (H3 : IZR (z1 / z2 * z2)= IZR z1 - IZR (z1 mod z2)).
replace (IZR (z1 / z2 * z2)) with (IZR (z1 / z2 * z2) + 0).
replace (IZR z1 - IZR (z1 mod z2)) with
(IZR (z1 / z2 * z2) + IZR z1 - IZR (z1 / z2 * z2) - IZR (z1 mod z2)).
replace (IZR (z1 / z2 * z2) + IZR z1 - IZR (z1 / z2 * z2) - IZR (z1 mod z2)) with
(IZR (z1 / z2 * z2) + (IZR z1 - IZR (z1 / z2 * z2) - IZR (z1 mod z2))).
apply Rplus_eq_compat_l. 
replace (IZR z1 - IZR (z1 / z2 * z2) - IZR (z1 mod z2)) with
(IZR z1 - IZR (z1 / z2 * z2)  + (- IZR (z1 mod z2))).
replace (0) with 
(IZR (z1 mod z2) + (- IZR (z1 mod z2))).
apply Rplus_eq_compat_r. rewrite <- minus_IZR. apply IZR_trivial. assumption.
ring. ring. ring. ring. ring. rewrite <- produitIZR in H3.
replace (IZR z1 - IZR (z1 mod z2)) with 
(((IZR z1 - IZR (z1 mod z2)) * / IZR z2) * IZR z2) in H3.
apply Rmult_eq_reg_r in H3. 
replace ((IZR z1 - IZR (z1 mod z2)) * / IZR z2) with
(IZR z1 * / IZR z2 - IZR (z1 mod z2) * / IZR z2) in H3.
assert (H4 : IZR (z1 mod z2) * / IZR z2 < 1).
replace (1) with (IZR z2 * / IZR z2). apply Rmult_lt_compat_r.
apply Rinv_0_lt_compat. apply IZR_lt.
apply inverseltZ. assumption. 
apply IZR_lt. apply Z_mod_lt. assumption. 
rewrite <- Rinv_r_sym. reflexivity. apply neqR.
apply inversegtR. apply IZR_lt. apply inverseltZ. assumption.
apply Ropp_lt_gt_contravar in H4.
assert (H5 : (z3 mod z4)%Z = (z3 - z3/z4 * z4)%Z).
rewrite Zmod_eq_full. reflexivity. apply ZneqR. assumption.
assert (H6 : IZR (z3 / z4 * z4)= IZR z3 - IZR (z3 mod z4)).
replace (IZR (z3 / z4 * z4)) with (IZR (z3 / z4 * z4) + 0).
replace (IZR z3 - IZR (z3 mod z4)) with
(IZR (z3 / z4 * z4) + IZR z3 - IZR (z3 / z4 * z4) - IZR (z3 mod z4)).
replace (IZR (z3 / z4 * z4) + IZR z3 - IZR (z3 / z4 * z4) - IZR (z3 mod z4)) with
(IZR (z3 / z4 * z4) + (IZR z3 - IZR (z3 / z4 * z4) - IZR (z3 mod z4))).
apply Rplus_eq_compat_l. 
replace (IZR z3 - IZR (z3 / z4 * z4) - IZR (z3 mod z4)) with
(IZR z3 - IZR (z3 / z4 * z4)  + (- IZR (z3 mod z4))).
replace (0) with 
(IZR (z3 mod z4) + (- IZR (z3 mod z4))).
apply Rplus_eq_compat_r. rewrite <- minus_IZR. apply IZR_trivial. assumption.
ring. ring. ring. ring. ring. rewrite <- produitIZR in H6.
replace (IZR z3 - IZR (z3 mod z4)) with 
(((IZR z3 - IZR (z3 mod z4)) * / IZR z4) * IZR z4) in H6.
apply Rmult_eq_reg_r in H6. 
replace ((IZR z3 - IZR (z3 mod z4)) * / IZR z4) with
(IZR z3 * / IZR z4 - IZR (z3 mod z4) * / IZR z4) in H6.
assert (H7 : IZR (z3 mod z4) * / IZR z4 < 1).
replace (1) with (IZR z4 * / IZR z4). apply Rmult_lt_compat_r.
apply Rinv_0_lt_compat. apply IZR_lt.
apply inverseltZ. assumption. 
apply IZR_lt. apply Z_mod_lt. assumption. 
rewrite <- Rinv_r_sym. reflexivity. apply neqR.
apply inversegtR. apply IZR_lt. apply inverseltZ. assumption.
apply Ropp_lt_gt_contravar in H7.
case (Z_zerop (z1 mod z2)). intros Q.
apply inversegtZ. apply lt_IZR.
rewrite H6. rewrite H3. rewrite Q.
replace (IZR z1 * / IZR z2 - 0 * / IZR z2) with
(IZR z1 * / IZR z2 ). assert (H8 : IZR (z3 mod z4) >= 0).
apply inversegeR. apply IZR_le. apply Z_mod_lt. assumption.
assert (H9 : IZR (z3 mod z4) * / IZR z4 >= 0 * / IZR z4).
apply Rmult_ge_compat_r. apply Rgt_ge. apply inversegtR. 
apply Rinv_0_lt_compat. apply IZR_lt. apply inverseltZ. assumption.
assumption. replace (0 * / IZR z4) with (0) in H9.
 apply Ropp_ge_le_contravar in H9. 
assert (H10 : IZR z3 * / IZR z4 - IZR (z3 mod z4) * / IZR z4 <= 
IZR z3 * / IZR z4).
replace (IZR z3 * / IZR z4 - IZR (z3 mod z4) * / IZR z4) with
(IZR z3 * / IZR z4 + (- IZR (z3 mod z4) * / IZR z4)).
replace (IZR z3 * / IZR z4) with (IZR z3 * / IZR z4 + 0).
replace (IZR z3 * / IZR z4 + 0 + - IZR (z3 mod z4) * / IZR z4) with
(IZR z3 * / IZR z4 + - IZR (z3 mod z4) * / IZR z4).
apply Rplus_le_compat_l. rewrite <- Ropp_mult_distr_l. 
replace (0) with (-0). assumption. ring. ring. ring.
ring. apply Rle_lt_trans with (IZR z3 * / IZR z4). assumption.
apply inverseltR. assumption. ring. ring.
intros Q. apply inversegtZ. apply lt_IZR.
assert (H8 : IZR (z3 / z4) <= IZR z3 * / IZR z4).
apply partieentièreinférieure. assumption.
replace (IZR (Z.succ (z1 / z2))) with (IZR(z1 / z2) + 1).
assert (IZR (z3 / z4) < IZR z1 * / IZR z2).
apply Rle_lt_trans with (IZR z3 * / IZR z4). assumption.
apply inverseltR. assumption.
apply Rgt_trans with (IZR z1 * / IZR z2).  
replace (IZR z1 * / IZR z2) with (IZR z1 * / IZR z2 - 1 + 1).
apply Rplus_gt_compat_r. apply Zdiv_inflt. assumption.
ring. apply inversegtR. apply Rle_lt_trans with (IZR z3 * / IZR z4).
assumption. apply inverseltR. assumption. rewrite <- plus_IZR.
apply IZR_trivial. ring. ring. apply neqR. apply inversegtR.
apply IZR_lt. apply inverseltZ. assumption. 
replace ((IZR z3 - IZR (z3 mod z4)) * / IZR z4 * IZR z4) with
((IZR z3 - IZR (z3 mod z4)) * IZR z4 * / IZR z4).
rewrite Rinv_r_simpl_l. reflexivity. apply neqR. apply inversegtR.
apply IZR_lt. apply inverseltZ. assumption. ring. ring.
apply neqR. apply inversegtR. apply IZR_lt. apply inverseltZ.
assumption.
replace ((IZR z1 - IZR (z1 mod z2)) * / IZR z2 * IZR z2) with
((IZR z1 - IZR (z1 mod z2)) * IZR z2 * / IZR z2).
rewrite Rinv_r_simpl_l. reflexivity. apply neqR.
apply inversegtR. apply IZR_lt. apply inverseltZ. assumption.
ring. Qed.





Lemma unplus2surrpositif : forall r : R,
r > 0 -> 1 + 2 * / r > 0.
Proof. intros r H. apply trivial28. replace (1) with (1 + 0).
- replace (1 + 0 + 2 * / r) with (1 + 2 * / r).
+ apply Rplus_gt_compat_l.
apply produitdedeuxpositifsR.
{ lra. }
apply inversegtR. apply Rinv_0_lt_compat.
apply inverseltR. assumption. 
+ ring. 
- ring. Qed.






Lemma ltadditifR : forall r1 r2 r3 r4 : R,
r1 < r2 -> r3 < r4 -> r1 + r3 < r2 + r4.
Proof. intros r1 r2 r3 r4 H1 H2. lra. Qed.







Lemma neqZneqR : forall z1 : Z,
(z1 <> 0)%Z -> IZR z1 <> 0.
Proof.
intros; apply not_0_IZR; assumption.
Qed.

Lemma geandneq : forall r1 r2 : R,
r1 >= r2 -> r1 <> r2 -> r1 > r2.
Proof.
intros r1 r2 Hr1r2; destruct Hr1r2.
trivial.
intros Hnot; elim (Hnot H). 
Qed.

Lemma Zdiv_supgt : forall z1 z2 : Z,
(z2 > 0)%Z -> IZR (Zdiv_sup z1 z2) < IZR z1 * / IZR z2 + 1.
Proof. intros z1 z2 K. unfold Zdiv_sup.
case (Z_zerop (z1 mod z2)).
intros H. rewrite Zmod_eq_full in H.
assert (H3 : IZR (z1) = IZR (z1 / z2 * z2)).
replace (IZR (z1 / z2 * z2)) with (0 + IZR (z1 / z2 * z2)).
replace (IZR z1) with (IZR z1 - IZR (z1 / z2 * z2) + IZR (z1 / z2 * z2)).
apply Rplus_eq_compat_r. rewrite <- minus_IZR. apply IZR_trivial.
assumption. ring. ring. rewrite <- produitIZR in H3.
assert (H4 : IZR z1 * / IZR z2 = (IZR (z1 / z2) * IZR z2) * / IZR z2).
apply Rmult_eq_compat_r. assumption.
rewrite Rinv_r_simpl_l in H4. symmetry in H4. 
rewrite H4. replace (IZR z1 * / IZR z2) with 
(0 + IZR z1 * / IZR z2).
replace (0 + IZR z1 * / IZR z2 + 1) with
(1 + IZR z1 * / IZR z2). apply Rplus_lt_compat_r. lra.
ring. ring. apply neqR. apply inversegtR. apply IZR_lt. apply inverseltZ.
assumption. apply ZneqR. assumption. 
intros H.
replace (Z.succ (z1 / z2)%Z) with (((z1 / z2) + 1)%Z).
rewrite plus_IZR. apply Rplus_lt_compat_r.
assert (H3 : IZR (z1 mod z2) = IZR (z1 - z1 / z2 * z2)).
apply IZR_trivial. rewrite Zmod_eq_full. reflexivity.
apply ZneqR. assumption.
assert (H4 : IZR (z1 mod z2) + IZR (z1 / z2 * z2) = IZR (z1)).
replace (IZR z1) with (IZR z1 - IZR (z1 / z2 * z2) + IZR (z1 / z2 * z2)).
rewrite <- minus_IZR. apply Rplus_eq_compat_r. assumption. ring.
assert (H5 : IZR (z1 / z2 * z2) = IZR z1 - IZR (z1 mod z2)).
replace (IZR z1 - IZR (z1 mod z2)) with (IZR z1 + (- IZR (z1 mod z2))).
replace (IZR (z1 / z2 * z2)) with (IZR (z1 / z2 * z2) + IZR (z1 mod z2) + (- IZR (z1 mod z2))).
apply Rplus_eq_compat_r. rewrite Rplus_comm. assumption.
ring. ring. rewrite <- minus_IZR in H5. 
assert (H6 : IZR (z1 / z2) = (IZR (z1 - z1 mod z2)) * / IZR z2).
replace (IZR (z1 / z2)) with ((IZR (z1 / z2) * IZR z2) * / IZR z2).
apply Rmult_eq_compat_r. rewrite produitIZR. assumption.
apply Rinv_r_simpl_l. apply neqR. apply inversegtR. apply IZR_lt. 
apply inverseltZ. assumption.
replace (IZR (z1 - z1 mod z2) * / IZR z2) with
(IZR z1 * / IZR z2 - IZR (z1 mod z2) * / IZR z2) in H6.
rewrite H6. replace (IZR z1 * / IZR z2) with
(IZR z1 * / IZR z2 + 0).
replace (IZR z1 * / IZR z2 + 0 - IZR (z1 mod z2) * / IZR z2) with
(IZR z1 * / IZR z2 - IZR (z1 mod z2) * / IZR z2).
apply inverseltR. apply Rplus_gt_compat_l.
replace (0) with (-0).
apply Ropp_lt_gt_contravar. apply inverseltR.
apply produitdedeuxpositifsR.
assert (H7 : IZR (z1 mod z2) >= 0).
apply inversegeR. apply IZR_le.
apply Z_mod_lt. assumption. apply geandneq.
assumption.  apply neqZneqR. assumption. 
apply inversegtR. apply Rinv_0_lt_compat. apply IZR_lt.
apply inverseltZ. assumption. ring. 
ring. ring.  
replace (IZR z1 * / IZR z2 - IZR (z1 mod z2) * / IZR z2) with
(/IZR z2 *IZR z1 + /IZR z2 *  (-IZR (z1 mod z2))).
rewrite <- Rmult_plus_distr_l. rewrite Rmult_comm.
apply Rmult_eq_compat_r. rewrite minus_IZR. ring. ring.
ring. Qed.



Lemma lttransitifR : forall r1 r2 r3 : R,
r1 < r2 -> r2 < r3 -> r1 < r3.
Proof. intros r1 r2 r3 H1 H2. lra. Qed.


Lemma lettransitifR : forall r1 r2 r3 : R,
r1 <= r2 -> r2 < r3 -> r1 < r3.
Proof. intros r1 r2 r3 H1 H2. lra. Qed.


Lemma carregeR : forall r1 r2 : R,
r1 > 0 -> r2 > 0 -> r1 >= r2 -> r1 * r1 >= r2 * r2.
Proof. intros r1 r2 H1 H2 H3. apply Rmult_ge_compat.
- apply Rgt_ge. assumption.
- apply Rgt_ge. assumption.
- assumption.
- assumption. Qed.


Lemma trivial47 : forall r1 r2 r3 r4 r5 : R,
r4 > 0 -> r5 <> 0 -> r1 > 0 -> r3 > 0 -> r1 <= r2 -> 1 * / r4 <= 1 * / r5 ->
 r1 * r3 * / r4 <= r2 * r3 * / r5.
Proof. intros r1 r2 r3 r4 r5 H1 H2 H3 H4 H5 H6.  
replace (r1 * r3) with (r3 * r1).
replace (r2 * r3) with (r3 * r2).
replace (r3 * r1 * / r4) with (r3 * (r1 * / r4)).
- replace (r3 * r2 * / r5) with (r3 * (r2 * / r5)).
+ apply Rmult_le_compat_l. 
{ apply Rlt_le. apply inverseltR. assumption. }  
apply Rmult_le_compat. { apply inverseleR. apply Rgt_ge. assumption. }
apply inverseleR. apply Rgt_ge. apply inversegtR. apply Rinv_0_lt_compat.
apply inverseltR. assumption. assumption. 
replace (/ r4) with (1 * / r4). {
replace (/ r5) with (1 * / r5). assumption. ring. }
ring. + ring. 
- ring. 
- ring.
- ring. Qed.




Lemma trivial44 : forall r1 r2 r3 : R,
r1 > 0 -> r2 <= r3 -> r2 * r1 <= r3 * r1.
Proof. intros r1 r2 r3 H1 H2. apply Rmult_le_compat_r.
- apply Rlt_le. apply Rgt_lt. assumption.
- assumption. Qed.
 
Lemma letransitifR : forall r1 r2 r3 : R,
r1 <= r2 -> r2 <= r3 -> r1 <= r3.
Proof. intros r1 r2 r3 H1 H2. lra. Qed.

Lemma trivial32 : forall r1 : R,
r1 > 0 -> 1 + r1 > 0.
Proof. intros r1 H. lra. Qed.





Lemma trivial30 : forall r1 r2 r3 : R,
r1 > 0 -> r2 <= r3 -> r1 * r2 <= r1 * r3.
Proof. intros r1 r2 r3 H1 H2. replace (r1 * r2) with (r2 * r1).
replace (r1 * r3) with (r3 * r1). { apply trivial44. { assumption. } 
assumption. } apply commutativitedeR. apply commutativitedeR. Qed.



Lemma trivial29 : forall r1 r2 : R,
r1 > 0 -> r2 > 0 -> 1 * / r1 >= 1 * / r2 -> 1 * / (r1 * r1) >= 1 * / (r2 * r2).
Proof. intros r1 r2 H3 H4 H5. rewrite Rinv_mult_distr. 
-  replace (1 * (/ r1 * / r1)) with (/ r1 * / r1).
 + replace (1 * / (r2 * r2)) with (/ r2 * / r2). {
apply carregeR.
{ apply inversegtR. apply Rinv_0_lt_compat. apply inverseltR. assumption.
} apply inversegtR. apply Rinv_0_lt_compat. apply inverseltR. assumption.
replace (/ r1) with (1 * / r1).
{ replace (/ r2) with (1 * / r2).
{ assumption. } ring. } ring. } 
rewrite Rinv_mult_distr. { ring. }
apply neqR. assumption. 
apply neqR. assumption. 
+  ring. -
apply neqR. assumption. - 
apply neqR. assumption. Qed.

Lemma Rinv_lt : forall r r1 : R, 0 < r -> 0 < r1 -> r1 < r -> / r < / r1.
Proof.
intros r r1 H1 H2 H3. apply Rinv_lt_contravar. 
+ apply produitdedeuxpositifsR. apply inversegtR. assumption. 
apply inversegtR. assumption. 
+ assumption. Qed.




Lemma Rinv_ge : forall r r1 : R, 0 < r -> 0 < r1 -> r <= r1 ->1 * / r >=1 * / r1.
Proof. intros r r1 H1 H2 H3. 
assert (H4 : r * / r <= r1 * / r).
apply Rmult_le_compat_r. apply inverseleR. apply Rgt_ge. apply inversegtR.
apply Rinv_0_lt_compat. assumption. assumption. 
replace (r * / r) with (/r * r) in H4.
rewrite Rinv_l in H4.
assert (H5 : 1 * / r1 <= (r1 * / r) * / r1).
apply  Rmult_le_compat_r.
apply inverseleR. apply Rgt_ge. apply inversegtR.
apply Rinv_0_lt_compat. assumption. assumption.
rewrite Rinv_r_simpl_m in H5. replace (/ r) with (1 * / r)
in H5. apply inversegeR. assumption. ring. apply neqR. 
apply inversegtR. assumption.
apply neqR. apply inversegtR. assumption.
ring. Qed.





Lemma trivial20 : forall r1 r2 r3 r4 r5 r6 : R,
r1 > 0 -> r6 > 0 -> r5 * / r2 > 1 * / r3 ->  r5  * (r6*r1) * / r2 > r6 * r1 * / r3.
Proof. intros r1 r2 r3 r4 r5 r6 H4 H5 H6.
replace (r5 * (r6 * r1) * / r2) with (r6 * (r1* r5 * / r2)).
- replace (r6 * r1 * / r3) with (r6 * (r1 * / r3)).
+ apply Rmult_gt_compat_l. assumption.
replace (r1 * r5 * / r2) with (r1 * (r5 * / r2)).
{ apply Rmult_gt_compat_l. assumption.
replace (/ r3) with (1 * / r3). assumption. ring. }
ring. + ring. 
- ring. Qed.





Lemma trivial15 : forall r1 r2 r3 : R,
r1 > 0 -> r2 > r3 -> r2 * / r1 > r3 * / r1.
Proof. intros r1 r2 r3 H1 H2. apply Rmult_gt_compat_r.
- apply inversegtR. apply Rinv_0_lt_compat. apply inverseltR.
assumption.
- assumption. Qed. 

Lemma trivial12 : forall r1 r2 : R,
r1 > 0 -> r2 + r1 > r2.
Proof. intros; lra. Qed.

Lemma ge0transitifR : forall r1 r2 : R,
r1 >= r2 -> r2 > 0 -> r1 > 0.
Proof. intros; lra. Qed.





Lemma trivial9 : forall  r2 r3 : R,
-1 + r3 >= -1 + r2 -> r3 >= r2.
Proof. intros; lra. Qed.





Lemma foismoinsungeR : forall r1 r2 : R,
r1 >= r2 -> -r2 >= -r1.
Proof. intros r1 r2 H. apply Ropp_ge_contravar. assumption.
Qed.

Lemma foismoinsungtR : forall r1 r2 : R,
r1 > r2 -> -r2 > -r1.
Proof. intros r1 r2 H. apply Ropp_gt_contravar. assumption.
Qed.





Lemma inversefrac : forall r1 r2 r3 r4 : R,
r3 > 0 -> r4 > 0 -> r1 > 0 -> r2 > 0  -> 
r1 <= r3 -> r2 >= r4 -> r1 * / r2 <= r3 * / r4.

Proof. intros r1 r2 r3 r4 H1 H2 H3 H4 H5 H6. 
apply inverseleR. 
replace (r3 * / r4) with (1 * / (r4 * / r3)).
- replace (r1 * / r2) with (1 * / (r2 * / r1)).
+ apply Rinv_ge. 
{ apply produitdedeuxpositifsR. 
 assumption. apply inversegtR. apply Rinv_0_lt_compat.
 apply inverseltR. assumption. }
{ apply produitdedeuxpositifsR. 
 assumption. apply inversegtR. apply Rinv_0_lt_compat.
 apply inverseltR. assumption. }
apply Rmult_le_compat.
{ apply Rlt_le. apply inverseltR. assumption. }
apply Rlt_le. apply Rinv_0_lt_compat. apply inverseltR. assumption.
{ apply inverseleR. assumption. } 
replace (/ r3) with (1 * / r3).
replace (/ r1) with (1 * / r1).
 apply inverseleR. apply Rinv_ge. assumption. assumption.
assumption. ring. ring. 
+ replace (1 * / (r2 * / r1)) with (/ (r2 * / r1)).
rewrite Rinv_mult_distr. 
{ rewrite Rinv_involutive. ring. apply neqR. assumption. }
{ apply neqR. assumption. }
{ apply neqR. apply inversegtR. apply Rinv_0_lt_compat.
apply inverseltR. assumption. } ring.
- replace (1 * / (r4 * / r3)) with (/ (r4 * / r3)).
rewrite Rinv_mult_distr. 
{ rewrite Rinv_involutive. ring. apply neqR. assumption. }
{ apply neqR. assumption. }
{ apply neqR. apply inversegtR. apply Rinv_0_lt_compat.
apply inverseltR. assumption. } ring. Qed.




Lemma multfraction2 : forall r1 r2 a : R,
r1 * / 2 <= r2 * / 2 -> r1 <= r2.
Proof. intros r1 r2 a H1. lra. Qed.





Lemma inverseR : forall r1 r2 r3 : R,
r1 > 0 -> r2 <> 0 -> r3 <> 0 -> / r2 < / r3 -> r1 * / r2 < r1 * / r3.

Proof.
intros r1 r2 r3 H1 H2 H3 H4. apply inverseltR.
apply Rmult_gt_compat_l. 
- assumption.
- apply inversegtR. assumption. Qed.



Lemma soustractioninegalite : forall z1 z2 : R,
z1 > z2 -> z1 -z2 > 0.
Proof.
intros z1 z2 H. lra. Qed.





Lemma divisiondansfraction : forall z1 z2 z3 : R,
z3 > 0 -> z1 > 0 -> z2 > 0 -> 1 * / z1 >= 1 * / z2 -> z3 * / z1 >= z3 * / z2.
Proof. intros z1 z2 z3 H1 H2 H3 H4. apply Rmult_ge_compat_l.
- apply Rgt_ge. assumption.
- replace (/ z1) with (1 * / z1).
replace (/ z2) with (1 * / z2).
+ assumption.
+ ring.
+ ring. Qed.

Lemma additiongeR : forall r1 r2 r3 : R,
 r1 >= r2 -> r3 + r1 >= r3 + r2.
Proof. intros; lra. Qed.

Lemma additiongtR : forall r1 r2 r3 : R,
 r1 > r2 -> r1 + r3 > r2 + r3.
Proof. intros; lra. Qed.



Lemma trivial46 : forall r1 r2 : R,
r1 > 0 -> r2 > 0 -> r1 * / r2 > 0.
Proof. intros r1 r2 H1 H2. apply produitdedeuxpositifsR.
assumption. apply inversegtR. apply Rinv_0_lt_compat.
apply inverseltR. assumption. Qed.












Lemma neq0impliquerabsneq0 : forall r : R,
r <> 0 -> Rabs r <> 0.
Proof. intros r H. unfold Rabs. destruct (Rcase_abs r).
       apply Ropp_neq_0_compat; assumption.
       assumption.
Qed.

Lemma neqR0 : forall r : R,
Rabs r <> 0 -> Rabs r > 0.
Proof.
unfold Rabs; intros r.
destruct (Rcase_abs r).
intros.
replace 0 with (-0) by ring.

apply Ropp_lt_contravar; assumption.
intros.
destruct r0.
assumption.
elim (H H0).
Qed.




(*                       Inégalité sur R :    FIN  *)













(*                       Inégalite sur Z : DEBUT   *)










Lemma trivial41 : forall  z2 : Z,
(0 < z2)%Z -> (1 <= z2)%Z.
Proof. intros z1 H. omega. Qed.


Lemma trivial40 : forall z z1 z2 z3 z4 : Z,
(z1 + z3 + z4 > z2)%Z -> (z1 + z3 + z4 -z + z > z2)%Z.
Proof. intros; omega. Qed.

Lemma trivial38 : forall z1 z2 z3 : Z,
(z1 + z3 > z2 + z3)%Z -> (z1 > z2)%Z.
Proof. intros z1 z2 z3 H. 
apply inversegtZ. apply lt_IZR.
apply inverseltZ in H. apply IZR_lt in H.
 replace (IZR (z2 + z3)) with (IZR (z3 + z2)) in H.
replace (IZR (z1 + z3)) with (IZR (z3 + z1)) in H.
- rewrite plus_IZR in H.
replace (IZR (z3 + z1)) with (IZR z3 + IZR z1) in H.
+  apply Rplus_lt_reg_l in H. assumption.
+ rewrite plus_IZR. reflexivity.
- rewrite plus_IZR. 
rewrite Rplus_comm. rewrite <- plus_IZR. reflexivity.
- rewrite plus_IZR. 
rewrite Rplus_comm. rewrite <- plus_IZR. reflexivity. Qed.



Lemma trivial34 : forall z : Z,
(z > 1)%Z -> (z * z > 1)%Z.
Proof. intros z H. apply inversegtZ. 
apply lt_IZR. rewrite <- produitIZR.
apply inverseltR. apply carreplusgrandque1R.
- apply inversegtR. apply IZR_lt. apply inverseltZ. assumption.
- apply inversegtR. apply IZR_lt. apply inverseltZ. assumption.
Qed.



Lemma trivial26 : forall z1 z2 : Z,
(z1 > z2)%Z -> (z1 >= z2)%Z.
Proof. intros; omega. Qed.

Lemma trivial25 : forall z1 z2 : Z,
(z1 > z2 + 1)%Z    -> (z1 > z2)%Z.
Proof. intros z1 z2 H. omega. Qed.

Lemma trivial14 : forall z : Z,
(z >= 2 * 2)%Z -> IZR (z) <> 0.
Proof. intros z H. apply neqR.
apply Rge_gt_trans with 4.
- apply inversegeR. apply IZR_le.
apply inverseleZ. assumption.
- lra. Qed.



Lemma superieurausucc : forall z1 z2 : Z,
(Z.succ(z1) <= z2)%Z -> (z1 < z2)%Z.
Proof. intros z1 z2 H. omega. Qed.

Lemma superieurouegalausucc : forall z1 z2 : Z,
(Z.succ(z1) <= z2)%Z -> (z1 <= z2)%Z.
Proof. intros z1 z2 H. omega. Qed.



Lemma Zpower2 : forall z1 z2 : Z,
(z1 > 0)%Z -> (z2>0)%Z -> (z1 >= z2)%Z -> (z1*z1 >= z2*z2)%Z.
Proof. intros z1 z2 H1 H2 H3. apply inversegeZ. apply le_IZR. 
rewrite <- produitIZR. replace (IZR (z1 * z1)) with 
(IZR z1 * IZR z1).
- apply inverseleR. apply carregeR.
+ apply inversegtR. apply IZR_lt. apply inverseltZ. assumption.
+ apply inversegtR. apply IZR_lt. apply inverseltZ. assumption.
+ apply inversegeR. apply IZR_le. apply inverseleZ. assumption.
- rewrite produitIZR. reflexivity. Qed.





Lemma ArithZ : forall z1 z2 : Z,
(z1 > z2)%Z -> (z1 >= z2 + 1)%Z.

Proof.
intros z1 z2 H. omega. Qed.

Lemma ArithZpour1 : forall z1 z2 : Z,
(z1 > 1)%Z -> (z1 >= 2)%Z.

Proof.
intros z1 z2 H. omega. Qed.

Lemma ArithZ2 : forall z1 z2 z3 : Z,
(z1 - z3 > 0)%Z -> (z1 - z3 >= 1)%Z.

Proof.
intros z1 z2 H. omega. Qed.


Lemma ArithZ3 : forall z1 z2 z3 : Z,
(z1 - z3 < 3)%Z -> (z1 - z3 <= 2)%Z.

Proof.
intros z1 z2 H. omega. Qed.



Lemma soustractioninegalite2 : forall z1 z2 z3 : Z,
(z1 + z3 <= z2)%Z  -> (z1 <= z2 - z3)%Z.
Proof. 
intros z1 z2 z3 H. omega. Qed.





(*                       Inégalite sur Z : FIN     *)







(*                      Passer de R à Z ou de Z à R : DEBUT                     *)









Lemma trivial18 : forall z : Z,
(z >= 2 * 2)%Z -> IZR(z)-1 > 0.
Proof. intros z H. apply Rgt_minus.
apply Rge_gt_trans with 4.
- apply inversegeR. apply IZR_le. apply inverseleZ.
assumption. 
- lra. Qed.

Lemma trivial17 : forall z : Z,
(z >= 2 * 2)%Z -> IZR(z) > 0.
Proof. intros z H. apply Rge_gt_trans with 4.
- apply inversegeR. apply IZR_le. apply inverseleZ. assumption. 
- lra. Qed.

Lemma gt_IZR : forall z1 z2 : Z,
IZR(z1) > IZR(z2) -> (z1 > z2)%Z.
Proof. intros z1 z2 H. apply inversegtZ. apply lt_IZR. apply inverseltR. 
assumption. Qed.

Lemma ge_IZR : forall z1 z2 : Z,
IZR(z1) >= IZR(z2) -> (z1 >= z2)%Z.
Proof. intros z1 z2 H.  apply inversegeZ. apply le_IZR. apply inverseleR. 
assumption. Qed.



Lemma trivial_IZR : forall z1 z2 : Z,
IZR z1 = IZR z2 -> z1 = z2.
Proof. intros z1 z2 Hz1z2. apply eq_IZR; assumption. Qed.








(*                      Passer de R à Z ou de Z à R : FIN                     *)





 

(*                       Nat : DEBUT                                           *)


Lemma INR4 : INR 4 = 4.
Proof. rewrite S_INR. rewrite S_INR. rewrite S_INR. 
replace (INR 1) with 1. ring.
reflexivity. Qed.



Lemma Bneq0 : INR B <> 0.
Proof. apply neqR. apply Rge_gt_trans with 4.
- rewrite <- INR4. apply inversegeR. apply le_INR. apply B_sup_4.
- lra. Qed.




 




Lemma Bplusgrandque1 : 1 <= INR B.
Proof. apply Rlt_le. apply Rge_gt_trans with 4.
- apply inversegeR. rewrite <- INR4. apply le_INR. apply B_sup_4.
- lra. Qed.




Lemma NleR : forall n1 n2 : nat,
(n1 <= n2)%nat -> INR n1 <= INR n2.
Proof. intros n1 n2 H. apply le_INR. assumption.
Qed. 



(*                            Nat : FIN                         *)




                          (*         B_power : DEBUT    *)


Lemma Bexpos0 :
 B_powerRZ 0 = 1.
Proof. reflexivity. Qed.


Lemma Bexpos : forall n : Z,
B_powerRZ n > 0.

Proof.
  intros n.
unfold B_powerRZ.
apply powerRZ_lt.
apply INR_B_non_nul.
Qed.

Lemma injectiviteB_powerRZ : forall z1 z2 : Z,
z1 = z2 -> B_powerRZ (z1) = B_powerRZ (z2).
Proof. intros z1 z2 H. unfold B_powerRZ. apply powerRZ_trivial. assumption.
Qed.



Lemma B_powerRZandZofnat : forall z1 : Z, (z1 >= 0)%Z ->
B_powerRZ z1 = IZR (Z.of_nat B^z1).
Proof. intros.
  unfold B_powerRZ. unfold Z.of_nat.
destruct z1.
  unfold powerRZ; simpl; reflexivity.
simpl.
rewrite Z.pow_pos_fold.
rewrite <- positive_nat_Z.
rewrite <- pow_IZR.
simpl.
rewrite INR_IZR_INZ.
reflexivity. assert ((Z.neg p < 0)%Z). apply Pos2Z.neg_is_neg.
assert ((0 > Z.neg p)%Z <-> False). apply neg_false.
apply Zle_not_gt. apply inverseleZ. assumption.
assert (False). apply H1. apply inversegtZ. assumption. inversion H2.
Qed.



Lemma B_powerRZ1 : B_powerRZ 1  = INR B.
Proof. apply powerRZ_1. Qed.

Lemma Bge4 : B_powerRZ 1 >= 4.
Proof. rewrite B_powerRZ1. apply inversegeR. rewrite <- INR4. apply le_INR.
apply B_sup_4. Qed.


Lemma produitB_powerRZ : forall z1 z2 : Z,
B_powerRZ z1 * B_powerRZ z2=B_powerRZ (z1 + z2).
Proof. intros z1 z2. unfold B_powerRZ. 
rewrite powerRZ_add. - reflexivity.
- apply Bneq0. Qed. 




Lemma inverseB_power : forall z : Z, (z >= 0)%Z ->
IZR(B_powerZ z)=B_powerRZ z.
Proof. intros z H. unfold B_powerRZ. unfold B_powerZ. 
rewrite B_powerRZandZofnat. reflexivity. assumption.
Qed. 




Lemma quotientB_powerZ2 : forall z1 z2 : Z,
(2 * B_powerRZ (z1)) * / B_powerRZ (z2) = 2 * B_powerRZ (z1 + (-z2)).
Proof. intros z1 z2. unfold B_powerRZ. rewrite Rinv_powerRZ. { 
replace (powerRZ (INR B) z1) with (B_powerRZ z1).
replace (powerRZ (INR B) (-z2)) with (B_powerRZ (-z2)).
- replace (powerRZ (INR B) (z1 + - z2)) with (B_powerRZ (z1 + - z2)).
+
rewrite <- produitB_powerRZ. ring. 
+ trivial.
- trivial.
- trivial.
} apply Bneq0. Qed.


Lemma Bexposgt1 : forall n : Z,
 (n > 0)%Z -> B_powerRZ n > 1.

Proof.
intros n H. unfold B_powerRZ. apply inversegtR. apply powerRZ_lt_1. 
apply Rge_gt_trans with (4). rewrite <- B_powerRZ1.
apply Bge4. lra. apply inverseltZ. assumption. Qed.











(* B_power : FIN *)


                     (* résultat sur msd : DEBUT *)


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

                 (* résultat sur msd : FIN *)







Lemma negdif0 : forall r : R, r < 0 -> r <> 0.
Proof. intros r H. apply Rlt_not_eq. assumption. Qed.


Lemma Zabssgn : forall n : Z, (Z.abs n = n * (Z.sgn n))%Z.
Proof. intros n. rewrite Z.sgn_abs. reflexivity. Qed.



Lemma xdif0 :
forall x : R, x <> 0 -> x > 0 \/ x < 0.
Proof. intros x H. assert (H2 : x < 0 \/ x > 0). apply Rdichotomy. assumption.
inversion H2. apply or_intror. assumption. apply or_introl. assumption. 
Qed.


Lemma opposedif0 : forall z : Z,
(z <> 0)%Z -> (-z <> 0)%Z.
Proof. intros; omega. Qed.


Lemma divoppose3 : forall b c : Z,
(b mod -c = 0)%Z -> (b mod c = 0)%Z.
Proof. intros b c H2.
replace (c%Z) with ((--c)%Z). apply Z_mod_zero_opp_r. assumption.
ring. Qed.




Lemma divoppose2 : forall b c : Z,
(c <> 0)%Z ->  (b mod c <> 0)%Z -> ((b / c) + 1  = -(b / -c))%Z.
Proof. intros b c H H2.
rewrite Z_div_nz_opp_r. ring. assumption. Qed.




 

Lemma divoppose4 : forall b c : Z,
 (b mod -c <> 0)%Z -> (b mod c <> 0)%Z.
Proof. intros b c.
assert (contra : forall A B : Prop, (~A -> ~B) -> (B -> A)).
intros A B H2. apply Classical_Prop.or_to_imply.
apply Classical_Prop.imply_to_or in H2.
apply or_comm. apply Classical_Prop.imply_and_or2 with (~~A).
apply Classical_Prop.NNPP. assumption.
 apply contra.
assert (divop3 :  (b mod c = 0)%Z -> (b mod -c = 0)%Z).
apply Z_mod_zero_opp_r. 
intros H. assert (zdif0 : forall z : Z, ~(z <> 0)%Z <-> (z = 0)%Z).
intros z. apply Z.eq_dne. apply Z.eq_dne.
apply divop3. apply Z.eq_dne in H. assumption. Qed.







Lemma divoppose : forall b c : Z,
(c <> 0)%Z ->((b mod c = 0)%Z) -> (b / -c = -(b / c))%Z.
Proof. intros b c H H3. rewrite Zmod_eq_full in H3.
assert (H2 : ((b mod -c = 0)%Z)).
apply divoppose3. 
 rewrite Zmod_eq_full. 
replace ((--c)%Z) with ((c)%Z). assumption.
ring. replace ((--c)%Z) with ((c)%Z). assumption.
ring. rewrite Zmod_eq_full in H2.
assert (H4 : (b= b / c * c)%Z).
apply trivial_IZR. rewrite <- produitIZR. 
replace (IZR (b / c) * IZR c) with (0 + IZR (b / c) * IZR c).
replace (IZR b) with (IZR b - IZR (b / c) * IZR c + IZR (b / c) * IZR c).
apply Rplus_eq_compat_r. rewrite produitIZR. rewrite <- minus_IZR.
apply IZR_trivial. assumption. ring. ring.
assert (H5 : (b= b / -c * -c)%Z).
apply trivial_IZR. rewrite <- produitIZR. 
replace (IZR (b / -c) * IZR (-c)) with (0 + IZR (b / -c) * IZR (-c)).
replace (IZR b) with (IZR b - IZR (b / -c) * IZR (-c) + IZR (b / -c) * IZR (-c)).
apply Rplus_eq_compat_r. rewrite produitIZR. rewrite <- minus_IZR.
apply IZR_trivial. assumption. ring. ring.
assert (H6 : IZR b * / IZR c = IZR (b / c)).
replace (IZR (b / c)) with (IZR (b / c) * IZR c * / IZR c).
apply Rmult_eq_compat_r. rewrite produitIZR. apply IZR_trivial. assumption.
rewrite Rinv_r_simpl_l. reflexivity. 
apply neqZneqR. assumption.
assert (H7 : IZR b * / IZR (-c) = IZR (b / -c)).
replace (IZR (b / -c)) with (IZR (b / -c) * IZR (-c) * / IZR (-c)).
apply Rmult_eq_compat_r. rewrite produitIZR. apply IZR_trivial. assumption.
rewrite Rinv_r_simpl_l. reflexivity. 
apply neqZneqR. apply opposedif0. assumption.
replace (IZR b * / IZR (- c)) with (-IZR b * / IZR c) in H7.
apply trivial_IZR. rewrite <- H7.
replace (IZR (- (b / c))) with (-IZR ( (b / c))).
rewrite <- H6. ring. replace (- IZR (b / c)) with
(0 - IZR (b / c)). rewrite <- minus_IZR. apply IZR_trivial.
ring. ring. replace (IZR (- c)) with (-IZR (c)). 
rewrite <- Ropp_mult_distr_l.
replace (IZR b * / - IZR c) with (/ - IZR c * IZR b).
replace (/ - IZR c) with (- / IZR c).
rewrite <- Ropp_mult_distr_l. rewrite Rmult_comm. reflexivity.
rewrite Ropp_inv_permute. reflexivity. 
apply neqZneqR. assumption. ring. 
replace (- IZR c) with (0 - IZR c).
rewrite <- minus_IZR. apply IZR_trivial. ring.
ring. apply opposedif0. assumption. assumption. Qed.








Lemma Zdiv_sup_opp :
forall b c : Z, (c < 0)%Z -> (Z.sgn c * Zdiv_sup b (Z.abs c))%Z = (b / c)%Z.
Proof. intros b c H. unfold Zdiv_sup.
case (Z_zerop (b mod Z.abs c)). intros H2.
 rewrite Z.sgn_neg. rewrite Zabssgn. rewrite Z.sgn_neg.
replace (((c * -1))%Z) with ((-c)%Z). 
replace ((-1 * (b / - c))%Z) with ((-(b / - c))%Z).
rewrite divoppose.  ring. replace (c%Z) with ((--c)%Z).
apply opposedif0. apply ZneqR. 
apply gt_IZR. replace (IZR (- c)) with (-IZR (c)).
replace (0) with (0 + IZR c + - IZR c).
replace (- IZR c) with (0 + -  IZR c).
replace (0 + IZR c + (0 + - IZR c)) with (IZR c + - IZR c).
apply Rplus_gt_compat_r. apply inversegtR. apply IZR_lt. assumption.
ring. ring. ring. replace (- IZR c) with (0 - IZR c).
rewrite <- minus_IZR. apply IZR_trivial. ring. ring.
ring. apply divoppose3. 
rewrite Zabssgn in H2. 
rewrite Z.sgn_neg in H2.  replace ((c * -1)%Z) with 
((-c)%Z) in H2. assumption.  
ring. assumption. ring. ring. assumption. assumption.
 intros H2. rewrite Zabssgn in H2. rewrite Zabssgn.
rewrite Z.sgn_neg in H2. rewrite Z.sgn_neg. 
replace ((c * -1)%Z) with ((-c)%Z).
replace ((Z.succ (b / - c))%Z) with (((b / - c) + 1)%Z).
apply trivial_IZR. rewrite <- produitIZR. rewrite plus_IZR.
rewrite Rmult_plus_distr_l. replace (-1 * IZR (b / - c)) with
(-IZR (b / - c)). replace (-1 * 1) with (-1). 
replace (IZR (b / c)) with (IZR (b / c) + 1 + -1).
replace (IZR (b / c) + 1) with (IZR (b / c + 1)).
apply Rplus_eq_compat_r. replace (- IZR (b / - c)) with
(IZR (-(b / - c))). apply IZR_trivial. symmetry. apply divoppose2.
apply Z.lt_neq. assumption.
apply divoppose4. replace ((c * -1)%Z) with ((-c)%Z) in H2. assumption. ring.
replace (- IZR (b / - c)) with (0 - IZR (b / - c)).
rewrite <- minus_IZR. apply IZR_trivial. ring. ring.
rewrite plus_IZR. reflexivity. ring. ring. ring.
ring. ring. assumption. assumption. Qed.




Lemma Rabsunsurx : forall x : R, x <> 0 -> Rabs (1 * / x) = 1 * / Rabs x.
Proof. intros r H. rewrite <- Rabsolu_sg. rewrite <- Rabsolu_sg.
assert (H2 : r > 0 \/ r < 0). apply xdif0. assumption.
inversion H2. rewrite sg_pos. rewrite sg_pos.
replace (IZR (Z.succ 0)) with (1). replace (1 * r) with (r).
ring. ring. apply IZR_trivial. ring. assumption. replace (1 * / r) with
(/ r). apply inversegtR. apply Rinv_0_lt_compat. apply inverseltR.
assumption. ring. rewrite sg_neg. rewrite sg_neg. 
replace (1 * / (-1 * r)) with ( / (-1 * r)).
rewrite Rinv_mult_distr. rewrite <- Rmult_assoc.  
replace (-1 * 1 * / r) with (-1 * / r). apply Rmult_eq_compat_r.
replace (/ -1) with (- 1 * / 1).
replace (-1 * / 1) with (-(1 * / 1)).
 rewrite <- Rinv_r_sym. ring. apply neqR. lra.
ring. replace (/ -1) with (- / 1). replace (/ 1) with (1 * / 1). 
rewrite <- Rmult_assoc. replace (- (1 * / 1)) with 
(- 1 * (1 * / 1)). rewrite <- Rmult_assoc. reflexivity. 
ring. ring.  rewrite Ropp_inv_permute. replace (- (1)) with (-1). reflexivity.
ring.  apply neqR. lra. ring. apply negdif0.
lra. assumption. ring. assumption. replace (1 * / r) with
(/ r). apply Rinv_lt_0_compat. assumption. ring. Qed.
