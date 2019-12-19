Require Import Reals.
Require Export definition.
(*Require Export definition2.*)
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
Require Import Psatz.
Require Import Zarith_operations.
Require Import Rbase_operations.
Require Import inverse_lemma.
Require Import Coq.ZArith.Zeuclid.
Require Import ZArith.
Require Import Rlog.

Lemma inverse_correct :
forall (x : R) (xc : Reelc) (msdx : Z),
msd_prop xc msdx ->
x <> 0 -> encadrement xc x -> encadrement (inverse_reelc xc msdx) (1 * / x).

Proof.
intros x xc msdx msd_p H.
unfold encadrement in |- *; intros H0 n.
unfold inverse_reelc.
case (Z_le_gt_dec n (- msdx)).
intros; simpl in |- *.
RingReplace (0 - 1) (-1); RingReplace (0 + 1) 1.
apply Rbase_doubles_inegalites.Rabsolu_def3.
rewrite Rabs_mult.
apply Rle_lt_trans with (Rabs (1 * / x) * Rabs (B_powerRZ (- msdx))).
apply Rmult_le_compat_l.
apply Rabs_pos.
unfold B_powerRZ in |- *.
apply Rsqr_le_abs_0.
apply Rsqr_incr_1;
 [ idtac
 | apply Rlt_le; apply powerRZ_lt; apply INR_B_non_nul
 | apply Rlt_le; apply powerRZ_lt; apply INR_B_non_nul ].
apply Rle_powerRZ; [ idtac | auto ].
RingReplace 1 (INR 1); apply le_INR; generalize B_sup_4; omega.
rewrite <- Rabs_mult.
apply Rlt_le_trans with (1 * / (IZR (Z.abs (xc msdx)) - 1)).
apply Rlt_2_to_Rlt with (1 * / (IZR (Z.abs (xc msdx)) + 1)).
rewrite Rmult_assoc; rewrite Rabs_mult.
rewrite Rabs_R1.
rewrite Rabs_mult.
replace (Rabs (/ x)) with (/ Rabs x);
 [ idtac | symmetry  in |- *; apply Rabs_Rinv; auto ].
unfold B_powerRZ in |- *.
replace (Rabs (powerRZ (INR B) (- msdx))) with (/ powerRZ (INR B) msdx). 
replace (/ Rabs x * / powerRZ (INR B) msdx) with
 (/ (Rabs x * powerRZ (INR B) msdx)).
apply Rlt_2_Rinv.
rewrite <- plus_IZR; apply Rlt_gt.
apply IZR_lt.
apply Z.lt_trans with 1%Z.
auto with zarith.
apply Zlt_O_minus_lt.
rewrite Z.add_simpl_r.
now apply Z.lt_trans with 1%Z; [ omega | apply msd_c_ter ].
apply Rmult_gt_0_compat.
apply Rlt_gt; apply Rabs_pos_lt; auto.
apply Rlt_gt; apply powerRZ_lt; apply INR_B_non_nul.
apply Rlt_gt; apply Rlt_sub_compatibility.
RingReplace (0 + 1) 1.
now apply IZR_lt; apply msd_c_ter.
cut (encadrement (absolue_reelc xc) (Rabs x)).
unfold encadrement in |- *.
intro.
generalize (H1 msdx).
unfold absolue_reelc in |- *; unfold B_powerRZ in |- *; auto.
apply absolue_correct; auto.
apply Rinv_mult_distr.
apply Rabs_no_R0; auto.
apply powerRZ_INR_B_non_nul.
transitivity (powerRZ (INR B) (- msdx)).
apply Rinv_powerRZ.
apply Rgt_not_eq; apply Rlt_gt; apply INR_B_non_nul.
symmetry  in |- *; apply Rabs_pos_eq.
apply Rlt_le; apply powerRZ_lt; apply INR_B_non_nul.
rewrite Rmult_comm; apply Rle_Rinv_monotony.
apply Rlt_sub_compatibility.
RingReplace (0 + 1) 1.
now apply IZR_lt; apply msd_c_ter.
rewrite RIneq.Rmult_1_r.
apply Rle_add_compatibility.
rewrite <- plus_IZR; apply IZR_le.
now apply (Zlt_le_succ 1); apply msd_c_ter.


 intro.







assert (Hk: (n + 2*msdx +1 > msdx +1)%Z).
omega.
assert (Habs:(Z.abs (xc (n + 2 * msdx + 1)) > 1)%Z).
assert (n+2*msdx +1>=msdx)%Z.
omega.

assert (encadrement : (B_powerZ ((n + 2 * msdx + 1) - msdx) <= (Z.abs (xc (n + 2 * msdx + 1))) <=
(2*(Z_of_nat B)+1)*(B_powerZ ((n + 2 * msdx + 1)-msdx)))%Z  ).

apply msd_d with x. assumption.
apply inversegeZ. apply le_IZR. apply Rlt_le. apply IZR_lt.
apply lt_IZR. apply Rplus_lt_reg_r with (1). rewrite <- plus_IZR.
rewrite <- plus_IZR. apply inverseltR. 
apply Rgt_trans with (IZR (n + 2 * msdx + 1 )). apply inversegtR.
apply IZR_lt. omega. apply inversegtR. apply IZR_lt.
apply inverseltZ.

 assumption. assumption. assumption.

inversion encadrement.


assert (Bgt : (B_powerZ (n + 2 * msdx + 1 - msdx) > B_powerZ (1) )%Z ).

apply inversegtZ. apply lt_IZR. rewrite inverseB_power. rewrite inverseB_power.


apply powerRZ_croissance.
rewrite <- B_powerRZ1. apply Rlt_le_trans with (4). lra. apply inverseleR. 
apply Bge4.

assert (H4 : IZR (- msdx) + IZR (msdx + 1) < IZR n + IZR (msdx + 1)).

apply Rplus_lt_compat_r. apply IZR_lt. apply inverseltZ. assumption. 
replace (IZR (- msdx) + IZR (msdx + 1)) with (IZR 1) in H4.
rewrite <- plus_IZR in H4. apply lt_IZR.
replace (IZR (n + 2 * msdx + 1 - msdx)) with 
(IZR (n + (msdx + 1))). assumption. apply IZR_trivial. ring.
rewrite <- plus_IZR. apply IZR_trivial. ring. 
replace ((n + 2 * msdx + 1 - msdx)%Z) with 
((n + msdx + 1)%Z). apply inversegeZ. apply le_IZR.
apply Rle_trans with (IZR (n + msdx)). apply Rlt_le.
replace (0) with (IZR(-msdx + msdx)). 
rewrite plus_IZR. rewrite plus_IZR. apply Rplus_lt_compat_r.
apply IZR_lt. apply inverseltZ. assumption. apply IZR_trivial. 
ring. rewrite plus_IZR. rewrite plus_IZR. rewrite plus_IZR.
lra. ring. omega.

assert (H5 : (Z.abs (xc (n + 2 * msdx + 1)) > B_powerZ 1)%Z).
apply inversegtZ. apply lt_IZR. apply Rlt_le_trans with 
(IZR ((B_powerZ (n + 2 * msdx + 1 - msdx)))). apply IZR_lt.
 apply inverseltZ. assumption. apply IZR_le. assumption.
apply inversegtZ. apply lt_IZR. apply inverseltR.
 apply Rgt_trans with (IZR (B_powerZ 1)). 
apply inversegtR. apply IZR_lt. apply inverseltZ. assumption.
rewrite inverseB_power.  apply inversegtR.
apply Rlt_le_trans with (4). lra.
apply inverseleR. apply Bge4. omega.







set
(alpha :=
(Z_of_nat B ^ (2 * n + 2 * msdx + 1) /
(Z.abs (xc (n + 2 * msdx + 1)) + 1))%Z)
in *.
set
(beta :=
Zdiv_sup
(B_powerZ (2 * n + 2 * msdx + 1))
(Z.abs (xc (n + 2 * msdx + 1)%Z) - 1))
in *.





















assert (Halphabeta:(1 <= beta - alpha <= 2)%Z).
(* cela se prouve en utilisant ce qui est ecrit dans la partie 2
de la preuve du theoreme 16 *)





assert (H222:(0 < beta - alpha < 3)%Z).

assert(H4: (0 < Z.abs (xc (n + 2 * msdx + 1)) - 1)%Z).

- omega.


-assert (H5: (0 < Z.abs (xc (n + 2* msdx + 1 )) + 1)%Z).
+ omega.

+ assert (H6: (Z.abs (xc (n + 2* msdx + 1 )) - 1 < Z.abs (xc (n + 2* msdx + 1 )) + 1 )%Z).

{ omega. }



{assert (H8:  / IZR (Z.abs(xc (n + 2* msdx + 1 )) + 1)%Z <  / IZR (Z.abs(xc (n + 2* msdx + 1 )) - 1)%Z).

{ apply (Rinv_lt (IZR (Z.abs(xc (n + 2* msdx + 1 )) + 1)%Z) (IZR (Z.abs(xc (n + 2* msdx + 1 )) - 1)%Z)).
{  replace 0 with (IZR 0). apply IZR_lt. { assumption. }
{ trivial. } }
+ apply IZR_lt. assumption. 
+ apply IZR_lt. omega. }

assert (H7:  (B_powerRZ (2 * n + 2 * msdx + 1)) * / IZR (Z.abs(xc (n + 2* msdx + 1 )) + 1)%Z <
(B_powerRZ (2 * n + 2 * msdx + 1)) * / IZR (Z.abs(xc (n + 2* msdx + 1 )) - 1)%Z).

{ apply inverseR.
{ unfold B_powerRZ. apply Bexpos. }

{ apply neqR. apply inversegtR. apply IZR_lt. assumption. }
{ apply neqR. apply inversegtR. apply IZR_lt. assumption. }

 apply H8. }


 {assert (H10 : (Z.abs (xc (n + 2 * msdx + 1)) >= Z.succ(1))%Z). { apply ArithZ. assumption. }



assert (H11 : (Z.abs (xc (n + 2 * msdx + 1))*Z.abs (xc (n + 2 * msdx + 1)) >= 2 * 2)%Z).

 { 
apply Zpower2. { omega. }
{omega. } omega. }


{ assert (H12 :(B_powerRZ (2 * n + 2 * msdx + 1)) * / IZR (Z.abs(xc (n + 2* msdx + 1 )) - 1)%Z -
 (B_powerRZ (2 * n + 2 * msdx + 1)) * / IZR (Z.abs(xc (n + 2* msdx + 1 )) + 1)%Z > 0).

{ apply soustractioninegalite. assumption. }


assert (H13 : (B_powerRZ (2 * n + 2 * msdx + 1)) * / IZR (Z.abs(xc (n + 2* msdx + 1 )) - 1)%Z -
 (B_powerRZ (2 * n + 2 * msdx + 1)) * / IZR (Z.abs(xc (n + 2* msdx + 1 )) + 1)%Z = 
(2*B_powerRZ (2 * n + 2 * msdx + 1)) * / 
IZR (Z.abs(xc (n + 2* msdx + 1 ))*Z.abs(xc (n + 2* msdx + 1 )) - 1)%Z).


{ rewrite produitencroix. 

replace (IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) - 1) * IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) + 1))
with (IZR (Z.abs (xc (n + 2 * msdx + 1)%Z)*Z.abs (xc (n + 2 * msdx + 1)%Z) - 1)).

 {apply fractionsurR. { apply neqR.
  apply IZR_lt. apply superieurausucc. apply superieurouegalausucc.
apply superieurouegalausucc. apply soustractioninegalite2. apply inverseleZ. apply H11. }
rewrite factorisationR.

 replace (IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) + 1) - IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) - 1)) with (2).

{ ring. } rewrite simplificationIZR.  apply IZR_eq. omega. } rewrite factorisationR2.
apply IZR_eq.  { omega. } 

apply neqR. { apply inversegtR. apply IZR_lt. apply inverseltZ. 
replace ((Z.abs (xc (n + 2 * msdx + 1)) - 1)%Z) with ((Z.abs (xc (n + 2 * msdx + 1)) + (- 1))%Z).
replace (0%Z) with ((1 + (-1))%Z).
apply inversegtZ. apply lt_IZR. apply inverseltR. rewrite plus_IZR. rewrite plus_IZR.
apply Rplus_gt_compat_r. apply inversegtR. apply IZR_lt. apply inverseltZ. assumption.
ring. ring. }
 

apply neqR. apply inversegtR. apply IZR_lt. assumption.  }


assert (H14 : 2 * / (IZR (Z.abs(xc (n + 2* msdx + 1 ))%Z) * 
IZR(Z.abs(xc (n + 2* msdx + 1 ))%Z)) <= 1 * / 2).

{ apply multfraction2. assumption.


rewrite Rinv_r_simpl_m.


 replace (1 * / 2 * / 2) with (1 * / 4).
{  
 { 

replace (/ (IZR (Z.abs (xc (n + 2 * msdx + 1)%Z)) * IZR (Z.abs (xc (n + 2 * msdx + 1)%Z)))) with
(1 * / (IZR (Z.abs (xc (n + 2 * msdx + 1)%Z)) * IZR (Z.abs (xc (n + 2 * msdx + 1)%Z)))). {


apply inversefrac.  { lra. } lra. lra.

{ apply produitdedeuxpositifsR.

apply trivial28. apply inversegtR. apply IZR_lt. apply inverseltZ. assumption.
apply trivial28. apply inversegtR. apply IZR_lt. apply inverseltZ. assumption. }
lra.

 replace (4) with (2 * 2). {  apply carregeR. {

apply trivial28. apply inversegtR. apply IZR_lt. apply inverseltZ. assumption. }

lra. apply inversegeR. apply IZR_le. apply inverseleZ.

apply ArithZpour1. - trivial. 
- assumption. } ring. }   ring. } }
- apply trivialee. 
- apply neqR. lra. }
 
assert (H15 : -(2 * / IZR (Z.abs (xc (n + 2 * msdx + 1)%Z)*Z.abs (xc (n + 2 * msdx + 1)%Z) )) >= -(1 * / 2)). 


{ apply foismoinsungeR. apply inversegeR. rewrite <- produitIZR. assumption. }


assert(H16 : 1 - (2 * / IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) *
 Z.abs (xc (n + 2 * msdx + 1)%Z) )) >= 1 * / 2).


{apply trivial9. replace (-1 + 1 * / 2) with (-(1 * / 2)).
replace (-1 + (1 - 2 * / IZR (Z.abs (xc (n + 2 * msdx + 1)%Z)*Z.abs (xc (n + 2 * msdx + 1)%Z) ))) with
(- (2 * / IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) * Z.abs (xc (n + 2 * msdx + 1)%Z)))). { assumption. }
ring. apply trivial10. }

assert (H17 : 1 - 2 * / IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) * Z.abs (xc (n + 2 * msdx + 1)%Z)) > 0).

apply ge0transitifR with (1 * / 2). { assumption. } lra.  


assert (H18 : IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) * Z.abs (xc (n + 2 * msdx + 1)%Z)) + 
(1 - 2 * / IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) * Z.abs (xc (n + 2 * msdx + 1)%Z)))
> IZR(Z.abs (xc (n + 2 * msdx + 1)%Z) * Z.abs (xc (n + 2 * msdx + 1)%Z))).


 apply trivial12. { assumption. }

assert (H19 : (IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) * Z.abs (xc (n + 2 * msdx + 1)%Z))-1) * 
(1 + 2 * / IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) * Z.abs (xc (n + 2 * msdx + 1)%Z))) >
 IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) * Z.abs (xc (n + 2 * msdx + 1)%Z))).

replace ((IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) * Z.abs (xc (n + 2 * msdx + 1)%Z))-1) * 
(1 + 2 * / IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) * Z.abs (xc (n + 2 * msdx + 1)%Z)))) with 
(IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) * Z.abs (xc (n + 2 * msdx + 1)%Z)) + 
(1 - 2 * / IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) * Z.abs (xc (n + 2 * msdx + 1)%Z)))).

assumption. { rewrite trivial13.

 replace (2 * IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) * Z.abs (xc (n + 2 * msdx + 1)%Z)) * /
 IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) * Z.abs (xc (n + 2 * msdx + 1)%Z))) with (2).


 { replace ( 1 * 2) with (2). replace (1 * 1) with (1).
{ring. }ring. ring. }

 replace (2 * IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) * Z.abs (xc (n + 2 * msdx + 1)%Z)) * /
 IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) * Z.abs (xc (n + 2 * msdx + 1)%Z)))

with (2 * (IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) * Z.abs (xc (n + 2 * msdx + 1)%Z)) * /
 IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) * Z.abs (xc (n + 2 * msdx + 1)%Z)))).

{
 rewrite fracdersurr.  ring. apply trivial14. assumption. } ring. }


assert (H20 : ((IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) * Z.abs (xc (n + 2 * msdx + 1)%Z)) - 1) *
 (1 + 2 * / IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) * Z.abs (xc (n + 2 * msdx + 1)%Z)))) * / 
(IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) * Z.abs (xc (n + 2 * msdx + 1)%Z))*
(IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) * Z.abs (xc (n + 2 * msdx + 1)%Z))-1)) >
      IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) * Z.abs (xc (n + 2 * msdx + 1)%Z)) * / 
(IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) * Z.abs (xc (n + 2 * msdx + 1)%Z))*
(IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) * Z.abs (xc (n + 2 * msdx + 1)%Z))-1))).


{ apply trivial15. { apply produitdedeuxpositifsR. { apply trivial17. assumption. } 
apply trivial18. assumption. } assumption. }


assert (Lemme : 2*B_powerRZ (2 * n + 2 * msdx + 1) * /
 IZR (Z.abs(xc (n + 2* msdx + 1 )) * Z.abs(xc (n + 2* msdx + 1 )) - 1)%Z < 
(1 + 2 * / IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) * Z.abs (xc (n + 2 * msdx + 1)%Z))) *
(2*B_powerRZ (2 * n + 2 * msdx + 1)) * /
 IZR (Z.abs(xc (n + 2* msdx + 1 )) * Z.abs(xc (n + 2* msdx + 1 )))%Z).







 

replace (IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) * Z.abs (xc (n + 2 * msdx + 1)%Z)) *
      / (IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) * Z.abs (xc (n + 2 * msdx + 1)%Z)) * 
(IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) * Z.abs (xc (n + 2 * msdx + 1)%Z)) - 1))) 
with (1 * / (IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) * Z.abs (xc (n + 2 * msdx + 1)%Z)) - 1)) in H20.

 {

replace ((IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) * Z.abs (xc (n + 2 * msdx + 1)%Z)) - 1) * 
(1 + 2 * / IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) * Z.abs (xc (n + 2 * msdx + 1)%Z))) *
      / (IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) * Z.abs (xc (n + 2 * msdx + 1)%Z)) * 
(IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) * Z.abs (xc (n + 2 * msdx + 1)%Z)) - 1)))
with ((1 + 2 * / IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) * Z.abs (xc (n + 2 * msdx + 1)%Z))) * / 
IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) * Z.abs (xc (n + 2 * msdx + 1)%Z))) in H20. 

{

apply inverseltR. 
replace ((1 + 2 * / IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) * Z.abs (xc (n + 2 * msdx + 1)%Z))) * 
2 * B_powerRZ (2 * n + 2 * msdx + 1)) with 
(2 * B_powerRZ (2 * n + 2 * msdx + 1) * 
(1 + 2 * / IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) * Z.abs (xc (n + 2 * msdx + 1)%Z)))). {



 apply trivial20. 
{ assumption. } {  apply Bexpos. } lra. 

 
replace (IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) * Z.abs (xc (n + 2 * msdx + 1)%Z)  - 1))
with ((IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) * Z.abs (xc (n + 2 * msdx + 1)%Z)) - 1)). 
{ assumption. } rewrite trivial22. reflexivity. }
ring. } 


replace ((IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) * Z.abs (xc (n + 2 * msdx + 1)%Z)) - 1) *
 (1 + 2 * / IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) * Z.abs (xc (n + 2 * msdx + 1)%Z))) *
/ (IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) * Z.abs (xc (n + 2 * msdx + 1)%Z)) *
 (IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) * Z.abs (xc (n + 2 * msdx + 1)%Z)) - 1))) with
((1 + 2 * / IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) * Z.abs (xc (n + 2 * msdx + 1)%Z))) * / 
IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) * Z.abs (xc (n + 2 * msdx + 1)%Z))).


{ reflexivity. } rewrite trivial23. reflexivity.  { apply neqR. apply soustractioninegalite.
rewrite <- produitIZR. apply carreplusgrandque1R. 
apply inversegtR. apply IZR_lt. apply inverseltZ. assumption.
apply inversegtR. apply IZR_lt. apply inverseltZ. assumption. }

apply neqR. rewrite <-  produitIZR. apply produitdedeuxpositifsR.


apply trivial28. apply inversegtR. apply IZR_lt. apply inverseltZ. assumption.
apply trivial28. apply inversegtR. apply IZR_lt. apply inverseltZ. assumption.
}
rewrite trivial24. reflexivity. { 
apply neqR. rewrite <-  produitIZR. apply produitdedeuxpositifsR.
apply trivial28. apply inversegtR. apply IZR_lt. apply inverseltZ. assumption.
apply trivial28. apply inversegtR. apply IZR_lt. apply inverseltZ. assumption. }

{apply neqR. apply soustractioninegalite.
rewrite <- produitIZR. apply carreplusgrandque1R.
apply inversegtR. apply IZR_lt. apply inverseltZ. assumption.
apply inversegtR. apply IZR_lt. apply inverseltZ. assumption. }


assert (H21 : (n + 2 * msdx + 1 > msdx)%Z).


{ apply trivial25. assumption. }


assert (H22 : (B_powerZ ((n + 2 * msdx + 1) - msdx) <= (Z.abs (xc (n + 2 * msdx + 1))) <=
(2*(Z_of_nat B)+1)*(B_powerZ ((n + 2 * msdx + 1)-msdx)))%Z).


{ apply msd_d with x. assumption. apply trivial26. assumption. assumption.
  assumption. } inversion H22.


assert (H23 : 1 * / B_powerRZ (n + 2 * msdx + 1 - msdx) >= 
1 * / IZR(Z.abs (xc (n + 2 * msdx + 1)%Z))).



{ apply Rinv_ge. { apply trivial28. apply Bexposgt1. apply inversegtZ. 
apply lt_IZR. apply inverseltR. apply trivial28. 
assert (trivial : IZR n + IZR msdx > IZR (-msdx) + IZR msdx).
apply Rplus_gt_compat_r. apply inversegtR. apply IZR_lt. apply inverseltZ. assumption.
assert (trivial2 : (IZR n + IZR msdx) + 1 > (IZR (- msdx) + IZR msdx) + 1).
apply Rplus_gt_compat_r. assumption.
replace (IZR (- msdx) + IZR msdx + 1) with (1) in trivial2.
replace (IZR n + IZR msdx + 1) with (IZR (n + 2 * msdx + 1 - msdx)) in trivial2.
assumption. rewrite <- plus_IZR.
replace (IZR (n + msdx) + 1) with (IZR (n + msdx + 1)).
apply IZR_trivial. ring. rewrite <- plus_IZR. reflexivity.  rewrite <- plus_IZR.
replace (IZR (- msdx + msdx)) with (0). ring. apply IZR_trivial. ring.
 } 
{ apply trivial28. apply Rlt_gt.  apply IZR_lt. apply inverseltZ. assumption. } 

replace (B_powerRZ (n + 2 * msdx + 1 - msdx)) with 
(IZR (B_powerZ (n + 2 * msdx + 1 - msdx))).

apply IZR_le. 
assumption. apply inverseB_power. 
replace ((n + 2 * msdx + 1 - msdx)%Z) with 
((n + msdx + 1)%Z). apply inversegeZ. apply le_IZR.
apply Rle_trans with (IZR (n + msdx)). apply Rlt_le.
replace (0) with (IZR(-msdx + msdx)). 
rewrite plus_IZR. rewrite plus_IZR. apply Rplus_lt_compat_r.
apply IZR_lt. apply inverseltZ. assumption. apply IZR_trivial. 
ring. rewrite plus_IZR. rewrite plus_IZR. rewrite plus_IZR.
lra. ring.  }


assert (H24 : 1 * / (B_powerRZ (n + 2 * msdx + 1 - msdx)*B_powerRZ (n + 2 * msdx + 1 - msdx))
 >= 1 * / (IZR (Z.abs (xc (n + 2 * msdx + 1)%Z))*IZR (Z.abs (xc (n + 2 * msdx + 1)%Z)))).


{ apply trivial29. { apply Bexpos. }
{ apply trivial28. apply Rlt_gt.  apply IZR_lt. apply inverseltZ. assumption. } assumption. }


assert (H25 : (1 + 2 * / IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) * Z.abs (xc (n + 2 * msdx + 1)%Z))) * 2 *
B_powerRZ (2 * n + 2 * msdx + 1) *
        / IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) * Z.abs (xc (n + 2 * msdx + 1)%Z)) <= 
(1 + 2 * / IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) * Z.abs (xc (n + 2 * msdx + 1)%Z)))
 * 2 *B_powerRZ (2 * n + 2 * msdx + 1) *
        / (B_powerRZ (n + 2 * msdx + 1 - msdx) * B_powerRZ (n + 2 * msdx + 1 - msdx))).


{ apply trivial30. { apply produitdedeuxpositifsR. { apply produitdedeuxpositifsR. {
apply trivial32. apply trivial46. lra. 
apply trivial28. apply Rlt_gt.  apply IZR_lt. apply inverseltZ. 
apply trivial34. assumption. } lra. }
 apply Bexpos. }  
apply inverseleR. 

replace (/ (B_powerRZ (n + 2 * msdx + 1 - msdx) *
 B_powerRZ (n + 2 * msdx + 1 - msdx))) with
(1 * / (B_powerRZ (n + 2 * msdx + 1 - msdx) * B_powerRZ (n + 2 * msdx + 1 - msdx))).


{ replace (/ IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) * Z.abs (xc (n + 2 * msdx + 1)%Z))) with
(1 * / (IZR (Z.abs (xc (n + 2 * msdx + 1)%Z)) * IZR (Z.abs (xc (n + 2 * msdx + 1)%Z)))).


{ assumption. } replace (IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) * Z.abs (xc (n + 2 * msdx + 1)%Z))) with
((IZR (Z.abs (xc (n + 2 * msdx + 1)%Z)) * IZR (Z.abs (xc (n + 2 * msdx + 1)%Z)))). {
 ring. } rewrite produitIZR. reflexivity. } ring. }

assert (H27 : (n + 2 * msdx + 1 - msdx > 0)%Z).


{ apply trivial38 with msdx. rewrite <- plus0Z. apply trivial40. assumption. }



assert (H28 : B_powerRZ 1 <= B_powerRZ (n + 2 * msdx + 1 - msdx)).
unfold B_powerRZ. apply Rle_powerRZ. apply Bplusgrandque1. apply trivial41. 
apply inverseltZ. assumption.


assert (H29 : B_powerRZ (n + 2 * msdx + 1 - msdx) <= IZR(Z.abs (xc (n + 2 * msdx + 1)%Z))).
{ rewrite <- inverseB_power. apply IZR_le. assumption. 
replace ((n + 2 * msdx + 1 - msdx)%Z) with 
((n + msdx + 1)%Z). apply inversegeZ. apply le_IZR.
apply Rle_trans with (IZR (n + msdx)). apply Rlt_le.
replace (0) with (IZR(-msdx + msdx)). 
rewrite plus_IZR. rewrite plus_IZR. apply Rplus_lt_compat_r.
apply IZR_lt. apply inverseltZ. assumption. apply IZR_trivial. 
ring. rewrite plus_IZR. rewrite plus_IZR. rewrite plus_IZR.
lra. ring.  }  


assert (H30 : B_powerRZ 1 <= IZR (Z.abs (xc (n + 2 * msdx + 1)%Z))).


{apply letransitifR with (B_powerRZ (n + 2 * msdx + 1 - msdx)).
{ assumption. }
assumption. }


assert (H31 : B_powerRZ 2 <= IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) * Z.abs (xc (n + 2 * msdx + 1)%Z))).

{ replace (B_powerRZ 2) with ((B_powerRZ 1) * (B_powerRZ 1)).
{ rewrite <- inverseB_power. rewrite produitIZR.

apply IZR_le.  apply inverseleZ. apply Zpower2.
{ apply inversegtZ. apply lt_IZR. apply trivial28. apply Rlt_gt. 
 apply IZR_lt. apply inverseltZ. assumption. }
{ apply gt_IZR. rewrite inverseB_power. apply Bexpos. omega. } apply ge_IZR. apply inversegeR.
rewrite inverseB_power. assumption. omega. omega. }
rewrite produitB_powerRZ. reflexivity. } 


assert (H32 :1 * / B_powerRZ 2 >= 
1 * / IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) * Z.abs (xc (n + 2 * msdx + 1)%Z))).


{ apply Rinv_ge. apply inverseltR. apply Bexpos.
{ 

 rewrite <- produitIZR. apply inverseltR. apply produitdedeuxpositifsR. 
{ apply inversegtR.  apply trivial28. apply Rlt_gt. 
 apply IZR_lt. apply inverseltZ. assumption. }

apply inversegtR.  apply trivial28. apply Rlt_gt. 
 apply IZR_lt. apply inverseltZ. assumption.  } assumption. }


assert (H33 : 2 * / B_powerRZ 2 >= 2 * / IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) *
 Z.abs (xc (n + 2 * msdx + 1)%Z))). 


apply divisiondansfraction. lra.
apply Bexpos. { rewrite <- produitIZR. apply inverseltR. apply produitdedeuxpositifsR.  
{ apply inversegtR.  apply trivial28. apply Rlt_gt. 
 apply IZR_lt. apply inverseltZ. assumption. }
apply inversegtR.  apply trivial28. apply Rlt_gt. 
 apply IZR_lt. apply inverseltZ. assumption. }
{apply Rinv_ge. apply inverseltR. apply Bexpos.
{ rewrite <- produitIZR. apply inverseltR. apply produitdedeuxpositifsR. 
 apply inversegtR.  apply trivial28. apply Rlt_gt. 
 apply IZR_lt. apply inverseltZ. assumption.
apply inversegtR.  apply trivial28. apply Rlt_gt. 
 apply IZR_lt. apply inverseltZ. assumption. } assumption. }



assert (H34 :1 + 2 * / B_powerRZ 2 >= 1 + 2 * /
 IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) * Z.abs (xc (n + 2 * msdx + 1)%Z))).
{ apply additiongeR. assumption. }


assert (H35 : (1 + 2 * / IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) * Z.abs (xc (n + 2 * msdx + 1)%Z))) *
        (2 * B_powerRZ (2 * n + 2 * msdx + 1)) *
        / IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) * Z.abs (xc (n + 2 * msdx + 1)%Z)) <=
(1 + 2 * / B_powerRZ 2) *
        (2 * B_powerRZ (2 * n + 2 * msdx + 1)) *
        / IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) * Z.abs (xc (n + 2 * msdx + 1)%Z))).


{ apply trivial44. {


replace (/ IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) * Z.abs (xc (n + 2 * msdx + 1)%Z))) with
(1 * / IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) * Z.abs (xc (n + 2 * msdx + 1)%Z))).


{ apply trivial46. { lra. }
rewrite <- produitIZR. apply inverseltR. apply produitdedeuxpositifsR.
apply inversegtR.  apply trivial28. apply Rlt_gt. 
 apply IZR_lt. apply inverseltZ. assumption.
apply inversegtR.  apply trivial28. apply Rlt_gt. 
 apply IZR_lt. apply inverseltZ. assumption. }

ring. } apply trivial44.
apply produitdedeuxpositifsR. lra. 
apply Bexpos. apply inverseleR. assumption. }

assert (H36 : (1 + 2 * / IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) * Z.abs (xc (n + 2 * msdx + 1)%Z))) *
      (2 * B_powerRZ (2 * n + 2 * msdx + 1)) *
      / IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) * Z.abs (xc (n + 2 * msdx + 1)%Z)) <=
(1 + 2 * / B_powerRZ 2) * (2 * B_powerRZ (2 * n + 2 * msdx + 1)) * /


(B_powerRZ (n + 2 * msdx + 1 - msdx) * B_powerRZ (n + 2 * msdx + 1 - msdx)) ).
{ apply trivial47. {

 rewrite <- produitIZR. apply produitdedeuxpositifsR.

apply trivial28. apply inversegtR. apply IZR_lt. apply inverseltZ. assumption.
apply trivial28. apply inversegtR. apply IZR_lt. apply inverseltZ. assumption. }
{ apply neqR. apply produitdedeuxpositifsR.
apply Bexpos. apply Bexpos. }



{ apply unplus2surrpositif.

rewrite <- produitIZR. apply produitdedeuxpositifsR.

apply trivial28. apply inversegtR. apply IZR_lt. apply inverseltZ. assumption.
apply trivial28. apply inversegtR. apply IZR_lt. apply inverseltZ. assumption. }

apply produitdedeuxpositifsR.
lra. apply Bexpos. 

 apply inverseleR. assumption.  apply inverseleR. rewrite <- produitIZR. assumption. }


replace (B_powerRZ (n + 2 * msdx + 1 - msdx) * B_powerRZ (n + 2 * msdx + 1 - msdx))
with (B_powerRZ (2 * n + 2 * msdx + 2)) in H36. { 


replace ((1 + 2 * / B_powerRZ 2) * (2 * B_powerRZ (2 * n + 2 * msdx + 1)) *
      / B_powerRZ (2 * n + 2 * msdx + 2))
with ((1 + 2 * / B_powerRZ 2) * 2 * B_powerRZ (-(1))) in H36. {



assert (H37 : 4 <= INR B). 

{ replace (4) with (INR 4). { apply NleR. apply B_sup_4. }
 
apply INR4. }

assert (H38 : B_powerRZ (-(1)) <= 1 * / 4).

{ replace (B_powerRZ (-(1))) with (1 * / B_powerRZ 1). {

replace (1 * / B_powerRZ 1) with ( / B_powerRZ 1). {

replace (1 * / 4) with (/ 4). {


  apply Rinv_le. { apply Bexpos. } lra. rewrite B_powerRZ1. assumption. }
ring. } ring. } 






unfold B_powerRZ. replace (1 * / powerRZ (INR B) 1) with
( / powerRZ (INR B) 1). { rewrite Rinv_powerRZ. reflexivity.
 
apply Bneq0. } ring. }

assert (H39 : B_powerRZ 2 >= 16).


{ replace (B_powerRZ 2) with (B_powerRZ (1 + 1)).
{ rewrite <- produitB_powerRZ. replace (16) with (4 * 4).
{ apply carregeR. {apply Bexpos. } { lra. } apply Bge4. } ring. } 
reflexivity. }


assert (H40 : 1 * / B_powerRZ 2 <= 1 * / 16).


{ apply inverseleR. apply Rinv_ge. { lra. } { apply Bexpos. } apply inverseleR. 
assumption. }


assert (H41 : 1 + 2 * / B_powerRZ 2 <= 1 + 2 * / 16).


{ apply inverseleR. apply additiongeR. apply inversegeR. apply trivial30. lra.
replace (/ B_powerRZ 2) with (1 * / B_powerRZ 2).
replace (/ 16) with (1 * / 16). {

 assumption. } ring. ring. }


assert (H42 : (1 + 2 * / B_powerRZ 2) * 2 * B_powerRZ (- (1)) <= (1 + 2 * / B_powerRZ 2) * 2 * (1 * / 4)).


{ replace ((1 + 2 * / B_powerRZ 2) * 2 * B_powerRZ (- (1))) with 
(2 * B_powerRZ (- (1))*(1 + 2 * / B_powerRZ 2)).

 {
replace ((1 + 2 * / B_powerRZ 2) * 2 * (1 * / 4)) with (2 * (1 * / 4) *(1 + 2 * / B_powerRZ 2)). 

{

 
apply trivial44. apply trivial32. apply trivial46. lra. apply Bexpos. apply trivial30.
{ lra. }  assumption. } rewrite commutativitedeR. ring. }
rewrite commutativitedeR. ring. }

assert (H43 : (1 + 2 * / B_powerRZ 2) * 2 * (1 * / 4) <= (1 + 2 * / 16) * 2 * (1 * / 4)).

{ apply trivial44. { lra. } apply trivial44. {lra. } assumption. }


assert (H44 : (1 + 2 * / 16) * 2 * (1 * / 4) < 1). { lra. }


assert (H45 : (1 + 2 * / IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) * Z.abs (xc (n + 2 * msdx + 1)%Z))) *
      (2 * B_powerRZ (2 * n + 2 * msdx + 1)) *
      / IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) * Z.abs (xc (n + 2 * msdx + 1)%Z)) <=
(1 + 2 * / B_powerRZ 2) * 2 * (1 * / 4)).

{ apply letransitifR with ((1 + 2 * / B_powerRZ 2) * 2 * B_powerRZ (- (1))). { assumption. }
assumption. }


assert (H46 : (1 + 2 * / IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) * Z.abs (xc (n + 2 * msdx + 1)%Z))) *
      (2 * B_powerRZ (2 * n + 2 * msdx + 1)) *
      / IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) * Z.abs (xc (n + 2 * msdx + 1)%Z)) <=
(1 + 2 * / 16) * 2 * (1 * / 4)).


{ apply letransitifR with ((1 + 2 * / B_powerRZ 2) * 2 * (1 * / 4)).
assumption. assumption. }


assert (H47 : (1 + 2 * / IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) * Z.abs (xc (n + 2 * msdx + 1)%Z))) *
      (2 * B_powerRZ (2 * n + 2 * msdx + 1)) *
      / IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) * Z.abs (xc (n + 2 * msdx + 1)%Z)) < 1).


{ apply lettransitifR with ((1 + 2 * / 16) * 2 * (1 * / 4)). assumption. assumption. }



assert (H48 : 2 * B_powerRZ (2 * n + 2 * msdx + 1) *
        / IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) * Z.abs (xc (n + 2 * msdx + 1)%Z) - 1) < 1).


{ apply lttransitifR with ((1 + 2 * / IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) * 
Z.abs (xc (n + 2 * msdx + 1)%Z))) *
        (2 * B_powerRZ (2 * n + 2 * msdx + 1)) *
        / IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) * Z.abs (xc (n + 2 * msdx + 1)%Z))). {
 assumption. }  assumption. }



replace (2 * B_powerRZ (2 * n + 2 * msdx + 1) *
      / IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) * Z.abs (xc (n + 2 * msdx + 1)%Z) - 1))

with (B_powerRZ (2 * n + 2 * msdx + 1) * / IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) - 1) -
      B_powerRZ (2 * n + 2 * msdx + 1) * / IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) + 1)) in H48.



assert (H49 :0 < B_powerRZ (2 * n + 2 * msdx + 1) * / IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) - 1) -
      B_powerRZ (2 * n + 2 * msdx + 1) * / IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) + 1) < 1).
{ split. apply inverseltR. assumption. assumption. }



assert (H50 : IZR(Zdiv_sup (B_powerZ (2 * n + 2 * msdx + 1))
(Z.abs (xc (n + 2 * msdx + 1)%Z) - 1)) < 
  IZR (B_powerZ (2 * n + 2 * msdx + 1)) * /
IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) - 1) + 1).
apply Zdiv_supgt. apply inversegtZ.
apply lt_IZR.
replace (0) with (1 + (-1)). 
replace (IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) - 1)) with
(IZR (Z.abs (xc (n + 2 * msdx + 1)%Z)) + (- 1)). 
apply Rplus_lt_compat_r.
apply IZR_lt. apply inverseltZ. assumption. 
rewrite minus_IZR. ring. ring.

replace (IZR (B_powerZ (2 * n + 2 * msdx + 1))) with
(B_powerRZ (2 * n + 2 * msdx + 1)) in H50.
{ replace (IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) - 1)) with
(IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) - 1)) in H50.



{
 assert (H51 : IZR beta < B_powerRZ (2 * n + 2 * msdx + 1) * / 
IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) - 1) + 1).
{ assumption. }


assert (H52 : IZR (Z_of_nat B ^ (2 * n + 2 * msdx + 1) /
(Z.abs (xc (n + 2 * msdx + 1)) + 1))%Z > 
IZR (Z_of_nat B ^ (2 * n + 2 * msdx + 1)) * /
IZR  ((Z.abs (xc (n + 2 * msdx + 1)%Z) + 1)) - 1).

apply Zdiv_inflt.
apply inversegtZ. apply lt_IZR. apply inverseltR. apply trivial28.
replace (1) with (0 + 1). rewrite plus_IZR.
apply Rplus_gt_compat_r. apply trivial28. apply inversegtR. apply IZR_lt.
apply inverseltZ. assumption. ring.

replace (IZR (Z.of_nat B ^ (2 * n + 2 * msdx + 1))) with
(B_powerRZ (2 * n + 2 * msdx + 1)) in H52.

{ replace (IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) + 1)) with
(IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) + 1)) in H52.

{ 

assert (H53 : IZR alpha >
      B_powerRZ (2 * n + 2 * msdx + 1) * / IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) + 1) - 1).

assumption.

clear H52.

clear H50.

assert (H54 : -(IZR alpha) < -(B_powerRZ (2 * n + 2 * msdx + 1) * / 
IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) + 1) - 1) ).


apply foismoinsungtR. { assumption. }


assert (H55 : IZR beta + (- IZR alpha) < B_powerRZ (2 * n + 2 * msdx + 1) * / 
IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) - 1) + 1
+ - (B_powerRZ (2 * n + 2 * msdx + 1) * / IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) + 1) - 1) ).


{ apply ltadditifR. { assumption. } assumption. }

replace (B_powerRZ (2 * n + 2 * msdx + 1) * / IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) - 1) + 1 +
      - (B_powerRZ (2 * n + 2 * msdx + 1) * / IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) + 1) - 1)) with
(B_powerRZ (2 * n + 2 * msdx + 1) * / IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) - 1) -
      B_powerRZ (2 * n + 2 * msdx + 1) * / IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) + 1) +2) in H55.


{ assert (H56 : B_powerRZ (2 * n + 2 * msdx + 1) * / IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) - 1) -
      B_powerRZ (2 * n + 2 * msdx + 1) * / IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) + 1) + 2 < 3).


replace (3) with (1 + 2).

{ apply inverseltR. apply additiongtR. apply inversegtR. assumption. }
{ ring. }

assert (H57 : IZR beta + - IZR alpha < 3). {

apply lttransitifR with (B_powerRZ (2 * n + 2 * msdx + 1) * / IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) - 1) -
      B_powerRZ (2 * n + 2 * msdx + 1) * / IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) + 1) + 2).

assumption. assumption. }

split. 

{ apply inverseltZ. apply gt_IZR. rewrite soustractionIZR.
 apply soustractioninegalite. apply inversegtR. apply IZR_lt. apply inverseltZ. 
 apply ZdivsupgtZdiv.
replace (0%Z) with ((1 + (-1))%Z).
replace ((Z.abs (xc (n + 2 * msdx + 1)) - 1)%Z) with
((Z.abs (xc (n + 2 * msdx + 1)) + (- 1))%Z). apply inversegtZ.
apply lt_IZR. rewrite plus_IZR. rewrite plus_IZR.
apply Rplus_lt_compat_r. apply IZR_lt. apply inverseltZ. assumption.
ring. ring.
apply inversegtZ. apply lt_IZR. apply inverseltR. apply trivial28.
replace (1) with (0 + 1). rewrite plus_IZR. apply Rplus_gt_compat_r.
apply trivial28. apply inversegtR. apply IZR_lt. apply inverseltZ. assumption.
ring. 



replace (IZR (B_powerZ (2 * n + 2 * msdx + 1))) with
(B_powerRZ (2 * n + 2 * msdx + 1)).

{ replace (IZR (Z.of_nat B ^ (2 * n + 2 * msdx + 1))) with
(B_powerRZ (2 * n + 2 * msdx + 1)).

{ replace (IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) - 1)) with
(IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) - 1)).

{ replace (IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) + 1)) with
(IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) + 1)).

{ apply additionlt. assumption. } trivial. } trivial. }
apply B_powerRZandZofnat. 

apply inversegeZ. apply le_IZR.
rewrite plus_IZR. apply Rle_trans with (IZR (2 * n + 2 * msdx)).
rewrite plus_IZR. replace (0) with (IZR (-2 * msdx) + IZR (2 * msdx)).
apply Rplus_le_compat_r. replace (IZR (-2 * msdx)) with 
(IZR (-msdx) + IZR (-msdx)). replace (IZR (2 * n)) with
(IZR n + IZR n). apply Rplus_le_compat. apply Rlt_le. 
apply IZR_lt. apply inverseltZ. assumption. apply Rlt_le. 
apply IZR_lt. apply inverseltZ. assumption.
rewrite <- plus_IZR. apply IZR_trivial. ring.
rewrite <- plus_IZR. apply IZR_trivial. ring.
rewrite <- plus_IZR. apply IZR_trivial. ring. lra.
 }

unfold B_powerZ. apply B_powerRZandZofnat. 
apply inversegeZ. apply le_IZR.
rewrite plus_IZR. apply Rle_trans with (IZR (2 * n + 2 * msdx)).
rewrite plus_IZR. replace (0) with (IZR (-2 * msdx) + IZR (2 * msdx)).
apply Rplus_le_compat_r. replace (IZR (-2 * msdx)) with 
(IZR (-msdx) + IZR (-msdx)). replace (IZR (2 * n)) with
(IZR n + IZR n). apply Rplus_le_compat. apply Rlt_le. 
apply IZR_lt. apply inverseltZ. assumption. apply Rlt_le. 
apply IZR_lt. apply inverseltZ. assumption.
rewrite <- plus_IZR. apply IZR_trivial. ring.
rewrite <- plus_IZR. apply IZR_trivial. ring.
rewrite <- plus_IZR. apply IZR_trivial. ring. lra.
}
apply lt_IZR. rewrite soustractionIZR. assumption. }
ring. } trivial. } apply B_powerRZandZofnat. 
apply inversegeZ. apply le_IZR.
rewrite plus_IZR. apply Rle_trans with (IZR (2 * n + 2 * msdx)).
rewrite plus_IZR. replace (0) with (IZR (-2 * msdx) + IZR (2 * msdx)).
apply Rplus_le_compat_r. replace (IZR (-2 * msdx)) with 
(IZR (-msdx) + IZR (-msdx)). replace (IZR (2 * n)) with
(IZR n + IZR n). apply Rplus_le_compat. apply Rlt_le. 
apply IZR_lt. apply inverseltZ. assumption. apply Rlt_le. 
apply IZR_lt. apply inverseltZ. assumption.
rewrite <- plus_IZR. apply IZR_trivial. ring.
rewrite <- plus_IZR. apply IZR_trivial. ring.
rewrite <- plus_IZR. apply IZR_trivial. ring. lra.
} trivial. }
apply B_powerRZandZofnat. 
apply inversegeZ. apply le_IZR.
rewrite plus_IZR. apply Rle_trans with (IZR (2 * n + 2 * msdx)).
rewrite plus_IZR. replace (0) with (IZR (-2 * msdx) + IZR (2 * msdx)).
apply Rplus_le_compat_r. replace (IZR (-2 * msdx)) with 
(IZR (-msdx) + IZR (-msdx)). replace (IZR (2 * n)) with
(IZR n + IZR n). apply Rplus_le_compat. apply Rlt_le. 
apply IZR_lt. apply inverseltZ. assumption. apply Rlt_le. 
apply IZR_lt. apply inverseltZ. assumption.
rewrite <- plus_IZR. apply IZR_trivial. ring.
rewrite <- plus_IZR. apply IZR_trivial. ring.
rewrite <- plus_IZR. apply IZR_trivial. ring. lra.
} 

apply divisionR3.

rewrite quotientB_powerZ2. apply divisionR2.


apply injectiviteB_powerRZ.

omega. }

rewrite produitB_powerRZ. apply injectiviteB_powerRZ. omega.  } } }

- inversion H222.


split.


{ apply inverseleZ. 

apply ArithZ2. trivial. apply inversegtZ. assumption. }



apply ArithZ3. trivial. assumption. -

set
(lambda :=

(B_powerZ (2 * n + 2 * msdx + 1) /
           (xc (n + 2 * msdx + 1) + 1) + 1)%Z).

assert (H66 : encadrement (absolue_reelc xc) (Rabs x)).
{ apply absolue_correct. assumption. } 

assert (H64 : forall n : Z, encadrement_bis ((absolue_reelc xc) n) n (Rabs x)).
{ unfold encadrement_bis; intros; apply H66; assumption. }


assert (H65 : encadrement_bis ((absolue_reelc xc) (n + 2 * msdx + 1)%Z) (n + 2 * msdx + 1)%Z (Rabs x)).
{ apply H64. } unfold encadrement_bis in H65.

inversion H65.

assert (H3 : IZR (absolue_reelc xc (n + 2 * msdx + 1)%Z) - 1 <
 Rabs x * B_powerRZ (n + 2 * msdx + 1)). assumption. clear H1.

assert (H4 : Rabs x * B_powerRZ (n + 2 * msdx + 1) < 
IZR (absolue_reelc xc (n + 2 * msdx + 1)%Z) + 1). assumption. clear H2.

apply Rinv_lt_contravar in H3.


apply inverseltR in H4. apply Rinv_lt_contravar in H4.

{ apply inverseltR in H3. apply inverseltR in H3.




assert (H5 :B_powerRZ (n + 2 * msdx + 1) * / (Rabs x * B_powerRZ (n + 2 * msdx + 1)) < 

B_powerRZ (n + 2 * msdx + 1) * / (IZR (absolue_reelc xc (n + 2 * msdx + 1)%Z) - 1)).


{ apply Rmult_gt_compat_l. { apply Bexpos. } assumption. }

replace (/ (Rabs x * B_powerRZ (n + 2 * msdx + 1))) with (/ (B_powerRZ (n + 2 * msdx + 1)* Rabs x))
in H5.

rewrite Rinv_mult_distr in H5.

{ replace (B_powerRZ (n + 2 * msdx + 1) * (/ B_powerRZ (n + 2 * msdx + 1) * / Rabs x)) with
( 1 * / Rabs x) in H5.



assert (H6 : B_powerRZ n * / Rabs x < B_powerRZ n * B_powerRZ (n + 2 * msdx + 1) *

 / (IZR (absolue_reelc xc (n + 2 * msdx + 1)%Z) - 1)).

replace (B_powerRZ n * B_powerRZ (n + 2 * msdx + 1) * / (IZR (absolue_reelc xc (n + 2 * msdx + 1)%Z) - 1)) 
with (B_powerRZ n * (B_powerRZ (n + 2 * msdx + 1) * / (IZR (absolue_reelc xc (n + 2 * msdx + 1)%Z) - 1))).
{

{ apply Rmult_gt_compat_l. {   apply Bexpos. } apply inversegtR.

replace (/ Rabs x) with (1 * / Rabs x).
assumption. ring. } } ring.

rewrite produitB_powerRZ in H6. 


replace (B_powerRZ (n + (n + 2 * msdx + 1))) with (B_powerRZ (2*n + 2 * msdx + 1)) in H6.

{ clear H5. clear H3.


assert (H7 :B_powerRZ (n + 2 * msdx + 1) * / (IZR (absolue_reelc xc (n + 2 * msdx + 1)%Z) + 1) < 

B_powerRZ (n + 2 * msdx + 1) * / (Rabs x * B_powerRZ (n + 2 * msdx + 1))).

{ apply Rmult_gt_compat_l. { apply Bexpos. } assumption. }

replace ((Rabs x * B_powerRZ (n + 2 * msdx + 1))) with ((B_powerRZ (n + 2 * msdx + 1) * Rabs x)) in H7.

rewrite Rinv_mult_distr in H7.

{ replace (B_powerRZ (n + 2 * msdx + 1) * (/ B_powerRZ (n + 2 * msdx + 1) * / Rabs x)) with
(1 * / Rabs x) in H7.

{ assert (H8 : B_powerRZ n * B_powerRZ (n + 2 * msdx + 1) * / 
(IZR (absolue_reelc xc (n + 2 * msdx + 1)%Z) + 1)
 < B_powerRZ n * / Rabs x).

{ replace (B_powerRZ n * B_powerRZ (n + 2 * msdx + 1) * / (IZR (absolue_reelc xc (n + 2 * msdx + 1)%Z) + 1))
with (B_powerRZ n * (B_powerRZ (n + 2 * msdx + 1) * / (IZR (absolue_reelc xc (n + 2 * msdx + 1)%Z) + 1))).

{ apply Rmult_gt_compat_l. {   apply Bexpos. } apply inversegtR.

replace (/ Rabs x) with (1 * / Rabs x).
assumption. ring. }  ring. }

rewrite produitB_powerRZ in H8.

replace (B_powerRZ (n + (n + 2 * msdx + 1))) with (B_powerRZ (2*n + 2 * msdx + 1)) in H8.

{ clear H7. clear H4.


assert (H9 : B_powerRZ (2 * n + 2 * msdx + 1) * / (IZR (absolue_reelc xc (n + 2 * msdx + 1)%Z) - 1) <=
IZR (Zdiv_sup (B_powerZ (2 * n + 2 * msdx + 1))
          (Z.abs (xc (n + 2 * msdx + 1)%Z) - 1))).

{ apply inverseleR. 

replace (B_powerRZ (2 * n + 2 * msdx + 1)) with (IZR (B_powerZ (2 * n + 2 * msdx + 1))).

{ replace ((IZR (absolue_reelc xc (n + 2 * msdx + 1)%Z) - 1)) with
(IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) - 1)).

apply zdivsupge. 

apply inversegtZ. apply lt_IZR. rewrite minus_IZR. 
replace (IZR (Z.abs (xc (n + 2 * msdx + 1)%Z)) - 1) with
(IZR (Z.abs (xc (n + 2 * msdx + 1)%Z)) + (- 1)).
replace (0) with (1 + (-1)). apply Rplus_lt_compat_r. apply IZR_lt.
apply inverseltZ. assumption. ring. ring.

unfold absolue_reelc. rewrite <- trivial22. reflexivity. }

rewrite inverseB_power. reflexivity.  

apply inversegeZ. apply le_IZR.
rewrite plus_IZR. apply Rle_trans with (IZR (2 * n + 2 * msdx)).
rewrite plus_IZR. replace (0) with (IZR (-2 * msdx) + IZR (2 * msdx)).
apply Rplus_le_compat_r. replace (IZR (-2 * msdx)) with 
(IZR (-msdx) + IZR (-msdx)). replace (IZR (2 * n)) with
(IZR n + IZR n). apply Rplus_le_compat. apply Rlt_le. 
apply IZR_lt. apply inverseltZ. assumption. apply Rlt_le. 
apply IZR_lt. apply inverseltZ. assumption.
rewrite <- plus_IZR. apply IZR_trivial. ring.
rewrite <- plus_IZR. apply IZR_trivial. ring.
rewrite <- plus_IZR. apply IZR_trivial. ring. lra. }

assert (H10 : B_powerRZ n * / Rabs x < IZR beta).

{ apply Rlt_le_trans with 
(B_powerRZ (2 * n + 2 * msdx + 1) * / (IZR (absolue_reelc xc (n + 2 * msdx + 1)%Z) - 1)). assumption.
assumption. } clear H9.

assert (H11 : IZR ((Z.of_nat B ^ (2 * n + 2 * msdx + 1) /
          (Z.abs (xc (n + 2 * msdx + 1)) + 1))%Z) <=
 B_powerRZ (2 * n + 2 * msdx + 1) * / (IZR (absolue_reelc xc (n + 2 * msdx + 1)%Z) + 1)).

{ rewrite <- inverseB_power. unfold absolue_reelc.

replace ((IZR (Z.abs (xc (n + 2 * msdx + 1)%Z)) + 1)) with
(IZR ((Z.abs (xc (n + 2 * msdx + 1)%Z) + 1))).
{

apply partieentièreinférieure.

{ apply inversegtZ. apply lt_IZR. rewrite plus_IZR.

replace (0) with (-1 + 1).

{ apply Rplus_lt_compat_r.

apply inverseltR. apply Rgt_trans with (0).

 apply trivial28. apply inversegtR. apply IZR_lt.
apply inverseltZ. assumption. lra. } ring. } }
rewrite plus_IZR. reflexivity. 
apply inversegeZ. apply le_IZR.
rewrite plus_IZR. apply Rle_trans with (IZR (2 * n + 2 * msdx)).
rewrite plus_IZR. replace (0) with (IZR (-2 * msdx) + IZR (2 * msdx)).
apply Rplus_le_compat_r. replace (IZR (-2 * msdx)) with 
(IZR (-msdx) + IZR (-msdx)). replace (IZR (2 * n)) with
(IZR n + IZR n). apply Rplus_le_compat. apply Rlt_le. 
apply IZR_lt. apply inverseltZ. assumption. apply Rlt_le. 
apply IZR_lt. apply inverseltZ. assumption.
rewrite <- plus_IZR. apply IZR_trivial. ring.
rewrite <- plus_IZR. apply IZR_trivial. ring.
rewrite <- plus_IZR. apply IZR_trivial. ring. lra.
 }

assert (H12 : IZR alpha < B_powerRZ n * / Rabs x).

{ apply Rle_lt_trans with (B_powerRZ (2 * n + 2 * msdx + 1) * 
/ (IZR (absolue_reelc xc (n + 2 * msdx + 1)%Z) + 1)).

{ assumption. } assumption. } clear H11.

assert (encadrementalphaplus1 : encadrement_bis  (alpha + 1) n (1 * / Rabs x)).
unfold encadrement_bis. split.
rewrite plus_IZR. replace (IZR alpha + 1 - 1) with (IZR alpha).
replace (1 * / Rabs x * B_powerRZ n) with (B_powerRZ n * / Rabs x).
assumption. ring. ring.
replace (1 * / Rabs x * B_powerRZ n) with (B_powerRZ n * / Rabs x).
apply Rlt_le_trans with (IZR beta). assumption. 
rewrite plus_IZR. replace (IZR alpha + 1 + 1) with (IZR alpha + 2).
replace (IZR beta) with 
(IZR alpha + (IZR beta - IZR alpha)).
apply Rplus_le_compat_l. rewrite <- minus_IZR. apply IZR_le. 
inversion Halphabeta. assumption. ring. ring. ring.

assert (encadrementbetamoins1 : encadrement_bis (beta - 1) n (1 * / Rabs x)).
unfold encadrement_bis. split.
replace (IZR (beta - 1) - 1) with (IZR beta - 2).
apply Rle_lt_trans with (IZR alpha).
replace (IZR alpha) with ((IZR alpha + 2) -2).
replace (IZR beta - 2) with (IZR beta + (- 2)).
replace (IZR alpha + 2 - 2) with ((IZR alpha + 2) + (- 2)).
apply Rplus_le_compat_r.
replace (IZR beta) with (IZR alpha + (IZR beta - IZR alpha)).
apply Rplus_le_compat_l. rewrite <- minus_IZR. apply IZR_le. 
inversion Halphabeta. assumption. ring. ring. ring.
ring.
replace (1 * / Rabs x * B_powerRZ n) with (B_powerRZ n * / Rabs x).
assumption. ring. rewrite minus_IZR. ring. rewrite minus_IZR.
replace (IZR beta - 1 + 1) with (IZR beta).
replace (1 * / Rabs x * B_powerRZ n) with (B_powerRZ n * / Rabs x).
assumption. ring. ring.

replace (1 * / Rabs x) with (Rabs (1 * / x)) in encadrementalphaplus1.


apply encadrement_bis_prop1 in encadrementalphaplus1.


replace (1 * / Rabs x) with (Rabs (1 * / x)) in encadrementbetamoins1.


apply encadrement_bis_prop1 in encadrementbetamoins1.

assert (xpositifounegatif : x > 0 \/ x < 0).

apply xdif0. assumption. inversion xpositifounegatif.

rewrite sg_pos in encadrementalphaplus1.

unfold encadrement_bis in encadrementalphaplus1.

replace (IZR (1 * (alpha + 1))) with (IZR(alpha + 1)) in 
encadrementalphaplus1.
replace (IZR lambda) with (IZR alpha + 1). rewrite plus_IZR in encadrementalphaplus1.
assumption.

replace (IZR alpha) with (IZR (Z.of_nat B ^ (2 * n + 2 * msdx + 1) /
          (Z.abs (xc (n + 2 * msdx + 1)) + 1))%Z).

replace (IZR lambda) with (IZR (B_powerZ (2 * n + 2 * msdx + 1) /
           (xc (n + 2 * msdx + 1) + 1) + 1)%Z).

rewrite plus_IZR. apply Rplus_eq_compat_r.

unfold B_powerZ.

replace ((Z.abs (xc (n + 2 * msdx + 1)%Z) + 1)%Z) with 
((xc (n + 2 * msdx + 1)%Z + 1)%Z).

 reflexivity.  rewrite Zabssgn.

assert ((Z.sgn (xc (n + 2 * msdx + 1)) = sg x)%Z).
 apply Zsgn_sg_bis. assumption. apply lt_IZR. apply inverseltR. apply trivial28.
apply inversegtR. apply IZR_lt. apply inverseltZ. assumption.
rewrite H2. rewrite sg_pos. ring. assumption.

trivial. trivial.
rewrite <- produitIZR. ring. 
apply inversegtR. replace (1 * / x) with (/ x). apply Rinv_0_lt_compat. 
apply inverseltR. assumption. ring.

rewrite sg_neg in encadrementbetamoins1.
unfold encadrement_bis in encadrementbetamoins1.


rewrite <- produitIZR in encadrementbetamoins1.
rewrite minus_IZR in encadrementbetamoins1.

replace (-1 * (IZR beta - 1)) with (- IZR beta + 1) in encadrementbetamoins1.

replace (- IZR beta + 1 - 1) with (-IZR beta) in encadrementbetamoins1.

replace (- IZR beta + 1 + 1) with (- IZR beta + 2) in encadrementbetamoins1.

replace (IZR lambda + 1) with (IZR lambda - 1 + 2).

replace (IZR lambda - 1) with (- IZR beta). assumption.

replace (IZR beta) with (IZR (Zdiv_sup (B_powerZ (2 * n + 2 * msdx + 1))
          (Z.abs (xc (n + 2 * msdx + 1)%Z) - 1))).

replace (IZR lambda) with (IZR (B_powerZ (2 * n + 2 * msdx + 1) /
           (xc (n + 2 * msdx + 1) + 1) + 1)%Z).

rewrite plus_IZR.

replace (IZR
  (B_powerZ (2 * n + 2 * msdx + 1) /
   (xc (n + 2 * msdx + 1)%Z + 1)) + 1 - 1) with
(IZR
  (B_powerZ (2 * n + 2 * msdx + 1) /
   (xc (n + 2 * msdx + 1)%Z + 1))).


assert (sgnx : (Z.sgn (xc(n + 2 * msdx + 1) ) = sg x)%Z).
apply Zsgn_sg_bis. assumption.
apply lt_IZR. apply inverseltR. apply trivial28. apply inversegtR.
apply IZR_lt. apply inverseltZ. assumption.

assert (absxk : (Z.abs (xc (n + 2 * msdx + 1)%Z) - 1%Z =
Z.abs (xc (n + 2 * msdx + 1)%Z + 1))%Z ).

rewrite Zabssgn. rewrite Zabssgn.

rewrite Z.sgn_neg. rewrite Z.sgn_neg. ring.

rewrite Zabssgn in Habs. rewrite sgnx in Habs.

rewrite sg_neg in Habs. apply inverseltZ in Habs. apply IZR_lt in Habs.

apply Ropp_gt_lt_contravar in Habs.

replace (- IZR (xc (n + 2 * msdx + 1)%Z * -1)) with (0 - IZR (xc (n + 2 * msdx + 1)%Z * -1)) 
in Habs.


rewrite <- minus_IZR in Habs. replace (- (1)) with (0 - (1)) in Habs.
rewrite <- minus_IZR in Habs. apply lt_IZR in Habs.

replace ((0 - xc (n + 2 * msdx + 1) * -1)%Z) with ((xc (n + 2 * msdx + 1))%Z) in Habs.

replace ((0 - 1)%Z) with ((-1)%Z) in Habs.

apply lt_IZR. replace (0) with (-1 + 1).

replace (IZR (xc (n + 2 * msdx + 1)%Z + 1)) with
 (IZR (xc (n + 2 * msdx + 1)%Z + 1) - 1 + 1). rewrite <- minus_IZR.

apply Rplus_lt_compat_r.

replace (IZR (xc (n + 2 * msdx + 1)%Z + 1 - 1)) with
 (IZR (xc (n + 2 * msdx + 1)%Z)).

apply IZR_lt. assumption. apply IZR_trivial. ring.
ring. ring. ring. ring. ring. ring. assumption.

rewrite sg_neg in sgnx.


apply Z.sgn_neg_iff. assumption. assumption.

rewrite absxk.


replace (- IZR (Zdiv_sup (B_powerZ (2 * n + 2 * msdx + 1))
 (Z.abs (xc (n + 2 * msdx + 1)%Z + 1))))
with 
(IZR (Z.sgn (xc (n + 2 * msdx + 1)%Z + 1)) *
 IZR (Zdiv_sup (B_powerZ (2 * n + 2 * msdx + 1)) 
(Z.abs (xc (n + 2 * msdx + 1)%Z + 1)))).
rewrite produitIZR. apply IZR_trivial.

apply Zdiv_sup_opp. 

rewrite Zabssgn in Habs. rewrite sgnx in Habs.

rewrite sg_neg in Habs. apply inverseltZ in Habs. apply IZR_lt in Habs.

apply Ropp_gt_lt_contravar in Habs.

replace (- IZR (xc (n + 2 * msdx + 1)%Z * -1)) with (0 - IZR (xc (n + 2 * msdx + 1)%Z * -1)) 
in Habs.


rewrite <- minus_IZR in Habs. replace (- (1)) with (0 - (1)) in Habs.
rewrite <- minus_IZR in Habs. apply lt_IZR in Habs.

replace ((0 - xc (n + 2 * msdx + 1) * -1)%Z) with ((xc (n + 2 * msdx + 1))%Z) in Habs.

replace ((0 - 1)%Z) with ((-1)%Z) in Habs.

apply lt_IZR. replace (0) with (-1 + 1).

replace (IZR (xc (n + 2 * msdx + 1)%Z + 1)) with
 (IZR (xc (n + 2 * msdx + 1)%Z + 1) - 1 + 1). rewrite <- minus_IZR.

apply Rplus_lt_compat_r.

replace (IZR (xc (n + 2 * msdx + 1)%Z + 1 - 1)) with
 (IZR (xc (n + 2 * msdx + 1)%Z)).

apply IZR_lt. assumption. apply IZR_trivial. ring.
ring. ring. ring. ring. ring. ring. assumption.

assert (sgnxkplus1 : (Z.sgn (xc (n + 2 * msdx + 1)%Z + 1) = -1)%Z).

 apply Z.sgn_neg_iff.

rewrite Zabssgn in Habs. rewrite sgnx in Habs.

rewrite sg_neg in Habs. apply inverseltZ in Habs. apply IZR_lt in Habs.

apply Ropp_gt_lt_contravar in Habs.

replace (- IZR (xc (n + 2 * msdx + 1)%Z * -1)) with (0 - IZR (xc (n + 2 * msdx + 1)%Z * -1)) 
in Habs.


rewrite <- minus_IZR in Habs. replace (- (1)) with (0 - (1)) in Habs.
rewrite <- minus_IZR in Habs. apply lt_IZR in Habs.

replace ((0 - xc (n + 2 * msdx + 1) * -1)%Z) with ((xc (n + 2 * msdx + 1))%Z) in Habs.

replace ((0 - 1)%Z) with ((-1)%Z) in Habs.

apply lt_IZR. replace (0) with (-1 + 1).

replace (IZR (xc (n + 2 * msdx + 1)%Z + 1)) with
 (IZR (xc (n + 2 * msdx + 1)%Z + 1) - 1 + 1). rewrite <- minus_IZR.

apply Rplus_lt_compat_r.

replace (IZR (xc (n + 2 * msdx + 1)%Z + 1 - 1)) with
 (IZR (xc (n + 2 * msdx + 1)%Z)).

apply IZR_lt. assumption. apply IZR_trivial. ring.
ring. ring. ring. ring. ring. ring. assumption.

rewrite sgnxkplus1. ring. ring. reflexivity.

reflexivity. ring. ring. ring. ring.

replace (1 * / x) with (/ x). apply Rinv_lt_0_compat. assumption. ring.

apply le_IZR. replace (0) with (0 + 1 + (-1)).

replace (IZR (beta - 1)) with (IZR (beta - 1) + 1 + (-1)).
apply Rplus_le_compat_r. replace (IZR (beta - 1) + 1) with (IZR beta).
replace (0 + 1) with (1).
apply IZR_le. apply trivial41.

apply lt_IZR. replace (IZR beta) with 
(IZR (Zdiv_sup (B_powerZ (2 * n + 2 * msdx + 1))
          (Z.abs (xc (n + 2 * msdx + 1)%Z) - 1))).

apply Rlt_le_trans with (IZR (B_powerZ (2 * n + 2 * msdx + 1)) * /
IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) - 1)).
apply produitdedeuxpositifsR.

rewrite inverseB_power. apply Bexpos. 

apply inversegeZ. apply le_IZR.
rewrite plus_IZR. apply Rle_trans with (IZR (2 * n + 2 * msdx)).
rewrite plus_IZR. replace (0) with (IZR (-2 * msdx) + IZR (2 * msdx)).
apply Rplus_le_compat_r. replace (IZR (-2 * msdx)) with 
(IZR (-msdx) + IZR (-msdx)). replace (IZR (2 * n)) with
(IZR n + IZR n). apply Rplus_le_compat. apply Rlt_le. 
apply IZR_lt. apply inverseltZ. assumption. apply Rlt_le. 
apply IZR_lt. apply inverseltZ. assumption.
rewrite <- plus_IZR. apply IZR_trivial. ring.
rewrite <- plus_IZR. apply IZR_trivial. ring.
rewrite <- plus_IZR. apply IZR_trivial. ring. lra.

 apply inversegtR. apply Rinv_0_lt_compat.
replace (0) with (0 + 1 + (-1)).

replace (IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) - 1)) with
(IZR (Z.abs (xc (n + 2 * msdx + 1)%Z) - 1) + 1 + (-1)).

apply Rplus_lt_compat_r. rewrite  minus_IZR.
replace (0 + 1) with (1). 
replace (IZR (Z.abs (xc (n + 2 * msdx + 1)%Z)) - 1 + 1) with
(IZR (Z.abs (xc (n + 2 * msdx + 1)%Z))).
apply IZR_lt. apply inverseltZ. assumption. ring. ring. ring.
ring. 

apply inverseleR. apply zdivsupge.
apply inversegtZ. apply lt_IZR.
rewrite minus_IZR.
replace (IZR (Z.abs (xc (n + 2 * msdx + 1)%Z)) - 1) with
(IZR (Z.abs (xc (n + 2 * msdx + 1)%Z)) + (- 1)).
replace (0) with (1 + (-1)). apply Rplus_lt_compat_r.
apply IZR_lt. apply inverseltZ. assumption. ring.
ring.

 trivial. ring. rewrite minus_IZR. ring.
ring. ring.

rewrite Rabsunsurx. reflexivity.
assumption.

apply le_IZR. apply Rle_trans with (IZR alpha).  apply IZR_le. 
replace (alpha) with ((Z.of_nat B ^ (2 * n + 2 * msdx + 1) /
          (Z.abs (xc (n + 2 * msdx + 1)) + 1))%Z). 
apply inverseleZ.

apply Z_div_ge0.

apply inversegtZ. apply lt_IZR. apply inverseltR. apply trivial28.
replace (1) with (0 + 1). rewrite plus_IZR.
replace (IZR (1)) with (1). apply Rplus_gt_compat_r.
apply trivial28. apply inversegtR. apply IZR_lt. apply inverseltZ. assumption.
apply IZR_trivial. ring. ring.
apply inversegeZ.  apply le_IZR. rewrite <- B_powerRZandZofnat. apply inverseleR.
apply Rgt_ge. apply Bexpos. 
apply inversegeZ. apply le_IZR.
rewrite plus_IZR. apply Rle_trans with (IZR (2 * n + 2 * msdx)).
rewrite plus_IZR. replace (0) with (IZR (-2 * msdx) + IZR (2 * msdx)).
apply Rplus_le_compat_r. replace (IZR (-2 * msdx)) with 
(IZR (-msdx) + IZR (-msdx)). replace (IZR (2 * n)) with
(IZR n + IZR n). apply Rplus_le_compat. apply Rlt_le. 
apply IZR_lt. apply inverseltZ. assumption. apply Rlt_le. 
apply IZR_lt. apply inverseltZ. assumption.
rewrite <- plus_IZR. apply IZR_trivial. ring.
rewrite <- plus_IZR. apply IZR_trivial. ring.
rewrite <- plus_IZR. apply IZR_trivial. ring. lra.
now trivial.
replace (IZR alpha) with (IZR alpha + 0). rewrite plus_IZR.
apply Rplus_le_compat_l. lra. ring.
rewrite Rabsunsurx. reflexivity. assumption. }
unfold B_powerRZ. apply powerRZ_trivial. ring. } rewrite <- Rmult_assoc.
rewrite Rinv_r_simpl_r. ring. apply neqR. apply Bexpos. }
apply neqR. apply Bexpos. apply neq0impliquerabsneq0. assumption.
ring. }

unfold B_powerRZ. apply powerRZ_trivial. ring. 
rewrite <- Rmult_assoc. rewrite Rinv_r_simpl_r. ring.
apply neqR. apply Bexpos. }
apply neqR. apply Bexpos. apply neq0impliquerabsneq0. assumption.
rewrite Rinv_mult_distr. rewrite Rinv_mult_distr. ring.
apply neq0impliquerabsneq0. assumption. apply neqR. apply Bexpos.
apply neqR. apply Bexpos. apply neq0impliquerabsneq0. assumption. }

apply inverseltR. apply produitdedeuxpositifsR. apply produitdedeuxpositifsR.
apply inversegtR. apply Rabs_pos_lt. assumption. apply Bexpos.
unfold absolue_reelc. apply trivial28. replace (1) with (0 + 1).
replace (IZR (Z.abs (xc (n + 2 * msdx + 1)%Z)) + (0 + 1)) with
((IZR (Z.abs (xc (n + 2 * msdx + 1)%Z)) + 0) + 1).
apply Rplus_gt_compat_r. apply trivial28. 
replace (IZR (Z.abs (xc (n + 2 * msdx + 1)%Z)) + 0) with
(IZR (Z.abs (xc (n + 2 * msdx + 1)%Z))).
apply inversegtR. apply IZR_lt. apply inverseltZ. assumption.
ring. ring. ring. apply inverseltR. apply produitdedeuxpositifsR.
replace (0) with (1 + (-1)).
replace (IZR (absolue_reelc xc (n + 2 * msdx + 1)%Z) - 1) with
(IZR (absolue_reelc xc (n + 2 * msdx + 1)%Z) + (- 1)).
apply Rplus_gt_compat_r. unfold absolue_reelc. 
apply inversegtR. apply IZR_lt. apply inverseltZ. assumption.
ring. ring. apply produitdedeuxpositifsR.
apply Rabs_pos_lt. assumption. apply Bexpos.
Qed.
