(*
(C) Copyright 2010, COQTAIL team

Project Info: http://sourceforge.net/projects/coqtail/

This library is free software; you can redistribute it and/or modify it
under the terms of the GNU Lesser General Public License as published by
the Free Software Foundation; either version 2.1 of the License, or
(at your option) any later version.

This library is distributed in the hope that it will be useful, but
WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General Public
License for more details.

You should have received a copy of the GNU Lesser General Public
License along with this library; if not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301,
USA.
*)

Require Export Reals.
Require Export MyReals.
Require Export Rsequence_facts.
Require Export Rseries.
Require Export Rpser_facts.
Require Import Fourier.
Require Import Rintegral.

(* begin hide *)
Lemma continuity_pt_eq_compat :
  forall f g x, (exists alp, alp > 0 /\ forall y, R_dist x y < alp -> f y = g y) ->
  continuity_pt f x -> continuity_pt g x.
Proof.
intros f g x [alp1 [Halp1 H1]] H.
intros eps Heps.
destruct (H eps Heps) as [alp2 [Halp2 H2]].
exists (Rmin alp1 alp2); split.
apply Rmin_pos; assumption.
intros u Hu.
repeat rewrite <- H1.
apply H2.
split; intuition.
unfold Rmin in * |- ; destruct Rle_dec; fourier.
rewrite R_dist_eq; assumption.
apply Rlt_le_trans with (Rmin alp1 alp2).
  destruct Hu as [_ Hu].
  rewrite R_dist_sym; apply Hu.
  apply Rmin_l.
Qed.
(* end hide *)

(** * Taylor series of ln *)

Section ln_minus.

Let Un n :=
match n with
| 0 => 0
| _ => - / (INR n)
end.

Lemma ln_minus_cv_radius : Cv_radius_weak Un 1.
Proof.
exists 1; intros m [n Hn]; subst m.
unfold gt_abs_Pser.
rewrite pow1; rewrite Rmult_1_r.
unfold Un; destruct n.
  rewrite Rabs_R0; apply Rle_0_1.
  assert (Hle : 1 <= INR (S n)).
    rewrite S_INR.
    pattern 1 at 1; rewrite <- Rplus_0_l.
    apply Rplus_le_compat_r.
    apply pos_INR.
  rewrite Rabs_Ropp.
  rewrite Rabs_Rinv; [|intros Hc; fourier].
  rewrite Rabs_right; [|fourier].
  apply (Rmult_le_reg_l (INR (S n))); [fourier|].
  rewrite Rinv_r; [fourier|intros Hc; fourier].
Qed.

Let sum x := sum_r Un 1 ln_minus_cv_radius x.

Lemma ln_minus_taylor_sum :
  forall x, Rabs x < 1 -> sum x = (ln (1 - x)).
Proof.
intros x Hx.
pose (f := comp ln (fct_cte 1 - id)).
pose (df := fun u => / (1 - u) * (0 - 1)).
assert (Hb : forall u, Rmin 0 x <= u <= Rmax 0 x -> -1 < u < 1).
  destruct (Rabs_def2 x 1 Hx) as [Hmax Hmin].
  intros u [Hul Hur].
    unfold Rmin, Rmax in Hul, Hur.
    destruct Rle_dec; split; fourier.
pose (Hcv := ln_minus_cv_radius).
pose (g := sum_r Un 1 Hcv).
pose (dg := sum_r_derive Un 1 Hcv).
destruct Rint_derive2
  with (f := f) (a := 0) (b := x) (d := df) as [pr HI].
  intros u Hu.
  apply derivable_pt_lim_comp.
  apply derivable_pt_lim_minus.
  apply derivable_pt_lim_const.
  apply derivable_pt_lim_id.
  apply derivable_pt_lim_ln.
  apply Rgt_minus; apply (Hb u Hu).
  intros u Hu.
  apply continuity_pt_mult.
  apply continuity_pt_inv.
  apply continuity_pt_minus.
  apply continuity_pt_const; unfold constant; auto.
  apply derivable_continuous_pt; apply derivable_pt_id.
  apply Rgt_not_eq; apply Rgt_minus; apply (Hb u Hu).
  apply continuity_pt_minus.
  apply continuity_pt_const; unfold constant; auto.
  apply continuity_pt_const; unfold constant; auto.
assert (Heq : forall u, -1 < u < 1 -> dg u = df u).
  intros u [Hul Hur]; unfold df, dg.
  replace (/ (1 - u) * (0 - 1))
    with (- / (1 - u)) by (field; intros Hc; fourier).
  assert (Habs : Rabs u < 1).
    unfold Rabs; destruct Rcase_abs; fourier.
  assert (Hser1 := sum_r_derive_sums Un 1 Hcv u Habs).
  assert (Hser2 := GP_infinite u Habs).
  eapply Rseq_cv_unique.
    apply Hser1.
    unfold An_deriv.
    eapply Rseq_cv_eq_compat; [|apply Rseq_cv_opp_compat; apply Hser2].
    unfold Rseq_opp; intros n; induction n.
      simpl; field.
      simpl sum_f_R0 at 1; rewrite Ropp_plus_distr.
      rewrite IHn.
      simpl; apply Rplus_eq_compat_l; destruct n.
        field.
        field; assert (H := pos_INR (S n)); intros Hc; fourier.
edestruct Rint_eq_compat
  with (f := df) (g := dg) (a := 0) (b := x) as [pr2 HI2].
  intros u Hu.
  apply Heq; apply Hb; assumption.
  exists pr; apply HI.
destruct Rint_derive2
  with (f := g) (a := 0) (b := x) (d := dg) as [pr3 HI3].
  intros u Hu.
  apply Pser_derivability.
  apply Hb in Hu.
  destruct Hu as [Hul Hur].
  unfold Rabs; destruct Rcase_abs; fourier.
  intros u Hu.
  assert (Hu2 := Hb u Hu).
  destruct Hu2 as [Hul Hur].
  assert (Hct : continuity_pt df u).
    unfold df.
    apply continuity_pt_mult.
    apply continuity_pt_inv; [|intros Hc; fourier].
    apply continuity_pt_minus.
    apply continuity_pt_const; unfold constant; auto.
    apply derivable_continuous_pt; apply derivable_pt_id.
    apply continuity_pt_const; unfold constant; auto.
  eapply continuity_pt_eq_compat; [|apply Hct].
    pose (alp1 := u / 2 + / 2).
    pose (alp2 := /2 - u / 2).
    exists (Rmin alp1 alp2); split.
    apply Rmin_pos.
      unfold alp1; fourier.
      unfold alp2; fourier.
    intros y Hy; symmetry.
    apply Heq.
    unfold alp1, alp2, R_dist, Rabs, Rmin in *.
    destruct Rcase_abs as [Hc|Hc] in Hy;
    destruct Rle_dec as [Hl|Hl] in Hy;
    split; try fourier.
    apply Rnot_le_lt in Hl; fourier.
assert (Hint : Rint dg 0 x (f x - f 0)).
  apply Rint_eq_compat with (f := df).
  intros u Hu.
  apply Heq; apply Hb; assumption.
  exists pr; assumption.
assert (Heq_fun : g x - g 0 = f x - f 0).
  eapply Rint_uniqueness.
    exists pr3; assumption.
    assumption.
replace (ln (1 - x)) with (sum_r Un 1 Hcv x).
  unfold sum, Hcv; reflexivity.
unfold f, g, comp, fct_cte, id, minus_fct in Heq_fun; hnf in Heq_fun.
replace (1 - 0) with 1 in Heq_fun by ring; rewrite ln_1 in Heq_fun.
rewrite Rminus_0_r in Heq_fun.
replace (sum_r Un 1 Hcv 0) with 0 in Heq_fun.
rewrite Rminus_0_r in Heq_fun; assumption.
symmetry.
eapply Rseq_cv_unique.
apply sum_r_sums; rewrite Rabs_R0; fourier.
intros eps Heps; exists 0%nat; intros n _.
rewrite sum_eq_R0.
rewrite R_dist_eq; assumption.
intros m _; unfold Un; destruct m.
  field.
  rewrite pow_ne_zero; [field|].
    apply not_0_INR; auto.
    auto.
Qed.

Lemma ln_minus_taylor :
  forall x, Rabs x < 1 -> Pser Un x (ln (1 - x)).
Proof.
intros x Hx.
rewrite <- ln_minus_taylor_sum; [|assumption].
apply sum_r_sums; assumption.
Qed.

End ln_minus.

Section ln_plus.

Let Un n :=
match n with
| 0 => 0 
| _ => (- 1) ^ (S n) / (INR n)
end.

Lemma ln_plus_cv_radius : Cv_radius_weak Un 1.
exists 1; intros m [n Hn]; subst m.
unfold gt_abs_Pser.
rewrite pow1; rewrite Rmult_1_r.
unfold Un; destruct n.
  rewrite Rabs_R0; apply Rle_0_1.
  assert (Hle : 1 <= INR (S n)).
    rewrite S_INR.
    pattern 1 at 1; rewrite <- Rplus_0_l.
    apply Rplus_le_compat_r.
    apply pos_INR.
  unfold Rdiv; rewrite Rabs_mult.
  rewrite pow_1_abs; rewrite Rmult_1_l.
  rewrite Rabs_Rinv; [|intros Hc; fourier].
  rewrite Rabs_right; [|fourier].
  apply (Rmult_le_reg_l (INR (S n))); [fourier|].
  rewrite Rinv_r; [fourier|intros Hc; fourier].
Qed.

Let sum x := sum_r Un 1 ln_plus_cv_radius x.

Lemma ln_plus_taylor_sum :
  forall x, Rabs x < 1 -> sum x = (ln (1 + x)).
Proof.
intros x Hx.
assert (Hmx : Rabs (- x) < 1).
  rewrite Rabs_Ropp; assumption.
replace (1 + x) with (1 - (- x)) by ring.
eapply trans_eq; [|apply ln_minus_taylor_sum; assumption].
eapply Rseq_cv_unique.
  apply sum_r_sums; assumption.
eapply Rseq_cv_eq_compat; [|apply sum_r_sums; assumption].
intros n; apply sum_eq; intros i Hi; unfold Un.
destruct i; [field|].
replace (- x) with (- 1 * x) by ring.
rewrite Rpow_mult_distr.
repeat rewrite <- tech_pow_Rmult; field.
auto with real.
Qed.

Lemma ln_plus_taylor :
  forall x, Rabs x < 1 -> Pser Un x (ln (1 + x)).
Proof.
intros x Hx.
rewrite <- ln_plus_taylor_sum; [|assumption].
apply sum_r_sums; assumption.
Qed.

End ln_plus.
