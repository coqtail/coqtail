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

Require Import Rbase.
Require Import Ranalysis.
Require Import Rfunctions.
Require Import Rseries.
Require Import Fourier.
Require Import RiemannInt.
Require Import SeqProp.
Require Import Max.
Require Import MyRIneq.
Require Import MyRanalysis_def.
Require Import RIVT.


Local Open Scope R_scope.



(** * Interesting results *)

Lemma strictly_monotonous_recip_interval_comm : forall f g lb ub,
       strictly_monotonous_interval f lb ub ->
       reciprocal_interval f g (Rmin (f lb) (f ub)) (Rmax (f lb) (f ub)) ->
       (forall x, interval (Rmin (f lb) (f ub)) (Rmax (f lb) (f ub)) x -> interval lb ub (g x)) ->
       reciprocal_interval g f lb ub.
Proof.
intros f g lb ub f_mono f_recip_g g_right x x_encad.
  assert(f_inj := strictly_monotonous_injective_interval _ _ _ f_mono).
 destruct f_mono as [f_incr | f_decr].
 assert (f_incr2 := strictly_increasing_increasing_interval _ _ _ f_incr).
 assert (Hrew : forall x, lb <= x <= ub -> f (g (f x)) = f x).
  intros x0 x0_encad ;
   assert (fx0_encad : interval (Rmin (f lb) (f ub)) (Rmax (f lb) (f ub)) (f x0)).
   split.
    apply Rle_trans with (f lb) ; [apply Rmin_l | apply f_incr2].
     split ; [right ; reflexivity | apply Rle_trans with x0 ; intuition].
     assumption.
     intuition.
    apply Rle_trans with (f ub) ; [apply f_incr2 | apply RmaxLess2].
     assumption.
     split ; [apply Rle_trans with x0 ; intuition | right ; reflexivity].
     intuition.
  apply f_recip_g ; assumption.
  assert (fx_encad : interval (Rmin (f lb) (f ub)) (Rmax (f lb) (f ub)) (f x)).
 split ; unfold interval in x_encad.
   apply Rle_trans with (f lb) ; [apply Rmin_l | apply f_incr2].
    split ; [right ; reflexivity | apply Rle_trans with x ; intuition].
    assumption.
    intuition.
    apply Rle_trans with (f ub) ; [apply f_incr2 | apply RmaxLess2].
    assumption.
    split ; [apply Rle_trans with x ; intuition | right ; reflexivity].
    intuition.
apply f_inj.
 apply g_right.
    assumption.
    assumption.
    apply f_recip_g.
    assumption.

 assert (f_decr2 := strictly_decreasing_decreasing_interval _ _ _ f_decr).
 assert (Hrew : forall x, lb <= x <= ub -> f (g (f x)) = f x).
  intros x0 x0_encad ;
   assert (fx0_encad : interval (Rmin (f lb) (f ub)) (Rmax (f lb) (f ub)) (f x0)).
   split.
    apply Rle_trans with (f ub) ; [apply Rmin_r | apply f_decr2].
     assumption.
     split ; [apply Rle_trans with x0 ; intuition | right ; reflexivity].
     intuition.
    apply Rle_trans with (f lb) ; [apply f_decr2 | apply RmaxLess1].
     split ; [right ; reflexivity | apply Rle_trans with x0 ; intuition].
     assumption.
     intuition.
  apply f_recip_g ; assumption.
  assert (fx_encad : interval (Rmin (f lb) (f ub)) (Rmax (f lb) (f ub)) (f x)).
 split ; unfold interval in x_encad.
   apply Rle_trans with (f ub) ; [apply Rmin_r | apply f_decr2].
     assumption.
     split ; [apply Rle_trans with x ; intuition | right ; reflexivity].
     intuition.
    apply Rle_trans with (f lb) ; [apply f_decr2 | apply RmaxLess1].
     split ; [right ; reflexivity | apply Rle_trans with x ; intuition].
     assumption.
     intuition.
apply f_inj.
 apply g_right.
    assumption.
    assumption.
    apply f_recip_g.
    assumption.
Qed.

(* begin hide *)
Ltac case_le H :=
   let t := type of H in 
   let h' := fresh in 
      match t with ?x <= ?y => case (total_order_T x y);
         [intros h'; case h'; clear h' | 
          intros h'; clear -H h'; elimtype False; fourier ] end.
(* end hide *)

(** The image of an interval by a continuous function is an interval *)

Lemma continuity_interval_image_interval : forall (f:R->R) (lb ub y:R),
       lb <= ub ->
       interval (f lb) (f ub) y ->
       continuity_interval f lb ub ->
       {x | interval lb ub x /\ f x = y}.
Proof.
intros f lb ub y lb_le_ub y_encad f_cont_interv.
 case (Rle_lt_or_eq_dec _ _ lb_le_ub) ; clear lb_le_ub ; intro lb_lt_ub.
 case y_encad ; intro y_encad1.
   case_le y_encad1 ; intros y_encad2 y_encad3 ; case_le y_encad3.
    intro y_encad4.
     clear y_encad y_encad1 y_encad3.
     assert (Cont : forall a : R, lb <= a <= ub -> continuity_pt (fun x => f x - y) a).
      intros a a_encad. unfold continuity_pt, continue_in, limit1_in, limit_in ; simpl ; unfold R_dist.
      intros eps eps_pos. elim (f_cont_interv a a_encad eps eps_pos).
      intros alpha alpha_pos. destruct alpha_pos as (alpha_pos,Temp).
      exists alpha. split.
      assumption. intros x  x_cond.
      replace (f x - y - (f a - y)) with (f x - f a) by field.
      exact (Temp x x_cond).
     assert (H1 : interval (f lb - y) (f ub - y) 0).
      split ; left ; [apply Rlt_minus | apply Rgt_minus] ; assumption.
     destruct (IVT_interv (fun x => f x - y) lb ub Cont lb_lt_ub H1) as (x,Hx).
     exists x.
     destruct Hx as (Hyp,Result).
     split ; [assumption | intuition].
     intro H ; exists ub ; repeat split ; intuition.
     intro H ; exists lb ; repeat split ; intuition.
     intro H ; exists ub ; repeat split ; intuition.
     exists lb ; repeat split ; intuition.
     subst ; apply Rle_antisym ; unfold interval in * ; intuition.
Qed.

Lemma continuity_pt_recip_interval_prelim : forall (f g:R->R) (lb ub:R),
       lb <= ub ->
       strictly_increasing_interval f lb ub -> 
       reciprocal_interval g f lb ub ->
       continuity_interval f lb ub ->
       continuity_open_interval g (Rmin (f lb) (f ub)) (Rmax (f lb) (f ub)).
Proof.
intros f g lb ub lb_le_ub f_incr f_eq_g f_cont_interv b b_encad.
 (*destruct f_mono as [f_incr | f_decr].*)
  assert (f_incr2 := strictly_increasing_increasing_interval _ _ _ f_incr).
  intros eps eps_pos ; simpl ; unfold R_dist.
   assert (b_encad2 : open_interval (f lb) (f ub) b).
    apply strictly_increasing_open_interval_image ; assumption.
   assert (b_encad3 := open_interval_interval _ _ _ b_encad2).
   elim (continuity_interval_image_interval f lb ub b lb_le_ub b_encad3 f_cont_interv) ;
   intros x [x_encad f_x_b].
   assert (x_encad2 : open_interval lb ub x).
    split.
    assert (Temp : x <> lb).
     intro Hfalse ; rewrite Hfalse in f_x_b.
     assert (Temp' : b <> f lb).
      apply Rgt_not_eq ; exact (proj1 b_encad2).
     apply Temp' ; symmetry ; assumption.
    apply Rle_neq_lt ; split ; unfold interval in * ; intuition.
    assert (Temp : x <> ub).
    intro Hfalse ; rewrite Hfalse in f_x_b.
    assert (Temp' : b <> f ub).
     apply Rlt_not_eq ; exact (proj2 b_encad2).
    apply Temp' ; symmetry ; assumption.
    apply Rle_neq_lt ; split ; unfold interval in * ; intuition.
   pose (x1 := Rmax (x - eps) lb).
   pose (x2 := Rmin (x + eps) ub).
   assert (x1_encad : interval lb ub x1).
    split. apply RmaxLess2.
    apply Rlt_le. unfold x1 ; rewrite Rmax_lt_lt_lt ;
    split ; apply Rlt_trans with (r2:=x).
    fourier.
    apply (proj2 x_encad2).
    apply (proj1 x_encad2).
    apply (proj2 x_encad2).
  assert (x2_encad : interval lb ub x2).
   split. apply Rlt_le ; unfold x2 ; apply Rgt_lt ; rewrite Rmin_gt_gt_gt ;
   split ; apply Rgt_trans with (r2:=x).
   fourier.
   apply (proj1 x_encad2).
   apply (proj2 x_encad2).
   apply (proj1 x_encad2).
   apply Rmin_r.
 assert (x_lt_x2 : x < x2).
  unfold x2 ; apply Rgt_lt ; rewrite Rmin_gt_gt_gt ;
  split ; unfold open_interval in * ; intuition ; fourier.
 assert (x1_lt_x : x1 < x).
  unfold x1 ; rewrite Rmax_lt_lt_lt ; split ; unfold open_interval in * ; intuition ; fourier.
 exists (Rmin (f x - f x1) (f x2 - f x)).
 split. apply Rmin_pos ; apply Rgt_minus. apply f_incr ; assumption.
 apply f_incr ; assumption.
 intros y [_ y_cond].
  rewrite <- f_x_b in y_cond.
  assert (Temp : forall x y d1 d2, d1 > 0 -> d2 > 0 -> Rabs (y - x) < Rmin d1 d2 -> x - d1 <= y <= x + d2).
   intros.
    split. assert (H10 : forall x y z, x - y <= z -> x - z <= y). intuition. fourier.
    apply H10. apply Rle_trans with (r2:=Rabs (y0 - x0)).
    replace (Rabs (y0 - x0)) with (Rabs (x0 - y0)). apply RRle_abs.
    rewrite <- Rabs_Ropp. unfold Rminus ; rewrite Ropp_plus_distr. rewrite Ropp_involutive.
    intuition.
    apply Rle_trans with (r2:= Rmin d1 d2). apply Rlt_le ; assumption.
    apply Rmin_l.
    assert (H10 : forall x y z, x - y <= z -> x <= y + z). intuition. fourier.
    apply H10. apply Rle_trans with (r2:=Rabs (y0 - x0)). apply RRle_abs.
    apply Rle_trans with (r2:= Rmin d1 d2). apply Rlt_le ; assumption.
    apply Rmin_r.
  assert (Temp' := Temp (f x) y (f x - f x1) (f x2 - f x)).
  replace (f x - (f x - f x1)) with (f x1) in Temp' by field.
  replace (f x + (f x2 - f x)) with (f x2) in Temp' by field.
  assert (T : f x - f x1 > 0).
   apply Rgt_minus. apply f_incr ; assumption.
  assert (T' : f x2 - f x > 0).
   apply Rgt_minus. apply f_incr ; assumption.
  assert (Main := Temp' T T' y_cond).
  clear Temp Temp' T T'.
  assert (x1_lt_x2 : x1 < x2).
   apply Rlt_trans with (r2:=x) ; assumption.
   assert (f_cont_myinterv : forall a : R, x1 <= a <= x2 -> continuity_pt f a).
    intros ; apply f_cont_interv ; split ; unfold interval in *.
    apply Rle_trans with (r2 := x1) ; intuition.
    apply Rle_trans with (r2 := x2) ; intuition.
    assert (x1_le_x2 : x1 <= x2) by intuition.
    assert (f_cont_interv2 : continuity_interval f x1 x2).
     intros a a_in_I ; apply f_cont_interv.
     split ; unfold interval in *.
     apply Rle_trans with (r2 := x1) ; intuition.
     apply Rle_trans with (r2 := x2) ; intuition.
   destruct (continuity_interval_image_interval f x1 x2 y x1_le_x2 Main f_cont_interv2) as
   [x' [x'_encad f_x'_y]].
   rewrite <- f_x_b ; rewrite <- f_x'_y.
   unfold reciprocal_interval, comp in f_eq_g.
   repeat rewrite f_eq_g.
   unfold id.
   assert (x'_encad2 : interval (x - eps) (x + eps) x').
    split ; unfold interval in *.
    apply Rle_trans with (r2:=x1) ; [ apply RmaxLess1|] ; intuition.
    apply Rle_trans with (r2:=x2) ; [ | apply Rmin_l] ; intuition.
   assert (x1_neq_x' : x1 <> x').
    intro Hfalse. rewrite Hfalse, f_x'_y in y_cond.
    assert (Hf : Rabs (y - f x) < f x - y).
     apply Rlt_le_trans with (r2:=Rmin (f x - y) (f x2 - f x)). fourier.
     apply Rmin_l.
     assert(Hfin : f x - y < f x - y).
      apply Rle_lt_trans with (r2:=Rabs (y - f x)).
      rewrite Rabs_minus_sym ; apply RRle_abs.
      assumption.
      elim (Rlt_irrefl _ Hfin).
           assert (x'_lb : x - eps < x').
    apply Rle_neq_lt.
      split ; unfold interval in *. intuition. apply Rlt_not_eq.
      apply Rle_lt_trans with (r2:=x1) ; [ apply RmaxLess1|].
      apply Rle_neq_lt ; split ; intuition.
      assert (x2_neq_x' : x2 <> x').
      intro Hfalse ; assert (Hf : Rabs (y - f x) < y - f x).
      rewrite Hfalse, f_x'_y in y_cond.
      apply Rlt_le_trans with (r2:=Rmin (f x - f x1) (y - f x)). fourier.
       apply Rmin_r.
      assert(Hfin : y - f x < y - f x).
       apply Rle_lt_trans with (r2:=Rabs (y - f x)). apply RRle_abs. fourier.
      elim (Rlt_irrefl _ Hfin).
     assert (x'_ub : x' < x + eps).
   apply Rle_neq_lt.
      split ; unfold interval in *. intuition. apply Rlt_not_eq.
      apply Rlt_le_trans with (r2:=x2).
      apply Rle_neq_lt ; split ; intuition.
      apply Rmin_l.
    apply Rabs_def1 ; fourier.
    assumption.
    split ; [apply Rle_trans with x1 | apply Rle_trans with x2] ; unfold interval in * ;
    intuition.


Qed.

Lemma continuity_pt_recip_interv2 : forall (f g:R->R) (lb ub:R),
       lb <= ub ->
       strictly_monotonous_interval f lb ub -> 
       reciprocal_interval g f lb ub ->
       continuity_interval f lb ub ->
       continuity_open_interval g (Rmin (f lb) (f ub)) (Rmax (f lb) (f ub)).
intros f g lb ub lb_le_ub f_mono f_eq_g f_cont_interv.
 destruct f_mono as [f_incr | f_decr].
 apply continuity_pt_recip_interval_prelim ; assumption.
 assert (f_incr := strictly_decreasing_strictly_increasing_interval2 _ _ _ f_decr).
 assert (ub_le_lb : - ub <= - lb) by fourier.
 assert ( T : reciprocal_interval (- g)%F (fun x : R => f (- x)) (- ub) (- lb)).
  intros x x_in_I ; unfold comp ; simpl.
  replace ((- g)%F (f (- x))) with (- (comp g f) (-x)).
  rewrite f_eq_g.
  unfold id ; simpl ; ring.
  unfold interval in * ; split ; destruct x_in_I ;
  fourier.
  reflexivity.

 assert (T2 : continuity_interval (fun x : R => f (- x)) (- ub) (- lb)).
  intros x x_in_I eps eps_pos.
  assert (x_interv : interval lb ub (-x)).
   unfold interval in * ; split ; intuition ; fourier.
  destruct (f_cont_interv (-x) x_interv eps eps_pos) as [alpha [alpha_pos Halpha]] ;
  exists alpha.
  split.
  assumption.
  intros a Ha.
  case (Req_dec x a) ; intro Hxa.
  subst ; simpl ; unfold R_dist ; unfold Rminus ; rewrite Rplus_opp_r, Rabs_R0 ;
  assumption.
  apply Halpha ; split.
  unfold D_x, no_cond ; split.
  intuition.
  intro Hf ; apply Hxa.
  replace x with (- -x) by (apply Ropp_involutive).
  replace a with (- - a) by (apply Ropp_involutive).
  apply Ropp_eq_compat ; assumption.
  simpl ; unfold R_dist, Rminus ; rewrite <- Ropp_plus_distr, Rabs_Ropp ;
  apply (proj2 Ha).



 assert (H := continuity_pt_recip_interval_prelim (fun x => f(-x)) (-g)%F
 (-ub) (-lb) ub_le_lb f_incr T T2).
 simpl in H ; repeat rewrite Ropp_involutive in H.
 
apply continuity_open_interval_opp_rev ; rewrite Rmin_comm, Rmax_comm ;
assumption.
Qed.
