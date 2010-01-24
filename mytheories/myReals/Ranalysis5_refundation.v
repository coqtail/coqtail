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
Open Local Scope R_scope.

(** * Basic notions *)

Definition interval (lb ub x:R) := lb <= x <= ub.

Definition continuity_interval (f : R -> R) (lb ub:R) := forall x:R,
      interval lb ub x -> continuity_pt f x.

Definition injective_interval (f : R -> R) (lb ub:R) := forall (x y:R),
      interval lb ub x -> interval lb ub y -> f x = f y -> x = y.
Definition surjective_interval (f : R -> R) (lb ub:R) := forall y:R,
      interval lb ub y -> exists x:R, y = f x.

Definition injective (f : R -> R) := forall (x y:R), f x = f y -> x = y.
Definition surjective (f : R -> R) := forall y:R, exists x:R, y = f x.
Definition bijective (f : R -> R) := injective f /\ surjective f.

Definition strictly_increasing_interval (f : R -> R) (lb ub:R) := forall x y,
       interval lb ub x -> interval lb ub y -> x < y -> f x < f y.
Definition strictly_decreasing_interval (f : R -> R) (lb ub:R) := forall x y,
       interval lb ub x -> interval lb ub y -> x < y -> f y < f x.
Definition strictly_monotonous_interval (f : R -> R) (lb ub : R) :=
     {strictly_increasing_interval f lb ub} + {strictly_decreasing_interval f lb ub}.

Definition increasing_interval (f : R -> R) (lb ub:R) := forall x y,
       interval lb ub x -> interval lb ub y -> x <= y -> f x <= f y.
Definition decreasing_interval (f : R -> R) (lb ub:R) := forall x y,
       interval lb ub x -> interval lb ub y -> x <= y -> f y <= f x.
Definition monotonous_interval (f : R -> R) (lb ub : R) :=
     {increasing_interval f lb ub} + {decreasing_interval f lb ub}.

Definition strictly_increasing (f : R -> R) := forall x y, x < y -> f x < f y.
Definition strictly_decreasing (f : R -> R) := forall x y, x < y -> f y < f x.
Definition strictly_monotonous (f : R -> R) :=
     {strictly_increasing f} + {strictly_decreasing f}.

Definition reciprocal_interval (f g:R -> R) (lb ub:R) := forall x,
       interval lb ub x -> (comp f g) x = id x.

Definition reciprocal (f g:R -> R) := forall x, (comp f g) x = id x.

(** Manipulation *)

Lemma strictly_monotonous_injective_interval : forall f lb ub,
      strictly_monotonous_interval f lb ub -> injective_interval f lb ub.
Proof.
intros f c r Hf ; destruct Hf as [f_incr | f_decr] ;
 intros x y x_in_B y_in_B fx_eq_fy ;
 destruct (Rlt_le_dec x y) as [x_lt_y | x_ge_y].
  assert (H := f_incr _ _ x_in_B y_in_B x_lt_y) ; rewrite fx_eq_fy in H ;
  elim (Rlt_irrefl _ H).
  destruct x_ge_y as [y_lt_x | x_eq_y].
   assert (H := f_incr _ _ y_in_B x_in_B y_lt_x) ; rewrite fx_eq_fy in H ;
   elim (Rlt_irrefl _ H).
   symmetry ; assumption.
  assert (H := f_decr _ _ x_in_B y_in_B x_lt_y) ; rewrite fx_eq_fy in H ;
  elim (Rlt_irrefl _ H).
  destruct x_ge_y as [y_lt_x | x_eq_y].
   assert (H := f_decr _ _ y_in_B x_in_B y_lt_x) ; rewrite fx_eq_fy in H ;
   elim (Rlt_irrefl _ H).
   symmetry ; assumption.
Qed.

Lemma strictly_increasing_increasing_interval : forall f lb ub,
     strictly_increasing_interval f lb ub -> increasing_interval f lb ub.
Proof.
intros f lb ub f_incr x y x_in_I y_in_I x_le_y.
 destruct x_le_y as [x_lt_y | x_eq_y].
 left ; apply f_incr ; assumption.
 right ; subst ; reflexivity.
Qed.

Lemma strictly_decreasing_decreasing_interval : forall f lb ub,
     strictly_decreasing_interval f lb ub -> decreasing_interval f lb ub.
Proof.
intros f lb ub f_incr x y x_in_I y_in_I x_le_y.
 destruct x_le_y as [x_lt_y | x_eq_y].
 left ; apply f_incr ; assumption.
 right ; subst ; reflexivity.
Qed.

Lemma strictly_increasing_strictly_decreasing_interval : forall f lb ub,
    strictly_increasing_interval f lb ub -> strictly_decreasing_interval (-f)%F lb ub.
Proof.
intros f c r f_incr ; intros x y x_in_B y_in_B x_lt_y.
 assert (H := f_incr _ _ x_in_B y_in_B x_lt_y).
 unfold opp_fct ; intuition.
Qed.

Lemma strictly_decreasing_strictly_increasing_interval : forall f lb ub,
    strictly_decreasing_interval f lb ub -> strictly_increasing_interval (-f)%F lb ub.
Proof.
intros f c r f_incr ; intros x y x_in_B y_in_B x_lt_y.
 assert (H := f_incr _ _ x_in_B y_in_B x_lt_y).
 unfold opp_fct ; intuition.
Qed.

Lemma reciprocal_opp_compat_interval : forall f g lb ub,
       reciprocal_interval f g lb ub ->
       reciprocal_interval (-f)%F (fun x => g (-x)) (-ub) (-lb).
Proof.
intros f g lb ub f_recip_g x x_in_I.
 unfold comp.
 replace ((- f)%F (g (- x))) with (- (comp f g) (-x)).
 rewrite f_recip_g.
 unfold id ; ring.
 unfold interval in * ; destruct x_in_I.
 split ; fourier.
 reflexivity.
Qed.

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

Lemma continuity_pt_recip_interval : forall (f g:R->R) (lb ub:R),
       strictly_monotonous_interval f lb ub -> 
       reciprocal_interval f g lb ub ->
       continuity_interval f lb ub ->
       continuity_interval g (Rmin (f lb) (f ub)) (Rmax (f lb) (f ub)).
Proof.
Admitted.
