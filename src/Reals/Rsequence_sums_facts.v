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

Require Import Rsequence_def Rsequence_base_facts.
Require Import Rpser_def Rpser_def_simpl.
Require Import MyRIneq.

Open Scope R_scope.
Open Scope Rseq_scope.

(** * Rseq_sum properties *)

(** Basic properties *)

Lemma Rseq_sum_simpl : forall Un n,
  (Rseq_sum Un (S n) = Rseq_sum Un n + Un (S n))%R.
Proof.
intros ; reflexivity.
Qed.

Lemma Rseq_sum_ext_strong : forall Un Vn n,
  (forall p, (p <= n)%nat -> Un p = Vn p) ->
  Rseq_sum Un n = Rseq_sum Vn n.
Proof.
intros Un Vn n ; induction n ; intro Heq.
 simpl ; apply Heq ; trivial.
 do 2 rewrite Rseq_sum_simpl ; rewrite IHn, Heq.
  reflexivity.
  trivial.
  intros ; apply Heq ; auto.
Qed.

Lemma Rseq_sum_ext : forall Un Vn,
  Un == Vn -> Rseq_sum Un == Rseq_sum Vn.
Proof.
intros Un Vn Heq n ; apply Rseq_sum_ext_strong ; trivial.
Qed.

Lemma Rseq_sum_scal_compat_l : forall (l : R) Un,
  Rseq_sum (l * Un) == l * (Rseq_sum Un).
Proof.
intros l Un n ; induction n.
 reflexivity.
 simpl ; rewrite IHn ;
  unfold Rseq_mult, Rseq_constant ;
  simpl ; ring.
Qed.

(** Compatibility with common operations *)

Lemma Rseq_sum_scal_compat_r : forall (l : R) Un,
  Rseq_sum (Un * l) == Rseq_sum Un * l.
Proof.
intros l Un n ; induction n.
 reflexivity.
 simpl ; rewrite IHn ;
  unfold Rseq_mult, Rseq_constant ;
  simpl ; ring.
Qed.

Lemma Rseq_sum_opp_compat : forall Un,
  Rseq_sum (- Un) == - Rseq_sum Un.
Proof.
intros Un n ; induction n.
 reflexivity.
 simpl ; rewrite IHn ;
  unfold Rseq_opp ;
  simpl ; ring.
Qed.

Lemma Rseq_sum_plus_compat : forall Un Vn,
  Rseq_sum (Un + Vn) == Rseq_sum Un + Rseq_sum Vn.
Proof.
intros Un Vn n ; induction n.
 reflexivity.
 simpl ; rewrite IHn ;
  unfold Rseq_plus ; simpl ;
  ring.
Qed.

Lemma Rseq_sum_minus_compat : forall Un Vn,
  Rseq_sum (Un - Vn) == Rseq_sum Un - Rseq_sum Vn.
Proof.
intros Un Vn n ; rewrite Rseq_sum_ext with (Un - Vn) (Un + (- Vn)) _,
 Rseq_sum_plus_compat.
 unfold Rseq_plus, Rseq_minus ; rewrite Rseq_sum_opp_compat ; reflexivity.
 unfold Rseq_minus ; intro ; reflexivity.
Qed.

Lemma Rseq_sum_shift_compat : forall Un n,
  Rseq_sum (Rseq_shift Un) n = (Rseq_shift (Rseq_sum Un) n - Un O)%R.
Proof.
intros Un n ; induction n ;
 [| simpl ; rewrite IHn] ;
 unfold Rseq_shift, Rseq_minus ; simpl ; ring.
Qed.

Lemma Rseq_sum_shifts_compat : forall Un k n,
  Rseq_sum (Rseq_shifts Un (S k)) n = (Rseq_shifts (Rseq_sum Un) (S k) n - Rseq_sum Un k)%R.
Proof.
intros Un k n ; induction n.
 unfold Rseq_shifts, Rseq_minus ; simpl ; rewrite plus_0_r ; ring.
 simpl ; rewrite IHn ; unfold Rseq_minus, Rseq_shifts ;
  simpl ; rewrite <- (plus_n_Sm k n) ; simpl ; ring.
Qed.

Lemma Rseq_sum_reindex_compat : forall Un n,
  Rseq_sum Un n = Rseq_sum (fun i => Un (n - i)%nat) n.
Proof.
intros Un n ; revert Un ; induction n ; intro Un.
 reflexivity.
 do 2 rewrite Rseq_sum_simpl.
 rewrite (IHn (fun i => Un (S n - i)%nat)), minus_diag.
 rewrite (Rseq_sum_ext_strong (fun i => Un (S n - (n - i))%nat) (Rseq_shift Un)).
 rewrite Rseq_sum_shift_compat ; unfold Rseq_shift ; simpl ; ring.
 intros m m_bd ; unfold Rseq_shift ; replace (S n - (n - m))%nat with (S m) by omega ;
 reflexivity.
Qed.

Lemma Rseq_prod_comm: forall An Bn, An # Bn == Bn # An.
Proof.
intros An Bn n ; unfold Rseq_prod, Rseq_mult ;
 rewrite Rseq_sum_reindex_compat ; apply Rseq_sum_ext_strong ;
 intros p p_ub ; replace (n - (n - p))%nat with p by omega ;
 ring.
Qed.

Lemma Rseq_sum_prod_compat: forall An Bn n,
  Rseq_sum (An # Bn) n =
  Rseq_sum (fun i => (Rseq_sum Bn i) * An (n - i)%nat)%R n.
Proof.
intros An Bn n ; induction n.
 unfold Rseq_prod, Rseq_mult ; simpl ; apply Rmult_comm.
 transitivity (Rseq_sum ((fun i => (An i * (Rseq_sum Bn (n - i)%nat))%R) +
  (fun i => (An i * Bn (S (n - i))%nat))%R)%Rseq n + An (S n) * Bn O)%R.
 rewrite Rseq_sum_plus_compat, Rseq_sum_simpl, IHn ; unfold Rseq_plus ;
 rewrite Rplus_assoc ; apply Rplus_eq_compat.
 rewrite Rseq_sum_reindex_compat ; apply Rseq_sum_ext_strong ;
  intros p p_ub ; replace (n - (n - p))%nat with p by omega ; apply Rmult_comm.
 replace O with ((S n) - S n)%nat by omega ; unfold Rseq_prod ;
  rewrite Rseq_sum_simpl ; apply Rplus_eq_compat_r ; apply Rseq_sum_ext_strong ;
  intros p p_ub ; unfold Rseq_mult ; replace (S n - p)%nat with (S (n - p)) by omega ;
  reflexivity.
 transitivity (Rseq_sum (fun i => (An i * (Rseq_sum Bn (S n - i)))%R) (S n)).
 rewrite Rseq_sum_simpl, minus_diag ; apply Rplus_eq_compat ; [| trivial].
 apply Rseq_sum_ext_strong ; intros p p_ub ; unfold Rseq_plus ;
 replace (S n - p)%nat with (S (n - p)) by omega ; rewrite Rseq_sum_simpl ; ring.
 rewrite Rseq_sum_reindex_compat ; apply Rseq_sum_ext_strong ; intros p p_ub ;
 replace (S n - (S n - p))%nat with p by omega ; apply Rmult_comm.
Qed.


(** Compatibility with the orders *)

Lemma Rseq_sum_pos_strong : forall An n,
  (forall p, (p <= n)%nat -> 0 <= An p) ->
  0 <= Rseq_sum An n.
Proof.
intros An n ; induction n ; intro Hpos.
 simpl ; apply Hpos ; trivial.
 rewrite Rseq_sum_simpl ; apply Rplus_le_le_0_compat ;
 [apply IHn ; intros p p_bd |] ; apply Hpos ; omega.
Qed.

Lemma Rseq_sum_pos: forall An n,
 (forall n, 0 <= An n) ->  0 <= Rseq_sum An n.
Proof.
intros ; apply Rseq_sum_pos_strong ; trivial.
Qed.

Lemma Rseq_sum_le_compat_strong: forall An Bn n,
 (forall p, (p <= n)%nat -> An p <= Bn p) ->
 Rseq_sum An n <= Rseq_sum Bn n.
Proof.
intros An Bn n Hle ; induction n.
 simpl ; apply Hle ; trivial.
 simpl ; transitivity (Rseq_sum Bn n + An (S n))%R.
  apply Rplus_le_compat_r ; apply IHn ; auto.
  apply Rplus_le_compat_l ; apply Hle ; trivial.
Qed.

Lemma Rseq_sum_le_compat: forall An Bn n,
 (forall n, An n <= Bn n) -> Rseq_sum An n <= Rseq_sum Bn n.
Proof.
intros ; apply Rseq_sum_le_compat_strong ; trivial.
Qed.

Lemma Rseq_sum_lt_compat_strong: forall An Bn n,
 (forall p, (p <= n)%nat -> An p < Bn p) ->
 Rseq_sum An n < Rseq_sum Bn n.
Proof.
intros An Bn n Hlt ; induction n.
 simpl ; apply Hlt ; trivial.
 simpl ; transitivity (Rseq_sum Bn n + An (S n))%R.
  apply Rplus_lt_compat_r ; apply IHn ; auto.
  apply Rplus_lt_compat_l ; apply Hlt ; trivial.
Qed.

Lemma Rseq_sum_lt_compat: forall An Bn n,
 (forall n, An n < Bn n) -> Rseq_sum An n < Rseq_sum Bn n.
Proof.
intros ; apply Rseq_sum_lt_compat_strong ; trivial.
Qed.

Lemma Rseq_sum_triang: forall An n,
  Rabs (Rseq_sum An n) <= Rseq_sum (| An |) n.
Proof.
intros An n ; induction n.
 unfold Rseq_abs ; simpl ; reflexivity.
 do 2 rewrite Rseq_sum_simpl ; eapply Rle_trans ;
 [eapply Rabs_triang |] ; apply Rplus_le_compat ;
 [assumption | reflexivity].
Qed.

(** Partition *)

Lemma Rseq_sum_even_odd_split : forall (An : Rseq) n,
  (Rseq_sum (fun i => An (2 * i)%nat) n +
  Rseq_sum (fun i => An (S (2 * i))%nat) n
  = Rseq_sum An (S (2 * n)))%R.
Proof.
intros An n ; induction n.
 reflexivity.
 replace (2 * (S n))%nat with (S (S (2 * n))) by ring.
 do 4 rewrite Rseq_sum_simpl.
 replace (2 * (S n))%nat with (S (S (2 * n))) by ring.
 rewrite <- IHn ; ring.
Qed.

Lemma Rseq_sum_even_odd_split' : forall An n,
  (Rseq_sum (fun i => An (2 * i)%nat) (S n) +
  Rseq_sum (fun i => An (S (2 * i))) n
  = Rseq_sum An (2 * (S n)))%R.
Proof.
intros An n ; replace (2 * S n)%nat with (S (S (2 * n))) by ring ;
 do 2 rewrite Rseq_sum_simpl ; rewrite <- Rseq_sum_even_odd_split ;
 replace (2 * S n)%nat with (S (S (2 * n))) by ring ; ring.
Qed.

(** * Rseq_pps : compatibility with common operations. *)

Section Rseq_pps_facts.

Lemma Rseq_pps_simpl : forall An x n,
  Rseq_pps An x (S n) = (Rseq_pps An x n + (An (S n) * pow x (S n)))%R.
Proof.
intros ; reflexivity.
Qed.

Lemma Rseq_pps_0_simpl : forall An n,
 Rseq_pps An 0 n = An O.
Proof.
intros An n ; induction n.
 unfold Rseq_pps, gt_pser, Rseq_mult ; simpl ;
  rewrite Rmult_1_r ; reflexivity.
 rewrite Rseq_pps_simpl, IHn, pow_i ; [ring | omega].
Qed.

Lemma Rseq_pps_O_simpl : forall An x,
  Rseq_pps An x O = An O.
Proof.
intros An x ; unfold Rseq_pps ; apply gt_pser_0.
Qed.

Lemma Rseq_pps_ext : forall An Bn x,
  An == Bn ->
  Rseq_pps An x == Rseq_pps Bn x.
Proof.
intros An Bn x Hext ; apply Rseq_sum_ext ;
 intro n ; unfold gt_pser, Rseq_mult ; rewrite Hext ;
 reflexivity.
Qed.

Lemma Rseq_pps_scal_compat_l : forall (l : R) An x,
  Rseq_pps (l * An) x == l * Rseq_pps An x.
Proof.
intros l An x n ; unfold Rseq_pps ;
 rewrite Rseq_sum_ext with _ (l * (An * (pow x))) _.
 apply Rseq_sum_scal_compat_l.
 clear ; intro n ; unfold gt_pser, Rseq_mult, Rseq_constant ;
  ring.
Qed.

Lemma Rseq_pps_scal_compat_r : forall (l : R) An x,
  Rseq_pps (An * l) x == Rseq_pps An x * l.
Proof.
intros l An x n ; unfold Rseq_pps ;
 rewrite Rseq_sum_ext with _ ((An * (pow x)) * l) _.
 apply Rseq_sum_scal_compat_r.
 clear ; intro n ; unfold gt_pser, Rseq_mult, Rseq_constant ;
  ring.
Qed.

Lemma Rseq_pps_opp_compat : forall An x,
  Rseq_pps (- An) x == - Rseq_pps An x.
Proof.
intros An x n ; unfold Rseq_pps ;
 rewrite Rseq_sum_ext with _ (- (An * (pow x))) _.
 apply Rseq_sum_opp_compat.
 clear ; intro n ; unfold gt_pser, Rseq_mult, Rseq_opp ;
  ring.
Qed.

Lemma Rseq_pps_plus_compat : forall An Bn x,
  Rseq_pps (An + Bn) x == Rseq_pps An x + Rseq_pps Bn x.
Proof.
intros An Bn x n ; unfold Rseq_pps ;
 rewrite Rseq_sum_ext with _ ((An * (pow x)) + (Bn * (pow x))) _.
 apply Rseq_sum_plus_compat.
 clear ; intro n ; unfold gt_pser, Rseq_mult, Rseq_plus ;
  ring.
Qed.

Lemma Rseq_pps_abs_unfold : forall An x,
  Rseq_pps_abs An x == Rseq_pps (| An |) (Rabs x).
Proof.
intros An x ; apply Rseq_sum_ext ; apply gt_abs_pser_unfold.
Qed.

(** * Rpser_abs, Rpser *)

Lemma Rpser_abs_unfold : forall An r l,
  Rpser_abs An r l <-> Rpser (| An |) (Rabs r) l.
Proof.
intros An r l ; split ; intro Hyp ; unfold Rpser, Rpser_abs ;
assert (tmp := Rseq_pps_abs_unfold An r) ; eapply Rseq_cv_eq_compat ;
eauto ; symmetry ; assumption.
Qed.

End Rseq_pps_facts.
