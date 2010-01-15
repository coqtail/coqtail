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

Require Import NArith.
Require Import Omega.
Require Import Max.
Require Import Tools.

Inductive mod (n:nat) : nat -> nat -> Prop :=
     | mod_base : forall k, k < n -> mod n k k
     | mod_nS : forall k l, mod n k l -> mod n k (n + l).

Lemma pred_itere : forall n, 0 < n -> forall m, {k:nat | m < n} + {k | m = n + k}.
Proof.
intros n n_pos m ; induction m.
 left ; exists 0 ; assumption.
 case (le_lt_dec (S m) n) ; intro Hyp.
 case (le_lt_eq_dec _ _ Hyp) ; clear Hyp ; intro Hyp.
 left ; exists 0 ; assumption.
 right ; exists 0 ; rewrite Hyp ; trivial.
 case IHm ; intro H.
 left ; exists 0 ; apply False_ind ; destruct H as (_,Hf) ; omega.
 destruct H as (k,Hk) ; right ; exists (S k).
 rewrite <- plus_n_Sm ; rewrite Hk ; simpl ; reflexivity.
Qed.

Lemma mod_bounded : forall n m l, mod n l m -> l < n.
Proof.
intros n m l modnl ; induction modnl ; assumption.
Qed.

Lemma mod_uniqueness1 : forall n m l, l < n -> mod n l m -> forall p, p < n ->
      p <> l -> ~mod n p m. 
Proof.
intros n m l l_ub modnl p p_ub p_neq Hf ;
 induction modnl.
 inversion Hf ; intuition.
 apply IHmodnl.
 assumption.
 assumption.
 inversion Hf.
 assert (Temp := mod_bounded _ _ _ Hf).
 apply False_ind ; clear -H1 Temp ; intuition.
 assert (Temp := plus_reg_l _ _ _ H) ; rewrite <- Temp ; assumption.
Qed.

Lemma mod_uniqueness2 : forall n m l l', l < n -> l' < n -> mod n m l' -> mod n m l -> l = l'.
Proof.
intros n m l l' l_ub l'_ub modnl modnl' ; inversion modnl'.
 inversion modnl ; intuition.
 rewrite <- H1 in l_ub ; apply False_ind ; clear -l_ub ; intuition.
Qed.

Lemma mod_uniqueness : forall n m l l', mod n l m -> mod n l' m -> l = l'.
Proof.
intros n m l l' modnl modnl'.
 induction modnl.
 induction modnl'.
 reflexivity.
 apply False_ind ; intuition.
 apply IHmodnl ; inversion modnl'.
 apply False_ind ; intuition.
 assert (Temp := plus_reg_l _ _ _ H) ;
 rewrite <- Temp ; assumption.
Qed.

Lemma disjoints_prelim (n:nat) : 0 < n -> forall M m, m < max n M ->
      {k | k < n /\ mod n k m /\ forall l, l <> k -> ~ mod n l m}.
Proof.
intros n n_pos M ; induction M ; intros m m_ub.
 rewrite max_l in m_ub ; [| intuition].
 exists m ; repeat split ; [assumption | |].
 constructor ; assumption.
 intros l l_neq Hyp ; apply l_neq ; apply mod_uniqueness with (n:=n) (m:=m).
 intuition.
 constructor ; assumption.
 case (le_lt_dec m (max n M)) ; intro m_ub'.
 case (le_lt_eq_dec _ _ m_ub') ; clear m_ub' ; intro m_ub'.
 apply IHM ; intuition.
 case (pred_itere _ n_pos m) ; intro Hyp.
  exists 0 ; apply False_ind ; destruct Hyp as (_,Hf).
  assert (Hf' : n <= m).
  apply le_trans with (max n M) ; [apply le_max_l | rewrite m_ub' ; intuition].
  intuition.
  destruct Hyp as (k,Hk).
  case (le_lt_dec k n) ; intro Temp.
  case (le_lt_eq_dec _ _ Temp) ; clear Temp ; intro Temp.
  exists k ; repeat split ; [assumption | |].
  rewrite Hk ; constructor ; constructor ; assumption.
  intros l l_neq modnl ; assert (l_ub := mod_bounded _ _ _ modnl) ;
  apply (mod_uniqueness1 _ _ _ l_ub modnl _ Temp).
  intro Hf ; apply l_neq ; symmetry ; assumption.
  rewrite Hk ; constructor ; constructor ; assumption.
  exists 0 ; repeat split.
  assumption.
  rewrite Hk ; constructor.
  replace n with (n+0) in Temp by intuition ; rewrite Temp ; repeat constructor ; assumption.
  intros l l_neq modnl ; rewrite Hk in modnl.
  apply l_neq ; apply mod_uniqueness2 with (n:=n) (m:=l).
  apply (mod_bounded _ _ _ modnl).
  assumption.
  inversion modnl.
  apply False_ind ; intuition.
  assert (Temp2 := plus_reg_l _ _ _ H) ;
  replace n with (n+0) in Temp by intuition ; rewrite Temp2, Temp in H1.
  clear -H1 ; inversion H1.
  apply False_ind ; intuition.
  repeat (rewrite itere_S in H) ; assert (Temp2 := plus_reg_l _ _ _ H) ; rewrite <- Temp2 ;
  assumption.
  constructor.
  apply (mod_bounded _ _ _ modnl).
  assert (k_ub : k < max n M).
  rewrite Hk in m_ub' ; intuition.
  destruct (IHM k k_ub) as (p, [p_ub [modnp notmodnl]]) ; exists p ; repeat split.
  assumption.
  assert (H := mod_nS _ _ _ modnp).
  rewrite Hk ; assumption.
  intros l l_neq_p modnl.
  rewrite Hk in modnl ; inversion modnl.
  clear -H ; intuition.
  repeat (rewrite itere_S in H) ; assert (Temp2 := plus_reg_l _ _ _ H) ;
  replace n with (n+0) in Temp by intuition.
  rewrite Temp2 in H1.
  apply (notmodnl _ l_neq_p H1).
  exists 0 ; apply False_ind.
  assert (max n M = M).
  clear -m_ub m_ub' ; induction n.
  intuition.
  case (max_dec (S n) M) ; intro H.
  rewrite H in m_ub'.
  case (max_dec (S n) (S M)) ; intro H'.
  rewrite H' in m_ub ; apply False_ind ; intuition.
  assert (M < m).
  apply le_lt_trans with (max (S n) M).
  apply le_max_r.
  rewrite H ; assumption.
  rewrite H' in m_ub.
  apply False_ind ; intuition.
  assumption.
  assert (m < max (S n) (S M)).
  apply lt_le_trans with (max n (S M)).
  assumption.
  generalize M ; clear ; induction n.
  intuition.
  intro M ; replace (max (S (S n)) (S M)) with (S (max (S n) M)) by intuition.
  replace (max (S n) (S M)) with (S (max n M)) by intuition.
  apply le_n_S.
  destruct M.
  repeat (rewrite max_comm ; simpl) ; intuition.
  apply IHn.
  simpl in H0.
  intuition.
Qed.

Lemma disjoints (n:nat) : 0 < n -> forall m,
      {k | k < n /\ mod n k m /\ forall l, l <> k -> ~ mod n l m}.
Proof.
intros n n_pos m ; apply disjoints_prelim with (M:= (S m)) ; intuition.
Qed.

Lemma surjectif : forall n m p, m < n -> mod n m (n * p + m).
Proof.
intros n m p m_ub ; induction p.
 replace (n * 0) with 0 by omega ; constructor ; assumption.
 replace ((n * S p) + m) with (n + ((n * p) + m)).
 constructor ; assumption.
 rewrite mult_succ_r ; omega.
Qed.

Lemma n_decomp : forall N n m p, 0 < n -> p < (S N) * n -> mod n m p -> {k | p = k * n + m}.
Proof.
intro N ; induction N ; intros n m p n_pos p_ub p_modn.
 exists 0 ; inversion p_modn.
 intuition.
 rewrite <- H1 in p_ub ; apply False_ind ; intuition.
 case (le_lt_dec p ((S N) * n)) ; intro p_ub2.
 case (le_lt_eq_dec _ _ p_ub2) ; intro H.
 apply (IHN _ _ _ n_pos H p_modn).
  rewrite H in p_modn.
  replace (S N * n) with (N * n + n) in p_modn.
  destruct (IHN n m (N * n) n_pos) as (k, Hk).
  apply mult_lt_compat_r ; [constructor | apply n_pos].
  inversion p_modn.
  apply False_ind.
  assert (N * n < 0).
  apply plus_lt_reg_l with n.
  intuition.
  apply (lt_n_O _ H3).
  replace l with (N * n) in H2.
  assumption.
  intuition.
  exists (S k) ; simpl ; rewrite <- plus_assoc ; rewrite <- Hk ; intuition.
  apply plus_comm.
  assert (Hrew : p = n + (p - n)).
  apply le_plus_minus.
  apply le_trans with (S N * n) ; intuition.
  apply le_trans with (S 0 * n) ; intuition ; apply mult_le_compat_r ;
  intuition.
  destruct (IHN n m (p-n) n_pos) as (k, Hk).
  apply plus_lt_reg_l with n.
  rewrite <- Hrew ; intuition.
  rewrite plus_comm in Hrew ; rewrite Hrew in p_modn ; inversion p_modn.
  apply False_ind ; apply lt_irrefl with n.
  apply lt_trans with (S N * n).
  intuition.
  apply lt_trans with p.
  assumption.
  rewrite Hrew ; assumption.
  assert (Hrew' : l = p - n) by intuition.
  rewrite Hrew' in H1 ; assumption.
  exists (S k) ; simpl ; rewrite <- plus_assoc ; rewrite <- Hk ; intuition.
Qed.