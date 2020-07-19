Require Raxiom.
Require Import Arith QArith Qabs Max Qminmax.
Require Import Lia Lra.

(* changer le nom Qreals est deja utilisé dans la stdlib *)
(* (Tentative of) instantiation of real numbers without using Coq's stdlib *)

Open Scope Q_scope.

Definition cauchy (a : nat -> Q) : Prop :=
  forall eps : Q,
    0 < eps ->
    exists N : nat,
    forall p q,
      le N p -> le N q ->
      Qabs (a p - a q) <= eps.

(* Definition cauchy_prop (a : nat -> Prop) : Prop := *)
(*   exists N, forall p q, le N p -> le N q -> a p <-> a q. *)

Definition cauchy_continuous1 (f : Q -> Q) :=
  forall a, cauchy a -> cauchy (fun n => f (a n)).

Definition cauchy_continuous2 (f : Q -> Q -> Q) :=
  forall a b, cauchy a -> cauchy b -> cauchy (fun n => f (a n) (b n)).

Lemma const_cauchy x : cauchy (fun _ => x). Abort.
Lemma Qopp_cauchy : cauchy_continuous1 Qopp. Abort.
Lemma Qabs_cauchy : cauchy_continuous1 Qabs. Abort.
Lemma Qplus_cauchy : cauchy_continuous2 Qplus. Abort.
Lemma Qmult_cauchy : cauchy_continuous2 Qmult. Abort.

Definition strong_le_seq (a b : nat -> Q) : Prop := exists N, forall n, le N n -> a n <= b n.
Definition pos (a : nat -> Q) : Prop := exists q, 0 < q /\ strong_le_seq (fun _ => q) a.

Module Rrealize : Raxiom.CReals.
  (*Inductive _R : Type := Rcauchy : forall Un, Zseq_Cauchy Un -> _R.*)

  Record R_ : Type :=
    Rdef { approx : nat -> Q;
           R_cauchy : cauchy approx }.

  Definition R := R_.

  Ltac qelim :=
    repeat
      match goal with
      | a : Q |- _ => let a1 := fresh a in destruct a as [a a1]
      end;
    unfold Qminus, Qopp, Qmult, Qplus, Qabs, Qdiv, Qinv, Qlt, Qle in *; simpl in *.

  Program Definition Q2R (x : Q) := Rdef (fun _ => x) _.
  Next Obligation.
  Proof.
    intros eps Heps.
    exists O; intros p q _ _.
    ring_simplify (x - x).
    qelim.
    lia.
  Qed.

  Definition R0 := Q2R 0.
  Definition R1 := Q2R 1.

  Instance Qle_Setoid : PreOrder Qle. Admitted.
  Instance Qlt_Setoid : StrictOrder Qle. Admitted.
  Instance Qplus_Qle : Proper (Qle ==> Qle ==> Qle) Qplus. Admitted.

  Lemma eps_split a b ε : a <= ε / 2 -> b <= ε / 2 -> a + b <= ε.
  Proof.
    intros -> ->. qelim. lia.
  Qed.

  Lemma Qmult_pos (a b : Q) : 0 < a -> 0 < b -> 0 < a * b. Admitted.
  Lemma Qdiv_pos (a b : Q) : 0 < a -> 0 < b -> 0 < a / b. Admitted.
  (* Lemma Qplus_pos (a b : Q) : 0 < a -> 0 < b -> 0 < a + b. Admitted. *)
  Lemma Qmax_pos_l (a b : Q) : 0 < a -> 0 < Qmax a b. Admitted.
  Lemma Qmax_pos_r (a b : Q) : 0 < b -> 0 < Qmax a b. Admitted.
  Lemma Qplus_pos_l (a b : Q) : 0 < a -> 0 <= b -> 0 < a + b. Admitted.
  Lemma Qplus_pos_r (a b : Q) : 0 <= a -> 0 < b -> 0 < a + b. Admitted.
  Lemma Qplus_pos' (a b : Q) : 0 <= a -> 0 <= b -> 0 <= a + b. Admitted.
  Lemma pos_pos' (a : Q) : 0 < a -> 0 <= a. Admitted.
  Lemma Zpos_pos (d n : positive) : 0 < Zpos d # n. Admitted.
  Lemma Qabs_pos' (a : Q) : 0 <= Qabs a. Admitted.
  Lemma Qmult_Qle (a b c d : Q) : 0 <= a <= b -> 0 <= c <= d -> a * c <= b * d. Admitted.
  Hint Resolve Qmult_pos Qdiv_pos (* Qplus_pos *) Qplus_pos_l Qplus_pos_r Qabs_pos' Qplus_pos' pos_pos' eps_split : qarith.

  Program Definition Radd a b := Rdef (fun n => approx a n + approx b n) _.
  (*Program Definition Radd a b := match a, b with Rcauchy u Hu, Rcauchy v Hv =>
    Rcauchy (fun n => (u n + v n)%Z) _
  end.*)
  Next Obligation.
  Proof.
    destruct a as (u, Hu).
    destruct b as (v, Hv).
    intros ε Hε. simpl approx.
    destruct (Hu (ε / 2)) as (Nu, HNu); auto with qarith.
    destruct (Hv (ε / 2)) as (Nv, HNv); auto with qarith.
    exists (max Nu Nv).
    intros p q Hp Hq.
    assert (u p + v p - (u q + v q) == u p - u q + (v p - v q)) as -> by ring.
    rewrite Qabs_triangle, HNu, HNv. auto 20 with qarith. all: eauto with *.
  Qed.

  Program Definition Rmul a b := Rdef (fun n => approx a n * approx b n) _.
  Next Obligation.
    destruct a as (a, Ca).
    destruct b as (b, Cb).
    simpl approx.
    (* we need to bound |a| and |b| *)
    destruct (Ca 1) as [na0 Hna0]. qelim. lia.
    destruct (Cb 1) as [nb0 Hnb0]. qelim. lia.
    pose (n0 := max na0 nb0).
    pose (bound := Qmax (1 + Qabs (a n0)) (1 + Qabs (b n0))).
    assert (Hbound : 0 < bound) by (apply Qmax_pos_l, Qplus_pos_l; eauto 10 with qarith).
    (* assert (Hbound : 0 < bound) by (apply Qplus_pos_r; try apply Qplus_pos'; eauto 10 with qarith). *)
    assert (Ba : forall n, le n0 n -> Qabs (a n) <= bound).
    { intros n Hn. assert (a n == (a n - a n0) + a n0) as -> by ring.
      rewrite Qabs_triangle. unfold bound. rewrite <-Q.le_max_l. apply Qplus_Qle.
      apply Hna0. transitivity n0. all: unfold n0; auto 10 with *. }
    assert (Bb : forall n, le n0 n -> Qabs (b n) <= bound).
    { intros n Hn. assert (b n == (b n - b n0) + b n0) as -> by ring.
      rewrite Qabs_triangle. unfold bound. rewrite <-Q.le_max_r. apply Qplus_Qle.
      apply Hnb0. transitivity n0. all: unfold n0; auto 10 with *. }
    intros ε Hε.
    destruct (Ca (ε / 2 / bound)) as [na1 Hna1]. auto 20 with qarith.
    destruct (Cb (ε / 2 / bound)) as [nb1 Hnb1]. auto 20 with qarith.
    exists (max n0 (max na1 nb1)). intros p q Hp Hq.
    assert (a p * b p - a q * b q == a p * (b p - b q) + b q * (a p - a q)) as -> by ring.
    rewrite Qabs_triangle.
    assert (ε == bound * (ε / 2 / bound) + bound * (ε / 2 / bound)) as -> by (field; auto with *).
    rewrite 2Qabs_Qmult.
    apply Qplus_Qle.
    - apply Qmult_Qle.
      + split; auto with *. apply Ba. lia.
      + split; auto with *. apply Hnb1; lia.
    - apply Qmult_Qle.
      + split; auto with *. apply Bb. lia.
      + split; auto with *. apply Hna1; lia.
  Qed.

  Program Definition Ropp a := Rdef (fun n => - approx a n) _.
  Next Obligation.
    destruct a as (a, Ca).
    intros ε Hε.
    simpl approx.
    destruct (Ca ε Hε) as (N, HN).
    exists N; intros p q Hp Hq.
    rewrite <-(HN p q Hp Hq).
    rewrite <-Qabs_opp at 1.
    ring_simplify (- (- a p - - a q)).
    reflexivity.
  Qed.

  Definition Rsub a b := Radd a (Ropp b).

  Program Definition Rabs (r : R) := Rdef (

  Lemma Req_spec (a b : R) : Req a b <-> forall ε, ε > 0 -> Rabs (a - b) <= ε.
  Proof.
    ?
  Qed.

  (*Inductive _Rlt : R -> R -> Type :=
    | Rlt_c : forall (neps : nat) (N : nat) u (Hu : Zseq_Cauchy u) v (Hv : Zseq_Cauchy v),
        (forall n, le N n -> u n * Zpos (pow2 neps) + 1 < v n * Zpos (pow2 neps))%Z ->
        _Rlt (Rcauchy u Hu) (Rcauchy v Hv).*)

  (*Definition Rlt (a b : R) : Type := match a, b with
    | Rcauchy u Hu, Rcauchy v Hv => sigT (fun neps => sigT (fun N =>
        forall n, le N n -> u n * Zpos (pow2 neps) + Zpos (pow2 n) < v n * Zpos (pow2 neps))%Z)
  end.*)

  Definition Rpos (a : R) : Prop := exists δ, δ > 0 /\ exists N, forall n, le N n -> δ <= approx a n.
  Definition Rlt (a b : R) : Prop := Rpos (Rsub b a).
  Definition Rgt (a b : R) : Prop := Rpos (Rsub a b).
  Definition Rdiscr (r1 r2 : R) := sum (Rlt r1 r2) (Rlt r2 r1).
  Definition Req (r1 r2 : R) := Rdiscr r1 r2 -> False.
  Definition Rle (r1 r2 : R) := sumor (Rlt r1 r2) (Req r1 r2).
  Definition Rge (r1 r2 : R) := Rle r2 r1.

  Lemma Ropp_R0 : Req (Ropp R0) R0.
  Proof.
    
  Qed.

  Program Definition Rinv (x : R) (Hx : Rdiscr x R0) :=
    Rdef (fun n => / approx x n) _.
  Next Obligation.
    unfold Rdiscr in *.
    unfold Rlt in *.
    
    destruct x as (u, Cu). simpl approx.
    intros ε Hε.
    destruct Hx as [ Hx | Hx ].
    - admit.
    - destruct Hx as (δ & Hδ & N & Hx).
      
      (* Cas : x > 0 *)
      destruct xpos as (en, (Nen, Hen)).
      simpl Rseq in Hen.
      simpl.
      intros neps.
      
      Open Scope Z_scope.
      (* |up - uq| < ε |up uq| pour p, q assez grands. *)
      (* |up - uq| < ε * δ²/2   donc δ = 2^-(2*en+2) *)
      (* aussi, trouver n pour δ/2 < up, uq *)
      assert (epscut : { N | (forall p q, le N p -> le N q ->
          ((u q * P2 p - u p * P2 q) * P2 neps
          <= u p * P2 p * u q * P2 q
          <= (u q * P2 p - u p * P2 q) * P2 neps)) /\
          forall n, le N n -> 0 < u n}).
        admit.
      (* Check epscut.*) (* endassert →→ tactique "now" ? *)
      
      destruct epscut as (N, (HN, upos)).
      exists N.
      intros p q Pp Pq.
      specialize (HN p q Pp Pq); destruct HN as (HNl, HNu).
      apply (Z_div_le _ _ (u p)) in HNl.
      (* SUPER RELOU, il faut gérer la division dans Z avec les ≤ dans tous les sens. *)
      split.
        (* - 2p2q <= _ *)
        admit.
        
        (* _ <= + 2p2q *)
        unfold Z.div.
        
  Admitted.
  
  Definition Rdiv x y (p : Rdiscr y R0) := Rmul x (Rinv y p).
  
  Lemma Rlt_trans : forall x y z, Rlt x y -> Rlt y z -> Rlt x z.
  Proof.
   intros (x, Cx) (y, Cy) (z, Cz) (nxy, (Nxy, Hxy)) (nyz, (Nyz, Hyz)).
   exists nxy; exists (max Nxy Nyz).
   intros n Hn.
   eapply Z.le_trans.
    apply Hxy; eapply max_lub_l; eauto.
    cut (y n <= z n)%Z.
     intros H.
     apply Zmult_le_compat_r; auto.
     apply Zlt_le_weak; reflexivity.
     
     apply (Zmult_lt_0_le_reg_r _ _ (Zpos (pow2 nyz))).
      reflexivity.
      refine (Z.le_trans _ _ _ _ (Hyz n (max_lub_r _ _ _ Hn))).
      rewrite <- Zplus_0_r at 1.
      apply Zplus_le_compat_l; apply Zlt_le_weak; reflexivity.
  Qed.
  
  Lemma Rlt_asym : forall x y : R, Rlt x y -> Rlt y x -> False.
   intros (x, Cx) (y, Cy) (nxy, (Nxy, Hxy)) (nyx, (Nyx, Hyx)).
   simpl Rseq in *.
   pose (N := max Nxy Nyx).
   assert (Zpospos : forall p, (0 < Zpos p)%Z) by reflexivity.
   remember (Zpos (pow2 nxy)) as n1.
   remember (Zpos (pow2 nyx)) as n2.
   assert (Pn1 : (0 < n1)%Z) by (subst; reflexivity).
   assert (Pn2 : (0 < n2)%Z) by (subst; reflexivity).
   assert (XY := Hxy N (le_max_l _ _)).
   assert (YX := Hyx N (le_max_r _ _)).
   assert (XY2 := Zmult_le_compat_r _ _ n2 XY (Zlt_le_weak _ _ Pn2)).
   assert (YX2 := Zmult_le_compat_r _ _ n1 YX (Zlt_le_weak _ _ Pn1)).
   rewrite Zmult_plus_distr_l in *.
   repeat rewrite <- Zmult_assoc in *.
   rewrite <- (Zmult_comm n1) in *.
   repeat rewrite Zmult_assoc in *.
   cut (forall a b p, (0 < p -> a + p * n1 <= b -> b + p * n2 <= a -> False)%Z).
    intros HF; eapply (HF _ _ (Zpos (pow2 N)) (eq_refl _)); eauto.
    clear -Pn1 Pn2.
    intros.
    assert (0 < p * n1)%Z by (apply Zmult_lt_0_compat; auto).
    assert (0 < p * n2)%Z by (apply Zmult_lt_0_compat; auto).
    set (p * n1)%Z in *.
    set (p * n2)%Z in *.
    omega.
  Qed.
  
  Lemma JOKER {P} : P.
  Admitted.
  
  Lemma Zneg_Zpos : forall p, Zneg p = Z.opp (Zpos p).
  Proof.
   reflexivity.
  Qed.
  
  Lemma Req_lt_compat_l : forall a b c : R, Req a b -> Rlt a c -> Rlt b c.
  Proof.
   intros (a, Ca) (b, Cb) (c, Cc) Heq (nac, (Nac, Hac)).
   assert (Q : forall {a b}, ((a + b) -> False) -> (a -> False))
     by intuition; assert (Nltab := Q _ _ Heq); clear Heq.
   set (neps := S (S nac)).
   destruct (Ca neps) as (Na, HNa).
   destruct (Cb neps) as (Nb, HNb).
   destruct (Cc neps) as (Nc, HNc).
   assert (Easy : sigT (fun N => (le Nac N * le Na N * le Nb N * le Nc N)%type)) by admit.
   destruct Easy as (N, (((NNac, NNa), NNb), NNc)).
   exists neps; exists N.
   intros n Hn.
   simpl Rseq.
   assert (HNa' := HNa N n NNa JOKER).
   assert (HNb' := HNb N n NNb JOKER).
   assert (HNc' := HNc N n NNc JOKER).
   assert (Hac' := Hac n JOKER).
   simpl Rseq in *.
   unfold neps in *; simpl pow2 in *; rewrite Zpos_xO, (Zpos_xO (pow2 nac)) in *.
   rewrite Zneg_Zpos, Zpos_mult_morphism in *.
   set (DN := Zpos (pow2 N)) in *.
   set (Dn := Zpos (pow2 n)) in *.
   set (DE := Zpos (pow2 nac)) in *.
   
   destruct (Z_lt_le_dec (a N * 4 * DE + 2 * DN) (b N * 4 * DE)) as [AB | AB].
    elimtype False.
    (*clear Hn Dn HNc' Hac' n.*)
    apply Nltab.
    exists nac; exists N; intros.
    simpl Rseq.
    fold DE.
    assert (HNa'' := proj1 (HNa N n0 NNa JOKER)).
    assert (HNb'' := HNb N n0 NNb JOKER).
    rewrite Zneg_Zpos, Zpos_mult_morphism in *.
    set (Dn0 := Zpos (pow2 n0)) in *; fold DN in HNa'', HNb''.
    apply Zmult_lt_0_le_reg_r with (4 * DN)%Z; [ reflexivity | ].
    rewrite Zmult_plus_distr_l.
    ring_simplify.
    apply Z.le_trans with (4 * a N * DE * Dn0 + 5 * Dn0 * DN)%Z.
     apply Zplus_le_reg_r with (- 4 * a n0 * DE * DN - 5 * DN * Dn0)%Z.
     ring_simplify.
     assert (AP : forall a a' b b', a = a' -> b = b' -> Z.le a b -> Z.le a' b')
       by (intros; subst; auto).
     refine (AP _ _ _ _ _ _ HNa''); ring.
     
     apply Z.le_trans with (4 * DE * Dn0 * b N - DN * Dn0)%Z.
      replace (5 * Dn0 * DN)%Z with (5 * DN * Dn0)%Z by ring.
      replace (4 * DE * Dn0 * b N)%Z with (4 * DE * b N * Dn0)%Z by ring.
      rewrite <- Zmult_plus_distr_l.
      rewrite <- Zmult_minus_distr_r.
      apply Zmult_gt_0_le_compat_r; [ reflexivity | ].
      
      
    clear HNa HNb HNc Hac.
    ring_simplify.
    replace (2 * (2 * DE))%Z with (4 * DE)%Z in * by ring.
    remember (4 * DE)%Z as DE4.
    rewrite Zmult_comm, Zmult_assoc, (Zmult_comm DE), <- HeqDE4.
    rewrite <- Zmult_assoc, <- HeqDE4 in AB.

    assert (I1 : (b n * DN * DE4 + Dn * DN <= b N * Dn * DE4)%Z).
      admit.
    assert (I2 : (b N * Dn * DE4 <= a N * Dn * DE4 + 2 * Dn * DN)%Z).
      replace (b N * Dn * DE4)%Z with (Dn * (b N * DE4))%Z by ring.
      replace (a N * Dn * DE4 + 2 * Dn * DN)%Z with (Dn * (a N * DE4 + 2 * DN))%Z by ring.
(*      replace (a N * DE4)%Z with (a N * 4 * DE)%Z by (subst; ring).
      refine (Zmult_le_compat_l _ _ Dn AB JOKER).
    assert (I3 : (a N * Dn * DE4 + 2 * Dn * DN <= c N * Dn * DE4)%Z).
      admit.
    assert (I4 : (c N * Dn * DE4 <= c n * DN * DE4 - Dn * DN)%Z).
      admit.
    assert (I5 := Z.le_trans _ _ _ I1 (Z.le_trans _ _ _ I2 (Z.le_trans _ _ _ I3 I4))).
    repeat rewrite <- Zmult_assoc in I5.
    repeat rewrite (Zmult_comm DN) in I5.
    repeat rewrite Zmult_assoc in I5.
    rewrite <- Zmult_plus_distr_l, <- Zmult_minus_distr_r in I5.
    assert (I6 := Zmult_lt_0_le_reg_r _ _ _ JOKER I5).
    assert (0 < Dn)%Z by reflexivity.
    repeat rewrite <- (Zmult_comm DE4) in *.
    set (DE4 * c n)%Z in *.
    set (DE4 * b n)%Z in *.
    omega.*)
    admit.
    admit.
    admit.
    admit.
  Admitted.
  
  Lemma Req_lt_compat_r : forall x1 x2 y : R, Req x1 x2 -> Rlt y x1 -> Rlt y x2.
  Admitted. (* TODO *)
  
  Lemma Radd_lt_compat_l : forall x y1 y2 : R, Rlt y1 y2 -> Rlt (Radd x y1) (Radd x y2).
  Admitted. (* TODO *)
  
  Lemma Radd_eq_compat_l : forall x y1 y2, Req y1 y2 -> Req (Radd x y1) (Radd x y2).
  Admitted. (* TODO *)
  
  Lemma Rmul_lt_compat_l : forall x y1 y2 : R, Rlt R0 x -> Rlt y1 y2 -> Rlt (Rmul x y1) (Rmul x y2).
  Admitted. (* TODO *)
  
  Lemma Rmul_eq_compat_l : forall x y1 y2, Req y1 y2 -> Req (Rmul x y1) (Rmul x y2).
  Admitted. (* TODO *)
  
  Lemma Rinv_0_lt_compat : forall (x : R) (pr : Rlt R0 x) (pr' : Rdiscr x R0), Rlt R0 (Rinv x pr').
  Admitted. (* TODO *)
  
  Lemma Radd_comm : forall a b, Req (Radd a b) (Radd b a).
  Admitted. (* TODO *)
  
  Lemma Radd_assoc : forall x y z, Req (Radd (Radd x y) z) (Radd x (Radd y z)).
  Admitted. (* TODO *)
  
  Lemma Radd_opp_r : forall x, Req (Radd x (Ropp x)) R0.
  Admitted. (* TODO *)
  
  Lemma Radd_0_l : forall x, Req (Radd R0 x) x.
  Proof.
    intros x [Lt | Lt]; destruct Lt as (NE, (N, HN));
      assert (HNN := HN N (le_refl _));
      simpl in HNN;
      set (Rseq x N * Zpos (pow2 NE))%Z in *;
      assert (0 < Zpos (pow2 N))%Z by reflexivity;
      omega.
  Qed.
  
  Lemma Rmul_add_distr_l a b c : Req (Rmul a (Radd b c)) (Radd (Rmul a b) (Rmul a c)).
  Admitted. (* TODO *)
  
  Lemma Rmul_comm : forall a b, Req (Rmul a b) (Rmul b a).
  Proof.
    intros a b [Lt | Lt]; destruct Lt as (NE, (N, HN));
      assert (HNN := HN N (le_refl _));
      simpl in HNN;
      rewrite (Zmult_comm (Rseq b N)) in HNN;
      set (Rseq a N * Rseq b N * Zpos (pow2 N) * Zpos (pow2 NE))%Z in *;
      assert (0 < Zpos (pow2 N))%Z by reflexivity;
      omega.
  Qed.
  
  Lemma Rmul_assoc : forall x y z, Req (Rmul (Rmul x y) z) (Rmul x (Rmul y z)).
  Proof.
    assert (BAH : forall a a' c, (a = a' -> 0 < c -> a + c <= a' -> False)%Z) by (intros; omega).
    intros a b c [Lt | Lt]; destruct Lt as (NE, (N, HN));
      assert (HNN := HN N (le_refl _));
      simpl in HNN;
      (refine (BAH _ _ _ _ _ HNN); [ ring | reflexivity ]).
  Qed.
  
  Lemma Rmul_1_l : forall x, Req (Rmul R1 x) x.
  Admitted. (* TODO *)
  
  Lemma Rinv_l : forall (x : R) (pr : Rdiscr x R0), Req (Rmul (Rinv x pr) x) R1.
  Admitted. (* TODO *)
  
  Lemma Rlt_0_1 : Rlt R0 R1.
  Proof.
    exists O; exists O; intros n Hn.
    simpl; rewrite Zpos_mult_morphism; omega.
  Qed.
  
  Fixpoint IPR (p : positive) : R :=
    match p with
      | xI p => Radd (Rmul (Radd R1 R1) (IPR p)) R1
      | xO p => Rmul (Radd R1 R1) (IPR p)
      | xH => R1
    end.
  
  Definition IZR (z : BinInt.Z) : R :=
    match z with
      | Z0 => R0
      | Zpos p => IPR p
      | Zneg p => Ropp (IPR p)
    end.
  
  Definition Rdist x y d : Type := prod (Rlt (Rsub x y) d) (Rlt (Ropp d) (Rsub x y)).
  
  Definition Rup (x : R) : Z := let (N, _) := Rcauchy x 1%nat in (Z.div (Rseq x N) (Zpos (pow2 N))).
  
  Lemma Rup_spec : forall r : R, Rdist r (IZR (Rup r)) R1.
  Proof.
    intros (u, Hu).
    unfold Rup; simpl.
    destruct (Hu 1%nat) as (N, HN).
    split; exists O; exists N; intros n Hn.
    destruct (HN N n (le_refl _) Hn) as (NS, NI).
    (* simpl Hu. *)
    (* assert (HNN := Hu 1%nat). *)
    (* simpl Rup. *)
  Admitted.
  
  Definition Rseq_Cauchy (Un : nat -> R) : Type := forall eps, Rlt R0 eps ->
    {N : nat & forall p q, (N <= p)%nat -> (N <= q)%nat -> Rdist (Un p) (Un q) eps}.
  
  Definition Rseq_cv (Un : nat -> R) (l : R) : Type := forall eps, Rlt R0 eps ->
    {N : nat & forall n, (N <= n)%nat -> Rdist (Un n) l eps}.
  
  Lemma Rcomplete : forall Un, Rseq_Cauchy Un -> {l : R & Rseq_cv Un l}.
  Admitted. (* TODO *)
  
End Rrealize.
