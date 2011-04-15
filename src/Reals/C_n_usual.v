Require Import Reals.
Require Import Rfunction_facts.
Require Import C_n_def C_n_facts.
Require Import Rextensionality.

Require Import Rpser_def.
Require Import Rpser_def Rpser_cv_facts Rpser_sums Rpser_sums_facts Rpser_derivative.

Open Local Scope R_scope.

(** * Classification of common functions *)

(** Polynoms *)

Lemma C_infty_zero : C_infty (fct_cte 0).
Proof.
 intro n ; induction n.
  constructor; reg.
  apply C_Sn with (derivable_const 0) ;
  apply C_ext with (fct_cte 0) ; [| assumption].
  intro x ; unfold derive , fct_cte ; symmetry ;
  rewrite derive_pt_eq ; apply derivable_pt_lim_const.
Qed.

Lemma C_infty_const : forall (c : R), C_infty (fct_cte c).
Proof.
 intros c n ; destruct n.
  constructor ; reg. 
  apply C_Sn with (derivable_const c) ;
  apply C_ext with (fct_cte 0).
  intro x ; unfold derive ; symmetry ;
  rewrite derive_pt_eq ; apply derivable_pt_lim_const.
  apply C_infty_zero.
Qed.

Lemma C_infty_id : C_infty id.
Proof.
 intros n ; destruct n.
  constructor ; reg.
 apply C_Sn with derivable_id ;
 apply C_ext with (fct_cte 1).
 intro x ; unfold derive ; symmetry ;
 rewrite derive_pt_eq ; apply derivable_pt_lim_id.
 eapply C_infty_const.
Qed.

Lemma C_infty_monomial : forall d a,  C_infty (fun x => Rmult a (pow x d)).
Proof.
intro d ; induction d ; intros a n.
 apply C_ext with (fct_cte a).
  intro ; ring_simplify ; reflexivity.
  eapply C_infty_const.
 destruct n.
  constructor; intro; reg.
  assert (pr : derivable (fun x : R => (a * x ^ S d)%R)) by reg ;
  apply C_Sn with pr ; apply C_ext with (fun x => (a * INR (S d) * pow x d)%R).
  intro x ; symmetry ; pose (fmod := mult_real_fct a (fun x0 : R => (x0 ^ S d)%R)) ;
  transitivity (derive_pt _ x (derivable_pt_scal _ a x (derivable_pt_pow (S d) _))).
   apply pr_nu.
   rewrite derive_pt_scal, Rmult_assoc ; apply Rmult_eq_compat_l ;
   apply derive_pt_pow.
   eapply IHd.
Qed.

(** Stdlib's trigonometric functions *)

Lemma C_cos_sin : forall n, C n sin * C n cos * C n (-sin)%F * C n (-cos)%F.
intro n ; induction n.
  repeat split; constructor; reg.

  destruct IHn as [[[IHs IHc] IHns] IHnc].
  repeat split.

   apply C_Sn with derivable_sin.
   apply C_ext with cos.
   intro x ; symmetry ; unfold derive ; reg.
   assumption.

   apply C_Sn with derivable_cos.
   apply C_ext with (-sin)%F.
   intro x ; symmetry ; unfold derive ; reg.
   assumption.

   assert (dns : derivable (-sin)) by reg.
   apply C_Sn with dns.
   apply C_ext with (-cos)%F.
   intro x ; symmetry ; unfold derive ; reg.
   assumption.

   assert (dnc : derivable (-cos)) by reg.
   apply C_Sn with dnc.
   apply C_ext with sin.
   intro x ; symmetry ; unfold derive ; reg.
   assumption.
Qed.

Lemma C_infty_sin : C_infty sin.
Proof.
 intro ; eapply C_cos_sin.
Qed.

Lemma C_infty_cos : C_infty cos.
Proof.
 intro ; eapply C_cos_sin.
Qed.


(** Stdlib's exponential *)

Lemma C_infty_exp : C_infty exp.
Proof.
 intro n ; induction n.
  constructor ; apply derivable_continuous ; apply derivable_exp.

  apply C_Sn with (derivable_exp) ; apply C_ext with exp.
   intro x ; rewrite <- (derive_pt_exp x) ; apply pr_nu_var ; reflexivity.

   apply IHn.
Qed.

(** Power series *)

Lemma C_infty_Rpser : forall (An  : nat -> R) (Rho : infinite_cv_radius An),
 C_infty (sum An Rho).
Proof.
intros An Rho n ; generalize Rho ; generalize An.
 clear An Rho ; induction n.
  intros An Rho ; constructor.
  intro x ; apply continuity_pt_sum.
  intros An Rho.
  apply C_Sn with (derivable_sum An Rho).
  apply C_ext with (sum_derive An Rho).
  intro x ; symmetry ; apply derive_pt_eq_0 ; apply derivable_pt_lim_sum.
  apply IHn.
Qed.

(** Handy abstractions: a function together with the proof
that it is C_infty *)

Lemma Cinfty_zero : Cinfty.
Proof.
exists (fct_cte 0) ; apply C_infty_zero.
Defined.

Hint Resolve C_infty_const : C_hint.
Hint Resolve C_infty_id : C_hint.
Hint Resolve C_infty_monomial : C_hint.
Hint Resolve C_infty_sin : C_hint.
Hint Resolve C_infty_cos : C_hint.
Hint Resolve C_infty_exp : C_hint.
Hint Resolve C_infty_Rpser : C_hint.
