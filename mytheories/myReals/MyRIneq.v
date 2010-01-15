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

Require Export Raxioms.
Require Import RIneq.

Open Scope R_scope.

Implicit Type r : R.

Lemma Req_dec : forall r1 r2, {r1 = r2} + {r1 <> r2}.
Proof.
intros r1 r2.
destruct (total_order_T r1 r2) as [[Hlt|Heq]|Hgt].
right; intro Hn; apply (Rlt_irrefl r2);
  rewrite Hn in Hlt; assumption.
left; assumption.
right; intros Hn; apply (Rlt_irrefl r2);
  rewrite Hn in Hgt; assumption.
Qed.

Lemma Req_or_neq : forall r, {r = 0} + {r <> 0}.
Proof.
intros r; exact (Req_dec r 0).
Qed.

Lemma Rplus_eq_compat_r : forall r r1 r2, r1 = r2 -> r1 + r = r2 + r.
Proof.
intros r r1 r2 H; rewrite H; reflexivity.
Qed.

Lemma Rmult_eq_compat_r : forall r1 r2 r, r1 = r2 -> r1 * r = r2 * r.
Proof.
intros r1 r2 r r_neq.
 rewrite Rmult_comm.
 replace (r2 * r) with (r * r2) by field.
 apply Rmult_eq_compat_l ; assumption.
Qed.
