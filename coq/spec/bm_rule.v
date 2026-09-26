(* SPDX-License-Identifier: Apache-2.0
   SPDX-FileCopyrightText: 2026 Next Ridge Solutions Ltd

   The rule for BigMult at four limbs of 64 bits: the input assumption PRE_bm (a and b each have exactly
   4 limbs, each in [0, 2^64)), the relation REL_bm (out has exactly 8 limbs, each in [0, 2^64), and the
   value of out is the value of a times the value of b), and `adequate`: under the input assumption, a
   circuit accepts exactly the triples the relation accepts. Checked examples follow: triples the relation
   accepts, triples it rejects (a wrong product, an output limb out of range), and an input the assumption
   rejects (a 65-bit limb).

   Scope: these results bind the formal (Coq) layer only; the generated constraint model's fidelity to the circuit implementation, and the implementation itself, are outside them. *)

From Coq Require Import ZArith List.
Import ListNotations.
Open Scope Z_scope.

Definition N_BITS : Z := 64.
Definition K : nat := 4.
Definition B : Z := 2 ^ N_BITS.

Definition VAL (v : list Z) : Z := fold_right (fun x acc => x + B * acc) 0 v.

Definition limb_ok (x : Z) : Prop := 0 <= x < B.

(* The input assumption: a and b have exactly 4 limbs, each in [0, 2^64). A hypothesis of the
   theorems; the circuit does not check it. *)
Definition PRE_bm (a b : list Z) : Prop :=
  length a = K /\ length b = K /\ Forall limb_ok a /\ Forall limb_ok b.

(* The relation: out has exactly 8 limbs, each in [0, 2^64), and its value is the product of the
   input values, as an equality of integers (not modulo anything). *)
Definition REL_bm (a b out : list Z) : Prop :=
  length out = (2 * K)%nat /\ Forall limb_ok out /\ VAL out = VAL a * VAL b.

(* Adequacy: for inputs satisfying the input assumption, acceptance and the relation coincide. *)
Definition adequate (accepts : list Z -> list Z -> list Z -> Prop) : Prop :=
  forall a b out, PRE_bm a b -> (accepts a b out <-> REL_bm a b out).

From Coq Require Import Lia.

Lemma N_BITS_val : N_BITS = 64. Proof. reflexivity. Qed.
Lemma K_val : K = 4%nat. Proof. reflexivity. Qed.

Lemma B_value : B = 18446744073709551616.
Proof. unfold B, N_BITS. vm_compute. reflexivity. Qed.

Lemma B_pos : 0 < B.
Proof. rewrite B_value. lia. Qed.

Lemma VAL_nil : VAL [] = 0. Proof. reflexivity. Qed.
Lemma VAL_cons : forall x t, VAL (x :: t) = x + B * VAL t. Proof. reflexivity. Qed.

Lemma VAL_firstn_skipn : forall n v,
  VAL v = VAL (firstn n v) + B ^ Z.of_nat n * VAL (skipn n v).
Proof.
  induction n as [|n IH]; intro v.
  - cbn [firstn skipn Z.of_nat]. rewrite Z.pow_0_r, VAL_nil. ring.
  - destruct v as [|x t].
    + cbn [firstn skipn]. rewrite VAL_nil. ring.
    + cbn [firstn skipn]. rewrite !VAL_cons, (IH t).
      rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. ring.
Qed.

Lemma B_pow_nonzero : forall n, B ^ Z.of_nat n <> 0.
Proof. intro n. apply Z.pow_nonzero; [ rewrite B_value; lia | lia ]. Qed.

Theorem VAL_product_is_the_convolution : forall a0 a1 a2 a3 b0 b1 b2 b3,
  VAL [a0; a1; a2; a3] * VAL [b0; b1; b2; b3]
  = VAL [a0 * b0; a0 * b1 + a1 * b0; a0 * b2 + a1 * b1 + a2 * b0;
         a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0; a1 * b3 + a2 * b2 + a3 * b1;
         a2 * b3 + a3 * b2; a3 * b3].
Proof. intros. unfold VAL. cbn [fold_right]. ring. Qed.

Lemma VAL_bound : forall v, Forall limb_ok v ->
  0 <= VAL v < B ^ Z.of_nat (length v).
Proof.
  induction v as [|x t IH]; intro Hf.
  - cbn. lia.
  - inversion Hf as [|? ? Hx Ht]; subst. unfold limb_ok in Hx.
    specialize (IH Ht). rewrite VAL_cons. cbn [length].
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    pose proof B_pos. nia.
Qed.

Theorem PRE_product_fits_2K_limbs : forall a b,
  PRE_bm a b -> 0 <= VAL a * VAL b < B ^ 8.
Proof.
  intros a b [Hla [Hlb [Ha Hb]]].
  pose proof (VAL_bound a Ha) as HA. pose proof (VAL_bound b Hb) as HB.
  rewrite Hla in HA. rewrite Hlb in HB. unfold K in *.

  change (Z.of_nat 4) with 4 in HA, HB.
  change (B ^ 8) with (B ^ 4 * B ^ 4).
  split; [ nia | ].
  apply Z.mul_lt_mono_nonneg; lia.
Qed.

Example rel_anchor : REL_bm [2^64-1;0;0;0] [2^64-1;0;0;0] [1;2^64-2;0;0;0;0;0;0].
Proof. unfold REL_bm, limb_ok, B, N_BITS, K. split; [reflexivity|split].
 - repeat constructor; vm_compute; congruence.
 - vm_compute. reflexivity. Qed.
Example rel_fraud : ~ REL_bm [2^64-1;0;0;0] [2^64-1;0;0;0] [1;2^64-1;0;0;0;0;0;0].
Proof. unfold REL_bm. intros [_ [_ H]]. vm_compute in H. discriminate. Qed.

Example top : VAL [2^64-1;2^64-1;2^64-1;2^64-1] * VAL [2^64-1;2^64-1;2^64-1;2^64-1] < B ^ 8.
Proof. apply Z.ltb_lt. vm_compute. reflexivity. Qed.

Lemma carry_step_bound : forall c r,
  0 <= c <= 4 * (B - 1) ^ 2 -> 0 <= r <= 4 * (B - 1) -> 0 <= (c + r) / B <= 4 * (B - 1).
Proof.
  intros c r Hc Hr. assert (HB : 0 < B) by (unfold B, N_BITS; lia).
  split. - apply Z.div_pos; lia.
  - apply Z.div_le_upper_bound; [lia|]. nia.
Qed.
Example carry_fits_67 : 4 * (B - 1) < 2 ^ 66 /\ 2 ^ 66 < 2 ^ 67.
Proof. unfold B, N_BITS. split; apply Z.ltb_lt; vm_compute; reflexivity. Qed.
Example coef_bound : 4 * (B - 1) ^ 2 < 2 ^ 130.
Proof. unfold B, N_BITS. apply Z.ltb_lt; vm_compute; reflexivity. Qed.

Ltac limbs := repeat (apply Forall_cons; [ unfold limb_ok; rewrite B_value; lia | ]); apply Forall_nil.
Ltac pre_row := split; [reflexivity|]; split; [reflexivity|]; split; limbs.
Ltac rel_row := split; [reflexivity|]; split; [limbs|]; vm_compute; reflexivity.

Definition DIAG_A : list Z := [2^64-1; 0; 0; 0].
Definition DIAG_OUT : list Z := [1; 2^64-2; 0; 0; 0; 0; 0; 0].
Example diag_row_pre : PRE_bm DIAG_A DIAG_A. Proof. unfold DIAG_A. pre_row. Qed.
Example diag_row_rel : REL_bm DIAG_A DIAG_A DIAG_OUT.
Proof. unfold DIAG_A, DIAG_OUT. rel_row. Qed.

Definition CORNER : list Z := [2^64-1; 2^64-1; 2^64-1; 2^64-1].
Definition CORNER_OUT : list Z := [1; 0; 0; 0; 2^64-2; 2^64-1; 2^64-1; 2^64-1].
Example corner_pre : PRE_bm CORNER CORNER. Proof. unfold CORNER. pre_row. Qed.
Example corner_rel : REL_bm CORNER CORNER CORNER_OUT.
Proof. unfold CORNER, CORNER_OUT. rel_row. Qed.

Definition CORNER_FRAUD : list Z := [1; 0; 0; 0; 2^64-2; 2^64-1; 2^64-2; 2^64-1].
Example corner_fraud_refused : ~ REL_bm CORNER CORNER CORNER_FRAUD.
Proof. intros [_ [_ H]]. vm_compute in H. discriminate. Qed.
Example wrong_product_refused : ~ REL_bm DIAG_A DIAG_A CORNER_OUT.
Proof. intros [_ [_ H]]. vm_compute in H. discriminate. Qed.

Definition DIAG_OUT_WIDE : list Z := [2^64+1; 2^64-3; 0; 0; 0; 0; 0; 0].
Example wide_out_val_equal : VAL DIAG_OUT_WIDE = VAL DIAG_A * VAL DIAG_A.
Proof. vm_compute. reflexivity. Qed.
Example wide_out_refused : ~ REL_bm DIAG_A DIAG_A DIAG_OUT_WIDE.
Proof.
  intros [_ [H _]]. inversion H as [|? ? Hx _]; subst. unfold limb_ok in Hx.
  rewrite B_value in Hx. lia.
Qed.

Example pre_refuses_a_65_bit_limb : ~ PRE_bm [2^64; 0; 0; 0] [1; 0; 0; 0].
Proof.
  intros [_ [_ [Ha _]]]. inversion Ha as [|? ? Hx _]; subst. unfold limb_ok in Hx.
  rewrite B_value in Hx. lia.
Qed.

Print Assumptions N_BITS_val.
Print Assumptions K_val.
Print Assumptions B_value.
Print Assumptions B_pos.
Print Assumptions VAL_nil.
Print Assumptions VAL_cons.
Print Assumptions VAL_firstn_skipn.
Print Assumptions B_pow_nonzero.
Print Assumptions VAL_product_is_the_convolution.
Print Assumptions VAL_bound.
Print Assumptions PRE_product_fits_2K_limbs.
Print Assumptions rel_anchor.
Print Assumptions rel_fraud.
Print Assumptions top.
Print Assumptions carry_step_bound.
Print Assumptions carry_fits_67.
Print Assumptions coef_bound.
Print Assumptions diag_row_pre.
Print Assumptions diag_row_rel.
Print Assumptions corner_pre.
Print Assumptions corner_rel.
Print Assumptions corner_fraud_refused.
Print Assumptions wrong_product_refused.
Print Assumptions wide_out_val_equal.
Print Assumptions wide_out_refused.
Print Assumptions pre_refuses_a_65_bit_limb.
