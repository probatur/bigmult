(* SPDX-License-Identifier: Apache-2.0
   SPDX-FileCopyrightText: 2026 Next Ridge Solutions Ltd

   Facts about the model used by the proofs. In every accepted filling the output limbs lie in [0, 2^64)
   (out_limbs_in_range) and the first six carry cells in [0, 2^66) (carry_cells_in_range); the
   output limbs agree with the public cells. Also: the decoded values are canonical, a 64-bit limb is at
   most half the field prime, each input cell is read only by the constraints that compute the product, and the
   relation is an equality of integers, not a congruence modulo p (REL_is_a_value_equality_not_mod_q).

   Scope: these results bind the formal (Coq) layer only; the generated constraint model's fidelity to the circuit implementation, and the implementation itself, are outside them. *)

From Coq Require Import ZArith Lia List Znumtheory. Import ListNotations.
Open Scope Z_scope.

Require Import Generated.bm_model_gen.
Require Import Generated.bm_scaffold_gen.
Require Import Constraints.bm_semantic.
Require bm_rule.

Theorem one_member : bm_rule.N_BITS = 64 /\ bm_rule.K = 4%nat.
Proof. split; reflexivity. Qed.

Theorem the_decode_is_canonical : forall a c,
  dc a c = (a (c, 0%nat)) mod p /\ 0 <= dc a c < p.
Proof. intros a c. split; [ reflexivity | apply dc_range ]. Qed.

Theorem n_bit_limb_is_at_most_half_field : forall P x,
  2 ^ 65 <= P -> 0 <= x < 2 ^ 64 -> x <= (P - 1) / 2.
Proof.
  intros P x HP Hx. apply Z.div_le_lower_bound; [ lia | ].
  assert (H : 2 ^ 65 = 2 * 2 ^ 64) by reflexivity. lia.
Qed.

Theorem on_pasta_every_limb_is_below_half : 2 ^ 64 - 1 <= HALF.
Proof. pose proof HALF_big. assert (2 ^ 64 <= 2 ^ 140) by (apply Z.pow_le_mono_r; lia). lia. Qed.

Theorem each_input_cell_is_read_only_by_chain_gates :
  map (fun c => length (filter (reads_b (c, 0%nat)) deployed_gates)) (seq 0 8)
  = [4; 4; 4; 4; 4; 4; 4; 4]%nat
  /\ map (fun c => length (filter (reads_b (c, 0%nat)) tg_chain)) (seq 0 8)
  = [4; 4; 4; 4; 4; 4; 4; 4]%nat.
Proof. split; vm_compute; reflexivity. Qed.

Theorem ab_cell_indices_lie_below_OUTBIT_BASE :
  OUTBIT_BASE = 23%nat /\ (forall c, (c < 8)%nat -> (c < OUTBIT_BASE)%nat).
Proof. split; [ reflexivity | intros c Hc; unfold OUTBIT_BASE; lia ]. Qed.

Theorem out_limbs_in_range : forall a,
  sat deployed_model a -> Forall bm_rule.limb_ok (out_l a).
Proof.
  intros a Hs. unfold out_l.
  pose proof (rng_out a Hs) as H. unfold bm_rule.limb_ok. rewrite bm_rule.B_value.

  apply Forall_cons; [ exact (H 0%nat ltac:(lia)) | ].
  apply Forall_cons; [ exact (H 1%nat ltac:(lia)) | ].
  apply Forall_cons; [ exact (H 2%nat ltac:(lia)) | ].
  apply Forall_cons; [ exact (H 3%nat ltac:(lia)) | ].
  apply Forall_cons; [ exact (H 4%nat ltac:(lia)) | ].
  apply Forall_cons; [ exact (H 5%nat ltac:(lia)) | ].
  apply Forall_cons; [ exact (H 6%nat ltac:(lia)) | ].
  apply Forall_cons; [ exact (H 7%nat ltac:(lia)) | ].
  apply Forall_nil.
Qed.

Theorem carry_cells_in_range : forall a,
  sat deployed_model a ->
  forall i, (i < 6)%nat -> 0 <= cc a i < 2 ^ 66.
Proof.
  intros a Hs i Hi. change (2 ^ 66) with 73786976294838206464. exact (rng_c a Hs i Hi).
Qed.

Definition CORNER_ALIAS : list Z := [11037532056220336130; 2469829653914515739; 0; 4611686018427387904; 18446744073709551614; 18446744073709551615; 18446744073709551615; 18446744073709551615].

Theorem REL_is_a_value_equality_not_mod_q :
  bm_rule.REL_bm bm_rule.CORNER bm_rule.CORNER bm_rule.CORNER_OUT
  /\ bm_rule.VAL CORNER_ALIAS = bm_rule.VAL bm_rule.CORNER_OUT + p
  /\ (bm_rule.VAL CORNER_ALIAS) mod p = (bm_rule.VAL bm_rule.CORNER_OUT) mod p
  /\ length CORNER_ALIAS = 8%nat /\ Forall bm_rule.limb_ok CORNER_ALIAS
  /\ ~ bm_rule.REL_bm bm_rule.CORNER bm_rule.CORNER CORNER_ALIAS.
Proof.
  split; [ exact bm_rule.corner_rel | ].
  split; [ vm_compute; reflexivity | ].
  split; [ vm_compute; reflexivity | ].
  split; [ reflexivity | ].
  split.
  - unfold CORNER_ALIAS, bm_rule.limb_ok. rewrite bm_rule.B_value.
    repeat (apply Forall_cons; [ lia | ]). apply Forall_nil.
  - intros [_ [_ H]]. vm_compute in H. discriminate.
Qed.

Theorem the_product_fits_2K_limbs : forall a b out,
  bm_rule.REL_bm a b out -> 0 <= bm_rule.VAL out < bm_rule.B ^ 8.
Proof.
  intros a b out [Hl [Hf _]]. pose proof (bm_rule.VAL_bound out Hf) as H.
  rewrite Hl in H. exact H.
Qed.

Theorem out_limbs_are_pinned_to_public_cells : forall a,
  sat deployed_model a -> PINS_bm a.
Proof. exact answer_pins_are_DERIVED. Qed.

Theorem X2_margin_on_pasta : 2 ^ 131 < HALF.
Proof. pose proof HALF_big. assert (2 ^ 131 < 2 ^ 140) by (apply Z.pow_lt_mono_r; lia). lia. Qed.

Print Assumptions one_member.
Print Assumptions the_decode_is_canonical.
Print Assumptions n_bit_limb_is_at_most_half_field.
Print Assumptions on_pasta_every_limb_is_below_half.
Print Assumptions each_input_cell_is_read_only_by_chain_gates.
Print Assumptions ab_cell_indices_lie_below_OUTBIT_BASE.
Print Assumptions out_limbs_in_range.
Print Assumptions carry_cells_in_range.
Print Assumptions REL_is_a_value_equality_not_mod_q.
Print Assumptions the_product_fits_2K_limbs.
Print Assumptions out_limbs_are_pinned_to_public_cells.
Print Assumptions X2_margin_on_pasta.
