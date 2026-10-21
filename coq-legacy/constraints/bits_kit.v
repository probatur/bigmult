(* SPDX-License-Identifier: Apache-2.0
   SPDX-FileCopyrightText: 2026 Next Ridge Solutions Ltd

   Bit decompositions (bits_of) and their weighted sums, facts about small residues modulo a positive
   number, a computed modular inverse (finv), and small list utilities.

   Scope: these results bind the formal (Coq) layer only; the generated constraint model's fidelity to the circuit implementation, and the implementation itself, are outside them. *)

From Coq Require Import ZArith Lia List Znumtheory Zpow_facts.
Import ListNotations. Open Scope Z_scope.
Require Import Constraints.field_order_lift.

Definition bits_of (d:Z) (j:nat) : Z := Z.b2z (Z.testbit d (Z.of_nat j)).

Lemma bits_of_bool : forall d i, bits_of d i = 0 \/ bits_of d i = 1.
Proof. intros d i. unfold bits_of, Z.b2z. destruct (Z.testbit d (Z.of_nat i)); auto. Qed.

Lemma wpow_pow2 : forall n, wpow n = 2 ^ (Z.of_nat n).
Proof.
  induction n as [|n IH].
  - reflexivity.
  - cbn [wpow]. rewrite IH. rewrite Nat2Z.inj_succ.
    rewrite Z.pow_succ_r by apply Nat2Z.is_nonneg.
    reflexivity.
Qed.

Lemma bitsum_bits_of : forall n d, 0 <= d -> bitsum (bits_of d) n = d mod (wpow n).
Proof.
  induction n as [|n IH]; intros d Hd.
  - cbn [bitsum wpow]. rewrite Z.mod_1_r. reflexivity.
  - pose proof (wpow_pos n) as Hw.
    cbn [bitsum]. rewrite (IH d Hd).
    replace (wpow (S n)) with (wpow n * 2) by (cbn [wpow]; ring).
    rewrite (Z.rem_mul_r d (wpow n) 2) by lia.
    unfold bits_of.
    rewrite (Z.testbit_spec' d (Z.of_nat n)) by apply Nat2Z.is_nonneg.
    rewrite <- wpow_pow2.
    ring.
Qed.

Lemma bitsum64_bits_of : forall d, 0 <= d < 2^64 -> bitsum (bits_of d) 64 = d.
Proof.
  intros d [Hlo Hhi].
  assert (H64 : wpow 64 = 2 ^ 64) by (rewrite wpow_pow2; reflexivity).
  rewrite (bitsum_bits_of 64 d Hlo), H64.
  apply Z.mod_small. lia.
Qed.

Lemma mul_le_neg : forall P m, 0 < P -> m <= -1 -> m * P <= -P.
Proof.
  intros P m HP Hm.
  replace (-P) with ((-1)*P) by ring. apply Z.mul_le_mono_nonneg_r; lia.
Qed.

Lemma mul_ge_pos : forall P m, 0 < P -> 1 <= m -> P <= m * P.
Proof.
  intros P m HP Hm.
  replace P with (1*P) at 1 by ring. apply Z.mul_le_mono_nonneg_r; lia.
Qed.

Lemma no_wrap_zero : forall P z, 0 < P -> -P < z -> z < P -> z mod P = 0 -> z = 0.
Proof.
  intros P z HP Hlo Hhi Hm.
  destruct (Zmod_divide z P (ltac:(lia)) Hm) as [k Hk].
  destruct (Z.le_gt_cases k (-1)) as [Hk1|Hk1].
  - pose proof (mul_le_neg P k HP Hk1). lia.
  - destruct (Z.eq_dec k 0) as [Hk0|Hk0].
    + subst k. rewrite Z.mul_0_l in Hk. exact Hk.
    + pose proof (mul_ge_pos P k HP (ltac:(lia))). lia.
Qed.

Lemma small_nonzero_residue : forall P z, 0 < P -> -P < z -> z < P -> z <> 0 -> z mod P <> 0.
Proof.
  intros P z HP Hlo Hhi Hnz Hm. apply Hnz. exact (no_wrap_zero P z HP Hlo Hhi Hm).
Qed.

Definition finv (P m : Z) : Z := Zpow_mod (m mod P) (P - 2) P.

Definition drop_nth {A:Type} (n:nat) (l:list A) : list A :=
  firstn n l ++ skipn (S n) l.

Lemma drop_nth_length : forall (A:Type) (n:nat) (l:list A),
  (n < length l)%nat -> length (drop_nth n l) = (length l - 1)%nat.
Proof.
  intros A n l Hn. unfold drop_nth.
  rewrite app_length. rewrite firstn_length_le by lia. rewrite skipn_length. lia.
Qed.

Lemma drop_nth_incl : forall (A:Type) (n:nat) (l:list A) (x:A),
  In x (drop_nth n l) -> In x l.
Proof.
  intros A n l x Hin. unfold drop_nth in Hin.
  apply in_app_or in Hin. destruct Hin as [H|H].
  - rewrite <- (firstn_skipn n l). apply in_or_app. left. exact H.
  - rewrite <- (firstn_skipn (S n) l). apply in_or_app. right. exact H.
Qed.

Print Assumptions bits_of_bool.
Print Assumptions wpow_pow2.
Print Assumptions bitsum_bits_of.
Print Assumptions bitsum64_bits_of.
Print Assumptions no_wrap_zero.
Print Assumptions small_nonzero_residue.
Print Assumptions drop_nth_length.
Print Assumptions drop_nth_incl.
