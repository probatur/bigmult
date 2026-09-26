(* SPDX-License-Identifier: Apache-2.0
   SPDX-FileCopyrightText: 2026 Next Ridge Solutions Ltd

   Lifting from the field to the integers (order_lift): when 2^n is at most p, each bit is 0 or 1 modulo p,
   and the weighted bit sum equals v modulo p, the residue of v modulo p lies in [0, 2^n) and equals the
   weighted sum of the canonical bits.

   Scope: these results bind the formal (Coq) layer only; the generated constraint model's fidelity to the circuit implementation, and the implementation itself, are outside them. *)

From Coq Require Import ZArith Lia. Open Scope Z_scope.
Require Import Constraints.range_field_pasta.

Section OrderLift.
  Context (p : Z) (Hp2 : 2 <= p).

  Fixpoint wpow (k:nat) : Z := match k with O => 1 | S j => 2 * wpow j end.

  Lemma wpow_pos : forall k, 0 < wpow k.
  Proof. induction k as [|k IH]; cbn [wpow]; lia. Qed.

  Fixpoint bitsum (bits:nat->Z) (n:nat) : Z :=
    match n with O => 0 | S k => bitsum bits k + bits k * wpow k end.

  Definition cbitsum (bits:nat->Z) (n:nat) : Z :=
    bitsum (fun i => bits i mod p) n.

  Lemma cbitsum_bound : forall bits n,
    (forall i, (i<n)%nat -> bits i mod p = 0 \/ bits i mod p = 1) ->
    0 <= cbitsum bits n <= wpow n - 1.
  Proof.
    intros bits n; revert bits. induction n as [|k IH]; intros bits Hb.
    - cbn [cbitsum bitsum wpow]. lia.
    - assert (Hk : bits k mod p = 0 \/ bits k mod p = 1) by (apply Hb; lia).
      assert (Hrec : forall i, (i<k)%nat -> bits i mod p = 0 \/ bits i mod p = 1)
        by (intros i Hi; apply Hb; lia).
      specialize (IH bits Hrec).
      pose proof (wpow_pos k) as Hwk.
      unfold cbitsum in *. cbn [bitsum wpow].
      destruct Hk as [E|E]; rewrite E; lia.
  Qed.

  Lemma bitsum_mod : forall bits n,
    bitsum bits n mod p = cbitsum bits n mod p.
  Proof.
    intros bits n; revert bits. induction n as [|k IH]; intros bits.
    - reflexivity.
    - unfold cbitsum in *. cbn [bitsum].
      rewrite (Zplus_mod (bitsum bits k)), IH.
      rewrite (Zplus_mod (bitsum (fun i => bits i mod p) k)).
      f_equal. f_equal.
      symmetry. apply Zmult_mod_idemp_l.
  Qed.

  Lemma order_lift : forall bits n v,
    wpow n <= p ->
    (forall i, (i<n)%nat -> bits i mod p = 0 \/ bits i mod p = 1) ->
    (bitsum bits n - v) mod p = 0 ->
    v mod p = cbitsum bits n /\ 0 <= v mod p < wpow n.
  Proof.
    intros bits n v Hnw Hb Hres.
    pose proof (cbitsum_bound bits n Hb) as [Hlo Hhi].

    assert (Hcbmod : cbitsum bits n mod p = cbitsum bits n)
      by (apply Z.mod_small; lia).

    pose proof (Z.mod_pos_bound (bitsum bits n) p ltac:(lia)) as [Ha1 Ha2].
    pose proof (Z.mod_pos_bound v p ltac:(lia)) as [Hb1 Hb2].
    assert (Hd0 : ((bitsum bits n) mod p - v mod p) mod p = 0)
      by (rewrite <- Zminus_mod; exact Hres).
    apply Z.mod_divide in Hd0; [| lia].
    destruct Hd0 as [q Hq].
    assert (Hq0 : q = 0) by nia. subst q.
    assert (Hvsum : v mod p = bitsum bits n mod p) by lia.

    assert (Hv : v mod p = cbitsum bits n)
      by (rewrite Hvsum, bitsum_mod, Hcbmod; reflexivity).
    split; [exact Hv | rewrite Hv; split; [exact Hlo | lia]].
  Qed.

End OrderLift.

Lemma pasta_ge2 : 2 <= pasta_p.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.

Lemma wpow64_le_pasta : wpow 64 <= pasta_p.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.

Lemma wpow14_le_pasta : wpow 14 <= pasta_p.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.

Lemma wpow8_le_pasta : wpow 8 <= pasta_p.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.

Definition order_lift_pasta := order_lift pasta_p pasta_ge2.

Print Assumptions order_lift.
Print Assumptions order_lift_pasta.
Print Assumptions wpow64_le_pasta.
