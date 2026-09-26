(* SPDX-License-Identifier: Apache-2.0
   SPDX-FileCopyrightText: 2026 Next Ridge Solutions Ltd

   Soundness: every accepted filling whose inputs satisfy the input assumption yields a triple the
   relation accepts (bridge_sound). Also, at the input whose limbs are all 2^64 - 1: an accepted filling
   decodes to it and its product, and no accepted filling decodes to an output that equals the product
   only modulo p, or to a named wrong output.

   Scope: these results bind the formal (Coq) layer only; the generated constraint model's fidelity to the circuit implementation, and the implementation itself, are outside them. *)

From Coq Require Import ZArith Lia List Znumtheory. Import ListNotations.
Open Scope Z_scope.

Require Import Generated.bm_model_gen.
Require Import Generated.bm_wires_gen.
Require Import Generated.bm_scaffold_gen.
Require Import Generated.bm_necessity_gen.
Require Import Constraints.field_order_lift.
Require Import Constraints.range_field_pasta.
Require Import Constraints.bits_kit.
Require Import Constraints.bm_semantic.
Require Import Constraints.bm_model_facts.
Require bm_rule.

Definition CONV (a b : list Z) : list Z :=
  [nth 0 a 0 * nth 0 b 0;
   nth 0 a 0 * nth 1 b 0 + nth 1 a 0 * nth 0 b 0;
   nth 0 a 0 * nth 2 b 0 + nth 1 a 0 * nth 1 b 0 + nth 2 a 0 * nth 0 b 0;
   nth 0 a 0 * nth 3 b 0 + nth 1 a 0 * nth 2 b 0 + nth 2 a 0 * nth 1 b 0 + nth 3 a 0 * nth 0 b 0;
   nth 1 a 0 * nth 3 b 0 + nth 2 a 0 * nth 2 b 0 + nth 3 a 0 * nth 1 b 0;
   nth 2 a 0 * nth 3 b 0 + nth 3 a 0 * nth 2 b 0;
   nth 3 a 0 * nth 3 b 0].

Lemma CONV_length : forall a b, length (CONV a b) = 7%nat.
Proof. reflexivity. Qed.

Theorem VAL_CONV : forall a b, length a = 4%nat -> length b = 4%nat ->
  bm_rule.VAL (CONV a b) = bm_rule.VAL a * bm_rule.VAL b.
Proof.
  intros a b Ha Hb.
  destruct a as [|a0 [|a1 [|a2 [|a3 [|? ?]]]]]; cbn [length] in Ha; try lia.
  destruct b as [|b0 [|b1 [|b2 [|b3 [|? ?]]]]]; cbn [length] in Hb; try lia.
  unfold CONV. cbn [nth]. symmetry. apply bm_rule.VAL_product_is_the_convolution.
Qed.

Lemma nth_limb : forall v i, Forall bm_rule.limb_ok v -> 0 <= nth i v 0 <= bm_rule.B - 1.
Proof.
  intros v i Hf. destruct (Nat.lt_ge_cases i (length v)) as [Hi|Hi].
  - rewrite Forall_forall in Hf. pose proof (Hf _ (nth_In v 0 Hi)) as H.
    unfold bm_rule.limb_ok in H. lia.
  - rewrite nth_overflow by exact Hi. rewrite bm_rule.B_value. lia.
Qed.

Lemma prod_bound : forall x y, 0 <= x <= bm_rule.B - 1 -> 0 <= y <= bm_rule.B - 1 ->
  0 <= x * y <= (bm_rule.B - 1) * (bm_rule.B - 1).
Proof. intros x y Hx Hy. split; [ nia | apply Z.mul_le_mono_nonneg; lia ]. Qed.

Theorem CONV_elem_bound : forall a b, bm_rule.PRE_bm a b ->
  forall m, 0 <= nth m (CONV a b) 0 <= 4 * (bm_rule.B - 1) * (bm_rule.B - 1).
Proof.
  intros a b [_ [_ [Fa Fb]]] m.
  pose proof (fun i => nth_limb a i Fa) as HA. pose proof (fun j => nth_limb b j Fb) as HB.
  pose proof (prod_bound _ _ (HA 0%nat) (HB 0%nat)) as P00.
  pose proof (prod_bound _ _ (HA 0%nat) (HB 1%nat)) as P01.
  pose proof (prod_bound _ _ (HA 0%nat) (HB 2%nat)) as P02.
  pose proof (prod_bound _ _ (HA 0%nat) (HB 3%nat)) as P03.
  pose proof (prod_bound _ _ (HA 1%nat) (HB 0%nat)) as P10.
  pose proof (prod_bound _ _ (HA 1%nat) (HB 1%nat)) as P11.
  pose proof (prod_bound _ _ (HA 1%nat) (HB 2%nat)) as P12.
  pose proof (prod_bound _ _ (HA 1%nat) (HB 3%nat)) as P13.
  pose proof (prod_bound _ _ (HA 2%nat) (HB 0%nat)) as P20.
  pose proof (prod_bound _ _ (HA 2%nat) (HB 1%nat)) as P21.
  pose proof (prod_bound _ _ (HA 2%nat) (HB 2%nat)) as P22.
  pose proof (prod_bound _ _ (HA 2%nat) (HB 3%nat)) as P23.
  pose proof (prod_bound _ _ (HA 3%nat) (HB 0%nat)) as P30.
  pose proof (prod_bound _ _ (HA 3%nat) (HB 1%nat)) as P31.
  pose proof (prod_bound _ _ (HA 3%nat) (HB 2%nat)) as P32.
  pose proof (prod_bound _ _ (HA 3%nat) (HB 3%nat)) as P33.
  destruct (Nat.lt_ge_cases m 7) as [Hm|Hm].
  - rewrite bm_rule.B_value in *.
    do 7 (destruct m as [|m]; [ cbn [CONV nth]; lia | ]). lia.
  - rewrite nth_overflow by (rewrite CONV_length; exact Hm). rewrite bm_rule.B_value. lia.
Qed.

Lemma VAL_firstn_S : forall i v,
  bm_rule.VAL (firstn (S i) v)
  = bm_rule.VAL (firstn i v) + bm_rule.B ^ Z.of_nat i * nth i v 0.
Proof.
  induction i as [|i IH]; intro v; destruct v as [|x t].
  - cbn [firstn nth Z.of_nat]. rewrite bm_rule.VAL_nil. ring.
  - cbn [firstn nth Z.of_nat]. rewrite bm_rule.VAL_cons, !bm_rule.VAL_nil. ring.
  - cbn [firstn nth]. rewrite bm_rule.VAL_nil. ring.
  - change (firstn (S (S i)) (x :: t)) with (x :: firstn (S i) t).
    change (firstn (S i) (x :: t)) with (x :: firstn i t).
    change (nth (S i) (x :: t) 0) with (nth i t 0).
    rewrite !bm_rule.VAL_cons, (IH t).
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. ring.
Qed.

Definition prevc (c : nat -> Z) (i : nat) : Z :=
  match i with O => 0 | S j => c j end.

Theorem prefix_telescopes : forall (s o : list Z) (c : nat -> Z) n,
  (forall i, (i <= n)%nat -> nth i s 0 - nth i o 0 = c i * bm_rule.B - prevc c i) ->
  bm_rule.VAL (firstn (S n) s) - bm_rule.VAL (firstn (S n) o)
  = c n * bm_rule.B ^ Z.of_nat (S n).
Proof.
  intros s o c n. induction n as [|n IH]; intro H.
  - rewrite !(VAL_firstn_S 0). cbn [firstn Z.of_nat]. rewrite bm_rule.VAL_nil.
    pose proof (H 0%nat ltac:(lia)) as H0. cbn [prevc] in H0.
    rewrite Z.pow_0_r. rewrite Z.pow_1_r. lia.
  - rewrite !(VAL_firstn_S (S n)).
    pose proof (IH (fun i Hi => H i ltac:(lia))) as IHn.
    pose proof (H (S n) ltac:(lia)) as Hs. cbn [prevc] in Hs.
    replace (bm_rule.VAL (firstn (S n) s) + bm_rule.B ^ Z.of_nat (S n) * nth (S n) s 0 -
             (bm_rule.VAL (firstn (S n) o) + bm_rule.B ^ Z.of_nat (S n) * nth (S n) o 0))
       with ((bm_rule.VAL (firstn (S n) s) - bm_rule.VAL (firstn (S n) o))
             + bm_rule.B ^ Z.of_nat (S n) * (nth (S n) s 0 - nth (S n) o 0)) by ring.
    rewrite IHn, Hs.
    rewrite (Nat2Z.inj_succ (S n)), (Z.pow_succ_r _ (Z.of_nat (S n))) by lia. ring.
Qed.

Lemma cong_add : forall x y x' y', x mod p = x' mod p -> y mod p = y' mod p ->
  (x + y) mod p = (x' + y') mod p.
Proof. intros. rewrite Zplus_mod, H, H0, <- Zplus_mod. reflexivity. Qed.
Lemma cong_sub : forall x y x' y', x mod p = x' mod p -> y mod p = y' mod p ->
  (x - y) mod p = (x' - y') mod p.
Proof. intros. rewrite Zminus_mod, H, H0, <- Zminus_mod. reflexivity. Qed.
Lemma cong_mul : forall x y x' y', x mod p = x' mod p -> y mod p = y' mod p ->
  (x * y) mod p = (x' * y') mod p.
Proof. intros. rewrite Zmult_mod, H, H0, <- Zmult_mod. reflexivity. Qed.
Lemma cong_dc : forall a c, (dc a c) mod p = (a (c, 0%nat)) mod p.
Proof. intros. unfold dc. apply Zmod_mod. Qed.
Lemma cong_cc : forall a i, (cc a i) mod p = (a ((16 + i)%nat, 0%nat)) mod p.
Proof. intros. unfold cc. apply cong_dc. Qed.

Ltac cong := repeat first
  [ apply cong_dc | apply cong_cc | apply cong_mul | apply cong_sub | apply cong_add | reflexivity ].

Lemma p_pos : 0 < p. Proof. pose proof p_ge2. lia. Qed.

Definition EEND (a : Assignment) : Z := cc a 6 - dc a 15.
Definition RWEND (a : Assignment) : Z := a (22%nat, 0%nat) - a (15%nat, 0%nat).
Lemma ev_end : forall a, eval a (nth 0 tg_end (EConst 0)) = RWEND a.
Proof. intro a. unfold RWEND. cbn [nth tg_end eval]. ring. Qed.
Lemma cong_EEND : forall a, (EEND a) mod p = (RWEND a) mod p.
Proof. intro a. unfold EEND, RWEND. cong. Qed.

Theorem the_last_carry_cell_is_out7 : forall a, sat deployed_model a -> cc a 6 = dc a 15.
Proof.
  intros a Hs.
  assert (HE : EEND a = 0).
  { apply (no_wrap_zero p); [ exact p_pos | | | ].
    3: { rewrite cong_EEND, <- ev_end. destruct Hs as [Hg _]. exact (Hg _ tg_end_in). }

    all: pose proof (dc_range a 22); pose proof (dc_range a 15);
         unfold EEND; change (cc a 6) with (dc a 22); lia. }
  unfold EEND in HE. lia.
Qed.

Definition E0 (a : Assignment) : Z := nth 0 (CONV (a_l a) (b_l a)) 0 - dc a 8 - cc a 0 * 18446744073709551616.
Definition RW0 (a : Assignment) : Z := a (0%nat, 0%nat) * a (4%nat, 0%nat) - a (8%nat, 0%nat) - a (16%nat, 0%nat) * 18446744073709551616.
Lemma ev_chain_0 : forall a, eval a (nth 0 tg_chain (EConst 0)) = RW0 a.
Proof. intro a. unfold RW0. cbn [nth tg_chain eval]. ring. Qed.
Lemma cong_E0 : forall a, (E0 a) mod p = (RW0 a) mod p.
Proof. intro a. unfold E0, RW0, CONV, a_l, b_l. cbn [nth]. cong. Qed.
Definition E1 (a : Assignment) : Z := nth 1 (CONV (a_l a) (b_l a)) 0 - dc a 9 + cc a 0 - cc a 1 * 18446744073709551616.
Definition RW1 (a : Assignment) : Z := a (0%nat, 0%nat) * a (5%nat, 0%nat) + a (1%nat, 0%nat) * a (4%nat, 0%nat) - a (9%nat, 0%nat) + a (16%nat, 0%nat) - a (17%nat, 0%nat) * 18446744073709551616.
Lemma ev_chain_1 : forall a, eval a (nth 1 tg_chain (EConst 0)) = RW1 a.
Proof. intro a. unfold RW1. cbn [nth tg_chain eval]. ring. Qed.
Lemma cong_E1 : forall a, (E1 a) mod p = (RW1 a) mod p.
Proof. intro a. unfold E1, RW1, CONV, a_l, b_l. cbn [nth]. cong. Qed.
Definition E2 (a : Assignment) : Z := nth 2 (CONV (a_l a) (b_l a)) 0 - dc a 10 + cc a 1 - cc a 2 * 18446744073709551616.
Definition RW2 (a : Assignment) : Z := a (0%nat, 0%nat) * a (6%nat, 0%nat) + a (1%nat, 0%nat) * a (5%nat, 0%nat) + a (2%nat, 0%nat) * a (4%nat, 0%nat) - a (10%nat, 0%nat) + a (17%nat, 0%nat) - a (18%nat, 0%nat) * 18446744073709551616.
Lemma ev_chain_2 : forall a, eval a (nth 2 tg_chain (EConst 0)) = RW2 a.
Proof. intro a. unfold RW2. cbn [nth tg_chain eval]. ring. Qed.
Lemma cong_E2 : forall a, (E2 a) mod p = (RW2 a) mod p.
Proof. intro a. unfold E2, RW2, CONV, a_l, b_l. cbn [nth]. cong. Qed.
Definition E3 (a : Assignment) : Z := nth 3 (CONV (a_l a) (b_l a)) 0 - dc a 11 + cc a 2 - cc a 3 * 18446744073709551616.
Definition RW3 (a : Assignment) : Z := a (0%nat, 0%nat) * a (7%nat, 0%nat) + a (1%nat, 0%nat) * a (6%nat, 0%nat) + a (2%nat, 0%nat) * a (5%nat, 0%nat) + a (3%nat, 0%nat) * a (4%nat, 0%nat) - a (11%nat, 0%nat) + a (18%nat, 0%nat) - a (19%nat, 0%nat) * 18446744073709551616.
Lemma ev_chain_3 : forall a, eval a (nth 3 tg_chain (EConst 0)) = RW3 a.
Proof. intro a. unfold RW3. cbn [nth tg_chain eval]. ring. Qed.
Lemma cong_E3 : forall a, (E3 a) mod p = (RW3 a) mod p.
Proof. intro a. unfold E3, RW3, CONV, a_l, b_l. cbn [nth]. cong. Qed.
Definition E4 (a : Assignment) : Z := nth 4 (CONV (a_l a) (b_l a)) 0 - dc a 12 + cc a 3 - cc a 4 * 18446744073709551616.
Definition RW4 (a : Assignment) : Z := a (1%nat, 0%nat) * a (7%nat, 0%nat) + a (2%nat, 0%nat) * a (6%nat, 0%nat) + a (3%nat, 0%nat) * a (5%nat, 0%nat) - a (12%nat, 0%nat) + a (19%nat, 0%nat) - a (20%nat, 0%nat) * 18446744073709551616.
Lemma ev_chain_4 : forall a, eval a (nth 4 tg_chain (EConst 0)) = RW4 a.
Proof. intro a. unfold RW4. cbn [nth tg_chain eval]. ring. Qed.
Lemma cong_E4 : forall a, (E4 a) mod p = (RW4 a) mod p.
Proof. intro a. unfold E4, RW4, CONV, a_l, b_l. cbn [nth]. cong. Qed.
Definition E5 (a : Assignment) : Z := nth 5 (CONV (a_l a) (b_l a)) 0 - dc a 13 + cc a 4 - cc a 5 * 18446744073709551616.
Definition RW5 (a : Assignment) : Z := a (2%nat, 0%nat) * a (7%nat, 0%nat) + a (3%nat, 0%nat) * a (6%nat, 0%nat) - a (13%nat, 0%nat) + a (20%nat, 0%nat) - a (21%nat, 0%nat) * 18446744073709551616.
Lemma ev_chain_5 : forall a, eval a (nth 5 tg_chain (EConst 0)) = RW5 a.
Proof. intro a. unfold RW5. cbn [nth tg_chain eval]. ring. Qed.
Lemma cong_E5 : forall a, (E5 a) mod p = (RW5 a) mod p.
Proof. intro a. unfold E5, RW5, CONV, a_l, b_l. cbn [nth]. cong. Qed.
Definition E6 (a : Assignment) : Z := nth 6 (CONV (a_l a) (b_l a)) 0 - dc a 14 + cc a 5 - cc a 6 * 18446744073709551616.
Definition RW6 (a : Assignment) : Z := a (3%nat, 0%nat) * a (7%nat, 0%nat) - a (14%nat, 0%nat) + a (21%nat, 0%nat) - a (22%nat, 0%nat) * 18446744073709551616.
Lemma ev_chain_6 : forall a, eval a (nth 6 tg_chain (EConst 0)) = RW6 a.
Proof. intro a. unfold RW6. cbn [nth tg_chain eval]. ring. Qed.
Lemma cong_E6 : forall a, (E6 a) mod p = (RW6 a) mod p.
Proof. intro a. unfold E6, RW6, CONV, a_l, b_l. cbn [nth]. cong. Qed.

Lemma E0_zero : forall a, sat deployed_model a -> bm_rule.PRE_bm (a_l a) (b_l a) -> E0 a = 0.
Proof.
  intros a Hs Hpre. apply (no_wrap_zero p); [ exact p_pos | | | ].
  3: { rewrite cong_E0, <- ev_chain_0. destruct Hs as [Hg _].
       exact (Hg _ (tg_chain_in 0%nat ltac:(lia))). }
  all: pose proof (CONV_elem_bound (a_l a) (b_l a) Hpre 0%nat) as Hv; rewrite bm_rule.B_value in Hv;
       pose proof (rng_out a Hs 0%nat ltac:(lia)) as Ho; cbn [Nat.add] in Ho;
       pose proof (rng_c a Hs 0%nat ltac:(lia)) as Hc;
       pose proof p_odd; pose proof HALF_big;
       change (2 ^ 140) with 1393796574908163946345982392040522594123776 in *;
       unfold E0; lia.
Qed.
Lemma E1_zero : forall a, sat deployed_model a -> bm_rule.PRE_bm (a_l a) (b_l a) -> E1 a = 0.
Proof.
  intros a Hs Hpre. apply (no_wrap_zero p); [ exact p_pos | | | ].
  3: { rewrite cong_E1, <- ev_chain_1. destruct Hs as [Hg _].
       exact (Hg _ (tg_chain_in 1%nat ltac:(lia))). }
  all: pose proof (CONV_elem_bound (a_l a) (b_l a) Hpre 1%nat) as Hv; rewrite bm_rule.B_value in Hv;
       pose proof (rng_out a Hs 1%nat ltac:(lia)) as Ho; cbn [Nat.add] in Ho;
       pose proof (rng_c a Hs 1%nat ltac:(lia)) as Hc;
       pose proof (rng_c a Hs 0%nat ltac:(lia)) as Hp;
       pose proof p_odd; pose proof HALF_big;
       change (2 ^ 140) with 1393796574908163946345982392040522594123776 in *;
       unfold E1; lia.
Qed.
Lemma E2_zero : forall a, sat deployed_model a -> bm_rule.PRE_bm (a_l a) (b_l a) -> E2 a = 0.
Proof.
  intros a Hs Hpre. apply (no_wrap_zero p); [ exact p_pos | | | ].
  3: { rewrite cong_E2, <- ev_chain_2. destruct Hs as [Hg _].
       exact (Hg _ (tg_chain_in 2%nat ltac:(lia))). }
  all: pose proof (CONV_elem_bound (a_l a) (b_l a) Hpre 2%nat) as Hv; rewrite bm_rule.B_value in Hv;
       pose proof (rng_out a Hs 2%nat ltac:(lia)) as Ho; cbn [Nat.add] in Ho;
       pose proof (rng_c a Hs 2%nat ltac:(lia)) as Hc;
       pose proof (rng_c a Hs 1%nat ltac:(lia)) as Hp;
       pose proof p_odd; pose proof HALF_big;
       change (2 ^ 140) with 1393796574908163946345982392040522594123776 in *;
       unfold E2; lia.
Qed.
Lemma E3_zero : forall a, sat deployed_model a -> bm_rule.PRE_bm (a_l a) (b_l a) -> E3 a = 0.
Proof.
  intros a Hs Hpre. apply (no_wrap_zero p); [ exact p_pos | | | ].
  3: { rewrite cong_E3, <- ev_chain_3. destruct Hs as [Hg _].
       exact (Hg _ (tg_chain_in 3%nat ltac:(lia))). }
  all: pose proof (CONV_elem_bound (a_l a) (b_l a) Hpre 3%nat) as Hv; rewrite bm_rule.B_value in Hv;
       pose proof (rng_out a Hs 3%nat ltac:(lia)) as Ho; cbn [Nat.add] in Ho;
       pose proof (rng_c a Hs 3%nat ltac:(lia)) as Hc;
       pose proof (rng_c a Hs 2%nat ltac:(lia)) as Hp;
       pose proof p_odd; pose proof HALF_big;
       change (2 ^ 140) with 1393796574908163946345982392040522594123776 in *;
       unfold E3; lia.
Qed.
Lemma E4_zero : forall a, sat deployed_model a -> bm_rule.PRE_bm (a_l a) (b_l a) -> E4 a = 0.
Proof.
  intros a Hs Hpre. apply (no_wrap_zero p); [ exact p_pos | | | ].
  3: { rewrite cong_E4, <- ev_chain_4. destruct Hs as [Hg _].
       exact (Hg _ (tg_chain_in 4%nat ltac:(lia))). }
  all: pose proof (CONV_elem_bound (a_l a) (b_l a) Hpre 4%nat) as Hv; rewrite bm_rule.B_value in Hv;
       pose proof (rng_out a Hs 4%nat ltac:(lia)) as Ho; cbn [Nat.add] in Ho;
       pose proof (rng_c a Hs 4%nat ltac:(lia)) as Hc;
       pose proof (rng_c a Hs 3%nat ltac:(lia)) as Hp;
       pose proof p_odd; pose proof HALF_big;
       change (2 ^ 140) with 1393796574908163946345982392040522594123776 in *;
       unfold E4; lia.
Qed.
Lemma E5_zero : forall a, sat deployed_model a -> bm_rule.PRE_bm (a_l a) (b_l a) -> E5 a = 0.
Proof.
  intros a Hs Hpre. apply (no_wrap_zero p); [ exact p_pos | | | ].
  3: { rewrite cong_E5, <- ev_chain_5. destruct Hs as [Hg _].
       exact (Hg _ (tg_chain_in 5%nat ltac:(lia))). }
  all: pose proof (CONV_elem_bound (a_l a) (b_l a) Hpre 5%nat) as Hv; rewrite bm_rule.B_value in Hv;
       pose proof (rng_out a Hs 5%nat ltac:(lia)) as Ho; cbn [Nat.add] in Ho;
       pose proof (rng_c a Hs 5%nat ltac:(lia)) as Hc;
       pose proof (rng_c a Hs 4%nat ltac:(lia)) as Hp;
       pose proof p_odd; pose proof HALF_big;
       change (2 ^ 140) with 1393796574908163946345982392040522594123776 in *;
       unfold E5; lia.
Qed.
Lemma E6_zero : forall a, sat deployed_model a -> bm_rule.PRE_bm (a_l a) (b_l a) -> E6 a = 0.
Proof.
  intros a Hs Hpre. apply (no_wrap_zero p); [ exact p_pos | | | ].
  3: { rewrite cong_E6, <- ev_chain_6. destruct Hs as [Hg _].
       exact (Hg _ (tg_chain_in 6%nat ltac:(lia))). }
  all: pose proof (CONV_elem_bound (a_l a) (b_l a) Hpre 6%nat) as Hv; rewrite bm_rule.B_value in Hv;
       pose proof (rng_out a Hs 6%nat ltac:(lia)) as Ho; cbn [Nat.add] in Ho;
       pose proof (the_last_carry_cell_is_out7 a Hs) as H6; pose proof (rng_out a Hs 7%nat ltac:(lia)) as Hc; cbn [Nat.add] in Hc;
       pose proof (rng_c a Hs 5%nat ltac:(lia)) as Hp;
       pose proof p_odd; pose proof HALF_big;
       change (2 ^ 140) with 1393796574908163946345982392040522594123776 in *;
       unfold E6; lia.
Qed.

Theorem circuit_running : forall a, sat deployed_model a -> bm_rule.PRE_bm (a_l a) (b_l a) ->
  forall i, (i <= 6)%nat ->
    nth i (CONV (a_l a) (b_l a)) 0 - nth i (out_l a) 0 = cc a i * bm_rule.B - prevc (cc a) i.
Proof.
  intros a Hs Hpre i Hi. rewrite bm_rule.B_value.
  destruct i as [|i]; [ pose proof (E0_zero a Hs Hpre) as HE; unfold E0 in HE; cbn [prevc nth out_l]; lia | ].
  destruct i as [|i]; [ pose proof (E1_zero a Hs Hpre) as HE; unfold E1 in HE; cbn [prevc nth out_l]; lia | ].
  destruct i as [|i]; [ pose proof (E2_zero a Hs Hpre) as HE; unfold E2 in HE; cbn [prevc nth out_l]; lia | ].
  destruct i as [|i]; [ pose proof (E3_zero a Hs Hpre) as HE; unfold E3 in HE; cbn [prevc nth out_l]; lia | ].
  destruct i as [|i]; [ pose proof (E4_zero a Hs Hpre) as HE; unfold E4 in HE; cbn [prevc nth out_l]; lia | ].
  destruct i as [|i]; [ pose proof (E5_zero a Hs Hpre) as HE; unfold E5 in HE; cbn [prevc nth out_l]; lia | ].
  destruct i as [|i]; [ pose proof (E6_zero a Hs Hpre) as HE; unfold E6 in HE; cbn [prevc nth out_l]; lia | ].
  lia.
Qed.

Lemma CONV_firstn : forall a b, firstn 7 (CONV a b) = CONV a b.
Proof. reflexivity. Qed.
Lemma out_l_skipn : forall a, skipn 7 (out_l a) = [dc a 15].
Proof. reflexivity. Qed.

Theorem values_agree : forall a, sat deployed_model a -> bm_rule.PRE_bm (a_l a) (b_l a) ->
  bm_rule.VAL (out_l a) = bm_rule.VAL (a_l a) * bm_rule.VAL (b_l a).
Proof.
  intros a Hs Hpre.
  pose proof (prefix_telescopes (CONV (a_l a) (b_l a)) (out_l a) (cc a) 6
                (fun i Hi => circuit_running a Hs Hpre i Hi)) as T.
  rewrite CONV_firstn in T.
  rewrite (VAL_CONV (a_l a) (b_l a) (a_l_length a) (b_l_length a)) in T.
  pose proof (bm_rule.VAL_firstn_skipn 7 (out_l a)) as S7.
  rewrite out_l_skipn in S7.
  assert (Hv : bm_rule.VAL [dc a 15] = dc a 15)
    by (rewrite bm_rule.VAL_cons, bm_rule.VAL_nil; ring).
  rewrite Hv in S7.
  rewrite (the_last_carry_cell_is_out7 a Hs) in T.
  assert (HC : dc a 15 * bm_rule.B ^ Z.of_nat 7 = bm_rule.B ^ Z.of_nat 7 * dc a 15) by ring.
  lia.
Qed.

(* Soundness, for accepted fillings whose inputs satisfy the input assumption. *)
Theorem bridge_sound : forall a,
  sat deployed_model a ->
  CANON_bm a ->
  bm_rule.PRE_bm (a_l a) (b_l a) ->
  bm_rule.REL_bm (a_l a) (b_l a) (out_l a).
Proof.
  intros a Hs _ Hpre.
  split; [ reflexivity | ].
  split; [ exact (out_limbs_in_range a Hs) | exact (values_agree a Hs Hpre) ].
Qed.

Theorem bridge_sound_without_CANON : forall a,
  sat deployed_model a -> bm_rule.PRE_bm (a_l a) (b_l a) ->
  bm_rule.REL_bm (a_l a) (b_l a) (out_l a).
Proof. intros a Hs Hpre. exact (bridge_sound a Hs (CANON_is_free a) Hpre). Qed.

Theorem nonvacuity_the_honest_row_decodes_to_the_corner :
  sat deployed_model wit_honest_bm
  /\ a_l wit_honest_bm = bm_rule.CORNER
  /\ b_l wit_honest_bm = bm_rule.CORNER
  /\ out_l wit_honest_bm = bm_rule.CORNER_OUT.
Proof.
  split; [ exact honest_full_sat_bm | ].
  split; [ vm_compute; reflexivity | ]. split; vm_compute; reflexivity.
Qed.

Theorem nonvacuity_the_corner_is_ACCEPTED :
  bm_rule.REL_bm (a_l wit_honest_bm) (b_l wit_honest_bm) (out_l wit_honest_bm).
Proof.
  destruct nonvacuity_the_honest_row_decodes_to_the_corner as [Hs [Ha [Hb _]]].
  apply (bridge_sound_without_CANON _ Hs). rewrite Ha, Hb. exact bm_rule.corner_pre.
Qed.

Theorem no_satisfying_row_decodes_to_the_modular_alias : forall a,
  sat deployed_model a ->
  ~ (a_l a = bm_rule.CORNER /\ b_l a = bm_rule.CORNER /\ out_l a = CORNER_ALIAS).
Proof.
  intros a Hs [Ha [Hb Ho]].
  destruct REL_is_a_value_equality_not_mod_q as [_ [_ [_ [_ [_ Hn]]]]]. apply Hn.
  rewrite <- Ha at 1. rewrite <- Hb, <- Ho.
  apply (bridge_sound_without_CANON a Hs). rewrite Ha, Hb. exact bm_rule.corner_pre.
Qed.

Theorem no_satisfying_row_decodes_to_the_corner_fraud : forall a,
  sat deployed_model a ->
  ~ (a_l a = bm_rule.CORNER /\ b_l a = bm_rule.CORNER /\ out_l a = bm_rule.CORNER_FRAUD).
Proof.
  intros a Hs [Ha [Hb Ho]]. apply bm_rule.corner_fraud_refused.
  rewrite <- Ha at 1. rewrite <- Hb, <- Ho.
  apply (bridge_sound_without_CANON a Hs). rewrite Ha, Hb. exact bm_rule.corner_pre.
Qed.

Print Assumptions VAL_CONV.
Print Assumptions nth_limb.
Print Assumptions prod_bound.
Print Assumptions CONV_elem_bound.
Print Assumptions VAL_firstn_S.
Print Assumptions prefix_telescopes.
Print Assumptions the_last_carry_cell_is_out7.
Print Assumptions circuit_running.
Print Assumptions values_agree.
Print Assumptions bridge_sound.
Print Assumptions bridge_sound_without_CANON.
Print Assumptions nonvacuity_the_honest_row_decodes_to_the_corner.
Print Assumptions nonvacuity_the_corner_is_ACCEPTED.
Print Assumptions no_satisfying_row_decodes_to_the_modular_alias.
Print Assumptions no_satisfying_row_decodes_to_the_corner_fraud.
