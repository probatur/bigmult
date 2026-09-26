(* SPDX-License-Identifier: Apache-2.0
   SPDX-FileCopyrightText: 2026 Next Ridge Solutions Ltd

   Reading the operand triple off a filling: each operand cell as its canonical remainder modulo p (dc),
   the vectors a_l, b_l and out_l, and the canonicity predicate CANON_bm, which every filling satisfies
   (CANON_is_free). Also the public cells' agreement with the output cells, derived from the copy
   constraints (answer_pins_are_DERIVED), the checked count of polynomial constraints (dg_len), and the
   range bounds every accepted filling puts on its output cells and its first six carry cells
   (rng_out, rng_c).

   Scope: these results bind the formal (Coq) layer only; the generated constraint model's fidelity to the circuit implementation, and the implementation itself, are outside them. *)

From Coq Require Import ZArith Lia List Znumtheory. Import ListNotations.
Open Scope Z_scope.

Require Import Generated.bm_model_gen.
Require Import Generated.bm_wires_gen.
Require Import Generated.bm_scaffold_gen.
Require Import Constraints.field_order_lift.
Require Import Constraints.range_field_pasta.
Require bm_rule.

Lemma p_eq_pasta : p = pasta_p.
Proof. reflexivity. Qed.

Lemma p_prime : prime p.
Proof. rewrite p_eq_pasta. exact pasta_prime. Qed.

Lemma p_ge2 : 2 <= p.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.

Definition HALF : Z := (p - 1) / 2.

Lemma p_odd : p = 2 * HALF + 1.
Proof. vm_compute. reflexivity. Qed.

Lemma HALF_big : 2 ^ 140 <= HALF.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.

Definition dc (a : Assignment) (c : nat) : Z := (a (c, 0%nat)) mod p.

Definition A_BASE      : nat := 0.
Definition B_BASE      : nat := 4.
Definition OUT_BASE    : nat := 8.
Definition C_BASE      : nat := 16.
Definition OUTBIT_BASE : nat := 23.
Definition CBIT_BASE   : nat := 535.
Definition N_ADVICE    : nat := 931.
Definition TAG_BASE    : nat := 2000.

Definition a_l (a : Assignment) : list Z := [dc a 0; dc a 1; dc a 2; dc a 3].
Definition b_l (a : Assignment) : list Z := [dc a 4; dc a 5; dc a 6; dc a 7].
Definition out_l (a : Assignment) : list Z :=
  [dc a 8; dc a 9; dc a 10; dc a 11; dc a 12; dc a 13; dc a 14; dc a 15].

Definition cc (a : Assignment) (i : nat) : Z := dc a (16 + i).

Lemma a_l_length : forall a, length (a_l a) = bm_rule.K.
Proof. reflexivity. Qed.
Lemma b_l_length : forall a, length (b_l a) = bm_rule.K.
Proof. reflexivity. Qed.
Lemma out_l_length : forall a, length (out_l a) = (2 * bm_rule.K)%nat.
Proof. reflexivity. Qed.

Lemma dc_range : forall a c, 0 <= dc a c < p.
Proof. intros a c. unfold dc. apply Z.mod_pos_bound. pose proof p_ge2. lia. Qed.

Definition bool_gate (c : nat) : Expr :=
  EMul (ECell (c, 0%nat)) (ESub (ECell (c, 0%nat)) (EConst 1)).

Lemma in_firstn_in : forall (A : Type) n (l : list A) x,
  In x (firstn n l) -> In x l.
Proof.
  intros A n. induction n as [|n IH]; intros l x H; [ destruct H | ].
  destruct l as [|y l]; [ destruct H | ].
  cbn [firstn] in H. destruct H as [->|H]; [ left; reflexivity | ].
  right. exact (IH l x H).
Qed.

Lemma in_skipn_in : forall (A : Type) n (l : list A) x,
  In x (skipn n l) -> In x l.
Proof.
  intros A n. induction n as [|n IH]; intros l x H; [ exact H | ].
  destruct l as [|y l]; [ destruct H | ].
  cbn [skipn] in H. right. exact (IH l x H).
Qed.

Theorem head_is_the_booleanity_bank :
  firstn 908 deployed_gates = map (fun j => bool_gate (23 + j)) (seq 0 908).
Proof. vm_compute. reflexivity. Qed.

Lemma bool_gate_in_model : forall j, (j < 908)%nat ->
  In (bool_gate (23 + j)) deployed_gates.
Proof.
  intros j Hj. apply (in_firstn_in _ 908).
  rewrite head_is_the_booleanity_bank.
  apply (in_map (fun k => bool_gate (23 + k)%nat)). apply in_seq. lia.
Qed.

Definition tail_gates : list Expr := Eval vm_compute in (skipn 908 deployed_gates).

Lemma tail_gates_length : length tail_gates = 22%nat.
Proof. reflexivity. Qed.

(* The model has 930 polynomial constraints (the 8 copy constraints are separate). *)
Lemma dg_len : length deployed_gates = 930%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma head_and_tail_exhaust_the_model :
  (908 + length tail_gates)%nat = length deployed_gates.
Proof. rewrite tail_gates_length, dg_len. reflexivity. Qed.

Definition tg_rec_out : list Expr := Eval vm_compute in (firstn 8 tail_gates).
Definition tg_rec_c   : list Expr := Eval vm_compute in (firstn 6 (skipn 8 tail_gates)).
Definition tg_chain   : list Expr := Eval vm_compute in (firstn 7 (skipn 14 tail_gates)).
Definition tg_end     : list Expr := Eval vm_compute in (skipn 21 tail_gates).

Lemma tg_rec_out_eq : tg_rec_out = firstn 8 tail_gates. Proof. vm_compute. reflexivity. Qed.
Lemma tg_rec_c_eq : tg_rec_c = firstn 6 (skipn 8 tail_gates). Proof. vm_compute. reflexivity. Qed.
Lemma tg_chain_eq : tg_chain = firstn 7 (skipn 14 tail_gates). Proof. vm_compute. reflexivity. Qed.
Lemma tg_end_eq : tg_end = skipn 21 tail_gates. Proof. vm_compute. reflexivity. Qed.

Theorem tail_split_is_a_partition :
  tg_rec_out ++ tg_rec_c ++ tg_chain ++ tg_end = tail_gates.
Proof. vm_compute. reflexivity. Qed.

Lemma tg_rec_out_len : length tg_rec_out = 8%nat. Proof. reflexivity. Qed.
Lemma tg_rec_c_len   : length tg_rec_c   = 6%nat. Proof. reflexivity. Qed.
Lemma tg_chain_len   : length tg_chain   = 7%nat. Proof. reflexivity. Qed.
Lemma tg_end_len     : length tg_end     = 1%nat. Proof. reflexivity. Qed.

Lemma in_tail_in_model : forall x, In x tail_gates -> In x deployed_gates.
Proof.
  intros x H. apply (in_skipn_in _ 908).
  change (skipn 908 deployed_gates) with tail_gates. exact H.
Qed.

Lemma tg_rec_out_in : forall k, (k < 8)%nat -> In (nth k tg_rec_out (EConst 0)) deployed_gates.
Proof.
  intros k Hk. apply in_tail_in_model. apply (in_firstn_in _ 8).
  rewrite <- tg_rec_out_eq. apply nth_In. rewrite tg_rec_out_len. exact Hk.
Qed.
Lemma tg_rec_c_in : forall k, (k < 6)%nat -> In (nth k tg_rec_c (EConst 0)) deployed_gates.
Proof.
  intros k Hk. apply in_tail_in_model. apply (in_skipn_in _ 8). apply (in_firstn_in _ 6).
  rewrite <- tg_rec_c_eq. apply nth_In. rewrite tg_rec_c_len. exact Hk.
Qed.
Lemma tg_chain_in : forall k, (k < 7)%nat -> In (nth k tg_chain (EConst 0)) deployed_gates.
Proof.
  intros k Hk. apply in_tail_in_model. apply (in_skipn_in _ 14). apply (in_firstn_in _ 7).
  rewrite <- tg_chain_eq. apply nth_In. rewrite tg_chain_len. exact Hk.
Qed.
Lemma tg_end_in : In (nth 0 tg_end (EConst 0)) deployed_gates.
Proof.
  apply in_tail_in_model. apply (in_skipn_in _ 21).
  rewrite <- tg_end_eq. apply nth_In. rewrite tg_end_len. lia.
Qed.

Definition CANON_bm (a : Assignment) : Prop :=
  (forall i, (i < 4)%nat -> 0 <= dc a (0 + i) < p)
  /\ (forall i, (i < 4)%nat -> 0 <= dc a (4 + i) < p)
  /\ (forall i, (i < 8)%nat -> 0 <= dc a (8 + i) < p).

Theorem CANON_is_free : forall a, CANON_bm a.
Proof. intro a. split; [ | split ]; intros i _; apply dc_range. Qed.

Definition PINS_bm (a : Assignment) : Prop :=
  forall j, (j < 8)%nat -> dc a (8 + j) = (a (2000%nat, j)) mod p.

Theorem answer_pins_are_DERIVED : forall a, sat deployed_model a -> PINS_bm a.
Proof.
  intros a [_ Hc] j Hj. unfold dc.
  do 8 (destruct j as [|j];
    [ first [ exact (copy_get a _ _ Hc in_copy_1) | exact (copy_get a _ _ Hc in_copy_2)
            | exact (copy_get a _ _ Hc in_copy_3) | exact (copy_get a _ _ Hc in_copy_4)
            | exact (copy_get a _ _ Hc in_copy_5) | exact (copy_get a _ _ Hc in_copy_6)
            | exact (copy_get a _ _ Hc in_copy_7) | exact (copy_get a _ _ Hc in_copy_8) ] | ]).
  lia.
Qed.

Theorem every_bit_cell_is_boolean : forall a,
  sat deployed_model a ->
  forall j, (j < 908)%nat ->
    (a ((23 + j)%nat, 0%nat)) mod p = 0 \/ (a ((23 + j)%nat, 0%nat)) mod p = 1.
Proof.
  intros a [Hg _] j Hj.
  pose proof (Hg _ (bool_gate_in_model j Hj)) as H.
  unfold gate_holds in H. cbn [eval] in H.
  apply (range_field.bool_mod_forces_01 p p_prime).
  replace (a ((23 + j)%nat, 0%nat) * a ((23 + j)%nat, 0%nat) - a ((23 + j)%nat, 0%nat))
     with (a ((23 + j)%nat, 0%nat) * (a ((23 + j)%nat, 0%nat) - 1)) by ring.
  exact H.
Qed.

Definition bits_at (a : Assignment) (b : nat) : nat -> Z :=
  fun j => a ((b + j)%nat, 0%nat).

Lemma bank_bits_boolean : forall a,
  sat deployed_model a ->
  forall b n, (23 <= b)%nat -> (b + n <= 931)%nat ->
  forall j, (j < n)%nat ->
    (bits_at a b j) mod p = 0 \/ (bits_at a b j) mod p = 1.
Proof.
  intros a Hs b n Hb Hbn j Hj. unfold bits_at.
  replace (b + j)%nat with (23 + (b - 23 + j))%nat by lia.
  apply (every_bit_cell_is_boolean a Hs). lia.
Qed.

Lemma wpow64_le_p : wpow 64 <= p.
Proof. rewrite p_eq_pasta. exact wpow64_le_pasta. Qed.
Lemma wpow66_le_p : wpow 66 <= p.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma wpow64_val : wpow 64 = 18446744073709551616.
Proof. vm_compute. reflexivity. Qed.
Lemma wpow66_val : wpow 66 = 73786976294838206464.
Proof. vm_compute. reflexivity. Qed.

Lemma range_from_gate : forall a b n v,
  sat deployed_model a ->
  (23 <= b)%nat -> (b + n <= 931)%nat ->
  wpow n <= p ->
  (bitsum (bits_at a b) n - v) mod p = 0 ->
  0 <= v mod p < wpow n.
Proof.
  intros a b n v Hs Hb Hbn Hw Hres.
  destruct (order_lift p p_ge2 (bits_at a b) n v Hw
              (bank_bits_boolean a Hs b n Hb Hbn) Hres) as [_ Hr].
  exact Hr.
Qed.
Lemma ev_rec_out_0 : forall a, eval a (nth 0 tg_rec_out (EConst 0))
  = bitsum (bits_at a 23) 64 - a (8%nat, 0%nat).
Proof. intro a. unfold bits_at. cbn [nth tg_rec_out eval bitsum wpow Nat.add]. ring. Qed.
Lemma ev_rec_out_1 : forall a, eval a (nth 1 tg_rec_out (EConst 0))
  = bitsum (bits_at a 87) 64 - a (9%nat, 0%nat).
Proof. intro a. unfold bits_at. cbn [nth tg_rec_out eval bitsum wpow Nat.add]. ring. Qed.
Lemma ev_rec_out_2 : forall a, eval a (nth 2 tg_rec_out (EConst 0))
  = bitsum (bits_at a 151) 64 - a (10%nat, 0%nat).
Proof. intro a. unfold bits_at. cbn [nth tg_rec_out eval bitsum wpow Nat.add]. ring. Qed.
Lemma ev_rec_out_3 : forall a, eval a (nth 3 tg_rec_out (EConst 0))
  = bitsum (bits_at a 215) 64 - a (11%nat, 0%nat).
Proof. intro a. unfold bits_at. cbn [nth tg_rec_out eval bitsum wpow Nat.add]. ring. Qed.
Lemma ev_rec_out_4 : forall a, eval a (nth 4 tg_rec_out (EConst 0))
  = bitsum (bits_at a 279) 64 - a (12%nat, 0%nat).
Proof. intro a. unfold bits_at. cbn [nth tg_rec_out eval bitsum wpow Nat.add]. ring. Qed.
Lemma ev_rec_out_5 : forall a, eval a (nth 5 tg_rec_out (EConst 0))
  = bitsum (bits_at a 343) 64 - a (13%nat, 0%nat).
Proof. intro a. unfold bits_at. cbn [nth tg_rec_out eval bitsum wpow Nat.add]. ring. Qed.
Lemma ev_rec_out_6 : forall a, eval a (nth 6 tg_rec_out (EConst 0))
  = bitsum (bits_at a 407) 64 - a (14%nat, 0%nat).
Proof. intro a. unfold bits_at. cbn [nth tg_rec_out eval bitsum wpow Nat.add]. ring. Qed.
Lemma ev_rec_out_7 : forall a, eval a (nth 7 tg_rec_out (EConst 0))
  = bitsum (bits_at a 471) 64 - a (15%nat, 0%nat).
Proof. intro a. unfold bits_at. cbn [nth tg_rec_out eval bitsum wpow Nat.add]. ring. Qed.
Lemma ev_rec_c_0 : forall a, eval a (nth 0 tg_rec_c (EConst 0))
  = bitsum (bits_at a 535) 66 - a (16%nat, 0%nat).
Proof. intro a. unfold bits_at. cbn [nth tg_rec_c eval bitsum wpow Nat.add]. ring. Qed.
Lemma ev_rec_c_1 : forall a, eval a (nth 1 tg_rec_c (EConst 0))
  = bitsum (bits_at a 601) 66 - a (17%nat, 0%nat).
Proof. intro a. unfold bits_at. cbn [nth tg_rec_c eval bitsum wpow Nat.add]. ring. Qed.
Lemma ev_rec_c_2 : forall a, eval a (nth 2 tg_rec_c (EConst 0))
  = bitsum (bits_at a 667) 66 - a (18%nat, 0%nat).
Proof. intro a. unfold bits_at. cbn [nth tg_rec_c eval bitsum wpow Nat.add]. ring. Qed.
Lemma ev_rec_c_3 : forall a, eval a (nth 3 tg_rec_c (EConst 0))
  = bitsum (bits_at a 733) 66 - a (19%nat, 0%nat).
Proof. intro a. unfold bits_at. cbn [nth tg_rec_c eval bitsum wpow Nat.add]. ring. Qed.
Lemma ev_rec_c_4 : forall a, eval a (nth 4 tg_rec_c (EConst 0))
  = bitsum (bits_at a 799) 66 - a (20%nat, 0%nat).
Proof. intro a. unfold bits_at. cbn [nth tg_rec_c eval bitsum wpow Nat.add]. ring. Qed.
Lemma ev_rec_c_5 : forall a, eval a (nth 5 tg_rec_c (EConst 0))
  = bitsum (bits_at a 865) 66 - a (21%nat, 0%nat).
Proof. intro a. unfold bits_at. cbn [nth tg_rec_c eval bitsum wpow Nat.add]. ring. Qed.

Theorem rng_out : forall a, sat deployed_model a ->
  forall i, (i < 8)%nat -> 0 <= dc a (8 + i) < 18446744073709551616.
Proof.
  intros a Hs i Hi. unfold dc. rewrite <- wpow64_val.
  destruct Hs as [Hg Hc].
  destruct i as [|i].
  { apply (range_from_gate a 23 64 _ (conj Hg Hc)); [ lia | lia | exact wpow64_le_p | ].
    rewrite <- ev_rec_out_0. exact (Hg _ (tg_rec_out_in 0 ltac:(lia))). }
  destruct i as [|i].
  { apply (range_from_gate a 87 64 _ (conj Hg Hc)); [ lia | lia | exact wpow64_le_p | ].
    rewrite <- ev_rec_out_1. exact (Hg _ (tg_rec_out_in 1 ltac:(lia))). }
  destruct i as [|i].
  { apply (range_from_gate a 151 64 _ (conj Hg Hc)); [ lia | lia | exact wpow64_le_p | ].
    rewrite <- ev_rec_out_2. exact (Hg _ (tg_rec_out_in 2 ltac:(lia))). }
  destruct i as [|i].
  { apply (range_from_gate a 215 64 _ (conj Hg Hc)); [ lia | lia | exact wpow64_le_p | ].
    rewrite <- ev_rec_out_3. exact (Hg _ (tg_rec_out_in 3 ltac:(lia))). }
  destruct i as [|i].
  { apply (range_from_gate a 279 64 _ (conj Hg Hc)); [ lia | lia | exact wpow64_le_p | ].
    rewrite <- ev_rec_out_4. exact (Hg _ (tg_rec_out_in 4 ltac:(lia))). }
  destruct i as [|i].
  { apply (range_from_gate a 343 64 _ (conj Hg Hc)); [ lia | lia | exact wpow64_le_p | ].
    rewrite <- ev_rec_out_5. exact (Hg _ (tg_rec_out_in 5 ltac:(lia))). }
  destruct i as [|i].
  { apply (range_from_gate a 407 64 _ (conj Hg Hc)); [ lia | lia | exact wpow64_le_p | ].
    rewrite <- ev_rec_out_6. exact (Hg _ (tg_rec_out_in 6 ltac:(lia))). }
  destruct i as [|i].
  { apply (range_from_gate a 471 64 _ (conj Hg Hc)); [ lia | lia | exact wpow64_le_p | ].
    rewrite <- ev_rec_out_7. exact (Hg _ (tg_rec_out_in 7 ltac:(lia))). }
  lia.
Qed.

Theorem rng_c : forall a, sat deployed_model a ->
  forall i, (i < 6)%nat -> 0 <= cc a i < 73786976294838206464.
Proof.
  intros a Hs i Hi. unfold cc, dc. rewrite <- wpow66_val.
  destruct Hs as [Hg Hc].
  destruct i as [|i].
  { apply (range_from_gate a 535 66 _ (conj Hg Hc)); [ lia | lia | exact wpow66_le_p | ].
    rewrite <- ev_rec_c_0. exact (Hg _ (tg_rec_c_in 0 ltac:(lia))). }
  destruct i as [|i].
  { apply (range_from_gate a 601 66 _ (conj Hg Hc)); [ lia | lia | exact wpow66_le_p | ].
    rewrite <- ev_rec_c_1. exact (Hg _ (tg_rec_c_in 1 ltac:(lia))). }
  destruct i as [|i].
  { apply (range_from_gate a 667 66 _ (conj Hg Hc)); [ lia | lia | exact wpow66_le_p | ].
    rewrite <- ev_rec_c_2. exact (Hg _ (tg_rec_c_in 2 ltac:(lia))). }
  destruct i as [|i].
  { apply (range_from_gate a 733 66 _ (conj Hg Hc)); [ lia | lia | exact wpow66_le_p | ].
    rewrite <- ev_rec_c_3. exact (Hg _ (tg_rec_c_in 3 ltac:(lia))). }
  destruct i as [|i].
  { apply (range_from_gate a 799 66 _ (conj Hg Hc)); [ lia | lia | exact wpow66_le_p | ].
    rewrite <- ev_rec_c_4. exact (Hg _ (tg_rec_c_in 4 ltac:(lia))). }
  destruct i as [|i].
  { apply (range_from_gate a 865 66 _ (conj Hg Hc)); [ lia | lia | exact wpow66_le_p | ].
    rewrite <- ev_rec_c_5. exact (Hg _ (tg_rec_c_in 5 ltac:(lia))). }
  lia.
Qed.

Print Assumptions p_prime.
Print Assumptions p_odd.
Print Assumptions HALF_big.
Print Assumptions dc_range.
Print Assumptions head_is_the_booleanity_bank.
Print Assumptions head_and_tail_exhaust_the_model.
Print Assumptions tail_split_is_a_partition.
Print Assumptions CANON_is_free.
Print Assumptions answer_pins_are_DERIVED.
Print Assumptions every_bit_cell_is_boolean.
Print Assumptions rng_out.
Print Assumptions rng_c.
