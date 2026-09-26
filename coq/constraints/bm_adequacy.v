(* SPDX-License-Identifier: Apache-2.0
   SPDX-FileCopyrightText: 2026 Next Ridge Solutions Ltd

   Completeness (bridge_complete), and soundness and completeness as one theorem: under the input
   assumption, the circuit accepts a triple exactly when the relation does (policy_adequacy_bm; the
   two directions stated separately in policy_adequacy_bm_conj).

   Scope: these results bind the formal (Coq) layer only; the generated constraint model's fidelity to the circuit implementation, and the implementation itself, are outside them. *)

From Coq Require Import ZArith Lia List Znumtheory. Import ListNotations.
Open Scope Z_scope.

Require Import Generated.bm_model_gen.
Require Import Generated.bm_wires_gen.
Require Import Generated.bm_scaffold_gen.
Require Import Constraints.field_order_lift.
Require Import Constraints.range_field_pasta.
Require Import Constraints.bits_kit.
Require Import Constraints.bm_semantic.
Require Import Constraints.bm_model_facts.
Require Import Constraints.bm_soundness.
Require bm_rule.

Definition CARRYC (s o : list Z) (i : nat) : Z :=
  (bm_rule.VAL (firstn (S i) s) - bm_rule.VAL (firstn (S i) o)) / bm_rule.B ^ Z.of_nat (S i).

Lemma CARRYC_exact : forall s o i,
  bm_rule.VAL o = bm_rule.VAL s ->
  bm_rule.VAL (firstn (S i) s) - bm_rule.VAL (firstn (S i) o)
  = bm_rule.B ^ Z.of_nat (S i) * (bm_rule.VAL (skipn (S i) o) - bm_rule.VAL (skipn (S i) s)).
Proof.
  intros s o i Heq.
  pose proof (bm_rule.VAL_firstn_skipn (S i) s) as Hi.
  pose proof (bm_rule.VAL_firstn_skipn (S i) o) as Ho.
  rewrite Heq in Ho. rewrite Z.mul_sub_distr_l. lia.
Qed.

Theorem CARRYC_is_suffix_difference : forall s o i,
  bm_rule.VAL o = bm_rule.VAL s ->
  CARRYC s o i = bm_rule.VAL (skipn (S i) o) - bm_rule.VAL (skipn (S i) s).
Proof.
  intros s o i Heq. unfold CARRYC.
  rewrite (CARRYC_exact s o i Heq), Z.mul_comm.
  apply Z.div_mul. apply bm_rule.B_pow_nonzero.
Qed.

Lemma VAL_skipn_S : forall i v,
  bm_rule.VAL (skipn i v) = nth i v 0 + bm_rule.B * bm_rule.VAL (skipn (S i) v).
Proof.
  induction i as [|i IH]; intro v; destruct v as [|x t].
  - cbn [skipn nth]. rewrite bm_rule.VAL_nil. ring.
  - cbn [skipn nth]. rewrite bm_rule.VAL_cons. ring.
  - cbn [skipn nth]. rewrite bm_rule.VAL_nil. ring.
  - change (skipn (S i) (x :: t)) with (skipn i t).
    change (skipn (S (S i)) (x :: t)) with (skipn (S i) t).
    change (nth (S i) (x :: t) 0) with (nth i t 0). apply IH.
Qed.

Theorem REL_running : forall s o,
  bm_rule.VAL o = bm_rule.VAL s ->
  forall i, nth i s 0 - nth i o 0 = CARRYC s o i * bm_rule.B - prevc (CARRYC s o) i.
Proof.
  intros s o Heq i.
  rewrite (CARRYC_is_suffix_difference s o i Heq).
  pose proof (VAL_skipn_S i s) as Hi. pose proof (VAL_skipn_S i o) as Ho.

  destruct i as [|j]; cbn [prevc].
  - change (skipn 0 s) with s in Hi. change (skipn 0 o) with o in Ho.
    rewrite bm_rule.B_value in *. lia.
  - rewrite (CARRYC_is_suffix_difference s o j Heq).
    rewrite bm_rule.B_value in *. lia.
Qed.

Theorem the_last_carry_is_the_top_limb : forall s o,
  length s = 7%nat -> length o = 8%nat -> bm_rule.VAL o = bm_rule.VAL s ->
  CARRYC s o 6 = nth 7 o 0.
Proof.
  intros s o Hls Hlo Heq.
  rewrite (CARRYC_is_suffix_difference s o 6 Heq).
  rewrite (skipn_all2 s) by (rewrite Hls; lia).
  rewrite (VAL_skipn_S 7 o), (skipn_all2 o) by (rewrite Hlo; lia).
  rewrite !bm_rule.VAL_nil. ring.
Qed.

Lemma VAL_firstn_bound : forall M v n, 0 <= M ->
  (forall m, 0 <= nth m v 0 <= M * (bm_rule.B - 1)) ->
  0 <= bm_rule.VAL (firstn n v) <= M * (bm_rule.B ^ Z.of_nat n - 1).
Proof.
  intros M v n HM Hv. induction n as [|n IH].
  - cbn [firstn Z.of_nat]. rewrite bm_rule.VAL_nil, Z.pow_0_r. lia.
  - rewrite VAL_firstn_S, Nat2Z.inj_succ, Z.pow_succ_r by lia.
    assert (HX : 0 < bm_rule.B ^ Z.of_nat n)
      by (apply Z.pow_pos_nonneg; [ exact bm_rule.B_pos | lia ]).
    set (X := bm_rule.B ^ Z.of_nat n) in *.
    pose proof (Hv n) as Hn. pose proof bm_rule.B_pos.
    assert (H1 : X * nth n v 0 <= X * (M * (bm_rule.B - 1)))
      by (apply Z.mul_le_mono_nonneg_l; lia).
    assert (H2 : 0 <= X * nth n v 0) by (apply Z.mul_nonneg_nonneg; lia).
    replace (M * (bm_rule.B * X - 1)) with (M * (X - 1) + X * (M * (bm_rule.B - 1))) by ring.
    lia.
Qed.

Lemma nth_limb1 : forall v m, Forall bm_rule.limb_ok v -> 0 <= nth m v 0 <= 1 * (bm_rule.B - 1).
Proof. intros v m Hf. pose proof (nth_limb v m Hf). lia. Qed.

Lemma VAL_out_is_VAL_CONV : forall a b out, bm_rule.PRE_bm a b -> bm_rule.REL_bm a b out ->
  bm_rule.VAL out = bm_rule.VAL (CONV a b).
Proof.
  intros a b out [Ha [Hb _]] [_ [_ Hv]]. rewrite Hv. symmetry. apply VAL_CONV; assumption.
Qed.

Theorem carry_bound : forall a b out, bm_rule.PRE_bm a b -> bm_rule.REL_bm a b out ->
  forall k, 0 <= CARRYC (CONV a b) out k < 2 ^ 66.
Proof.
  intros a b out Hpre HR k.
  pose proof (VAL_out_is_VAL_CONV a b out Hpre HR) as Hvs.
  destruct HR as [_ [Hf _]].
  pose proof (CARRYC_exact (CONV a b) out k Hvs) as HE.
  rewrite (CARRYC_is_suffix_difference (CONV a b) out k Hvs).
  set (c := bm_rule.VAL (skipn (S k) out) - bm_rule.VAL (skipn (S k) (CONV a b))) in *.
  assert (HX : 0 < bm_rule.B ^ Z.of_nat (S k))
    by (apply Z.pow_pos_nonneg; [ exact bm_rule.B_pos | lia ]).
  pose proof (VAL_firstn_bound (4 * (bm_rule.B - 1)) (CONV a b) (S k)
                ltac:(rewrite bm_rule.B_value; lia) (CONV_elem_bound a b Hpre)) as Hs.
  pose proof (VAL_firstn_bound 1 out (S k) ltac:(lia) (fun m => nth_limb1 out m Hf)) as Ho.
  set (X := bm_rule.B ^ Z.of_nat (S k)) in *.
  set (Ps := bm_rule.VAL (firstn (S k) (CONV a b))) in *.
  set (Po := bm_rule.VAL (firstn (S k) out)) in *.
  pose proof bm_rule.B_pos as HB0.
  assert (Hc0 : 0 <= c).
  { destruct (Z.le_gt_cases 0 c) as [H|H]; [ exact H | exfalso ].
    pose proof (mul_le_neg X c HX ltac:(lia)). nia. }
  assert (Hc1 : c < 4 * (bm_rule.B - 1)).
  { destruct (Z.lt_ge_cases c (4 * (bm_rule.B - 1))) as [H|H]; [ exact H | exfalso ].
    assert (X * (4 * (bm_rule.B - 1)) <= X * c) by (apply Z.mul_le_mono_nonneg_l; lia).
    rewrite bm_rule.B_value in *. nia. }
  rewrite bm_rule.B_value in Hc1. split; [ exact Hc0 | ]. lia.
Qed.

Lemma bitsum_ext : forall n (f g : nat -> Z),
  (forall j, (j < n)%nat -> f j = g j) -> bitsum f n = bitsum g n.
Proof.
  induction n as [|n IH]; intros f g H; [ reflexivity | ].
  cbn [bitsum]. rewrite (IH f g) by (intros j Hj; apply H; lia).
  rewrite (H n) by lia. reflexivity.
Qed.

Lemma bitsum66_bits_of : forall d, 0 <= d < 73786976294838206464 ->
  bitsum (bits_of d) 66 = d.
Proof.
  intros d [Hlo Hhi]. rewrite (bitsum_bits_of 66 d Hlo).
  rewrite wpow66_val. apply Z.mod_small. lia.
Qed.

Lemma in_firstn_or_skipn : forall (A : Type) (n : nat) (l : list A) (x : A),
  In x l -> In x (firstn n l) \/ In x (skipn n l).
Proof. intros A n l x H. rewrite <- (firstn_skipn n l) in H. apply in_app_or. exact H. Qed.

Lemma nat_split : forall k q r, (0 < k)%nat -> (r < k)%nat ->
  ((q * k + r) / k = q)%nat /\ ((q * k + r) mod k = r)%nat.
Proof.
  intros k q r Hk Hr.
  assert (Hd : ((q * k + r) / k = q)%nat).
  { rewrite Nat.div_add_l by lia. rewrite (Nat.div_small r k Hr). lia. }
  split; [ exact Hd | ].
  pose proof (Nat.div_mod_eq (q * k + r) k) as H. rewrite Hd in H. lia.
Qed.

Lemma list_four : forall (v : list Z), length v = 4%nat ->
  v = [nth 0 v 0; nth 1 v 0; nth 2 v 0; nth 3 v 0].
Proof.
  intros v Hl. destruct v as [|a [|b [|c [|d [|e v]]]]]; cbn [length] in Hl; try lia.
  reflexivity.
Qed.

Lemma list_eight : forall (v : list Z), length v = 8%nat ->
  v = [nth 0 v 0; nth 1 v 0; nth 2 v 0; nth 3 v 0; nth 4 v 0; nth 5 v 0; nth 6 v 0; nth 7 v 0].
Proof.
  intros v Hl. destruct v as [|a [|b [|c [|d [|e [|f [|g [|h [|i v]]]]]]]]]; cbn [length] in Hl; try lia.
  reflexivity.
Qed.

Lemma B64_lt_p : 18446744073709551616 < p.
Proof. apply Z.ltb_lt. vm_compute. reflexivity. Qed.

Definition cellv (xs ys outs cs : list Z) (c : nat) : Z :=
  if (c <? 4)%nat then nth c xs 0
  else if (c <? 8)%nat then nth (c - 4) ys 0
  else if (c <? 16)%nat then nth (c - 8) outs 0
  else if (c <? 23)%nat then nth (c - 16) cs 0
  else if (c <? 535)%nat then bits_of (nth ((c - 23) / 64) outs 0) ((c - 23) mod 64)
  else if (c <? 931)%nat then bits_of (nth ((c - 535) / 66) cs 0) ((c - 535) mod 66)
  else 0.

Definition mkW (xs ys outs cs : list Z) : Assignment :=
  fun cl => if Nat.eqb (fst cl) 2000 then nth (snd cl) outs 0
            else if Nat.eqb (snd cl) 0 then cellv xs ys outs cs (fst cl) else 0.

Section Builder.
Variables xs ys outs cs : list Z.

Lemma mkW_cell : forall c, (c < 931)%nat -> mkW xs ys outs cs (c, 0%nat) = cellv xs ys outs cs c.
Proof.
  intros c Hc. unfold mkW. cbn [fst snd].
  rewrite (proj2 (Nat.eqb_neq c 2000) ltac:(lia)). reflexivity.
Qed.

Lemma mkW_a : forall c, (c < 4)%nat -> mkW xs ys outs cs (c, 0%nat) = nth c xs 0.
Proof.
  intros c Hc. rewrite mkW_cell by lia. unfold cellv.
  rewrite (proj2 (Nat.ltb_lt c 4) Hc). reflexivity.
Qed.

Lemma mkW_b : forall c, (4 <= c < 8)%nat -> mkW xs ys outs cs (c, 0%nat) = nth (c - 4) ys 0.
Proof.
  intros c Hc. rewrite mkW_cell by lia. unfold cellv.
  rewrite (proj2 (Nat.ltb_ge c 4) ltac:(lia)), (proj2 (Nat.ltb_lt c 8) ltac:(lia)). reflexivity.
Qed.

Lemma mkW_out : forall c, (8 <= c < 16)%nat -> mkW xs ys outs cs (c, 0%nat) = nth (c - 8) outs 0.
Proof.
  intros c Hc. rewrite mkW_cell by lia. unfold cellv.
  rewrite (proj2 (Nat.ltb_ge c 4) ltac:(lia)), (proj2 (Nat.ltb_ge c 8) ltac:(lia)),
          (proj2 (Nat.ltb_lt c 16) ltac:(lia)). reflexivity.
Qed.

Lemma mkW_cc : forall c, (16 <= c < 23)%nat -> mkW xs ys outs cs (c, 0%nat) = nth (c - 16) cs 0.
Proof.
  intros c Hc. rewrite mkW_cell by lia. unfold cellv.
  rewrite (proj2 (Nat.ltb_ge c 4) ltac:(lia)), (proj2 (Nat.ltb_ge c 8) ltac:(lia)),
          (proj2 (Nat.ltb_ge c 16) ltac:(lia)), (proj2 (Nat.ltb_lt c 23) ltac:(lia)). reflexivity.
Qed.

Lemma mkW_pub : forall j, mkW xs ys outs cs (2000%nat, j) = nth j outs 0.
Proof. intro j. reflexivity. Qed.

Lemma mkW_bool : forall c, (23 <= c < 931)%nat ->
  mkW xs ys outs cs (c, 0%nat) = 0 \/ mkW xs ys outs cs (c, 0%nat) = 1.
Proof.
  intros c Hc. rewrite mkW_cell by lia. unfold cellv.
  rewrite (proj2 (Nat.ltb_ge c 4) ltac:(lia)), (proj2 (Nat.ltb_ge c 8) ltac:(lia)),
          (proj2 (Nat.ltb_ge c 16) ltac:(lia)), (proj2 (Nat.ltb_ge c 23) ltac:(lia)).
  destruct (c <? 535)%nat; [ apply bits_of_bool | ].
  rewrite (proj2 (Nat.ltb_lt c 931) ltac:(lia)). apply bits_of_bool.
Qed.

Lemma bat_out : forall i j, (i < 8)%nat -> (j < 64)%nat ->
  bits_at (mkW xs ys outs cs) (23 + 64 * i)%nat j = bits_of (nth i outs 0) j.
Proof.
  intros i j Hi Hj. unfold bits_at. rewrite mkW_cell by lia. unfold cellv.
  rewrite (proj2 (Nat.ltb_ge (23 + 64 * i + j) 4) ltac:(lia)),
          (proj2 (Nat.ltb_ge (23 + 64 * i + j) 8) ltac:(lia)),
          (proj2 (Nat.ltb_ge (23 + 64 * i + j) 16) ltac:(lia)),
          (proj2 (Nat.ltb_ge (23 + 64 * i + j) 23) ltac:(lia)),
          (proj2 (Nat.ltb_lt (23 + 64 * i + j) 535) ltac:(lia)).
  replace (23 + 64 * i + j - 23)%nat with (i * 64 + j)%nat by lia.
  destruct (nat_split 64 i j ltac:(lia) Hj) as [Hd Hm]. rewrite Hd, Hm. reflexivity.
Qed.

Lemma bat_c : forall i j, (i < 6)%nat -> (j < 66)%nat ->
  bits_at (mkW xs ys outs cs) (535 + 66 * i)%nat j = bits_of (nth i cs 0) j.
Proof.
  intros i j Hi Hj. unfold bits_at. rewrite mkW_cell by lia. unfold cellv.
  rewrite (proj2 (Nat.ltb_ge (535 + 66 * i + j) 4) ltac:(lia)),
          (proj2 (Nat.ltb_ge (535 + 66 * i + j) 8) ltac:(lia)),
          (proj2 (Nat.ltb_ge (535 + 66 * i + j) 16) ltac:(lia)),
          (proj2 (Nat.ltb_ge (535 + 66 * i + j) 23) ltac:(lia)),
          (proj2 (Nat.ltb_ge (535 + 66 * i + j) 535) ltac:(lia)),
          (proj2 (Nat.ltb_lt (535 + 66 * i + j) 931) ltac:(lia)).
  replace (535 + 66 * i + j - 535)%nat with (i * 66 + j)%nat by lia.
  destruct (nat_split 66 i j ltac:(lia) Hj) as [Hd Hm]. rewrite Hd, Hm. reflexivity.
Qed.

Lemma g_bool : forall j, (j < 908)%nat -> gate_holds (mkW xs ys outs cs) (bool_gate (23 + j)%nat).
Proof.
  intros j Hj. unfold gate_holds, bool_gate. cbn [eval].
  destruct (mkW_bool (23 + j)%nat ltac:(lia)) as [E|E]; rewrite E;
    [ replace (0 * (0 - 1)) with 0 by ring | replace (1 * (1 - 1)) with 0 by ring ];
    apply Zmod_0_l.
Qed.

Theorem mkW_copies_hold : copy_holds (mkW xs ys outs cs) deployed_copy.
Proof.
  intros e Hin. cbn [deployed_copy In] in Hin.
  repeat (destruct Hin as [<-|Hin]; [ cbn [fst snd]; rewrite mkW_out by lia; reflexivity | ]).
  destruct Hin.
Qed.

End Builder.

Definition carries_of (a b out : list Z) : list Z :=
  map (CARRYC (CONV a b) out) (seq 0 7).

Definition ASG (a b out : list Z) : Assignment := mkW a b out (carries_of a b out).

Lemma nth_carries : forall a b out k, (k < 7)%nat ->
  nth k (carries_of a b out) 0 = CARRYC (CONV a b) out k.
Proof. intros a b out k Hk. do 7 (destruct k as [|k]; [ reflexivity | ]). lia. Qed.

Section Witness.
Variables a b out : list Z.

Lemma g_rec_out : bm_rule.REL_bm a b out ->
  forall k, (k < 8)%nat -> gate_holds (ASG a b out) (nth k tg_rec_out (EConst 0)).
Proof.
  intros [Hlo [Hf _]] k Hk. unfold gate_holds, ASG.
  destruct k as [|k].
  { rewrite ev_rec_out_0.
    rewrite (bitsum_ext 64 (bits_at (mkW a b out (carries_of a b out)) 23) (bits_of (nth 0 out 0))
              (fun j Hj => bat_out a b out (carries_of a b out) 0 j ltac:(lia) Hj)).
    rewrite bitsum64_bits_of by (pose proof (nth_limb out 0 Hf) as Hn; rewrite bm_rule.B_value in Hn; lia).
    rewrite (mkW_out a b out (carries_of a b out) 8) by lia. cbn [Nat.sub].
    rewrite Z.sub_diag. apply Zmod_0_l. }
  destruct k as [|k].
  { rewrite ev_rec_out_1.
    rewrite (bitsum_ext 64 (bits_at (mkW a b out (carries_of a b out)) 87) (bits_of (nth 1 out 0))
              (fun j Hj => bat_out a b out (carries_of a b out) 1 j ltac:(lia) Hj)).
    rewrite bitsum64_bits_of by (pose proof (nth_limb out 1 Hf) as Hn; rewrite bm_rule.B_value in Hn; lia).
    rewrite (mkW_out a b out (carries_of a b out) 9) by lia. cbn [Nat.sub].
    rewrite Z.sub_diag. apply Zmod_0_l. }
  destruct k as [|k].
  { rewrite ev_rec_out_2.
    rewrite (bitsum_ext 64 (bits_at (mkW a b out (carries_of a b out)) 151) (bits_of (nth 2 out 0))
              (fun j Hj => bat_out a b out (carries_of a b out) 2 j ltac:(lia) Hj)).
    rewrite bitsum64_bits_of by (pose proof (nth_limb out 2 Hf) as Hn; rewrite bm_rule.B_value in Hn; lia).
    rewrite (mkW_out a b out (carries_of a b out) 10) by lia. cbn [Nat.sub].
    rewrite Z.sub_diag. apply Zmod_0_l. }
  destruct k as [|k].
  { rewrite ev_rec_out_3.
    rewrite (bitsum_ext 64 (bits_at (mkW a b out (carries_of a b out)) 215) (bits_of (nth 3 out 0))
              (fun j Hj => bat_out a b out (carries_of a b out) 3 j ltac:(lia) Hj)).
    rewrite bitsum64_bits_of by (pose proof (nth_limb out 3 Hf) as Hn; rewrite bm_rule.B_value in Hn; lia).
    rewrite (mkW_out a b out (carries_of a b out) 11) by lia. cbn [Nat.sub].
    rewrite Z.sub_diag. apply Zmod_0_l. }
  destruct k as [|k].
  { rewrite ev_rec_out_4.
    rewrite (bitsum_ext 64 (bits_at (mkW a b out (carries_of a b out)) 279) (bits_of (nth 4 out 0))
              (fun j Hj => bat_out a b out (carries_of a b out) 4 j ltac:(lia) Hj)).
    rewrite bitsum64_bits_of by (pose proof (nth_limb out 4 Hf) as Hn; rewrite bm_rule.B_value in Hn; lia).
    rewrite (mkW_out a b out (carries_of a b out) 12) by lia. cbn [Nat.sub].
    rewrite Z.sub_diag. apply Zmod_0_l. }
  destruct k as [|k].
  { rewrite ev_rec_out_5.
    rewrite (bitsum_ext 64 (bits_at (mkW a b out (carries_of a b out)) 343) (bits_of (nth 5 out 0))
              (fun j Hj => bat_out a b out (carries_of a b out) 5 j ltac:(lia) Hj)).
    rewrite bitsum64_bits_of by (pose proof (nth_limb out 5 Hf) as Hn; rewrite bm_rule.B_value in Hn; lia).
    rewrite (mkW_out a b out (carries_of a b out) 13) by lia. cbn [Nat.sub].
    rewrite Z.sub_diag. apply Zmod_0_l. }
  destruct k as [|k].
  { rewrite ev_rec_out_6.
    rewrite (bitsum_ext 64 (bits_at (mkW a b out (carries_of a b out)) 407) (bits_of (nth 6 out 0))
              (fun j Hj => bat_out a b out (carries_of a b out) 6 j ltac:(lia) Hj)).
    rewrite bitsum64_bits_of by (pose proof (nth_limb out 6 Hf) as Hn; rewrite bm_rule.B_value in Hn; lia).
    rewrite (mkW_out a b out (carries_of a b out) 14) by lia. cbn [Nat.sub].
    rewrite Z.sub_diag. apply Zmod_0_l. }
  destruct k as [|k].
  { rewrite ev_rec_out_7.
    rewrite (bitsum_ext 64 (bits_at (mkW a b out (carries_of a b out)) 471) (bits_of (nth 7 out 0))
              (fun j Hj => bat_out a b out (carries_of a b out) 7 j ltac:(lia) Hj)).
    rewrite bitsum64_bits_of by (pose proof (nth_limb out 7 Hf) as Hn; rewrite bm_rule.B_value in Hn; lia).
    rewrite (mkW_out a b out (carries_of a b out) 15) by lia. cbn [Nat.sub].
    rewrite Z.sub_diag. apply Zmod_0_l. }
  lia.
Qed.

Lemma g_rec_c : bm_rule.PRE_bm a b -> bm_rule.REL_bm a b out ->
  forall k, (k < 6)%nat -> gate_holds (ASG a b out) (nth k tg_rec_c (EConst 0)).
Proof.
  intros Hpre HR k Hk. unfold gate_holds, ASG.
  destruct k as [|k].
  { rewrite ev_rec_c_0.
    rewrite (bitsum_ext 66 (bits_at (mkW a b out (carries_of a b out)) 535) (bits_of (nth 0 (carries_of a b out) 0))
              (fun j Hj => bat_c a b out (carries_of a b out) 0 j ltac:(lia) Hj)).
    rewrite (nth_carries a b out 0) by lia.
    rewrite bitsum66_bits_of by (pose proof (carry_bound a b out Hpre HR 0%nat) as Hcb; lia).
    rewrite (mkW_cc a b out (carries_of a b out) 16) by lia. cbn [Nat.sub].
    rewrite (nth_carries a b out 0) by lia.
    rewrite Z.sub_diag. apply Zmod_0_l. }
  destruct k as [|k].
  { rewrite ev_rec_c_1.
    rewrite (bitsum_ext 66 (bits_at (mkW a b out (carries_of a b out)) 601) (bits_of (nth 1 (carries_of a b out) 0))
              (fun j Hj => bat_c a b out (carries_of a b out) 1 j ltac:(lia) Hj)).
    rewrite (nth_carries a b out 1) by lia.
    rewrite bitsum66_bits_of by (pose proof (carry_bound a b out Hpre HR 1%nat) as Hcb; lia).
    rewrite (mkW_cc a b out (carries_of a b out) 17) by lia. cbn [Nat.sub].
    rewrite (nth_carries a b out 1) by lia.
    rewrite Z.sub_diag. apply Zmod_0_l. }
  destruct k as [|k].
  { rewrite ev_rec_c_2.
    rewrite (bitsum_ext 66 (bits_at (mkW a b out (carries_of a b out)) 667) (bits_of (nth 2 (carries_of a b out) 0))
              (fun j Hj => bat_c a b out (carries_of a b out) 2 j ltac:(lia) Hj)).
    rewrite (nth_carries a b out 2) by lia.
    rewrite bitsum66_bits_of by (pose proof (carry_bound a b out Hpre HR 2%nat) as Hcb; lia).
    rewrite (mkW_cc a b out (carries_of a b out) 18) by lia. cbn [Nat.sub].
    rewrite (nth_carries a b out 2) by lia.
    rewrite Z.sub_diag. apply Zmod_0_l. }
  destruct k as [|k].
  { rewrite ev_rec_c_3.
    rewrite (bitsum_ext 66 (bits_at (mkW a b out (carries_of a b out)) 733) (bits_of (nth 3 (carries_of a b out) 0))
              (fun j Hj => bat_c a b out (carries_of a b out) 3 j ltac:(lia) Hj)).
    rewrite (nth_carries a b out 3) by lia.
    rewrite bitsum66_bits_of by (pose proof (carry_bound a b out Hpre HR 3%nat) as Hcb; lia).
    rewrite (mkW_cc a b out (carries_of a b out) 19) by lia. cbn [Nat.sub].
    rewrite (nth_carries a b out 3) by lia.
    rewrite Z.sub_diag. apply Zmod_0_l. }
  destruct k as [|k].
  { rewrite ev_rec_c_4.
    rewrite (bitsum_ext 66 (bits_at (mkW a b out (carries_of a b out)) 799) (bits_of (nth 4 (carries_of a b out) 0))
              (fun j Hj => bat_c a b out (carries_of a b out) 4 j ltac:(lia) Hj)).
    rewrite (nth_carries a b out 4) by lia.
    rewrite bitsum66_bits_of by (pose proof (carry_bound a b out Hpre HR 4%nat) as Hcb; lia).
    rewrite (mkW_cc a b out (carries_of a b out) 20) by lia. cbn [Nat.sub].
    rewrite (nth_carries a b out 4) by lia.
    rewrite Z.sub_diag. apply Zmod_0_l. }
  destruct k as [|k].
  { rewrite ev_rec_c_5.
    rewrite (bitsum_ext 66 (bits_at (mkW a b out (carries_of a b out)) 865) (bits_of (nth 5 (carries_of a b out) 0))
              (fun j Hj => bat_c a b out (carries_of a b out) 5 j ltac:(lia) Hj)).
    rewrite (nth_carries a b out 5) by lia.
    rewrite bitsum66_bits_of by (pose proof (carry_bound a b out Hpre HR 5%nat) as Hcb; lia).
    rewrite (mkW_cc a b out (carries_of a b out) 21) by lia. cbn [Nat.sub].
    rewrite (nth_carries a b out 5) by lia.
    rewrite Z.sub_diag. apply Zmod_0_l. }
  lia.
Qed.

Lemma g_chain : bm_rule.PRE_bm a b -> bm_rule.REL_bm a b out ->
  forall k, (k < 7)%nat -> gate_holds (ASG a b out) (nth k tg_chain (EConst 0)).
Proof.
  intros Hpre HR k Hk. unfold gate_holds, ASG.
  pose proof (REL_running (CONV a b) out (VAL_out_is_VAL_CONV a b out Hpre HR)) as HRR.
  destruct k as [|k].
  { rewrite ev_chain_0. unfold RW0.
    rewrite (mkW_a a b out (carries_of a b out) 0) by lia.
    rewrite (mkW_b a b out (carries_of a b out) 4) by lia.
    rewrite (mkW_out a b out (carries_of a b out) 8) by lia.
    rewrite (mkW_cc a b out (carries_of a b out) 16) by lia.
    cbn [Nat.sub]. rewrite !nth_carries by lia.
    pose proof (HRR 0%nat) as H. cbn [prevc] in H.
    change (nth 0 (CONV a b) 0) with (nth 0 a 0 * nth 0 b 0) in H.
    rewrite bm_rule.B_value in H.
    replace (_ - _) with 0 by lia. apply Zmod_0_l. }
  destruct k as [|k].
  { rewrite ev_chain_1. unfold RW1.
    rewrite (mkW_a a b out (carries_of a b out) 0) by lia.
    rewrite (mkW_a a b out (carries_of a b out) 1) by lia.
    rewrite (mkW_b a b out (carries_of a b out) 5) by lia.
    rewrite (mkW_b a b out (carries_of a b out) 4) by lia.
    rewrite (mkW_out a b out (carries_of a b out) 9) by lia.
    rewrite (mkW_cc a b out (carries_of a b out) 16) by lia.
    rewrite (mkW_cc a b out (carries_of a b out) 17) by lia.
    cbn [Nat.sub]. rewrite !nth_carries by lia.
    pose proof (HRR 1%nat) as H. cbn [prevc] in H.
    change (nth 1 (CONV a b) 0) with (nth 0 a 0 * nth 1 b 0 + nth 1 a 0 * nth 0 b 0) in H.
    rewrite bm_rule.B_value in H.
    replace (_ - _) with 0 by lia. apply Zmod_0_l. }
  destruct k as [|k].
  { rewrite ev_chain_2. unfold RW2.
    rewrite (mkW_a a b out (carries_of a b out) 0) by lia.
    rewrite (mkW_a a b out (carries_of a b out) 1) by lia.
    rewrite (mkW_a a b out (carries_of a b out) 2) by lia.
    rewrite (mkW_b a b out (carries_of a b out) 6) by lia.
    rewrite (mkW_b a b out (carries_of a b out) 5) by lia.
    rewrite (mkW_b a b out (carries_of a b out) 4) by lia.
    rewrite (mkW_out a b out (carries_of a b out) 10) by lia.
    rewrite (mkW_cc a b out (carries_of a b out) 17) by lia.
    rewrite (mkW_cc a b out (carries_of a b out) 18) by lia.
    cbn [Nat.sub]. rewrite !nth_carries by lia.
    pose proof (HRR 2%nat) as H. cbn [prevc] in H.
    change (nth 2 (CONV a b) 0) with (nth 0 a 0 * nth 2 b 0 + nth 1 a 0 * nth 1 b 0 + nth 2 a 0 * nth 0 b 0) in H.
    rewrite bm_rule.B_value in H.
    replace (_ - _) with 0 by lia. apply Zmod_0_l. }
  destruct k as [|k].
  { rewrite ev_chain_3. unfold RW3.
    rewrite (mkW_a a b out (carries_of a b out) 0) by lia.
    rewrite (mkW_a a b out (carries_of a b out) 1) by lia.
    rewrite (mkW_a a b out (carries_of a b out) 2) by lia.
    rewrite (mkW_a a b out (carries_of a b out) 3) by lia.
    rewrite (mkW_b a b out (carries_of a b out) 7) by lia.
    rewrite (mkW_b a b out (carries_of a b out) 6) by lia.
    rewrite (mkW_b a b out (carries_of a b out) 5) by lia.
    rewrite (mkW_b a b out (carries_of a b out) 4) by lia.
    rewrite (mkW_out a b out (carries_of a b out) 11) by lia.
    rewrite (mkW_cc a b out (carries_of a b out) 18) by lia.
    rewrite (mkW_cc a b out (carries_of a b out) 19) by lia.
    cbn [Nat.sub]. rewrite !nth_carries by lia.
    pose proof (HRR 3%nat) as H. cbn [prevc] in H.
    change (nth 3 (CONV a b) 0) with (nth 0 a 0 * nth 3 b 0 + nth 1 a 0 * nth 2 b 0 + nth 2 a 0 * nth 1 b 0 + nth 3 a 0 * nth 0 b 0) in H.
    rewrite bm_rule.B_value in H.
    replace (_ - _) with 0 by lia. apply Zmod_0_l. }
  destruct k as [|k].
  { rewrite ev_chain_4. unfold RW4.
    rewrite (mkW_a a b out (carries_of a b out) 1) by lia.
    rewrite (mkW_a a b out (carries_of a b out) 2) by lia.
    rewrite (mkW_a a b out (carries_of a b out) 3) by lia.
    rewrite (mkW_b a b out (carries_of a b out) 7) by lia.
    rewrite (mkW_b a b out (carries_of a b out) 6) by lia.
    rewrite (mkW_b a b out (carries_of a b out) 5) by lia.
    rewrite (mkW_out a b out (carries_of a b out) 12) by lia.
    rewrite (mkW_cc a b out (carries_of a b out) 19) by lia.
    rewrite (mkW_cc a b out (carries_of a b out) 20) by lia.
    cbn [Nat.sub]. rewrite !nth_carries by lia.
    pose proof (HRR 4%nat) as H. cbn [prevc] in H.
    change (nth 4 (CONV a b) 0) with (nth 1 a 0 * nth 3 b 0 + nth 2 a 0 * nth 2 b 0 + nth 3 a 0 * nth 1 b 0) in H.
    rewrite bm_rule.B_value in H.
    replace (_ - _) with 0 by lia. apply Zmod_0_l. }
  destruct k as [|k].
  { rewrite ev_chain_5. unfold RW5.
    rewrite (mkW_a a b out (carries_of a b out) 2) by lia.
    rewrite (mkW_a a b out (carries_of a b out) 3) by lia.
    rewrite (mkW_b a b out (carries_of a b out) 7) by lia.
    rewrite (mkW_b a b out (carries_of a b out) 6) by lia.
    rewrite (mkW_out a b out (carries_of a b out) 13) by lia.
    rewrite (mkW_cc a b out (carries_of a b out) 20) by lia.
    rewrite (mkW_cc a b out (carries_of a b out) 21) by lia.
    cbn [Nat.sub]. rewrite !nth_carries by lia.
    pose proof (HRR 5%nat) as H. cbn [prevc] in H.
    change (nth 5 (CONV a b) 0) with (nth 2 a 0 * nth 3 b 0 + nth 3 a 0 * nth 2 b 0) in H.
    rewrite bm_rule.B_value in H.
    replace (_ - _) with 0 by lia. apply Zmod_0_l. }
  destruct k as [|k].
  { rewrite ev_chain_6. unfold RW6.
    rewrite (mkW_a a b out (carries_of a b out) 3) by lia.
    rewrite (mkW_b a b out (carries_of a b out) 7) by lia.
    rewrite (mkW_out a b out (carries_of a b out) 14) by lia.
    rewrite (mkW_cc a b out (carries_of a b out) 21) by lia.
    rewrite (mkW_cc a b out (carries_of a b out) 22) by lia.
    cbn [Nat.sub]. rewrite !nth_carries by lia.
    pose proof (HRR 6%nat) as H. cbn [prevc] in H.
    change (nth 6 (CONV a b) 0) with (nth 3 a 0 * nth 3 b 0) in H.
    rewrite bm_rule.B_value in H.
    replace (_ - _) with 0 by lia. apply Zmod_0_l. }
  lia.
Qed.

Lemma g_end : bm_rule.PRE_bm a b -> bm_rule.REL_bm a b out ->
  gate_holds (ASG a b out) (nth 0 tg_end (EConst 0)).
Proof.
  intros Hpre HR. pose proof (VAL_out_is_VAL_CONV a b out Hpre HR) as Hvs.
  destruct HR as [Hlo _]. unfold gate_holds, ASG.
  rewrite ev_end. unfold RWEND.
  rewrite (mkW_cc a b out (carries_of a b out) 22) by lia.
  rewrite (mkW_out a b out (carries_of a b out) 15) by lia.
  cbn [Nat.sub]. rewrite nth_carries by lia.
  rewrite (the_last_carry_is_the_top_limb (CONV a b) out (CONV_length a b) Hlo Hvs).
  rewrite Z.sub_diag. apply Zmod_0_l.
Qed.

Theorem all_gates_hold : bm_rule.PRE_bm a b -> bm_rule.REL_bm a b out ->
  gates_hold (ASG a b out) deployed_gates.
Proof.
  intros Hpre HR g Hin.
  destruct (in_firstn_or_skipn _ 908 deployed_gates g Hin) as [Hh|Ht].
  - rewrite head_is_the_booleanity_bank in Hh.
    apply in_map_iff in Hh. destruct Hh as [j [Hj Hseq]].
    apply in_seq in Hseq. subst g. apply g_bool. lia.
  - change (skipn 908 deployed_gates) with tail_gates in Ht.
    rewrite <- tail_split_is_a_partition in Ht.
    repeat (apply in_app_or in Ht; destruct Ht as [Ht|Ht]).
    + apply (In_nth _ _ (EConst 0)) in Ht. destruct Ht as [k [Hk Hg]].
      rewrite tg_rec_out_len in Hk. subst g. apply g_rec_out; assumption.
    + apply (In_nth _ _ (EConst 0)) in Ht. destruct Ht as [k [Hk Hg]].
      rewrite tg_rec_c_len in Hk. subst g. apply g_rec_c; assumption.
    + apply (In_nth _ _ (EConst 0)) in Ht. destruct Ht as [k [Hk Hg]].
      rewrite tg_chain_len in Hk. subst g. apply g_chain; assumption.
    + apply (In_nth _ _ (EConst 0)) in Ht. destruct Ht as [k [Hk Hg]].
      rewrite tg_end_len in Hk. assert (k = 0%nat) by lia. subst k g.
      apply g_end; assumption.
Qed.

Theorem ASG_sat : bm_rule.PRE_bm a b -> bm_rule.REL_bm a b out ->
  sat deployed_model (ASG a b out).
Proof.
  intros Hpre HR. split; [ exact (all_gates_hold Hpre HR) | apply mkW_copies_hold ].
Qed.

Lemma canon_small : forall x, 0 <= x <= bm_rule.B - 1 -> x mod p = x.
Proof.
  intros x Hx. apply Z.mod_small. pose proof B64_lt_p. rewrite bm_rule.B_value in Hx. lia.
Qed.

Lemma decode_a : bm_rule.PRE_bm a b -> a_l (ASG a b out) = a.
Proof.
  intros [Ha [_ [Fa _]]].
  unfold a_l, dc, ASG.
  rewrite !(mkW_a a b out (carries_of a b out)) by lia.
  rewrite !canon_small by (apply nth_limb; exact Fa).
  symmetry. apply list_four. exact Ha.
Qed.

Lemma decode_b : bm_rule.PRE_bm a b -> b_l (ASG a b out) = b.
Proof.
  intros [_ [Hb [_ Fb]]].
  unfold b_l, dc, ASG.
  rewrite !(mkW_b a b out (carries_of a b out)) by lia. cbn [Nat.sub].
  rewrite !canon_small by (apply nth_limb; exact Fb).
  symmetry. apply list_four. exact Hb.
Qed.

Lemma decode_out : bm_rule.REL_bm a b out -> out_l (ASG a b out) = out.
Proof.
  intros [Hlo [Hf _]].
  unfold out_l, dc, ASG.
  rewrite !(mkW_out a b out (carries_of a b out)) by lia. cbn [Nat.sub].
  rewrite !canon_small by (apply nth_limb; exact Hf).
  symmetry. apply list_eight. exact Hlo.
Qed.

End Witness.

(* Completeness: for every triple satisfying the input assumption and the relation, there is a
   filling the circuit accepts that reads back as exactly that triple. *)
Theorem bridge_complete : forall a b out,
  bm_rule.PRE_bm a b ->
  bm_rule.REL_bm a b out ->
  exists al, sat deployed_model al /\ CANON_bm al
             /\ a_l al = a /\ b_l al = b /\ out_l al = out.
Proof.
  intros a b out Hpre HR. exists (ASG a b out).
  split; [ exact (ASG_sat a b out Hpre HR) | ].
  split; [ apply CANON_is_free | ].
  split; [ exact (decode_a a b out Hpre) | ].
  split; [ exact (decode_b a b out Hpre) | exact (decode_out a b out HR) ].
Qed.

Definition accepts_bm (a b out : list Z) : Prop :=
  exists al, sat deployed_model al /\ CANON_bm al
             /\ a_l al = a /\ b_l al = b /\ out_l al = out.

(* Soundness and completeness as one theorem, for inputs satisfying the input assumption. *)
Theorem policy_adequacy_bm : bm_rule.adequate accepts_bm.
Proof.
  intros a b out Hpre. split.
  - intros [al [Hs [Hc [Ha [Hb Ho]]]]]. subst a b out.
    exact (bridge_sound al Hs Hc Hpre).
  - intros HR. exact (bridge_complete a b out Hpre HR).
Qed.

Theorem policy_adequacy_bm_conj :
  (forall al, sat deployed_model al -> CANON_bm al -> bm_rule.PRE_bm (a_l al) (b_l al) ->
              bm_rule.REL_bm (a_l al) (b_l al) (out_l al))
  /\
  (forall a b out, bm_rule.PRE_bm a b -> bm_rule.REL_bm a b out ->
     exists al, sat deployed_model al /\ CANON_bm al
                /\ a_l al = a /\ b_l al = b /\ out_l al = out).
Proof. split; [ exact bridge_sound | exact bridge_complete ]. Qed.

Theorem completeness_hypothesis_is_INHABITED :
  bm_rule.PRE_bm bm_rule.CORNER bm_rule.CORNER
  /\ bm_rule.REL_bm bm_rule.CORNER bm_rule.CORNER bm_rule.CORNER_OUT.
Proof. split; [ exact bm_rule.corner_pre | exact bm_rule.corner_rel ]. Qed.

Theorem the_corner_is_ACCEPTED : accepts_bm bm_rule.CORNER bm_rule.CORNER bm_rule.CORNER_OUT.
Proof. apply policy_adequacy_bm; [ exact bm_rule.corner_pre | exact bm_rule.corner_rel ]. Qed.

Theorem the_diag_row_is_ACCEPTED : accepts_bm bm_rule.DIAG_A bm_rule.DIAG_A bm_rule.DIAG_OUT.
Proof. apply policy_adequacy_bm; [ exact bm_rule.diag_row_pre | exact bm_rule.diag_row_rel ]. Qed.

Theorem the_corner_carries_fill_the_66_bit_bank :
  carries_of bm_rule.CORNER bm_rule.CORNER bm_rule.CORNER_OUT = [18446744073709551614; 36893488147419103229; 55340232221128654844; 73786976294838206459; 55340232221128654845; 36893488147419103230; 18446744073709551615]
  /\ 2 ^ 65 <= nth 2 (carries_of bm_rule.CORNER bm_rule.CORNER bm_rule.CORNER_OUT) 0 < 2 ^ 66.
Proof.

  split; [ vm_compute; reflexivity | ].
  split; [ apply Z.leb_le | apply Z.ltb_lt ]; vm_compute; reflexivity.
Qed.

Theorem accepts_bm_is_canonical : forall a b out, accepts_bm a b out ->
  Forall (fun x => 0 <= x < p) a /\ Forall (fun x => 0 <= x < p) b
  /\ Forall (fun x => 0 <= x < p) out.
Proof.
  intros a b out [al [_ [_ [Ha [Hb Ho]]]]]. subst a b out.
  unfold a_l, b_l, out_l.
  split; [ | split ]; repeat (apply Forall_cons; [ apply dc_range | ]); apply Forall_nil.
Qed.

Theorem accepts_is_not_mod_q_invariant :
  accepts_bm bm_rule.CORNER bm_rule.CORNER bm_rule.CORNER_OUT
  /\ ~ accepts_bm [2 ^ 64 - 1 + p; 2 ^ 64 - 1; 2 ^ 64 - 1; 2 ^ 64 - 1] bm_rule.CORNER bm_rule.CORNER_OUT.
Proof.
  split; [ exact the_corner_is_ACCEPTED | ].
  intros Hacc. destruct (accepts_bm_is_canonical _ _ _ Hacc) as [Ha _].

  apply Forall_inv in Ha. cbn beta in Ha.
  pose proof (Z.pow_pos_nonneg 2 64 ltac:(lia) ltac:(lia)). lia.
Qed.

Theorem accepts_bm_fixes_the_arity : forall a b out, accepts_bm a b out ->
  length a = bm_rule.K /\ length b = bm_rule.K.
Proof. intros a b out [al [_ [_ [Ha [Hb _]]]]]. subst a b. split; reflexivity. Qed.

Print Assumptions CARRYC_exact.
Print Assumptions CARRYC_is_suffix_difference.
Print Assumptions VAL_skipn_S.
Print Assumptions REL_running.
Print Assumptions the_last_carry_is_the_top_limb.
Print Assumptions VAL_firstn_bound.
Print Assumptions carry_bound.
Print Assumptions bitsum66_bits_of.
Print Assumptions mkW_copies_hold.
Print Assumptions all_gates_hold.
Print Assumptions ASG_sat.
Print Assumptions decode_a.
Print Assumptions decode_b.
Print Assumptions decode_out.
Print Assumptions bridge_complete.
Print Assumptions policy_adequacy_bm.
Print Assumptions policy_adequacy_bm_conj.
Print Assumptions completeness_hypothesis_is_INHABITED.
Print Assumptions the_corner_is_ACCEPTED.
Print Assumptions the_diag_row_is_ACCEPTED.
Print Assumptions the_corner_carries_fill_the_66_bit_bank.
Print Assumptions accepts_bm_is_canonical.
Print Assumptions accepts_is_not_mod_q_invariant.
Print Assumptions accepts_bm_fixes_the_arity.
