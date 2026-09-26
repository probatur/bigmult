(* SPDX-License-Identifier: Apache-2.0
   SPDX-FileCopyrightText: 2026 Next Ridge Solutions Ltd

   Field facts for the Pasta prime, including its primality, proved by a Pocklington certificate
   (pasta_prime), and the range-check soundness of range_field.v instantiated at that prime.

   Scope: these results bind the formal (Coq) layer only; the generated constraint model's fidelity to the circuit implementation, and the implementation itself, are outside them. *)

From Coq Require Import ZArith Lia List String Znumtheory.
Import ListNotations.
Open Scope Z_scope.
From Constraints Require Import pfcs range_field.

Require Import Coq.Arith.Arith Coq.ZArith.Zpow_facts.

From Coq Require Import ZArith Lia List Arith.
Import ListNotations.
Open Scope nat_scope.

Fixpoint binom (n k : nat) : nat :=
  match n, k with
  | _, O => 1
  | O, S _ => 0
  | S n', S k' => binom n' k' + binom n' (S k')
  end.
Lemma binom_n_0 n : binom n 0 = 1. Proof. destruct n; reflexivity. Qed.
Lemma binom_pascal n k : binom (S n) (S k) = binom n k + binom n (S k).
Proof. reflexivity. Qed.
Lemma binom_gt n k : (n < k) -> binom n k = 0.
Proof.
  revert k. induction n as [|n IH]; intros k Hk.
  - destruct k. lia. reflexivity.
  - destruct k. lia. rewrite binom_pascal, !IH by lia. reflexivity.
Qed.

Open Scope Z_scope.
Definition bterm (x:Z) (n k:nat) : Z := Z.of_nat (binom n k) * x ^ Z.of_nat k.
Definition bsum (x:Z) (n:nat) : Z := fold_right Z.add 0 (map (bterm x n) (seq 0 (S n))).

Lemma fold_add_app l1 l2 :
  fold_right Z.add 0 (l1 ++ l2) = fold_right Z.add 0 l1 + fold_right Z.add 0 l2.
Proof. induction l1 as [|a l IH]; simpl; [ring | rewrite IH; ring]. Qed.

Lemma fold_add_map_ext (f g : nat -> Z) l :
  (forall k, In k l -> f k = g k) ->
  fold_right Z.add 0 (map f l) = fold_right Z.add 0 (map g l).
Proof.
  induction l as [|a l IH]; intro H; simpl. reflexivity.
  rewrite H by (simpl; auto). rewrite IH. reflexivity.
  intros k Hk. apply H. simpl; auto.
Qed.

Lemma seq_split_head m (f : nat -> Z) :
  fold_right Z.add 0 (map f (seq 0 (S m))) =
  f 0%nat + fold_right Z.add 0 (map (fun k => f (S k)) (seq 0 m)).
Proof.
  simpl. f_equal.
  rewrite <- seq_shift, map_map. reflexivity.
Qed.

Lemma binom_thm : forall n (x:Z), (1 + x) ^ Z.of_nat n = bsum x n.
Proof.
  induction n as [|n IH]; intro x.
  - cbv [bsum]. simpl. cbv [bterm]. simpl. ring.
  - rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. rewrite IH.

    unfold bsum at 2.

    rewrite (seq_split_head (S n) (bterm x (S n))).

    assert (Hb0a : bterm x (S n) 0%nat = 1) by (cbv [bterm]; rewrite binom_n_0; simpl; ring); rewrite Hb0a.

    erewrite fold_add_map_ext with
      (g := fun k => bterm x n (S k) + x * bterm x n k).
    2:{ intros k Hk. cbv [bterm].
        rewrite binom_pascal, Nat2Z.inj_add.
        rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. ring. }

    assert (Hsplit : forall (u v : nat -> Z) l,
      fold_right Z.add 0 (map (fun k => u k + v k) l)
      = fold_right Z.add 0 (map u l) + fold_right Z.add 0 (map v l)).
    { intros u v l. induction l as [|a l IHl]; simpl. ring. rewrite IHl. ring. }
    rewrite Hsplit.

    assert (Hscale : forall (u:nat->Z) c l,
      fold_right Z.add 0 (map (fun k => c * u k) l) = c * fold_right Z.add 0 (map u l)).
    { intros u c l. induction l as [|a l IHl]; simpl. ring. rewrite IHl; ring. }
    rewrite Hscale.

    rewrite seq_S, map_app, fold_add_app.
    assert (Hbz : bterm x n (S (0 + n)) = 0).
    { unfold bterm. rewrite (binom_gt n (S (0+n))) by lia. simpl (Z.of_nat 0). ring. }
    assert (Hz : fold_right Z.add 0 (map (fun k => bterm x n (S k)) [0 + n]%nat) = 0).
    { cbn [map fold_right]. rewrite Hbz. ring. }
    rewrite Hz, Z.add_0_r.

    assert (Hbs : bsum x n = bterm x n 0%nat + fold_right Z.add 0 (map (fun k => bterm x n (S k)) (seq 0 n))).
    { unfold bsum. apply seq_split_head. }
    assert (Hb0b : bterm x n 0%nat = 1) by (cbv [bterm]; rewrite binom_n_0; simpl; ring); rewrite Hb0b in Hbs.
    set (A := fold_right Z.add 0 (map (fun k => bterm x n (S k)) (seq 0 n))) in *.
    rewrite <- seq_S. fold (bsum x n). rewrite Hbs. ring.
Qed.

From Coq Require Import Znumtheory Zpow_facts.

Lemma binom_n_n n : binom n n = 1%nat.
Proof.
  induction n as [|n IH]. reflexivity.
  rewrite binom_pascal, IH, (binom_gt n (S n)) by lia. lia.
Qed.

Section FRESHMAN.
Variable r : Z.
Hypothesis Hr : prime r.

Hypothesis Hmid : forall k, (0 < k < Z.to_nat r)%nat -> (r | Z.of_nat (binom (Z.to_nat r) k)).

Lemma bterm_mid_mod x k : (0 < k < Z.to_nat r)%nat -> (bterm x (Z.to_nat r) k) mod r = 0.
Proof.
  intros Hk. unfold bterm.
  apply Z.mod_divide. pose proof (prime_ge_2 _ Hr); lia.
  apply Z.divide_mul_l. apply Hmid; exact Hk.
Qed.

Lemma freshman x : ((x + 1) ^ r) mod r = (x ^ r + 1) mod r.
Proof.
  pose proof (prime_ge_2 _ Hr) as Hr2.
  set (rn := Z.to_nat r) in *.
  assert (Hrn : Z.of_nat rn = r) by (unfold rn; rewrite Z2Nat.id; lia).

  assert (Hxr : (x + 1) ^ r = bsum x rn).
  { rewrite <- Hrn at 1. rewrite <- binom_thm. f_equal. ring. }
  rewrite Hxr.

  unfold bsum.

  rewrite seq_split_head.
  assert (Hb0 : bterm x rn 0%nat = 1) by (unfold bterm; rewrite binom_n_0; simpl; ring).
  rewrite Hb0.

  destruct rn as [|m] eqn:Erm. lia.

  rewrite seq_S, map_app, fold_add_app.

  assert (Hlast : fold_right Z.add 0 (map (fun k => bterm x (S m) (S k)) [0 + m]%nat)
                  = x ^ r).
  { cbn [map fold_right]. unfold bterm.
    replace (S (0 + m)) with (S m) by lia. rewrite binom_n_n.
    rewrite Hrn. simpl (Z.of_nat 1). ring. }
  rewrite Hlast.

  set (Mid := fold_right Z.add 0 (map (fun k => bterm x (S m) (S k)) (seq 0 m))).
  assert (HMid0 : Mid mod r = 0).
  { unfold Mid.

    assert (Hall : forall k, In k (seq 0 m) -> (bterm x (S m) (S k)) mod r = 0).
    { intros k Hk. rewrite in_seq in Hk.
      unfold bterm. apply Z.mod_divide; [lia|].
      apply Z.divide_mul_l.
      apply (Hmid (S k)). lia. }

    revert Hall. generalize (seq 0 m) as l. induction l as [|a l IHl]; intro Hall.
    - reflexivity.
    - cbn [map fold_right]. rewrite Zplus_mod.
      rewrite (Hall a) by (simpl; auto).
      rewrite IHl by (intros; apply Hall; simpl; auto).
      reflexivity. }

  assert (Hdiff : (1 + (Mid + x ^ r)) = (x ^ r + 1) + Mid) by ring.
  rewrite Hdiff.
  apply Z.mod_divide in HMid0; [|lia].
  destruct HMid0 as [c Hc].
  rewrite Hc, Z_mod_plus_full. reflexivity.
Qed.

End FRESHMAN.

Fixpoint fact (n:nat) : nat := match n with O => 1 | S m => n * fact m end%nat.

Lemma binom_fact_id : forall n k, (k <= n)%nat ->
  (binom n k * (fact k * fact (n - k)) = fact n)%nat.
Proof.
  induction n as [|n IH]; intros k Hk.
  - assert (k = 0)%nat by lia. subst. reflexivity.
  - destruct k as [|k].
    + rewrite binom_n_0. replace (S n - 0)%nat with (S n) by lia.
      simpl (fact 0). lia.
    + replace (S n - S k)%nat with (n - k)%nat by lia.
      destruct (Nat.eq_dec (S k) (S n)) as [He|Hne].
      * assert (Hkn : k = n) by lia. subst k.
        rewrite binom_pascal.
        assert (Hbgt : binom n (S n) = 0%nat) by (apply binom_gt; lia).
        assert (Hsub : (n - n = 0)%nat) by lia.
        rewrite Hbgt, binom_n_n, Hsub. simpl (fact 0). lia.
      * assert (HSkn : (S k <= n)%nat) by lia.
        rewrite binom_pascal.
        pose proof (IH k ltac:(lia)) as Ha.
        pose proof (IH (S k) ltac:(lia)) as Hb.
        assert (Hnk1 : (n - k = S (n - S k))%nat) by lia.
        replace (fact (S k)) with (S k * fact k)%nat by reflexivity.
        rewrite Hnk1.
        replace (fact (S (n - S k))) with (S (n - S k) * fact (n - S k))%nat by reflexivity.
        set (Ck := binom n k) in *. set (Csk := binom n (S k)) in *.
        set (fk := fact k) in *. set (fnk := fact (n - S k)) in *.
        rewrite Hnk1 in Ha.
        replace (fact (S (n - S k))) with (S (n - S k) * fnk)%nat in Ha by reflexivity.
        replace (fact (S k)) with (S k * fk)%nat in Hb by reflexivity.
        simpl (fact (S n)).
        assert (Hn : (n = k + S (n - S k))%nat) by lia.
        nia.
Qed.

Lemma prime_not_div_fact : forall (r:Z), prime r ->
  forall m, (Z.of_nat m < r) -> ~ (r | Z.of_nat (fact m)).
Proof.
  intros r Hr m. induction m as [|m IH]; intros Hm.
  - simpl (fact 0). intro Hd. pose proof (prime_ge_2 _ Hr) as Hr2.
    apply Z.divide_1_r in Hd. lia.
  - rewrite Nat2Z.inj_succ in Hm.
    replace (fact (S m)) with (S m * fact m)%nat by reflexivity.
    rewrite Nat2Z.inj_mul, Nat2Z.inj_succ. intro Hd.
    apply prime_mult in Hd; [| exact Hr].
    destruct Hd as [H1|H2].
    + pose proof (prime_ge_2 _ Hr) as Hr2.
      apply Z.divide_pos_le in H1; lia.
    + apply IH; [lia | exact H2].
Qed.

Lemma prime_div_fact_self : forall (r:Z), prime r ->
  (r | Z.of_nat (fact (Z.to_nat r))).
Proof.
  intros r Hr. pose proof (prime_ge_2 _ Hr) as Hr2.
  set (rn := Z.to_nat r).
  assert (Hrn : Z.of_nat rn = r) by (unfold rn; rewrite Z2Nat.id; lia).
  assert (Hpos : (0 < rn)%nat) by (unfold rn; lia).
  destruct rn as [|m] eqn:E. lia.
  replace (fact (S m)) with (S m * fact m)%nat by reflexivity.
  rewrite Nat2Z.inj_mul. apply Z.divide_mul_l.
  rewrite Hrn. apply Z.divide_refl.
Qed.

Lemma prime_div_binom : forall (r:Z), prime r ->
  forall k, (0 < k < Z.to_nat r)%nat ->
  (r | Z.of_nat (binom (Z.to_nat r) k)).
Proof.
  intros r Hr k Hk. pose proof (prime_ge_2 _ Hr) as Hr2.
  set (rn := Z.to_nat r) in *.
  assert (Hrn : Z.of_nat rn = r) by (unfold rn; rewrite Z2Nat.id; lia).
  pose proof (binom_fact_id rn k ltac:(lia)) as Hid.
  pose proof (prime_div_fact_self r Hr) as Hdivfact. fold rn in Hdivfact.
  rewrite <- Hid in Hdivfact.
  rewrite !Nat2Z.inj_mul in Hdivfact.
  apply prime_mult in Hdivfact; [| exact Hr].
  destruct Hdivfact as [Hb | Hrest].
  - exact Hb.
  - exfalso. apply prime_mult in Hrest; [| exact Hr].
    destruct Hrest as [Hfk | Hfrk].
    + apply (prime_not_div_fact r Hr k); [rewrite <- Hrn; apply Nat2Z.inj_lt; lia | exact Hfk].
    + apply (prime_not_div_fact r Hr (rn - k)); [rewrite <- Hrn; apply Nat2Z.inj_lt; lia | exact Hfrk].
Qed.

Lemma freshman' : forall (r:Z), prime r -> forall x,
  (x + 1) ^ r mod r = (x ^ r + 1) mod r.
Proof.
  intros r Hr x. apply freshman; auto.
  intros k Hk. apply prime_div_binom; auto.
Qed.

Lemma fermat_nonneg : forall (r:Z), prime r -> forall a, 0 <= a ->
  a ^ r mod r = a mod r.
Proof.
  intros r Hr. pose proof (prime_ge_2 _ Hr) as Hr2.

  intros a Ha. pattern a. apply natlike_ind; [ | | exact Ha].
  -
    rewrite Z.pow_0_l by lia. reflexivity.
  -
    intros n Hn IH.
    replace (Z.succ n) with (n + 1) by lia.
    rewrite (freshman' r Hr n).

    rewrite Zplus_mod, IH, <- Zplus_mod. reflexivity.
Qed.

Lemma fermat_all : forall (r:Z), prime r -> forall a, a ^ r mod r = a mod r.
Proof.
  intros r Hr a. pose proof (prime_ge_2 _ Hr) as Hr2.

  assert (Hb : 0 <= a mod r < r) by (apply Z.mod_pos_bound; lia).
  transitivity ((a mod r) ^ r mod r).
  - rewrite (Zpower_mod a r r) by lia. reflexivity.
  - rewrite (fermat_nonneg r Hr (a mod r)) by lia. rewrite Zmod_mod. reflexivity.
Qed.

Lemma fermat_little : forall (r:Z), prime r -> forall a,
  rel_prime a r -> a ^ (r - 1) mod r = 1 mod r.
Proof.
  intros r Hr a Hcop. pose proof (prime_ge_2 _ Hr) as Hr2.

  assert (Hsplit : a ^ r = a * a ^ (r - 1)).
  { rewrite <- Z.pow_succ_r by lia. f_equal. lia. }
  pose proof (fermat_all r Hr a) as Hf. rewrite Hsplit in Hf.

  assert (Hdvd : (r | a * (a ^ (r - 1) - 1))).
  { apply Z.mod_divide; [lia|].
    replace (a * (a ^ (r - 1) - 1)) with (a * a ^ (r - 1) - a) by ring.
    rewrite Zminus_mod, Hf, <- Zminus_mod. rewrite Z.sub_diag. reflexivity. }

  apply Gauss in Hdvd; [| apply rel_prime_sym; exact Hcop].

  destruct Hdvd as [c Hc].

  assert (Hval : a ^ (r-1) = 1 + c * r) by lia.
  rewrite Hval. rewrite Z_mod_plus_full. reflexivity.
Qed.

Lemma exists_inv : forall r a, 1 < r -> rel_prime a r ->
  exists u, (a * u) mod r = 1 mod r.
Proof.
  intros r a Hr Hcop.
  apply rel_prime_bezout in Hcop. destruct Hcop as [u v Huv].
  exists u.
  assert (a * u = 1 - v * r) by lia.
  rewrite H. rewrite Zminus_mod, Z_mod_mult, Z.sub_0_r, Zmod_mod. reflexivity.
Qed.

Lemma pow_cong_one_sub : forall r a m k, 1 < r -> rel_prime a r ->
  (0 <= k <= m) ->
  a ^ m mod r = 1 mod r -> a ^ k mod r = 1 mod r ->
  a ^ (m - k) mod r = 1 mod r.
Proof.
  intros r a m k Hr Hcop Hkm Hm Hk.

  assert (Hsplit : a ^ m = a ^ k * a ^ (m - k)).
  { rewrite <- Z.pow_add_r by lia. f_equal. lia. }

  assert (Hak : rel_prime (a ^ k) r).
  { apply rel_prime_sym. apply rel_prime_Zpower_r; [lia | apply rel_prime_sym; exact Hcop]. }
  destruct (exists_inv r (a ^ k) Hr Hak) as [u Hu].

  assert (E : a ^ (m - k) mod r = ((a ^ k * u) * a ^ (m - k)) mod r).
  { rewrite (Zmult_mod (a^k * u)). rewrite Hu.
    rewrite (Z.mod_small 1 r) by lia. rewrite Z.mul_1_l, Zmod_mod. reflexivity. }
  rewrite E.

  replace (a ^ k * u * a ^ (m - k)) with (u * (a ^ k * a ^ (m - k))) by ring.
  rewrite <- Hsplit.

  rewrite Zmult_mod, Hm, (Z.mod_small 1 r) by lia.
  rewrite Z.mul_1_r, Zmod_mod.

  rewrite Zmult_mod, Hk, (Z.mod_small 1 r) in Hu by lia.
  rewrite Z.mul_1_l, Zmod_mod in Hu. exact Hu.
Qed.

Lemma pow_cong_one_mul : forall r a k t, 1 < r -> 0 <= k -> 0 <= t ->
  a ^ k mod r = 1 mod r -> a ^ (k * t) mod r = 1 mod r.
Proof.
  intros r a k t Hr Hk Ht Hak.
  rewrite Z.pow_mul_r by lia.

  rewrite Zpower_mod by lia. rewrite Hak.
  rewrite <- Zpower_mod by lia. rewrite Z.pow_1_l by lia.
  reflexivity.
Qed.

Lemma pow_cong_one_gcd : forall r a, 1 < r -> rel_prime a r ->
  forall N, (0 <= N) -> forall m k, 0 <= m -> 0 <= k -> (m + k <= N) ->
  a ^ m mod r = 1 mod r -> a ^ k mod r = 1 mod r ->
  a ^ (Z.gcd m k) mod r = 1 mod r.
Proof.
  intros r a Hr Hcop N HN. pattern N. apply Z_lt_induction; [| exact HN].
  clear N HN. intros N IH m k Hm Hk Hmk Hpm Hpk.
  destruct (Z.eq_dec k 0) as [Hk0|Hk0].
  - subst k. rewrite Z.gcd_0_r. rewrite Z.abs_eq by lia. exact Hpm.
  - destruct (Z.eq_dec m 0) as [Hm0|Hm0].
    + subst m. rewrite Z.gcd_0_l. rewrite Z.abs_eq by lia. exact Hpk.
    + destruct (Z.le_gt_cases k m) as [Hle|Hgt].
      *
        assert (Hsub : a ^ (m - k) mod r = 1 mod r).
        { apply pow_cong_one_sub; auto; lia. }

        assert (Hg : Z.gcd m k = Z.gcd (m - k) k).
        { rewrite (Z.gcd_comm m k), (Z.gcd_comm (m-k) k).
          symmetry. apply Z.gcd_sub_diag_r. }
        rewrite Hg. apply (IH (m - k + k)); try lia; auto.
      *
        assert (Hsub : a ^ (k - m) mod r = 1 mod r).
        { apply pow_cong_one_sub; auto; lia. }
        assert (Hg : Z.gcd m k = Z.gcd m (k - m)).
        { symmetry. apply Z.gcd_sub_diag_r. }
        rewrite Hg. apply (IH (m + (k - m))); try lia; auto.
Qed.

Lemma has_prime_divisor : forall n, 1 < n -> exists q, prime q /\ (q | n).
Proof.
  intros n Hn0. assert (Hnn : 0 <= n) by lia. revert Hn0.
  pattern n. apply Z_lt_induction; [| exact Hnn].
  clear n Hnn. intros n IH Hn.
  destruct (prime_dec n) as [Hp|Hnp].
  - exists n; split; [exact Hp | apply Z.divide_refl].
  - destruct (not_prime_divide n Hn Hnp) as [d [Hd Hdvd]].
    destruct (IH d ltac:(lia) ltac:(lia)) as [q [Hq Hqd]].
    exists q; split; [exact Hq | apply Z.divide_trans with d; auto].
Qed.

Lemma pocklington_div : forall N r a,
  prime r -> 1 < N -> rel_prime a r ->
  a ^ (N - 1) mod r = 1 mod r ->
  (forall q, prime q -> (q | (N - 1)) ->
     a ^ ((N - 1) / q) mod r <> 1 mod r) ->
  ((N - 1) | (r - 1)).
Proof.
  intros N r a Hr HN Hcop Hferm Hno.
  pose proof (prime_ge_2 _ Hr) as Hr2.
  set (M := N - 1) in *.
  assert (HM : 0 < M) by lia.

  pose proof (fermat_little r Hr a Hcop) as Hfr.

  set (g := Z.gcd M (r - 1)).
  assert (Hg_dvd_M : (g | M)) by apply Z.gcd_divide_l.
  assert (Hg_dvd_r1 : (g | (r - 1))) by apply Z.gcd_divide_r.
  assert (Hgpos : 0 < g).
  { assert (0 <= g) by apply Z.gcd_nonneg.
    assert (g <> 0). { intro Hg0. apply Z.gcd_eq_0_l in Hg0. lia. }
    lia. }
  assert (Hr1 : 1 < r) by lia.
  assert (Hag : a ^ g mod r = 1 mod r).
  { apply (pow_cong_one_gcd r a Hr1 Hcop (M + (r-1))); try lia; auto. }

  assert (HgM : g = M).
  { destruct (Z.eq_dec g M) as [He|Hne]; [exact He|].
    exfalso.

    assert (Hgle : g <= M) by (apply Z.divide_pos_le; auto; lia).
    assert (Hquot : M = g * (M / g)) by (apply Zdivide_Zdiv_eq; auto).
    assert (HMg1 : 1 < M / g).
    { assert (M / g >= 1).
      { apply Z.le_ge. apply Z.div_le_lower_bound; lia. }
      destruct (Z.eq_dec (M / g) 1) as [E1|E1].
      - rewrite E1 in Hquot. lia.
      - lia. }
    destruct (has_prime_divisor (M / g) HMg1) as [q [Hq Hqdvd]].

    assert (HqM : (q | M)).
    { rewrite Hquot. apply Z.divide_mul_r; auto. }

    destruct Hqdvd as [c Hc].
    assert (HMq : M / q = g * c).
    {
      assert (HMval : M = (g * c) * q) by (rewrite Hquot, Hc; ring).
      rewrite HMval. rewrite Z.div_mul by (pose proof (prime_ge_2 _ Hq); lia). reflexivity. }
    assert (Hg_dvd_Mq : (g | (M / q))) by (rewrite HMq; apply Z.divide_factor_l).

    destruct Hg_dvd_Mq as [t Ht].
    pose proof (prime_ge_2 _ Hq) as Hq2.
    assert (HMqpos : 0 <= M / q) by (apply Z.div_pos; lia).
    assert (Htpos : 0 <= t) by nia.
    assert (Hcontra : a ^ (M / q) mod r = 1 mod r).
    { rewrite Ht. rewrite Z.mul_comm. apply pow_cong_one_mul; auto; lia. }
    apply (Hno q Hq HqM). exact Hcontra. }

  rewrite <- HgM. exact Hg_dvd_r1.
Qed.

Lemma pow_one_rel_prime : forall r a m, 1 < r -> 0 < m ->
  a ^ m mod r = 1 mod r -> rel_prime a r.
Proof.
  intros r a m Hr Hm Hpow.

  assert (Hsplit : a ^ m = a * a ^ (m - 1)).
  { rewrite <- Z.pow_succ_r by lia. f_equal. lia. }
  rewrite Hsplit in Hpow.

  assert (Hdvd : (r | a * a ^ (m-1) - 1)).
  { apply Z.mod_divide; [lia|].
    rewrite Zminus_mod, Hpow, (Z.mod_small 1 r) by lia.
    rewrite Z.sub_diag. reflexivity. }
  destruct Hdvd as [c Hc].

  apply bezout_rel_prime.
  apply (Bezout_intro a r 1 (a ^ (m-1)) (- c)). lia.
Qed.

Theorem pocklington_prime : forall N a,
  1 < N ->
  a ^ (N - 1) mod N = 1 mod N ->
  (forall q, prime q -> (q | (N - 1)) -> Z.gcd (a ^ ((N - 1) / q) - 1) N = 1) ->
  prime N.
Proof.
  intros N a HN Hferm Hgcd.
  apply prime_alt. split; [exact HN|].
  intros n [Hn1 HnN] HndivN.

  destruct (has_prime_divisor n Hn1) as [r [Hr Hrn]].
  pose proof (prime_ge_2 _ Hr) as Hr2.
  assert (HrN : (r | N)) by (apply Z.divide_trans with n; auto).
  assert (HrleN : r <= n) by (apply Z.divide_pos_le; auto; lia).

  assert (HfermR : a ^ (N - 1) mod r = 1 mod r).
  {
    destruct HrN as [s Hs].
    assert (Hd : (r | a ^ (N-1) - 1)).
    { apply Z.divide_trans with N; [exists s; lia|].
      apply Z.mod_divide; [lia|].
      rewrite Zminus_mod, Hferm, (Z.mod_small 1 N) by lia.
      rewrite Z.sub_diag. reflexivity. }
    destruct Hd as [c Hc].
    assert (Hav : a ^ (N-1) = 1 + c * r) by lia.
    rewrite Hav, Z_mod_plus_full. reflexivity. }
  assert (HcopR : rel_prime a r) by (apply (pow_one_rel_prime r a (N-1)); auto; lia).
  assert (HnoR : forall q, prime q -> (q | (N - 1)) ->
            a ^ ((N - 1) / q) mod r <> 1 mod r).
  { intros q Hq Hqdvd Heq.

    assert (Hrdvd : (r | a ^ ((N-1)/q) - 1)).
    { apply Z.mod_divide; [lia|].
      rewrite Zminus_mod, Heq, (Z.mod_small 1 r) by lia.
      rewrite Z.sub_diag. reflexivity. }
    pose proof (Hgcd q Hq Hqdvd) as Hg1.
    assert (Hrgcd : (r | Z.gcd (a ^ ((N-1)/q) - 1) N)).
    { apply Z.gcd_greatest; auto. }
    rewrite Hg1 in Hrgcd. apply Z.divide_1_r in Hrgcd. lia. }

  pose proof (pocklington_div N r a Hr HN HcopR HfermR HnoR) as Hdvd.
  assert (Hr1pos : 0 < r - 1) by lia.
  assert (HleN1 : N - 1 <= r - 1) by (apply Z.divide_pos_le; auto; lia).

  lia.
Qed.

Record PFactor := { pf_prime : Z; pf_pow : Z }.

Fixpoint prod_pows (l : list PFactor) : Z :=
  match l with
  | [] => 1
  | f :: tl => pf_pow f * prod_pows tl
  end.

Lemma prime_div_prod : forall (l : list PFactor) q, prime q ->
  (q | prod_pows l) ->
  exists f, In f l /\ (q | pf_pow f).
Proof.
  induction l as [|f tl IH]; intros q Hq Hdvd; simpl in Hdvd.
  - apply Z.divide_1_r in Hdvd. pose proof (prime_ge_2 _ Hq). lia.
  - apply prime_mult in Hdvd; [| exact Hq].
    destruct Hdvd as [H1|H2].
    + exists f; split; [left; reflexivity | exact H1].
    + destruct (IH q Hq H2) as [f' [Hin Hdv]].
      exists f'; split; [right; exact Hin | exact Hdv].
Qed.

Lemma prime_div_primepow : forall p q e, prime p -> prime q ->
  0 <= e -> (q | p ^ e) -> q = p.
Proof.
  intros p q e Hp Hq He Hdvd.
  apply (prime_power_prime q p e); auto.
Qed.

Definition wf_factor (f : PFactor) (e : Z) : Prop :=
  prime (pf_prime f) /\ 0 <= e /\ pf_pow f = (pf_prime f) ^ e.

Theorem pocklington_prime_list : forall N a (L : list PFactor) (es : list Z),
  1 < N ->
  N - 1 = prod_pows L ->
  length es = length L ->
  (forall i, (i < length L)%nat ->
     wf_factor (nth i L {| pf_prime := 2; pf_pow := 2 |}) (nth i es 0)) ->
  a ^ (N - 1) mod N = 1 mod N ->
  (forall f, In f L -> Z.gcd (a ^ ((N - 1) / (pf_prime f)) - 1) N = 1) ->
  prime N.
Proof.
  intros N a L es HN Hprod Hlen Hwf Hferm Hgcd.
  apply (pocklington_prime N a HN Hferm).
  intros q Hq HqdvdM.

  rewrite Hprod in HqdvdM.
  destruct (prime_div_prod L q Hq HqdvdM) as [f [Hin Hdvf]].

  apply In_nth with (d := {| pf_prime := 2; pf_pow := 2 |}) in Hin.
  destruct Hin as [i [Hi Hnth]].
  pose proof (Hwf i Hi) as Hwfi. unfold wf_factor in Hwfi.
  rewrite Hnth in Hwfi. destruct Hwfi as [Hpp [He Hpow]].

  rewrite Hpow in Hdvf.
  assert (Hqeq : q = pf_prime f) by (apply (prime_div_primepow (pf_prime f) q (nth i es 0)); auto).
  rewrite Hqeq.
  apply Hgcd. rewrite <- Hnth. apply nth_In. exact Hi.
Qed.

Lemma zpow_mod_eq : forall a e N, N <> 0 -> 0 <= e ->
  Zpow_mod a e N = a ^ e mod N.
Proof. intros. apply Zpow_mod_correct; auto. Qed.

Lemma gcd_sub1_mod : forall x N, N <> 0 ->
  Z.gcd (x - 1) N = Z.gcd (x mod N - 1) N.
Proof.
  intros x N HN.
  assert (Hx : x - 1 = (x mod N - 1) + (x / N) * N).
  { rewrite (Z.div_mod x N HN) at 1. ring. }
  rewrite Hx.
  rewrite Z.gcd_comm. rewrite Z.gcd_add_mult_diag_r. rewrite Z.gcd_comm.
  reflexivity.
Qed.

Lemma gcd_pow_bridge : forall a e N, N <> 0 -> 0 <= e ->
  Z.gcd ((Zpow_mod a e N) - 1) N = 1 ->
  Z.gcd (a ^ e - 1) N = 1.
Proof.
  intros a e N HN He H.
  rewrite zpow_mod_eq in H by auto.
  rewrite (gcd_sub1_mod (a ^ e) N HN). exact H.
Qed.

Lemma fermat_from_zpow : forall a N, 1 < N ->
  Zpow_mod a (N - 1) N = 1 ->
  a ^ (N - 1) mod N = 1 mod N.
Proof.
  intros a N HN H. rewrite zpow_mod_eq in H by lia.
  rewrite H, (Z.mod_small 1 N) by lia. reflexivity.
Qed.

Theorem pocklington_prime_compute :
  forall N a (L : list PFactor) (es : list Z),
  1 < N ->
  N - 1 = prod_pows L ->
  length es = length L ->
  (forall i, (i < length L)%nat ->
     wf_factor (nth i L {| pf_prime := 2; pf_pow := 2 |}) (nth i es 0)) ->
  Zpow_mod a (N - 1) N = 1 ->
  (forall f, In f L -> Z.gcd ((Zpow_mod a ((N - 1) / (pf_prime f)) N) - 1) N = 1) ->
  prime N.
Proof.
  intros N a L es HN Hprod Hlen Hwf Hferm Hgcd.
  apply (pocklington_prime_list N a L es HN Hprod Hlen Hwf).
  - apply fermat_from_zpow; auto.
  - intros f Hin.
    pose proof (Hgcd f Hin) as Hg.
    apply gcd_pow_bridge; [lia | | exact Hg].

    apply In_nth with (d := {| pf_prime := 2; pf_pow := 2 |}) in Hin.
    destruct Hin as [i [Hi Hnth]].
    pose proof (Hwf i Hi) as Hwfi. unfold wf_factor in Hwfi.
    rewrite Hnth in Hwfi. destruct Hwfi as [Hpp _].
    pose proof (prime_ge_2 _ Hpp) as Hp2.
    apply Z.div_pos; lia.
Qed.

Open Scope Z_scope.

Fixpoint nodiv (p : Z) (d : Z) (fuel : nat) : bool :=
  match fuel with
  | O => true
  | S f =>
      if Z.ltb p (d * d) then true
      else if Z.eqb (Z.modulo p d) 0 then false
      else nodiv p (d + 1) f
  end.

Definition prime_test (p : Z) : bool :=
  if Z.leb p 1 then false else nodiv p 2 (S (Z.to_nat (Z.sqrt p))).

Lemma nodiv_sound : forall fuel p d,
  2 <= d ->
  nodiv p d fuel = true ->
  forall k, d <= k -> k * k <= p -> (k - d < Z.of_nat fuel) -> ~ (k | p).
Proof.
  induction fuel as [|f IH]; intros p d Hd Hnodiv k Hdk Hkk Hfuel.
  - simpl in Hfuel. lia.
  - simpl in Hnodiv.
    destruct (Z.ltb p (d * d)) eqn:Hlt.
    +
      apply Z.ltb_lt in Hlt. nia.
    + apply Z.ltb_ge in Hlt.
      destruct (Z.eqb (p mod d) 0) eqn:Hmod.
      * discriminate.
      * apply Z.eqb_neq in Hmod.

        destruct (Z.eq_dec k d) as [He|Hne].
        -- subst k. intro Hdvd. apply Hmod. apply Z.mod_divide; [lia | exact Hdvd].
        --
           apply (IH p (d + 1)); try lia.
           exact Hnodiv.
Qed.

Lemma no_small_div_prime : forall p, 2 <= p ->
  (forall k, 2 <= k -> k * k <= p -> ~ (k | p)) -> prime p.
Proof.
  intros p Hp Hnd. apply prime_alt. split; [lia|].
  intros n [Hn1 HnP] HndvdN.

  assert (Hpn : p = n * (p / n)).
  { apply Zdivide_Zdiv_eq; [lia | exact HndvdN]. }
  set (m := p / n) in *.
  assert (Hm2 : 2 <= m).
  { assert (0 < m). { unfold m. apply Z.div_str_pos; lia. }
    destruct (Z.eq_dec m 1) as [E|E]; [ rewrite E in Hpn; lia | lia ]. }
  destruct (Z.le_gt_cases (n * n) p) as [Hle|Hgt].
  - apply (Hnd n); [lia | exact Hle | exact HndvdN].
  -
    assert (Hmlt : m < n) by nia.
    assert (Hmm : m * m <= p) by nia.
    apply (Hnd m); [lia | exact Hmm |].
    rewrite Hpn. apply Z.divide_factor_r.
Qed.

Lemma prime_test_sound : forall p, prime_test p = true -> prime p.
Proof.
  intros p Hpt. unfold prime_test in Hpt.
  destruct (Z.leb p 1) eqn:Hle1; [discriminate|].
  apply Z.leb_gt in Hle1.
  apply no_small_div_prime; [lia|].
  intros k Hk2 Hkk.
  apply (nodiv_sound (S (Z.to_nat (Z.sqrt p))) p 2); auto.
  - lia.
  -
    rewrite Nat2Z.inj_succ, Z2Nat.id by (apply Z.sqrt_nonneg).

    assert (Hksqrt : k <= Z.sqrt p).
    { apply (Z.sqrt_le_square p k); [lia | lia | exact Hkk]. }
    pose proof (Z.sqrt_nonneg p). lia.
Qed.

Ltac prove_prime_small := apply prime_test_sound; vm_compute; reflexivity.

Open Scope Z_scope.

Ltac wf_slot lem := split; [ apply lem | split; [ cbn; lia | vm_compute; reflexivity ] ].

Lemma prime_463 : prime 463.
Proof. apply prime_test_sound; vm_compute; reflexivity. Qed.

Lemma prime_89 : prime 89.
Proof. apply prime_test_sound; vm_compute; reflexivity. Qed.

Lemma prime_14923 : prime 14923.
Proof. apply prime_test_sound; vm_compute; reflexivity. Qed.

Lemma prime_417677162933 : prime 417677162933.
Proof. apply prime_test_sound; vm_compute; reflexivity. Qed.

Lemma prime_539204044132271846773 : prime 539204044132271846773.
Proof.
  apply (pocklington_prime_compute 539204044132271846773 5
    [ {| pf_prime := 2; pf_pow := 4 |} ; {| pf_prime := 3; pf_pow := 243 |} ; {| pf_prime := 89; pf_pow := 89 |} ; {| pf_prime := 14923; pf_pow := 14923 |} ; {| pf_prime := 417677162933; pf_pow := 417677162933 |} ]
    [2;5;1;1;1]).
  - lia.
  - vm_compute; reflexivity.
  - reflexivity.
  - intros i Hi; simpl in Hi;
      (destruct i as [|i]; [ wf_slot prime_2 |]);
      (destruct i as [|i]; [ wf_slot prime_3 |]);
      (destruct i as [|i]; [ wf_slot prime_89 |]);
      (destruct i as [|i]; [ wf_slot prime_14923 |]);
      (destruct i as [|i]; [ wf_slot prime_417677162933 |]);
      lia.
  - vm_compute; reflexivity.
  - intros f Hf; simpl in Hf;
    repeat (destruct Hf as [<-|Hf]; [ vm_compute; reflexivity |]);
    destruct Hf.
Qed.

Lemma prime_11 : prime 11.
Proof. apply prime_test_sound; vm_compute; reflexivity. Qed.

Lemma prime_2531 : prime 2531.
Proof. apply prime_test_sound; vm_compute; reflexivity. Qed.

Lemma prime_115603 : prime 115603.
Proof. apply prime_test_sound; vm_compute; reflexivity. Qed.

Lemma prime_1197907 : prime 1197907.
Proof. apply prime_test_sound; vm_compute; reflexivity. Qed.

Lemma prime_22160661629 : prime 22160661629.
Proof. apply prime_test_sound; vm_compute; reflexivity. Qed.

Lemma prime_509 : prime 509.
Proof. apply prime_test_sound; vm_compute; reflexivity. Qed.

Lemma prime_413527 : prime 413527.
Proof. apply prime_test_sound; vm_compute; reflexivity. Qed.

Lemma prime_772231 : prime 772231.
Proof. apply prime_test_sound; vm_compute; reflexivity. Qed.

Lemma prime_325086459374267 : prime 325086459374267.
Proof.
  apply (pocklington_prime_compute 325086459374267 2
    [ {| pf_prime := 2; pf_pow := 2 |} ; {| pf_prime := 509; pf_pow := 509 |} ; {| pf_prime := 413527; pf_pow := 413527 |} ; {| pf_prime := 772231; pf_pow := 772231 |} ]
    [1;1;1;1]).
  - lia.
  - vm_compute; reflexivity.
  - reflexivity.
  - intros i Hi; simpl in Hi;
      (destruct i as [|i]; [ wf_slot prime_2 |]);
      (destruct i as [|i]; [ wf_slot prime_509 |]);
      (destruct i as [|i]; [ wf_slot prime_413527 |]);
      (destruct i as [|i]; [ wf_slot prime_772231 |]);
      lia.
  - vm_compute; reflexivity.
  - intros f Hf; simpl in Hf;
    repeat (destruct Hf as [<-|Hf]; [ vm_compute; reflexivity |]);
    destruct Hf.
Qed.

Lemma prime_8999194758858563409123804352480028797519453 : prime 8999194758858563409123804352480028797519453.
Proof.
  apply (pocklington_prime_compute 8999194758858563409123804352480028797519453 2
    [ {| pf_prime := 2; pf_pow := 4 |} ; {| pf_prime := 3; pf_pow := 81 |} ; {| pf_prime := 11; pf_pow := 11 |} ; {| pf_prime := 2531; pf_pow := 2531 |} ; {| pf_prime := 115603; pf_pow := 115603 |} ; {| pf_prime := 1197907; pf_pow := 1197907 |} ; {| pf_prime := 22160661629; pf_pow := 22160661629 |} ; {| pf_prime := 325086459374267; pf_pow := 325086459374267 |} ]
    [2;4;1;1;1;1;1;1]).
  - lia.
  - vm_compute; reflexivity.
  - reflexivity.
  - intros i Hi; simpl in Hi;
      (destruct i as [|i]; [ wf_slot prime_2 |]);
      (destruct i as [|i]; [ wf_slot prime_3 |]);
      (destruct i as [|i]; [ wf_slot prime_11 |]);
      (destruct i as [|i]; [ wf_slot prime_2531 |]);
      (destruct i as [|i]; [ wf_slot prime_115603 |]);
      (destruct i as [|i]; [ wf_slot prime_1197907 |]);
      (destruct i as [|i]; [ wf_slot prime_22160661629 |]);
      (destruct i as [|i]; [ wf_slot prime_325086459374267 |]);
      lia.
  - vm_compute; reflexivity.
  - intros f Hf; simpl in Hf;
    repeat (destruct Hf as [<-|Hf]; [ vm_compute; reflexivity |]);
    destruct Hf.
Qed.

Lemma prime_28948022309329048855892746252171976963363056481941560715954676764349967630337 : prime 28948022309329048855892746252171976963363056481941560715954676764349967630337.
Proof.
  apply (pocklington_prime_compute 28948022309329048855892746252171976963363056481941560715954676764349967630337 5
    [ {| pf_prime := 2; pf_pow := 4294967296 |} ; {| pf_prime := 3; pf_pow := 3 |} ; {| pf_prime := 463; pf_pow := 463 |} ; {| pf_prime := 539204044132271846773; pf_pow := 539204044132271846773 |} ; {| pf_prime := 8999194758858563409123804352480028797519453; pf_pow := 8999194758858563409123804352480028797519453 |} ]
    [32;1;1;1;1]).
  - lia.
  - vm_compute; reflexivity.
  - reflexivity.
  - intros i Hi; simpl in Hi;
      (destruct i as [|i]; [ wf_slot prime_2 |]);
      (destruct i as [|i]; [ wf_slot prime_3 |]);
      (destruct i as [|i]; [ wf_slot prime_463 |]);
      (destruct i as [|i]; [ wf_slot prime_539204044132271846773 |]);
      (destruct i as [|i]; [ wf_slot prime_8999194758858563409123804352480028797519453 |]);
      lia.
  - vm_compute; reflexivity.
  - intros f Hf; simpl in Hf;
    repeat (destruct Hf as [<-|Hf]; [ vm_compute; reflexivity |]);
    destruct Hf.
Qed.

Definition pasta_p : Z := 28948022309329048855892746252171976963363056481941560715954676764349967630337.
Lemma pasta_prime : prime pasta_p. Proof. unfold pasta_p. exact prime_28948022309329048855892746252171976963363056481941560715954676764349967630337. Qed.

Lemma pasta_nowrap : 2 ^ 64 <= pasta_p.
Proof. unfold pasta_p. lia. Qed.

Definition range_tail_sound_field_pasta := range_tail_sound_field pasta_p pasta_prime.

Definition e_zero : Env Z := fun _ => Some 0.
Lemma e_zero_get : forall w, e_zero w = Some 0. Proof. reflexivity. Qed.

Lemma nv_zero_sat_gen : forall n t base (e : Env Z),
  (forall w, e w = Some 0) ->
  (t < base)%nat ->
  satisfies (zp pasta_p) [] e (range_tail t base n).
Proof.
  induction n as [|m IH]; intros t base e He Hlt; simpl.
  - eapply Sat_Eq; cbn [eval_poly]; rewrite ?He; reflexivity.
  - apply Sat_Exists with (w := 0).
    apply Sat_Exists with (w := 0).
    set (e2 := env_extend (env_extend e base 0) (S base) 0).
    assert (He2 : forall w, e2 w = Some 0).
    { intro w. unfold e2, env_extend.
      destruct (Nat.eqb (S base) w); [reflexivity|].
      destruct (Nat.eqb base w); [reflexivity| apply He]. }
    apply Sat_And.
    + eapply Sat_Eq; cbn [eval_poly]; rewrite ?He2; reflexivity.
    + apply Sat_And.
      * eapply Sat_Eq; cbn [eval_poly]; rewrite ?He2; reflexivity.
      * apply IH; [exact He2 | lia].
Qed.

Lemma nv_zero_sat : forall n t base,
  (t < base)%nat ->
  satisfies (zp pasta_p) [] e_zero (range_tail t base n).
Proof. intros. apply nv_zero_sat_gen; [apply e_zero_get | exact H]. Qed.

Lemma nv_pasta_64 : 0 <= (0 mod pasta_p) < 2 ^ (Z.of_nat 64).
Proof.
  apply (range_tail_sound_field_pasta 64%nat 0%nat 1%nat e_zero 0).
  - change (Z.of_nat 64) with 64. apply pasta_nowrap.
  - lia.
  - apply e_zero_get.
  - apply nv_zero_sat. lia.
Qed.

Lemma nv_pasta_64_boundary : 0 <= ((2 ^ 64 - 1) mod pasta_p) < 2 ^ (Z.of_nat 64).
Proof.
  pose proof pasta_nowrap as Hp.
  assert (Hmod : (2 ^ 64 - 1) mod pasta_p = 2 ^ 64 - 1) by (apply Z.mod_small; lia).
  rewrite Hmod. change (Z.of_nat 64) with 64. lia.
Qed.

Print Assumptions range_tail_sound_field_pasta.
Print Assumptions nv_pasta_64.
Print Assumptions nv_pasta_64_boundary.
