(* SPDX-License-Identifier: Apache-2.0
   SPDX-FileCopyrightText: 2026 Next Ridge Solutions Ltd

   Soundness of bit-decomposition range checks over a prime field given as a parameter: when 2^n is at
   most p, a value whose n-bit decomposition constraints are satisfied lies in [0, 2^n) modulo p
   (range_tail_sound_field).

   Scope: these results bind the formal (Coq) layer only; the generated constraint model's fidelity to the circuit implementation, and the implementation itself, are outside them. *)

From Coq Require Import ZArith Lia List String Znumtheory.
Import ListNotations.
From Constraints Require Import pfcs.
Open Scope Z_scope.

Section PrimeField.
Variable p : Z.
Hypothesis Hp : prime p.

Definition zp : FieldOps Z :=
  {| fzero := 0;
     fone  := 1;
     fadd  := fun a b => (a + b) mod p;
     fmul  := fun a b => (a * b) mod p;
     fneg  := fun a => (- a) mod p;
     feqb  := fun a b => Z.eqb (a mod p) (b mod p) |}.

Definition Cbool (b : Var) : Constraint Z :=
  Eq (PAdd (PMul (PVar b) (PVar b)) (PNeg (PVar b))) (PConst 0).
Definition Cbitsum_step (t b tl : Var) : Constraint Z :=
  Eq (PVar t) (PAdd (PVar b) (PAdd (PVar tl) (PVar tl))).

Fixpoint range_tail (t : Var) (base : Var) (n : nat) : Constraint Z :=
  match n with
  | O => Eq (PVar t) (PConst 0)
  | S m =>
      Exists base
        (Exists (S base)
           (And (Cbitsum_step t base (S base))
                (And (Cbool base)
                     (range_tail (S base) (S (S base)) m))))
  end.

Lemma env_extend_eq : forall (e : Env Z) (k : Var) (x : Z),
  env_extend e k x k = Some x.
Proof. intros. unfold env_extend. rewrite Nat.eqb_refl. reflexivity. Qed.
Lemma env_extend_neq : forall (e : Env Z) (k j : Var) (x : Z),
  k <> j -> env_extend e k x j = e j.
Proof.
  intros e k j x H. unfold env_extend.
  destruct (Nat.eqb k j) eqn:Hkj.
  - apply Nat.eqb_eq in Hkj. contradiction.
  - reflexivity.
Qed.

Lemma bool_mod_forces_01 : forall b,
  (b * b - b) mod p = 0 ->
  b mod p = 0 \/ b mod p = 1.
Proof.
  intros b Hb. pose proof (prime_ge_2 _ Hp) as Hp2.
  replace (b * b - b) with (b * (b - 1)) in Hb by ring.
  apply Z.mod_divide in Hb; [| lia].
  apply prime_mult in Hb; [| exact Hp].
  destruct Hb as [H|H].
  - left.  apply Z.mod_divide in H; [exact H | lia].
  - right.
    assert (Hm1 : (b - 1) mod p = 0) by (apply Z.mod_divide; [lia | exact H]).
    replace b with ((b - 1) + 1) by ring.
    rewrite Zplus_mod, Hm1, Z.add_0_l, Zmod_mod.
    rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma range_tail_sound_field :
  forall (n : nat) (t base : Var) (e : Env Z) (d : Z),
    2 ^ (Z.of_nat n) <= p ->
    (t < base)%nat ->
    e t = Some d ->
    satisfies zp [] e (range_tail t base n) ->
    0 <= d mod p < 2 ^ (Z.of_nat n).
Proof.
  pose proof (prime_ge_2 _ Hp) as Hp2.
  induction n as [| m IH]; intros t base e d Hnowrap Hlt Het Hsat; simpl in Hsat.
  -
    inversion Hsat as [e0 pp qq vv Hpp Hqq | | | ]; subst.
    cbn [eval_poly] in Hpp, Hqq. rewrite Het in Hpp.
    inversion Hpp; subst vv. inversion Hqq as [Hd0].
    change (Z.of_nat 0) with 0%Z. rewrite Z.pow_0_r.
    assert (d = 0) by lia. subst d. rewrite Zmod_0_l. lia.
  -
    assert (Hpow : 2 ^ (Z.of_nat (S m)) = 2 * 2 ^ (Z.of_nat m)).
    { rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. ring. }
    assert (Hpowm_pos : 0 < 2 ^ (Z.of_nat m)) by (apply Z.pow_pos_nonneg; lia).
    assert (Hnowrap_m : 2 ^ (Z.of_nat m) <= p) by lia.
    inversion Hsat as [| | e0 x c wb Hsb Hx Hc | ]; subst; clear Hsat.
    inversion Hsb as [| | e1 x1 c1 wtl Hstl Hx1 Hc1 | ]; subst; clear Hsb.
    set (eb := env_extend (env_extend e base wb) (S base) wtl) in *.
    inversion Hstl as [ | e2 ca cb Hand1 Hand2 | | ]; subst; clear Hstl.
    inversion Hand2 as [ | e3 ca3 cb3 Hbool Hrest | | ]; subst; clear Hand2.
    inversion Hand1 as [ eb' pp qq vv Hpp Hqq Heqeb | | | ]; subst; clear Hand1.
    assert (Hb_eb : eb base = Some wb).
    { unfold eb. rewrite env_extend_neq by lia. apply env_extend_eq. }
    assert (Htl_eb : eb (S base) = Some wtl).
    { unfold eb. apply env_extend_eq. }
    assert (Ht_eb : eb t = Some d).
    { unfold eb. rewrite env_extend_neq by lia.
      rewrite env_extend_neq by lia. exact Het. }
    cbn [eval_poly] in Hpp, Hqq.
    rewrite Ht_eb in Hpp.
    rewrite Hb_eb, Htl_eb in Hqq.

    injection Hpp as Hppe.
    injection Hqq as Hqqe.
    assert (Hd_mod : d = (wb + (wtl + wtl) mod p) mod p) by lia.
    inversion Hbool as [ ec pp2 qq2 vv2 Hpp2 Hqq2 | | | ]; clear Hbool.
    cbn [eval_poly] in Hpp2, Hqq2.
    rewrite Hb_eb in Hpp2.
    injection Hpp2 as Hbool_val.
    injection Hqq2 as Hzero.
    assert (Hwb_mod0 : (wb * wb - wb) mod p = 0).
    { replace (wb * wb - wb) with (wb * wb + (- wb)) by ring.
      rewrite Zplus_mod, Hbool_val, <- Hzero. reflexivity. }
    apply bool_mod_forces_01 in Hwb_mod0.
    assert (Htl_bound : 0 <= wtl mod p < 2 ^ (Z.of_nat m)).
    { eapply IH with (t := S base) (base := S (S base)) (e := eb).
      - exact Hnowrap_m.
      - lia.
      - exact Htl_eb.
      - exact Hrest. }

    set (vb := wb mod p) in *.
    set (vt := wtl mod p) in *.
    set (v := vb + 2 * vt).
    assert (Hv_lo : 0 <= v).
    { unfold v. destruct Hwb_mod0 as [Hbb|Hbb]; rewrite Hbb; lia. }
    assert (Hv_hi : v < 2 ^ (Z.of_nat (S m))).
    { unfold v. rewrite Hpow. destruct Hwb_mod0 as [Hbb|Hbb]; rewrite Hbb; lia. }

    assert (Hv_lt_p : v < p) by lia.
    assert (Hv_modp : v mod p = v) by (apply Z.mod_small; lia).

    assert (Hcollapse : d mod p = (wb + 2 * wtl) mod p).
    { rewrite Hd_mod, Zmod_mod.
      rewrite (Zplus_mod wb ((wtl + wtl) mod p)), Zmod_mod,
              <- (Zplus_mod wb (wtl + wtl)).
      f_equal. ring. }

    assert (Hcong : (wb + 2 * wtl) mod p = v).
    { assert (Hsplit : wb + 2 * wtl = v + (wb / p + 2 * (wtl / p)) * p).
      { unfold v, vb, vt.
        rewrite (Z.div_mod wb p) at 1 by lia.
        rewrite (Z.div_mod wtl p) at 1 by lia. ring. }
      rewrite Hsplit, Z.mod_add by lia. rewrite Hv_modp. reflexivity. }
    assert (Hd_eq_v : d mod p = v) by (rewrite Hcollapse, Hcong; reflexivity).
    rewrite Hd_eq_v. lia.
Qed.

End PrimeField.

Print Assumptions range_tail_sound_field.
