(* SPDX-License-Identifier: Apache-2.0
   SPDX-FileCopyrightText: 2026 Next Ridge Solutions Ltd

   Assignments, the evaluator for constraint expressions, and the acceptance predicate sat: every
   polynomial constraint evaluates to zero modulo p, and every copy constraint holds. Also the intended
   public interface (RD_bm_gen: each output cell agrees modulo p with its public cell), which the model
   refines (deployed_refines_RD_bm_gen).

   Scope: these results bind the formal (Coq) layer only; the generated constraint model's fidelity to the circuit implementation, and the implementation itself, are outside them. *)

From Coq Require Import ZArith List Lia. Import ListNotations. Open Scope Z_scope.
Require Import Generated.bm_model_gen.
Require Import Generated.bm_wires_gen.

Definition Assignment := Cell -> Z.

Fixpoint eval (a:Assignment) (e:Expr) : Z :=
  match e with
  | EConst z    => z
  | ECell c     => a c
  | EAdd x y    => eval a x + eval a y
  | ESub x y    => eval a x - eval a y
  | EMul x y    => eval a x * eval a y
  | ENeg x      => - eval a x
  | EScaled x z => eval a x * z
  end.

Definition gate_holds a g : Prop := (eval a g) mod p = 0.
Definition gates_hold a gs : Prop := forall g, In g gs -> gate_holds a g.
Definition copy_holds a (cp:list (Cell*Cell)) : Prop :=
  forall e, In e cp -> (a (fst e)) mod p = (a (snd e)) mod p.
Definition sat (m:CircuitModel) a : Prop :=
  gates_hold a (cm_gates m) /\ copy_holds a (cm_copy m).

Definition cell_eqb (c d:Cell) : bool :=
  match c, d with
  | (c1,c2),(d1,d2) => andb (Nat.eqb c1 d1) (Nat.eqb c2 d2)
  end.
Definition cellpair_eqb (e f:Cell*Cell) : bool :=
  andb (cell_eqb (fst e) (fst f)) (cell_eqb (snd e) (snd f)).

Fixpoint reads_b (t:Cell) (e:Expr) : bool :=
  match e with
  | EConst _    => false
  | ECell c     => cell_eqb c t
  | EAdd x y    => orb (reads_b t x) (reads_b t y)
  | ESub x y    => orb (reads_b t x) (reads_b t y)
  | EMul x y    => orb (reads_b t x) (reads_b t y)
  | ENeg x      => reads_b t x
  | EScaled x _ => reads_b t x
  end.
Definition reads (t:Cell) (e:Expr) : Prop := reads_b t e = true.

Lemma copy_get : forall (a:Assignment) (c1 c2:Cell),
  copy_holds a deployed_copy ->
  In (c1,c2) deployed_copy ->
  (a c1) mod p = (a c2) mod p.
Proof. intros a c1 c2 H Hin. specialize (H _ Hin). cbn [fst snd] in H. exact H. Qed.

Ltac gates_tac :=
  let g := fresh "g" in let Hin := fresh "Hin" in
  intros g Hin; cbn in Hin;
  repeat (destruct Hin as [<-|Hin]; [vm_compute; reflexivity| ]);
  contradiction.
Ltac copy_tac :=
  let e := fresh "e" in let Hin := fresh "Hin" in
  intros e Hin; cbn in Hin;
  repeat (destruct Hin as [<-|Hin]; [vm_compute; reflexivity| ]);
  contradiction.

Definition gates_holdb (a:Assignment) (gs:list Expr) : bool :=
  forallb (fun g => Z.eqb ((eval a g) mod p) 0) gs.
Definition copy_holdsb (a:Assignment) (cp:list (Cell*Cell)) : bool :=
  forallb (fun e => Z.eqb ((a (fst e)) mod p) ((a (snd e)) mod p)) cp.

Lemma gates_holdb_sound : forall a gs, gates_holdb a gs = true -> gates_hold a gs.
Proof.
  intros a gs H g Hin.
  unfold gates_holdb in H. rewrite forallb_forall in H.
  specialize (H g Hin). apply Z.eqb_eq in H. exact H.
Qed.
Lemma copy_holdsb_sound : forall a cp, copy_holdsb a cp = true -> copy_holds a cp.
Proof.
  intros a cp H e Hin.
  unfold copy_holdsb in H. rewrite forallb_forall in H.
  specialize (H e Hin). apply Z.eqb_eq in H. exact H.
Qed.

Lemma in_copy_1 : In ((8%nat, 0%nat), (2000%nat, 0%nat)) deployed_copy.
Proof. apply (nth_error_In deployed_copy 0); vm_compute; reflexivity. Qed.
Lemma in_copy_2 : In ((9%nat, 0%nat), (2000%nat, 1%nat)) deployed_copy.
Proof. apply (nth_error_In deployed_copy 1); vm_compute; reflexivity. Qed.
Lemma in_copy_3 : In ((10%nat, 0%nat), (2000%nat, 2%nat)) deployed_copy.
Proof. apply (nth_error_In deployed_copy 2); vm_compute; reflexivity. Qed.
Lemma in_copy_4 : In ((11%nat, 0%nat), (2000%nat, 3%nat)) deployed_copy.
Proof. apply (nth_error_In deployed_copy 3); vm_compute; reflexivity. Qed.
Lemma in_copy_5 : In ((12%nat, 0%nat), (2000%nat, 4%nat)) deployed_copy.
Proof. apply (nth_error_In deployed_copy 4); vm_compute; reflexivity. Qed.
Lemma in_copy_6 : In ((13%nat, 0%nat), (2000%nat, 5%nat)) deployed_copy.
Proof. apply (nth_error_In deployed_copy 5); vm_compute; reflexivity. Qed.
Lemma in_copy_7 : In ((14%nat, 0%nat), (2000%nat, 6%nat)) deployed_copy.
Proof. apply (nth_error_In deployed_copy 6); vm_compute; reflexivity. Qed.
Lemma in_copy_8 : In ((15%nat, 0%nat), (2000%nat, 7%nat)) deployed_copy.
Proof. apply (nth_error_In deployed_copy 7); vm_compute; reflexivity. Qed.

Record Ports_bm_gen := mk_ports_bm_gen { }.
Definition intact_ports_bm_gen : Ports_bm_gen := mk_ports_bm_gen.

Definition RD_bm_gen (pts:Ports_bm_gen) (a:Assignment) : Prop :=
  (a (8%nat, 0%nat)) mod p = (a (2000%nat, 0%nat)) mod p /\
  (a (9%nat, 0%nat)) mod p = (a (2000%nat, 1%nat)) mod p /\
  (a (10%nat, 0%nat)) mod p = (a (2000%nat, 2%nat)) mod p /\
  (a (11%nat, 0%nat)) mod p = (a (2000%nat, 3%nat)) mod p /\
  (a (12%nat, 0%nat)) mod p = (a (2000%nat, 4%nat)) mod p /\
  (a (13%nat, 0%nat)) mod p = (a (2000%nat, 5%nat)) mod p /\
  (a (14%nat, 0%nat)) mod p = (a (2000%nat, 6%nat)) mod p /\
  (a (15%nat, 0%nat)) mod p = (a (2000%nat, 7%nat)) mod p.

Definition refinesD_bm_gen (m:CircuitModel) (pts:Ports_bm_gen) : Prop :=
  forall a, sat m a -> RD_bm_gen pts a.

Theorem deployed_refines_RD_bm_gen : refinesD_bm_gen deployed_model intact_ports_bm_gen.
Proof.
  unfold refinesD_bm_gen. intros a [Hg Hc].
  unfold RD_bm_gen. cbn [intact_ports_bm_gen].
  repeat split;
    try reflexivity;
    first [ exact (copy_get a _ _ Hc in_copy_1)
          | exact (copy_get a _ _ Hc in_copy_2)
          | exact (copy_get a _ _ Hc in_copy_3)
          | exact (copy_get a _ _ Hc in_copy_4)
          | exact (copy_get a _ _ Hc in_copy_5)
          | exact (copy_get a _ _ Hc in_copy_6)
          | exact (copy_get a _ _ Hc in_copy_7)
          | exact (copy_get a _ _ Hc in_copy_8) ].
Qed.
