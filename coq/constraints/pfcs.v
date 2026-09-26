(* SPDX-License-Identifier: Apache-2.0
   SPDX-FileCopyrightText: 2026 Next Ridge Solutions Ltd

   A Coq embedding of prime-field constraint systems (polynomials, constraints, and the satisfaction
   relation), following the PFCS formalism of A. Coglio, E. McCarthy and E. W. Smith, "Formal
   Verification of Zero-Knowledge Circuits", arXiv:2311.08858.

   Scope: these results bind the formal (Coq) layer only; the generated constraint model's fidelity to the circuit implementation, and the implementation itself, are outside them. *)

From Coq Require Import Init.Datatypes.
From Coq Require Import Lists.List.
From Coq Require Import Arith.PeanoNat.

Import ListNotations.

Record FieldOps (F : Type) : Type := {
  fzero : F;
  fone  : F;
  fadd  : F -> F -> F;
  fmul  : F -> F -> F;
  fneg  : F -> F;
  feqb  : F -> F -> bool
}.

Arguments fzero {F} _.
Arguments fone  {F} _.
Arguments fadd  {F} _ _ _.
Arguments fmul  {F} _ _ _.
Arguments fneg  {F} _ _.
Arguments feqb  {F} _ _ _.

Definition Var : Set := nat.
Definition ProcName : Set := nat.

Inductive Poly (F : Type) : Type :=
| PConst : F -> Poly F
| PVar   : Var -> Poly F
| PAdd   : Poly F -> Poly F -> Poly F
| PMul   : Poly F -> Poly F -> Poly F
| PNeg   : Poly F -> Poly F.

Arguments PConst {F} _.
Arguments PVar   {F} _.
Arguments PAdd   {F} _ _.
Arguments PMul   {F} _ _.
Arguments PNeg   {F} _.

Inductive Constraint (F : Type) : Type :=
| Eq     : Poly F -> Poly F -> Constraint F
| And    : Constraint F -> Constraint F -> Constraint F
| Exists : Var -> Constraint F -> Constraint F
| Call   : ProcName -> list (Poly F) -> Constraint F.

Arguments Eq     {F} _ _.
Arguments And    {F} _ _.
Arguments Exists {F} _ _.
Arguments Call   {F} _ _.

Record ProcDef (F : Type) : Type := {
  pd_name   : ProcName;
  pd_args   : list Var;
  pd_locals : list Var;
  pd_body   : Constraint F;
  pd_spec   : Constraint F
}.

Arguments pd_name   {F} _.
Arguments pd_args   {F} _.
Arguments pd_locals {F} _.
Arguments pd_body   {F} _.
Arguments pd_spec   {F} _.

Definition Program (F : Type) : Type := list (ProcName * ProcDef F).

Definition lookup_proc {F : Type} (prog : Program F) (n : ProcName)
  : option (ProcDef F) :=
  match find (fun kv => Nat.eqb (fst kv) n) prog with
  | Some (_, pd) => Some pd
  | None         => None
  end.

Definition Env (F : Type) : Type := Var -> option F.

Definition empty_env {F : Type} : Env F := fun _ => None.

Definition env_extend {F : Type} (e : Env F) (v : Var) (x : F) : Env F :=
  fun w => if Nat.eqb v w then Some x else e w.

Definition extend_pairs {F : Type} (e : Env F)
                        (pairs : list (Var * F)) : Env F :=
  fold_left (fun acc xv => env_extend acc (fst xv) (snd xv)) pairs e.

Definition arg_env {F : Type} (args : list Var) (vs : list F) : Env F :=
  extend_pairs empty_env (combine args vs).

Fixpoint eval_poly {F : Type} (ops : FieldOps F) (e : Env F) (p : Poly F)
  : option F :=
  match p with
  | PConst k    => Some k
  | PVar v      => e v
  | PAdd p1 p2  =>
      match eval_poly ops e p1, eval_poly ops e p2 with
      | Some v1, Some v2 => Some (fadd ops v1 v2)
      | _, _ => None
      end
  | PMul p1 p2  =>
      match eval_poly ops e p1, eval_poly ops e p2 with
      | Some v1, Some v2 => Some (fmul ops v1 v2)
      | _, _ => None
      end
  | PNeg p1     =>
      match eval_poly ops e p1 with
      | Some v => Some (fneg ops v)
      | None   => None
      end
  end.

Inductive satisfies {F : Type} (ops : FieldOps F) (prog : Program F)
  : Env F -> Constraint F -> Prop :=

| Sat_Eq : forall (e : Env F) (p q : Poly F) (v : F),
    eval_poly ops e p = Some v ->
    eval_poly ops e q = Some v ->
    satisfies ops prog e (Eq p q)

| Sat_And : forall (e : Env F) (c1 c2 : Constraint F),
    satisfies ops prog e c1 ->
    satisfies ops prog e c2 ->
    satisfies ops prog e (And c1 c2)

| Sat_Exists : forall (e : Env F) (x : Var) (c : Constraint F) (w : F),
    satisfies ops prog (env_extend e x w) c ->
    satisfies ops prog e (Exists x c)

| Sat_Call : forall (e : Env F) (name : ProcName) (args : list (Poly F))
                    (pd : ProcDef F) (vs : list F),
    lookup_proc prog name = Some pd ->
    map (eval_poly ops e) args = map (@Some F) vs ->
    satisfies ops prog (arg_env (pd_args pd) vs) (pd_spec pd) ->
    satisfies ops prog e (Call name args).
