(* SPDX-License-Identifier: Apache-2.0
   SPDX-FileCopyrightText: 2026 Next Ridge Solutions Ltd

   Each copy constraint is necessary: the model with any one of the eight copy constraints removed no
   longer refines the intended public interface (mutant_wcopy_1_not_refines and its seven siblings), shown
   by an explicit filling. bm_all_wires_closed_gen collects these facts with the full model's refinement.

   Scope: these results bind the formal (Coq) layer only; the generated constraint model's fidelity to the circuit implementation, and the implementation itself, are outside them. *)

From Coq Require Import ZArith List Lia. Import ListNotations. Open Scope Z_scope.
Require Import Generated.bm_model_gen.
Require Import Generated.bm_wires_gen.
Require Import Generated.bm_scaffold_gen.

Fixpoint expr_eqb (x y:Expr) : bool :=
  match x, y with
  | EConst a, EConst b       => Z.eqb a b
  | ECell a, ECell b         => cell_eqb a b
  | EAdd a1 a2, EAdd b1 b2   => andb (expr_eqb a1 b1) (expr_eqb a2 b2)
  | ESub a1 a2, ESub b1 b2   => andb (expr_eqb a1 b1) (expr_eqb a2 b2)
  | EMul a1 a2, EMul b1 b2   => andb (expr_eqb a1 b1) (expr_eqb a2 b2)
  | ENeg a, ENeg b           => expr_eqb a b
  | EScaled a z1, EScaled b z2 => andb (expr_eqb a b) (Z.eqb z1 z2)
  | _, _                     => false
  end.

Definition cut_edge_bm (e:Cell*Cell) : list (Cell*Cell) :=
  filter (fun f => negb (cellpair_eqb f e)) deployed_copy.
Definition cut_copy_model_bm (e:Cell*Cell) : CircuitModel :=
  mk_model p deployed_gates (cut_edge_bm e).

Definition no_gate_reads_bm (t:Cell) : Prop := forall g, In g deployed_gates -> reads_b t g = false.
Ltac noreads_tac :=
  let g := fresh "g" in let Hin := fresh "Hin" in
  intros g Hin; cbn in Hin;
  repeat (destruct Hin as [<-|Hin]; [vm_compute; reflexivity| ]);
  contradiction.

Definition wit_honest_bm : Assignment := fun c =>
  if cell_eqb c (0%nat, 0%nat) then 18446744073709551615 else
  if cell_eqb c (1%nat, 0%nat) then 18446744073709551615 else
  if cell_eqb c (2%nat, 0%nat) then 18446744073709551615 else
  if cell_eqb c (3%nat, 0%nat) then 18446744073709551615 else
  if cell_eqb c (4%nat, 0%nat) then 18446744073709551615 else
  if cell_eqb c (5%nat, 0%nat) then 18446744073709551615 else
  if cell_eqb c (6%nat, 0%nat) then 18446744073709551615 else
  if cell_eqb c (7%nat, 0%nat) then 18446744073709551615 else
  if cell_eqb c (8%nat, 0%nat) then 1 else
  if cell_eqb c (12%nat, 0%nat) then 18446744073709551614 else
  if cell_eqb c (13%nat, 0%nat) then 18446744073709551615 else
  if cell_eqb c (14%nat, 0%nat) then 18446744073709551615 else
  if cell_eqb c (15%nat, 0%nat) then 18446744073709551615 else
  if cell_eqb c (16%nat, 0%nat) then 18446744073709551614 else
  if cell_eqb c (17%nat, 0%nat) then 36893488147419103229 else
  if cell_eqb c (18%nat, 0%nat) then 55340232221128654844 else
  if cell_eqb c (19%nat, 0%nat) then 73786976294838206459 else
  if cell_eqb c (20%nat, 0%nat) then 55340232221128654845 else
  if cell_eqb c (21%nat, 0%nat) then 36893488147419103230 else
  if cell_eqb c (22%nat, 0%nat) then 18446744073709551615 else
  if cell_eqb c (23%nat, 0%nat) then 1 else
  if cell_eqb c (280%nat, 0%nat) then 1 else
  if cell_eqb c (281%nat, 0%nat) then 1 else
  if cell_eqb c (282%nat, 0%nat) then 1 else
  if cell_eqb c (283%nat, 0%nat) then 1 else
  if cell_eqb c (284%nat, 0%nat) then 1 else
  if cell_eqb c (285%nat, 0%nat) then 1 else
  if cell_eqb c (286%nat, 0%nat) then 1 else
  if cell_eqb c (287%nat, 0%nat) then 1 else
  if cell_eqb c (288%nat, 0%nat) then 1 else
  if cell_eqb c (289%nat, 0%nat) then 1 else
  if cell_eqb c (290%nat, 0%nat) then 1 else
  if cell_eqb c (291%nat, 0%nat) then 1 else
  if cell_eqb c (292%nat, 0%nat) then 1 else
  if cell_eqb c (293%nat, 0%nat) then 1 else
  if cell_eqb c (294%nat, 0%nat) then 1 else
  if cell_eqb c (295%nat, 0%nat) then 1 else
  if cell_eqb c (296%nat, 0%nat) then 1 else
  if cell_eqb c (297%nat, 0%nat) then 1 else
  if cell_eqb c (298%nat, 0%nat) then 1 else
  if cell_eqb c (299%nat, 0%nat) then 1 else
  if cell_eqb c (300%nat, 0%nat) then 1 else
  if cell_eqb c (301%nat, 0%nat) then 1 else
  if cell_eqb c (302%nat, 0%nat) then 1 else
  if cell_eqb c (303%nat, 0%nat) then 1 else
  if cell_eqb c (304%nat, 0%nat) then 1 else
  if cell_eqb c (305%nat, 0%nat) then 1 else
  if cell_eqb c (306%nat, 0%nat) then 1 else
  if cell_eqb c (307%nat, 0%nat) then 1 else
  if cell_eqb c (308%nat, 0%nat) then 1 else
  if cell_eqb c (309%nat, 0%nat) then 1 else
  if cell_eqb c (310%nat, 0%nat) then 1 else
  if cell_eqb c (311%nat, 0%nat) then 1 else
  if cell_eqb c (312%nat, 0%nat) then 1 else
  if cell_eqb c (313%nat, 0%nat) then 1 else
  if cell_eqb c (314%nat, 0%nat) then 1 else
  if cell_eqb c (315%nat, 0%nat) then 1 else
  if cell_eqb c (316%nat, 0%nat) then 1 else
  if cell_eqb c (317%nat, 0%nat) then 1 else
  if cell_eqb c (318%nat, 0%nat) then 1 else
  if cell_eqb c (319%nat, 0%nat) then 1 else
  if cell_eqb c (320%nat, 0%nat) then 1 else
  if cell_eqb c (321%nat, 0%nat) then 1 else
  if cell_eqb c (322%nat, 0%nat) then 1 else
  if cell_eqb c (323%nat, 0%nat) then 1 else
  if cell_eqb c (324%nat, 0%nat) then 1 else
  if cell_eqb c (325%nat, 0%nat) then 1 else
  if cell_eqb c (326%nat, 0%nat) then 1 else
  if cell_eqb c (327%nat, 0%nat) then 1 else
  if cell_eqb c (328%nat, 0%nat) then 1 else
  if cell_eqb c (329%nat, 0%nat) then 1 else
  if cell_eqb c (330%nat, 0%nat) then 1 else
  if cell_eqb c (331%nat, 0%nat) then 1 else
  if cell_eqb c (332%nat, 0%nat) then 1 else
  if cell_eqb c (333%nat, 0%nat) then 1 else
  if cell_eqb c (334%nat, 0%nat) then 1 else
  if cell_eqb c (335%nat, 0%nat) then 1 else
  if cell_eqb c (336%nat, 0%nat) then 1 else
  if cell_eqb c (337%nat, 0%nat) then 1 else
  if cell_eqb c (338%nat, 0%nat) then 1 else
  if cell_eqb c (339%nat, 0%nat) then 1 else
  if cell_eqb c (340%nat, 0%nat) then 1 else
  if cell_eqb c (341%nat, 0%nat) then 1 else
  if cell_eqb c (342%nat, 0%nat) then 1 else
  if cell_eqb c (343%nat, 0%nat) then 1 else
  if cell_eqb c (344%nat, 0%nat) then 1 else
  if cell_eqb c (345%nat, 0%nat) then 1 else
  if cell_eqb c (346%nat, 0%nat) then 1 else
  if cell_eqb c (347%nat, 0%nat) then 1 else
  if cell_eqb c (348%nat, 0%nat) then 1 else
  if cell_eqb c (349%nat, 0%nat) then 1 else
  if cell_eqb c (350%nat, 0%nat) then 1 else
  if cell_eqb c (351%nat, 0%nat) then 1 else
  if cell_eqb c (352%nat, 0%nat) then 1 else
  if cell_eqb c (353%nat, 0%nat) then 1 else
  if cell_eqb c (354%nat, 0%nat) then 1 else
  if cell_eqb c (355%nat, 0%nat) then 1 else
  if cell_eqb c (356%nat, 0%nat) then 1 else
  if cell_eqb c (357%nat, 0%nat) then 1 else
  if cell_eqb c (358%nat, 0%nat) then 1 else
  if cell_eqb c (359%nat, 0%nat) then 1 else
  if cell_eqb c (360%nat, 0%nat) then 1 else
  if cell_eqb c (361%nat, 0%nat) then 1 else
  if cell_eqb c (362%nat, 0%nat) then 1 else
  if cell_eqb c (363%nat, 0%nat) then 1 else
  if cell_eqb c (364%nat, 0%nat) then 1 else
  if cell_eqb c (365%nat, 0%nat) then 1 else
  if cell_eqb c (366%nat, 0%nat) then 1 else
  if cell_eqb c (367%nat, 0%nat) then 1 else
  if cell_eqb c (368%nat, 0%nat) then 1 else
  if cell_eqb c (369%nat, 0%nat) then 1 else
  if cell_eqb c (370%nat, 0%nat) then 1 else
  if cell_eqb c (371%nat, 0%nat) then 1 else
  if cell_eqb c (372%nat, 0%nat) then 1 else
  if cell_eqb c (373%nat, 0%nat) then 1 else
  if cell_eqb c (374%nat, 0%nat) then 1 else
  if cell_eqb c (375%nat, 0%nat) then 1 else
  if cell_eqb c (376%nat, 0%nat) then 1 else
  if cell_eqb c (377%nat, 0%nat) then 1 else
  if cell_eqb c (378%nat, 0%nat) then 1 else
  if cell_eqb c (379%nat, 0%nat) then 1 else
  if cell_eqb c (380%nat, 0%nat) then 1 else
  if cell_eqb c (381%nat, 0%nat) then 1 else
  if cell_eqb c (382%nat, 0%nat) then 1 else
  if cell_eqb c (383%nat, 0%nat) then 1 else
  if cell_eqb c (384%nat, 0%nat) then 1 else
  if cell_eqb c (385%nat, 0%nat) then 1 else
  if cell_eqb c (386%nat, 0%nat) then 1 else
  if cell_eqb c (387%nat, 0%nat) then 1 else
  if cell_eqb c (388%nat, 0%nat) then 1 else
  if cell_eqb c (389%nat, 0%nat) then 1 else
  if cell_eqb c (390%nat, 0%nat) then 1 else
  if cell_eqb c (391%nat, 0%nat) then 1 else
  if cell_eqb c (392%nat, 0%nat) then 1 else
  if cell_eqb c (393%nat, 0%nat) then 1 else
  if cell_eqb c (394%nat, 0%nat) then 1 else
  if cell_eqb c (395%nat, 0%nat) then 1 else
  if cell_eqb c (396%nat, 0%nat) then 1 else
  if cell_eqb c (397%nat, 0%nat) then 1 else
  if cell_eqb c (398%nat, 0%nat) then 1 else
  if cell_eqb c (399%nat, 0%nat) then 1 else
  if cell_eqb c (400%nat, 0%nat) then 1 else
  if cell_eqb c (401%nat, 0%nat) then 1 else
  if cell_eqb c (402%nat, 0%nat) then 1 else
  if cell_eqb c (403%nat, 0%nat) then 1 else
  if cell_eqb c (404%nat, 0%nat) then 1 else
  if cell_eqb c (405%nat, 0%nat) then 1 else
  if cell_eqb c (406%nat, 0%nat) then 1 else
  if cell_eqb c (407%nat, 0%nat) then 1 else
  if cell_eqb c (408%nat, 0%nat) then 1 else
  if cell_eqb c (409%nat, 0%nat) then 1 else
  if cell_eqb c (410%nat, 0%nat) then 1 else
  if cell_eqb c (411%nat, 0%nat) then 1 else
  if cell_eqb c (412%nat, 0%nat) then 1 else
  if cell_eqb c (413%nat, 0%nat) then 1 else
  if cell_eqb c (414%nat, 0%nat) then 1 else
  if cell_eqb c (415%nat, 0%nat) then 1 else
  if cell_eqb c (416%nat, 0%nat) then 1 else
  if cell_eqb c (417%nat, 0%nat) then 1 else
  if cell_eqb c (418%nat, 0%nat) then 1 else
  if cell_eqb c (419%nat, 0%nat) then 1 else
  if cell_eqb c (420%nat, 0%nat) then 1 else
  if cell_eqb c (421%nat, 0%nat) then 1 else
  if cell_eqb c (422%nat, 0%nat) then 1 else
  if cell_eqb c (423%nat, 0%nat) then 1 else
  if cell_eqb c (424%nat, 0%nat) then 1 else
  if cell_eqb c (425%nat, 0%nat) then 1 else
  if cell_eqb c (426%nat, 0%nat) then 1 else
  if cell_eqb c (427%nat, 0%nat) then 1 else
  if cell_eqb c (428%nat, 0%nat) then 1 else
  if cell_eqb c (429%nat, 0%nat) then 1 else
  if cell_eqb c (430%nat, 0%nat) then 1 else
  if cell_eqb c (431%nat, 0%nat) then 1 else
  if cell_eqb c (432%nat, 0%nat) then 1 else
  if cell_eqb c (433%nat, 0%nat) then 1 else
  if cell_eqb c (434%nat, 0%nat) then 1 else
  if cell_eqb c (435%nat, 0%nat) then 1 else
  if cell_eqb c (436%nat, 0%nat) then 1 else
  if cell_eqb c (437%nat, 0%nat) then 1 else
  if cell_eqb c (438%nat, 0%nat) then 1 else
  if cell_eqb c (439%nat, 0%nat) then 1 else
  if cell_eqb c (440%nat, 0%nat) then 1 else
  if cell_eqb c (441%nat, 0%nat) then 1 else
  if cell_eqb c (442%nat, 0%nat) then 1 else
  if cell_eqb c (443%nat, 0%nat) then 1 else
  if cell_eqb c (444%nat, 0%nat) then 1 else
  if cell_eqb c (445%nat, 0%nat) then 1 else
  if cell_eqb c (446%nat, 0%nat) then 1 else
  if cell_eqb c (447%nat, 0%nat) then 1 else
  if cell_eqb c (448%nat, 0%nat) then 1 else
  if cell_eqb c (449%nat, 0%nat) then 1 else
  if cell_eqb c (450%nat, 0%nat) then 1 else
  if cell_eqb c (451%nat, 0%nat) then 1 else
  if cell_eqb c (452%nat, 0%nat) then 1 else
  if cell_eqb c (453%nat, 0%nat) then 1 else
  if cell_eqb c (454%nat, 0%nat) then 1 else
  if cell_eqb c (455%nat, 0%nat) then 1 else
  if cell_eqb c (456%nat, 0%nat) then 1 else
  if cell_eqb c (457%nat, 0%nat) then 1 else
  if cell_eqb c (458%nat, 0%nat) then 1 else
  if cell_eqb c (459%nat, 0%nat) then 1 else
  if cell_eqb c (460%nat, 0%nat) then 1 else
  if cell_eqb c (461%nat, 0%nat) then 1 else
  if cell_eqb c (462%nat, 0%nat) then 1 else
  if cell_eqb c (463%nat, 0%nat) then 1 else
  if cell_eqb c (464%nat, 0%nat) then 1 else
  if cell_eqb c (465%nat, 0%nat) then 1 else
  if cell_eqb c (466%nat, 0%nat) then 1 else
  if cell_eqb c (467%nat, 0%nat) then 1 else
  if cell_eqb c (468%nat, 0%nat) then 1 else
  if cell_eqb c (469%nat, 0%nat) then 1 else
  if cell_eqb c (470%nat, 0%nat) then 1 else
  if cell_eqb c (471%nat, 0%nat) then 1 else
  if cell_eqb c (472%nat, 0%nat) then 1 else
  if cell_eqb c (473%nat, 0%nat) then 1 else
  if cell_eqb c (474%nat, 0%nat) then 1 else
  if cell_eqb c (475%nat, 0%nat) then 1 else
  if cell_eqb c (476%nat, 0%nat) then 1 else
  if cell_eqb c (477%nat, 0%nat) then 1 else
  if cell_eqb c (478%nat, 0%nat) then 1 else
  if cell_eqb c (479%nat, 0%nat) then 1 else
  if cell_eqb c (480%nat, 0%nat) then 1 else
  if cell_eqb c (481%nat, 0%nat) then 1 else
  if cell_eqb c (482%nat, 0%nat) then 1 else
  if cell_eqb c (483%nat, 0%nat) then 1 else
  if cell_eqb c (484%nat, 0%nat) then 1 else
  if cell_eqb c (485%nat, 0%nat) then 1 else
  if cell_eqb c (486%nat, 0%nat) then 1 else
  if cell_eqb c (487%nat, 0%nat) then 1 else
  if cell_eqb c (488%nat, 0%nat) then 1 else
  if cell_eqb c (489%nat, 0%nat) then 1 else
  if cell_eqb c (490%nat, 0%nat) then 1 else
  if cell_eqb c (491%nat, 0%nat) then 1 else
  if cell_eqb c (492%nat, 0%nat) then 1 else
  if cell_eqb c (493%nat, 0%nat) then 1 else
  if cell_eqb c (494%nat, 0%nat) then 1 else
  if cell_eqb c (495%nat, 0%nat) then 1 else
  if cell_eqb c (496%nat, 0%nat) then 1 else
  if cell_eqb c (497%nat, 0%nat) then 1 else
  if cell_eqb c (498%nat, 0%nat) then 1 else
  if cell_eqb c (499%nat, 0%nat) then 1 else
  if cell_eqb c (500%nat, 0%nat) then 1 else
  if cell_eqb c (501%nat, 0%nat) then 1 else
  if cell_eqb c (502%nat, 0%nat) then 1 else
  if cell_eqb c (503%nat, 0%nat) then 1 else
  if cell_eqb c (504%nat, 0%nat) then 1 else
  if cell_eqb c (505%nat, 0%nat) then 1 else
  if cell_eqb c (506%nat, 0%nat) then 1 else
  if cell_eqb c (507%nat, 0%nat) then 1 else
  if cell_eqb c (508%nat, 0%nat) then 1 else
  if cell_eqb c (509%nat, 0%nat) then 1 else
  if cell_eqb c (510%nat, 0%nat) then 1 else
  if cell_eqb c (511%nat, 0%nat) then 1 else
  if cell_eqb c (512%nat, 0%nat) then 1 else
  if cell_eqb c (513%nat, 0%nat) then 1 else
  if cell_eqb c (514%nat, 0%nat) then 1 else
  if cell_eqb c (515%nat, 0%nat) then 1 else
  if cell_eqb c (516%nat, 0%nat) then 1 else
  if cell_eqb c (517%nat, 0%nat) then 1 else
  if cell_eqb c (518%nat, 0%nat) then 1 else
  if cell_eqb c (519%nat, 0%nat) then 1 else
  if cell_eqb c (520%nat, 0%nat) then 1 else
  if cell_eqb c (521%nat, 0%nat) then 1 else
  if cell_eqb c (522%nat, 0%nat) then 1 else
  if cell_eqb c (523%nat, 0%nat) then 1 else
  if cell_eqb c (524%nat, 0%nat) then 1 else
  if cell_eqb c (525%nat, 0%nat) then 1 else
  if cell_eqb c (526%nat, 0%nat) then 1 else
  if cell_eqb c (527%nat, 0%nat) then 1 else
  if cell_eqb c (528%nat, 0%nat) then 1 else
  if cell_eqb c (529%nat, 0%nat) then 1 else
  if cell_eqb c (530%nat, 0%nat) then 1 else
  if cell_eqb c (531%nat, 0%nat) then 1 else
  if cell_eqb c (532%nat, 0%nat) then 1 else
  if cell_eqb c (533%nat, 0%nat) then 1 else
  if cell_eqb c (534%nat, 0%nat) then 1 else
  if cell_eqb c (536%nat, 0%nat) then 1 else
  if cell_eqb c (537%nat, 0%nat) then 1 else
  if cell_eqb c (538%nat, 0%nat) then 1 else
  if cell_eqb c (539%nat, 0%nat) then 1 else
  if cell_eqb c (540%nat, 0%nat) then 1 else
  if cell_eqb c (541%nat, 0%nat) then 1 else
  if cell_eqb c (542%nat, 0%nat) then 1 else
  if cell_eqb c (543%nat, 0%nat) then 1 else
  if cell_eqb c (544%nat, 0%nat) then 1 else
  if cell_eqb c (545%nat, 0%nat) then 1 else
  if cell_eqb c (546%nat, 0%nat) then 1 else
  if cell_eqb c (547%nat, 0%nat) then 1 else
  if cell_eqb c (548%nat, 0%nat) then 1 else
  if cell_eqb c (549%nat, 0%nat) then 1 else
  if cell_eqb c (550%nat, 0%nat) then 1 else
  if cell_eqb c (551%nat, 0%nat) then 1 else
  if cell_eqb c (552%nat, 0%nat) then 1 else
  if cell_eqb c (553%nat, 0%nat) then 1 else
  if cell_eqb c (554%nat, 0%nat) then 1 else
  if cell_eqb c (555%nat, 0%nat) then 1 else
  if cell_eqb c (556%nat, 0%nat) then 1 else
  if cell_eqb c (557%nat, 0%nat) then 1 else
  if cell_eqb c (558%nat, 0%nat) then 1 else
  if cell_eqb c (559%nat, 0%nat) then 1 else
  if cell_eqb c (560%nat, 0%nat) then 1 else
  if cell_eqb c (561%nat, 0%nat) then 1 else
  if cell_eqb c (562%nat, 0%nat) then 1 else
  if cell_eqb c (563%nat, 0%nat) then 1 else
  if cell_eqb c (564%nat, 0%nat) then 1 else
  if cell_eqb c (565%nat, 0%nat) then 1 else
  if cell_eqb c (566%nat, 0%nat) then 1 else
  if cell_eqb c (567%nat, 0%nat) then 1 else
  if cell_eqb c (568%nat, 0%nat) then 1 else
  if cell_eqb c (569%nat, 0%nat) then 1 else
  if cell_eqb c (570%nat, 0%nat) then 1 else
  if cell_eqb c (571%nat, 0%nat) then 1 else
  if cell_eqb c (572%nat, 0%nat) then 1 else
  if cell_eqb c (573%nat, 0%nat) then 1 else
  if cell_eqb c (574%nat, 0%nat) then 1 else
  if cell_eqb c (575%nat, 0%nat) then 1 else
  if cell_eqb c (576%nat, 0%nat) then 1 else
  if cell_eqb c (577%nat, 0%nat) then 1 else
  if cell_eqb c (578%nat, 0%nat) then 1 else
  if cell_eqb c (579%nat, 0%nat) then 1 else
  if cell_eqb c (580%nat, 0%nat) then 1 else
  if cell_eqb c (581%nat, 0%nat) then 1 else
  if cell_eqb c (582%nat, 0%nat) then 1 else
  if cell_eqb c (583%nat, 0%nat) then 1 else
  if cell_eqb c (584%nat, 0%nat) then 1 else
  if cell_eqb c (585%nat, 0%nat) then 1 else
  if cell_eqb c (586%nat, 0%nat) then 1 else
  if cell_eqb c (587%nat, 0%nat) then 1 else
  if cell_eqb c (588%nat, 0%nat) then 1 else
  if cell_eqb c (589%nat, 0%nat) then 1 else
  if cell_eqb c (590%nat, 0%nat) then 1 else
  if cell_eqb c (591%nat, 0%nat) then 1 else
  if cell_eqb c (592%nat, 0%nat) then 1 else
  if cell_eqb c (593%nat, 0%nat) then 1 else
  if cell_eqb c (594%nat, 0%nat) then 1 else
  if cell_eqb c (595%nat, 0%nat) then 1 else
  if cell_eqb c (596%nat, 0%nat) then 1 else
  if cell_eqb c (597%nat, 0%nat) then 1 else
  if cell_eqb c (598%nat, 0%nat) then 1 else
  if cell_eqb c (601%nat, 0%nat) then 1 else
  if cell_eqb c (603%nat, 0%nat) then 1 else
  if cell_eqb c (604%nat, 0%nat) then 1 else
  if cell_eqb c (605%nat, 0%nat) then 1 else
  if cell_eqb c (606%nat, 0%nat) then 1 else
  if cell_eqb c (607%nat, 0%nat) then 1 else
  if cell_eqb c (608%nat, 0%nat) then 1 else
  if cell_eqb c (609%nat, 0%nat) then 1 else
  if cell_eqb c (610%nat, 0%nat) then 1 else
  if cell_eqb c (611%nat, 0%nat) then 1 else
  if cell_eqb c (612%nat, 0%nat) then 1 else
  if cell_eqb c (613%nat, 0%nat) then 1 else
  if cell_eqb c (614%nat, 0%nat) then 1 else
  if cell_eqb c (615%nat, 0%nat) then 1 else
  if cell_eqb c (616%nat, 0%nat) then 1 else
  if cell_eqb c (617%nat, 0%nat) then 1 else
  if cell_eqb c (618%nat, 0%nat) then 1 else
  if cell_eqb c (619%nat, 0%nat) then 1 else
  if cell_eqb c (620%nat, 0%nat) then 1 else
  if cell_eqb c (621%nat, 0%nat) then 1 else
  if cell_eqb c (622%nat, 0%nat) then 1 else
  if cell_eqb c (623%nat, 0%nat) then 1 else
  if cell_eqb c (624%nat, 0%nat) then 1 else
  if cell_eqb c (625%nat, 0%nat) then 1 else
  if cell_eqb c (626%nat, 0%nat) then 1 else
  if cell_eqb c (627%nat, 0%nat) then 1 else
  if cell_eqb c (628%nat, 0%nat) then 1 else
  if cell_eqb c (629%nat, 0%nat) then 1 else
  if cell_eqb c (630%nat, 0%nat) then 1 else
  if cell_eqb c (631%nat, 0%nat) then 1 else
  if cell_eqb c (632%nat, 0%nat) then 1 else
  if cell_eqb c (633%nat, 0%nat) then 1 else
  if cell_eqb c (634%nat, 0%nat) then 1 else
  if cell_eqb c (635%nat, 0%nat) then 1 else
  if cell_eqb c (636%nat, 0%nat) then 1 else
  if cell_eqb c (637%nat, 0%nat) then 1 else
  if cell_eqb c (638%nat, 0%nat) then 1 else
  if cell_eqb c (639%nat, 0%nat) then 1 else
  if cell_eqb c (640%nat, 0%nat) then 1 else
  if cell_eqb c (641%nat, 0%nat) then 1 else
  if cell_eqb c (642%nat, 0%nat) then 1 else
  if cell_eqb c (643%nat, 0%nat) then 1 else
  if cell_eqb c (644%nat, 0%nat) then 1 else
  if cell_eqb c (645%nat, 0%nat) then 1 else
  if cell_eqb c (646%nat, 0%nat) then 1 else
  if cell_eqb c (647%nat, 0%nat) then 1 else
  if cell_eqb c (648%nat, 0%nat) then 1 else
  if cell_eqb c (649%nat, 0%nat) then 1 else
  if cell_eqb c (650%nat, 0%nat) then 1 else
  if cell_eqb c (651%nat, 0%nat) then 1 else
  if cell_eqb c (652%nat, 0%nat) then 1 else
  if cell_eqb c (653%nat, 0%nat) then 1 else
  if cell_eqb c (654%nat, 0%nat) then 1 else
  if cell_eqb c (655%nat, 0%nat) then 1 else
  if cell_eqb c (656%nat, 0%nat) then 1 else
  if cell_eqb c (657%nat, 0%nat) then 1 else
  if cell_eqb c (658%nat, 0%nat) then 1 else
  if cell_eqb c (659%nat, 0%nat) then 1 else
  if cell_eqb c (660%nat, 0%nat) then 1 else
  if cell_eqb c (661%nat, 0%nat) then 1 else
  if cell_eqb c (662%nat, 0%nat) then 1 else
  if cell_eqb c (663%nat, 0%nat) then 1 else
  if cell_eqb c (664%nat, 0%nat) then 1 else
  if cell_eqb c (665%nat, 0%nat) then 1 else
  if cell_eqb c (669%nat, 0%nat) then 1 else
  if cell_eqb c (670%nat, 0%nat) then 1 else
  if cell_eqb c (671%nat, 0%nat) then 1 else
  if cell_eqb c (672%nat, 0%nat) then 1 else
  if cell_eqb c (673%nat, 0%nat) then 1 else
  if cell_eqb c (674%nat, 0%nat) then 1 else
  if cell_eqb c (675%nat, 0%nat) then 1 else
  if cell_eqb c (676%nat, 0%nat) then 1 else
  if cell_eqb c (677%nat, 0%nat) then 1 else
  if cell_eqb c (678%nat, 0%nat) then 1 else
  if cell_eqb c (679%nat, 0%nat) then 1 else
  if cell_eqb c (680%nat, 0%nat) then 1 else
  if cell_eqb c (681%nat, 0%nat) then 1 else
  if cell_eqb c (682%nat, 0%nat) then 1 else
  if cell_eqb c (683%nat, 0%nat) then 1 else
  if cell_eqb c (684%nat, 0%nat) then 1 else
  if cell_eqb c (685%nat, 0%nat) then 1 else
  if cell_eqb c (686%nat, 0%nat) then 1 else
  if cell_eqb c (687%nat, 0%nat) then 1 else
  if cell_eqb c (688%nat, 0%nat) then 1 else
  if cell_eqb c (689%nat, 0%nat) then 1 else
  if cell_eqb c (690%nat, 0%nat) then 1 else
  if cell_eqb c (691%nat, 0%nat) then 1 else
  if cell_eqb c (692%nat, 0%nat) then 1 else
  if cell_eqb c (693%nat, 0%nat) then 1 else
  if cell_eqb c (694%nat, 0%nat) then 1 else
  if cell_eqb c (695%nat, 0%nat) then 1 else
  if cell_eqb c (696%nat, 0%nat) then 1 else
  if cell_eqb c (697%nat, 0%nat) then 1 else
  if cell_eqb c (698%nat, 0%nat) then 1 else
  if cell_eqb c (699%nat, 0%nat) then 1 else
  if cell_eqb c (700%nat, 0%nat) then 1 else
  if cell_eqb c (701%nat, 0%nat) then 1 else
  if cell_eqb c (702%nat, 0%nat) then 1 else
  if cell_eqb c (703%nat, 0%nat) then 1 else
  if cell_eqb c (704%nat, 0%nat) then 1 else
  if cell_eqb c (705%nat, 0%nat) then 1 else
  if cell_eqb c (706%nat, 0%nat) then 1 else
  if cell_eqb c (707%nat, 0%nat) then 1 else
  if cell_eqb c (708%nat, 0%nat) then 1 else
  if cell_eqb c (709%nat, 0%nat) then 1 else
  if cell_eqb c (710%nat, 0%nat) then 1 else
  if cell_eqb c (711%nat, 0%nat) then 1 else
  if cell_eqb c (712%nat, 0%nat) then 1 else
  if cell_eqb c (713%nat, 0%nat) then 1 else
  if cell_eqb c (714%nat, 0%nat) then 1 else
  if cell_eqb c (715%nat, 0%nat) then 1 else
  if cell_eqb c (716%nat, 0%nat) then 1 else
  if cell_eqb c (717%nat, 0%nat) then 1 else
  if cell_eqb c (718%nat, 0%nat) then 1 else
  if cell_eqb c (719%nat, 0%nat) then 1 else
  if cell_eqb c (720%nat, 0%nat) then 1 else
  if cell_eqb c (721%nat, 0%nat) then 1 else
  if cell_eqb c (722%nat, 0%nat) then 1 else
  if cell_eqb c (723%nat, 0%nat) then 1 else
  if cell_eqb c (724%nat, 0%nat) then 1 else
  if cell_eqb c (725%nat, 0%nat) then 1 else
  if cell_eqb c (726%nat, 0%nat) then 1 else
  if cell_eqb c (727%nat, 0%nat) then 1 else
  if cell_eqb c (728%nat, 0%nat) then 1 else
  if cell_eqb c (729%nat, 0%nat) then 1 else
  if cell_eqb c (730%nat, 0%nat) then 1 else
  if cell_eqb c (732%nat, 0%nat) then 1 else
  if cell_eqb c (733%nat, 0%nat) then 1 else
  if cell_eqb c (734%nat, 0%nat) then 1 else
  if cell_eqb c (736%nat, 0%nat) then 1 else
  if cell_eqb c (737%nat, 0%nat) then 1 else
  if cell_eqb c (738%nat, 0%nat) then 1 else
  if cell_eqb c (739%nat, 0%nat) then 1 else
  if cell_eqb c (740%nat, 0%nat) then 1 else
  if cell_eqb c (741%nat, 0%nat) then 1 else
  if cell_eqb c (742%nat, 0%nat) then 1 else
  if cell_eqb c (743%nat, 0%nat) then 1 else
  if cell_eqb c (744%nat, 0%nat) then 1 else
  if cell_eqb c (745%nat, 0%nat) then 1 else
  if cell_eqb c (746%nat, 0%nat) then 1 else
  if cell_eqb c (747%nat, 0%nat) then 1 else
  if cell_eqb c (748%nat, 0%nat) then 1 else
  if cell_eqb c (749%nat, 0%nat) then 1 else
  if cell_eqb c (750%nat, 0%nat) then 1 else
  if cell_eqb c (751%nat, 0%nat) then 1 else
  if cell_eqb c (752%nat, 0%nat) then 1 else
  if cell_eqb c (753%nat, 0%nat) then 1 else
  if cell_eqb c (754%nat, 0%nat) then 1 else
  if cell_eqb c (755%nat, 0%nat) then 1 else
  if cell_eqb c (756%nat, 0%nat) then 1 else
  if cell_eqb c (757%nat, 0%nat) then 1 else
  if cell_eqb c (758%nat, 0%nat) then 1 else
  if cell_eqb c (759%nat, 0%nat) then 1 else
  if cell_eqb c (760%nat, 0%nat) then 1 else
  if cell_eqb c (761%nat, 0%nat) then 1 else
  if cell_eqb c (762%nat, 0%nat) then 1 else
  if cell_eqb c (763%nat, 0%nat) then 1 else
  if cell_eqb c (764%nat, 0%nat) then 1 else
  if cell_eqb c (765%nat, 0%nat) then 1 else
  if cell_eqb c (766%nat, 0%nat) then 1 else
  if cell_eqb c (767%nat, 0%nat) then 1 else
  if cell_eqb c (768%nat, 0%nat) then 1 else
  if cell_eqb c (769%nat, 0%nat) then 1 else
  if cell_eqb c (770%nat, 0%nat) then 1 else
  if cell_eqb c (771%nat, 0%nat) then 1 else
  if cell_eqb c (772%nat, 0%nat) then 1 else
  if cell_eqb c (773%nat, 0%nat) then 1 else
  if cell_eqb c (774%nat, 0%nat) then 1 else
  if cell_eqb c (775%nat, 0%nat) then 1 else
  if cell_eqb c (776%nat, 0%nat) then 1 else
  if cell_eqb c (777%nat, 0%nat) then 1 else
  if cell_eqb c (778%nat, 0%nat) then 1 else
  if cell_eqb c (779%nat, 0%nat) then 1 else
  if cell_eqb c (780%nat, 0%nat) then 1 else
  if cell_eqb c (781%nat, 0%nat) then 1 else
  if cell_eqb c (782%nat, 0%nat) then 1 else
  if cell_eqb c (783%nat, 0%nat) then 1 else
  if cell_eqb c (784%nat, 0%nat) then 1 else
  if cell_eqb c (785%nat, 0%nat) then 1 else
  if cell_eqb c (786%nat, 0%nat) then 1 else
  if cell_eqb c (787%nat, 0%nat) then 1 else
  if cell_eqb c (788%nat, 0%nat) then 1 else
  if cell_eqb c (789%nat, 0%nat) then 1 else
  if cell_eqb c (790%nat, 0%nat) then 1 else
  if cell_eqb c (791%nat, 0%nat) then 1 else
  if cell_eqb c (792%nat, 0%nat) then 1 else
  if cell_eqb c (793%nat, 0%nat) then 1 else
  if cell_eqb c (794%nat, 0%nat) then 1 else
  if cell_eqb c (795%nat, 0%nat) then 1 else
  if cell_eqb c (796%nat, 0%nat) then 1 else
  if cell_eqb c (797%nat, 0%nat) then 1 else
  if cell_eqb c (798%nat, 0%nat) then 1 else
  if cell_eqb c (799%nat, 0%nat) then 1 else
  if cell_eqb c (801%nat, 0%nat) then 1 else
  if cell_eqb c (802%nat, 0%nat) then 1 else
  if cell_eqb c (803%nat, 0%nat) then 1 else
  if cell_eqb c (804%nat, 0%nat) then 1 else
  if cell_eqb c (805%nat, 0%nat) then 1 else
  if cell_eqb c (806%nat, 0%nat) then 1 else
  if cell_eqb c (807%nat, 0%nat) then 1 else
  if cell_eqb c (808%nat, 0%nat) then 1 else
  if cell_eqb c (809%nat, 0%nat) then 1 else
  if cell_eqb c (810%nat, 0%nat) then 1 else
  if cell_eqb c (811%nat, 0%nat) then 1 else
  if cell_eqb c (812%nat, 0%nat) then 1 else
  if cell_eqb c (813%nat, 0%nat) then 1 else
  if cell_eqb c (814%nat, 0%nat) then 1 else
  if cell_eqb c (815%nat, 0%nat) then 1 else
  if cell_eqb c (816%nat, 0%nat) then 1 else
  if cell_eqb c (817%nat, 0%nat) then 1 else
  if cell_eqb c (818%nat, 0%nat) then 1 else
  if cell_eqb c (819%nat, 0%nat) then 1 else
  if cell_eqb c (820%nat, 0%nat) then 1 else
  if cell_eqb c (821%nat, 0%nat) then 1 else
  if cell_eqb c (822%nat, 0%nat) then 1 else
  if cell_eqb c (823%nat, 0%nat) then 1 else
  if cell_eqb c (824%nat, 0%nat) then 1 else
  if cell_eqb c (825%nat, 0%nat) then 1 else
  if cell_eqb c (826%nat, 0%nat) then 1 else
  if cell_eqb c (827%nat, 0%nat) then 1 else
  if cell_eqb c (828%nat, 0%nat) then 1 else
  if cell_eqb c (829%nat, 0%nat) then 1 else
  if cell_eqb c (830%nat, 0%nat) then 1 else
  if cell_eqb c (831%nat, 0%nat) then 1 else
  if cell_eqb c (832%nat, 0%nat) then 1 else
  if cell_eqb c (833%nat, 0%nat) then 1 else
  if cell_eqb c (834%nat, 0%nat) then 1 else
  if cell_eqb c (835%nat, 0%nat) then 1 else
  if cell_eqb c (836%nat, 0%nat) then 1 else
  if cell_eqb c (837%nat, 0%nat) then 1 else
  if cell_eqb c (838%nat, 0%nat) then 1 else
  if cell_eqb c (839%nat, 0%nat) then 1 else
  if cell_eqb c (840%nat, 0%nat) then 1 else
  if cell_eqb c (841%nat, 0%nat) then 1 else
  if cell_eqb c (842%nat, 0%nat) then 1 else
  if cell_eqb c (843%nat, 0%nat) then 1 else
  if cell_eqb c (844%nat, 0%nat) then 1 else
  if cell_eqb c (845%nat, 0%nat) then 1 else
  if cell_eqb c (846%nat, 0%nat) then 1 else
  if cell_eqb c (847%nat, 0%nat) then 1 else
  if cell_eqb c (848%nat, 0%nat) then 1 else
  if cell_eqb c (849%nat, 0%nat) then 1 else
  if cell_eqb c (850%nat, 0%nat) then 1 else
  if cell_eqb c (851%nat, 0%nat) then 1 else
  if cell_eqb c (852%nat, 0%nat) then 1 else
  if cell_eqb c (853%nat, 0%nat) then 1 else
  if cell_eqb c (854%nat, 0%nat) then 1 else
  if cell_eqb c (855%nat, 0%nat) then 1 else
  if cell_eqb c (856%nat, 0%nat) then 1 else
  if cell_eqb c (857%nat, 0%nat) then 1 else
  if cell_eqb c (858%nat, 0%nat) then 1 else
  if cell_eqb c (859%nat, 0%nat) then 1 else
  if cell_eqb c (860%nat, 0%nat) then 1 else
  if cell_eqb c (861%nat, 0%nat) then 1 else
  if cell_eqb c (862%nat, 0%nat) then 1 else
  if cell_eqb c (864%nat, 0%nat) then 1 else
  if cell_eqb c (866%nat, 0%nat) then 1 else
  if cell_eqb c (867%nat, 0%nat) then 1 else
  if cell_eqb c (868%nat, 0%nat) then 1 else
  if cell_eqb c (869%nat, 0%nat) then 1 else
  if cell_eqb c (870%nat, 0%nat) then 1 else
  if cell_eqb c (871%nat, 0%nat) then 1 else
  if cell_eqb c (872%nat, 0%nat) then 1 else
  if cell_eqb c (873%nat, 0%nat) then 1 else
  if cell_eqb c (874%nat, 0%nat) then 1 else
  if cell_eqb c (875%nat, 0%nat) then 1 else
  if cell_eqb c (876%nat, 0%nat) then 1 else
  if cell_eqb c (877%nat, 0%nat) then 1 else
  if cell_eqb c (878%nat, 0%nat) then 1 else
  if cell_eqb c (879%nat, 0%nat) then 1 else
  if cell_eqb c (880%nat, 0%nat) then 1 else
  if cell_eqb c (881%nat, 0%nat) then 1 else
  if cell_eqb c (882%nat, 0%nat) then 1 else
  if cell_eqb c (883%nat, 0%nat) then 1 else
  if cell_eqb c (884%nat, 0%nat) then 1 else
  if cell_eqb c (885%nat, 0%nat) then 1 else
  if cell_eqb c (886%nat, 0%nat) then 1 else
  if cell_eqb c (887%nat, 0%nat) then 1 else
  if cell_eqb c (888%nat, 0%nat) then 1 else
  if cell_eqb c (889%nat, 0%nat) then 1 else
  if cell_eqb c (890%nat, 0%nat) then 1 else
  if cell_eqb c (891%nat, 0%nat) then 1 else
  if cell_eqb c (892%nat, 0%nat) then 1 else
  if cell_eqb c (893%nat, 0%nat) then 1 else
  if cell_eqb c (894%nat, 0%nat) then 1 else
  if cell_eqb c (895%nat, 0%nat) then 1 else
  if cell_eqb c (896%nat, 0%nat) then 1 else
  if cell_eqb c (897%nat, 0%nat) then 1 else
  if cell_eqb c (898%nat, 0%nat) then 1 else
  if cell_eqb c (899%nat, 0%nat) then 1 else
  if cell_eqb c (900%nat, 0%nat) then 1 else
  if cell_eqb c (901%nat, 0%nat) then 1 else
  if cell_eqb c (902%nat, 0%nat) then 1 else
  if cell_eqb c (903%nat, 0%nat) then 1 else
  if cell_eqb c (904%nat, 0%nat) then 1 else
  if cell_eqb c (905%nat, 0%nat) then 1 else
  if cell_eqb c (906%nat, 0%nat) then 1 else
  if cell_eqb c (907%nat, 0%nat) then 1 else
  if cell_eqb c (908%nat, 0%nat) then 1 else
  if cell_eqb c (909%nat, 0%nat) then 1 else
  if cell_eqb c (910%nat, 0%nat) then 1 else
  if cell_eqb c (911%nat, 0%nat) then 1 else
  if cell_eqb c (912%nat, 0%nat) then 1 else
  if cell_eqb c (913%nat, 0%nat) then 1 else
  if cell_eqb c (914%nat, 0%nat) then 1 else
  if cell_eqb c (915%nat, 0%nat) then 1 else
  if cell_eqb c (916%nat, 0%nat) then 1 else
  if cell_eqb c (917%nat, 0%nat) then 1 else
  if cell_eqb c (918%nat, 0%nat) then 1 else
  if cell_eqb c (919%nat, 0%nat) then 1 else
  if cell_eqb c (920%nat, 0%nat) then 1 else
  if cell_eqb c (921%nat, 0%nat) then 1 else
  if cell_eqb c (922%nat, 0%nat) then 1 else
  if cell_eqb c (923%nat, 0%nat) then 1 else
  if cell_eqb c (924%nat, 0%nat) then 1 else
  if cell_eqb c (925%nat, 0%nat) then 1 else
  if cell_eqb c (926%nat, 0%nat) then 1 else
  if cell_eqb c (927%nat, 0%nat) then 1 else
  if cell_eqb c (928%nat, 0%nat) then 1 else
  if cell_eqb c (929%nat, 0%nat) then 1 else
  if cell_eqb c (2000%nat, 0%nat) then 1 else
  if cell_eqb c (2000%nat, 4%nat) then 18446744073709551614 else
  if cell_eqb c (2000%nat, 5%nat) then 18446744073709551615 else
  if cell_eqb c (2000%nat, 6%nat) then 18446744073709551615 else
  if cell_eqb c (2000%nat, 7%nat) then 18446744073709551615 else
  0.

Lemma honest_full_sat_bm : sat deployed_model wit_honest_bm.
Proof. split; [ apply gates_holdb_sound; vm_compute; reflexivity | apply copy_holdsb_sound; vm_compute; reflexivity ]. Qed.

Definition mutant_wcopy_1_model : CircuitModel := cut_copy_model_bm ((8%nat, 0%nat), (2000%nat, 0%nat)).
Definition wit_wcopy_1 : Assignment := fun c =>
  if cell_eqb c (2000%nat, 0%nat) then 2 else
  wit_honest_bm c.
Lemma wcopy_1_split_sat : sat mutant_wcopy_1_model wit_wcopy_1.
Proof. split; [ apply gates_holdb_sound; vm_compute; reflexivity | apply copy_holdsb_sound; vm_compute; reflexivity ]. Qed.
Theorem mutant_wcopy_1_not_refines : ~ refinesD_bm_gen mutant_wcopy_1_model intact_ports_bm_gen.
Proof.
  unfold refinesD_bm_gen. intro H. specialize (H wit_wcopy_1 wcopy_1_split_sat).
  unfold RD_bm_gen in H. cbn [ intact_ports_bm_gen] in H.
  pose proof (proj1 H) as Hc.
  vm_compute in Hc. discriminate Hc.
Qed.

Definition mutant_wcopy_2_model : CircuitModel := cut_copy_model_bm ((9%nat, 0%nat), (2000%nat, 1%nat)).
Definition wit_wcopy_2 : Assignment := fun c =>
  if cell_eqb c (2000%nat, 1%nat) then 1 else
  wit_honest_bm c.
Lemma wcopy_2_split_sat : sat mutant_wcopy_2_model wit_wcopy_2.
Proof. split; [ apply gates_holdb_sound; vm_compute; reflexivity | apply copy_holdsb_sound; vm_compute; reflexivity ]. Qed.
Theorem mutant_wcopy_2_not_refines : ~ refinesD_bm_gen mutant_wcopy_2_model intact_ports_bm_gen.
Proof.
  unfold refinesD_bm_gen. intro H. specialize (H wit_wcopy_2 wcopy_2_split_sat).
  unfold RD_bm_gen in H. cbn [ intact_ports_bm_gen] in H.
  pose proof (proj1 (proj2 H)) as Hc.
  vm_compute in Hc. discriminate Hc.
Qed.

Definition mutant_wcopy_3_model : CircuitModel := cut_copy_model_bm ((10%nat, 0%nat), (2000%nat, 2%nat)).
Definition wit_wcopy_3 : Assignment := fun c =>
  if cell_eqb c (2000%nat, 2%nat) then 1 else
  wit_honest_bm c.
Lemma wcopy_3_split_sat : sat mutant_wcopy_3_model wit_wcopy_3.
Proof. split; [ apply gates_holdb_sound; vm_compute; reflexivity | apply copy_holdsb_sound; vm_compute; reflexivity ]. Qed.
Theorem mutant_wcopy_3_not_refines : ~ refinesD_bm_gen mutant_wcopy_3_model intact_ports_bm_gen.
Proof.
  unfold refinesD_bm_gen. intro H. specialize (H wit_wcopy_3 wcopy_3_split_sat).
  unfold RD_bm_gen in H. cbn [ intact_ports_bm_gen] in H.
  pose proof (proj1 (proj2 (proj2 H))) as Hc.
  vm_compute in Hc. discriminate Hc.
Qed.

Definition mutant_wcopy_4_model : CircuitModel := cut_copy_model_bm ((11%nat, 0%nat), (2000%nat, 3%nat)).
Definition wit_wcopy_4 : Assignment := fun c =>
  if cell_eqb c (2000%nat, 3%nat) then 1 else
  wit_honest_bm c.
Lemma wcopy_4_split_sat : sat mutant_wcopy_4_model wit_wcopy_4.
Proof. split; [ apply gates_holdb_sound; vm_compute; reflexivity | apply copy_holdsb_sound; vm_compute; reflexivity ]. Qed.
Theorem mutant_wcopy_4_not_refines : ~ refinesD_bm_gen mutant_wcopy_4_model intact_ports_bm_gen.
Proof.
  unfold refinesD_bm_gen. intro H. specialize (H wit_wcopy_4 wcopy_4_split_sat).
  unfold RD_bm_gen in H. cbn [ intact_ports_bm_gen] in H.
  pose proof (proj1 (proj2 (proj2 (proj2 H)))) as Hc.
  vm_compute in Hc. discriminate Hc.
Qed.

Definition mutant_wcopy_5_model : CircuitModel := cut_copy_model_bm ((12%nat, 0%nat), (2000%nat, 4%nat)).
Definition wit_wcopy_5 : Assignment := fun c =>
  if cell_eqb c (2000%nat, 4%nat) then 18446744073709551615 else
  wit_honest_bm c.
Lemma wcopy_5_split_sat : sat mutant_wcopy_5_model wit_wcopy_5.
Proof. split; [ apply gates_holdb_sound; vm_compute; reflexivity | apply copy_holdsb_sound; vm_compute; reflexivity ]. Qed.
Theorem mutant_wcopy_5_not_refines : ~ refinesD_bm_gen mutant_wcopy_5_model intact_ports_bm_gen.
Proof.
  unfold refinesD_bm_gen. intro H. specialize (H wit_wcopy_5 wcopy_5_split_sat).
  unfold RD_bm_gen in H. cbn [ intact_ports_bm_gen] in H.
  pose proof (proj1 (proj2 (proj2 (proj2 (proj2 H))))) as Hc.
  vm_compute in Hc. discriminate Hc.
Qed.

Definition mutant_wcopy_6_model : CircuitModel := cut_copy_model_bm ((13%nat, 0%nat), (2000%nat, 5%nat)).
Definition wit_wcopy_6 : Assignment := fun c =>
  if cell_eqb c (2000%nat, 5%nat) then 18446744073709551616 else
  wit_honest_bm c.
Lemma wcopy_6_split_sat : sat mutant_wcopy_6_model wit_wcopy_6.
Proof. split; [ apply gates_holdb_sound; vm_compute; reflexivity | apply copy_holdsb_sound; vm_compute; reflexivity ]. Qed.
Theorem mutant_wcopy_6_not_refines : ~ refinesD_bm_gen mutant_wcopy_6_model intact_ports_bm_gen.
Proof.
  unfold refinesD_bm_gen. intro H. specialize (H wit_wcopy_6 wcopy_6_split_sat).
  unfold RD_bm_gen in H. cbn [ intact_ports_bm_gen] in H.
  pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))) as Hc.
  vm_compute in Hc. discriminate Hc.
Qed.

Definition mutant_wcopy_7_model : CircuitModel := cut_copy_model_bm ((14%nat, 0%nat), (2000%nat, 6%nat)).
Definition wit_wcopy_7 : Assignment := fun c =>
  if cell_eqb c (2000%nat, 6%nat) then 18446744073709551616 else
  wit_honest_bm c.
Lemma wcopy_7_split_sat : sat mutant_wcopy_7_model wit_wcopy_7.
Proof. split; [ apply gates_holdb_sound; vm_compute; reflexivity | apply copy_holdsb_sound; vm_compute; reflexivity ]. Qed.
Theorem mutant_wcopy_7_not_refines : ~ refinesD_bm_gen mutant_wcopy_7_model intact_ports_bm_gen.
Proof.
  unfold refinesD_bm_gen. intro H. specialize (H wit_wcopy_7 wcopy_7_split_sat).
  unfold RD_bm_gen in H. cbn [ intact_ports_bm_gen] in H.
  pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H))))))) as Hc.
  vm_compute in Hc. discriminate Hc.
Qed.

Definition mutant_wcopy_8_model : CircuitModel := cut_copy_model_bm ((15%nat, 0%nat), (2000%nat, 7%nat)).
Definition wit_wcopy_8 : Assignment := fun c =>
  if cell_eqb c (2000%nat, 7%nat) then 18446744073709551616 else
  wit_honest_bm c.
Lemma wcopy_8_split_sat : sat mutant_wcopy_8_model wit_wcopy_8.
Proof. split; [ apply gates_holdb_sound; vm_compute; reflexivity | apply copy_holdsb_sound; vm_compute; reflexivity ]. Qed.
Theorem mutant_wcopy_8_not_refines : ~ refinesD_bm_gen mutant_wcopy_8_model intact_ports_bm_gen.
Proof.
  unfold refinesD_bm_gen. intro H. specialize (H wit_wcopy_8 wcopy_8_split_sat).
  unfold RD_bm_gen in H. cbn [ intact_ports_bm_gen] in H.
  pose proof (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H))))))) as Hc.
  vm_compute in Hc. discriminate Hc.
Qed.

Theorem bm_all_wires_closed_gen :
  (In ((8%nat, 0%nat), (2000%nat, 0%nat)) deployed_copy /\
   In ((9%nat, 0%nat), (2000%nat, 1%nat)) deployed_copy /\
   In ((10%nat, 0%nat), (2000%nat, 2%nat)) deployed_copy /\
   In ((11%nat, 0%nat), (2000%nat, 3%nat)) deployed_copy /\
   In ((12%nat, 0%nat), (2000%nat, 4%nat)) deployed_copy /\
   In ((13%nat, 0%nat), (2000%nat, 5%nat)) deployed_copy /\
   In ((14%nat, 0%nat), (2000%nat, 6%nat)) deployed_copy /\
   In ((15%nat, 0%nat), (2000%nat, 7%nat)) deployed_copy) /\
  (refinesD_bm_gen deployed_model intact_ports_bm_gen /\
   sat deployed_model wit_honest_bm) /\
  (~ refinesD_bm_gen mutant_wcopy_1_model intact_ports_bm_gen /\
   ~ refinesD_bm_gen mutant_wcopy_2_model intact_ports_bm_gen /\
   ~ refinesD_bm_gen mutant_wcopy_3_model intact_ports_bm_gen /\
   ~ refinesD_bm_gen mutant_wcopy_4_model intact_ports_bm_gen /\
   ~ refinesD_bm_gen mutant_wcopy_5_model intact_ports_bm_gen /\
   ~ refinesD_bm_gen mutant_wcopy_6_model intact_ports_bm_gen /\
   ~ refinesD_bm_gen mutant_wcopy_7_model intact_ports_bm_gen /\
   ~ refinesD_bm_gen mutant_wcopy_8_model intact_ports_bm_gen).
Proof.
  split; [| split].
  - repeat split;
      first [ exact in_copy_1
            | exact in_copy_2
            | exact in_copy_3
            | exact in_copy_4
            | exact in_copy_5
            | exact in_copy_6
            | exact in_copy_7
            | exact in_copy_8 ].
  - split; [ exact deployed_refines_RD_bm_gen | exact honest_full_sat_bm ].
  - exact (conj mutant_wcopy_1_not_refines
      (conj mutant_wcopy_2_not_refines
      (conj mutant_wcopy_3_not_refines
      (conj mutant_wcopy_4_not_refines
      (conj mutant_wcopy_5_not_refines
      (conj mutant_wcopy_6_not_refines
      (conj mutant_wcopy_7_not_refines
      (mutant_wcopy_8_not_refines)))))))).
Qed.
