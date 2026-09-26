<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 Next Ridge Solutions Ltd -->

# Our BigMult circuit, verified: sound and complete

A formally verified BigMult circuit of our own, soundness and completeness, kernel-checked, at four limbs of 64
bits each (*n* = 64, *k* = 4).

BigMult is the big-integer multiplication template of the circom-bigint library. Given two big integers *a* and
*b*, each written as *k* limbs of *n* bits, its output *out*, of 2*k* limbs of *n* bits, is meant to be their
product. The public audit of that library, *Auditing Report for circom-bigint (circomlib)* (0xPARC Community,
Ethereum Foundation and Veridise Inc., 2022), lists BigMult as "In Progress" in its table of Coda verification
results. Coda, the open-source Coq library the audit used, states a soundness theorem for the template and closes
it with `Admitted`: the theorem is stated there, not proved (repository `Veridise/Coda`, commit `96e5c94e`, its
main branch on 2026-09-25, file `BigInt/src/BigInt/Proof/BigMult.v`, line 720).

This repository holds **our own circuit** for that job and **our own written rule** for it, and a proof, checked
by the Coq kernel, that the two agree exactly:

- **sound**: every filling of the circuit's cells that the circuit accepts, and whose inputs satisfy the rule's
  input assumption, yields an operand triple the rule accepts;
- **complete**: every operand triple that satisfies the rule's input assumption and that the rule accepts is
  realised by some filling the circuit accepts.

The two directions are one theorem, `policy_adequacy_bm`. The audit set out to verify a fixed circuit it did not
design; we designed ours to fit the rule. This proof is of our circuit against our rule: our own implementation of
the template's function, never a proof about the template itself. The rule's value relation is the one Coda's theorem
states, transcribed; the two-direction claim and the circuit are ours. No code from circom-bigint or from Coda is
in this repository.

## Check it yourself

```
git clone https://github.com/probatur/bigmult
cd bigmult
docker build .
```

The build compiles every proof from source in the public Coq 8.20.1 image, pinned by digest in the Dockerfile,
then re-checks the whole development, together with the parts of Coq's standard library it uses, with coqchk,
Coq's independent kernel checker. It fails unless coqchk accepts everything and reports no axioms, and its last
step prints the theorem exactly as the kernel states it, with the two definitions it is stated with (reproduced
below). With BuildKit, add `--progress=plain` to see every line. The same build runs on every push, from
`.github/workflows/check.yml`. If you run it, you are welcome to add a line to [REPRODUCTIONS.md](REPRODUCTIONS.md).

## The theorem, as the kernel states it

<!-- STATEMENT:BEGIN (filled from the check's own output; never edited by hand) -->

```
policy_adequacy_bm
     : bm_rule.adequate accepts_bm
bm_rule.adequate =
fun accepts : list BinNums.Z -> list BinNums.Z -> list BinNums.Z -> Prop =>
forall a b out : list BinNums.Z,
bm_rule.PRE_bm a b -> accepts a b out <-> bm_rule.REL_bm a b out
     : (list BinNums.Z -> list BinNums.Z -> list BinNums.Z -> Prop) -> Prop

Arguments bm_rule.adequate accepts%function_scope
accepts_bm =
fun a b out : list BinNums.Z =>
exists al : bm_scaffold_gen.Assignment,
  bm_scaffold_gen.sat bm_model_gen.deployed_model al /\
  bm_semantic.CANON_bm al /\
  bm_semantic.a_l al = a /\
  bm_semantic.b_l al = b /\ bm_semantic.out_l al = out
     : list BinNums.Z -> list BinNums.Z -> list BinNums.Z -> Prop

Arguments accepts_bm (a b out)%list_scope
```

<!-- STATEMENT:END -->

## The theorem in plain language

### The two objects it connects

**The circuit.** A fixed arithmetic circuit over the prime field of the 255-bit Pasta prime
2^254 + 45560315531419706090280762371685220353. It is a table of cells, each holding a field element, together
with 930 polynomial constraints, each of which must evaluate to zero in the field, and 8 copy constraints, each
requiring an output cell and a public cell to hold the same value. A filling of the cells that passes all 930
polynomial constraints and all 8 copy constraints is an **accepted assignment** (`sat deployed_model` in the
development). That is the whole acceptance condition: the model contains no lookup tables and no other kind of
constraint.

**The rule** (`coq/spec/bm_rule.v`), written by us, about triples of vectors (*a*, *b*, *out*). A vector has
limbs; a limb is a whole number from 0 up to, but not including, 2^64; a vector's value `VAL` is its
little-endian base-2^64 reading. The rule has two parts, kept separate on purpose:

- **the input assumption** `PRE_bm`, about *a* and *b*: each has exactly 4 limbs, and every limb is in range.
  This is the input assumption of the template BigMult hands its inputs to (`BigMultNoCarry`, whose comment asks
  for registers of *n* bits; neither template range-checks them), and it is the hypothesis of Coda's theorem. It
  is assumed, never enforced, exactly as the templates assume it.
- **the relation** `REL_bm`, about the whole triple: *out* has exactly 8 limbs, all in range, and
  `VAL out = VAL a · VAL b`, as an equality of integers.

**What "accepts" means** (`accepts_bm`): the circuit accepts a triple when there is an accepted assignment whose
operand cells, each read as its canonical integer in [0, *p*) for the field prime *p*, are exactly that triple.
The theorem, `adequate accepts_bm`, says: for every *a* and *b* satisfying the input assumption, and every *out*,
the circuit accepts (*a*, *b*, *out*) **exactly when** the relation holds.

### Soundness: nothing the circuit accepts escapes the rule

For every accepted assignment, read the sixteen operand cells (four for *a*, four for *b*, eight for *out*), each
as its canonical remainder modulo the field prime. If the *a* and *b* so read satisfy the input assumption, then
the triple so read satisfies the relation (`bridge_sound`).

- The quantifier really is over **all** fillings. Accepted fillings whose *a* or *b* cells are out of range are
  not excluded; the rule asserts nothing about them, because its input assumption fails. That is the template's
  own posture: input ranges are the caller's burden. The development proves that each input cell is read only by
  the constraints that compute the product (`each_input_cell_is_read_only_by_chain_gates`).
- The output's range is not assumed: every accepted filling has its eight output limbs in [0, 2^64)
  (`out_limbs_in_range`).
- The public cells are not assumed to agree with the output cells: that agreement is derived from the copy
  constraints (`answer_pins_are_DERIVED`).

### Completeness: nothing the rule accepts, within its input assumption, is beyond the circuit

For every triple satisfying the input assumption and the relation, there is a filling that the circuit accepts,
passing all 930 polynomial constraints and all 8 copy constraints, whose sixteen operand cells read back as
**exactly that triple**, *out* included, limb for limb (`bridge_complete`). This direction is ours: the audit's
certification criterion, and Coda's theorem, are one-directional.

### Two things that are easy to confuse

- **The field prime and the product.** The circuit's constraints are equations over a field of about 2^254
  elements, while the product of two 256-bit values can approach 2^512. A circuit could accept an output that
  equals the product only modulo the field prime. The rule is an equality of integers, and the development shows
  the difference is real: for the input whose limbs are all 2^64 − 1, it exhibits an 8-limb output, every limb in
  range, whose value is the true product plus the field prime, which the rule does not accept (`REL_is_a_value_equality_not_mod_q`), and it proves that
  no accepted filling decodes to it (`no_satisfying_row_decodes_to_the_modular_alias`).
- **The input assumption and the circuit's behaviour.** The input assumption is where the guarantee starts. It is
  not a description of exactly which inputs the circuit accepts, and the theorem says nothing about fillings whose
  inputs fall outside it.

## Where each part of the rule comes from

| part of the rule | what it says | where it comes from |
|---|---|---|
| `PRE_bm` | *a* and *b* have exactly 4 limbs, each in [0, 2^64) | the hypotheses of Coda's theorem (every limb of *a* and of *b* below 2^*n*, with *k* limbs each); the templates' own input assumption; carried as an assumption, as the templates carry it |
| `REL_bm`, first two conjuncts | *out* has exactly 8 limbs, each in [0, 2^64) | the conclusion of Coda's theorem (every limb of the 2*k*-limb output below 2^*n*); the template range-checks each output limb with `Num2Bits(n)` |
| `REL_bm`, third conjunct | `VAL out = VAL a · VAL b` | the conclusion of Coda's theorem: the value of *a* times the value of *b* equals the value of *out*, over the integers |
| `adequate` | the two directions together | ours |

The template is `BigMult(n, k)` in circom-bigint, `circuits/bigint.circom`, lines 277–296 at commit
`7505e5c60b8bc76cfb5cc06646d81aafbae66180` (the commit the audit's engineers worked on), and byte-identical at
lines 302–321 of commit `2eceb9c` (the version in the report's application summary). The output range checks are
in the template it hands the product to, `LongToShortNoEndCarry`, lines 256–260 at `7505e5c`.

## Reading notes

1. **Counting the constraints.** The circuit has 930 polynomial constraints and 8 copy constraints; the theorem
   covers exactly the set of fillings that passes both kinds together. The count of 930 polynomial constraints,
   beside the 8 copy constraints, is itself a checked fact of the development (`dg_len`).
2. **Completeness is universal.** It holds for every triple that satisfies the input assumption and the relation.
   The development also shows instances, for example the input whose limbs are all 2^64 − 1, accepted with its
   product (`the_corner_is_ACCEPTED`); those are instances shown, not the evidence.
3. **A premise that does no work, and the development proves it.** The definition of acceptance carries a
   canonicity condition, `CANON_bm`; it is provably satisfied by every filling (`CANON_is_free`), so it narrows
   nothing. Soundness is also proved without it (`bridge_sound_without_CANON`).
4. **Every copy constraint is needed.** With any one of the 8 copy constraints removed, the model no longer
   meets its intended public interface, shown by an explicit filling for each (`bm_all_wires_closed_gen`).
5. **Scope.** Scope: these results bind the formal (Coq) layer only; the generated constraint model's fidelity to the circuit implementation, and the implementation itself, are outside them.

## What is not claimed

- **Nothing about circom-bigint's own circuit, or about Coda's development**, beyond the facts cited above: the
  template's text, and that Coda's BigMult soundness theorem is stated and closed with `Admitted`. The circuit
  proved here is ours, built for the same function; the rule is ours. We designed our circuit to meet our rule.
- **Nothing beyond the parameter set *n* = 64, *k* = 4.** The theorem is about our circuit, over the Pasta
  field; nothing is claimed about any other (*n*, *k*), or about any circuit over another field.
- **Nothing about the layers below the formal model.** That the generated constraint model (the 930 polynomial
  constraints, the 8 copy constraints, the field prime, the cell layout, and the absence of lookups and of other
  constraint kinds) faithfully mirrors the circuit implementation is outside this claim, as are the
  implementation, the prover and the verifier themselves.
- **Nothing about inputs outside the input assumption**: the circuit does not check it, and the theorem does not
  describe what the circuit accepts there.

## A proof about a circuit, not a proof made by one

Two different objects are called "proofs" around circuits like this one. This repository contains the first: a
single machine-checked argument, in Coq, about what the circuit's constraints accept. It is checked once, and it
does not depend on any execution. The circuit itself, when used, produces a different kind of proof, a
zero-knowledge proof for each execution. None of those is in this repository, and nothing here depends on them.

## Files

| file | what it holds |
|---|---|
| `coq/spec/bm_rule.v` | the rule: `PRE_bm`, `REL_bm`, `adequate`, and facts about it |
| `coq/constraints/gen/bm_model_gen.v` | the circuit's constraint model: the field prime, the 930 polynomial constraints, the 8 copy constraints |
| `coq/constraints/gen/bm_scaffold_gen.v` | cells, assignments, evaluation, and the acceptance predicate `sat` |
| `coq/constraints/gen/bm_wires_gen.v` | the eight copy wires, from the output cells to the public cells |
| `coq/constraints/gen/bm_necessity_gen.v` | each copy constraint is necessary: with any one of the eight removed, the model no longer refines the intended public interface (`mutant_wcopy_1_not_refines` and its seven siblings) |
| `coq/constraints/pfcs.v` | a Coq embedding of prime-field constraint systems, following the PFCS formalism |
| `coq/constraints/range_field.v`, `coq/constraints/range_field_pasta.v` | range checks over a prime field, and a primality certificate for the Pasta prime |
| `coq/constraints/field_order_lift.v`, `coq/constraints/bits_kit.v` | lifting facts from the field to the integers; bit decompositions |
| `coq/constraints/bm_semantic.v` | reading operand triples off a filling |
| `coq/constraints/bm_model_facts.v` | facts about the model: range bounds on output and carry cells, the modular alias |
| `coq/constraints/bm_soundness.v` | soundness (`bridge_sound`) |
| `coq/constraints/bm_adequacy.v` | completeness, and the two directions as one theorem (`policy_adequacy_bm`) |

## Credits

- The PFCS formalism: A. Coglio, E. McCarthy, E. W. Smith, *Formal Verification of Zero-Knowledge Circuits*,
  arXiv:2311.08858 (ACL2 Workshop 2023). `coq/constraints/pfcs.v` follows it.
- circom-bigint, by its authors (GPL-3.0), whose BigMult template this work answers to. Its behaviour is
  described here; none of its code is copied.
- Coda, by Veridise, whose stated BigMult theorem the rule's relation transcribes. It is described here; none of
  its code is copied.
- *Auditing Report for circom-bigint (circomlib)*, 0xPARC Community, Ethereum Foundation and Veridise Inc., 2022.

## Licence

Apache-2.0: see [LICENSE](LICENSE) and [NOTICE](NOTICE).

## Contact

Probatur is published by Next Ridge Solutions Ltd: [nxridge.com](https://nxridge.com).
