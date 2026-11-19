# Software is bidirectional

Contracts — vanishingly, compoundingly small, independently
derivable, with a finite search space that is parametrically
solvable — bidirectionally produce, equivalently or by an
independent route, an optimally and speculatively optimizable
engineering and reengineering analysis for any set of
qualifications. This repo carries the proved model of that
claim, the composition with the rest of the family at named
pins, and the ever-growing empirical census that tests the
one premise the theorems cannot discharge: that a real
system's measures factor through its derived contract.

Four states are kept apart throughout, never blurred:
settled intent, proposed semantics, implemented behavior,
verified behavior. Everything in the proof folder is
verified behavior: it compiles under the family gate, cold,
with zero sorries and printed axioms exactly {propext,
Quot.sound}. The census is campaign evidence, labeled as
such, and is never a theorem.

## Contents

- proof/Core.lean — the model: states up to equivalence as
  a join-semilattice (the hyperlattice), recorded steps and
  their derivability closure, the analysis and synthesis
  maps with both round trips, smallness against the power
  of two, bounds over candidate lists with incremental
  tightening, the finite candidate grid, and every named
  measure with its characterization.
- proof/Controls.lean — four standing controls: smallness
  can fail; the two derivation routes disagree on an
  incomplete recording; a join inside the bounds tightens
  nothing; the content bound fails without injectivity.
- proof/Synthesis.lean — the composition: the losses core
  mirrored and discharged at its pin, the persistence
  elimination result discharged in this vocabulary, the
  recorded-state lattice, and the joined theorem assembling
  the whole method from this model's theorems and the
  family's restated hypotheses under named premises.
- defs.md — every term at implementer resolution, tied to
  its Lean counterpart, with exactly what each measure
  captures and what it does not.
- spec.md — the claim, the executable method, the theorem
  inventory at honest strength, falsification protocols,
  the synthesis provenance at pins, the gap register, the
  application, and the completion state.
- census.md — the empirical arm: a dated census of
  subjects, each row at its pin, measured bounds against
  proved bounds, anything unmeasured marked UNMEASURED
  with its blocking step. The list only grows.

## The gate

The family gate is proof/check.sh. Run it with the family
toolchain (Lean 4.19.0):

    cd proof
    LEAN=<path to lean 4.19.0> ./check.sh

It compiles every file cold, rejects sorries and escapes,
treats warnings as errors, and audits the printed axioms
of every declared result. At the landing pin it passes
cold: 74 audited declarations, printed axioms exactly
{propext, Quot.sound}, no Classical.choice anywhere.
