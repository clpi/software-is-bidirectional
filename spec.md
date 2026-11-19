# Software is bidirectional: the specification

## The claim

Settled intent, in the directing words of 2026-11-19
01:54 PST: prove rigidly, constructively, and
empirically that vanishingly, compoundingly small,
possibly independently derivable contracts — whose
search space is parametrically solvable, optimizable,
and synthesizable — bidirectionally produce, completely
equivalently or via an independent methodology, an
optimally and speculatively optimizable engineering
and reengineering analysis for any arbitrary set of
qualifications; that the constructed invariant measures
across software (performance, binary size, compression,
scheduling, ordering, venue selection, and the rest)
are solvable, with upper and lower bounds found
incrementally over the compounding hyperlattice of
possible states and transitions in the finite state
machine definition of software; and prove the measures
of semantic mass, velocity, redundancy, suboptimal
scheduling, suboptimal venue use, and suboptimal
parametric test sets, each clarifying exactly what it
clarifies, with the search space finite and
incrementally solvable in a compounding fashion.

Binding addition, 2026-11-19 01:55 PST: any practical
ceiling or floor, info gap, resolution gap, or
constructed profiling, tracing, representation,
execution, layout, or ordering gap is closed end to end
at the certifiable Pareto optimum. In this repo: every
bound stated is either certified tight at the optimum
or carried in the gap register below with its closing
route; the distance between a proved upper and a proved
lower bound is itself a recorded gap, never a caveat.

Four states are distinguished throughout: settled
intent (this section), proposed semantics (labeled
where it appears), implemented behavior (the executed
census machinery), verified behavior (the Lean model
under the family gate). Nothing below blurs them.

## The executable method

Each step names its artifact, its measure, and the
theorem that proves the step sound. The method is the
joined theorem (Synthesis.joined) read operationally.

1. Fix the qualification: its axes (per-code measures)
   and its required levels. Artifact: the axis list.
   The qualification is a named, finite thing; its
   finiteness is what the candidate space's finiteness
   is derived from (step 6), never assumed.
2. Record the system: facts, recorded steps, behavior
   record. Artifact: the Sys value. Measure: the record
   lengths, which bound the contract's description
   (Core small).
3. Derive the contract by two independent routes: the
   direct analysis of the record, and the chunked
   analysis over any chunking of the recording.
   Artifact: the Contract value. Soundness: the routes
   agree whenever the chunks concatenate to the whole
   record (Core agree); control two is the standing
   warning that an incomplete recording breaks
   agreement, so agreement is checked, not presumed.
4. Check smallness: compute desc and compare against
   the qualification's bound. Measure: desc. The
   description is at most the record length plus the
   step count (Core small), and any bound is vanishing
   against the power of two of the description (Core
   vanish). A contract failing its bound is not small —
   control one — and the method stops there for that
   qualification.
5. Run both round trips: analyze the synthesized system
   (must return the contract exactly, Core rtone) and
   synthesize the analyzed system (must return a system
   equivalent under the qualification, Core rttwo).
   Then the reengineering analysis: analyze, synthesize,
   re-analyze (Core thm.reeng) — forward and
   reengineering analyses agree by theorem.
6. Enumerate the candidate space: the grid of the
   contract's two lists. Measure: its length, the
   product of the two lengths (Core finite). The space
   is finite with a computed size; searches over it are
   decidable (Core optdec, stated in the joined theorem
   as the decided disjunction).
7. Compute the constructed measures over the candidate
   states and the paths among them: performance, size,
   and compression axes through the axis projection;
   semantic mass and velocity over the universe;
   redundancy over the recorded steps; scheduling,
   venue, and test set suboptimality; ordering descents;
   content. Each measure's characterization theorem
   (inventory below) states what it captures.
8. Bound every measure over the candidate list: lo and
   hi by the fold bounds. Soundness: every member lies
   inside (Core inbounds) and both bounds are attained
   (Core attained). Grow the list by joins as new states
   are discovered: bounds update from the parts
   (Core boundsjoin) and the best and the gap to any
   floor tighten monotonically (Core tighten). Where
   the best meets a certified floor, the attaining
   member is a certified optimum (Core certified);
   where it does not, the distance is a gap in the
   register, with its closing route.
9. Fix losses structurally: project the record per
   axis; a shortfall against a required level is a gap
   at a named site — a component or the recorded
   interaction — never at an instance (Synthesis
   localizes). Component gaps compose compoundingly
   (Synthesis compound), the bound is tight at the
   no-surplus point (Synthesis tight), and loss-free
   parts with a loss-free interaction compose to a
   loss-free whole (Synthesis wholefree). The axis
   checks decide each site (Synthesis check, allcheck)
   and their verdicts are sound (Synthesis sound,
   allsound).
10. Eliminate redundant computation: flag the one-step
    redundant steps (Core redone, redcount; sound by
    Core redsound) and adjoin derivable facts freely —
    the derivable set is unchanged (Synthesis elim).
    Compress persistent data to its minimum over the
    candidate space (step 8's certified optimum; the
    general minimum existence is the persistence
    hypothesis of the joined theorem).
11. Speculate on premise cones: a result under
    hypothesized facts is a Spec whose cone lists them;
    it is valid exactly while the cone is contained in
    the system's facts (Core specvalid) and stays valid
    under joins (Core specmono). Refuting a premise is
    removing a cone member; the update is incremental
    by construction.
12. Grow the census: run steps 2–8 on each new subject,
    append its dated row at its pin (census.md), and
    record measured bounds against proved bounds. The
    census is the empirical arm; its rows are campaign
    evidence, and its contract-fidelity verdicts are
    the falsification protocol of gap G4.

## Theorem inventory, at honest strength

Verified in this repo (proof/Core.lean; the family gate
passes cold at the landing pin; printed axioms exactly
{propext, Quot.sound} for every entry):

- The hyperlattice: joincomm, joinassoc, joinidem,
  joinleft, joinright, joinleast — states up to
  membership equivalence, ordered by information, form
  a join-semilattice with join the least upper bound.
- Derivability: stepclose, derivmono, derivsteps.
- Bidirectionality: rtone (analysis of synthesis is the
  identity on contracts), rttwo (synthesis of analysis
  is qualification-equivalent to the system), thm.reeng
  (the reengineering analysis returns the contract).
- Independent derivability: agree (the direct and
  chunked routes coincide under a complete recording).
- Smallness: small (the description bound), vanish and
  powbound (a description is vanishing against the
  power of two of its size), smalljoin (description
  adds over contract joins).
- Speculation: specvalid (validity is cone containment),
  specmono (validity survives joins).
- Bounds: inbounds, attained, boundsjoin (the joined
  bounds are the parts' min and max), tighten (best and
  gap tighten monotonically under joins), certified
  (best at a certified floor is a certified optimum).
- Finiteness and decidability: finite and gridlength
  (the candidate count is the computed product),
  optdec (the optimum question is decidable).
- Measures, each with its characterization: massmono
  and massjoin (semantic mass), telescope (velocity is
  exactly mass change along a growing path), redsound
  (the redundancy test is sound in the one-step face),
  thm.schedsub (scheduling suboptimality is exactly the
  idle sum), thm.venuesub (venue suboptimality is the
  exact excess over the best candidate), thm.testsub
  (test set suboptimality vanishes exactly at equal
  mass under containment), ordzero with ordnil and
  ordone (ordering optimality is the absence of
  adjacent descents).
- Controls (proof/Controls.lean): ctrlone (smallness
  can fail), ctrltwo (routes disagree on an incomplete
  recording), ctrlthree (a join inside the bounds
  tightens nothing), ctrlfour (the content bound fails
  without injectivity).

Verified in this repo (proof/Synthesis.lean), mirrored
and discharged from the losses core at its pin: additive,
projected, split, gapfree, composed, wholefree,
compound, tight, monotone, localizes, finite (the
contract space), sound, allsound — over definitions
identical to the source's, with this repo's proofs.

Discharged in this vocabulary: elim — the persistence
elimination result, proved over this model's
derivability; and lattice — the recorded-state
join-semilattice, which discharges for exactly that
class the general join-semilattice premise the
compilers repo carries as a label. No wider discharge
is claimed: graph-shaped states in general are not
recorded fact lists.

Restated hypotheses of the joined theorem (proved in
their home repos at the pins in the synthesis table;
taken here as arguments, in vocabulary-independent
form): minimum existence over a nonempty candidate
list and frontier completeness (persistence,
quantifiable); certificate soundness and monotonicity
(persistence); baseline-free measurement and
incremental equals full (profiling); admission
composition under the interaction-closed side
condition (composable); checker soundness and cone
exactness (incrementally-safe); fold exactness under
retraction (traceability); quotient recovery by
carrying (compilers-lose-info); bounds soundness and
attainment for the general measure interface
(optimality — its list instance is proved here as
inbounds and attained).

Named premises of the joined theorem (they bind
applicability; no conjunct proof uses them): contract
fidelity (G4), record fidelity and re-measure
(losses), coverage (quantifiable), the spec authority
premise (incrementally-safe), witness faithfulness
(profiling).

Proposed, not proved: the content bound under
injectivity of the content map on the universe (the
unconditional form is refuted, control four); the
profiling visibility vector and time-varying
re-solving (G2); weighted and continuous axes and
richer derivations in the losses mirror (G7).

## Falsification protocols

Every claim not proved outright carries the run that
would refute it.

- Contract fidelity (G4): for each census subject, the
  measured axes must reproduce from the derived
  contract alone. A subject whose measured axes do not
  so reproduce refutes fidelity for that qualification
  and is recorded as such in its census row. Blocking
  step for the first tranche: contract extraction from
  Idol sources is not mechanized; the rows carry it.
- Record fidelity and re-measure (losses premises):
  replay each recorded step against its execution log;
  a step that does not replay voids the contract
  derived from that recording. This is also G9's
  protocol, inherited from the persistence spec.
- Candidate completeness (G8): run the persistence
  enumeration check on the restart-records corpus; a
  representation in use but outside the enumerated
  space names the alphabet extension owed.
- The gzip witness (G6): one ruling in both programs —
  either compressed forms are admitted as candidates
  (the representation definition extends and readability
  is re-proved) or the figure leaves the witness role.
  Until the ruling, the corpus's best candidate upper
  bound is ambiguous between the two recorded figures,
  and the record says so.

## Synthesis

Provenance, verified live at the pins named (the
program record carries the full table):

- Losses (software-losses-are-compositional) at
  12ee66e9c9cdaeec4bea5eb8fb1fd61e6df780fb: the
  contract notion, the derivation, the projection, the
  record gap and the composition theorems — mirrored
  and discharged in proof/Synthesis.lean; its campaign
  premises (record fidelity, re-measure) carried as
  named premises of the joined theorem.
- Persistence (software-persistence-is-minimal) at
  eb01cf2e33a20bfbda5a03aba7a48c70fbd10741: the
  redundancy notion and elimination (discharged here
  as Synthesis.elim), minimum existence and certificate
  soundness and monotonicity (restated hypotheses);
  its gate at that pin passes cold with printed axioms
  exactly {propext, Quot.sound}.
- Profiling (software-profiling-is-synthesizable) at
  a53c4bf5aa83e8677ecb66571d61ed4c11e2d88d: baseline-free
  measurement and incremental equals full, restated
  hypotheses; witness faithfulness a named premise;
  its visibility vector stays proposed (G2).
- Quantifiable at
  d88acbdc3ba78fff994067d2c73bcc01622b3f61: frontier
  completeness, restated; coverage a named premise.
- Optimality at
  95df5fb7e922e7316b0ebe90b7847fd45a208d88: bounds
  soundness and attainment for the general interface,
  restated; the list instance is proved in this repo.
- Composable at
  7b1746467a410e9e5ae309f2a86bc4cd37700989: admission
  composition under its interaction-closed side
  condition, restated with the side condition explicit.
- Incrementally-safe at
  97e55d28edc0d33f3466de3a3e4061e010c3b4d5: checker
  soundness and cone exactness, restated; the spec
  authority premise named. Its gate at this head is
  unrecorded in its tree (G3).
- Traceability at
  8f6a128069d0e68e97c4a69d78689c84350b0d2f: the event
  fold and retraction exactness, restated.
- Compilers-lose-info at
  69358971221d66e6304b64ff68a2e111d15231b3: quotient
  recovery by carrying, restated; its general
  join-semilattice claim is a labelled premise there
  and is discharged here for recorded fact states
  (Synthesis.lattice), no wider.
- Closed-loop (software-is-a-closed-loop) at tree head
  f2c3b6d643bba02e90fb16381d20c9b891210e65: census layer
  only — it contributes no hypotheses; its synthesis
  theorems are instances over the family.

Certified tight under the 01:55 law (audit verdicts,
not gaps): the persistence model minimum (minimum by
construction, its Pareto claim bounded by its axis
set); the losses compound bound as
certified-with-characterized-residual (tight attains
exactly at the no-surplus point; the residual under
surplus is exactly the truncated-subtraction clipping,
quantified site by site); the family equality results
(finiteness counts, cost additivity, localization),
tight by construction.

Gap register (each owned, each with its closing route;
the program record carries the full text):

- G1: the restart-records corpus minimum is
  uncertified — current 3,516,608 bytes, the
  dictionary/columnar construction 1,425,683, the gzip
  figure 280,522 (witness status contested, G6), no
  proved floor, the full Pareto verdict UNMEASURED.
  Route: fix the access-cost contract, prove the floor
  from the distinct-value census, run the persistence
  checkers end to end.
- G2: the profiling visibility vector is proposed and
  unformalized; time-varying re-solving is open.
  Route: formalize in the profiling repo or import as
  a named premise with its falsification protocol.
- G3: incrementally-safe has no recorded gate at its
  current head. Route: run its family gate cold at the
  head and land the log.
- G4: contract fidelity is a premise, not a theorem.
  Route: the census — each subject whose measured axes
  reproduce from its contract alone is evidence; a
  non-reproducing subject refutes it there.
- G5: empirical subjects beyond the executed runs are
  UNMEASURED until their row's run lands. Route: the
  census only grows, one row per run, same contract.
- G6: the gzip witness status conflict (see the
  falsification protocols). Route: one ruling in both
  programs.
- G7: the losses mirror's generality — sum derivation,
  Nat axes, position-independent per-entry measures.
  Route: the losses program's general derivation
  interface pass.
- G8: candidate completeness for the corpus unchecked.
  Route: run the enumeration check (protocol above).
- G9: the persistence premise falsification runs on
  the corpus never ran. Route: run both protocols as
  written in its spec.
- G10: pin drift in imported citations inside two
  family repos. Route: statement-level diff between
  cited and current pins; re-derive or carry the
  differences as named premises.

## Application

The empirical arm lives in census.md, dated and pinned,
and only grows. First tranche, landed 2026-11-19:
idol-lib at 69ee40eb000f557e07dae548efa9a503703ecb35 —
1,067 tree entries, 16 folder rows, all UNMEASURED with
the blocking step named (contract extraction from Idol
sources is not mechanized; the end-to-end checker run
over corpora is the open run); the 19 software-prefixed
family repos at their individually read pins, 17 proof
repos and 2 synthesis repos. Executed runs of the
method's own machinery (the model's analysis, synthesis,
round trip, and bounds, in executable form) over the
three landed inventories: losses at its pin — desc 16,
mass 16, round trip PASS, state space 65,536;
persistence at its pin — desc 31, mass 31, PASS,
2,147,483,648; profiling at its pin — desc 19, mass 19,
PASS, 524,288. In each case desc is below 2^desc by the
proved bound, and the bounds over the three subjects
are attained at both ends: lo 16 (losses), hi 31
(persistence), for desc and mass alike. The evidenced
claim is narrow and stated as such: the round trip and
the bound machinery execute and agree on real
inventories. Contract fidelity for these subjects
stays G4, open.

## Completion

Verified and landed: the model (proof/Core.lean), the
controls (proof/Controls.lean), and the composition
(proof/Synthesis.lean) under the family gate, cold, at
the landing pin — zero sorries, warnings as errors,
74 audited declarations, printed axioms exactly
{propext, Quot.sound}. The joined theorem assembles the
method for an arbitrary system under an arbitrary
qualification from this repo's theorems, the mirrored
losses core, the discharged elimination and lattice
results, and the family's restated hypotheses under six
named premises.

Open, each owned in the register above: the corpus
minimum and its floor (G1, with G6, G8, G9), the
visibility vector (G2), one sibling gate log (G3),
contract fidelity as a standing premise discharged
only empirically, row by row (G4, G5), the losses
generality pass (G7), and citation pin drift (G10).
The census grows from here; the register shrinks only
on executed proof.
