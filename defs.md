# Definitions

Every term of the bidirectional model, at implementer
resolution, tied to its Lean counterpart in the proof
folder. Where a measure is defined, the entry states
exactly what it captures and what it does not; the
characterization theorem named in the entry is the
authority, and the spec's inventory records its strength.

## State

A list of fact codes (List Nat), taken up to membership:
two lists with the same members are the same state for
every purpose of the model. Lean: the type is List Nat
throughout, with equiv below. A state is a node of the
hyperlattice; its information content is its member set.
Duplicates and order carry no information.

## Equivalence

equiv s t: every code is a member of s exactly when it is
a member of t. All lattice laws are stated up to equiv,
never up to list equality.

## Information order

le s t: every member of s is a member of t. Read: t knows
at least everything s knows.

## Join, and the hyperlattice

join s t is append. Up to equiv it is commutative,
associative, and idempotent, it extends both arguments,
and it is the least state doing so (joincomm, joinassoc,
joinidem, joinleft, joinright, joinleast; assembled as
Synthesis.lattice). States so ordered are the
join-semilattice the program calls the hyperlattice: the
compounding space of possible states, closed under join.
A transition between states is a recorded step, next.

## Step

A record with two fields: pre, a list of fact codes (the
premises), and add, one fact code (the conclusion). A step
is one recorded transition of the finite state machine:
from any state deriving all of pre, the machine may move
to a state also containing add. Lean: the Step structure.

## Derivability

Deriv steps s x: x is derivable from state s through the
recorded steps — either x is already in s, or some
recorded step concludes x and every premise of that step
is derivable. The inductive closure of the recordings.
Monotone in the state (derivmono) and in the step list
(derivsteps); a step whose premises are derivable closes
(stepclose). Derivability is the model's one closure
notion: redundancy, certificates, and the premise cone
all speak of it.

## System

A record of three fields: facts (the current state),
steps (the recorded transitions), record (the behavior
record: the capability codes the system's recordings
exhibit). Lean: the Sys structure. A system is the
subject of analysis; nothing about it is assumed beyond
its three lists.

## Contract

A record of two lists: caps (capability codes) and
designs (design codes). The contract set of a system
under a qualification: behaviorally derived (it is read
off the recordings, next entry), additively recorded
(projections over it add over appends, Synthesis
projected). The same two-list form as the losses model's
contract, shared deliberately. Lean: the Contract
structure.

## Analysis

analyze s: the contract whose caps are the system's
record and whose designs are the added facts of its
recorded steps, in order. The forward map, system to
contracts. It reads only the recordings — that is what
makes contract fidelity (gap G4) a real premise rather
than a definitional truth.

## Synthesis

synth c: the canonical system built from a contract —
no facts, one premise-free step per design concluding
that design, and the contract's caps as its record. The
backward map, contracts to system. The round trips:
analyzing a synthesized contract returns it exactly
(rtone); synthesizing an analyzed system returns a
system equivalent under the qualification (rttwo).

## Qualification equivalence

qequiv axes s t: the two systems analyze to the same
contract and agree on every axis value in axes, an axis
value being the sum over caps plus the sum over designs
of a per-code measure. Equivalence in this program is
qualification-relative throughout: systems are the same
when the qualification cannot tell them apart.

## Reengineering

reeng s is analyze after synth after analyze: the
engineering analysis read forward, then the system
rebuilt from its contract and re-analyzed. It returns
the original contract exactly (thm.reeng) — the forward
and reengineering analyses agree by construction, not
by inspection.

## The chunked route, and agreement

analyzechunks s chunks derives the contract from a
recording presented in chunks: caps are the flattened
chunks, designs as in analyze. When the chunks
concatenate to the whole record, the two independent
routes agree (agree). Control two shows the premise is
load-bearing: over chunks that do not concatenate to
the record, the routes provably disagree.

## Description size, and smallness

desc c: the length of caps plus the length of designs.
Small u c: desc c is at most u. The analysis of any
system has desc bounded by the record length plus the
step count (small), and any bound u is vanishing against
the state space: u is below 2^u whenever u is at least 1
(vanish, powbound), so a contract whose description is
linear in the recordings describes a state space
exponential in that description. Smallness is a
property proved per qualification, never assumed:
control one is a contract that is not small at bound 3.

## System join

sysjoin a b: componentwise append of two systems. A
speculative result valid on one system stays valid on
any join extending it (specmono).

## Speculative spec, premise cone, validity

A Spec is a value with a cone: the list of premise codes
the value's derivation depends on. valid sp s: the cone
is contained in the system's facts — the result holds
exactly on its premise cone (specvalid), and validity
is preserved when the system grows by joins (specmono):
discharging premises keeps the result, and a refuted
premise is precisely a cone member leaving the facts.
Speculation is premise-tracked by construction; there
is no untracked hypothetical result in the model.

## Candidate list, values, bounds

A candidate list L is a list of states. vals m L maps a
measure m over it. vmin and vmax are the fold minimum
and maximum (0 on the empty list, a convention the
attainment theorem's nonemptiness hypothesis exists to
exclude). lo m L is the least value, hi m L the greatest,
best m L the least — the optimum under minimization.
Every member's value lies between lo and hi (inbounds),
and on a nonempty list both bounds are attained by
members (attained). gap m F L is best minus a floor F:
the recorded distance between the proved optimum over
the candidates and a certified floor; under the gap law
of 2026-11-19 01:55 this distance is a gap to close,
never a caveat. When the best equals the floor and the
floor underlies every member, the attaining member is a
certified optimum over the list (certified).

## Bound update under join

boundsjoin: on nonempty lists, the bounds of a joined
candidate list are the min and max of the parts' bounds
— bounds update from the joined parts, exactly.
tighten: joining more candidates never raises the best
and never widens the gap to a floor — bounds tighten
monotonically as the hyperlattice compounds. Control
three is the boundary: a join whose new member lies
inside the current bounds tightens nothing.

## Candidate grid, finiteness, decidability

grid caps designs pairs every capability with every
design (the losses grid, verbatim). Its length is the
product of the lengths (finite, gridlength): the
candidate space of a qualification is finite with a
computed size, derived from the contract's two finite
lists — finiteness is a conclusion of what a
qualification is, never a hypothesis. optdec: whether
the best value equals a stated value is decidable, by
Nat.decEq; the joined theorem states the resulting
disjunction as a proposition.

## Semantic mass

mass U s: the number of universe entries (counted with
multiplicity over U) that are members of s — the weight
of the state inside a fixed universe U. Monotone in the
state (massmono), subadditive under join (massjoin). It
captures how much of the universe the state covers; it
does not capture which codes, nor any structure among
them.

## Velocity

gains U path: the consecutive mass differences along a
path of states. telescope: along a componentwise
growing path, the gains sum with the first state's mass
to the last state's mass — velocity is exactly mass
change, no more and no less; it says nothing about the
cost or the cause of a transition.

## Redundancy

redone steps facts st: one step is redundant when its
conclusion is already a fact, or another recorded step
concludes the same fact from premises that are all
facts. redcount counts such steps. Soundness (redsound):
a step the test flags does have a derivable conclusion
— the flagged computation is provably redundant in the
one-step face. This is the decidable surface of the
persistence model's redundancy notion, imported at its
pin; the full elimination theorem — adjoining a
derivable fact changes the derivable set not at all —
is discharged in this vocabulary as Synthesis.elim.

## Scheduling suboptimality

makespan work idle is total work plus total idle.
schedsub is makespan minus the work sum, and equals
exactly the idle sum (thm.schedsub): the suboptimality
of a schedule, in this measure, is precisely its idle
time. It captures waiting; it does not capture ordering
effects between tasks, which are the ordering measure's
subject.

## Venue suboptimality

venuesub chosen venues is the chosen venue's cost minus
the least cost among the candidate venues. When the
chosen venue is among the candidates, the suboptimality
plus the best cost is exactly the chosen cost
(thm.venuesub): the measure is the exact excess over the
best available venue, and is zero exactly at an optimal
choice. It captures cost excess only, not latency or
any unlisted axis.

## Test set suboptimality

testsub U pool test is the mass of the parametric pool
minus the mass of the chosen test set, under universe U.
When the test set is contained in the pool, the
suboptimality is zero exactly when the masses are equal
(thm.testsub) — for finite counted mass, equal mass
under containment is coverage of everything the pool
covers in U. It captures coverage shortfall against the
pool; it does not capture the cost of running the set.

## Ordering

descents r path counts adjacent descents of a ranking r
along a path. ordzero characterizes a descent-free path
pair by pair, with ordnil and ordone as the empty and
singleton bases: a path is ordering-optimal exactly
when no adjacent pair descends. The measure counts
inversions against the ranking; it does not weight
their sizes.

## Content

content f U s is the mass of the projected state in the
projected universe, under a content map f. The naive
bound — content mass at most mass — is false: control
four is the counterexample (a constant map over universe
[0, 1] and state [0] gives content mass 2 against mass
1). The bound stands proposed only under injectivity of
the content map on the universe, which keeps the
projected universe duplicate-free. As defined, content
captures projected coverage counted with the projected
universe's multiplicities; it does not capture distinct
projected coverage unless the map is injective on U.

## The losses mirror

In the synthesis file's namespace: derive (a record's
level is its sum), the record gap and freeness on an
axis, the composition theorems (additive, projected,
split, gapfree, composed, wholefree, compound, tight,
monotone, localizes), the contract space and its
finiteness, and the axis checks with their soundness
(check, allcheck, sound, allsound). These are the losses
model's core results at its pin, over definitions
identical to its own, with proofs of this repo: losses
compose compoundingly, the bound is tight exactly at
the no-surplus point, and every loss in a whole
localizes to a component or interaction site.

## Domination, minimum, frontier

The joined theorem takes a domination relation over
states as a parameter. A minimum over a candidate list
is a member no other member dominates; the frontier is
the set of minima. The hypotheses hmin (a minimum
exists over every nonempty candidate list) and
hfrontier (every candidate is a minimum or is dominated
by one) are the vocabulary-independent content of the
persistence minimum theorem and the quantifiable
frontier theorem, restated at their pins in the spec's
provenance table; in the persistence model's own axes
vocabulary they are its theorems, not its premises.
