/-
  The composition across the family, in one development.

  Three forms of import, kept distinct. Mirrored and
  discharged: the losses core, restated over this file's
  identical definitions (the projection is the core file's
  own, the contract is the core file's two list form) with
  proofs of this repo, at the losses pin
  12ee66e9c9cdaeec4bea5eb8fb1fd61e6df780fb. Discharged in
  this vocabulary: the persistence elimination result, at
  eb01cf2e33a20bfbda5a03aba7a48c70fbd10741, proved here
  over this model's derivability. Restated hypotheses of
  the joined theorem: minimum existence and frontier
  completeness (persistence and quantifiable), certificate
  soundness and monotonicity (persistence), baseline free
  measurement and incremental equals full (profiling),
  bounds for the general measure interface (optimality),
  admission composition under its side condition
  (composable), checker soundness and cone exactness
  (incrementally safe), fold exactness under retraction
  (traceability), and quotient recovery by carrying
  (compilers lose info) — each taken at the pin the
  provenance table in the spec records. The compilers
  repo's general join semilattice claim is a labelled
  premise there; the lattice theorem below discharges it
  for recorded fact states, the class this model ranges
  over, and no wider.

  Named premises in the joined antecedent, unused by the
  conjunct proofs, binding applicability: contract
  fidelity (this program's gap G4), record fidelity and
  re-measure (losses), coverage (quantifiable), the spec
  authority premise (incrementally safe), witness
  faithfulness (profiling).
-/

import Core

namespace Synthesis

/-- The losses derivation: the level of a record is its
    sum. Mirrored from the losses core at its pin. -/
def derive (r : List Nat) : Nat :=
  r.sum

/-- The sum of an append is the sum of the sums. -/
theorem sumsplit : ∀ (a b : List Nat),
    (a ++ b).sum = a.sum + b.sum
  | [], _ => by simp
  | _ :: rest, b => by
    simp [List.sum_cons, sumsplit rest b, Nat.add_assoc]

/-- Additive recording: the derived level of a
    composition is the sum of the derived levels. -/
theorem additive (a b : List Nat) :
    derive (a ++ b) = derive a + derive b := by
  show (a ++ b).sum = a.sum + b.sum
  exact sumsplit a b

/-- Projection is compositional per axis. The projection
    here is the core file's, identical to the losses
    projection. -/
theorem projected (f : Nat → Nat) (a b : List Nat) :
    project f (a ++ b) = project f a + project f b := by
  show ((a ++ b).map f).sum = (a.map f).sum + (b.map f).sum
  rw [List.map_append]
  exact sumsplit (a.map f) (b.map f)

/-- The three way split of a projection over two parts
    and their interaction. -/
theorem split (f : Nat → Nat) (a inter b : List Nat) :
    project f (a ++ inter ++ b)
      = project f a + project f inter + project f b := by
  rw [projected f (a ++ inter) b, projected f a inter]

/-- A gap on an axis: the shortfall against a required
    level. (The core file's gap is the bounds gap of a
    candidate list; this is the losses record gap, in
    this namespace.) -/
def gap (f : Nat → Nat) (req : Nat) (r : List Nat) : Nat :=
  req - project f r

/-- Loss freeness on one axis. -/
def free (f : Nat → Nat) (req : Nat) (r : List Nat) : Prop :=
  req ≤ project f r

/-- Gap zero is loss freeness. -/
theorem gapfree (f : Nat → Nat) (req : Nat) (r : List Nat) :
    gap f req r = 0 ↔ free f req r :=
  Nat.sub_eq_zero_iff_le

/-- Two part composition of loss freeness. -/
theorem composed (f : Nat → Nat) (s1 s2 : Nat)
    (a b : List Nat)
    (h1 : free f s1 a) (h2 : free f s2 b) :
    free f (s1 + s2) (a ++ b) := by
  unfold free at *
  rw [projected]
  omega

/-- The structural fix theorem: components and the
    recorded interaction loss free against their shares
    give the composition loss free against the sum. -/
theorem wholefree (f : Nat → Nat) (s1 si s2 : Nat)
    (a inter b : List Nat)
    (h1 : free f s1 a) (hi : free f si inter)
    (h2 : free f s2 b) :
    free f (s1 + si + s2) (a ++ inter ++ b) := by
  unfold free at *
  rw [split f a inter b]
  omega

/-- Gaps compose compoundingly: the gap of a composition
    is at most the sum of the component and interaction
    gaps. -/
theorem compound (f : Nat → Nat) (s1 si s2 : Nat)
    (a inter b : List Nat) :
    gap f (s1 + si + s2) (a ++ inter ++ b)
      ≤ gap f s1 a + gap f si inter + gap f s2 b := by
  unfold gap
  rw [split f a inter b]
  omega

/-- The compounding bound is tight at the no surplus
    point: when no site runs a surplus over its share,
    the gap of the composition is exactly the sum. The
    residual under surplus is exactly the surplus that
    masks a site gap, by truncated subtraction. -/
theorem tight (f : Nat → Nat) (s1 si s2 : Nat)
    (a inter b : List Nat)
    (h1 : project f a ≤ s1) (hi : project f inter ≤ si)
    (h2 : project f b ≤ s2) :
    gap f (s1 + si + s2) (a ++ inter ++ b)
      = gap f s1 a + gap f si inter + gap f s2 b := by
  unfold gap
  rw [split f a inter b]
  omega

/-- The gap is monotone in each component. -/
theorem monotone (f : Nat → Nat) (req : Nat)
    (a b : List Nat) (h : project f a ≤ project f b) :
    gap f req b ≤ gap f req a := by
  unfold gap
  omega

/-- Localization: a gap in the whole is a gap at a
    component site or at the interaction site. -/
theorem localizes (f : Nat → Nat) (s1 si s2 : Nat)
    (a inter b : List Nat)
    (h : project f (a ++ inter ++ b) < s1 + si + s2) :
    project f a < s1 ∨ project f inter < si
      ∨ project f b < s2 := by
  rw [split f a inter b] at h
  omega

/-- The problem space of a contract: the grid of its
    two lists, the core file's grid. -/
def space (c : Contract) : List (Nat × Nat) :=
  grid c.caps c.designs

/-- Finiteness, derived: the space size is the computed
    product of the two list lengths. -/
theorem finite (c : Contract) :
    (space c).length = c.caps.length * c.designs.length :=
  gridlength c.caps c.designs

/-- The analysis check on one axis. -/
def check (f : Nat → Nat) (req : Nat) (r : List Nat) : Bool :=
  decide (req ≤ project f r)

/-- A passing check implies loss freeness. -/
theorem sound (f : Nat → Nat) (req : Nat) (r : List Nat)
    (h : check f req r = true) : free f req r := by
  unfold check at h
  have h2 : req ≤ project f r := of_decide_eq_true h
  exact h2

/-- The analysis over a list of axes. -/
def allcheck (axes : List (Nat → Nat)) (req : Nat)
    (r : List Nat) : Bool :=
  axes.all (fun f => check f req r)

/-- A passing full verdict implies loss freeness on
    every axis in the list. -/
theorem allsound (axes : List (Nat → Nat)) (req : Nat)
    (r : List Nat) (h : allcheck axes req r = true) :
    ∀ f ∈ axes, free f req r := by
  intro f hf
  unfold allcheck at h
  rw [List.all_eq_true] at h
  exact sound f req r (h f hf)

/-- Elimination, the persistence result at its pin,
    discharged in this model's vocabulary: adjoining an
    already derivable fact to the state changes the
    derivable set not at all, in both directions. The
    side conditions are the hypotheses: the fact is
    derivable from the state as it stands. -/
theorem elim {steps : List Step} {s : List Nat} {c x : Nat}
    (hc : Deriv steps s c) :
    Deriv steps (c :: s) x ↔ Deriv steps s x := by
  constructor
  · intro h
    induction h with
    | base hmem =>
      cases List.mem_cons.mp hmem with
      | inl h => subst h; exact hc
      | inr h => exact Deriv.base h
    | step hst _ ih => exact Deriv.step hst ih
  · intro h
    exact derivmono (fun y hy => List.mem_cons_of_mem c hy) h

/-- The recorded state lattice: states up to membership
    equivalence, ordered by information, form a join
    semilattice, join the least upper bound. This is the
    instance that discharges, for recorded fact states,
    the general join semilattice premise the compilers
    repo labels. -/
theorem lattice (s t u : List Nat) :
    equiv (join s t) (join t s)
    ∧ equiv (join (join s t) u) (join s (join t u))
    ∧ equiv (join s s) s
    ∧ (le s u → le t u → le (join s t) u) :=
  ⟨joincomm s t, joinassoc s t u, joinidem s,
   fun hs ht => joinleast s t u hs ht⟩

/- The joined theorem: the method for an arbitrary
    system under an arbitrary qualification, assembled
    from this model's theorems, the mirrored losses core,
    the discharged elimination result, and the restated
    family hypotheses at their pins, under the named
    premises. Conjunct by conjunct: the round trips and
    qualification equivalence; agreement of the two
    derivation routes under a complete recording; the
    description bound and its vanishing against the
    power of two; bounds attained and inside, with the
    certified optimum at a floor; tightening under
    candidate join; the finite candidate count and the
    decidable optimum question; certified derivability
    with elimination and certificate monotonicity;
    checked loss freeness of the composed record;
    minimum existence over the candidate list; frontier
    completeness; baseline free measurement and
    incremental equals full; admission composition;
    safety from checker acceptance with cone exactness;
    fold exactness under retraction; quotient recovery
    by carrying; and the recorded state lattice. The
    premises binder binds applicability and does not
    enter the conjunct proofs, so the unused variable
    linter is scoped off for this declaration, the
    family's form for a premises argument. -/
set_option linter.unusedVariables false in
theorem joined
    (ContractFaith RecordFaith Remeasure Coverage
      SpecAuthority WitnessFaith : Prop)
    (hprem : ContractFaith ∧ RecordFaith ∧ Remeasure
      ∧ Coverage ∧ SpecAuthority ∧ WitnessFaith)
    (Dom : List Nat → List Nat → Prop)
    (hmin : ∀ (cands : List (List Nat)), cands ≠ [] →
      ∃ r ∈ cands, ∀ s ∈ cands, ¬ Dom s r)
    (hfrontier : ∀ (cands : List (List Nat)) (r : List Nat),
      r ∈ cands → (∀ s ∈ cands, ¬ Dom s r)
        ∨ ∃ m ∈ cands, (∀ s ∈ cands, ¬ Dom s m) ∧ Dom m r)
    (checkCert : List Step → List Nat → Nat → List Step → Bool)
    (hcertsound : ∀ (steps : List Step) (s : List Nat)
      (t : Nat) (cert : List Step),
      checkCert steps s t cert = true → Deriv steps s t)
    (hcertmono : ∀ (steps steps' : List Step)
      (s s' : List Nat) (t : Nat) (cert : List Step),
      checkCert steps s t cert = true →
      (∀ st ∈ steps, st ∈ steps') → le s s' →
      checkCert steps' s' t cert = true)
    (wmeasure profbase : List Nat → Nat)
    (hprof : ∀ w, profbase w = wmeasure w)
    (full : List Nat → Nat) (incr : List Nat → List Nat → Nat)
    (h_incr : ∀ base add, incr base add = full (base ++ add))
    (IC : Prop) (Adm : List Nat → Prop)
    (h_adm : IC → ∀ a b, Adm a → Adm b → Adm (a ++ b))
    (hic : IC)
    (Safe : List Nat → Prop) (scheck : List Nat → Bool)
    (h_ssound : ∀ r, scheck r = true → Safe r)
    (cone affected : List Nat → List Nat)
    (h_cone : ∀ r, cone r = affected r)
    (foldf : List Nat → List Nat)
    (h_fold : ∀ (stream keep : List Nat),
      foldf (stream.filter (fun e => decide (e ∈ keep)))
        = (foldf stream).filter (fun e => decide (e ∈ keep)))
    (G A Q : Type) (carry : G → A) (recover : A → Q)
    (qual : G → Q)
    (h_carry : ∀ g, recover (carry g) = qual g)
    (sys : Sys) (axes : List (Nat → Nat))
    (chunks : List (List Nat))
    (hchunks : chunks.flatten = sys.record)
    (m : List Nat → Nat) (L : List (List Nat)) (hne : L ≠ [])
    (F : Nat) (hfloor : ∀ s ∈ L, F ≤ m s)
    (laxes : List (Nat → Nat)) (req : Nat)
    (ra ri rb : List Nat)
    (hcheck : allcheck laxes req (ra ++ ri ++ rb) = true)
    (hadm : Adm ra ∧ Adm ri ∧ Adm rb)
    (cert : List Step) (t : Nat)
    (hcert : checkCert sys.steps sys.facts t cert = true) :
    (analyze (synth (analyze sys)) = analyze sys
      ∧ qequiv axes (synth (analyze sys)) sys
      ∧ reeng sys = analyze sys)
    ∧ (analyzechunks sys chunks = analyze sys)
    ∧ (desc (analyze sys)
        ≤ sys.record.length + sys.steps.length
      ∧ desc (analyze sys) < 2 ^ desc (analyze sys))
    ∧ ((∃ s ∈ L, m s = lo m L) ∧ (∃ s ∈ L, m s = hi m L)
      ∧ (∀ s ∈ L, lo m L ≤ m s ∧ m s ≤ hi m L)
      ∧ (best m L = F →
          ∃ s ∈ L, m s = F ∧ ∀ u ∈ L, m s ≤ m u))
    ∧ (∀ L2 : List (List Nat), best m (L ++ L2) ≤ best m L
      ∧ _root_.gap m F (L ++ L2) ≤ _root_.gap m F L)
    ∧ ((grid (analyze sys).caps (analyze sys).designs).length
        = (analyze sys).caps.length
          * (analyze sys).designs.length
      ∧ (best m L = F ∨ best m L ≠ F))
    ∧ (Deriv sys.steps sys.facts t
      ∧ (∀ x, Deriv sys.steps (t :: sys.facts) x
          ↔ Deriv sys.steps sys.facts x)
      ∧ (∀ steps', (∀ st ∈ sys.steps, st ∈ steps') →
          checkCert steps' sys.facts t cert = true))
    ∧ (∀ f ∈ laxes, free f req (ra ++ ri ++ rb))
    ∧ (∃ r ∈ L, ∀ s ∈ L, ¬ Dom s r)
    ∧ (∀ r ∈ L, (∀ s ∈ L, ¬ Dom s r)
        ∨ ∃ mm ∈ L, (∀ s ∈ L, ¬ Dom s mm) ∧ Dom mm r)
    ∧ (profbase sys.record = wmeasure sys.record
      ∧ incr sys.record sys.record
        = full (sys.record ++ sys.record))
    ∧ (Adm (ra ++ ri ++ rb))
    ∧ ((scheck (ra ++ ri ++ rb) = true
        → Safe (ra ++ ri ++ rb))
      ∧ cone sys.record = affected sys.record)
    ∧ (foldf (sys.record.filter
          (fun e => decide (e ∈ sys.facts)))
      = (foldf sys.record).filter
          (fun e => decide (e ∈ sys.facts)))
    ∧ (∀ g, recover (carry g) = qual g)
    ∧ (∀ s t u : List Nat,
        equiv (join s t) (join t s)
        ∧ equiv (join (join s t) u) (join s (join t u))
        ∧ equiv (join s s) s
        ∧ (le s u → le t u → le (join s t) u)) := by
  have hcert' : Deriv sys.steps sys.facts t :=
    hcertsound sys.steps sys.facts t cert hcert
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · exact ⟨rtone (analyze sys), rttwo axes sys,
      thm.reeng sys⟩
  · exact agree sys chunks hchunks
  · exact ⟨small sys, powbound (desc (analyze sys))⟩
  · obtain ⟨hatt1, hatt2⟩ := attained m L hne
    exact ⟨hatt1, hatt2,
      fun s hs => inbounds m L s hs,
      fun h => certified m F L hfloor h hne⟩
  · intro L2
    exact tighten m F L L2 hne
  · refine ⟨_root_.finite (analyze sys), ?_⟩
    cases optdec m L F with
    | isTrue h => exact Or.inl h
    | isFalse h => exact Or.inr h
  · exact ⟨hcert', fun x => elim hcert',
      fun steps' hsub => hcertmono sys.steps steps'
        sys.facts sys.facts t cert hcert hsub
        (fun y hy => hy)⟩
  · exact allsound laxes req (ra ++ ri ++ rb) hcheck
  · exact hmin L hne
  · exact fun r hr => hfrontier L r hr
  · exact ⟨hprof sys.record, h_incr sys.record sys.record⟩
  · exact h_adm hic (ra ++ ri) rb
      (h_adm hic ra ri hadm.1 hadm.2.1) hadm.2.2
  · exact ⟨fun h => h_ssound _ h, h_cone sys.record⟩
  · exact h_fold sys.record sys.facts
  · exact h_carry
  · exact fun s t u => lattice s t u

end Synthesis

#print axioms Synthesis.sumsplit
#print axioms Synthesis.additive
#print axioms Synthesis.projected
#print axioms Synthesis.split
#print axioms Synthesis.gapfree
#print axioms Synthesis.composed
#print axioms Synthesis.wholefree
#print axioms Synthesis.compound
#print axioms Synthesis.tight
#print axioms Synthesis.monotone
#print axioms Synthesis.localizes
#print axioms Synthesis.finite
#print axioms Synthesis.sound
#print axioms Synthesis.allsound
#print axioms Synthesis.elim
#print axioms Synthesis.lattice
#print axioms Synthesis.joined
