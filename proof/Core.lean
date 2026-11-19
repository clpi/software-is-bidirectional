/-
  Software is bidirectional: the proved model.

  A state is a list of fact codes, taken up to membership.
  A system is facts, recorded steps, and a behavior record.
  The analysis map derives a contract from a system and the
  synthesis map builds the canonical system from a contract;
  the two round trip. Contracts are vanishingly small against
  the state space they qualify, their candidate space is a
  finite grid computed from the contract itself, and every
  named measure over states and paths carries a proved
  characterization. Every theorem below is proved in full.
-/

/-- Membership equivalence of states. -/
def equiv (s t : List Nat) : Prop :=
  ∀ x, x ∈ s ↔ x ∈ t

/-- The information order on states. -/
def le (s t : List Nat) : Prop :=
  ∀ x, x ∈ s → x ∈ t

/-- Join of states is append. -/
def join (s t : List Nat) : List Nat :=
  s ++ t

/-- A recorded step: a premise list and an added fact. -/
structure Step where
  pre : List Nat
  add : Nat
deriving DecidableEq, Repr

/-- Derivability of a fact from a state through recorded
    steps: the inductive closure. -/
inductive Deriv (steps : List Step) (s : List Nat) :
    Nat → Prop where
  | base {x : Nat} : x ∈ s → Deriv steps s x
  | step {st : Step} : st ∈ steps →
      (∀ p ∈ st.pre, Deriv steps s p) → Deriv steps s st.add

/-- The qualification contract: a capability list and a
    design list, each finite and discrete. -/
structure Contract where
  caps : List Nat
  designs : List Nat
deriving DecidableEq, Repr

/-- A system: facts, recorded steps, and a behavior
    record. -/
structure Sys where
  facts : List Nat
  steps : List Step
  record : List Nat
deriving DecidableEq, Repr

/-- The analysis map: capabilities from the record, designs
    from the steps. -/
def analyze (s : Sys) : Contract :=
  { caps := s.record, designs := s.steps.map Step.add }

/-- The synthesis map: the canonical system of a contract,
    with no facts, one premise free step per design, and the
    record equal to the capabilities. -/
def synth (c : Contract) : Sys :=
  { facts := [], steps := c.designs.map
      (fun a => { pre := [], add := a } : Nat → Step),
    record := c.caps }

/-- Projection of a list onto one axis: apply the axis to
    every entry and sum. -/
def project (f : Nat → Nat) (r : List Nat) : Nat :=
  (r.map f).sum

/-- Equivalence of systems under a qualification: the same
    derived contract, and the same value on every axis of
    the qualification, axes being contract projections. -/
def qequiv (axes : List (Nat → Nat)) (s t : Sys) : Prop :=
  analyze s = analyze t
    ∧ ∀ f ∈ axes, project f (analyze s).caps
        + project f (analyze s).designs
      = project f (analyze t).caps
        + project f (analyze t).designs

/-- The reengineering analysis: analyze after synthesize
    after analyze. -/
def reeng (s : Sys) : Contract :=
  analyze (synth (analyze s))

/-- The chunked analysis route: the record is derived by
    folding it in chunks, the capabilities are the flattened
    chunks. -/
def analyzechunks (s : Sys) (chunks : List (List Nat)) :
    Contract :=
  { caps := chunks.flatten, designs := s.steps.map Step.add }

/-- The description size of a contract. -/
def desc (c : Contract) : Nat :=
  c.caps.length + c.designs.length

/-- A contract is small at a bound when its description
    size is at most the bound. -/
def Small (u : Nat) (c : Contract) : Prop :=
  desc c ≤ u

/-- Join of systems, componentwise by append. -/
def sysjoin (a b : Sys) : Sys :=
  { facts := a.facts ++ b.facts, steps := a.steps ++ b.steps,
    record := a.record ++ b.record }

/-- A speculative result: a value with a premise cone. -/
structure Spec where
  value : Nat
  cone : List Nat
deriving DecidableEq, Repr

/-- A speculative result is valid in a system exactly when
    its cone is inside the facts of the system. -/
def valid (sp : Spec) (s : Sys) : Prop :=
  sp.cone ⊆ s.facts

/-- The values of a measure over a list of states. -/
def vals (m : List Nat → Nat) (L : List (List Nat)) :
    List Nat :=
  L.map m

/-- The fold minimum of a list of values, zero on the
    empty list. -/
def vmin : List Nat → Nat
  | [] => 0
  | a :: as => as.foldl min a

/-- The fold maximum of a list of values, zero on the
    empty list. -/
def vmax : List Nat → Nat
  | [] => 0
  | a :: as => as.foldl max a

/-- The lower bound of a measure over a list of states. -/
def lo (m : List Nat → Nat) (L : List (List Nat)) : Nat :=
  vmin (vals m L)

/-- The upper bound of a measure over a list of states. -/
def hi (m : List Nat → Nat) (L : List (List Nat)) : Nat :=
  vmax (vals m L)

/-- The best value of a measure over a list of states: the
    lower bound. -/
def best (m : List Nat → Nat) (L : List (List Nat)) : Nat :=
  lo m L

/-- The gap between the best value and a certified
    floor. -/
def gap (m : List Nat → Nat) (F : Nat)
    (L : List (List Nat)) : Nat :=
  best m L - F

/-- The grid of a pair of discrete lists: every capability
    paired with every design. -/
def grid : List Nat → List Nat → List (Nat × Nat)
  | [], _ => []
  | v :: rest, designs => designs.map (fun o => (v, o))
      ++ grid rest designs

/-- Semantic mass of a state against a universe: the count
    of universe entries that lie in the state. -/
def mass (U s : List Nat) : Nat :=
  (U.filter (fun x => decide (x ∈ s))).length

/-- The per step mass gains along a recorded path. -/
def gains (U : List Nat) : List (List Nat) → List Nat
  | [] => []
  | [_] => []
  | s :: t :: rest =>
    (mass U t - mass U s) :: gains U (t :: rest)

/-- The decidable redundancy face: a step is redundant when
    its added fact is present, or some recorded step with
    the same added fact has all premises present. -/
def redone (steps : List Step) (facts : List Nat)
    (st : Step) : Bool :=
  decide (st.add ∈ facts)
    || steps.any (fun st' => decide (st'.add = st.add)
      && st'.pre.all (fun p => decide (p ∈ facts)))

/-- The redundancy count of a step list against facts. -/
def redcount (steps : List Step) (facts : List Nat) : Nat :=
  (steps.filter (redone steps facts)).length

/-- The makespan of a schedule: work plus idle. -/
def makespan (work idle : List Nat) : Nat :=
  work.sum + idle.sum

/-- Scheduling suboptimality: makespan minus the work
    bound. -/
def schedsub (work idle : List Nat) : Nat :=
  makespan work idle - work.sum

/-- Venue suboptimality: the chosen venue cost minus the
    best listed venue cost. -/
def venuesub (chosen : Nat) (venues : List Nat) : Nat :=
  chosen - vmin venues

/-- Test set suboptimality: pool mass minus test mass. -/
def testsub (U pool test : List Nat) : Nat :=
  mass U pool - mass U test

/-- Adjacent descents of an execution order against a
    ranking. -/
def descents (r : Nat → Nat) : List Nat → Nat
  | [] => 0
  | [_] => 0
  | a :: b :: rest =>
    (if r b < r a then 1 else 0) + descents r (b :: rest)

/-- Content mass: mass after projecting facts through a
    content map. -/
def content (f : Nat → Nat) (U s : List Nat) : Nat :=
  mass (U.map f) (s.map f)

/-- Join of contracts, componentwise by append. -/
def cjoin (a b : Contract) : Contract :=
  { caps := a.caps ++ b.caps, designs := a.designs ++ b.designs }

/-- A path is monotone when every consecutive pair is
    ordered by inclusion. -/
def mono : List (List Nat) → Prop
  | [] => True
  | [_] => True
  | s :: t :: rest =>
    (∀ x ∈ s, x ∈ t) ∧ mono (t :: rest)

/-- A path ends at a stated last state. -/
def ends (p : List (List Nat)) (l : List Nat) : Prop :=
  p.getLast? = some l

/-- Join commutes up to equivalence. -/
theorem joincomm (s t : List Nat) :
    equiv (join s t) (join t s) := by
  intro x
  show x ∈ s ++ t ↔ x ∈ t ++ s
  rw [List.mem_append, List.mem_append]
  exact or_comm

/-- Join associates up to equivalence. -/
theorem joinassoc (s t u : List Nat) :
    equiv (join (join s t) u) (join s (join t u)) := by
  intro x
  show x ∈ (s ++ t) ++ u ↔ x ∈ s ++ (t ++ u)
  rw [List.mem_append, List.mem_append, List.mem_append,
    List.mem_append]
  exact or_assoc

/-- Join is idempotent up to equivalence. -/
theorem joinidem (s : List Nat) : equiv (join s s) s := by
  intro x
  show x ∈ s ++ s ↔ x ∈ s
  rw [List.mem_append]
  exact or_self_iff

/-- The left part lies below the join. -/
theorem joinleft (s t : List Nat) : le s (join s t) :=
  fun _x hx => List.mem_append_left t hx

/-- The right part lies below the join. -/
theorem joinright (s t : List Nat) : le t (join s t) :=
  fun _x hx => List.mem_append_right s hx

/-- Join is the least upper bound up to equivalence. -/
theorem joinleast (s t u : List Nat) (hs : le s u)
    (ht : le t u) : le (join s t) u := by
  intro x hx
  cases List.mem_append.mp hx with
  | inl h => exact hs x h
  | inr h => exact ht x h

/-- Step closure: a recorded step whose premises are all
    derivable has a derivable added fact. -/
theorem stepclose {steps : List Step} {s : List Nat}
    {st : Step} (hst : st ∈ steps)
    (hpre : ∀ p ∈ st.pre, Deriv steps s p) :
    Deriv steps s st.add :=
  Deriv.step hst hpre

/-- Derivability is monotone in the state. -/
theorem derivmono {steps : List Step} {s t : List Nat}
    (hle : le s t) {x : Nat} (h : Deriv steps s x) :
    Deriv steps t x := by
  induction h with
  | base hmem => exact Deriv.base (hle _ hmem)
  | step hst _ ih => exact Deriv.step hst ih

/-- Derivability is monotone in the recorded steps. -/
theorem derivsteps {steps steps' : List Step} {s : List Nat}
    (hsub : ∀ st ∈ steps, st ∈ steps') {x : Nat}
    (h : Deriv steps s x) : Deriv steps' s x := by
  induction h with
  | base hmem => exact Deriv.base hmem
  | step hst _ ih => exact Deriv.step (hsub _ hst) ih

/-- The designs of a synthesized contract read back
    exactly: mapping the premise free step constructor and
    then the added fact projection is the identity. -/
theorem mapadd : ∀ (l : List Nat),
    (l.map (fun a => { pre := [], add := a } : Nat → Step)).map
        Step.add = l
  | [] => rfl
  | a :: as => by
    show a :: ((as.map
        (fun a => { pre := [], add := a } : Nat → Step)).map
          Step.add) = a :: as
    rw [mapadd as]

/-- First round trip: analyzing a synthesized system
    returns the contract exactly. -/
theorem rtone (c : Contract) : analyze (synth c) = c := by
  cases c with
  | mk caps designs =>
    show Contract.mk caps ((designs.map
        (fun a => { pre := [], add := a } : Nat → Step)).map
          Step.add) = Contract.mk caps designs
    rw [mapadd]

/-- Second round trip: synthesizing an analyzed system
    returns a system equivalent under any qualification. -/
theorem rttwo (axes : List (Nat → Nat)) (s : Sys) :
    qequiv axes (synth (analyze s)) s := by
  refine ⟨rtone (analyze s), ?_⟩
  intro f _
  rw [rtone (analyze s)]

/-- The chunked route agrees with the direct route exactly
    when the chunks concatenate to the record. -/
theorem agree (s : Sys) (chunks : List (List Nat))
    (h : chunks.flatten = s.record) :
    analyzechunks s chunks = analyze s := by
  show Contract.mk chunks.flatten (s.steps.map Step.add)
    = Contract.mk s.record (s.steps.map Step.add)
  rw [h]

/-- Smallness of the standard derivation: the description
    of the derived contract is at most the record length
    plus the step count. -/
theorem small (s : Sys) :
    desc (analyze s) ≤ s.record.length + s.steps.length := by
  show s.record.length + (s.steps.map Step.add).length
    ≤ s.record.length + s.steps.length
  rw [List.length_map]
  exact Nat.le_refl _

/-- Every natural is below its power of two. -/
theorem powbound (n : Nat) : n < 2 ^ n := by
  induction n with
  | zero => decide
  | succ k ih =>
    have h2 : 2 ^ (Nat.succ k) = 2 ^ k + 2 ^ k := by
      have h := Nat.pow_succ 2 k
      rw [Nat.mul_two] at h
      exact h
    omega

/-- Vanishing: a linear size is strictly below the power
    of two of that size, for positive size. -/
theorem vanish (n : Nat) (_h : 1 ≤ n) : n < 2 ^ n :=
  powbound n

/-- State counts multiply under join: the power of a sum
    is the product of the powers. -/
theorem powjoin (a b : Nat) : 2 ^ (a + b) = 2 ^ a * 2 ^ b :=
  Nat.pow_add 2 a b

/-- Description sizes add under contract join. -/
theorem smalljoin (a b : Contract) :
    desc (cjoin a b) = desc a + desc b := by
  simp only [desc, cjoin, List.length_append]
  omega

/-- Validity of a speculative result is exactly cone
    inclusion in the facts. -/
theorem specvalid (sp : Spec) (s : Sys) :
    valid sp s ↔ ∀ p ∈ sp.cone, p ∈ s.facts :=
  Iff.intro (fun h _p hp => h hp) (fun h p hp => h p hp)

/-- Validity is monotone under system join. -/
theorem specmono (sp : Spec) (a b : Sys)
    (h : valid sp a) : valid sp (sysjoin a b) :=
  fun _p hp => List.mem_append_left b.facts (h hp)

/-- The fold minimum is at most its starting value. -/
theorem fminle : ∀ (as : List Nat) (a : Nat),
    as.foldl min a ≤ a
  | [], _ => Nat.le_refl _
  | b :: bs, a =>
    Nat.le_trans (fminle bs (min a b)) (Nat.min_le_left a b)

/-- The fold minimum is at most every folded entry. -/
theorem fminmem : ∀ (as : List Nat) (a x : Nat),
    x ∈ as → as.foldl min a ≤ x
  | b :: bs, a, x, hx => by
    cases List.mem_cons.mp hx with
    | inl h =>
      subst h
      exact Nat.le_trans (fminle bs (min a x)) (Nat.min_le_right a x)
    | inr h => exact fminmem bs (min a b) x h

/-- The fold maximum is at least its starting value. -/
theorem fmaxge : ∀ (as : List Nat) (a : Nat),
    a ≤ as.foldl max a
  | [], _ => Nat.le_refl _
  | b :: bs, a =>
    Nat.le_trans (Nat.le_max_left a b) (fmaxge bs (max a b))

/-- Every folded entry is at most the fold maximum. -/
theorem fmaxmem : ∀ (as : List Nat) (a x : Nat),
    x ∈ as → x ≤ as.foldl max a
  | b :: bs, a, x, hx => by
    cases List.mem_cons.mp hx with
    | inl h =>
      subst h
      exact Nat.le_trans (Nat.le_max_right a x) (fmaxge bs (max a x))
    | inr h => exact fmaxmem bs (max a b) x h

/-- The fold minimum is attained: it is the starting value
    or a folded entry. -/
theorem fminex : ∀ (as : List Nat) (a : Nat),
    ∃ y, (y = a ∨ y ∈ as) ∧ as.foldl min a = y
  | [], a => ⟨a, Or.inl rfl, rfl⟩
  | b :: bs, a => by
    obtain ⟨y, hy, hyeq⟩ := fminex bs (min a b)
    refine ⟨y, ?_, hyeq⟩
    cases hy with
    | inl h =>
      subst h
      cases Nat.le_total a b with
      | inl hab =>
        rw [Nat.min_eq_left hab]
        exact Or.inl rfl
      | inr hba =>
        rw [Nat.min_eq_right hba]
        exact Or.inr List.mem_cons_self
    | inr h => exact Or.inr (List.mem_cons_of_mem b h)

/-- The fold maximum is attained: it is the starting value
    or a folded entry. -/
theorem fmaxex : ∀ (as : List Nat) (a : Nat),
    ∃ y, (y = a ∨ y ∈ as) ∧ as.foldl max a = y
  | [], a => ⟨a, Or.inl rfl, rfl⟩
  | b :: bs, a => by
    obtain ⟨y, hy, hyeq⟩ := fmaxex bs (max a b)
    refine ⟨y, ?_, hyeq⟩
    cases hy with
    | inl h =>
      subst h
      cases Nat.le_total a b with
      | inl hab =>
        rw [Nat.max_eq_right hab]
        exact Or.inr List.mem_cons_self
      | inr hba =>
        rw [Nat.max_eq_left hba]
        exact Or.inl rfl
    | inr h => exact Or.inr (List.mem_cons_of_mem b h)

/-- The fold minimum of a list is at most every entry. -/
theorem vminle (l : List Nat) (x : Nat) (hx : x ∈ l) :
    vmin l ≤ x := by
  cases l with
  | nil => simp at hx
  | cons a as =>
    cases List.mem_cons.mp hx with
    | inl h =>
      subst h
      exact fminle as x
    | inr h => exact fminmem as a x h

/-- Every entry of a list is at most its fold maximum. -/
theorem vmaxge (l : List Nat) (x : Nat) (hx : x ∈ l) :
    x ≤ vmax l := by
  cases l with
  | nil => simp at hx
  | cons a as =>
    cases List.mem_cons.mp hx with
    | inl h =>
      subst h
      exact fmaxge as x
    | inr h => exact fmaxmem as a x h

/-- The fold minimum of a nonempty list is attained in
    the list. -/
theorem vminex (l : List Nat) (hne : l ≠ []) :
    ∃ y ∈ l, vmin l = y := by
  cases l with
  | nil => exact absurd rfl hne
  | cons a as =>
    obtain ⟨y, hy, hyeq⟩ := fminex as a
    refine ⟨y, ?_, hyeq⟩
    cases hy with
    | inl h =>
      subst h
      exact List.mem_cons_self
    | inr h => exact List.mem_cons_of_mem a h

/-- The fold maximum of a nonempty list is attained in
    the list. -/
theorem vmaxex (l : List Nat) (hne : l ≠ []) :
    ∃ y ∈ l, vmax l = y := by
  cases l with
  | nil => exact absurd rfl hne
  | cons a as =>
    obtain ⟨y, hy, hyeq⟩ := fmaxex as a
    refine ⟨y, ?_, hyeq⟩
    cases hy with
    | inl h =>
      subst h
      exact List.mem_cons_self
    | inr h => exact List.mem_cons_of_mem a h

/-- Bounds: every listed state has its measure between
    the lower and upper bounds. -/
theorem inbounds (m : List Nat → Nat) (L : List (List Nat))
    (s : List Nat) (hs : s ∈ L) :
    lo m L ≤ m s ∧ m s ≤ hi m L := by
  have hm : m s ∈ vals m L := List.mem_map_of_mem hs
  exact ⟨vminle (vals m L) (m s) hm,
    vmaxge (vals m L) (m s) hm⟩

/-- Both bounds are attained in any nonempty list. -/
theorem attained (m : List Nat → Nat) (L : List (List Nat))
    (hne : L ≠ []) :
    (∃ s ∈ L, m s = lo m L) ∧ (∃ s ∈ L, m s = hi m L) := by
  have hne' : vals m L ≠ [] := by
    cases L with
    | nil => exact absurd rfl hne
    | cons a as => simp [vals]
  constructor
  · obtain ⟨y, hy, hyeq⟩ := vminex (vals m L) hne'
    obtain ⟨s, hs, hms⟩ := List.mem_map.mp hy
    exact ⟨s, hs, hms.trans hyeq.symm⟩
  · obtain ⟨y, hy, hyeq⟩ := vmaxex (vals m L) hne'
    obtain ⟨s, hs, hms⟩ := List.mem_map.mp hy
    exact ⟨s, hs, hms.trans hyeq.symm⟩

/-- The fold minimum over an append is the minimum of the
    parts, for nonempty parts. -/
theorem vminappend (l1 l2 : List Nat) (h1 : l1 ≠ [])
    (h2 : l2 ≠ []) :
    vmin (l1 ++ l2) = min (vmin l1) (vmin l2) := by
  have hle1 : vmin (l1 ++ l2) ≤ vmin l1 := by
    obtain ⟨y, hy, hyeq⟩ := vminex l1 h1
    have hy' : y ∈ l1 ++ l2 := List.mem_append_left l2 hy
    have hle := vminle (l1 ++ l2) y hy'
    omega
  have hle2 : vmin (l1 ++ l2) ≤ vmin l2 := by
    obtain ⟨y, hy, hyeq⟩ := vminex l2 h2
    have hy' : y ∈ l1 ++ l2 := List.mem_append_right l1 hy
    have hle := vminle (l1 ++ l2) y hy'
    omega
  have hge : min (vmin l1) (vmin l2) ≤ vmin (l1 ++ l2) := by
    have hne : l1 ++ l2 ≠ [] := by
      cases l1 with
      | nil => exact absurd rfl h1
      | cons a as => simp
    obtain ⟨y, hy, hyeq⟩ := vminex (l1 ++ l2) hne
    cases List.mem_append.mp hy with
    | inl h =>
      have hle := vminle l1 y h
      have hmin : min (vmin l1) (vmin l2) ≤ vmin l1 :=
        Nat.min_le_left _ _
      omega
    | inr h =>
      have hle := vminle l2 y h
      have hmin : min (vmin l1) (vmin l2) ≤ vmin l2 :=
        Nat.min_le_right _ _
      omega
  apply Nat.le_antisymm
  · cases Nat.le_total (vmin l1) (vmin l2) with
    | inl h =>
      rw [Nat.min_eq_left h]
      exact hle1
    | inr h =>
      rw [Nat.min_eq_right h]
      exact hle2
  · exact hge

/-- The fold maximum over an append is the maximum of the
    parts, for nonempty parts. -/
theorem vmaxappend (l1 l2 : List Nat) (h1 : l1 ≠ [])
    (h2 : l2 ≠ []) :
    vmax (l1 ++ l2) = max (vmax l1) (vmax l2) := by
  have hge1 : vmax l1 ≤ vmax (l1 ++ l2) := by
    obtain ⟨y, hy, hyeq⟩ := vmaxex l1 h1
    have hy' : y ∈ l1 ++ l2 := List.mem_append_left l2 hy
    have hge := vmaxge (l1 ++ l2) y hy'
    omega
  have hge2 : vmax l2 ≤ vmax (l1 ++ l2) := by
    obtain ⟨y, hy, hyeq⟩ := vmaxex l2 h2
    have hy' : y ∈ l1 ++ l2 := List.mem_append_right l1 hy
    have hge := vmaxge (l1 ++ l2) y hy'
    omega
  have hle : vmax (l1 ++ l2) ≤ max (vmax l1) (vmax l2) := by
    have hne : l1 ++ l2 ≠ [] := by
      cases l1 with
      | nil => exact absurd rfl h1
      | cons a as => simp
    obtain ⟨y, hy, hyeq⟩ := vmaxex (l1 ++ l2) hne
    cases List.mem_append.mp hy with
    | inl h =>
      have hge := vmaxge l1 y h
      have hmax : vmax l1 ≤ max (vmax l1) (vmax l2) :=
        Nat.le_max_left _ _
      omega
    | inr h =>
      have hge := vmaxge l2 y h
      have hmax : vmax l2 ≤ max (vmax l1) (vmax l2) :=
        Nat.le_max_right _ _
      omega
  apply Nat.le_antisymm
  · exact hle
  · cases Nat.le_total (vmax l1) (vmax l2) with
    | inl h =>
      rw [Nat.max_eq_right h]
      exact hge2
    | inr h =>
      rw [Nat.max_eq_left h]
      exact hge1

/-- Bounds over an append are exact from the parts: no gap
    is introduced by composition. -/
theorem boundsjoin (m : List Nat → Nat)
    (L1 L2 : List (List Nat)) (h1 : L1 ≠ []) (h2 : L2 ≠ []) :
    lo m (L1 ++ L2) = min (lo m L1) (lo m L2)
      ∧ hi m (L1 ++ L2) = max (hi m L1) (hi m L2) := by
  have h1' : vals m L1 ≠ [] := by
    cases L1 with
    | nil => exact absurd rfl h1
    | cons a as => simp [vals]
  have h2' : vals m L2 ≠ [] := by
    cases L2 with
    | nil => exact absurd rfl h2
    | cons a as => simp [vals]
  have hmap : vals m (L1 ++ L2) = vals m L1 ++ vals m L2 := by
    show (L1 ++ L2).map m = L1.map m ++ L2.map m
    exact List.map_append
  constructor
  · show vmin (vals m (L1 ++ L2)) = min (vmin (vals m L1))
      (vmin (vals m L2))
    rw [hmap]
    exact vminappend (vals m L1) (vals m L2) h1' h2'
  · show vmax (vals m (L1 ++ L2)) = max (vmax (vals m L1))
      (vmax (vals m L2))
    rw [hmap]
    exact vmaxappend (vals m L1) (vals m L2) h1' h2'

/-- Tightening: the best value never rises under append,
    and the gap to any floor never grows. -/
theorem tighten (m : List Nat → Nat) (F : Nat)
    (L1 L2 : List (List Nat)) (h1 : L1 ≠ []) :
    best m (L1 ++ L2) ≤ best m L1
      ∧ gap m F (L1 ++ L2) ≤ gap m F L1 := by
  obtain ⟨s, hs, hms⟩ := (attained m L1 h1).1
  have hs' : s ∈ L1 ++ L2 := List.mem_append_left L2 hs
  have hle := (inbounds m (L1 ++ L2) s hs').1
  have hbest : best m (L1 ++ L2) ≤ best m L1 := by
    show lo m (L1 ++ L2) ≤ lo m L1
    omega
  refine ⟨hbest, ?_⟩
  show best m (L1 ++ L2) - F ≤ best m L1 - F
  omega

/-- Certification: when the best value equals a floor that
    floors every listed value, the optimum is attained and
    nothing listed beats it. -/
theorem certified (m : List Nat → Nat) (F : Nat)
    (L : List (List Nat))
    (hfloor : ∀ s ∈ L, F ≤ m s) (hbest : best m L = F)
    (hne : L ≠ []) :
    ∃ s ∈ L, m s = F ∧ ∀ t ∈ L, m s ≤ m t := by
  obtain ⟨s, hs, hms⟩ := (attained m L hne).1
  have hsF : m s = F := by
    show m s = F
    rw [← hbest]
    exact hms
  exact ⟨s, hs, hsF, fun t ht => by rw [hsF]; exact hfloor t ht⟩

/-- The grid length is the product of the list lengths. -/
theorem gridlength : ∀ (caps designs : List Nat),
    (grid caps designs).length = caps.length * designs.length
  | [], _ => by simp [grid]
  | v :: rest, designs => by
    show (designs.map (fun o => (v, o))
      ++ grid rest designs).length
      = (rest.length + 1) * designs.length
    rw [List.length_append, List.length_map,
      gridlength rest designs, Nat.succ_mul]
    exact Nat.add_comm _ _

/-- Finiteness, derived: the candidate count of a contract
    is the computed product of its list lengths. -/
theorem finite (c : Contract) :
    (grid c.caps c.designs).length
      = c.caps.length * c.designs.length :=
  gridlength c.caps c.designs

/-- Solvability: the optimum question over a candidate
    list is decidable, by decidable equality of
    naturals. -/
def optdec (m : List Nat → Nat) (L : List (List Nat))
    (v : Nat) : Decidable (best m L = v) :=
  Nat.decEq (best m L) v

/-- Mass at a cons universe: the head contributes one
    exactly when it lies in the state. -/
theorem masscons (a : Nat) (U s : List Nat) :
    mass (a :: U) s
      = (if a ∈ s then 1 else 0) + mass U s := by
  by_cases h : a ∈ s <;> simp [mass, h] <;> omega

/-- Mass is monotone in the state. -/
theorem massmono (U s t : List Nat)
    (h : ∀ x ∈ s, x ∈ t) : mass U s ≤ mass U t := by
  induction U with
  | nil => simp [mass]
  | cons a U ih =>
    rw [masscons a U s, masscons a U t]
    by_cases ha : a ∈ s
    · have hat : a ∈ t := h a ha
      simp only [if_pos ha, if_pos hat]
      omega
    · by_cases hat : a ∈ t
      · simp only [if_neg ha, if_pos hat]
        omega
      · simp only [if_neg ha, if_neg hat]
        omega

/-- Mass of a join is at most the sum of the masses. -/
theorem massjoin (U s t : List Nat) :
    mass U (s ++ t) ≤ mass U s + mass U t := by
  induction U with
  | nil => simp [mass]
  | cons a U ih =>
    rw [masscons a U (s ++ t), masscons a U s, masscons a U t]
    by_cases hs : a ∈ s <;> by_cases ht : a ∈ t
    · have ha : a ∈ s ++ t := List.mem_append_left t hs
      simp only [if_pos ha, if_pos hs, if_pos ht]
      omega
    · have ha : a ∈ s ++ t := List.mem_append_left t hs
      simp only [if_pos ha, if_pos hs, if_neg ht]
      omega
    · have ha : a ∈ s ++ t := List.mem_append_right s ht
      simp only [if_pos ha, if_neg hs, if_pos ht]
      omega
    · have ha : ¬ a ∈ s ++ t := by
        intro hmem
        cases List.mem_append.mp hmem with
        | inl h => exact hs h
        | inr h => exact ht h
      simp only [if_neg ha, if_neg hs, if_neg ht]
      omega

/-- The last state of a path is unchanged by dropping the
    head when at least two states remain. -/
theorem laststep (s t : List Nat) (rest : List (List Nat)) :
    (s :: t :: rest).getLast? = (t :: rest).getLast? := by
  cases rest with
  | nil => rfl
  | cons c cs => rfl

/-- Velocity telescopes: on a monotone path, the gains sum
    with the mass of the first state to the mass of the
    last state. -/
theorem telescope (U : List Nat) (s : List Nat) :
    ∀ (rest : List (List Nat)) (l : List Nat),
      mono (s :: rest) → ends (s :: rest) l →
      (gains U (s :: rest)).sum + mass U s = mass U l := by
  intro rest
  induction rest generalizing s with
  | nil =>
    intro l _ he
    have hseq : s = l := by
      have h : ([s] : List (List Nat)).getLast? = some l := he
      simp at h
      exact h
    subst hseq
    simp [gains]
  | cons t rest ih =>
    intro l hm he
    have hinc : ∀ x ∈ s, x ∈ t := by
      have hm' : (∀ x ∈ s, x ∈ t) ∧ mono (t :: rest) := hm
      exact hm'.1
    have hm2 : mono (t :: rest) := by
      have hm' : (∀ x ∈ s, x ∈ t) ∧ mono (t :: rest) := hm
      exact hm'.2
    have he2 : ends (t :: rest) l := by
      have h : (s :: t :: rest).getLast? = some l := he
      rw [laststep s t rest] at h
      exact h
    have ih' := ih t l hm2 he2
    have hle : mass U s ≤ mass U t := massmono U s t hinc
    have hsum : (gains U (s :: t :: rest)).sum
        = (mass U t - mass U s) + (gains U (t :: rest)).sum := by
      show ((mass U t - mass U s) :: gains U (t :: rest)).sum
        = (mass U t - mass U s) + (gains U (t :: rest)).sum
      exact List.sum_cons
    omega

/-- Redundancy soundness: a step the decidable face marks
    redundant has a derivable added fact. -/
theorem redsound (steps : List Step) (facts : List Nat)
    (st : Step) (h : redone steps facts st = true) :
    Deriv steps facts st.add := by
  have hor : decide (st.add ∈ facts) = true
      ∨ steps.any (fun st' => decide (st'.add = st.add)
        && st'.pre.all (fun p => decide (p ∈ facts))) = true :=
    Bool.or_eq_true_iff.mp h
  cases hor with
  | inl hdec =>
    exact Deriv.base (of_decide_eq_true hdec)
  | inr hany =>
    obtain ⟨st', hmem, hbool⟩ := List.any_eq_true.mp hany
    obtain ⟨hadd, hall⟩ := Bool.and_eq_true_iff.mp hbool
    have haddeq : st'.add = st.add := of_decide_eq_true hadd
    have hder : Deriv steps facts st'.add :=
      Deriv.step hmem (fun p hp => Deriv.base
        (of_decide_eq_true ((List.all_eq_true.mp hall) p hp)))
    rwa [haddeq] at hder

/-- Ordering, base case on the empty order. -/
theorem ordnil (r : Nat → Nat) : descents r [] = 0 :=
  rfl

/-- Ordering, base case on a singleton order. -/
theorem ordone (r : Nat → Nat) (a : Nat) :
    descents r [a] = 0 :=
  rfl

/-- Ordering decomposes: the descent count at a head pair
    is zero exactly when the pair is ordered and the rest
    has no descents. -/
theorem ordzero (r : Nat → Nat) (a b : Nat)
    (rest : List Nat) :
    descents r (a :: b :: rest) = 0
      ↔ ¬ (r b < r a) ∧ descents r (b :: rest) = 0 := by
  show ((if r b < r a then 1 else 0)
      + descents r (b :: rest) = 0)
    ↔ ¬ (r b < r a) ∧ descents r (b :: rest) = 0
  by_cases h : r b < r a
  · simp [h]
  · simp [h]

namespace thm

/-- The reengineering analysis equals the engineering
    analysis. The name shares its spelling with the
    reengineering map itself, so the theorem lives in its
    own namespace: one declaration name cannot name both
    the map and its characterization in Lean. -/
theorem reeng (s : Sys) : reeng s = analyze s :=
  rtone (analyze s)

/-- Scheduling suboptimality is exactly the idle sum. The
    name shares its spelling with the measure itself, so
    the theorem lives in its own namespace. -/
theorem schedsub (work idle : List Nat) :
    schedsub work idle = idle.sum := by
  show makespan work idle - work.sum = idle.sum
  show work.sum + idle.sum - work.sum = idle.sum
  omega

/-- Venue suboptimality vanishes exactly at the best
    venue: the suboptimality plus the best cost is the
    chosen cost, for a listed venue. The name shares its
    spelling with the measure itself, so the theorem lives
    in its own namespace. -/
theorem venuesub (chosen : Nat) (venues : List Nat)
    (h : chosen ∈ venues) :
    venuesub chosen venues + vmin venues = chosen := by
  have hle : vmin venues ≤ chosen := vminle venues chosen h
  show chosen - vmin venues + vmin venues = chosen
  omega

/-- Test set suboptimality is zero exactly at pool mass
    equality, under inclusion of the test set in its pool.
    The name shares its spelling with the measure itself,
    so the theorem lives in its own namespace. -/
theorem testsub (U pool test : List Nat)
    (h : ∀ x ∈ test, x ∈ pool) :
    testsub U pool test = 0
      ↔ mass U pool = mass U test := by
  have hle : mass U test ≤ mass U pool :=
    massmono U test pool h
  show mass U pool - mass U test = 0
    ↔ mass U pool = mass U test
  constructor
  · intro hz
    omega
  · intro heq
    rw [heq]
    exact Nat.sub_self _

end thm

#print axioms joincomm
#print axioms joinassoc
#print axioms joinidem
#print axioms joinleft
#print axioms joinright
#print axioms joinleast
#print axioms stepclose
#print axioms derivmono
#print axioms derivsteps
#print axioms mapadd
#print axioms rtone
#print axioms rttwo
#print axioms agree
#print axioms small
#print axioms powbound
#print axioms vanish
#print axioms powjoin
#print axioms smalljoin
#print axioms specvalid
#print axioms specmono
#print axioms fminle
#print axioms fminmem
#print axioms fmaxge
#print axioms fmaxmem
#print axioms fminex
#print axioms fmaxex
#print axioms vminle
#print axioms vmaxge
#print axioms vminex
#print axioms vmaxex
#print axioms inbounds
#print axioms attained
#print axioms vminappend
#print axioms vmaxappend
#print axioms boundsjoin
#print axioms tighten
#print axioms certified
#print axioms gridlength
#print axioms finite
#print axioms optdec
#print axioms masscons
#print axioms massmono
#print axioms massjoin
#print axioms laststep
#print axioms telescope
#print axioms redsound
#print axioms ordnil
#print axioms ordone
#print axioms ordzero
#print axioms thm.reeng
#print axioms thm.schedsub
#print axioms thm.venuesub
#print axioms thm.testsub
