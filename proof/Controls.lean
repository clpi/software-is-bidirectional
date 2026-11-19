/-
  Standing controls for the bidirectional model.

  Each control is a proved fact over concrete values: a
  load-bearing condition of the model is removed or varied,
  and the failure is exhibited exactly. The controls stand
  in the tree permanently; a change that breaks one has
  broken the condition it guards.
-/

import Core

/-- Control one, smallness can fail: a contract whose
    description exceeds its bound is not small. Smallness
    is per qualification, never automatic. -/
theorem ctrlone :
    ¬ Small 3 { caps := [0, 1, 2, 3, 4, 5, 6, 7], designs := [] } := by
  show ¬ (desc { caps := [0, 1, 2, 3, 4, 5, 6, 7], designs := [] } ≤ 3)
  decide

/-- Control two, routes disagree on a truncated recording:
    the chunked route over chunks that do not concatenate
    to the record derives a different contract than the
    direct route. Completeness of the recording is load
    bearing for the agreement theorem. -/
theorem ctrltwo :
    analyzechunks { facts := [], steps := [], record := [1, 2, 3] } [[1], [2]]
      ≠ analyze { facts := [], steps := [], record := [1, 2, 3] } := by
  decide

/-- Control three, no tightening inside the bounds: joining
    a candidate whose measure lies strictly inside the
    current bounds moves neither bound, and the best value
    does not tighten. Tightening happens only at the
    bounds, never inside them. -/
theorem ctrlthree :
    lo (mass [0, 1, 2]) ([[0], [0, 1]] ++ [[1]])
        = lo (mass [0, 1, 2]) [[0], [0, 1]]
      ∧ hi (mass [0, 1, 2]) ([[0], [0, 1]] ++ [[1]])
        = hi (mass [0, 1, 2]) [[0], [0, 1]]
      ∧ best (mass [0, 1, 2]) ([[0], [0, 1]] ++ [[1]])
        = best (mass [0, 1, 2]) [[0], [0, 1]] := by
  decide

/-- Control four, the content bound needs injectivity:
    projecting facts through a content map that collapses
    the universe inflates the count, since every universe
    entry whose image lands in the projected state is
    counted. With the constant zero map, universe [0, 1],
    and state [0], the content mass is 2 against a mass
    of 1. The bound content mass at most mass is therefore
    false as stated; it stands proposed only in the form
    that requires the content map injective on the
    universe. -/
theorem ctrlfour :
    ¬ (content (fun _ => 0) [0, 1] [0] ≤ mass [0, 1] [0]) := by
  decide

#print axioms ctrlone
#print axioms ctrltwo
#print axioms ctrlthree
#print axioms ctrlfour
