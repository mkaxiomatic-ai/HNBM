/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.CNS.Reduce

/-!
# An exact solver, for counting and for comparison

Three things the neurodynamic search cannot do for us:

* **Count solutions.** Table II's "# of solutions" column is really `2^dim`, the size of the
  reduced search space, not a solution count (see `CNS.Instances`). The actual counts matter
  anyway: Sabuncu3 is not a proper Sudoku — it has 27 completions — and that is worth
  establishing rather than asserting.
* **Validate a puzzle.** Before running Algorithm 2 on a user-supplied grid it is worth knowing
  whether it has no solution, one, or many.
* **Give an honest baseline.** A metaheuristic's runtime means little without something to
  compare against. Constraint propagation plus backtracking solves these instances in
  milliseconds; the collaborative neurodynamic search takes seconds. That gap is a property of
  the method, not of this implementation, and reporting it is more useful than avoiding it.

The search is ordinary: propagate with Algorithm 1's own deductions (`reduce`), then branch on
the most constrained open cell. Recursion is bounded by an explicit node budget rather than a
termination proof, so the function is total.
-/

namespace CNS

/-- Digits still available at cell `c`, i.e. those no peer already uses. -/
def candidatesAt (g : Grid) (c : Nat) : Array Nat :=
  let used := usedByPeers g c
  (Array.range n).filter fun k => !(used.getD k false)

/-- The open cell with the fewest candidates, together with them. `none` when the grid is
complete. -/
def mostConstrained (g : Grid) : Option (Nat × Array Nat) := Id.run do
  let mut best : Option (Nat × Array Nat) := none
  for c in [0:numCells] do
    if (g.get c).isNone then
      let cs := candidatesAt g c
      match best with
      | none => best := some (c, cs)
      | some (_, bs) => if cs.size < bs.size then best := some (c, cs)
  return best

/-- Count completions, stopping once `cap` have been found, and return the first one.

`fuel` bounds the number of search nodes. Returns `(count, firstSolution)`; a count of `cap`
means "at least `cap`". -/
def countAux : Nat → Grid → Nat → Nat × Option Grid
  | 0, _, _ => (0, none)
  | fuel + 1, g, cap =>
    if cap == 0 then (0, none) else
    let R := reduce g
    let g' := R.grid
    match mostConstrained g' with
    | none => if g'.isSolution then (1, some g') else (0, none)
    | some (c, cands) =>
      if cands.isEmpty then (0, none) else
        -- branch over the candidates of the most constrained cell
        cands.foldl (fun (acc : Nat × Option Grid) k =>
          if acc.1 ≥ cap then acc else
            let (m, sol) := countAux fuel (g'.assign c k) (cap - acc.1)
            (acc.1 + m, acc.2.orElse (fun _ => sol))) (0, none)

/-- Number of completions of `g`, capped at `cap`. -/
def countSolutions (g : Grid) (cap : Nat := 100) : Nat := (countAux 4096 g cap).1

/-- A completion of `g`, if one exists. -/
def solveExact (g : Grid) : Option Grid := (countAux 4096 g 1).2

/-- Classification of a puzzle, for validating user input. -/
inductive Status where
  /-- No completion exists. -/
  | unsolvable
  /-- Exactly one completion — a proper Sudoku. -/
  | unique
  /-- More than one completion. -/
  | multiple (atLeast : Nat)
  deriving Repr, BEq

/-- Render for reports. -/
def Status.describe : Status → String
  | .unsolvable => "no solution"
  | .unique => "unique solution"
  | .multiple k => s!"{k} solutions (not a proper Sudoku)"

/-- Classify a puzzle by counting its completions. -/
def classify (g : Grid) (cap : Nat := 100) : Status :=
  match countSolutions g cap with
  | 0 => .unsolvable
  | 1 => .unique
  | k => .multiple k

end CNS
