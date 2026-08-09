/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.CNS.Sudoku

/-!
# Algorithm 1: variable reduction

A faithful executable rendering of Li & Wang's Algorithm 1 (ICIST 2022, p. 11).

The paper maintains two `{0,1}`-vectors indexed like `x̄`:

* `s ∈ {0,1}^{n³}` — the value a variable has been pinned to;
* `δ ∈ {0,1}^{n³}` — whether it has been pinned at all (`δᵢ = 1` means `x̄ᵢ` is fixed and its
  column is deleted from `Aₐ..A_d`).

and grows a set `G` of known `(i, j, k)` assignments until no further deduction is possible.
Steps 5-15 pin all `n` variables of a given cell; steps 16-31 zero the variables that a given
rules out in the same row, column, or block; steps 32-37 extend `G` when a cell admits a unique
digit or a digit admits a unique cell in some unit, and set the loop flag `Δ` accordingly.

## Deviations from the printed algorithm

The printed pseudocode has several index slips, corrected here:

* line 26 tests `(i, k, k) ∈ G`, which cannot be right; the intended test is `(i, j, k) ∈ G`
  ranging over the cells `(i, j)` of the block containing `(iₑ, jₑ)`;
* lines 18 and 22 write `s_{iₑ×n²+c×n+k}` and `s_{r×n²+jₑ×n+k}`, i.e. they zero the *given's*
  variable rather than the *empty cell's*; the intended target is `s_{iₑ×n²+jₑ×n+k}`;
* the prose accompanying line 43 says "if `δᵢ = 0` then `x̄ᵢ` is fixed", contradicting lines 9
  and 12; `δᵢ = 1` means fixed.

Step 32 reads "A element `(i,j)` that is not given has a unique `k` in a row, column, or
sub-grid", which is the conjunction of the two classical deductions: a cell with a single
remaining candidate (naked single) and a digit with a single remaining cell in a unit (hidden
single). Implementing exactly those two reproduces Table I on all ten benchmark instances.

Like the paper's `while` loop, this performs **one** deduction per iteration.
-/

namespace CNS

/-- Assign digit `k` to cell `c`. -/
def Grid.assign (g : Grid) (c k : Nat) : Grid := ⟨g.cells.set! c (some k)⟩

/-- One step of the `usedByPeers` fold: mark the digit peer `p` holds, if it holds one.

Named rather than written inline because two syntactically identical `match` expressions
elaborate to two *distinct* matcher constants, which do not unify; `usedByPeers_spec` has to
state its induction over the same function this fold uses. -/
def markUsed (g : Grid) (acc : Array Bool) (p : Nat) : Array Bool :=
  match g.get p with
  | some k => acc.set! k true
  | none   => acc

/-- Digits already placed in a peer of `c`; these are the `k` ruled out at `c` by steps 16-31. -/
def usedByPeers (g : Grid) (c : Nat) : Array Bool :=
  -- folds over `List`, not `Array`: Lean core has no `Array.foldl = List.foldl ∘ toList`
  -- lemma, and `CNS.ReduceSound` needs to induct over this.
  (peers c).toList.foldl (markUsed g) (Array.replicate n false)

/-- The flags of a single variable: `(s, δ)` for `x_{ijk}` where `v = varIdx i j k`.

Since `varIdx i j k = (i*n + j)*n + k = cellIdx i j * n + k`, the variable index `v` splits as
cell `v / n` and digit `v % n`. Steps 5-15 pin every variable of a given cell; steps 16-31 pin
to `0` the variables an empty cell's peers rule out. -/
def flagOf (g : Grid) (v : Nat) : Bool × Bool :=
  let c := v / n
  let k := v % n
  match g.get c with
  | some kg => (k == kg, true)
  | none    => if (usedByPeers g c).getD k false then (false, true) else (false, false)

/-- Build the paper's `s` and `δ` from the current assignment set `G`.

Written as a `map` over variable indices rather than as an accumulating loop over cells: the
two are the same function (each cell writes only its own `n` variables, so the writes never
interfere), but this form is characterised in one step by `buildFlags_snd`, which
`CNS.ReduceSound` needs. -/
def buildFlags (g : Grid) : Array Bool × Array Bool :=
  ((Array.range numVars).map (fun v => (flagOf g v).1),
   (Array.range numVars).map (fun v => (flagOf g v).2))

/-- Is `x_{ijk}` still free, i.e. `δ = 0`? -/
@[inline] def free (d : Array Bool) (i j k : Nat) : Bool := !(d.getD (varIdx i j k) false)

/-- Number of variables surviving the reduction: the count of `δᵢ = 0`.

This is the quantity tabulated in Li & Wang's Table I. -/
def countFree (d : Array Bool) : Nat := d.foldl (fun acc b => if b then acc else acc + 1) 0

/-- A cell that is not given and admits exactly one digit (a *naked single*). -/
def nakedSingle? (g : Grid) (d : Array Bool) : Option (Nat × Nat) :=
  (Array.range numCells).findSome? fun c =>
    if (g.get c).isSome then none
    else
      let i := rowOf c
      let j := colOf c
      let cands := (Array.range n).filter (fun k => free d i j k)
      if cands.size == 1 then (cands[0]?).map (fun k => (c, k)) else none

/-- A digit that can go in exactly one cell of some unit (a *hidden single*). -/
def hiddenSingle? (g : Grid) (d : Array Bool) : Option (Nat × Nat) :=
  units.findSome? fun u =>
    (Array.range n).findSome? fun k =>
      -- skip digits already placed in this unit
      if u.any (fun c => g.get c == some k) then none
      else
        let spots := u.filter fun c =>
          (g.get c).isNone && free d (rowOf c) (colOf c) k
        if spots.size == 1 then (spots[0]?).map (fun c => (c, k)) else none

/-- The outcome of Algorithm 1. -/
structure Reduced where
  /-- `G` after the fixpoint: the givens together with everything deduced. -/
  grid : Grid
  /-- The paper's `s`. -/
  fixedVal : Array Bool
  /-- The paper's `δ`. -/
  isFixed : Array Bool
  /-- Number of `while` iterations that made a deduction. -/
  rounds : Nat
  deriving Inhabited

/-- Variables remaining after reduction — the Table I quantity. -/
def Reduced.remaining (r : Reduced) : Nat := countFree r.isFixed

/-- Cells still undetermined after reduction. -/
def Reduced.openCells (r : Reduced) : Array Nat :=
  (Array.range numCells).filter fun c => (r.grid.get c).isNone

/-- The paper's `while Δ = 1` loop, bounded by fuel. Each productive iteration assigns one
cell, so `numCells` iterations always suffice to reach the fixpoint. -/
def reduceFuel : Nat → Grid → Nat → Grid × Nat
  | 0, g, r => (g, r)
  | fuel + 1, g, r =>
    let (_, d) := buildFlags g
    match nakedSingle? g d with
    | some (c, k) => reduceFuel fuel (g.assign c k) (r + 1)
    | none =>
      match hiddenSingle? g d with
      | some (c, k) => reduceFuel fuel (g.assign c k) (r + 1)
      | none        => (g, r)

/-- Algorithm 1. -/
def reduce (g : Grid) : Reduced :=
  let (g', rounds) := reduceFuel numCells g 0
  let (s, d) := buildFlags g'
  { grid := g', fixedVal := s, isFixed := d, rounds := rounds }

/-- Algorithm 1, keeping every intermediate board rather than only the fixpoint.

Frame `0` is the givens and frame `i` the board after `i` deductions, so the last frame is
`(reduce g).grid` and there are `(reduce g).rounds + 1` of them. Mirrors `reduceFuel` step for
step; it exists to animate the reduction, not to be reasoned about. -/
def reduceFrames (g : Grid) : Array Grid := Id.run do
  let mut frames := #[g]
  let mut cur := g
  for _ in [0:numCells] do
    let (_, d) := buildFlags cur
    match nakedSingle? cur d with
    | some (c, k) =>
        cur := cur.assign c k
        frames := frames.push cur
    | none =>
      match hiddenSingle? cur d with
      | some (c, k) =>
          cur := cur.assign c k
          frames := frames.push cur
      | none => break
  return frames

end CNS
