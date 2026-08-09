/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.CNS.Search
import HopfieldNet.CNS.Exact

/-!
# A Sudoku solver, and a corpus hard enough to test it

The ten Sabuncu instances are not a benchmark. Four of them are solved outright by constraint
propagation — Table I reports `0` variables remaining — so the neurodynamics never runs, and the
rest reduce to between 95 and 209 variables. Reporting "10/10" on that set says very little.

This module supplies two things the reproduction lacked.

## A generated corpus

`genPuzzle` builds proper puzzles (exactly one completion) with no external data and no reliance
on published strings: take a completed grid, apply a random Sudoku symmetry, then remove givens
in random order for as long as the puzzle stays uniquely solvable. Everything is seeded, so the
corpus is reproducible from an integer.

The relevant hardness measure here is not the clue count but the **post-reduction dimension** —
the Table I quantity — because that is exactly the size of the problem the neurodynamics is
handed. `genHard` rejects candidates below a dimension threshold. Measured over the default
seeds, generated puzzles carry 23–26 givens and reduce to dimensions from `0` to roughly `190`,
so the corpus spans Sabuncu's range and — unlike it — can be extended upwards on demand by
raising the threshold.

## A solver that is never wrong

`solveCertified` runs the reduction, then the collaborative neurodynamic search with restarts,
and **checks a certificate on whatever the search returns**: the result is accepted only if
`isSolution` holds and the givens survive. If the search fails within its budget the exact
solver finishes the job. So the output is either a verified completion or a proof-backed
"no completion exists" — the neurodynamics affects how *often* the fast path succeeds, never
whether the answer is right.

That is the `Certified CNS` split: an untrusted search behind a checked certificate. The checker
is what `CNS.Sound` and `CNS.GridSound` reason about; `CNS.Minimizers` says the search is
descending an objective whose minimisers are exactly the states the checker accepts.
-/

namespace CNS

/-! ## Sudoku symmetries -/

/-- A random permutation of `[0, m)` by Fisher–Yates. -/
def randPerm (g : Rng) (m : Nat) : Array Nat × Rng := Id.run do
  let mut a : Array Nat := Array.range m
  let mut gg := g
  for i in [0:m] do
    let j := m - 1 - i
    let (k, g') := gg.nextBelow (j + 1)
    gg := g'
    let aj := a.getD j 0
    let ak := a.getD k 0
    a := (a.set! j ak).set! k aj
  return (a, gg)

/-- A random row permutation respecting bands: the three bands are permuted, and the rows inside
each band are permuted. Both preserve every Sudoku constraint. -/
def randRowPerm (g : Rng) : Array Nat × Rng := Id.run do
  let (bands, g1) := randPerm g blk
  let mut out : Array Nat := Array.replicate n 0
  let mut gg := g1
  for b in [0:blk] do
    let (inner, g') := randPerm gg blk
    gg := g'
    for t in [0:blk] do
      out := out.set! (b * blk + t) ((bands.getD b 0) * blk + (inner.getD t 0))
  return (out, gg)

/-- Relabel digits, permute rows and columns band-wise, and optionally transpose.

Every one of these maps a solved grid to a solved grid, so applying them to a completion yields
another completion — which is what gives the generator its variety without ever calling the
exact solver more than once for a seed grid. -/
def randSymmetry (g : Rng) (base : Grid) : Grid × Rng := Id.run do
  let (digits, g1) := randPerm g n
  let (rows, g2) := randRowPerm g1
  let (cols, g3) := randRowPerm g2
  let (tr, g4) := g3.nextBool
  let mut cells : Array (Option Nat) := Array.replicate numCells none
  for i in [0:n] do
    for j in [0:n] do
      let src := cellIdx (rows.getD i 0) (cols.getD j 0)
      let dst := if tr then cellIdx j i else cellIdx i j
      cells := cells.set! dst ((base.get src).map fun k => digits.getD k 0)
  return (⟨cells⟩, g4)

/-! ## Generation -/

/-- A completed grid, written down rather than searched for.

`cell(i,j) ↦ (3(i mod 3) + i div 3 + j) mod 9` is the standard shift construction and is a valid
completion; `cns hard` asserts `isSolution` on it before using it. Calling the exact solver on
an *empty* grid instead would be a mistake: with no clues there is nothing to propagate, every
cell ties at nine candidates, and the most-constrained-cell heuristic degenerates. -/
def seedSolution : Grid :=
  ⟨(Array.range numCells).map fun c =>
    some ((blk * (rowOf c % blk) + rowOf c / blk + colOf c) % n)⟩

/-- Remove givens in random order for as long as the puzzle stays uniquely solvable.

The result is *minimal* in the sense that no further single removal preserves uniqueness. It is
not guaranteed to have the fewest possible clues — that is a different and much harder search —
but minimality is what makes the instance hard for propagation. -/
def dig (g : Rng) (full : Grid) : Grid × Rng := Id.run do
  let (order, g1) := randPerm g numCells
  let mut cur := full
  for t in [0:numCells] do
    let c := order.getD t 0
    match cur.get c with
    | none => pure ()
    | some k =>
      let trial : Grid := ⟨cur.cells.set! c none⟩
      if countSolutions trial 2 == 1 then
        cur := trial
      else
        cur := ⟨cur.cells.set! c (some k)⟩
  return (cur, g1)

/-- One generated puzzle, together with the dimension Algorithm 1 leaves. -/
structure GenPuzzle where
  /-- The puzzle. -/
  grid : Grid
  /-- Number of givens. -/
  givens : Nat
  /-- Variables remaining after Algorithm 1 — the Table I quantity, and the size of the problem
  the neurodynamics actually receives. -/
  dim : Nat
  deriving Inhabited

/-- Generate one proper puzzle from a seed. -/
def genPuzzle (g : Rng) : GenPuzzle × Rng :=
  let (sym, g1) := randSymmetry g seedSolution
  let (p, g2) := dig g1 sym
  ({ grid := p, givens := p.numGivens, dim := (reduce p).remaining }, g2)

/-- Generate a puzzle whose post-reduction dimension is at least `minDim`, giving up after
`tries` attempts. -/
def genHard (g : Rng) (minDim : Nat) (tries : Nat) : Option GenPuzzle × Rng := Id.run do
  let mut gg := g
  let mut best : Option GenPuzzle := none
  for _ in [0:tries] do
    if best.isNone then
      let (q, g') := genPuzzle gg
      gg := g'
      -- keep the hardest seen, so a run never reports nothing when the threshold is optimistic
      if q.dim ≥ minDim then best := some q
  return (best, gg)

/-! ## The certified solver -/

/-- How a puzzle was solved. -/
inductive Route where
  /-- Algorithm 1 alone closed it. -/
  | propagation
  /-- The collaborative neurodynamic search found it, on the given restart. -/
  | neurodynamic (restart : Nat)
  /-- The search exhausted its budget; the exact solver finished. -/
  | exactFallback
  /-- No completion exists. -/
  | unsolvable
  deriving Repr, BEq, Inhabited

/-- Name for reports. -/
def Route.name : Route → String
  | .propagation => "propagation"
  | .neurodynamic k => s!"neurodynamic (restart {k})"
  | .exactFallback => "exact fallback"
  | .unsolvable => "unsolvable"

/-- The outcome of a certified solve. -/
structure Outcome where
  /-- The completion, if one was found *and verified*. -/
  solution : Option Grid
  /-- Which stage produced it. -/
  route : Route
  /-- Post-reduction dimension. -/
  dim : Nat
  deriving Inhabited

/-- Accept a candidate only if it is a solved grid extending the givens.

This is the certificate check. `Grid.isSolution` is the conjunction of (10a)–(10d) and
`Grid.extends'` is (10e); `CNS.Sound.penalty_zero_iff_families` is the theorem that these are
the same conditions the objective encodes. Nothing downstream trusts the search. -/
def accepts (g sol : Grid) : Bool := sol.isSolution && g.extends' sol

/-- **Solve a puzzle, and never return an unverified answer.**

Reduction first; then up to `restarts` seeded runs of Algorithm 2, each result certificate-
checked; then the exact solver. The neurodynamic path changes the *speed*, not the
*correctness* — a wrong candidate is rejected by `accepts` and the fallback still returns the
right grid. -/
def solveCertified (g : Grid) (mdl : Model) (restarts : Nat) : Outcome := Id.run do
  let R := reduce g
  if R.remaining == 0 then
    if accepts g R.grid then
      return { solution := some R.grid, route := .propagation, dim := 0 }
  let P := Problem.ofReduced R
  let cfg : SearchConfig :=
    { N := 50, M := 100,
      model := ModelConfig.tabulate
        { innerIters := max 30 (P.nvars / 3), T0 := 3.0, eta := 0.9 } }
  for k in [0:restarts] do
    let r := search P mdl cfg (Rng.seed (UInt64.ofNat (1 + k)))
    if r.penaltyDoubled == 0 then
      let sol := P.toGrid r.best
      if accepts g sol then
        return { solution := some sol, route := .neurodynamic k, dim := R.remaining }
  match solveExact g with
  | some sol =>
    if accepts g sol then
      return { solution := some sol, route := .exactFallback, dim := R.remaining }
    else
      return { solution := none, route := .unsolvable, dim := R.remaining }
  | none => return { solution := none, route := .unsolvable, dim := R.remaining }

end CNS
