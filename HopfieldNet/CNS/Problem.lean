/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.CNS.Encoding

/-!
# The reduced QUBO instance

Algorithm 1 fixes some of the `n³` variables; §IV of the paper then deletes their columns from
`A_a … A_d` (steps 39-49) and redefines the penalties over the surviving vector `x̂`.

Splitting `x` into its free part `x̂` and its fixed part `s`,

  `A x − e = Â x̂ − b̂`,   where   `b̂ = e − A_F s`,

so the reduced objective is `p(x̂) = ½‖Â x̂ − b̂‖²`. This is precisely the paper's
`p_a(x̂) = ½‖Â_a x̂ − b_a‖²` etc. with `b· = e_{n²} − A· s` (steps 39-42).

Deleting *columns* leaves the row structure intact, so `diag(ÂᵀÂ)` is still `4` and the same
diagonal-folding argument gives

  `W = −(ÂᵀÂ − 4I)`,   `θ̂_u = 2 − Σ_{r ∋ u} b̂_r`,   `p(x̂) = −½x̂ᵀWx̂ + θ̂ᵀx̂ + ½‖b̂‖²`.

Note `θ̂` is no longer constant: reduction changes `b̂` row by row.

## Cost

Every variable lies in exactly four rows, so the net input is computed in `O(nvars)` rather than
`O(nvars²)`. Writing `ρ_r = Σ_{v ∈ r} x̂_v` for the row sums,

  `Σ_{r ∋ u} ρ_r = Σ_v (ÂᵀÂ)_{uv} x̂_v = 4 x̂_u + Σ_{v ≠ u} (ÂᵀÂ)_{uv} x̂_v`

hence `(W x̂)_u = 4 x̂_u − Σ_{r ∋ u} ρ_r`. That is the identity `netVec` implements, and it is
what makes the search tractable in Lean.
-/

namespace CNS

/-- A reduced QUBO instance, ready for the neurodynamics of (3) and (6). -/
structure Problem where
  /-- Number of surviving variables — the Table I quantity. -/
  nvars : Nat
  /-- Reduced index → original `x_{ijk}` index. -/
  varOf : Array Nat
  /-- Reduced index → the (at most four) penalty rows containing it. -/
  rowsOf : Array (Array Nat)
  /-- Penalty row → the surviving variables occurring in it. -/
  varsOf : Array (Array Nat)
  /-- `b̂ = e − A_F s`, one entry per penalty row. -/
  bhat : Array Int
  /-- `θ̂_u = 2 − Σ_{r ∋ u} b̂_r`. -/
  theta : Array Int
  /-- `‖b̂‖²`, i.e. twice the additive constant `½‖b̂‖²`. -/
  constDoubled : Int
  /-- The assignment Algorithm 1 already determined. -/
  base : Grid
  deriving Inhabited

namespace Problem

/-- Which original variables Algorithm 1 pinned to `1`; the paper's `s` restricted to its
support. -/
def pinnedOnes (R : Reduced) : Array Bool :=
  (Array.range numVars).map fun v => R.isFixed.getD v false && R.fixedVal.getD v false

/-- The surviving variables, in increasing order of their original index.

Built through `List.filter` rather than `Array.filter` on purpose. `Array.filter` carries an
optional `stop := as.size` argument, so unifying against it forces `(Array.range numVars).size`
to be evaluated, and every proof that mentions this definition then times out in `whnf`.
`List.filter` takes no such argument. -/
def survivors (R : Reduced) : Array Nat :=
  ((List.range numVars).filter fun v => !(R.isFixed.getD v false)).toArray

/-- `b̂ = e − A_F s`: one less than `1` for each pinned-to-one variable occurring in the row.

The four rows of a variable are distinct (`Problem.rowsOfVar_nodup`), so no row loses two units
for the same variable and the count is exactly the contribution the deleted columns carried. -/
def bhatRow (pinned : Array Bool) (r : Nat) : Int :=
  1 - ((List.range numVars).countP fun v => pinned.getD v false && (rowsOfVar v).contains r : Int)

/-- `b̂`, one entry per constraint row. -/
def bhatOf (R : Reduced) : Array Int := (Array.range numRows).map (bhatRow (pinnedOnes R))

/-- Deleting columns leaves the rows alone, so a survivor keeps its four original rows. -/
def rowsOfSurv (R : Reduced) : Array (Array Nat) := (survivors R).map rowsOfVar

/-- The surviving variables of one constraint row, in increasing reduced index. -/
def rowMembers (varOf : Array Nat) (r : Nat) : Array Nat :=
  ((List.range varOf.size).filter fun u => (rowsOfVar (varOf.getD u 0)).contains r).toArray

/-- Each constraint row restricted to its surviving variables. -/
def varsOfSurv (R : Reduced) : Array (Array Nat) :=
  (Array.range numRows).map (rowMembers (survivors R))

/-- `θ̂_u = 2 − Σ_{r ∋ u} b̂_r` for one variable's row set. -/
def thetaRow (bhat : Array Int) (rs : Array Nat) : Int :=
  2 - rs.foldl (fun acc r => acc + bhat.getD r 0) 0

/-- `θ̂`, no longer constant once `b̂` varies row by row. -/
def thetaOf (R : Reduced) : Array Int := (rowsOfSurv R).map (thetaRow (bhatOf R))

/-- Build the reduced instance from the output of Algorithm 1.

Every field is a `map` or `filter` over an index range rather than a scatter loop accumulating
with `set!`, and each is a named top-level function rather than a `let` in this body. Both
choices are deliberate and neither costs anything here — `ofReduced` runs once per puzzle, not
once per sweep. Together they make `Problem.Valid` provable pointwise: a field projection is
`rfl` with nothing to evaluate, and a `map` is characterised by `Array.getElem_map`, whereas a
`set!` loop can only be characterised by an induction over its trip count. This is the same
rewrite `buildFlags` received for `CNS.ReduceSound`. -/
def ofReduced (R : Reduced) : Problem where
  nvars := (survivors R).size
  varOf := survivors R
  rowsOf := rowsOfSurv R
  varsOf := varsOfSurv R
  bhat := bhatOf R
  theta := thetaOf R
  constDoubled := (bhatOf R).foldl (fun acc bi => acc + bi * bi) 0
  base := R.grid

/-- Run Algorithm 1 and build the reduced instance. -/
def ofGrid (g : Grid) : Problem := ofReduced (reduce g)

/-- Row sums `ρ_r = Σ_{v ∈ r} x̂_v`.

The `if` sits inside the assignment and the inner loop is a written-out `Array.foldl`. Both are
cosmetic at run time — the compiled code is the same scatter — but they matter for proofs: the
`@[simp]` lemma `List.forIn_pure_yield_eq_foldl` only matches a loop body of the shape
`fun u ρ => pure (.yield _)`, and an `if` wrapped around the `pure` blocks it. With this shape
`simp [Id.run]` turns the loop into a `List.foldl` that ordinary list induction can handle. -/
@[inline] def rowSums (P : Problem) (x : Array Bool) : Array Int := Id.run do
  let mut ρ : Array Int := Array.replicate numRows 0
  for u in [0:P.nvars] do
    ρ := if x.getD u false then
           (P.rowsOf.getD u #[]).foldl (fun ρ r => ρ.set! r ((ρ.getD r 0) + 1)) ρ
         else ρ
  return ρ

/-- `‖Â x̂ − b̂‖²`, i.e. twice the paper's `p(x̂)`. Zero exactly when `x̂` solves the puzzle. -/
def penaltyDoubled (P : Problem) (x : Array Bool) : Int :=
  let ρ := P.rowSums x
  (Array.range numRows).foldl
    (fun acc r => let d := (ρ.getD r 0) - (P.bhat.getD r 0); acc + d * d) 0

/-- The net input `W x̂ − θ̂` driving (1), (3) and (6).

Uses `(W x̂)_u = 4 x̂_u − Σ_{r ∋ u} ρ_r`, so the whole vector costs `O(nvars)`. -/
def netVec (P : Problem) (x : Array Bool) : Array Int :=
  let ρ := P.rowSums x
  (Array.range P.nvars).map fun u =>
    let s := (P.rowsOf.getD u #[]).foldl (fun acc r => acc + ρ.getD r 0) 0
    ((if x.getD u false then (4 : Int) else 0) - s) - P.theta.getD u 0

/-- Write a reduced assignment back into a full grid, on top of the Algorithm 1 base. -/
def toGrid (P : Problem) (x : Array Bool) : Grid := Id.run do
  let mut cells := P.base.cells
  for u in [0:P.nvars] do
    if x.getD u false then
      let v := P.varOf.getD u 0
      cells := cells.set! (v / n) (some (v % n))
  return ⟨cells⟩

/-- The surviving variables grouped by the cell they belong to, one group per still-open cell.

Every cell constraint (11a) forces exactly one variable per group to be `1`, so these groups are
the natural coordinates of the feasible set. -/
def openCellGroups (P : Problem) : Array (Array Nat) := Id.run do
  let mut byCell : Array (Array Nat) := Array.replicate numCells #[]
  for u in [0:P.nvars] do
    let c := (P.varOf.getD u 0) / n
    byCell := byCell.set! c ((byCell.getD c #[]).push u)
  return byCell.filter (fun grp => grp.size != 0)

/-- The reduced index of an original variable, when it survived the reduction.

A linear scan, which is fine: `embed` runs in the consistency checks, never in a sweep. Written
as a lookup rather than as a scatter with `set!` for the usual reason — `Array.getElem_map` and
`List.find?` are characterised pointwise, a scatter only by induction on its trip count. -/
def redIndex (P : Problem) (v : Nat) : Option Nat :=
  (List.range P.nvars).find? fun u => P.varOf.getD u 0 == v

/-- Embed a reduced assignment back into the full `n³` vector, filling the eliminated
coordinates with the values Algorithm 1 pinned them to.

This is the map along which the reduced objective should agree with the unreduced one: writing
`s` for the pinned values and `x̂` for the free ones,

  `A (embed x̂) − e = Â x̂ − b̂`,   since `b̂ = e − A_F s`,

so `Problem.penaltyDoubled P x̂` and `CNS.penaltyDoubled (P.embed x̂)` should be equal. That is
the bridge between what the solver minimises and what `CNS.Sound` proves about. -/
def embed (P : Problem) (fixedVal : Array Bool) (x : Array Bool) : Array Bool :=
  (Array.range numVars).map fun v =>
    match P.redIndex v with
    | some u => x.getD u false
    | none   => fixedVal.getD v false


/-- Number of off-diagonal neighbours of a surviving variable (≤ 28). -/
def degree (P : Problem) (u : Nat) : Nat :=
  ((P.rowsOf.getD u #[]).foldl (fun acc r =>
    (P.varsOf.getD r #[]).foldl (fun a w =>
      if w == u || a.contains w then a else a.push w) acc) #[]).size

end Problem
end CNS
