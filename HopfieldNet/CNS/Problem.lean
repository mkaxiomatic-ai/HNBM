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

/-- Build the reduced instance from the output of Algorithm 1. -/
def ofReduced (R : Reduced) : Problem := Id.run do
  -- surviving variables, in increasing order of their original index
  let varOf := (Array.range numVars).filter fun v => !(R.isFixed.getD v false)
  let mut idxOf : Array Nat := Array.replicate numVars 0
  let mut present : Array Bool := Array.replicate numVars false
  for u in [0:varOf.size] do
    let v := varOf.getD u 0
    idxOf := idxOf.set! v u
    present := present.set! v true
  -- b̂ = e − A_F s : subtract the contribution of variables already pinned to 1
  let mut bhat : Array Int := Array.replicate numRows 1
  for v in [0:numVars] do
    if R.isFixed.getD v false && R.fixedVal.getD v false then
      for r in rowsOfVar v do
        bhat := bhat.set! r ((bhat.getD r 0) - 1)
  -- restrict each row to its surviving variables
  let mut varsOf : Array (Array Nat) := Array.replicate numRows #[]
  for u in [0:varOf.size] do
    let v := varOf.getD u 0
    for r in rowsOfVar v do
      varsOf := varsOf.set! r ((varsOf.getD r #[]).push u)
  -- rowsOf and θ̂
  let mut rowsOf : Array (Array Nat) := Array.replicate varOf.size #[]
  let mut theta : Array Int := Array.replicate varOf.size 0
  for u in [0:varOf.size] do
    let rs := rowsOfVar (varOf.getD u 0)
    rowsOf := rowsOf.set! u rs
    theta := theta.set! u (2 - rs.foldl (fun acc r => acc + bhat.getD r 0) 0)
  let constDoubled := bhat.foldl (fun acc bi => acc + bi * bi) 0
  return { nvars := varOf.size, varOf := varOf, rowsOf := rowsOf, varsOf := varsOf,
           bhat := bhat, theta := theta, constDoubled := constDoubled, base := R.grid }

/-- Run Algorithm 1 and build the reduced instance. -/
def ofGrid (g : Grid) : Problem := ofReduced (reduce g)

/-- Row sums `ρ_r = Σ_{v ∈ r} x̂_v`. -/
@[inline] def rowSums (P : Problem) (x : Array Bool) : Array Int := Id.run do
  let mut ρ : Array Int := Array.replicate numRows 0
  for u in [0:P.nvars] do
    if x.getD u false then
      for r in P.rowsOf.getD u #[] do
        ρ := ρ.set! r ((ρ.getD r 0) + 1)
  return ρ

/-- `‖Â x̂ − b̂‖²`, i.e. twice the paper's `p(x̂)`. Zero exactly when `x̂` solves the puzzle. -/
def penaltyDoubled (P : Problem) (x : Array Bool) : Int :=
  let ρ := P.rowSums x
  (Array.range numRows).foldl
    (fun acc r => let d := (ρ.getD r 0) - (P.bhat.getD r 0); acc + d * d) 0

/-- The net input `W x̂ − θ̂` driving (1), (3) and (6).

Uses `(W x̂)_u = 4 x̂_u − Σ_{r ∋ u} ρ_r`, so the whole vector costs `O(nvars)`. -/
def netVec (P : Problem) (x : Array Bool) : Array Int := Id.run do
  let ρ := P.rowSums x
  let mut out : Array Int := Array.replicate P.nvars 0
  for u in [0:P.nvars] do
    let s := (P.rowsOf.getD u #[]).foldl (fun acc r => acc + ρ.getD r 0) 0
    let wx := (if x.getD u false then (4 : Int) else 0) - s
    out := out.set! u (wx - P.theta.getD u 0)
  return out

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

/-- Embed a reduced assignment back into the full `n³` vector, filling the eliminated
coordinates with the values Algorithm 1 pinned them to.

This is the map along which the reduced objective should agree with the unreduced one: writing
`s` for the pinned values and `x̂` for the free ones,

  `A (embed x̂) − e = Â x̂ − b̂`,   since `b̂ = e − A_F s`,

so `Problem.penaltyDoubled P x̂` and `CNS.penaltyDoubled (P.embed x̂)` should be equal. That is
the bridge between what the solver minimises and what `CNS.Sound` proves about. -/
def embed (P : Problem) (fixedVal : Array Bool) (x : Array Bool) : Array Bool := Id.run do
  let mut full := fixedVal
  for u in [0:P.nvars] do
    full := full.set! (P.varOf.getD u 0) (x.getD u false)
  return full

/-- Number of off-diagonal neighbours of a surviving variable (≤ 28). -/
def degree (P : Problem) (u : Nat) : Nat :=
  ((P.rowsOf.getD u #[]).foldl (fun acc r =>
    (P.varsOf.getD r #[]).foldl (fun a w =>
      if w == u || a.contains w then a else a.push w) acc) #[]).size

end Problem
end CNS
