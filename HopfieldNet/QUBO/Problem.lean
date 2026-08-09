/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# A 0/1 QUBO in canonical form

`Problem` is the data the solver runs on: a constraint system `Â x̂ = b̂` with `Â` a `0/1`
matrix given column-wise, together with the folded threshold `θ̂` and the additive constant.
The objective is `‖Â x̂ − b̂‖²`, and a zero of it is a feasible point.

Nothing here is about Sudoku. `HopfieldNet.CNS` builds one of these from a Sudoku puzzle;
`HopfieldNet.QUBO.Instances.*` build others. The theory that makes this a Hopfield/Boltzmann
network lives in `HopfieldNet.QUBO.Net`.
-/

namespace QUBO

structure Problem where
  /-- Number of surviving variables — the Table I quantity. -/
  nvars : Nat
  /-- Number of constraint rows of `Â`. A field rather than the global `numRows` so that the
  QUBO layer (`CNS.Net`, `CNS.Refine`, `CNS.Minimizers`) is about an arbitrary 0/1 incidence;
  see `CNS.Incidence`. -/
  nrows : Nat
  /-- Reduced index → original `x_{ijk}` index. -/
  varOf : Array Nat
  /-- Reduced index → the (at most four) penalty rows containing it. -/
  rowsOf : Array (Array Nat)
  /-- Penalty row → the surviving variables occurring in it. -/
  varsOf : Array (Array Nat)
  /-- `b̂ = e − A_F s`, one entry per penalty row. -/
  bhat : Array Int
  /-- `θ̂_u = ½·deg(u) − Σ_{r ∋ u} b̂_r`, with `deg(u) = (rowsOf u).size`. Stored halved;
  Stored **doubled**: this field is `2 θ̂_u`, not `θ̂_u`.

  `θ̂_u = ½·deg(u) − Σ_{r ∋ u} b̂_r` is a half-integer whenever `deg(u)` is odd, so storing it
  directly would silently restrict the library to even-degree incidences — a restriction Sudoku
  (degree 4) hides, and which bites the moment a subset has odd size or a vertex has even graph
  degree. Doubling costs nothing and removes it; `thetaR` halves on the way to `ℝ`. -/
  theta : Array Int
  /-- `‖b̂‖²`, i.e. twice the additive constant `½‖b̂‖²`. -/
  constDoubled : Int
  /-- The assignment Algorithm 1 already determined. -/
  base : Array (Option Nat)
  deriving Inhabited

namespace Problem

/-- Row sums `ρ_r = Σ_{v ∈ r} x̂_v`.

The `if` sits inside the assignment and the inner loop is a written-out `Array.foldl`. Both are
cosmetic at run time — the compiled code is the same scatter — but they matter for proofs: the
`@[simp]` lemma `List.forIn_pure_yield_eq_foldl` only matches a loop body of the shape
`fun u ρ => pure (.yield _)`, and an `if` wrapped around the `pure` blocks it. With this shape
`simp [Id.run]` turns the loop into a `List.foldl` that ordinary list induction can handle. -/
@[inline] def rowSums (P : Problem) (x : Array Bool) : Array Int := Id.run do
  let mut ρ : Array Int := Array.replicate P.nrows 0
  for u in [0:P.nvars] do
    ρ := if x.getD u false then
           (P.rowsOf.getD u #[]).foldl (fun ρ r => ρ.set! r ((ρ.getD r 0) + 1)) ρ
         else ρ
  return ρ

/-- `‖Â x̂ − b̂‖²`, i.e. twice the paper's `p(x̂)`. Zero exactly when `x̂` solves the puzzle. -/
def penaltyDoubled (P : Problem) (x : Array Bool) : Int :=
  let ρ := P.rowSums x
  (Array.range P.nrows).foldl
    (fun acc r => let d := (ρ.getD r 0) - (P.bhat.getD r 0); acc + d * d) 0

/-- The net input `W x̂ − θ̂` driving (1), (3) and (6).

Uses `(W x̂)_u = deg(u)·x̂_u − Σ_{r ∋ u} ρ_r`, so the whole vector costs `O(nvars)`.
The degree is read per column rather than fixed at Sudoku's `4`; see `CNS.Incidence`. -/
def netVec (P : Problem) (x : Array Bool) : Array Int :=
  let ρ := P.rowSums x
  (Array.range P.nvars).map fun u =>
    let s := (P.rowsOf.getD u #[]).foldl (fun acc r => acc + ρ.getD r 0) 0
    2 * ((if x.getD u false then ((P.rowsOf.getD u #[]).size : Int) else 0) - s)
      - P.theta.getD u 0

/-- The reduced index of an original variable, when it survived the reduction.

A linear scan, which is fine: `embed` runs in the consistency checks, never in a sweep. Written
as a lookup rather than as a scatter with `set!` for the usual reason — `Array.getElem_map` and
`List.find?` are characterised pointwise, a scatter only by induction on its trip count. -/
def redIndex (P : Problem) (v : Nat) : Option Nat :=
  (List.range P.nvars).find? fun u => P.varOf.getD u 0 == v

/-- Number of off-diagonal neighbours of a surviving variable (≤ 28). -/
def degree (P : Problem) (u : Nat) : Nat :=
  ((P.rowsOf.getD u #[]).foldl (fun acc r =>
    (P.varsOf.getD r #[]).foldl (fun a w =>
      if w == u || a.contains w then a else a.push w) acc) #[]).size

end Problem
end QUBO
