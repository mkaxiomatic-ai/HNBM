/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.QUBO.Folds
import HopfieldNet.QUBO.Problem

/-!
# Constraint incidence, abstracted away from Sudoku

Everything the QUBO layer needs to know about a constraint system is its **incidence**: which
rows each column of `A` meets. `CNS.Net` proves `E(x̂) = ½‖Âx̂ − b̂‖² − ½‖b̂‖²` and `CNS.Refine`
identifies the solver's integer inner loop with the network's local field; neither uses anything
about Sudoku beyond that.

This module isolates the interface, so those theorems are about *any* 0/1 QUBO in canonical form
and Sudoku is one instance of it. Exact cover, graph colouring and max-cut are then values of
`Incidence`, not new developments.

## No degree constant

An earlier reading of the algebra had `diag(ÂᵀÂ) = 4` — the four rows of a Sudoku variable —
folded into `θ̂`, which would make regularity of the incidence a hypothesis. It is not needed:
the diagonal fold cancels *pointwise per column*, so the degree may vary from column to column.
What survives is the per-column `(rowsOf u).size`, and `Incidence` accordingly carries no degree
field. `CNS.ToyQubo` exhibits an instance with two different degrees, so this genericity is
exercised rather than merely claimed.
-/

namespace QUBO

/-- **A 0/1 constraint-incidence matrix, presented column-wise.**

`rowsOf v` lists the rows in which column `v` has a nonzero entry. `nodup` is what makes the
matrix 0/1 rather than integer-valued: a column meets each row at most once.

There is deliberately no degree field — see the module docstring. -/
structure Incidence where
  /-- Number of columns, i.e. decision variables. -/
  nvars : Nat
  /-- Number of rows, i.e. constraints. -/
  nrows : Nat
  /-- The rows in which column `v` has a nonzero entry. -/
  rowsOf : Nat → Array Nat
  /-- A column meets each of its rows exactly once, so the entries are `0` or `1`. -/
  nodup : ∀ v, v < nvars → (rowsOf v).toList.Nodup
  /-- Listed rows are real rows. -/
  mem_lt : ∀ v, v < nvars → ∀ r ∈ rowsOf v, r < nrows

/-- Optional regularity record. No theorem depends on it; it exists to document the degree of
an incidence that happens to be regular, such as Sudoku's `4`. -/
structure Incidence.Regular (I : Incidence) where
  /-- The common column degree. -/
  deg : Nat
  /-- Every in-range column has that degree. -/
  deg_eq : ∀ v, v < I.nvars → (I.rowsOf v).size = deg

end QUBO
