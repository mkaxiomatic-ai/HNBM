/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.CNS.Problem
import HopfieldNet.QUBO.Net

/-!
# Sudoku as an instance of `QUBO.Incidence`

`QUBO.Incidence` is the interface the QUBO theory is stated against: which rows each column of
`A` meets, nothing more. This module supplies the value for Sudoku's constraints (10a)-(10d),
together with the fact that makes it well formed — a variable's four rows are pairwise distinct,
because the four families occupy disjoint index bands.

The degree `4` is recorded as an `Incidence.Regular` witness, but nothing depends on it: the
theory in `QUBO.Net` is degree-free. See `QUBO.ToyQubo` for an irregular instance.
-/

namespace CNS

open QUBO
open QUBO.Problem

namespace Problem

/-! ## The four rows of a Sudoku variable are distinct

This is what makes Sudoku's incidence 4-regular. Nothing downstream needs the constant, but the
`nodup` and in-range obligations of `Incidence` do have to be discharged. -/

/-- `boxOf` of a cell index is a legal block number. -/
private theorem boxOf_cellIdx_lt {i j : Nat} (hi : i < n) (hj : j < n) :
    boxOf (cellIdx i j) < n := by
  simp only [boxOf, rowOf, colOf, cellIdx, blk, n] at *
  omega

/-- `rowsOfVar` in the form the band argument needs: four rows, one per constraint family. -/
private theorem rowsOfVar_eq (v : Nat) (hv : v < numVars) :
    ∃ i j k b, i < n ∧ j < n ∧ k < n ∧ b < n ∧
      rowsOfVar v = #[rowCell i j, rowCol j k, rowRow i k, rowBox b k] := by
  have hi : v / (n * n) < n := by simp only [numVars, n] at *; omega
  have hj : v % (n * n) / n < n := by simp only [n] at *; omega
  have hk : v % n < n := by simp only [n] at *; omega
  exact ⟨_, _, _, _, hi, hj, hk, boxOf_cellIdx_lt hi hj, rfl⟩

/-- **The four constraint rows of a variable are pairwise distinct and in range.**

This is what makes `diag(ÂᵀÂ) = 4`, and hence what licenses folding the diagonal into `θ̂`.
The four families occupy the disjoint index bands `[0,n²)`, `[n²,2n²)`, `[2n²,3n²)`,
`[3n²,4n²)`, so no two of them can collide. -/
theorem rowsOfVar_nodup (v : Nat) (hv : v < numVars) :
    (rowsOfVar v).toList.Nodup ∧ ∀ r ∈ rowsOfVar v, r < numRows := by
  obtain ⟨i, j, k, b, hi, hj, hk, hb, hrv⟩ := rowsOfVar_eq v hv
  rw [hrv]
  constructor
  · show List.Nodup [rowCell i j, rowCol j k, rowRow i k, rowBox b k]
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil, not_or,
      not_false_eq_true, and_true, rowCell, rowCol, rowRow, rowBox, cellIdx]
    simp only [n] at *
    omega
  · intro r hr
    simp only [rowCell, rowCol, rowRow, rowBox, cellIdx] at hr
    simp at hr
    simp only [numRows, rowCell, rowCol, rowRow, rowBox, cellIdx, n] at *
    rcases hr with h | h | h | h <;> omega

/-- Every variable lies in exactly four constraint rows. -/
theorem rowsOfVar_size (v : Nat) : (rowsOfVar v).size = 4 := by
  simp [rowsOfVar]
end Problem


/-- **The Sudoku incidence** — constraints (10a)–(10d), one row per cell, row, column and block
occupancy. -/
def sudokuInc : Incidence where
  nvars  := numVars
  nrows  := numRows
  rowsOf := rowsOfVar
  nodup  := fun v h => (Problem.rowsOfVar_nodup v h).1
  mem_lt := fun v h => (Problem.rowsOfVar_nodup v h).2

@[simp] theorem sudokuInc_nvars  : sudokuInc.nvars  = numVars   := rfl
@[simp] theorem sudokuInc_nrows  : sudokuInc.nrows  = numRows   := rfl
@[simp] theorem sudokuInc_rowsOf : sudokuInc.rowsOf = rowsOfVar := rfl

/-- Sudoku's incidence is 4-regular. -/
def sudokuInc.regular : Incidence.Regular sudokuInc where
  deg := 4
  deg_eq := fun v _ => Problem.rowsOfVar_size v

end CNS

namespace QUBO.Problem

open CNS

/-- The structural invariants `Problem.ofReduced` establishes: a well-formed 0/1 QUBO that
refines the Sudoku incidence.

The `Wf` half is what every theorem in `HopfieldNet.QUBO` actually uses; the `Refines` half is
the only part that mentions Sudoku. `CNS.NetValid` proves the pipeline's problems satisfy both. -/
structure Valid (P : Problem) : Prop extends Wf P, Refines sudokuInc P

end QUBO.Problem
