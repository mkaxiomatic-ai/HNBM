/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.QUBO.Net

/-!
# A non-Sudoku QUBO, with two different column degrees

`CNS.Net` proves `E(x̂) = ½‖Âx̂ − b̂‖² − ½‖b̂‖²` from `Problem.Wf` alone, which mentions no
incidence and no degree. That claim is easy to make and easy to get wrong: with only Sudoku
available, a generalisation that secretly still assumes `deg = 4` typechecks, the solver keeps
working, and one ships a "generic QUBO" theorem true of exactly one QUBO.

This module is the guard. `toyP` has two variables of degrees `2` and `4`, so any proof that
smuggled in regularity fails here. It exists to be built, not to be used.
-/

namespace QUBO
namespace Problem

/-- Two variables and four rows: variable `0` meets rows `{0,1}`, variable `1` meets all four.
The degrees are `2` and `4`, so this incidence is *not* regular. -/
def toyP : Problem where
  nvars := 2
  nrows := 4
  varOf := #[0, 1]
  rowsOf := #[#[0, 1], #[0, 1, 2, 3]]
  varsOf := #[#[0, 1], #[0, 1], #[1], #[1]]
  bhat := #[1, 1, 0, 0]
  -- `2θ₀ = 2 − 2(b̂₀+b̂₁) = −2` and `2θ₁ = 4 − 2(b̂₀+b̂₁+b̂₂+b̂₃) = 0`
  theta := #[-2, 0]
  constDoubled := 2
  base := #[]

instance : Nonempty (Fin toyP.nvars) := ⟨⟨0, by decide⟩⟩

/-- The toy instance is a well-formed 0/1 QUBO. -/
theorem toyP_wf : toyP.Wf where
  nodup := by decide
  mem_lt := by decide
  theta_eq := by
    intro u hu
    have hu' : u < 2 := hu
    interval_cases u <;>
      simp [toyP, Finset.sum_range_succ, Array.getD_eq_getD_getElem?]
  const_eq := by
    simp [toyP, Finset.sum_range_succ, Array.getD_eq_getD_getElem?]

/-- **The energy bridge holds at an irregular incidence.**

The same theorem `CNS.Net` proves for the Sudoku QUBO, instantiated where the columns have
different degrees. If this ever fails to compile, a regularity assumption has crept back in. -/
theorem toy_zeroOneHamiltonian_eq (x : Fin toyP.nvars → Bool) :
    HopfieldEnergy.zeroOneHamiltonian (netParams toyP) (stateOfBits toyP x)
      = (penaltyR toyP x - constR toyP) / 2 :=
  zeroOneHamiltonian_eq toyP toyP_wf x

/-- The two columns really do have different degrees. -/
example : (toyP.rowsOf.getD 0 #[]).size ≠ (toyP.rowsOf.getD 1 #[]).size := by decide

/-- One variable meeting three rows: column degree `3`, which is **odd**.

This is the guard on the doubled `theta`. Before it, `theta` stored `θ̂_u = ½·deg(u) − Σ b̂_r`
directly, so an odd degree had no integer representation and the library silently only worked
for even-degree incidences — a restriction Sudoku's degree `4` hid completely, and which both
`QUBO.Instances.ExactCover` and `QUBO.Instances.Colouring` had to work around by duplicating
every row. If this stops compiling, the halving has crept back in. -/
def toyOdd : Problem where
  nvars := 1
  nrows := 3
  varOf := #[0]
  rowsOf := #[#[0, 1, 2]]
  varsOf := #[#[0], #[0], #[0]]
  bhat := #[1, 1, 1]
  -- `2θ̂₀ = 3 − 2(1+1+1) = −3`, odd, and therefore unrepresentable before the change
  theta := #[-3]
  constDoubled := 3
  base := #[]

instance : Nonempty (Fin toyOdd.nvars) := ⟨⟨0, by decide⟩⟩

/-- The odd-degree instance is well formed. -/
theorem toyOdd_wf : toyOdd.Wf where
  nodup := by decide
  mem_lt := by decide
  theta_eq := by
    intro u hu
    have hu' : u < 1 := hu
    interval_cases u <;>
      simp [toyOdd, Finset.sum_range_succ, Array.getD_eq_getD_getElem?]
  const_eq := by
    simp [toyOdd, Finset.sum_range_succ, Array.getD_eq_getD_getElem?]

/-- **The energy bridge holds at an odd column degree.** -/
theorem toyOdd_zeroOneHamiltonian_eq (x : Fin toyOdd.nvars → Bool) :
    HopfieldEnergy.zeroOneHamiltonian (netParams toyOdd) (stateOfBits toyOdd x)
      = (penaltyR toyOdd x - constR toyOdd) / 2 :=
  zeroOneHamiltonian_eq toyOdd toyOdd_wf x

/-- The degree really is odd. -/
example : (toyOdd.rowsOf.getD 0 #[]).size = 3 := by decide

end Problem
end QUBO
