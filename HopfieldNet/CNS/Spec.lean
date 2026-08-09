/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.CNS.Encoding
import HopfieldNet.Quiver.NeuralNetwork.TwoState

/-!
# The Sudoku QUBO as an HNBM network

Everything else under `HopfieldNet/CNS/` is deliberately Mathlib-free, so that the data and
execution layers rebuild in seconds. This module is the exception: it imports Mathlib and the
`HopfieldNet.Quiver` development in order to exhibit Li & Wang's Sudoku QUBO as an honest
instance of the repository's existing Hopfield/Boltzmann framework, rather than as a parallel
construction that merely resembles one.

**Building this module is slow** (it pulls in Mathlib and `TwoState`); nothing in the executable
pipeline depends on it, and `lake exe cns` does not build it.

## What is exhibited

`TwoState.ZeroOne ℝ (Fin numVars)` is the repository's `{0,1}`-valued network: its `fact` is the
hard threshold `if θ ≤ net then 1 else 0` of the paper's eq. (2), its `fnet` is `(Wx)_u`
excluding the self-term, and its `κ₂ = 1` gives one scalar threshold per neuron. To place a
problem on it one must supply a `Params`, whose non-trivial obligation is

  `pm W = W.IsSymm ∧ ∀ u, W u u = 0`.

That is exactly the shape the paper's QUBO takes once the diagonal of `AᵀA` is folded into `θ`
using `x² = x` — the derivation in `CNS.Encoding`. So the fit is not a coincidence to be checked
numerically; it is a consequence of the encoding, and `quboParams` below is the witness.

## `W` here versus `weight` in `CNS.Encoding`

`CNS.Encoding.weight` computes `−(AᵀA − 4I)` by counting shared rows with `Array.contains`,
which is fast but makes symmetry a statement about multiset intersection. Here `W` is written
directly as the incidence sum

  `W u v = if u = v then 0 else −∑_r A_{ru} A_{rv}`,

for which symmetry is `mul_comm` under the sum. The two agree; `cns encoding` checks the
executable one, and this module proves the obligations for the mathematical one.
-/

namespace CNS

namespace Spec

open scoped Classical

/-- Incidence of the stacked constraint matrix: `1` when variable `v` occurs in row `r`. -/
noncomputable def Aent (r v : Nat) : ℝ := if (rowsOfVar v).contains r then 1 else 0

/-- The coupling matrix `W = −(AᵀA − 4I)`, written as an incidence sum so that symmetry is
`mul_comm` and the zero diagonal is definitional. -/
noncomputable def Wmat : Matrix (Fin numVars) (Fin numVars) ℝ := fun u v =>
  if u = v then 0 else -(∑ r : Fin numRows, Aent r.val u.val * Aent r.val v.val)

/-- `W` is symmetric. -/
theorem Wmat_isSymm : Wmat.IsSymm := by
  ext u v
  simp only [Matrix.transpose_apply, Wmat]
  by_cases h : u = v
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h)]
    congr 1
    exact Finset.sum_congr rfl fun r _ => mul_comm _ _

/-- `W` has zero diagonal — the second half of `pm`, and what folding `diag(AᵀA)` into `θ`
buys. -/
theorem Wmat_diag (u : Fin numVars) : Wmat u u = 0 := by
  simp [Wmat]

/-- `numVars = n³ > 0`, so the index type is inhabited. `numVars` is a `def`, so this is not
found by instance search on its own. -/
instance : Nonempty (Fin numVars) := ⟨⟨0, by simp only [numVars, n]; omega⟩⟩

/-- The per-neuron threshold `θ̂_u`, transported from `CNS.Encoding`. -/
noncomputable def thetaR (u : Fin numVars) : ℝ := (theta u.val : ℝ)

/-- **The Sudoku QUBO as parameters of the repository's `{0,1}` network.**

The only substantive obligation is `pm`, discharged by `Wmat_isSymm` and `Wmat_diag`; `pw` is
`True` for this network, and the off-arrow condition reduces to the zero diagonal because
`ZeroOne`'s arrows are exactly the pairs `u ≠ v`. -/
noncomputable def quboParams : Params (TwoState.ZeroOne ℝ (Fin numVars)) where
  h_arrows := fun _ _ _ => trivial
  w := Wmat
  σ := fun _ => ⟨#[0], rfl⟩
  θ := fun u => ⟨#[thetaR u], rfl⟩
  hw := by
    intro u v huv
    -- no arrow between `u` and `v` forces `u = v`, where `W` vanishes
    have : u = v := by
      by_contra hne
      exact huv ⟨⟨hne⟩, trivial⟩
    subst this
    exact Wmat_diag u
  hw' := ⟨Wmat_isSymm, Wmat_diag⟩

end Spec
end CNS
