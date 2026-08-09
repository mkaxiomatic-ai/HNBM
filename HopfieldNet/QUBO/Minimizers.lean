/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.QUBO.Refine

/-!
# The energy minimisers are exactly the feasible assignments

`CNS.Net` shows the HNBM energy of the reduced network is the paper's objective. This module
draws the consequence that makes the neurodynamics *correct* rather than merely *plausible*:

  the global minimisers of `zeroOneHamiltonian (netParams P)` are exactly the states whose
  reduced penalty vanishes,

and the energy gap between a minimiser and anything else is at least `1/2`. The gap matters:
it is what turns "the Boltzmann measure favours low energy" into "the Boltzmann measure
concentrates on solutions", with an explicit rate.

Combined with the ergodicity results in `HopfieldNet.Quiver.BM.Ergodicity` — the random-scan
Gibbs chain has a unique stationary distribution and it is the Boltzmann measure of this very
energy — this says the annealed Boltzmann machine of eq. (6) concentrates on the solution set.
Combined with `CNS.Refine.netVec_eq_localField`, it says that about the code that runs.

## What is *not* claimed

Nothing here is a statement about the *momentum* recurrence of eqs (3) and (6). That dynamics
is an undamped accumulator, it is not an `Up` of any HNBM network, and no convergence theory
for it exists. The results below apply to the memoryless single-site reading, which is the one
`ModelConfig.sequential` selects.
-/

namespace QUBO
namespace Problem

open Finset

variable (P : Problem)

/-! ## The reduced objective is a non-negative integer -/

/-- The reduced objective is a sum of squares, hence non-negative. -/
theorem penaltyR_nonneg (x : Fin P.nvars → Bool) : 0 ≤ penaltyR P x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The objective vanishes exactly when every constraint row is satisfied. -/
theorem penaltyR_eq_zero_iff (x : Fin P.nvars → Bool) :
    penaltyR P x = 0 ↔ ∀ r ∈ Finset.range P.nrows, rowSumR P x r = bhatR P r := by
  unfold penaltyR
  rw [Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _]
  constructor
  · intro h r hr; have := h r hr; rwa [sq_eq_zero_iff, sub_eq_zero] at this
  · intro h r hr; rw [h r hr, sub_self]; ring

/-- A row sum is the cardinality of the set of active variables in that row, hence an integer. -/
theorem rowSumR_eq_card (x : Fin P.nvars → Bool) (r : Nat) :
    rowSumR P x r
      = ((Finset.univ.filter fun u : Fin P.nvars => (x u && P.inRow u.val r) = true).card : ℝ) := by
  have hpt : ∀ u : Fin P.nvars, Ahat P r u * bit (x u)
      = (if (x u && P.inRow u.val r) = true then (1 : ℝ) else 0) := by
    intro u
    unfold Ahat bit
    by_cases h1 : x u = true <;> by_cases h2 : P.inRow u.val r = true <;> simp [h1, h2]
  unfold rowSumR
  rw [Finset.sum_congr rfl fun u _ => hpt u, ← Finset.sum_filter, Finset.sum_const,
    nsmul_eq_mul, mul_one]

/-- **The objective takes integer values.**

Each residual is a difference of two integers, so the sum of squares is an integer — and a
non-zero one is therefore at least `1`. -/
theorem exists_int_penaltyR (x : Fin P.nvars → Bool) : ∃ m : ℤ, penaltyR P x = (m : ℝ) := by
  refine ⟨∑ r ∈ Finset.range P.nrows,
    (((Finset.univ.filter fun u : Fin P.nvars => (x u && P.inRow u.val r) = true).card : ℤ)
      - P.bhat.getD r 0) ^ 2, ?_⟩
  unfold penaltyR bhatR
  push_cast
  exact Finset.sum_congr rfl fun r _ => by rw [rowSumR_eq_card]

/-- **A non-zero objective is at least `1`.**

There is no state whose penalty is a small positive number: the search either lands on a
solution or misses by a whole unit. -/
theorem one_le_penaltyR_of_ne_zero {x : Fin P.nvars → Bool} (hx : penaltyR P x ≠ 0) :
    1 ≤ penaltyR P x := by
  obtain ⟨m, hm⟩ := exists_int_penaltyR P x
  have hpos : 0 < penaltyR P x := lt_of_le_of_ne (penaltyR_nonneg P x) (Ne.symm hx)
  rw [hm] at hpos ⊢
  exact_mod_cast (by exact_mod_cast hpos : (0 : ℤ) < m)

/-! ## Recovering a state's bits -/

variable [Nonempty (Fin P.nvars)]

/-- The bits of an abstract state. `pact` pins each activation to `0` or `1`, so this loses
nothing. -/
noncomputable def bitsOfState (s : (TwoState.ZeroOne ℝ (Fin P.nvars)).State) :
    Fin P.nvars → Bool :=
  fun u => decide (s.act u = 1)

/-- Every state is the state of its own bits: `stateOfBits` and `bitsOfState` are inverse. -/
theorem stateOfBits_bitsOfState (s : (TwoState.ZeroOne ℝ (Fin P.nvars)).State) :
    stateOfBits P (bitsOfState P s) = s := by
  refine NeuralNetwork.ext fun u => ?_
  show bit (bitsOfState P s u) = s.act u
  unfold bitsOfState bit
  rcases s.hp u with h | h
  · rw [if_neg (by simp [h]), h]
  · rw [if_pos (by simp [h]), h]

/-! ## The minimisers -/

/-- The minimum value the energy can take: attained exactly on the feasible assignments. -/
noncomputable def minEnergy : ℝ := -constR P / 2

/-- **The energy is bounded below by `−‖b̂‖²/2`.** -/
theorem minEnergy_le (hW : P.Wf) (s : (TwoState.ZeroOne ℝ (Fin P.nvars)).State) :
    minEnergy P ≤ HopfieldEnergy.zeroOneHamiltonian (netParams P) s := by
  rw [← stateOfBits_bitsOfState P s, zeroOneHamiltonian_eq P hW]
  unfold minEnergy
  have := penaltyR_nonneg P (bitsOfState P s)
  linarith

/-- **A state attains the minimum energy exactly when it is feasible.**

The left-hand side is a statement about the repository's Boltzmann Hamiltonian; the right-hand
side is `p(x̂) = 0`, which `CNS.Sound` identifies with satisfying the constraints (10a)–(10d).
So minimising the HNBM energy *is* solving the puzzle — not a relaxation of it, and not a
heuristic correlated with it. -/
theorem energy_eq_min_iff (hW : P.Wf) (s : (TwoState.ZeroOne ℝ (Fin P.nvars)).State) :
    HopfieldEnergy.zeroOneHamiltonian (netParams P) s = minEnergy P
      ↔ penaltyR P (bitsOfState P s) = 0 := by
  rw [← stateOfBits_bitsOfState P s, zeroOneHamiltonian_eq P hW]
  unfold minEnergy
  simp only [stateOfBits_bitsOfState]
  constructor
  · intro h; linarith
  · intro h; rw [h]; ring

/-- **The energy gap is at least one half.**

Any state that is not feasible sits at least `1/2` above the minimum. Because the gap is
bounded away from zero and the state space is finite, the Boltzmann weight of every infeasible
state decays like `exp(−1/(2T))` relative to a feasible one. -/
theorem half_le_energy_sub_min (hW : P.Wf) (s : (TwoState.ZeroOne ℝ (Fin P.nvars)).State)
    (hs : HopfieldEnergy.zeroOneHamiltonian (netParams P) s ≠ minEnergy P) :
    minEnergy P + 1 / 2 ≤ HopfieldEnergy.zeroOneHamiltonian (netParams P) s := by
  have hpen : penaltyR P (bitsOfState P s) ≠ 0 := fun h => hs ((energy_eq_min_iff P hW s).mpr h)
  have h1 := one_le_penaltyR_of_ne_zero P hpen
  have heq : HopfieldEnergy.zeroOneHamiltonian (netParams P) s
      = (penaltyR P (bitsOfState P s) - constR P) / 2 := by
    rw [← stateOfBits_bitsOfState P s, zeroOneHamiltonian_eq P hW]
    simp only [stateOfBits_bitsOfState]
  rw [heq]
  unfold minEnergy
  linarith

/-- **The Boltzmann weight of an infeasible state vanishes as the temperature falls.**

Relative to a feasible state, an infeasible one is suppressed by at least `exp(−1/(2T))`. With
`HopfieldNet.Quiver.BM.Ergodicity`'s identification of the random-scan chain's unique stationary
distribution as the Boltzmann measure of this energy, this is the sense in which the annealed
Boltzmann machine of eq. (6) concentrates on the solutions of the puzzle. -/
theorem boltzmann_ratio_le (hW : P.Wf) {T : ℝ} (hT : 0 < T)
    (s s' : (TwoState.ZeroOne ℝ (Fin P.nvars)).State)
    (hs : HopfieldEnergy.zeroOneHamiltonian (netParams P) s ≠ minEnergy P)
    (hs' : HopfieldEnergy.zeroOneHamiltonian (netParams P) s' = minEnergy P) :
    Real.exp (-(HopfieldEnergy.zeroOneHamiltonian (netParams P) s) / T)
      ≤ Real.exp (-(1 / 2) / T) * Real.exp (-(HopfieldEnergy.zeroOneHamiltonian
          (netParams P) s') / T) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [hs']
  have hgap := half_le_energy_sub_min P hW s hs
  rw [show -(1 / 2 : ℝ) / T + -(minEnergy P) / T = (-(1 / 2) + -(minEnergy P)) / T by ring,
    div_le_div_iff_of_pos_right hT]
  linarith

/-- The suppression factor tends to zero as the temperature does. -/
theorem tendsto_suppression :
    Filter.Tendsto (fun T : ℝ => Real.exp (-(1 / 2) / T))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hdiv : Filter.Tendsto (fun T : ℝ => -(1 / 2) / T)
      (nhdsWithin 0 (Set.Ioi 0)) Filter.atBot := by
    have : Filter.Tendsto (fun T : ℝ => T⁻¹) (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop :=
      tendsto_inv_nhdsGT_zero
    simpa [div_eq_mul_inv] using this.const_mul_atTop_of_neg (by norm_num : (-(1 / 2) : ℝ) < 0)
  exact Real.tendsto_exp_atBot.comp hdiv

end Problem
end QUBO
