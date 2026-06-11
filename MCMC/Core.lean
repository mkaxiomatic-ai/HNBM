/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import PF.PerronFrobenius.Aperiodic
import PF.PerronFrobenius.Stochastic

/-!
# Finite MCMC core definitions

Row-stochastic matrices, stationarity, and the `IsMCMC` typeclass.
-/

open Matrix Finset
open scoped BigOperators

variable {n : Type*} [Fintype n]

/-- A matrix is row-stochastic if it is nonnegative and every row sums to `1`. -/
def IsStochastic (P : Matrix n n ℝ) : Prop :=
  (∀ i j, 0 ≤ P i j) ∧ ∀ i, ∑ j, P i j = 1

lemma isStochastic_one [DecidableEq n] : IsStochastic (1 : Matrix n n ℝ) := by
  constructor
  · intro i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  · intro i
    simp [Matrix.one_apply]

lemma isStochastic_mul {P Q : Matrix n n ℝ}
    (hP : IsStochastic P) (hQ : IsStochastic Q) : IsStochastic (P * Q) := by
  constructor
  · intro i j
    simpa [Matrix.mul_apply] using
      sum_nonneg fun k _ => mul_nonneg (hP.1 i k) (hQ.1 k j)
  · intro i
    calc
      ∑ j, (P * Q) i j = ∑ j, ∑ k, P i k * Q k j := by simp [Matrix.mul_apply]
      _ = ∑ k, ∑ j, P i k * Q k j := by
          simpa using
            Finset.sum_comm (s := Finset.univ) (t := Finset.univ) (f := fun j k => P i k * Q k j)
      _ = ∑ k, P i k * ∑ j, Q k j := by simp [mul_sum]
      _ = 1 := by simp [hQ.2, hP.2 i]

lemma isStochastic_pow [DecidableEq n] {P : Matrix n n ℝ} (hP : IsStochastic P) :
    ∀ k, IsStochastic (P ^ k)
  | 0 => isStochastic_one
  | k + 1 => isStochastic_mul (isStochastic_pow hP k) hP

/-- `π` is stationary for `P` when `Pᵀ *ᵥ π = π`. -/
def IsStationary (P : Matrix n n ℝ) (π : stdSimplex ℝ n) : Prop :=
  Pᵀ *ᵥ π.val = π.val

/-- Verified MCMC transition matrix together with its target stationary distribution. -/
class IsMCMC [DecidableEq n] (P : Matrix n n ℝ) (π : stdSimplex ℝ n) where
  stochastic : IsStochastic P
  stationary : IsStationary P π
  irreducible : Matrix.IsIrreducible P
  primitive : IsPrimitive P

variable [Nonempty n]

/-- Irreducible stochastic matrices admit a unique stationary distribution. -/
theorem exists_unique_stationary_distribution_of_irreducible
    [DecidableEq n] {P : Matrix n n ℝ}
    (h_stoch : IsStochastic P) (h_irred : Matrix.IsIrreducible P) :
    ∃! π : stdSimplex ℝ n, IsStationary P π := by
  have hPT_col_stoch : ∀ j, ∑ i, Pᵀ i j = 1 := fun j => by simp [transpose_apply, h_stoch.2 j]
  simpa [IsStationary] using
    Matrix.exists_positive_eigenvector_of_irreducible_stochastic
      (isIrreducible_transpose_iff.mpr h_irred) hPT_col_stoch

/-- The unique stationary distribution of an irreducible stochastic matrix. -/
noncomputable def stationaryDistribution [DecidableEq n] (P : Matrix n n ℝ)
    (h_irred : Matrix.IsIrreducible P) (h_stoch : IsStochastic P) : stdSimplex ℝ n :=
  Classical.choose (exists_unique_stationary_distribution_of_irreducible h_stoch h_irred).exists

lemma stationaryDistribution_is_stationary [DecidableEq n] (P : Matrix n n ℝ)
    (h_irred : Matrix.IsIrreducible P) (h_stoch : IsStochastic P) :
    IsStationary P (stationaryDistribution P h_irred h_stoch) :=
  Classical.choose_spec (exists_unique_stationary_distribution_of_irreducible h_stoch h_irred).exists

/-- Stochastic, irreducible, primitive matrices define a valid MCMC setup. -/
theorem isMCMC_of_properties (P : Matrix n n ℝ) [DecidableEq n]
    (h_stoch : IsStochastic P) (h_irred : Matrix.IsIrreducible P) (h_prim : IsPrimitive P) :
    IsMCMC P (stationaryDistribution P h_irred h_stoch) where
  stochastic := h_stoch
  stationary := stationaryDistribution_is_stationary P h_irred h_stoch
  irreducible := h_irred
  primitive := h_prim

private lemma aperiodic_of_primitive [DecidableEq n] [Nonempty n] (P : Matrix n n ℝ)
    (h_nonneg : ∀ i j, 0 ≤ P i j) (h_prim : IsPrimitive P) :
    Matrix.IsAperiodic P :=
  Matrix.primitive_implies_irreducible_and_aperiodic (A := P) h_nonneg h_prim

omit [Nonempty n] in
/-- Aperiodicity follows from primitivity. -/
theorem aperiodic_of_properties [DecidableEq n] [Nonempty n] (P : Matrix n n ℝ)
    (h_stoch : IsStochastic P) (h_prim : IsPrimitive P) :
    Matrix.IsAperiodic P :=
  aperiodic_of_primitive P h_stoch.1 h_prim

omit [Nonempty n] in
lemma IsMCMC.aperiodic [DecidableEq n] [Nonempty n]
    {P : Matrix n n ℝ} {π : stdSimplex ℝ n} (h : IsMCMC P π) :
    Matrix.IsAperiodic P :=
  aperiodic_of_primitive P h.stochastic.1 h.primitive
