/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import PF.PerronFrobenius.Dominance

namespace Matrix

open Matrix CollatzWielandt Quiver.Path

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-READY FOR REVIEW -/

/--
**Perron-Frobenius Theorem for Column-Stochastic Matrices**.

An irreducible, non-negative matrix with column sums equal to 1 (i.e., column-stochastic)
has a Perron root of 1, and there exists a unique (up to scaling) strictly positive
eigenvector `v` for this eigenvalue. This stationary vector is unique when constrained
to the standard simplex.
-/
theorem exists_positive_eigenvector_of_irreducible_stochastic
    {A : Matrix n n ℝ} (hA_irred : A.IsIrreducible) (h_col_stoch : ∀ j, ∑ i, A i j = 1) :
    ∃! (v : stdSimplex ℝ n), A *ᵥ v.val = v.val := by
  have hA_nonneg := hA_irred.1

  -- Explicitly typed to n → ℝ so HSMul knows how to apply the scalar
  have h_eig_T : Aᵀ *ᵥ (fun _ ↦ 1 : n → ℝ) = (1 : ℝ) • (fun _ ↦ 1 : n → ℝ) := by
    ext i; simp [mulVec_apply_eq_sum, h_col_stoch]

  -- Using rw and .symm directly instead of fighting the elaborator with .trans
  have r_A_eq_one : perronRoot_alt A = 1 := by
    rw [perronRoot_transpose_eq A hA_irred]
    exact (eigenvalue_is_perron_root_of_positive_eigenvector hA_irred.transpose
      (fun i j ↦ hA_nonneg j i) zero_lt_one (fun _ ↦ zero_lt_one) h_eig_T).symm

  obtain ⟨v, ⟨r, hr_pos, h_eig⟩, _⟩ := pft_irreducible hA_irred
  have v_pos_raw := eigenvector_is_positive_of_irreducible hA_irred h_eig v.property.1 (ne_zero_of_mem_stdSimplex v.property)
  have h_eig_one : A *ᵥ v.val = v.val := by
    have r_eq := eigenvalue_is_perron_root_of_positive_eigenvector hA_irred hA_nonneg hr_pos v_pos_raw h_eig
    simpa [r_eq, r_A_eq_one] using h_eig

  refine ⟨v, h_eig_one, fun w hw_eig ↦ Subtype.ext ?_⟩
  have hv_eig' : A *ᵥ v.val = (1 : ℝ) • v.val := by simpa using h_eig_one
  have hw_eig' : A *ᵥ w.val = (1 : ℝ) • w.val := by simpa using hw_eig
  have v_pos := eigenvector_is_positive_of_irreducible hA_irred hv_eig' v.property.1 (ne_zero_of_mem_stdSimplex v.property)
  have w_pos := eigenvector_is_positive_of_irreducible hA_irred hw_eig' w.property.1 (ne_zero_of_mem_stdSimplex w.property)

  obtain ⟨c, _, hc_eq⟩ := uniqueness_of_positive_eigenvector_gen hA_irred zero_lt_one v_pos w_pos hv_eig' hw_eig'
  have hc_one : c = 1 := calc
    c = c * ∑ i, w.val i := by simp [w.property.2]
    _ = ∑ i, c * w.val i := by rw [← Finset.mul_sum]
    _ = ∑ i, v.val i := by simp [hc_eq, smul_eq_mul]
    _ = 1 := v.property.2
  simp [hc_eq, hc_one]

end Matrix
