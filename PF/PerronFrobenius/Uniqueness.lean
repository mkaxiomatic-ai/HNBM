/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import PF.PerronFrobenius.Primitive



/-READY FOR REVIEW-/

/-!
# Perron-Frobenius Theorem: Uniqueness of the Eigenvector

This file proves that for a primitive, non-negative matrix, the strictly positive
eigenvector corresponding to the Perron root `r` is unique up to a positive
scalar multiple. This corresponds to part (d) of Theorem 1.1 in Seneta's
"Non-negative Matrices and Markov Chains".

The proof strategy is as follows:
1. Given two strictly positive eigenvectors `v` and `w` for the same eigenvalue `r`.
2. Construct a new vector `z = v - c • w`, where `c` is the minimum of the
   component-wise ratios `vᵢ / wᵢ`.
3. By construction, `z` is a non-negative vector, and at least one of its
   components is zero.
4. Show that `z` is also an eigenvector of `A` with eigenvalue `r`.
5. Use the primitivity of `A` to show that if `z` were non-zero, then `A^k * z`
   would be strictly positive for a large enough `k`.
6. However, `A^k * z = r^k • z`, which must have a zero component since `z` does.
   This is a contradiction.
7. Thus, `z` must be the zero vector, which implies `v = c • w`.
-/

namespace Matrix
variable {n : Type*} [Fintype n] [Nonempty n] [DecidableEq n]
variable {A : Matrix n n ℝ} {r : ℝ}

/--
A non-zero, non-negative eigenvector `z` of a primitive matrix `A` corresponding to a
positive eigenvalue `r` cannot have any zero entries. This is a crucial lemma for
the uniqueness and dominance proofs.
-/
lemma eigenvector_no_zero_entries_of_primitive (hA_prim : IsPrimitive A) (_ : 0 < r)
    {z : n → ℝ} (h_eig : A *ᵥ z = r • z) (hz_nonneg : ∀ i, 0 ≤ z i) (hz_ne_zero : z ≠ 0)
    (i₀ : n) (hi₀_zero : z i₀ = 0) :
    False := by
  obtain ⟨_, k, _, hA_k_pos⟩ := hA_prim
  have h_gen : ∀ m, (A ^ m) *ᵥ z = (r ^ m) • z := by
    intro m; induction m with
    | zero => simp
    | succ m ih => rw [pow_mulVec_succ, ih, mulVec_smul, h_eig, smul_smul, pow_succ', pow_mul_comm']
  simpa [h_gen, hi₀_zero] using positive_mul_vec_of_nonneg_vec hA_k_pos hz_nonneg hz_ne_zero i₀


/--
**Uniqueness of the Positive Eigenvector for Primitive Matrices**

The positive eigenvector of a primitive matrix `A` corresponding to a positive eigenvalue `r`
is unique up to a positive scalar multiple. This corresponds to Theorem 1.1 (d) in Seneta.
-/
theorem uniqueness_of_positive_eigenvector (hA_prim : IsPrimitive A) (hr_pos : 0 < r) (v w : n → ℝ)
    (hv_eig : A *ᵥ v = r • v) (hw_eig : A *ᵥ w = r • w) (hv_pos : ∀ i, 0 < v i) (hw_pos : ∀ i, 0 < w i) :
    ∃ c : ℝ, 0 < c ∧ v = c • w := by
  let c := Finset.univ.inf' Finset.univ_nonempty (fun i ↦ v i / w i)
  refine ⟨c, Finset.inf'_pos _ (fun i _ ↦ div_pos (hv_pos i) (hw_pos i)), ?_⟩
  have hz_nonneg : ∀ i, 0 ≤ (v - c • w) i := fun i ↦ sub_nonneg.2 <|
    (le_div_iff₀ (hw_pos i)).1 (Finset.inf'_le _ (Finset.mem_univ i))
  have hz_eig : A *ᵥ (v - c • w) = r • (v - c • w) := by
    simp only [mulVec_sub]; simp only [mulVec_smul]; simp only [ hv_eig];
    simp only [hw_eig]; simp only [smul_sub]; rw [smul_comm]
  by_cases h_z : v - c • w = 0
  · exact sub_eq_zero.1 h_z
  · obtain ⟨i₀, _, hi₀⟩ := Finset.exists_mem_eq_inf' _ (fun i ↦ v i / w i)
    have hz_zero : (v - c • w) i₀ = 0 := by simp [sub_eq_zero, ← div_eq_iff (hw_pos i₀).ne', ← hi₀]; rfl
    exact (eigenvector_no_zero_entries_of_primitive hA_prim hr_pos hz_eig hz_nonneg h_z i₀ hz_zero).elim

end Matrix
