import PF.PerronFrobenius.CollatzWielandt
import PF.PerronFrobenius.Lemmas
import Mathlib.Tactic

namespace Matrix
open Finset Quiver
variable {n : Type*} [Fintype n]


/-READY FOR REVIEW-/

/-!
### The Perron-Frobenius Theorem for Primitive Matrices


This section formalizes Theorem 1.1 from Seneta's "Non-negative Matrices and Markov Chains".
The proof follows Seneta's logic :
1. Define the Perron root `r` as the supremum of the Collatz-Wielandt function `r(x)`.
2. Use the fact that `r(x)` is upper-semicontinuous on a compact set (the standard simplex)
   to guarantee the supremum is attained by a vector `v`.
3. Prove that `v` is an eigenvector by a contradiction argument using the primitivity of `A`.
4. Prove that `v` is strictly positive, again using primitivity.
-/
section PerronFrobenius
variable {n : Type*} [Fintype n]
variable {A : Matrix n n ℝ}

open LinearMap Set Filter Topology Finset Matrix.CollatzWielandt
open scoped Convex Pointwise

end PerronFrobenius

end Matrix

open Set Finset MetricSpace Topology Convex Quiver.Path

namespace Matrix

open Topology Metric Set Finset
section PerronFrobenius
open Finset Set IsCompact Topology Matrix

variable {n : Type*} [Fintype n] {A : Matrix n n ℝ}

lemma ratio_le_max_row_sum_simple (hA_nonneg : ∀ i j, 0 ≤ A i j) [Nonempty n]
    {x : n → ℝ} (_ : ∀ i, 0 ≤ x i) (i : n) (hx_i_pos : 0 < x i) :
    (A *ᵥ x) i / x i ≤ (∑ j, A i j) * (univ.sup' univ_nonempty x) / x i := by
  rw [mulVec_apply, div_le_div_iff_of_pos_right hx_i_pos, Finset.sum_mul]
  exact sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_left (le_sup' x (mem_univ j)) (hA_nonneg i j)

variable [Nonempty n] {A : Matrix n n ℝ}

/-- For an irreducible non-negative matrix, the Collatz-Wielandt value of the vector of all ones
    is strictly positive. This relies on the fact that an irreducible matrix cannot have a zero row
    (unless n=1, which is handled). A zero row would imply the sum of its entries is zero, which
    is the Collatz-Wielandt value for the vector of all ones. -/

lemma collatzWielandtFn_of_ones_is_pos (hA_irred : IsIrreducible A) (hA_nonneg : ∀ i j, 0 ≤ A i j) :
    0 < collatzWielandtFn A (fun _ ↦ 1) := by
  dsimp [collatzWielandtFn]; rw [dif_pos ⟨Classical.arbitrary n, by simp⟩]
  refine inf'_pos _ (fun i _ ↦ ?_)
  simp only [mulVec_apply, mul_one, div_one]
  refine sum_pos_of_nonneg_of_ne_zero (fun j _ ↦ hA_nonneg i j) (fun h_sum ↦ ?_)
  have h_zero : ∀ j, A i j = 0 := fun j ↦ (sum_eq_zero_iff_of_nonneg fun j _ ↦ hA_nonneg i j).mp h_sum j (mem_univ j)
  rcases Nat.eq_one_or_one_lt (Fintype.card n) Fintype.card_ne_zero with h1 | hgt
  · exact lt_irrefl 0 <| h_zero i ▸ irreducible_one_element_implies_diagonal_pos hA_irred h1 i
  · haveI : Nontrivial n := Fintype.one_lt_card_iff_nontrivial.1 hgt
    exact lt_irrefl 0 <| h_zero (hA_irred.exists_pos i).choose ▸ (hA_irred.exists_pos i).choose_spec


variable [DecidableEq n]

/-- The Perron root (the supremum of the Collatz-Wielandt function) is positive for an
    irreducible, non-negative matrix. This follows by showing the value for the vector of
    all ones is positive, and that value is a lower bound for the supremum. -/
lemma collatzWielandt_sup_is_pos (hA_irred : IsIrreducible A) (hA_nonneg : ∀ i j, 0 ≤ A i j) :
    0 < sSup (collatzWielandtFn A '' {x | (∀ i, 0 ≤ x i) ∧ x ≠ 0}) := by
  have h1 : (fun _ : n ↦ (1 : ℝ)) ∈ {x | (∀ i, 0 ≤ x i) ∧ x ≠ 0} :=
    ⟨fun _ ↦ zero_le_one, fun h ↦ one_ne_zero (congr_fun h (Classical.arbitrary n))⟩
  exact lt_of_lt_of_le (collatzWielandtFn_of_ones_is_pos hA_irred hA_nonneg) <|
    le_csSup (CollatzWielandt.bddAbove A hA_nonneg) (mem_image_of_mem _ h1)

/-- For a maximizer `v` of the Collatz-Wielandt function, `A * v = r • v`. -/
theorem maximizer_is_eigenvector (hA_prim : IsPrimitive A) (hA_nonneg : ∀ i j, 0 ≤ A i j) {v : n → ℝ}
    (hv_max : IsMaxOn (collatzWielandtFn A) (stdSimplex ℝ n) v) (hv_simplex : v ∈ stdSimplex ℝ n) (r : ℝ)
    (hr_def : r = collatzWielandtFn A v) : A *ᵥ v = r • v := by
  have hv_ne_zero : v ≠ 0 := fun h ↦ by simpa [h, stdSimplex] using hv_simplex.2
  have h_le : r • v ≤ A *ᵥ v := hr_def ▸ CollatzWielandt.le_mulVec hA_nonneg hv_simplex.1 hv_ne_zero
  by_contra h_ne
  let z := A *ᵥ v - r • v
  have hz_nonneg : ∀ i, 0 ≤ z i := fun i ↦ sub_nonneg.mpr (h_le i)
  obtain ⟨_, k, _, hk_pos⟩ := hA_prim
  let y := (A ^ k) *ᵥ v
  have hy_pos : ∀ i, 0 < y i := positive_mul_vec_of_nonneg_vec hk_pos hv_simplex.1 hv_ne_zero
  have h_Ay : ∀ i, r * y i < (A *ᵥ y) i := fun i ↦ calc
    r * y i < r * y i + ((A ^ k) *ᵥ z) i := lt_add_of_pos_right _
      (positive_mul_vec_of_nonneg_vec hk_pos hz_nonneg (by grind) i)
    _ = (A *ᵥ y) i := by simp [y, z, mulVec_sub, mulVec_smul, ← pow_succ', pow_succ, mulVec_mulVec]
  have h_r_lt : r < collatzWielandtFn A y := by
    rw [collatzWielandtFn, dif_pos ⟨Classical.arbitrary n, by simp [hy_pos]⟩]
    exact (Finset.lt_inf'_iff _).mpr fun i _ ↦ (lt_div_iff₀ (hy_pos i)).mpr (h_Ay i)
  let c := (∑ i, y i)⁻¹
  have hc_pos : 0 < c := inv_pos.mpr (sum_pos (fun i _ ↦ hy_pos i) univ_nonempty)
  have y_norm_simplex : c • y ∈ stdSimplex ℝ n :=
    ⟨fun i ↦ smul_nonneg hc_pos.le (hy_pos i).le, by
    simp [c, smul_eq_mul, ← Finset.mul_sum, inv_mul_cancel₀
    (ne_of_gt (sum_pos (fun i _ ↦ hy_pos i) univ_nonempty))]⟩
  have h_cw_eq : collatzWielandtFn A (c • y) = collatzWielandtFn A y :=
    CollatzWielandt.smul hc_pos hA_nonneg (fun i ↦ (hy_pos i).le)
    (fun h ↦ ne_of_gt (hy_pos (Classical.arbitrary n)) (by simp [h]))
  grind [hv_max y_norm_simplex]


/-- Short alias for `maximizer_is_eigenvector`. -/
theorem max_is_eig (hA_prim : IsPrimitive A)
      (hA_nonneg : ∀ i j, 0 ≤ A i j) {v : n → ℝ} (hv_max : IsMaxOn (collatzWielandtFn A) (stdSimplex ℝ n) v)
      (hv_simplex : v ∈ stdSimplex ℝ n) (r : ℝ) (hr_def : r = collatzWielandtFn A v) : A *ᵥ v = r • v :=
    maximizer_is_eigenvector hA_prim hA_nonneg hv_max hv_simplex r hr_def

/-- An eigenvector `v` of a primitive matrix `A` corresponding to a positive eigenvalue `r`
    must be strictly positive. -/
lemma eigenvector_of_primitive_is_positive {r : ℝ} (hA_prim : IsPrimitive A) (hr_pos : 0 < r)
    {v : n → ℝ} (h_eigen : A *ᵥ v = r • v) (hv_nonneg : ∀ i, 0 ≤ v i) (hv_ne_zero : v ≠ 0) :
    ∀ i, 0 < v i := by
  obtain ⟨_, k, _, hk_pos⟩ := hA_prim
  have h_gen : ∀ m, (A ^ m) *ᵥ v = (r ^ m) • v := by
    intro m; induction m with | zero => simp | succ m ih =>
      rw [@pow_mulVec_succ, ih, mulVec_smul, h_eigen, smul_smul, pow_succ]
  intro i
  have h_pos := positive_mul_vec_of_nonneg_vec hk_pos hv_nonneg hv_ne_zero i
  exact (mul_pos_iff_of_pos_left (pow_pos hr_pos k)).mp (by aesop)


/-- The Perron root `r = collatzWielandtFn A v` is positive. -/
lemma perron_root_pos_of_primitive (hA_prim : IsPrimitive A) (hA_nonneg : ∀ i j, 0 ≤ A i j)
    {v : n → ℝ} (_ : v ∈ stdSimplex ℝ n) (hvM : IsMaxOn (collatzWielandtFn A) (stdSimplex ℝ n) v) :
    0 < collatzWielandtFn A v := by
  let c : ℝ := (Fintype.card n : ℝ)⁻¹
  have hc : 0 < c := inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)
  let ones : n → ℝ := fun _ ↦ 1
  have h_ones_simp : c • ones ∈ stdSimplex ℝ n :=
    ⟨fun _ ↦ smul_nonneg hc.le zero_le_one, by aesop⟩
  have cw_scale : collatzWielandtFn A (c • ones) = collatzWielandtFn A ones :=
    CollatzWielandt.smul hc hA_nonneg (fun _ ↦ zero_le_one)
    (fun h ↦ one_ne_zero (congr_fun h (Classical.arbitrary n)))
  calc 0 < collatzWielandtFn A ones := collatzWielandtFn_of_ones_is_pos hA_prim.isIrreducible hA_nonneg
    _ = collatzWielandtFn A (c • ones) := cw_scale.symm
    _ ≤ collatzWielandtFn A v := hvM h_ones_simp

open Matrix.CollatzWielandt

/-- **Perron-Frobenius theorem for primitive matrices - Existence part**-/
theorem exists_positive_eigenvector_of_primitive
  (hA_prim : IsPrimitive A) (hA_nonneg : ∀ i j, 0 ≤ A i j) :
  ∃ (r : ℝ) (v : n → ℝ), r > 0 ∧ (∀ i, v i > 0) ∧ A *ᵥ v = r • v := by
  haveI : Nonempty (stdSimplex ℝ n) := ⟨fun _ ↦ (Fintype.card n : ℝ)⁻¹,
    fun _ ↦ inv_nonneg.mpr (Nat.cast_nonneg _), by aesop⟩
  obtain ⟨v, hvS, hvM⟩ := CollatzWielandt.exists_maximizer (A := A)
  have hr := perron_root_pos_of_primitive hA_prim hA_nonneg hvS hvM
  have heig := maximizer_is_eigenvector hA_prim hA_nonneg hvM hvS _ rfl
  refine ⟨_, v, hr, eigenvector_of_primitive_is_positive hA_prim hr heig hvS.1
    (fun h ↦ by simpa [h] using hvS.2), heig⟩

end PerronFrobenius
end Matrix
