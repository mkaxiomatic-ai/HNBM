import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecificLimits.Basic

open Set Filter Topology

namespace IsCompact

variable {α : Type*} [TopologicalSpace α] --[Nonempty α]
variable {f : α → ℝ} {K : Set α}

section GeneralProof
-- This section provides proofs that do not rely on first-countability.

lemma upperSemicontinuousOn_iff_upperSemicontinuous {s : Set α} :
  UpperSemicontinuousOn f s ↔ UpperSemicontinuous (s.restrict f) := by
  refine ⟨fun h x c hc ↦ by
  rw [nhds_subtype_eq_comap_nhdsWithin s x]
  exact h x x.prop c hc |>.comap Subtype.val,
  fun h x hx c hc ↦ by
    rw [nhdsWithin_eq_map_subtype_coe]
    exact h ⟨x, hx⟩ c hc⟩

/--
**Boundedness Theorem (General Version)**: An upper semicontinuous function on a compact set
is bounded above.

This proof uses the open cover definition of compactness and does not require the space
to be first-countable.
-/
theorem bddAbove_image_of_upperSemicontinuousOn (hK : IsCompact K)
    (hf : UpperSemicontinuousOn f K) : BddAbove (f '' K) := by
  -- We proceed by contradiction. Assume the image `f '' K` is not bounded above.
  by_contra h_unbdd
  -- We work on the space `K` with the subspace topology.
  -- The hypothesis `IsCompact K` is equivalent to `K` being a compact space.
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  -- Define a family of sets `U n = {x : K | f(x) < n}`.
  let U : ℕ → Set K := fun n => {x : K | f x < n}
  -- By upper semicontinuity, each `U n` is an open set in the subspace topology of K.
  have hU_open : ∀ n, IsOpen (U n) := by
    intro n
    have hf_restrict : UpperSemicontinuous (K.restrict f) := (upperSemicontinuousOn_iff_upperSemicontinuous).mp hf
    rw [upperSemicontinuous_iff_isOpen_preimage] at hf_restrict
    convert hf_restrict n
  -- If `f` is unbounded on `K`, then the collection `{U n}` covers `K` (i.e., `univ` in `Set K`).
  have hU_covers_univ : (univ : Set K) ⊆ ⋃ n, U n := fun x _ ↦ by
    rcases exists_nat_gt (f x) with ⟨n, hn⟩
    exact mem_iUnion.2 ⟨n, hn⟩
  -- Since K is a compact space, its `univ` set is compact. The open cover `{U n}`
  -- must have a finite subcover.
  rcases isCompact_univ.elim_finite_subcover U hU_open hU_covers_univ with ⟨s, hs_cover⟩
  -- Let N be the maximum of the natural numbers in the finite index set `s`.
  -- As `s` is a finite nonempty set of natural numbers, it has a maximum.
  have s_nonempty : s.Nonempty := by
    rcases K.eq_empty_or_nonempty with rfl | hK_nonempty
    · exfalso; simp at h_unbdd
    · by_contra hs_empty
      rw [Finset.not_nonempty_iff_eq_empty.mp hs_empty] at hs_cover
      aesop
  let N := s.sup id
  -- The union of the finite subcover is a subset of U (N + 1).
  have h_union_sub_UN : (⋃ i ∈ s, U i) ⊆ U (N + 1) := by
    intro x hx_union
    simp only [mem_iUnion] at hx_union ⊢
    rcases hx_union with ⟨i, hi_s, hf_lt_i⟩
    -- If f(x) < i and i ≤ N, then f(x) < N + 1.
    have hi_le_N : i ≤ N := Finset.le_sup hi_s (f := id)
    have hi_le_N_real : (i : ℝ) ≤ (N : ℝ) := by norm_cast
    exact hf_lt_i.trans (lt_of_le_of_lt hi_le_N_real (by aesop))
  -- This implies that for all `x` in `K`, `f x < N + 1`.
  have h_all_lt : ∀ (x : K), f x < N + 1 := by
    intro x
    -- `x` belongs to the union of the finite sub-cover
    have x_in_union : x ∈ ⋃ i ∈ s, U i := hs_cover (mem_univ x)
    -- therefore it belongs to `U (N + 1)`
    have hx : x ∈ U (N + 1) := h_union_sub_UN x_in_union
    simpa [U] using hx
  -- This means that f is bounded above by N+1 on K.
  have h_bdd_final : BddAbove (f '' K) := by
    use (N : ℝ) + 1
    intro y hy_img
    rcases hy_img with ⟨x, hx_K, rfl⟩
    exact (h_all_lt ⟨x, hx_K⟩).le
  exact h_unbdd h_bdd_final

lemma tendsto_const_sub_inv_add_one_atTop (c : ℝ) :
    Tendsto (fun n : ℕ => c - 1 / (n + 1)) atTop (𝓝 c) := by
  have h_inv : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  simpa using tendsto_const_nhds.sub (h_inv)

/--
**Extreme Value Theorem (General Version)**: An upper semicontinuous function on a non-empty
compact set attains its supremum.
-/
theorem exists_isMaxOn_of_upperSemicontinuousOn (hK : IsCompact K) (hK_nonempty : K.Nonempty)
    (hf : UpperSemicontinuousOn f K) : ∃ x₀ ∈ K, IsMaxOn f K x₀ := by
  -- The function is bounded above on K.
  have h_bdd_above : BddAbove (f '' K) := bddAbove_image_of_upperSemicontinuousOn hK hf
  let s := sSup (f '' K)
  -- We work in the compact space `K`.
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  -- Consider the sets Cₙ = {x ∈ K | s - 1/(n+1) ≤ f(x)}.
  let C : ℕ → Set K := fun n => {x : K | s - 1 / (n + 1 : ℝ) ≤ f x}
  -- These sets are closed in the compact space K.
  have hC_closed : ∀ n, IsClosed (C n) := by
    intro n
    have : C n = K.restrict f ⁻¹' Ici (s - 1 / (n + 1 : ℝ)) := by ext x; simp [C]
    rw [this]
    exact (upperSemicontinuousOn_iff_upperSemicontinuous.mp hf).isClosed_preimage (s - 1 / (n + 1 : ℝ))
  have hC_compact : ∀ n, IsCompact (C n) := fun n => (hC_closed n).isCompact
  -- The family `C n` is decreasing, hence it is directed by `⊇`.
  have hC_directed : Directed (· ⊇ ·) C := by
    intro n m
    refine ⟨max n m, ?_, ?_⟩
    · -- `C (max n m) ⊆ C n`
      intro x hx
      -- `hx` is the inequality for the bigger threshold
      have hx_le : s - 1 / ((max n m : ℝ) + 1) ≤ f x := by
        simpa [C] using hx
      have h_thresh : s - 1 / ((n : ℝ) + 1) ≤ s - 1 / ((max n m : ℝ) + 1) := by
        have h_inv : (1 / ((max n m : ℝ) + 1)) ≤ 1 / ((n : ℝ) + 1) := by
          gcongr; norm_cast; exact le_max_left n m
        simpa using (sub_le_sub_left h_inv s)
      have : s - 1 / ((n : ℝ) + 1) ≤ f x := le_trans h_thresh hx_le
      simpa [C] using this
    · -- `C (max n m) ⊆ C m`
      intro x hx
      have hx_le : s - 1 / ((max n m : ℝ) + 1) ≤ f x := by
        simpa [C] using hx
      have h_thresh : s - 1 / ((m : ℝ) + 1) ≤ s - 1 / ((max n m : ℝ) + 1) := by
        have h_inv : (1 / ((max n m : ℝ) + 1)) ≤ 1 / ((m : ℝ) + 1) := by
          gcongr; norm_cast; exact le_max_right n m
        simpa using (sub_le_sub_left h_inv s)
      have : s - 1 / ((m : ℝ) + 1) ≤ f x := le_trans h_thresh hx_le
      simpa [C] using this
  -- Non-emptiness of each `C n`.
  have hC_nonempty : ∀ n, (C n).Nonempty := fun n =>
    let ⟨_, ⟨x, hx, rfl⟩, h⟩ := exists_lt_of_lt_csSup (hK_nonempty.image f)
      (sub_lt_self s (one_div_pos.mpr (Nat.cast_add_one_pos n)))
    ⟨⟨x, hx⟩, le_of_lt h⟩
  -- Cantor's intersection theorem gives a point in ⋂ `C n`.
  have h_nonempty_inter : (⋂ n, C n).Nonempty :=
    IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      (t := C) hC_directed hC_nonempty hC_compact hC_closed
  -- Any point in this intersection is a point where the maximum is attained.
  rcases h_nonempty_inter with ⟨x₀, hx₀_inter⟩
  use x₀.val, x₀.prop
  -- We show `f x₀ = s`. Since `s` is the supremum, this proves `x₀` is a maximum.
  have h_fx_eq_s : f x₀ = s := by
    simp only [mem_iInter] at hx₀_inter
    have h_le : f x₀ ≤ s := le_csSup h_bdd_above (mem_image_of_mem f x₀.prop)
    have h_ge : s ≤ f x₀ :=
      le_of_tendsto (tendsto_const_sub_inv_add_one_atTop s) (Filter.Eventually.of_forall (fun n => hx₀_inter n))
    exact le_antisymm h_le h_ge
  -- This implies `IsMaxOn`.
  intro y hy
  rw [h_fx_eq_s]
  exact le_csSup h_bdd_above (mem_image_of_mem f hy)

-- shorter aliases for latex formatting

/- Short aliases for long names (backwards‑compatible) -/
-- upperSemicontinuousOn_iff_upperSemicontinuous
lemma usco_on_iff_usco {s : Set α} :
  UpperSemicontinuousOn f s ↔ UpperSemicontinuous (s.restrict f) :=
  upperSemicontinuousOn_iff_upperSemicontinuous

-- bddAbove_image_of_upperSemicontinuousOn
theorem bdd_above_image_usco_on (hK : IsCompact K)
    (hf : UpperSemicontinuousOn f K) : BddAbove (f '' K) :=
  bddAbove_image_of_upperSemicontinuousOn hK hf

-- tendsto_const_sub_inv_add_one_atTop
lemma tendsto_sub_inv_atTop (c : ℝ) :
  Tendsto (fun n : ℕ => c - 1 / (n + 1)) atTop (𝓝 c) :=
  tendsto_const_sub_inv_add_one_atTop c

-- exists_isMaxOn_of_upperSemicontinuousOn
theorem exists_max_on_usco (hK : IsCompact K) (hK_nonempty : K.Nonempty)
    (hf : UpperSemicontinuousOn f K) : ∃ x₀ ∈ K, IsMaxOn f K x₀ :=
  exists_isMaxOn_of_upperSemicontinuousOn hK hK_nonempty hf

end GeneralProof
end IsCompact
