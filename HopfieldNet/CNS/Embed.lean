/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.QUBO.Refine
import HopfieldNet.CNS.NetValid
import HopfieldNet.CNS.Sound

/-!
# The reduced objective is the paper's objective

§IV of the paper deletes the columns of `A` belonging to variables Algorithm 1 fixed, and
redefines the penalty over the survivors. `Problem.penaltyDoubled` implements the redefined one
and is what the dynamics descend; `CNS.penaltyDoubled` is the original `‖Ax − e‖²` that
`CNS.Sound` proves is Sudoku. This module proves they agree:

  `Problem.penaltyDoubled P x = CNS.penaltyDoubled (P.embed R.fixedVal x)`.

Until now that identity was only checked at run time (`cns reduced`, 200 random vectors per
instance). With it proved, the chain closes: minimising what the search minimises is solving the
puzzle, by `CNS.Sound.penalty_zero_iff_families` and `CNS.GridSound`.

## The one piece of real content

Everything reduces to the fact that `A` read by rows agrees with `A` read by columns:

  `v ∈ varsOfRowSpec r  ↔  r ∈ rowsOfVar v`.

`varsOfRowSpec` enumerates the four constraint families directly (`CNS.Sound` reasons with it);
`rowsOfVar` names the four rows a variable occupies (the dynamics use it, because it is what
makes the net input `O(nvars)`). They are the same incidence relation read along the two axes,
and `cns encoding` has always checked it numerically as `specMatchesTable`. The proof is the
band argument again: the four families live in disjoint index ranges, so a row index determines
which family it belongs to, and within a family the coordinates match by `omega`.
-/

namespace CNS

open QUBO
open QUBO.Problem

open Finset

-- `numVars = 729` and `numRows = 324` are `def`s; unification occasionally tries to evaluate
-- `List.range` at them.
set_option maxRecDepth 8000

/-! ## Coordinates of a variable -/

/-- A variable index splits into its cell coordinates and digit. -/
theorem varIdx_decomp {v : Nat} (hv : v < numVars) :
    varIdx (v / (n * n)) (v % (n * n) / n) (v % n) = v := by
  simp only [varIdx, numVars, n] at *
  omega

/-- The coordinates of a variable are in range. -/
theorem coords_lt {v : Nat} (hv : v < numVars) :
    v / (n * n) < n ∧ v % (n * n) / n < n ∧ v % n < n := by
  simp only [numVars, n] at *
  refine ⟨by omega, by omega, by omega⟩

/-- `varIdx` is injective on legal coordinates: reading the coordinates back is the identity. -/
theorem varIdx_coords {i j k : Nat} (hi : i < n) (hj : j < n) (hk : k < n) :
    varIdx i j k / (n * n) = i ∧ varIdx i j k % (n * n) / n = j ∧ varIdx i j k % n = k := by
  simp only [varIdx, n] at *
  refine ⟨by omega, by omega, by omega⟩

/-! ## Membership in the four families -/

theorem mem_cellVars {v i j : Nat} : v ∈ cellVars i j ↔ ∃ k, k < n ∧ varIdx i j k = v := by
  unfold cellVars; simp [List.mem_map, List.mem_range]

theorem mem_colVars {v j k : Nat} : v ∈ colVars j k ↔ ∃ i, i < n ∧ varIdx i j k = v := by
  unfold colVars; simp [List.mem_map, List.mem_range]

theorem mem_rowVars {v i k : Nat} : v ∈ rowVars i k ↔ ∃ j, j < n ∧ varIdx i j k = v := by
  unfold rowVars; simp [List.mem_map, List.mem_range]

theorem mem_boxVars {v b k : Nat} :
    v ∈ boxVars b k ↔ ∃ t, t < n ∧
      varIdx ((b / blk) * blk + t / blk) ((b % blk) * blk + t % blk) k = v := by
  unfold boxVars; simp [List.mem_map, List.mem_range]

/-- `varIdx` is injective on legal coordinates. -/
theorem varIdx_inj {a b c i j k : Nat} (ha : a < n) (hb : b < n) (hc : c < n)
    (hi : i < n) (hj : j < n) (hk : k < n) (h : varIdx a b c = varIdx i j k) :
    a = i ∧ b = j ∧ c = k := by
  simp only [varIdx, n] at *
  omega

/-! ## The duality -/

/-- `boxOf` at a cell, in coordinates. -/
private theorem boxOf_cellIdx {i j : Nat} (hi : i < n) (hj : j < n) :
    boxOf (cellIdx i j) = (i / blk) * blk + j / blk := by
  simp only [boxOf, rowOf, colOf, cellIdx, blk, n] at *
  omega

/-- `rowsOfVar` at a variable given by its coordinates. -/
private theorem rowsOfVar_varIdx {i j k : Nat} (hi : i < n) (hj : j < n) (hk : k < n) :
    rowsOfVar (varIdx i j k)
      = #[rowCell i j, rowCol j k, rowRow i k, rowBox ((i / blk) * blk + j / blk) k] := by
  obtain ⟨e1, e2, e3⟩ := varIdx_coords hi hj hk
  simp only [rowsOfVar]
  rw [e1, e2, e3, boxOf_cellIdx hi hj]

/-- Membership in `rowsOfVar`, in coordinates and numerals. -/
private theorem mem_rowsOfVar_varIdx {i j k r : Nat} (hi : i < n) (hj : j < n) (hk : k < n) :
    (rowsOfVar (varIdx i j k)).contains r ↔
      r = i * n + j ∨ r = n * n + j * n + k ∨ r = 2 * n * n + i * n + k ∨
      r = 3 * n * n + ((i / blk) * blk + j / blk) * n + k := by
  rw [Array.contains_iff_mem, rowsOfVar_varIdx hi hj hk]
  simp only [rowCell, rowCol, rowRow, rowBox, cellIdx]
  simp

/-- **`A` read by rows agrees with `A` read by columns.**

The two enumerations of the incidence structure — `varsOfRowSpec`, which lists the variables of
a constraint, and `rowsOfVar`, which lists the constraints of a variable — describe the same
relation. `cns encoding` checks this numerically as `specMatchesTable`; here it is a theorem. -/
theorem mem_varsOfRowSpec_iff_coords {i j k r : Nat} (hi : i < n) (hj : j < n) (hk : k < n)
    (hr : r < numRows) :
    varIdx i j k ∈ varsOfRowSpec r ↔ (rowsOfVar (varIdx i j k)).contains r := by
  rw [mem_rowsOfVar_varIdx hi hj hk]
  unfold varsOfRowSpec
  rcases Nat.lt_or_ge r (n * n) with h1 | h1
  · -- cell constraints
    rw [if_pos h1, mem_cellVars]
    constructor
    · rintro ⟨k', hk', hvk'⟩
      obtain ⟨e1, e2, e3⟩ := varIdx_inj
        (show r / n < n by simp only [numRows, n] at *; omega)
        (show r % n < n by simp only [numRows, n] at *; omega) hk' hi hj hk hvk'
      left; simp only [numRows, n] at *; omega
    · rintro (he | he | he | he)
      · refine ⟨k, hk, ?_⟩
        have h2 : r / n = i ∧ r % n = j := by simp only [numRows, n] at *; omega
        rw [h2.1, h2.2]
      all_goals (exfalso; simp only [numRows, blk, n] at *; omega)
  · rw [if_neg (by omega)]
    rcases Nat.lt_or_ge r (2 * (n * n)) with h2 | h2
    · -- column constraints
      rw [if_pos (by simp only [numRows, n] at *; omega), mem_colVars]
      constructor
      · rintro ⟨i', hi', hvi'⟩
        obtain ⟨e1, e2, e3⟩ := varIdx_inj hi'
          (show (r - n * n) / n < n by simp only [numRows, n] at *; omega)
          (show (r - n * n) % n < n by simp only [numRows, n] at *; omega) hi hj hk hvi'
        right; left; simp only [numRows, n] at *; omega
      · rintro (he | he | he | he)
        · exfalso; simp only [numRows, n] at *; omega
        · refine ⟨i, hi, ?_⟩
          have h3 : (r - n * n) / n = j ∧ (r - n * n) % n = k := by simp only [numRows, n] at *; omega
          rw [h3.1, h3.2]
        all_goals (exfalso; simp only [numRows, blk, n] at *; omega)
    · rw [if_neg (by simp only [numRows, n] at *; omega)]
      rcases Nat.lt_or_ge r (3 * (n * n)) with h3 | h3
      · -- row constraints
        rw [if_pos (by simp only [numRows, n] at *; omega), mem_rowVars]
        constructor
        · rintro ⟨j', hj', hvj'⟩
          obtain ⟨e1, e2, e3⟩ := varIdx_inj
            (show (r - 2 * n * n) / n < n by simp only [numRows, n] at *; omega) hj'
            (show (r - 2 * n * n) % n < n by simp only [numRows, n] at *; omega) hi hj hk hvj'
          right; right; left; simp only [numRows, n] at *; omega
        · rintro (he | he | he | he)
          · exfalso; simp only [numRows, n] at *; omega
          · exfalso; simp only [numRows, n] at *; omega
          · refine ⟨j, hj, ?_⟩
            have h4 : (r - 2 * n * n) / n = i ∧ (r - 2 * n * n) % n = k := by
              simp only [numRows, n] at *; omega
            rw [h4.1, h4.2]
          · exfalso; simp only [numRows, blk, n] at *; omega
      · -- block constraints
        rw [if_neg (by simp only [numRows, n] at *; omega), mem_boxVars]
        constructor
        · rintro ⟨t, ht, hvt⟩
          obtain ⟨e1, e2, e3⟩ := varIdx_inj
            (show (r - 3 * n * n) / n / blk * blk + t / blk < n by simp only [numRows, blk, n] at *; omega)
            (show (r - 3 * n * n) / n % blk * blk + t % blk < n by simp only [numRows, blk, n] at *; omega)
            (show (r - 3 * n * n) % n < n by simp only [numRows, n] at *; omega) hi hj hk hvt
          right; right; right
          simp only [numRows, blk, n] at *
          omega
        · rintro (he | he | he | he)
          · exfalso; simp only [numRows, blk, n] at *; omega
          · exfalso; simp only [numRows, blk, n] at *; omega
          · exfalso; simp only [numRows, blk, n] at *; omega
          · refine ⟨blk * (i % blk) + j % blk, by simp only [numRows, blk, n] at *; omega, ?_⟩
            have h5 : (r - 3 * n * n) / n = (i / blk) * blk + j / blk
                ∧ (r - 3 * n * n) % n = k := by simp only [numRows, blk, n] at *; omega
            rw [h5.1, h5.2]
            congr 1 <;> (simp only [numRows, blk, n] at *; omega)

/-- The duality, at an arbitrary variable index. -/
theorem mem_varsOfRowSpec_iff {v r : Nat} (hv : v < numVars) (hr : r < numRows) :
    v ∈ varsOfRowSpec r ↔ (rowsOfVar v).contains r := by
  obtain ⟨hi, hj, hk⟩ := coords_lt hv
  have h := mem_varsOfRowSpec_iff_coords hi hj hk hr
  rwa [varIdx_decomp hv] at h

/-! ## `varsOfRowSpec` is a duplicate-free list of legal variables -/

theorem varIdx_lt {i j k : Nat} (hi : i < n) (hj : j < n) (hk : k < n) :
    varIdx i j k < numVars := by
  simp only [varIdx, numVars, n] at *
  omega

/-- Every variable of a constraint row is a legal index. -/
theorem varsOfRowSpec_lt {r : Nat} (hr : r < numRows) : ∀ v ∈ varsOfRowSpec r, v < numVars := by
  intro v hv
  unfold varsOfRowSpec at hv
  split at hv
  · rw [mem_cellVars] at hv
    obtain ⟨k, hk, rfl⟩ := hv
    exact varIdx_lt (by simp only [n] at *; omega) (by simp only [n] at *; omega) hk
  · split at hv
    · rw [mem_colVars] at hv
      obtain ⟨i, hi, rfl⟩ := hv
      exact varIdx_lt hi (by simp only [n] at *; omega) (by simp only [n] at *; omega)
    · split at hv
      · rw [mem_rowVars] at hv
        obtain ⟨j, hj, rfl⟩ := hv
        exact varIdx_lt (by simp only [n] at *; omega) hj (by simp only [n] at *; omega)
      · rw [mem_boxVars] at hv
        obtain ⟨t, ht, rfl⟩ := hv
        -- the block coordinate needs `r < numRows`: it bounds the block number below `n`
        exact varIdx_lt (by simp only [numRows, blk, n] at *; omega)
          (by simp only [numRows, blk, n] at *; omega)
          (by simp only [numRows, n] at *; omega)

/-- Injectivity of the block family's index map: the shared coordinates cancel and the
surviving digit sits below the next place value, so no bound on `B`, `K` is needed. -/
private theorem boxVars_inj {B K a b : Nat}
    (h : varIdx ((B / blk) * blk + a / blk) ((B % blk) * blk + a % blk) K
       = varIdx ((B / blk) * blk + b / blk) ((B % blk) * blk + b % blk) K) : a = b := by
  simp only [varIdx, blk, n] at h
  omega

/-- The same for the cell family. -/
private theorem cellVars_inj {i j a b : Nat} (h : varIdx i j a = varIdx i j b) : a = b := by
  simp only [varIdx, n] at h; omega

/-- The same for the column family. -/
private theorem colVars_inj {j k a b : Nat} (h : varIdx a j k = varIdx b j k) : a = b := by
  simp only [varIdx, n] at h; omega

/-- The same for the row family. -/
private theorem rowVars_inj {i k a b : Nat} (h : varIdx i a k = varIdx i b k) : a = b := by
  simp only [varIdx, n] at h; omega

/-- A constraint row lists nine *distinct* variables. -/
theorem varsOfRowSpec_nodup (r : Nat) : (varsOfRowSpec r).Nodup := by
  have key : ∀ (f : Nat → Nat), (∀ a, a < n → ∀ b, b < n → f a = f b → a = b) →
      ((List.range n).map f).Nodup := by
    intro f hinj
    exact List.Nodup.map_on
      (fun a ha b hb h => hinj a (List.mem_range.mp ha) b (List.mem_range.mp hb) h)
      List.nodup_range
  unfold varsOfRowSpec
  split
  · exact key _ fun _ _ _ _ h => cellVars_inj h
  · split
    · exact key _ fun _ _ _ _ h => colVars_inj h
    · split
      · exact key _ fun _ _ _ _ h => rowVars_inj h
      · exact key _ fun _ _ _ _ h => boxVars_inj h

/-! ## Counting over a row versus counting over all variables -/

/-- `countOn` is `List.countP`, in `Int`. -/
theorem countOn_foldl (y : Array Bool) : ∀ (l : List Nat) (acc : Int),
    l.foldl (fun a v => if y.getD v false then a + 1 else a) acc
      = acc + (l.countP fun v => y.getD v false : Int) := by
  intro l
  induction l with
  | nil => intro acc; simp
  | cons v t ih =>
    intro acc
    rw [List.foldl_cons, List.countP_cons, ih]
    by_cases h : y.getD v false = true <;> simp only [h, if_true, if_false, Bool.false_eq_true] <;>
      push_cast <;> ring

/-- **Counting over a constraint row is counting over all variables against the row indicator.**

This is where the duality does its work: the nine variables `varsOfRowSpec r` lists are exactly
those whose `rowsOfVar` contains `r`. -/
theorem countOn_varsOfRowSpec (y : Array Bool) {r : Nat} (hr : r < numRows) :
    countOn y (varsOfRowSpec r)
      = ((List.range numVars).countP
          fun v => y.getD v false && (rowsOfVar v).contains r : Int) := by
  unfold countOn
  rw [countOn_foldl y (varsOfRowSpec r) 0, zero_add]
  congr 1
  rw [List.countP_eq_length_filter, List.countP_eq_length_filter]
  have hnd1 : ((varsOfRowSpec r).filter fun v => y.getD v false).Nodup :=
    List.Nodup.filter _ (varsOfRowSpec_nodup r)
  have hnd2 : ((List.range numVars).filter
      fun v => y.getD v false && (rowsOfVar v).contains r).Nodup :=
    List.Nodup.filter _ List.nodup_range
  rw [← List.toFinset_card_of_nodup hnd1, ← List.toFinset_card_of_nodup hnd2]
  congr 1
  ext a
  simp only [List.mem_toFinset, List.mem_filter, List.mem_range, Bool.and_eq_true]
  constructor
  · rintro ⟨hmem, hy⟩
    have ha := varsOfRowSpec_lt hr a hmem
    exact ⟨ha, hy, (mem_varsOfRowSpec_iff ha hr).mp hmem⟩
  · rintro ⟨ha, hy, hc⟩
    exact ⟨(mem_varsOfRowSpec_iff ha hr).mpr hc, hy⟩

/-- Counting over a list is counting over its index range. -/
theorem countP_range_length {α : Type*} (p : α → Bool) (d : α) : ∀ (l : List α),
    (List.range l.length).countP (fun i => p (l.getD i d)) = l.countP p := by
  intro l
  induction l with
  | nil => simp
  | cons x t ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.countP_cons, List.countP_map,
      List.countP_cons]
    simp only [Function.comp_def, List.getD_cons_succ, List.getD_cons_zero, ih]

/-- Splitting a count on an auxiliary predicate. -/
theorem countP_split {α : Type*} (p q : α → Bool) : ∀ (l : List α),
    l.countP p = l.countP (fun v => p v && q v) + l.countP (fun v => p v && !q v) := by
  intro l
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.countP_cons, List.countP_cons, List.countP_cons, ih]
    cases hp : p a <;> cases hq : q a <;> simp [hp, hq] <;> omega

/-- Reading an array is reading its list. -/
theorem Array.getD_toList {α : Type*} (a : Array α) (i : Nat) (d : α) :
    a.toList.getD i d = a.getD i d := by
  rw [List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?]
  by_cases h : i < a.size
  · rw [List.getElem?_eq_getElem (by simpa using h), Array.getElem?_eq_getElem h]; simp
  · rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_lt h),
      Array.getElem?_eq_none (Nat.le_of_not_lt h)]

/-- Counting respects pointwise equality of predicates on the list's members. -/
theorem countP_congr {α : Type*} {p q : α → Bool} : ∀ (l : List α),
    (∀ v ∈ l, p v = q v) → l.countP p = l.countP q := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a t ih =>
    intro h
    rw [List.countP_cons, List.countP_cons, h a (List.mem_cons_self ..),
      ih (fun v hv => h v (List.mem_cons_of_mem _ hv))]

/-- Folds of additions agree when the summands do. -/
theorem foldl_add_congr {f g : Nat → Int} : ∀ (l : List Nat), (∀ r ∈ l, f r = g r) →
    ∀ acc, l.foldl (fun a r => a + f r) acc = l.foldl (fun a r => a + g r) acc := by
  intro l
  induction l with
  | nil => intro _ acc; rfl
  | cons r t ih =>
    intro h acc
    rw [List.foldl_cons, List.foldl_cons, h r (List.mem_cons_self ..),
      ih (fun v hv => h v (List.mem_cons_of_mem _ hv))]

namespace Problem

/-! ## The reduced index -/

theorem redIndex_some {P : Problem} {v u : Nat} (h : P.redIndex v = some u) :
    u < P.nvars ∧ P.varOf.getD u 0 = v := by
  unfold redIndex at h
  exact ⟨List.mem_range.mp (List.mem_of_find?_eq_some h),
    by simpa using List.find?_some h⟩

theorem redIndex_none {P : Problem} {v : Nat} (h : P.redIndex v = none) :
    ∀ u < P.nvars, P.varOf.getD u 0 ≠ v := by
  intro u hu
  unfold redIndex at h
  have := (List.find?_eq_none.mp h) u (List.mem_range.mpr hu)
  simpa using this

/-- With `varOf` injective, the lookup inverts it. -/
theorem redIndex_varOf {P : Problem} (hV : P.Valid) {u : Nat} (hu : u < P.nvars) :
    P.redIndex (P.varOf.getD u 0) = some u := by
  cases h : P.redIndex (P.varOf.getD u 0) with
  | none => exact absurd rfl (redIndex_none h u hu)
  | some u' =>
    obtain ⟨hu', hval⟩ := redIndex_some h
    rw [hV.varOf_inj u' hu' u hu hval]

/-- A variable has a reduced index exactly when it survived. -/
theorem redIndex_isSome (R : Reduced) {v : Nat} (hv : v < numVars) :
    ((ofReduced R).redIndex v).isSome = !(R.isFixed.getD v false) := by
  have hvarOf : (ofReduced R).varOf = survivors R := by simp only [ofReduced]
  have hnv : (ofReduced R).nvars = (survivors R).size := by simp only [ofReduced]
  have hmem : (∃ u, u < (ofReduced R).nvars ∧ (ofReduced R).varOf.getD u 0 = v)
      ↔ v ∈ survivors R := by
    rw [hvarOf, hnv]
    constructor
    · rintro ⟨u, hu, rfl⟩
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hu]
      exact Array.getElem_mem hu
    · intro hm
      obtain ⟨u, hu, he⟩ := Array.getElem_of_mem hm
      exact ⟨u, hu, by rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hu]; exact he⟩
  have hsurv : v ∈ survivors R ↔ !(R.isFixed.getD v false) = true := by
    unfold survivors
    rw [Array.mem_toArray, List.mem_filter, List.mem_range]
    simp only [Bool.not_eq_true', decide_eq_false_iff_not, Bool.not_eq_true]
    exact ⟨fun h => h.2, fun h => ⟨hv, h⟩⟩
  cases h : (ofReduced R).redIndex v with
  | some u =>
    obtain ⟨hu, hval⟩ := redIndex_some h
    simpa using (hsurv.mp (hmem.mp ⟨u, hu, hval⟩))
  | none =>
    have : ¬ (∃ u, u < (ofReduced R).nvars ∧ (ofReduced R).varOf.getD u 0 = v) := by
      rintro ⟨u, hu, hval⟩; exact redIndex_none h u hu hval
    simp only [Option.isSome_none, Bool.false_eq]
    rw [Bool.not_eq_false']
    by_contra hc
    exact this (hmem.mpr (hsurv.mpr (by simpa using hc)))

/-! ## Reading the embedding -/

theorem embed_getD (P : Problem) (s x : Array Bool) {v : Nat} (hv : v < numVars) :
    (P.embed s x).getD v false
      = match P.redIndex v with
        | some u => x.getD u false
        | none   => s.getD v false := by
  show ((Array.range numVars).map _).getD v false = _
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa using hv)]
  simp only [Array.getElem_map, Array.getElem_range]
  rfl

/-! ## The bridge -/

/-- The pinned-to-one flags, read off. -/
theorem pinnedOnes_getD (R : Reduced) {v : Nat} (hv : v < numVars) :
    (pinnedOnes R).getD v false = (R.isFixed.getD v false && R.fixedVal.getD v false) := by
  show ((Array.range numVars).map _).getD v false = _
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa using hv)]
  simp only [Array.getElem_map, Array.getElem_range]
  rfl

/-- `b̂` read off at a row. -/
theorem bhat_getD (R : Reduced) {r : Nat} (hr : r < numRows) :
    (ofReduced R).bhat.getD r 0 = bhatRow (pinnedOnes R) r := by
  show (bhatOf R).getD r 0 = _
  unfold bhatOf
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa using hr)]
  simp only [Array.getElem_map, Array.getElem_range]
  rfl

/-- **The row count of the embedded vector is the reduced row sum plus the pinned contribution.**

`(A · embed x̂)_r = (Â x̂)_r + (A_F s)_r`, and `b̂_r = 1 − (A_F s)_r` by construction, so the
residual `(A · embed x̂ − e)_r` is exactly the reduced residual `(Â x̂ − b̂)_r`. -/
theorem rowCount_embed (R : Reduced) (x : Array Bool) {r : Nat} (hr : r < numRows) :
    rowCount ((ofReduced R).embed R.fixedVal x) r
      = ((ofReduced R).rowSums x).getD r 0 + (1 - (ofReduced R).bhat.getD r 0) := by
  have hV : (ofReduced R).Valid := ofReduced_valid R
  set P := ofReduced R with hP
  set y := P.embed R.fixedVal x with hy
  set p : Nat → Bool := fun v =>
    (match P.redIndex v with | some u => x.getD u false | none => false)
      && (rowsOfVar v).contains r with hp
  -- the free part is the reduced row sum
  have hfree : ((List.range numVars).countP fun v => !(R.isFixed.getD v false) && p v : Int)
      = (P.rowSums x).getD r 0 := by
    rw [rowSums_spec P hV.toWf x (by rw [hP, (ofReduced_refines R).nrows_eq]; exact hr)]
    congr 1
    have hlen : ((survivors R).toList).length = P.nvars := by
      rw [Array.length_toList]; simp only [hP, ofReduced]
    have hstep := countP_range_length p 0 ((survivors R).toList)
    rw [hlen] at hstep
    have hfilter : ((survivors R).toList).countP p
        = (List.range numVars).countP (fun v => !(R.isFixed.getD v false) && p v) := by
      unfold survivors
      rw [List.toList_toArray, List.countP_filter]
      exact countP_congr _ fun v _ => Bool.and_comm _ _
    rw [← hfilter, ← hstep]
    refine (countP_congr _ fun u hu => ?_).symm
    have hu' : u < P.nvars := List.mem_range.mp hu
    have hvar : ((survivors R).toList).getD u 0 = P.varOf.getD u 0 := by
      rw [Array.getD_toList]; simp only [hP, ofReduced]
    rw [hvar, hp]
    simp only [redIndex_varOf hV hu', hV.rowsOf_eq u hu', sudokuInc_rowsOf]
  -- split the full count on whether the variable survived
  have hsplit := countP_split
    (fun v => y.getD v false && (rowsOfVar v).contains r)
    (fun v => (P.redIndex v).isSome) (List.range numVars)
  have h1 : (List.range numVars).countP
      (fun v => (y.getD v false && (rowsOfVar v).contains r) && (P.redIndex v).isSome)
      = (List.range numVars).countP (fun v => !(R.isFixed.getD v false) && p v) := by
    refine countP_congr _ fun v hv => ?_
    have hvlt := List.mem_range.mp hv
    rw [hy, embed_getD P R.fixedVal x hvlt, hp, ← redIndex_isSome R hvlt]
    cases h : P.redIndex v <;> simp [h]
  have h2 : (List.range numVars).countP
      (fun v => (y.getD v false && (rowsOfVar v).contains r) && !(P.redIndex v).isSome)
      = (List.range numVars).countP
          (fun v => (pinnedOnes R).getD v false && (rowsOfVar v).contains r) := by
    refine countP_congr _ fun v hv => ?_
    have hvlt := List.mem_range.mp hv
    rw [hy, embed_getD P R.fixedVal x hvlt, pinnedOnes_getD R hvlt]
    have hiso := redIndex_isSome R hvlt
    cases h : P.redIndex v <;> rw [h] at hiso <;> simp_all
  -- assemble
  show countOn y (varsOfRowSpec r) = _
  rw [countOn_varsOfRowSpec y hr, hsplit]
  push_cast
  rw [h1, h2, hfree, bhat_getD R hr]
  unfold bhatRow
  push_cast
  ring

/-- **The reduced objective is the paper's objective.**

What the collaborative neurodynamic search minimises, and what `CNS.Sound` proves is Sudoku, are
the same function. Until now this was checked at run time only (`cns reduced`). -/
theorem penaltyDoubled_embed (R : Reduced) (x : Array Bool) :
    (ofReduced R).penaltyDoubled x
      = CNS.penaltyDoubled ((ofReduced R).embed R.fixedVal x) := by
  set P := ofReduced R with hP
  set y := P.embed R.fixedVal x with hy
  have hterm : ∀ r ∈ List.range numRows,
      ((P.rowSums x).getD r 0 - P.bhat.getD r 0) * ((P.rowSums x).getD r 0 - P.bhat.getD r 0)
        = residual y r * residual y r := by
    intro r hr
    have hr' : r < numRows := List.mem_range.mp hr
    have := rowCount_embed R x hr'
    rw [hy, hP]
    unfold residual
    rw [this]
    ring_nf
  show (Array.range numRows).foldl _ 0 = (List.range numRows).foldl _ 0
  rw [← Array.foldl_toList]
  simp only [Array.toList_range]
  exact foldl_add_congr (List.range numRows) hterm 0

end Problem
end CNS
