/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.CNS.GridSound
import HopfieldNet.CNS.Embed

/-!
# A zero penalty decodes to a solved grid

`CNS.GridSound` proves one direction — a solved grid encodes to zero penalty. This module proves
the other, which is the direction the search relies on:

  `penaltyDoubled x = 0  →  (decode x).isSolution`.

Until now that step was exercised only by the runtime certificate check on every solve. With it
proved, `p(x) = 0` and "this is a solved Sudoku" are interderivable in both directions, at the
level of *grids* rather than of the `n³` encoding variables.

## How it goes

`penalty_zero_iff_families` turns a zero penalty into the four family constraints. The cell
family (10a) says each cell's nine variables carry exactly one `1`, so `hitsAt` is a singleton
and `decode` assigns that digit — giving completeness and legal digits at once. The other three
families become `Grid.isConsistent` once the counts are transported along `decode_get_iff`:
"cell `(i,j)` holds `k`" and "`x_{ijk}` is set" are the same statement.
-/

namespace CNS

open Finset

/-! ## Reading the decoded grid -/

/-- `decode` applies its cell rule at each cell. -/
theorem decode_get {x : Array Bool} {c : Nat} (hc : c < numCells) :
    (decode x).get c = match hitsAt x c with | [k] => some k | _ => none := by
  show ((Array.range numCells).map _).getD c none = _
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa using hc)]
  simp only [Array.getElem_map, Array.getElem_range]
  rfl

/-- The cell constraint, counted over digits rather than over variables. -/
theorem length_hitsAt {x : Array Bool} {c : Nat} (hc : c < numCells)
    (h : countOn x (cellVars (rowOf c) (colOf c)) = 1) : (hitsAt x c).length = 1 := by
  unfold hitsAt
  rw [← List.countP_eq_length_filter]
  unfold countOn cellVars at h
  rw [countOn_foldl x _ 0, zero_add, List.countP_map] at h
  exact_mod_cast h

/-- **Each cell of the decoded grid holds exactly one legal digit.** -/
theorem hitsAt_singleton {x : Array Bool} (hx : penaltyDoubled x = 0) {c : Nat}
    (hc : c < numCells) : ∃ k, k < n ∧ hitsAt x c = [k] := by
  have hi : rowOf c < n := by simp only [rowOf, numCells, n] at *; omega
  have hj : colOf c < n := by simp only [colOf, n] at *; omega
  have hcell := ((penalty_zero_iff_families x).mp hx).1 _ hi _ hj
  obtain ⟨k, hk⟩ := List.length_eq_one_iff.mp (length_hitsAt hc hcell)
  refine ⟨k, ?_, hk⟩
  have : k ∈ hitsAt x c := by rw [hk]; exact List.mem_singleton_self k
  unfold hitsAt at this
  exact List.mem_range.mp (List.mem_filter.mp this).1

/-- **A cell of the decoded grid holds `k` exactly when `x` sets the corresponding variable.**

Both directions are used: forward for legal digits, backward to transport the row, column and
block counts from the encoding to the grid. -/
theorem decode_get_iff {x : Array Bool} (hx : penaltyDoubled x = 0) {c : Nat}
    (hc : c < numCells) {k : Nat} :
    (decode x).get c = some k
      ↔ (k < n ∧ x.getD (varIdx (rowOf c) (colOf c) k) false = true) := by
  obtain ⟨t, ht, hsing⟩ := hitsAt_singleton hx hc
  have hmem : ∀ s, s ∈ hitsAt x c ↔ (s < n ∧ x.getD (varIdx (rowOf c) (colOf c) s) false = true) := by
    intro s; unfold hitsAt; rw [List.mem_filter, List.mem_range]
  rw [decode_get hc, hsing]
  constructor
  · intro hk
    have hkt : t = k := by simpa using hk
    subst hkt
    exact (hmem t).mp (by rw [hsing]; exact List.mem_singleton_self t)
  · intro hk
    have hin : k ∈ hitsAt x c := (hmem k).mpr hk
    rw [hsing] at hin
    rw [List.mem_singleton.mp hin]

/-! ## The grid predicates -/

theorem decode_hasSize (x : Array Bool) : (decode x).hasSize = true := by
  show ((Array.range numCells).map _).size == numCells
  simp

theorem decode_cells_size (x : Array Bool) : (decode x).cells.size = numCells := by
  show ((Array.range numCells).map _).size = numCells
  simp

/-- Membership in the decoded cell array names a cell. -/
private theorem mem_decode_cells {x : Array Bool} {o : Option Nat} (ho : o ∈ (decode x).cells) :
    ∃ c, c < numCells ∧ (decode x).get c = o := by
  obtain ⟨i, hi, he⟩ := Array.getElem_of_mem ho
  refine ⟨i, by simpa [decode_cells_size] using hi, ?_⟩
  rw [Grid.get, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]
  exact he

theorem decode_isComplete {x : Array Bool} (hx : penaltyDoubled x = 0) :
    (decode x).isComplete = true := by
  unfold Grid.isComplete
  rw [Array.all_eq_true_iff_forall_mem]
  intro o ho
  obtain ⟨c, hc, hget⟩ := mem_decode_cells ho
  obtain ⟨k, hk, hsing⟩ := hitsAt_singleton hx hc
  rw [decode_get hc, hsing] at hget
  rw [← hget]
  rfl

theorem decode_digitsInRange {x : Array Bool} (hx : penaltyDoubled x = 0) :
    (decode x).digitsInRange = true := by
  unfold Grid.digitsInRange
  rw [Array.all_eq_true_iff_forall_mem]
  intro o ho
  obtain ⟨c, hc, hget⟩ := mem_decode_cells ho
  obtain ⟨k, hk, hsing⟩ := hitsAt_singleton hx hc
  rw [decode_get hc, hsing] at hget
  rw [← hget]
  simpa using hk

/-! ## Consistency

`units` is an append of three `map`s, so a unit is a row, a column or a block; each case
transports its family constraint through `decode_get_iff`. -/

theorem mem_units {u : Array Nat} (hu : u ∈ units) :
    (∃ i, i < n ∧ u = rowCells i) ∨ (∃ j, j < n ∧ u = colCells j) ∨
      (∃ b, b < n ∧ u = boxCells b) := by
  unfold units at hu
  rcases Array.mem_append.mp hu with h | h
  · rcases Array.mem_append.mp h with h' | h'
    · obtain ⟨i, hi, he⟩ := Array.mem_map.mp h'
      exact Or.inl ⟨i, Array.mem_range.mp hi, he.symm⟩
    · obtain ⟨j, hj, he⟩ := Array.mem_map.mp h'
      exact Or.inr (Or.inl ⟨j, Array.mem_range.mp hj, he.symm⟩)
  · obtain ⟨b, hb, he⟩ := Array.mem_map.mp h
    exact Or.inr (Or.inr ⟨b, Array.mem_range.mp hb, he.symm⟩)

theorem decode_isConsistent {x : Array Bool} (hx : penaltyDoubled x = 0) :
    (decode x).isConsistent = true := by
  obtain ⟨_, hcol, hrow, hbox⟩ := (penalty_zero_iff_families x).mp hx
  unfold Grid.isConsistent
  rw [Array.all_eq_true_iff_forall_mem]
  intro u hu
  rw [Array.all_eq_true_iff_forall_mem]
  intro kk hkk
  have hk : kk < n := Array.mem_range.mp hkk
  -- one generic step: a unit's cells against the matching variable family
  have step : ∀ (cells vars : Nat → Nat), (∀ t, t < n → cells t < numCells) →
      (∀ t, t < n → vars t = varIdx (rowOf (cells t)) (colOf (cells t)) kk) →
      countOn x ((List.range n).map vars) = 1 →
      (((List.range n).map cells).foldl
        (fun acc c => if (decode x).get c == some kk then acc + 1 else acc) 0 : Nat) = 1 := by
    intro cells vars hcl hvar hcount
    have hagree : ∀ t, t < n →
        x.getD (vars t) false = ((decode x).get (cells t) == some kk) := by
      intro t ht
      rw [hvar t ht]
      by_cases h : x.getD (varIdx (rowOf (cells t)) (colOf (cells t)) kk) false = true
      · rw [h, eq_comm, beq_iff_eq]
        exact (decode_get_iff hx (hcl t ht)).mpr ⟨hk, h⟩
      · simp only [Bool.not_eq_true] at h
        rw [h, eq_comm, beq_eq_false_iff_ne]
        intro hc
        exact absurd ((decode_get_iff hx (hcl t ht)).mp hc).2 (by rw [h]; simp)
    have := countOn_unit_eq (g := decode x) x cells vars hagree
    rw [hcount] at this
    exact_mod_cast this.symm
  rcases mem_units hu with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨b, hb, rfl⟩
  · have hcells : (rowCells i).toList = (List.range n).map (fun c => cellIdx i c) := by
      unfold rowCells; simp
    rw [hcells]
    refine beq_iff_eq.mpr (step (fun c => cellIdx i c) (fun c => varIdx i c kk)
      (fun t ht => by simp only [cellIdx, numCells, n] at *; omega)
      (fun t ht => by
        obtain ⟨hr, hcl⟩ := rowOf_colOf_cellIdx hi ht; rw [hr, hcl])
      (hrow i hi kk hk))
  · have hcells : (colCells j).toList = (List.range n).map (fun r => cellIdx r j) := by
      unfold colCells; simp
    rw [hcells]
    refine beq_iff_eq.mpr (step (fun r => cellIdx r j) (fun r => varIdx r j kk)
      (fun t ht => by simp only [cellIdx, numCells, n] at *; omega)
      (fun t ht => by
        obtain ⟨hr, hcl⟩ := rowOf_colOf_cellIdx ht hj; rw [hr, hcl])
      (hcol j hj kk hk))
  · have hcells : (boxCells b).toList
        = (List.range n).map (fun t => cellIdx ((b / blk) * blk + t / blk)
            ((b % blk) * blk + t % blk)) := by
      unfold boxCells; simp
    rw [hcells]
    refine beq_iff_eq.mpr (step _
      (fun t => varIdx ((b / blk) * blk + t / blk) ((b % blk) * blk + t % blk) kk)
      (fun t ht => by simp only [cellIdx, numCells, blk, n] at *; omega)
      (fun t ht => by
        obtain ⟨hr, hcl⟩ := rowOf_colOf_cellIdx
          (show (b / blk) * blk + t / blk < n by simp only [blk, n] at *; omega)
          (show (b % blk) * blk + t % blk < n by simp only [blk, n] at *; omega)
        rw [hr, hcl])
      (hbox b hb kk hk))

/-! ## The theorem -/

/-- **A zero penalty decodes to a solved grid.**

The converse of `CNS.GridSound.penalty_encode_eq_zero`, and the direction the search needs:
when the neurodynamics reports `p(x) = 0`, the grid read off from `x` really is a solved
Sudoku. Together the two say the objective and the puzzle are the same problem. -/
theorem decode_isSolution {x : Array Bool} (hx : penaltyDoubled x = 0) :
    (decode x).isSolution = true := by
  unfold Grid.isSolution
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  exact ⟨⟨⟨decode_hasSize x, decode_digitsInRange hx⟩, decode_isComplete hx⟩,
    decode_isConsistent hx⟩

/-- **A zero-penalty vector is the encoding of the grid it decodes to.**

With `decode_isSolution` this says the zero set of the paper's objective is exactly the set of
encoded solutions: nothing else reaches `p(x) = 0`, and every solution does. -/
theorem encode_decode {x : Array Bool} (hx : penaltyDoubled x = 0) {v : Nat} (hv : v < numVars) :
    (encode (decode x)).getD v false = x.getD v false := by
  rw [encode_getD hv]
  have hc : v / n < numCells := by simp only [numVars, numCells, n] at *; omega
  have hk : v % n < n := by simp only [n] at *; omega
  have hvar : varIdx (rowOf (v / n)) (colOf (v / n)) (v % n) = v := by
    rw [varIdx_of_cell hc]; simp only [n] at *; omega
  by_cases h : x.getD v false = true
  · rw [h, beq_iff_eq]
    exact (decode_get_iff hx hc).mpr ⟨hk, by rw [hvar]; exact h⟩
  · simp only [Bool.not_eq_true] at h
    rw [h, beq_eq_false_iff_ne]
    intro hcon
    have h2 := ((decode_get_iff hx hc).mp hcon).2
    rw [hvar, h] at h2
    simp at h2

end CNS
