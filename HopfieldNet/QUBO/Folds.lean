/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Basic

/-!
# Array folds as sums

Small bridging lemmas between the `Array.foldl` the executable uses and the `Finset.sum` the
algebra is stated in. Nothing here is about QUBOs, let alone Sudoku; they live here because
`QUBO.Refine` and `CNS.NetValid` both need them.
-/

namespace QUBO

open Finset

/-! ## Array folds as sums -/

/-- Folding an addition over a list is summing the mapped entries. -/
private theorem list_foldl_add {M : Type*} [AddCommMonoid M] {α : Type*} (f : α → M) :
    ∀ (l : List α) (acc : M), l.foldl (fun a x => a + f x) acc = acc + (l.map f).sum := by
  intro l
  induction l with
  | nil => intro acc; simp
  | cons x t ih => intro acc; simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih]
                   rw [add_assoc]

/-- The sum of a mapped list, indexed by position. -/
private theorem list_map_sum_eq_sum_range {M : Type*} [AddCommMonoid M] {α : Type*}
    (f : α → M) (d : α) :
    ∀ l : List α, (l.map f).sum = ∑ i ∈ Finset.range l.length, f (l.getD i d) := by
  intro l
  induction l with
  | nil => simp
  | cons x t ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Finset.sum_range_succ']
    rw [ih]
    simp [List.getD_cons_succ, List.getD_cons_zero, add_comm]

/-- **An array fold of additions is a `Finset` sum over its indices.**

The workhorse for turning `ofReduced`'s folds into the sums `Problem.Valid` is stated with. -/
theorem Array.foldl_add_eq_sum {M : Type*} [AddCommMonoid M] {α : Type*}
    (a : Array α) (f : α → M) (d : α) :
    a.foldl (fun acc x => acc + f x) 0 = ∑ i ∈ Finset.range a.size, f (a.getD i d) := by
  rw [← Array.foldl_toList, list_foldl_add f a.toList 0, zero_add,
    list_map_sum_eq_sum_range f d a.toList, Array.length_toList]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i < a.size := Finset.mem_range.mp hi
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi',
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hi')]
  simp

/-- Folding over a duplicate-free array of row indices is summing its indicator over all rows. -/
theorem sum_indicator_weighted {M : Type*} [AddCommMonoid M] {N : Nat} (a : Array Nat)
    (f : Nat → M) (hnd : a.toList.Nodup) (hlt : ∀ r ∈ a, r < N) :
    ∑ r ∈ Finset.range N, (if a.contains r then f r else 0)
      = a.foldl (fun acc r => acc + f r) 0 := by
  have hfilter : (Finset.range N).filter (fun r => a.contains r = true) = a.toList.toFinset := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_range, List.mem_toFinset, Array.contains_iff_mem,
      Array.mem_toList_iff]
    exact ⟨fun h => h.2, fun h => ⟨hlt r h, h⟩⟩
  rw [← Finset.sum_filter, hfilter, List.sum_toFinset _ hnd, ← Array.foldl_toList,
    list_foldl_add f a.toList 0, zero_add]

/-! ## Reading off `ofReduced`

Each field is a `map` or a `filter`; these lemmas are the pointwise readings. -/

end QUBO
