/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.CNS.Net

/-!
# The pipeline's reduced instances are valid

`CNS.Net` proves the energy bridge from `Problem.Valid`. This module discharges `Valid` for the
problems the pipeline actually builds, so that the bridge applies to them rather than to a
hypothetical instance.

All the array bookkeeping of §IV lives here. It is short only because `Problem.ofReduced` was
written as `map`s and `filter`s over index ranges rather than as scatter loops: a `map` is
characterised pointwise by `Array.getElem_map`, whereas a loop accumulating with `set!` can only
be characterised by an induction over its trip count carrying the whole array as an invariant.
-/

namespace CNS

open Finset

-- `numVars = 729` and `numRows = 324` are `def`s, so unification occasionally tries to evaluate
-- `Array.range` at them. Raise the limit rather than making the arithmetic opaque.
set_option maxRecDepth 8000

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

namespace Problem

variable (R : Reduced)

/-! `rfl` cannot be used for these: it unfolds the projection at default transparency and then
tries to evaluate `Array.range numVars`, which does not terminate within the heartbeat budget.
`simp only [ofReduced]` performs the projection symbolically instead. -/

/-- The surviving-variable table. -/
private theorem ofReduced_varOf : (ofReduced R).varOf = survivors R := by
  simp only [ofReduced]

/-- The dimension is the number of survivors. -/
private theorem ofReduced_nvars : (ofReduced R).nvars = (survivors R).size := by
  simp only [ofReduced]

/-- `rowsOf` is `varOf` mapped through `rowsOfVar`. -/
private theorem ofReduced_rowsOf : (ofReduced R).rowsOf = (survivors R).map rowsOfVar := by
  simp only [ofReduced, rowsOfSurv]

/-- `bhat` is the reduced right-hand side. -/
private theorem ofReduced_bhat : (ofReduced R).bhat = bhatOf R := by
  simp only [ofReduced]

/-- `theta` is `rowsOf` mapped through the fold against `b̂`. -/
private theorem ofReduced_theta :
    (ofReduced R).theta = (rowsOfSurv R).map (thetaRow (bhatOf R)) := by
  simp only [ofReduced, thetaOf]

/-- `constDoubled` is the fold of squares over `b̂`. -/
private theorem ofReduced_const :
    (ofReduced R).constDoubled = (bhatOf R).foldl (fun acc bi => acc + bi * bi) 0 := by
  simp only [ofReduced]

/-- `bhat` has one entry per constraint row. -/
theorem ofReduced_bhat_size : (ofReduced R).bhat.size = numRows := by
  rw [ofReduced_bhat]
  unfold bhatOf
  rw [Array.size_map, Array.size_range]

/-- The survivor table's length is the problem dimension. -/
private theorem varOf_size : (ofReduced R).varOf.size = (ofReduced R).nvars := by
  rw [ofReduced_varOf, ofReduced_nvars]

/-- Reading a `map` at an in-range index. -/
private theorem getD_map {α β : Type*} [Inhabited β] (a : Array α) (f : α → β) (d : α)
    {i : Nat} (hi : i < a.size) (db : β) : (a.map f).getD i db = f (a.getD i d) := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
    Array.getElem?_eq_getElem (by simpa using hi), Array.getElem?_eq_getElem hi]
  simp

/-- Survivors are legal variable indices. -/
private theorem varOf_lt' {u : Nat} (hu : u < (ofReduced R).nvars) :
    (ofReduced R).varOf.getD u 0 < numVars := by
  have hsz : u < (ofReduced R).varOf.size := by rw [varOf_size]; exact hu
  have hmem : (ofReduced R).varOf.getD u 0 ∈ (ofReduced R).varOf := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hsz]
    exact Array.getElem_mem hsz
  rw [ofReduced_varOf] at hmem
  unfold survivors at hmem
  rw [Array.mem_toArray] at hmem
  exact List.mem_range.mp (List.mem_filter.mp hmem).1

/-- Distinct reduced indices name distinct original variables: `varOf` is a filter of a range,
so its entries are pairwise distinct. -/
private theorem varOf_inj' {u : Nat} (hu : u < (ofReduced R).nvars) {v : Nat}
    (hv : v < (ofReduced R).nvars)
    (h : (ofReduced R).varOf.getD u 0 = (ofReduced R).varOf.getD v 0) : u = v := by
  have hnd : (ofReduced R).varOf.toList.Nodup := by
    rw [ofReduced_varOf]
    unfold survivors
    rw [List.toList_toArray]
    exact List.Nodup.filter _ List.nodup_range
  have hu' : u < (ofReduced R).varOf.size := by rw [varOf_size]; exact hu
  have hv' : v < (ofReduced R).varOf.size := by rw [varOf_size]; exact hv
  have hgu : (ofReduced R).varOf.getD u 0 = (ofReduced R).varOf[u] := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hu']; rfl
  have hgv : (ofReduced R).varOf.getD v 0 = (ofReduced R).varOf[v] := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hv']; rfl
  rw [hgu, hgv] at h
  have hlu : u < (ofReduced R).varOf.toList.length := by rwa [Array.length_toList]
  have hlv : v < (ofReduced R).varOf.toList.length := by rwa [Array.length_toList]
  exact (List.getElem_inj (h₀ := hlu) (h₁ := hlv) (h := hnd)).mp
    (by rw [Array.getElem_toList, Array.getElem_toList]; exact h)

/-- **Every problem the pipeline builds satisfies `Valid`.**

With this, `Net.zeroOneHamiltonian_eq` applies to the instances the search is actually run on:
the HNBM energy of `netParams (Problem.ofGrid g)` is the paper's `p(x̂)` for the reduced puzzle
of `g`. -/
theorem ofReduced_valid : (ofReduced R).Valid where
  varOf_lt := fun u hu => varOf_lt' R hu
  varOf_inj := fun u hu v hv h => varOf_inj' R hu hv h
  rowsOf_eq := fun u hu => by
    rw [ofReduced_rowsOf]
    exact getD_map _ _ 0 hu #[]
  theta_eq := fun u hu => by
    have hu' : u < (survivors R).size := by rw [← ofReduced_nvars]; exact hu
    have hRO : (ofReduced R).rowsOf = rowsOfSurv R := by rw [ofReduced_rowsOf]; unfold rowsOfSurv; rfl
    have hsz : u < (rowsOfSurv R).size := by unfold rowsOfSurv; rwa [Array.size_map]
    have hrs : (rowsOfSurv R).getD u #[] = rowsOfVar ((survivors R).getD u 0) := by
      unfold rowsOfSurv; exact getD_map _ _ 0 hu' #[]
    have hvlt : (survivors R).getD u 0 < numVars := by
      have := varOf_lt' R hu; rwa [ofReduced_varOf] at this
    obtain ⟨hnd, hlt⟩ := rowsOfVar_nodup _ hvlt
    rw [ofReduced_theta, getD_map _ _ #[] hsz 0, ofReduced_bhat, hRO, hrs]
    unfold thetaRow
    rw [← sum_indicator_weighted (N := numRows) _ _ hnd hlt]
  const_eq := by
    rw [ofReduced_const, Array.foldl_add_eq_sum (bhatOf R) (fun b => b * b) 0,
      ← ofReduced_bhat, ofReduced_bhat_size]
    exact Finset.sum_congr rfl fun r _ => by rw [ofReduced_bhat]; exact (sq _).symm

/-- The reduced instance of a puzzle is valid. -/
theorem ofGrid_valid (g : Grid) : (ofGrid g).Valid := ofReduced_valid _

end Problem
end CNS
