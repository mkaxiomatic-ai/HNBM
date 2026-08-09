/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.QUBO.Net

/-!
# The executable dynamics compute HNBM's local field

`CNS.Net` puts the reduced QUBO on `TwoState.ZeroOne` and shows the HNBM energy is the paper's
`p(x̂)`. That is a statement about a mathematical object. This module connects it to the object
that actually runs: `Problem.netVec`, the `O(nvars)` integer routine the sweeps in
`CNS.Dynamics` call.

The claim proved here is

  `(netVec P x)_u  =  (W x̂)_u − θ̂_u  =  s.net (netParams P) u − θ̂_u`,

the right-hand side being exactly `HopfieldEnergy`'s local field (`BoltzmannMachine.lean`'s
`localField`). So the search is not *modelled by* an HNBM network, it *is* one, evaluated by a
faster route.

## Why `netVec` is `O(nvars)` and not `O(nvars²)`

A surviving variable lies in `deg(u) = (rowsOf u).size` constraint rows (`Problem.sum_Ahat`),
four of them for Sudoku. Writing `ρ_r = Σ_{v ∈ r} x̂_v`,

  `Σ_{r ∋ u} ρ_r = Σ_v (ÂᵀÂ)_{uv} x̂_v = deg(u)·x̂_u + Σ_{v ≠ u} (ÂᵀÂ)_{uv} x̂_v`,

so `(W x̂)_u = deg(u)·x̂_u − Σ_{r ∋ u} ρ_r`. The row sums are computed once per sweep by a
scatter, and each neuron then costs `deg(u)` array reads. `rowSums_spec` below is what justifies that
rewriting.

## One genuine discrepancy

`ZeroOne.fact` fires on `θ ≤ net`, i.e. on local field `≥ 0`. The paper's activation (eq. 2) is
`σ(u) = 1` iff `u > 0`, i.e. `> 0`. The two differ exactly when the local field is zero. This is
recorded in `dhnm_tie_differs` rather than smoothed over: it is a real difference between the
paper's dynamics and the repository's, and it is on the measure-zero set where a threshold
network is undetermined anyway.
-/

namespace QUBO
namespace Problem

open Finset

/-! ## The scatter loop -/

/-- Setting along a duplicate-free list of indices adds one to exactly the listed rows. -/
private theorem scatter_list (r : Nat) :
    ∀ (l : List Nat) (ρ : Array Int), l.Nodup → r < ρ.size →
      (l.foldl (fun ρ r' => ρ.set! r' ((ρ.getD r' 0) + 1)) ρ).getD r 0
        = ρ.getD r 0 + (if r ∈ l then 1 else 0) := by
  intro l
  induction l with
  | nil => intro ρ _ _; simp
  | cons r' t ih =>
    intro ρ hnd hr
    have hsz : (ρ.set! r' ((ρ.getD r' 0) + 1)).size = ρ.size := by simp
    have hr' : r < (ρ.set! r' ((ρ.getD r' 0) + 1)).size := by rw [hsz]; exact hr
    rw [List.foldl_cons, ih _ (List.nodup_cons.mp hnd).2 hr']
    by_cases hrr : r = r'
    · subst hrr
      have hnotin : r ∉ t := (List.nodup_cons.mp hnd).1
      have hset : (ρ.set! r ((ρ.getD r 0) + 1)).getD r 0 = ρ.getD r 0 + 1 := by
        simp only [Array.set!_eq_setIfInBounds]
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_self_of_lt hr]
        simp
      rw [hset, if_neg hnotin, if_pos (List.mem_cons_self ..)]
      omega
    · have hset : (ρ.set! r' ((ρ.getD r' 0) + 1)).getD r 0 = ρ.getD r 0 := by
        simp [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_ne (Ne.symm hrr)]
      rw [hset]
      by_cases hmem : r ∈ t
      · rw [if_pos hmem, if_pos (List.mem_cons_of_mem _ hmem)]
      · rw [if_neg hmem, if_neg (by simpa [hrr] using hmem)]

/-- The scatter preserves the length of the accumulator. -/
private theorem scatter_size :
    ∀ (l : List Nat) (ρ : Array Int),
      (l.foldl (fun ρ r' => ρ.set! r' ((ρ.getD r' 0) + 1)) ρ).size = ρ.size := by
  intro l
  induction l with
  | nil => intro ρ; rfl
  | cons r' t ih => intro ρ; rw [List.foldl_cons, ih]; simp

/-- The outer loop of `rowSums`, as an accumulating statement about one row. -/
private theorem rowSums_aux (P : Problem) (hW : P.Wf) (x : Array Bool) (r : Nat) :
    ∀ (l : List Nat) (ρ : Array Int), (∀ u ∈ l, u < P.nvars) → r < ρ.size →
      (l.foldl (fun ρ u => if x.getD u false then
            (P.rowsOf.getD u #[]).foldl (fun ρ r' => ρ.set! r' ((ρ.getD r' 0) + 1)) ρ
          else ρ) ρ).getD r 0
        = ρ.getD r 0
          + (l.countP fun u => x.getD u false && (P.rowsOf.getD u #[]).contains r : Int) := by
  intro l
  induction l with
  | nil => intro ρ _ _; simp
  | cons u t ih =>
    intro ρ hlt hr
    have hu : u < P.nvars := hlt u (List.mem_cons_self ..)
    have hnd : (P.rowsOf.getD u #[]).toList.Nodup := by
      exact hW.nodup u hu
    rw [List.foldl_cons, List.countP_cons]
    by_cases hx : x.getD u false = true
    · have hstep : (if x.getD u false then
            (P.rowsOf.getD u #[]).foldl (fun ρ r' => ρ.set! r' ((ρ.getD r' 0) + 1)) ρ else ρ)
          = (P.rowsOf.getD u #[]).foldl (fun ρ r' => ρ.set! r' ((ρ.getD r' 0) + 1)) ρ := by
        rw [if_pos hx]
      rw [hstep]
      have hsz : ((P.rowsOf.getD u #[]).foldl
          (fun ρ r' => ρ.set! r' ((ρ.getD r' 0) + 1)) ρ).size = ρ.size := by
        rw [← Array.foldl_toList]; exact scatter_size _ _
      rw [ih _ (fun y hy => hlt y (List.mem_cons_of_mem _ hy)) (by rw [hsz]; exact hr),
        ← Array.foldl_toList, scatter_list r _ ρ hnd hr]
      have hmem : (r ∈ (P.rowsOf.getD u #[]).toList) = ((P.rowsOf.getD u #[]).contains r = true) := by
        simp [Array.contains_iff_mem]
      simp only [hx, Bool.true_and]
      by_cases hc : (P.rowsOf.getD u #[]).contains r = true
      · rw [if_pos (by rw [hmem]; exact hc), if_pos hc]; push_cast; ring
      · rw [if_neg (by rw [hmem]; exact hc), if_neg hc]; push_cast; ring
    · rw [if_neg hx, ih _ (fun y hy => hlt y (List.mem_cons_of_mem _ hy)) hr]
      simp only [Bool.not_eq_true] at hx
      rw [if_neg (by simp [hx])]
      simp

/-- **The row sums count the set variables of each constraint row.**

`ρ_r = |{u : x̂_u = 1 and u occurs in row r}|`. This is the specification of the scatter that
`Problem.rowSums` performs. -/
theorem rowSums_spec (P : Problem) (hW : P.Wf) (x : Array Bool) {r : Nat} (hr : r < P.nrows) :
    (P.rowSums x).getD r 0
      = ((List.range P.nvars).countP
          fun u => x.getD u false && (P.rowsOf.getD u #[]).contains r : Int) := by
  have hbase : (Array.replicate P.nrows (0 : Int)).getD r 0 = 0 := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa using hr)]
    simp
  have hsz : r < (Array.replicate P.nrows (0 : Int)).size := by simpa using hr
  show (Id.run _ : Array Int).getD r 0 = _
  rw [show (Id.run (do
        let mut ρ : Array Int := Array.replicate P.nrows 0
        for u in [0:P.nvars] do
          ρ := if x.getD u false then
                 (P.rowsOf.getD u #[]).foldl (fun ρ r => ρ.set! r ((ρ.getD r 0) + 1)) ρ
               else ρ
        return ρ) : Array Int)
      = (List.range P.nvars).foldl (fun ρ u => if x.getD u false then
            (P.rowsOf.getD u #[]).foldl (fun ρ r' => ρ.set! r' ((ρ.getD r' 0) + 1)) ρ
          else ρ) (Array.replicate P.nrows 0) from by
    simp [Id.run, List.range_eq_range']
    rfl]
  rw [rowSums_aux P hW x r _ _ (fun u hu => List.mem_range.mp hu) hsz, hbase, zero_add]

/-! ## The net input -/

/-- **`netVec` computes the local field `(W x̂)_u − θ̂_u`.**

Read off directly, since `netVec` is a `map`: the entry is `4x̂_u − Σ_{r ∋ u} ρ_r − θ̂_u`. That
this equals `(W x̂)_u − θ̂_u` is `netVec_eq_localField`. -/
theorem netVec_getD (P : Problem) (x : Array Bool) {u : Nat} (hu : u < P.nvars) :
    (P.netVec x).getD u 0
      = ((if x.getD u false then ((P.rowsOf.getD u #[]).size : Int) else 0)
          - (P.rowsOf.getD u #[]).foldl (fun acc r => acc + (P.rowSums x).getD r 0) 0)
        - P.theta.getD u 0 := by
  show ((Array.range P.nvars).map _).getD u 0 = _
  rw [Array.getD_eq_getD_getElem?,
    Array.getElem?_eq_getElem (by simpa using hu)]
  simp only [Array.getElem_map, Array.getElem_range]
  rfl

/-! ## From the executable state to the abstract one -/

/-- The bits of an executable state, as a function on the reduced index type. -/
def bitsOf (P : Problem) (x : Array Bool) : Fin P.nvars → Bool := fun u => x.getD u.val false

/-- **The executable row sums are the abstract ones.** -/
theorem rowSumR_eq (P : Problem) (hW : P.Wf) (x : Array Bool) {r : Nat} (hr : r < P.nrows) :
    rowSumR P (bitsOf P x) r = ((P.rowSums x).getD r 0 : ℝ) := by
  have hpt : ∀ u : Fin P.nvars, Ahat P r u * bit (bitsOf P x u)
      = (if (x.getD u.val false && (P.rowsOf.getD u.val #[]).contains r) then (1 : ℝ) else 0) := by
    intro u
    unfold Ahat bit bitsOf inRow
    by_cases h1 : x.getD u.val false = true <;>
      by_cases h2 : (P.rowsOf.getD u.val #[]).contains r = true <;> simp [h1, h2]
  have hfin : (Finset.range P.nvars).filter
      (fun i => (x.getD i false && (P.rowsOf.getD i #[]).contains r) = true)
      = ((List.range P.nvars).filter
          (fun i => x.getD i false && (P.rowsOf.getD i #[]).contains r)).toFinset := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, List.mem_toFinset, List.mem_filter,
      List.mem_range]
  unfold rowSumR
  rw [Finset.sum_congr rfl fun u _ => hpt u,
    Fin.sum_univ_eq_sum_range
      (fun i => if (x.getD i false && (P.rowsOf.getD i #[]).contains r) then (1 : ℝ) else 0),
    ← Finset.sum_filter, hfin, Finset.sum_const, nsmul_eq_mul, mul_one,
    List.toFinset_card_of_nodup (List.Nodup.filter _ List.nodup_range),
    ← List.countP_eq_length_filter, rowSums_spec P hW x hr]
  norm_num

/-- **`(W x̂)_u = deg(u)·x̂_u − Σ_{r ∋ u} ρ_r`.**

The identity that makes the net input `O(nvars)`: the Gram row against `x̂` is the sum of the
row sums of the rows containing `u`, and the diagonal contributes that column's degree. -/
theorem mulVec_Wr (P : Problem) (hW : P.Wf) (x : Fin P.nvars → Bool) (u : Fin P.nvars) :
    (Wr P).mulVec (fun v => bit (x v)) u
      = ((P.rowsOf.getD u.val #[]).size : ℝ) * bit (x u)
        - ∑ r ∈ Finset.range P.nrows, Ahat P r u * rowSumR P x r := by
  have hswap : ∑ v, gramR P u v * bit (x v)
      = ∑ r ∈ Finset.range P.nrows, Ahat P r u * rowSumR P x r := by
    unfold gramR rowSumR
    rw [Finset.sum_congr rfl fun v _ => Finset.sum_mul _ _ _, Finset.sum_comm]
    exact Finset.sum_congr rfl fun r _ => by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun v _ => by ring
  have hterm : ∀ v : Fin P.nvars, Wr P u v * bit (x v)
      = -(gramR P u v * bit (x v)) + (if u = v then gramR P u v * bit (x v) else 0) := by
    intro v; rw [Wr_split P u v]; split <;> ring
  rw [Matrix.mulVec_apply_eq_sum, Finset.sum_congr rfl fun v _ => hterm v,
    Finset.sum_add_distrib, Finset.sum_ite_eq Finset.univ u (fun v => gramR P u v * bit (x v))]
  simp only [Finset.mem_univ, if_true, gramR_diag P hW u]
  rw [Finset.sum_neg_distrib, hswap]
  ring

/-- Casting an integer fold of additions into `ℝ`. -/
private theorem cast_foldl_add (f : Nat → Int) :
    ∀ (l : List Nat) (acc : Int),
      ((l.foldl (fun a r => a + f r) acc : Int) : ℝ)
        = l.foldl (fun a r => a + (f r : ℝ)) (acc : ℝ) := by
  intro l
  induction l with
  | nil => intro acc; rfl
  | cons r t ih =>
    intro acc
    simp only [List.foldl_cons]
    rw [ih (acc + f r)]
    congr 1
    push_cast
    ring

/-- The same, for an array fold from zero. -/
private theorem cast_array_foldl_add (A : Array Nat) (f : Nat → Int) :
    (((A.foldl (fun acc r => acc + f r) (0 : Int)) : Int) : ℝ)
      = A.foldl (fun acc r => acc + (f r : ℝ)) (0 : ℝ) := by
  rw [← Array.foldl_toList, ← Array.foldl_toList, cast_foldl_add f A.toList 0]
  norm_num

/-- **The executable net input is HNBM's local field.**

`netVec P x` computes, at each neuron, exactly `s.net (netParams P) u − θ̂_u` — the quantity
`HopfieldEnergy` calls the local field, and which drives both `ZeroOne`'s threshold rule and the
Gibbs acceptance of the Boltzmann machine.

This is what makes the search an instance of the repository's network rather than a lookalike:
the integer routine in the inner loop and the `Finset.sum` in the specification agree on the
nose, so a theorem proved for `ZeroOne` at `netParams P` is a theorem about the running code. -/
theorem netVec_eq_localField (P : Problem) [Nonempty (Fin P.nvars)] (hW : P.Wf)
    (x : Array Bool) (u : Fin P.nvars) :
    ((P.netVec x).getD u.val 0 : ℝ)
      = (stateOfBits P (bitsOf P x)).net (netParams P) u
        - ((netParams P).θ u).get TwoState.fin0 := by
  -- `fnet` omits the diagonal, which `W` sets to zero, so it is the full `mulVec`
  have hnet : (stateOfBits P (bitsOf P x)).net (netParams P) u
      = (Wr P).mulVec (fun v => bit (bitsOf P x v)) u := by
    show ∑ v, (if v ≠ u then (netParams P).w u v * bit (bitsOf P x v) else 0) = _
    rw [Matrix.mulVec_apply_eq_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    by_cases h : v = u
    · subst h
      rw [if_neg (by simp)]
      show (0 : ℝ) = Wr P v v * _
      rw [Wr_diag P v, zero_mul]
    · rw [if_pos h]; rfl
  have hθ : ((netParams P).θ u).get TwoState.fin0 = (P.theta.getD u.val 0 : ℝ) := rfl
  -- the four-row fold against `ρ` is the indicator sum against `ρ`
  have hfold : ((((P.rowsOf.getD u.val #[]).foldl
        (fun acc r => acc + (P.rowSums x).getD r 0) (0 : Int)) : Int) : ℝ)
      = ∑ r ∈ Finset.range P.nrows, Ahat P r u * rowSumR P (bitsOf P x) r := by
    rw [cast_array_foldl_add,
      ← sum_indicator_weighted (N := P.nrows) (P.rowsOf.getD u.val #[])
        (fun r => ((P.rowSums x).getD r 0 : ℝ))
        (hW.nodup u.val u.isLt) (hW.mem_lt u.val u.isLt)]
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [rowSumR_eq P hW x (Finset.mem_range.mp hr)]
    unfold Ahat inRow
    split <;> simp
  have hbit : (if x.getD u.val false then ((P.rowsOf.getD u.val #[]).size : ℝ) else 0)
      = ((P.rowsOf.getD u.val #[]).size : ℝ) * bit (bitsOf P x u) := by
    unfold bit bitsOf; split <;> simp_all
  rw [hnet, hθ, mulVec_Wr P hW _ u, netVec_getD P x u.isLt]
  push_cast
  rw [hfold, hbit]

/-- **The paper's activation and `ZeroOne`'s differ exactly on a zero local field.**

`ZeroOne.fact` fires on `θ ≤ net`, i.e. local field `≥ 0`; the paper's `σ` of eq. (2) fires on
`> 0`. Recorded rather than smoothed over: it is a real difference between the two dynamics,
confined to the tie, where a threshold network is undetermined anyway. -/
theorem gt_zero_eq_le_of_ne_zero {L : Int} (hL : L ≠ 0) :
    decide (0 < L) = decide (0 ≤ L) := by
  by_cases h : 0 < L
  · simp [h, le_of_lt h]
  · have : L < 0 := by omega
    simp [h]; omega

end Problem
end QUBO
