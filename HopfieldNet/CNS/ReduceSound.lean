/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.CNS.Reduce

/-!
# Soundness of Algorithm 1

Algorithm 1 deletes variables, and Table I counts what survives. That count only means anything
if the deletions are **sound** — if every completion of the original puzzle is still a
completion of the reduced one. Otherwise "729 → 171" might be reporting that the reduction threw
the answer away.

Algorithm 1 makes exactly two kinds of deduction:

* a **naked single** — a cell whose peers already use eight of the nine digits, so the ninth is
  forced;
* a **hidden single** — a digit that no other cell of some unit can accept, so it is forced into
  the one cell that can.

Here we prove the first is genuinely forced in *every* completion, which is what licenses
writing it into the grid.

## A note on well-formedness

`Grid` carries no size invariant, and `Grid.isComplete` is `cells.all Option.isSome`, which is
vacuously `true` on an array shorter than `n²`. So `isSolution = true` alone does **not** imply
a grid is total. `Completes` therefore carries `WF` explicitly. Grids built by `Grid.ofString`
and `Grid.assign` satisfy it, but the type does not enforce it.

Mathlib-free, like everything under `CNS` except `CNS.Spec`.
-/

namespace CNS


/-! ## Completions -/

/-- A grid has the right number of cells. Not enforced by the type; see the module note. -/
def Grid.WF (g : Grid) : Prop := g.cells.size = numCells

/-- `h` completes `g`: a well-formed solved grid agreeing with every given of `g`.
This is constraints (10a)-(10d) together with (10e). -/
def Completes (g h : Grid) : Prop := h.WF ∧ h.isSolution = true ∧ g.extends' h = true

/-- `extends'` unfolded: every given of `g` survives in `h`. -/
theorem extends'_iff (g h : Grid) :
    g.extends' h = true ↔ ∀ c < numCells, ∀ k, g.get c = some k → h.get c = some k := by
  unfold Grid.extends'
  rw [Array.all_eq_true_iff_forall_mem]
  constructor
  · intro hall c hc k hk
    have := hall c (Array.mem_range.mpr hc)
    rw [hk] at this
    simpa using this
  · intro hall c hc
    have hc' := Array.mem_range.mp hc
    cases hg : g.get c with
    | none => simp [hg]
    | some k => simpa [hg] using hall c hc' k hg

/-! ## `usedByPeers` -/

/-- `usedByPeers g c` marks exactly the digits occurring in a peer of `c`.

This is the specification of steps 16-31 of Algorithm 1: the digits a given rules out at an
empty cell. -/
theorem usedByPeers_spec (g : Grid) (c k : Nat) (hk : k < n) :
    (usedByPeers g c).getD k false = true ↔ ∃ p ∈ (peers c).toList, g.get p = some k := by
  unfold usedByPeers
  suffices h : ∀ (l : List Nat) (acc : Array Bool), acc.size = n →
      ((l.foldl (markUsed g) acc).getD k false = true
        ↔ acc.getD k false = true ∨ ∃ p ∈ l, g.get p = some k) by
    have hbase : (Array.replicate n false).getD k false = false := by
      rw [Array.getD_eq_getD_getElem?]
      cases hq : (Array.replicate n false)[k]? with
      | none => rfl
      | some v =>
        have hv : v ∈ Array.replicate n false := Array.mem_of_getElem? hq
        simpa using (Array.mem_replicate.mp hv).2
    have hh := h (peers c).toList (Array.replicate n false) (by simp)
    rw [hbase] at hh
    simpa using hh
  intro l
  induction l with
  | nil => intro acc _; simp
  | cons p rest ih =>
    intro acc hsz
    cases hgp : g.get p with
    | none =>
      simp only [List.foldl_cons, markUsed, hgp]
      rw [ih acc hsz]
      constructor
      · rintro (hh | ⟨q, hq, hqk⟩)
        · exact Or.inl hh
        · exact Or.inr ⟨q, List.mem_cons_of_mem _ hq, hqk⟩
      · rintro (hh | ⟨q, hq, hqk⟩)
        · exact Or.inl hh
        · rcases List.mem_cons.mp hq with rfl | hq'
          · rw [hgp] at hqk; exact absurd hqk (by simp)
          · exact Or.inr ⟨q, hq', hqk⟩
    | some d =>
      have hsz' : (acc.set! d true).size = n := by simpa using hsz
      simp only [List.foldl_cons, markUsed, hgp]
      rw [ih (acc.set! d true) hsz']
      by_cases hdk : d = k
      · subst hdk
        have hset : (acc.set! d true).getD d false = true := by
          simp only [Array.set!_eq_setIfInBounds]
          rw [Array.getD_eq_getD_getElem?,
            Array.getElem?_setIfInBounds_self_of_lt (by omega : d < acc.size)]
          rfl
        constructor
        · intro _; exact Or.inr ⟨p, List.mem_cons_self .., hgp⟩
        · intro _; exact Or.inl hset
      · have hne : (acc.set! d true).getD k false = acc.getD k false := by
          simp [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_ne hdk]
        rw [hne]
        constructor
        · rintro (hh | ⟨q, hq, hqk⟩)
          · exact Or.inl hh
          · exact Or.inr ⟨q, List.mem_cons_of_mem _ hq, hqk⟩
        · rintro (hh | ⟨q, hq, hqk⟩)
          · exact Or.inl hh
          · rcases List.mem_cons.mp hq with rfl | hq'
            · rw [hgp] at hqk
              exact absurd (Option.some.inj hqk) hdk
            · exact Or.inr ⟨q, hq', hqk⟩

/-! ## Counting occurrences in a unit -/

/-- The running count only grows. -/
theorem le_foldl_count (f : Nat → Bool) : ∀ (l : List Nat) (acc : Nat),
    acc ≤ l.foldl (fun a x => if f x then a + 1 else a) acc := by
  intro l
  induction l with
  | nil => intro acc; exact Nat.le_refl acc
  | cons x rest ih =>
    intro acc
    simp only [List.foldl_cons]
    cases hfx : f x with
    | true  => simp only [hfx, if_true]; have := ih (acc + 1); omega
    | false => simp only [hfx, Bool.false_eq_true, if_false]; exact ih acc

/-- One member satisfying `f` forces the count up by one. -/
theorem one_le_foldl_count (f : Nat → Bool) {p : Nat} (hfp : f p = true) :
    ∀ (l : List Nat), p ∈ l → ∀ (acc : Nat),
      acc + 1 ≤ l.foldl (fun a x => if f x then a + 1 else a) acc := by
  intro l
  induction l with
  | nil => intro hp; exact absurd hp (by simp)
  | cons x rest ih =>
    intro hp acc
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hp with rfl | hp'
    · rw [if_pos hfp]
      exact le_foldl_count f rest (acc + 1)
    · cases hfx : f x with
      | true  => simp only [hfx, if_true]; have := ih hp' (acc + 1); omega
      | false =>
        simp only [hfx, Bool.false_eq_true, if_false]
        exact ih hp' acc

/-- Two *distinct* members satisfying `f` force the count to at least two.

This is what makes `isConsistent` bite: a unit holding the same digit in two different cells has
count `≥ 2`, contradicting the `≤ 1` the checker demands. -/
theorem two_le_foldl_count (f : Nat → Bool) {p q : Nat} (hpq : p ≠ q)
    (hfp : f p = true) (hfq : f q = true) :
    ∀ (l : List Nat), p ∈ l → q ∈ l → ∀ (acc : Nat),
      acc + 2 ≤ l.foldl (fun a x => if f x then a + 1 else a) acc := by
  intro l
  induction l with
  | nil => intro hp; exact absurd hp (by simp)
  | cons x rest ih =>
    intro hp hq acc
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hp with rfl | hp'
    · -- head is `p`, so `q` lies in the tail
      have hq' : q ∈ rest := by
        rcases List.mem_cons.mp hq with rfl | h
        · exact absurd rfl hpq
        · exact h
      rw [if_pos hfp]
      have := one_le_foldl_count f hfq rest hq' (acc + 1)
      omega
    · rcases List.mem_cons.mp hq with rfl | hq'
      · -- head is `q`, so `p` lies in the tail
        rw [if_pos hfq]
        have := one_le_foldl_count f hfp rest hp' (acc + 1)
        omega
      · cases hfx : f x with
        | true  => simp only [hfx, if_true]; have := ih hp' hq' (acc + 1); omega
        | false =>
          simp only [hfx, Bool.false_eq_true, if_false]
          exact ih hp' hq' acc

/-- With no member satisfying `f`, the count never moves. -/
theorem foldl_count_of_all_false (f : Nat → Bool) : ∀ (l : List Nat) (acc : Nat),
    (∀ x ∈ l, f x = false) → l.foldl (fun a x => if f x then a + 1 else a) acc = acc := by
  intro l
  induction l with
  | nil => intro acc _; rfl
  | cons x rest ih =>
    intro acc hall
    have hx : f x = false := hall x (List.mem_cons_self ..)
    simp only [List.foldl_cons, hx, Bool.false_eq_true, if_false]
    exact ih acc (fun y hy => hall y (List.mem_cons_of_mem _ hy))

/-- A nonzero count exhibits a member satisfying `f`. -/
theorem exists_of_foldl_count_ne (f : Nat → Bool) {l : List Nat} {acc : Nat}
    (h : l.foldl (fun a x => if f x then a + 1 else a) acc ≠ acc) : ∃ x ∈ l, f x = true := by
  refine Classical.byContradiction (fun hno => ?_)
  refine h (foldl_count_of_all_false f l acc ?_)
  intro x hx
  cases hfx : f x with
  | false => rfl
  | true => exact absurd ⟨x, hx, hfx⟩ hno

/-! ## Peers -//-! ## Peers -/

/-- `peers` contains exactly the other cells sharing a unit with `c`. -/
theorem mem_peers {c p : Nat} :
    p ∈ peers c ↔
      p < numCells ∧ p ≠ c ∧
        (rowOf p = rowOf c ∨ colOf p = colOf c ∨ boxOf p = boxOf c) := by
  unfold peers
  rw [Array.mem_filter]
  constructor
  · rintro ⟨hmem, hcond⟩
    refine ⟨Array.mem_range.mp hmem, ?_⟩
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.or_eq_true, beq_iff_eq] at hcond
    obtain ⟨hne, hshare⟩ := hcond
    refine ⟨hne, ?_⟩
    rcases hshare with (hr | hcol) | hb
    · exact Or.inl hr
    · exact Or.inr (Or.inl hcol)
    · exact Or.inr (Or.inr hb)
  · rintro ⟨hlt, hne, hshare⟩
    refine ⟨Array.mem_range.mpr hlt, ?_⟩
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.or_eq_true, beq_iff_eq]
    refine ⟨hne, ?_⟩
    rcases hshare with hr | hcol | hb
    · exact Or.inl (Or.inl hr)
    · exact Or.inl (Or.inr hcol)
    · exact Or.inr hb

/-! ## Block arithmetic

`omega` cannot relate `p / 9 / 3` to `p % 9 / 3` directly -- it treats them as unrelated atoms.
Splitting the reasoning into two one-level steps keeps every goal inside its reach. -/

/-- A column's block coordinate is below the block size. -/
theorem colOf_div_lt (c : Nat) : colOf c / blk < blk := by
  simp only [colOf, blk, n]; omega

/-- The block index recovers the row's block coordinate. -/
theorem boxOf_div (c : Nat) : boxOf c / blk = rowOf c / blk := by
  simp only [boxOf, blk] at *
  have h := colOf_div_lt c
  simp only [blk] at h
  omega

/-- The block index recovers the column's block coordinate. -/
theorem boxOf_mod (c : Nat) : boxOf c % blk = colOf c / blk := by
  simp only [boxOf, blk] at *
  have h := colOf_div_lt c
  simp only [blk] at h
  omega

/-- Cells in the same block agree on both block coordinates. -/
theorem box_coords {p c : Nat} (h : boxOf p = boxOf c) :
    rowOf p / blk = rowOf c / blk ∧ colOf p / blk = colOf c / blk :=
  ⟨by rw [← boxOf_div, ← boxOf_div, h], by rw [← boxOf_mod, ← boxOf_mod, h]⟩

/-! ## Units -/

/-- Row units are units. -/
theorem rowCells_mem_units {r : Nat} (hr : r < n) : rowCells r ∈ units := by
  unfold units
  refine Array.mem_append_left _ (Array.mem_append_left _ ?_)
  exact Array.mem_map.mpr ⟨r, Array.mem_range.mpr hr, rfl⟩

/-- Column units are units. -/
theorem colCells_mem_units {c : Nat} (hc : c < n) : colCells c ∈ units := by
  unfold units
  refine Array.mem_append_left _ (Array.mem_append_right _ ?_)
  exact Array.mem_map.mpr ⟨c, Array.mem_range.mpr hc, rfl⟩

/-- Block units are units. -/
theorem boxCells_mem_units {b : Nat} (hb : b < n) : boxCells b ∈ units := by
  unfold units
  refine Array.mem_append_right _ ?_
  exact Array.mem_map.mpr ⟨b, Array.mem_range.mpr hb, rfl⟩

/-- Every member of a unit is a cell index. -/
theorem unit_mem_lt {u : Array Nat} (hu : u ∈ units) {c : Nat} (hc : c ∈ u) : c < numCells := by
  unfold units at hu
  rcases Array.mem_append.mp hu with hu' | hb
  · rcases Array.mem_append.mp hu' with hr | hcol
    · obtain ⟨r, hrmem, rfl⟩ := Array.mem_map.mp hr
      obtain ⟨j, hjmem, rfl⟩ := Array.mem_map.mp hc
      have := Array.mem_range.mp hrmem
      have := Array.mem_range.mp hjmem
      simp only [cellIdx, numCells, n] at *; omega
    · obtain ⟨cc, hcmem, rfl⟩ := Array.mem_map.mp hcol
      obtain ⟨i, himem, rfl⟩ := Array.mem_map.mp hc
      have := Array.mem_range.mp hcmem
      have := Array.mem_range.mp himem
      simp only [cellIdx, numCells, n] at *; omega
  · obtain ⟨b, hbmem, rfl⟩ := Array.mem_map.mp hb
    obtain ⟨t, htmem, rfl⟩ := Array.mem_map.mp hc
    have := Array.mem_range.mp hbmem
    have := Array.mem_range.mp htmem
    have h1 : b / blk < blk := by simp only [blk, n] at *; omega
    have h2 : t / blk < blk := by simp only [blk, n] at *; omega
    have h3 : b % blk < blk := by simp only [blk]; omega
    have h4 : t % blk < blk := by simp only [blk]; omega
    simp only [cellIdx, numCells, n, blk] at *; omega

/-- A cell lies in its own row unit. -/
theorem self_mem_rowCells {c : Nat} (hc : c < numCells) : c ∈ rowCells (rowOf c) := by
  refine Array.mem_map.mpr ⟨colOf c, Array.mem_range.mpr ?_, ?_⟩
  · simp only [colOf, n, numCells] at *; omega
  · simp only [cellIdx, rowOf, colOf, n, numCells] at *; omega

/-- A cell lies in the row unit of any cell in the same row. -/
theorem mem_rowCells_of_rowOf_eq {p c : Nat} (hp : p < numCells) (h : rowOf p = rowOf c) :
    p ∈ rowCells (rowOf c) := by
  rw [← h]; exact self_mem_rowCells hp

/-! ## A peer never repeats a digit

`isConsistent` says every unit holds each digit exactly once. Two distinct cells of a common
unit carrying the same digit force the count to `2` (`two_le_foldl_count`), contradicting it. -/

/-- Unpack `isConsistent` at one unit and one digit: the digit occurs exactly once. -/
theorem consistent_at {h : Grid} (hcons : h.isConsistent = true)
    {u : Array Nat} (hu : u ∈ units) {k : Nat} (hk : k < n) :
    (u.toList.foldl (fun acc c => if h.get c == some k then acc + 1 else acc) 0) = 1 := by
  unfold Grid.isConsistent at hcons
  rw [Array.all_eq_true_iff_forall_mem] at hcons
  have h1 := hcons u hu
  rw [Array.all_eq_true_iff_forall_mem] at h1
  simpa using h1 k (Array.mem_range.mpr hk)

/-- In a consistent grid, two distinct cells of a common unit cannot share a digit. -/
theorem not_two_in_unit {h : Grid} (hcons : h.isConsistent = true)
    {u : Array Nat} (hu : u ∈ units) {p q k : Nat} (hk : k < n) (hpq : p ≠ q)
    (hpu : p ∈ u.toList) (hqu : q ∈ u.toList)
    (hpk : h.get p = some k) (hqk : h.get q = some k) : False := by
  have hle := consistent_at hcons hu hk
  have hfp : (h.get p == some k) = true := by rw [hpk]; simp
  have hfq : (h.get q == some k) = true := by rw [hqk]; simp
  have := two_le_foldl_count (fun c => h.get c == some k) hpq hfp hfq u.toList hpu hqu 0
  omega

/-- **A completion never repeats a digit between a cell and one of its peers.**

This is what licenses candidate elimination: the digits `usedByPeers` marks really are
impossible at `c`. -/
theorem peer_digit_excluded {h : Grid} (hcons : h.isConsistent = true)
    {c p k : Nat} (hc : c < numCells) (hk : k < n)
    (hp : p ∈ peers c) (hpk : h.get p = some k) : h.get c ≠ some k := by
  intro hck
  obtain ⟨hplt, hne, hshare⟩ := mem_peers.mp hp
  rcases hshare with hr | hcol | hb
  · -- same row
    exact not_two_in_unit hcons (rowCells_mem_units (by simp only [rowOf, n, numCells] at *; omega))
      hk hne
      (Array.mem_toList_iff.mpr (mem_rowCells_of_rowOf_eq hplt hr))
      (Array.mem_toList_iff.mpr (self_mem_rowCells hc)) hpk hck
  · -- same column
    have hcolLt : colOf c < n := by simp only [colOf, n, numCells] at *; omega
    have hpc : p ∈ colCells (colOf c) := by
      refine Array.mem_map.mpr ⟨rowOf p, Array.mem_range.mpr ?_, ?_⟩
      · simp only [rowOf, n, numCells] at *; omega
      · simp only [cellIdx, rowOf, colOf, n, numCells] at *; omega
    have hcc : c ∈ colCells (colOf c) := by
      refine Array.mem_map.mpr ⟨rowOf c, Array.mem_range.mpr ?_, ?_⟩
      · simp only [rowOf, n, numCells] at *; omega
      · simp only [cellIdx, rowOf, colOf, n, numCells] at *; omega
    exact not_two_in_unit hcons (colCells_mem_units hcolLt) hk hne
      (Array.mem_toList_iff.mpr hpc) (Array.mem_toList_iff.mpr hcc) hpk hck
  · -- same block
    have hbLt : boxOf c < n := by
      have hd := boxOf_div c
      have hm := boxOf_mod c
      have h1 : rowOf c / blk < blk := by simp only [rowOf, blk, n, numCells] at *; omega
      have h2 := colOf_div_lt c
      simp only [boxOf, blk, n] at *
      omega
    have hmem : ∀ q, q < numCells → boxOf q = boxOf c → q ∈ boxCells (boxOf c) := by
      intro q hq hbq
      obtain ⟨hr, hcl⟩ := box_coords hbq
      refine Array.mem_map.mpr ⟨(rowOf q % blk) * blk + (colOf q % blk),
        Array.mem_range.mpr ?_, ?_⟩
      · have : rowOf q % blk < blk := by simp only [blk]; omega
        have : colOf q % blk < blk := by simp only [blk]; omega
        simp only [blk, n] at *; omega
      · have hlt : colOf q % blk < blk := by simp only [blk]; omega
        have ht1 : ((rowOf q % blk) * blk + (colOf q % blk)) / blk = rowOf q % blk := by
          simp only [blk] at *; omega
        have ht2 : ((rowOf q % blk) * blk + (colOf q % blk)) % blk = colOf q % blk := by
          simp only [blk] at *; omega
        have hbd : boxOf c / blk = rowOf q / blk := by rw [boxOf_div, ← hr]
        have hbm : boxOf c % blk = colOf q / blk := by rw [boxOf_mod, ← hcl]
        rw [hbd, hbm, ht1, ht2]
        simp only [cellIdx, rowOf, colOf, blk, n, numCells] at *; omega
    exact not_two_in_unit hcons (boxCells_mem_units hbLt) hk hne
      (Array.mem_toList_iff.mpr (hmem p hplt hb))
      (Array.mem_toList_iff.mpr (hmem c hc rfl)) hpk hck

/-! ## Naked singles are forced

A cell of a completion carries *some* legal digit, and `peer_digit_excluded` rules out every
digit its peers already use. If `buildFlags` leaves exactly one digit free at that cell, the
completion has no choice. -/

/-- In a completion every cell carries a legal digit. -/
theorem exists_digit {g h : Grid} (hh : Completes g h) {c : Nat} (hc : c < numCells) :
    ∃ k, k < n ∧ h.get c = some k := by
  obtain ⟨hwf, hsol, _⟩ := hh
  simp only [Grid.isSolution, Grid.isComplete, Grid.digitsInRange, Bool.and_eq_true] at hsol
  obtain ⟨⟨⟨_, hrange⟩, hcomp⟩, _⟩ := hsol
  have hlt : c < h.cells.size := by rw [hwf]; exact hc
  have hmem : h.cells[c] ∈ h.cells := Array.getElem_mem hlt
  have hget : h.get c = h.cells[c] := by
    unfold Grid.get
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt]
    rfl
  -- completeness gives `isSome`, range gives the bound
  rw [Array.all_eq_true_iff_forall_mem] at hcomp hrange
  have h1 := hcomp _ hmem
  have h2 := hrange _ hmem
  cases hv : h.cells[c] with
  | none => rw [hv] at h1; simp at h1
  | some k =>
    refine ⟨k, ?_, by rw [hget, hv]⟩
    rw [hv] at h2
    simpa using h2

/-! ## `buildFlags` -/

/-- The variable index of digit `k` in cell `c`, in terms of `c` itself. -/
theorem varIdx_of_cell {c k : Nat} (hc : c < numCells) :
    varIdx (rowOf c) (colOf c) k = c * n + k := by
  simp only [varIdx, rowOf, colOf, n, numCells] at *; omega

/-- `buildFlags` reads off `flagOf` at each variable index. -/
theorem buildFlags_snd (g : Grid) {v : Nat} (hv : v < numVars) :
    (buildFlags g).2.getD v false = (flagOf g v).2 := by
  unfold buildFlags
  have hsz : ((Array.range numVars).map (fun v => (flagOf g v).2)).size = numVars := by simp
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by rw [hsz]; exact hv)]
  simp

/-- At an empty cell, a digit is free exactly when no peer uses it.

This is the specification of Algorithm 1's candidate elimination. -/
theorem free_iff_empty {g : Grid} {c : Nat} (hc : c < numCells) (hempty : g.get c = none)
    {k : Nat} (hk : k < n) :
    free (buildFlags g).2 (rowOf c) (colOf c) k = true ↔ ∀ p ∈ peers c, g.get p ≠ some k := by
  have hvar : varIdx (rowOf c) (colOf c) k = c * n + k := varIdx_of_cell hc
  have hlt : c * n + k < numVars := by simp only [numVars, numCells, n] at *; omega
  have hdiv : (c * n + k) / n = c := by simp only [n] at *; omega
  have hmod : (c * n + k) % n = k := by simp only [n] at *; omega
  have hflag : (flagOf g (c * n + k)).2
      = (if (usedByPeers g c).getD k false then true else false) := by
    simp only [flagOf, hdiv, hmod, hempty]
    by_cases hu : (usedByPeers g c).getD k false = true <;> simp [hu]
  simp only [free, hvar, buildFlags_snd g hlt, hflag]
  constructor
  · intro hfree p hp hpk
    have hused : (usedByPeers g c).getD k false = true :=
      (usedByPeers_spec g c k hk).mpr ⟨p, Array.mem_toList_iff.mpr hp, hpk⟩
    rw [hused] at hfree
    simp at hfree
  · intro hno
    have hnu : (usedByPeers g c).getD k false = false := by
      cases hq : (usedByPeers g c).getD k false with
      | false => rfl
      | true =>
        obtain ⟨p, hp, hpk⟩ := (usedByPeers_spec g c k hk).mp hq
        exact absurd hpk (hno p (Array.mem_toList_iff.mp hp))
    rw [hnu]
    simp

/-- A digit `buildFlags` has eliminated at an empty cell is impossible there in any completion.

This is the soundness of candidate elimination: `peer_digit_excluded` says a completion cannot
repeat a peer's digit, and `usedByPeers_spec` says eliminated digits are exactly the peers'. -/
theorem not_free_excluded {g h : Grid} (hh : Completes g h) {c : Nat} (hc : c < numCells)
    (hempty : g.get c = none) {k : Nat} (hk : k < n)
    (hnotfree : free (buildFlags g).2 (rowOf c) (colOf c) k = false) : h.get c ≠ some k := by
  have hvar : varIdx (rowOf c) (colOf c) k = c * n + k := varIdx_of_cell hc
  have hlt : c * n + k < numVars := by simp only [numVars, numCells, n] at *; omega
  have hdiv : (c * n + k) / n = c := by simp only [n] at *; omega
  have hmod : (c * n + k) % n = k := by simp only [n] at *; omega
  have hset : (buildFlags g).2.getD (c * n + k) false = true := by
    simp only [free, hvar] at hnotfree
    simpa using hnotfree
  rw [buildFlags_snd g hlt] at hset
  simp only [flagOf, hdiv, hmod, hempty] at hset
  have hused : (usedByPeers g c).getD k false = true := by
    cases hq : (usedByPeers g c).getD k false with
    | true => rfl
    | false => rw [hq] at hset; simp at hset
  obtain ⟨p, hp, hpk⟩ := (usedByPeers_spec g c k hk).mp hused
  have hpm := Array.mem_toList_iff.mp hp
  obtain ⟨hplt, _, _⟩ := mem_peers.mp hpm
  have hph : h.get p = some k := (extends'_iff g h).mp hh.2.2 p hplt k hpk
  have hcons : h.isConsistent = true := by
    have hs := hh.2.1
    simp only [Grid.isSolution, Bool.and_eq_true] at hs
    exact hs.2
  exact peer_digit_excluded hcons hc hk hpm hph

/-! ## Naked singles are forced -/

/-- Inversion for `nakedSingle?`: a hit names an empty cell at which `k` is free and is the
*only* free digit. -/
theorem nakedSingle_inv {g : Grid} {d : Array Bool} {c k : Nat}
    (hfind : nakedSingle? g d = some (c, k)) :
    c < numCells ∧ g.get c = none ∧ free d (rowOf c) (colOf c) k = true ∧
      (∀ t, free d (rowOf c) (colOf c) t = true → t < n → t = k) := by
  unfold nakedSingle? at hfind
  rw [← Array.findSome?_toList] at hfind
  obtain ⟨c', hc'mem, hc'eq⟩ := List.exists_of_findSome?_eq_some hfind
  have hc'lt : c' < numCells := Array.mem_range.mp (Array.mem_toList_iff.mp hc'mem)
  by_cases hsome : (g.get c').isSome = true
  · rw [if_pos hsome] at hc'eq; simp at hc'eq
  · rw [if_neg hsome] at hc'eq
    by_cases hone :
        ((Array.range n).filter (fun t => free d (rowOf c') (colOf c') t)).size == 1
    · rw [if_pos hone] at hc'eq
      cases h0 : ((Array.range n).filter (fun t => free d (rowOf c') (colOf c') t))[0]? with
      | none => rw [h0] at hc'eq; simp at hc'eq
      | some k0 =>
        rw [h0] at hc'eq
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hc'eq
        obtain ⟨rfl, rfl⟩ := hc'eq
        -- the filtered array is a singleton `[k]`
        have hsz : ((Array.range n).filter
            (fun t => free d (rowOf c') (colOf c') t)).size = 1 := by simpa using hone
        have hlen : ((Array.range n).filter
            (fun t => free d (rowOf c') (colOf c') t)).toList.length = 1 := by
          rw [Array.length_toList]; exact hsz
        obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp hlen
        -- a list-singleton array is `#[a]`, which pins `k0 = a`
        have harr : ((Array.range n).filter (fun t => free d (rowOf c') (colOf c') t)) = #[a] :=
          Array.toList_inj.mp (by simpa using ha)
        have hak : a = k0 := by
          rw [harr] at h0
          simpa using h0
        subst hak
        have hmemk : a ∈ (Array.range n).filter (fun t => free d (rowOf c') (colOf c') t) := by
          rw [harr]; simp
        obtain ⟨_, hfreek⟩ := Array.mem_filter.mp hmemk
        refine ⟨hc'lt, by simpa using hsome, hfreek, ?_⟩
        intro t hft htn
        have hmemt : t ∈ (Array.range n).filter (fun t => free d (rowOf c') (colOf c') t) :=
          Array.mem_filter.mpr ⟨Array.mem_range.mpr htn, hft⟩
        rw [← Array.mem_toList_iff, ha] at hmemt
        exact List.mem_singleton.mp hmemt
    · rw [if_neg hone] at hc'eq; simp at hc'eq

/-- **A naked single is forced.**

If `buildFlags` leaves exactly one digit free at an empty cell, every completion writes that
digit there: the cell holds *some* legal digit (`exists_digit`), and every excluded digit is
impossible (`not_free_excluded`). -/
theorem nakedSingle_forced {g : Grid} {c k : Nat}
    (hfind : nakedSingle? g (buildFlags g).2 = some (c, k))
    {h : Grid} (hh : Completes g h) : h.get c = some k := by
  obtain ⟨hc, hempty, _, huniq⟩ := nakedSingle_inv hfind
  obtain ⟨k', hk', hk'val⟩ := exists_digit hh hc
  by_cases hfree : free (buildFlags g).2 (rowOf c) (colOf c) k' = true
  · rw [hk'val, huniq k' hfree hk']
  · rw [Bool.not_eq_true] at hfree
    exact absurd hk'val (not_free_excluded hh hc hempty hk' hfree)

/-! ## Hidden singles are forced -/

/-- Inversion for `hiddenSingle?`: a hit names a unit that lacks the digit, in which exactly one
empty cell can still take it. -/
theorem hiddenSingle_inv {g : Grid} {d : Array Bool} {c k : Nat}
    (hfind : hiddenSingle? g d = some (c, k)) :
    ∃ u ∈ units, k < n ∧ (∀ q ∈ u, g.get q ≠ some k) ∧ c ∈ u ∧ g.get c = none ∧
      (∀ t ∈ u, g.get t = none → free d (rowOf t) (colOf t) k = true → t = c) := by
  unfold hiddenSingle? at hfind
  rw [← Array.findSome?_toList] at hfind
  obtain ⟨u, humem, hueq⟩ := List.exists_of_findSome?_eq_some hfind
  have hu : u ∈ units := Array.mem_toList_iff.mp humem
  rw [← Array.findSome?_toList] at hueq
  obtain ⟨k', hk'mem, hk'eq⟩ := List.exists_of_findSome?_eq_some hueq
  have hk'lt : k' < n := Array.mem_range.mp (Array.mem_toList_iff.mp hk'mem)
  by_cases hany : u.any (fun q => g.get q == some k') = true
  · rw [if_pos hany] at hk'eq; simp at hk'eq
  · rw [if_neg hany] at hk'eq
    by_cases hone :
        (u.filter (fun q => (g.get q).isNone && free d (rowOf q) (colOf q) k')).size == 1
    · rw [if_pos hone] at hk'eq
      cases h0 : (u.filter (fun q => (g.get q).isNone && free d (rowOf q) (colOf q) k'))[0]? with
      | none => rw [h0] at hk'eq; simp at hk'eq
      | some c0 =>
        rw [h0] at hk'eq
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hk'eq
        obtain ⟨rfl, rfl⟩ := hk'eq
        have hsz : (u.filter (fun q => (g.get q).isNone && free d (rowOf q) (colOf q) k')).size
            = 1 := by simpa using hone
        have hlen : (u.filter
            (fun q => (g.get q).isNone && free d (rowOf q) (colOf q) k')).toList.length = 1 := by
          rw [Array.length_toList]; exact hsz
        obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp hlen
        have harr : (u.filter (fun q => (g.get q).isNone && free d (rowOf q) (colOf q) k'))
            = #[a] := Array.toList_inj.mp (by simpa using ha)
        have hac : a = c0 := by rw [harr] at h0; simpa using h0
        subst hac
        have hmema : a ∈ u.filter (fun q => (g.get q).isNone && free d (rowOf q) (colOf q) k') := by
          rw [harr]; simp
        obtain ⟨hau, hapred⟩ := Array.mem_filter.mp hmema
        have haempty : g.get a = none := by
          simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hapred
          exact hapred.1
        -- no cell of the unit already carries the digit
        have hnone : ∀ q ∈ u, g.get q ≠ some k' := by
          intro q hq hqk
          refine hany ?_
          refine Array.any_eq_true'.mpr ⟨q, hq, ?_⟩
          rw [hqk]; simp
        refine ⟨u, hu, hk'lt, hnone, hau, haempty, ?_⟩
        intro t htu htnone htfree
        have hmemt : t ∈ u.filter (fun q => (g.get q).isNone && free d (rowOf q) (colOf q) k') :=
          Array.mem_filter.mpr ⟨htu, by simp [htnone, htfree]⟩
        rw [harr] at hmemt
        simpa using hmemt
    · rw [if_neg hone] at hk'eq; simp at hk'eq

/-- **A hidden single is forced.**

A completion places every digit exactly once in every unit (`isConsistent`). If the puzzle has
not yet placed `k` in that unit, the cell carrying it must be one still empty; every such cell
whose candidate `k` was eliminated is impossible (`not_free_excluded`); so if exactly one
survives, the completion writes `k` there. -/
theorem hiddenSingle_forced {g : Grid} {c k : Nat}
    (hfind : hiddenSingle? g (buildFlags g).2 = some (c, k))
    {h : Grid} (hh : Completes g h) : h.get c = some k := by
  obtain ⟨u, hu, hk, hnone, hcu, _, huniq⟩ := hiddenSingle_inv hfind
  have hcons : h.isConsistent = true := by
    have hs := hh.2.1
    simp only [Grid.isSolution, Bool.and_eq_true] at hs
    exact hs.2
  -- the digit occurs exactly once in this unit of the completion
  have hcount := consistent_at hcons hu hk
  obtain ⟨c', hc'u, hc'k⟩ :=
    exists_of_foldl_count_ne (fun q => h.get q == some k) (by rw [hcount]; omega)
  have hc'val : h.get c' = some k := by simpa using hc'k
  have hc'mem : c' ∈ u := Array.mem_toList_iff.mp hc'u
  -- that cell is empty in the puzzle: a given there would have to be `k`, which the unit lacks
  have hc'lt : c' < numCells := unit_mem_lt hu hc'mem
  have hc'empty : g.get c' = none := by
    cases hq : g.get c' with
    | none => rfl
    | some dg =>
      have : h.get c' = some dg := (extends'_iff g h).mp hh.2.2 c' hc'lt dg hq
      rw [hc'val] at this
      exact absurd (hq.trans (congrArg some (Option.some.inj this).symm)) (hnone c' hc'mem)
  -- and `k` is still a candidate there, else the completion could not use it
  have hc'free : free (buildFlags g).2 (rowOf c') (colOf c') k = true := by
    cases hf : free (buildFlags g).2 (rowOf c') (colOf c') k with
    | true => rfl
    | false => exact absurd hc'val (not_free_excluded hh hc'lt hc'empty hk hf)
  rw [← huniq c' hc'mem hc'empty hc'free]
  exact hc'val

/-! ## Writing a forced digit changes nothing -/

/-- `assign` preserves the cell count. -/
theorem assign_wf {g : Grid} (hg : g.WF) (c k : Nat) : (g.assign c k).WF := by
  unfold Grid.WF Grid.assign at *
  simpa using hg

/-- Reading back an assignment at the cell written. -/
theorem assign_get_self {g : Grid} {c k : Nat} (hc : c < g.cells.size) :
    (g.assign c k).get c = some k := by
  unfold Grid.assign Grid.get
  rw [Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds,
    Array.getElem?_setIfInBounds_self_of_lt hc]
  rfl

/-- Reading back an assignment elsewhere. -/
theorem assign_get_ne {g : Grid} {c k c' : Nat} (hne : c' ≠ c) :
    (g.assign c k).get c' = g.get c' := by
  unfold Grid.assign Grid.get
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
    Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne (Ne.symm hne)]

/-- **Writing a forced digit into an empty cell changes no completion.**

Every completion already had that digit there, so nothing is lost; and the extended grid has
strictly more givens, so nothing is gained. -/
theorem assign_preserves {g : Grid} (hg : g.WF) {c k : Nat} (hc : c < numCells)
    (hempty : g.get c = none) (hforced : ∀ h, Completes g h → h.get c = some k) (h : Grid) :
    Completes g h ↔ Completes (g.assign c k) h := by
  have hcs : c < g.cells.size := by rw [hg]; exact hc
  constructor
  · rintro hh
    refine ⟨hh.1, hh.2.1, ?_⟩
    rw [extends'_iff]
    intro c' hc' d hd
    by_cases hcc : c' = c
    · subst hcc
      rw [assign_get_self hcs] at hd
      rw [← Option.some.inj hd]
      exact hforced h hh
    · rw [assign_get_ne hcc] at hd
      exact (extends'_iff g h).mp hh.2.2 c' hc' d hd
  · rintro hh
    refine ⟨hh.1, hh.2.1, ?_⟩
    rw [extends'_iff]
    intro c' hc' d hd
    by_cases hcc : c' = c
    · subst hcc; rw [hempty] at hd; simp at hd
    · exact (extends'_iff _ h).mp hh.2.2 c' hc' d (by rw [assign_get_ne hcc]; exact hd)

/-! ## Algorithm 1 preserves the solution set -/

/-- The fuel-bounded loop of Algorithm 1 preserves completions at every step. -/
theorem reduceFuel_completions : ∀ (fuel : Nat) (g : Grid), g.WF → ∀ (r : Nat) (h : Grid),
    Completes g h ↔ Completes (reduceFuel fuel g r).1 h := by
  intro fuel
  induction fuel with
  | zero => intro g _ r h; exact Iff.rfl
  | succ fuel ih =>
    intro g hg r h
    show Completes g h ↔ Completes (reduceFuel (fuel + 1) g r).1 h
    unfold reduceFuel
    cases hn : nakedSingle? g (buildFlags g).2 with
    | some ck =>
      obtain ⟨c, k⟩ := ck
      obtain ⟨hc, hempty, _, _⟩ := nakedSingle_inv hn
      have hstep := assign_preserves hg hc hempty (fun h' hh' => nakedSingle_forced hn hh') h
      simp only [hn]
      exact hstep.trans (ih (g.assign c k) (assign_wf hg c k) (r + 1) h)
    | none =>
      cases hh2 : hiddenSingle? g (buildFlags g).2 with
      | some ck =>
        obtain ⟨c, k⟩ := ck
        obtain ⟨u, hu, hk, _, hcu, hempty, _⟩ := hiddenSingle_inv hh2
        have hc : c < numCells := unit_mem_lt hu hcu
        have hstep := assign_preserves hg hc hempty (fun h' hh' => hiddenSingle_forced hh2 hh') h
        simp only [hn, hh2]
        exact hstep.trans (ih (g.assign c k) (assign_wf hg c k) (r + 1) h)
      | none => simp only [hn, hh2]

/-- **Algorithm 1 is sound: it preserves the solution set exactly.**

The grid the reduction returns has precisely the completions the input puzzle had. This is what
makes Table I meaningful -- "729 → 171" counts variables the reduction may safely delete, not
solutions it discarded. -/
theorem reduce_completions {g : Grid} (hg : g.WF) (h : Grid) :
    Completes g h ↔ Completes (reduce g).grid h := by
  unfold reduce
  exact reduceFuel_completions numCells g hg 0 h

/-! ## What this file establishes, and what it does not

`reduce_completions` is closed: both deductions are proved forced (`nakedSingle_forced`,
`hiddenSingle_forced`), writing a forced digit preserves the completion set
(`assign_preserves`), and the fuel-bounded loop preserves it at every step
(`reduceFuel_completions`). No axiom beyond `propext`/`Classical.choice`/`Quot.sound`, no
`sorry`.

What is *not* here is the other half of §IV. Algorithm 1 decides which variables to delete;
`Problem.ofReduced` then actually deletes them and rebuilds `Â`, `b̂`, `θ̂`. That the rebuilt
objective agrees with the original — `Problem.penaltyDoubled P x = CNS.penaltyDoubled (P.embed x)`
— is the remaining bridge, and it lives in `Problem.lean`, not here. It is currently checked
executably (1000 random trials per instance, `cns reduced`) rather than proved. -/

end CNS
