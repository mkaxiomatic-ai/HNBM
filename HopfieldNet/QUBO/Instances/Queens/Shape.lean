/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.QUBO.Instances.Queens.Basic

/-!
# The shape of the queens system

`prop:sizes` of the paper asserts three things about the incidence `Â` of `QUBO.Queens.problem`, and
before this file none of them was a theorem: the counts were the definitions `nvars` and `nrows`, the
degrees were checked by `#guard` at particular board sizes, and the claim that `Âᵀ Â` is `0/1` off
its diagonal had no counterpart at all. All three are proved here, for a general board size.

* `nvars_eq`, `nrows_eq` — the closed forms `N² + 4N - 6` and `6N - 6 + |G|`, for `N ≥ 2`. The
  hypothesis is necessary: `ndiags = 2N - 3` truncates, so a `1 × 1` board has one neuron and two
  rows while both closed forms give `0`.
* `rowsOf_size_slackVar`, `rowsOf_size_cellVar`, `countP_onSlack_eq` — the degree of every neuron.
  Note the general form: a square's degree counts **one row per entry of `givens` naming it**, so a
  repeated given raises the degree. `⟨8, #[(3,3),(3,3),(3,3)]⟩` passes `givensOk` and has a neuron
  of degree `7`, which is why the paper's `deg(u) ∈ {1,3,4,5}` holds only when the givens are
  duplicate-free.
* `countP_shared_le_one` — two distinct neurons lie together in at most one row. This one needs no
  hypothesis on the givens, since a given row pins a single square and so is shared by nothing.
-/

namespace QUBO
namespace Queens
variable (I : Instance)

/-! ## The counts -/

/-- **The neuron count**, in the closed form the paper prints. -/
theorem nvars_eq (hN : 2 ≤ I.size) : I.nvars = I.size ^ 2 + 4 * I.size - 6 := by
  simp only [Instance.nvars, Instance.ncells, Instance.ndiags, pow_two]
  generalize I.size * I.size = s
  omega

/-- **The row count**, likewise. -/
theorem nrows_eq (hN : 2 ≤ I.size) : I.nrows = 6 * I.size - 6 + I.ngivens := by
  simp only [Instance.nrows, Instance.nbase, Instance.ndiags]
  omega

/-! ## The degrees -/
variable (I : Instance)

/-! ## Counting a predicate over an index range -/

/-- A predicate with a **unique** witness below `n` is counted once over `List.range n`. -/
private theorem countP_range_eq_one {n a : Nat} (ha : a < n) {p : Nat → Bool}
    (hp : ∀ b, b < n → (p b = true ↔ b = a)) : (List.range n).countP p = 1 := by
  have h : (List.range n).countP p = (List.range n).countP (fun b => b == a) := by
    refine List.countP_congr fun b hb => ?_
    rw [hp b (List.mem_range.mp hb)]
    simp
  rw [h, ← List.count_eq_countP]
  exact List.count_eq_one_of_mem List.nodup_range (List.mem_range.mpr ha)

/-- A predicate with **no** witness below `n` is counted zero times over `List.range n`. -/
private theorem countP_range_eq_zero {n : Nat} {p : Nat → Bool}
    (hp : ∀ b, b < n → p b = false) : (List.range n).countP p = 0 :=
  List.countP_eq_zero.mpr fun b hb => by rw [hp b (List.mem_range.mp hb)]; simp

/-- Reading a `Bool` off as `false` from its characterisation. -/
private theorem eq_false_of_iff {b : Bool} {P : Prop} (h : b = true ↔ P) (hP : ¬ P) :
    b = false := by
  cases b
  · rfl
  · exact absurd (h.mp rfl) hP

/-- Splitting a count over an index range into four consecutive blocks. -/
private theorem countP_range_split (p : Nat → Bool) (a b c d : Nat) :
    (List.range (a + b + c + d)).countP p
      = (List.range a).countP p + (List.range b).countP (fun t => p (a + t))
        + (List.range c).countP (fun t => p (a + b + t))
        + (List.range d).countP (fun t => p (a + b + c + t)) := by
  rw [List.range_add (n := a + b + c) (m := d), List.countP_append, List.countP_map,
    List.range_add (n := a + b) (m := c), List.countP_append, List.countP_map,
    List.range_add (n := a) (m := b), List.countP_append, List.countP_map]
  simp only [Function.comp_def]

/-- Counting over a list is counting over its index range. -/
private theorem countP_range_getD {α : Type*} (p : α → Bool) (d : α) : ∀ (l : List α),
    (List.range l.length).countP (fun i => p (l.getD i d)) = l.countP p := by
  intro l
  induction l with
  | nil => simp
  | cons x t ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.countP_cons, List.countP_map,
      List.countP_cons]
    simp only [Function.comp_def, List.getD_cons_succ, List.getD_cons_zero, ih]

/-! ## The degree, split over the four row families -/

/-- **The four blocks of the incidence.** `nbase = N + N + 2D + G`, and the four block index maps
are exactly `rowRow`, `colRow`, `slackRow`, `givRow`, so each summand is read by the
corresponding `baseInRow_*` lemma of `Queens.Basic`. -/
theorem baseRowList_length_split (u : Nat) :
    (I.baseRowList u).length
      = (List.range I.size).countP (fun i => I.baseInRow u (I.rowRow i))
        + (List.range I.size).countP (fun j => I.baseInRow u (I.colRow j))
        + (List.range (2 * I.ndiags)).countP (fun e => I.baseInRow u (I.slackRow e))
        + (List.range I.ngivens).countP (fun k => I.baseInRow u (I.givRow k)) := by
  have hb : I.nbase = I.size + I.size + 2 * I.ndiags + I.ngivens := by
    simp only [Instance.nbase]; omega
  rw [Instance.baseRowList, ← List.countP_eq_length_filter, hb,
    countP_range_split (fun r => I.baseInRow u r) I.size I.size (2 * I.ndiags) I.ngivens]
  simp only [Instance.rowRow, Instance.colRow, Instance.slackRow, Instance.givRow,
    show I.size + I.size = 2 * I.size from by omega]

/-! ## An auxiliary neuron lies in exactly one row -/

/-- A slack meets its own diagonal row and nothing else. -/
theorem baseRowList_length_slackVar {e : Nat} (he : e < 2 * I.ndiags) :
    (I.baseRowList (I.slackVar e)).length = 1 := by
  have hN : 2 ≤ I.size := I.two_le_size_of_slack he
  have hu : ¬ (I.slackVar e < I.ncells) := by simp only [Instance.slackVar]; omega
  have h1 : (List.range I.size).countP
      (fun i => I.baseInRow (I.slackVar e) (I.rowRow i)) = 0 := by
    exact countP_range_eq_zero fun i hi => eq_false_of_iff (I.baseInRow_rowRow hi) fun h => hu h.1
  have h2 : (List.range I.size).countP
      (fun j => I.baseInRow (I.slackVar e) (I.colRow j)) = 0 := by
    exact countP_range_eq_zero fun j hj => eq_false_of_iff (I.baseInRow_colRow hj) fun h => hu h.1
  have h3 : (List.range (2 * I.ndiags)).countP
      (fun e' => I.baseInRow (I.slackVar e) (I.slackRow e')) = 1 := by
    refine countP_range_eq_one he ?_
    intro e' he'
    rw [I.baseInRow_slackRow he']
    constructor
    · rintro (⟨hc, -⟩ | hh)
      · exact absurd hc hu
      · simp only [Instance.slackVar] at hh; omega
    · rintro rfl; exact Or.inr rfl
  have h4 : (List.range I.ngivens).countP
      (fun k => I.baseInRow (I.slackVar e) (I.givRow k)) = 0 := by
    refine countP_range_eq_zero fun k hk => ?_
    have hk' : k < I.givens.size := hk
    exact eq_false_of_iff (I.baseInRow_givRow (Array.getElem?_eq_getElem hk')) fun h => hu h.1
  rw [baseRowList_length_split, h1, h2, h3, h4]

/-- **(a) An auxiliary neuron lies in exactly one row.** -/
theorem rowsOf_size_slackVar {e : Nat} (he : e < 2 * I.ndiags) :
    (I.rowsOf (I.slackVar e)).size = 1 := by
  rw [I.rowsOf_size, baseRowList_length_slackVar I he]

/-! ## The degree of a square -/

/-- **(b) A square's degree** splits into its board row, its column, its diagonals and its
givens. -/
theorem rowsOf_size_cellVar {i j : Nat} (hN : 2 ≤ I.size) (hi : i < I.size) (hj : j < I.size) :
    (I.rowsOf (I.cellVar i j)).size
      = 2 + ((List.range (2 * I.ndiags)).countP (fun e => I.onSlack i j e))
          + (I.givens.toList.countP (fun p => p == (i, j))) := by
  -- `hN` is not needed for the split: on a board with no diagonal of length `≥ 2` the middle
  -- summand is a count over `List.range 0`. It is kept for uniformity with (c).
  have _hN : 0 < I.size := Nat.lt_of_lt_of_le Nat.zero_lt_two hN
  have hlt : I.cellVar i j < I.ncells := I.cellVar_lt hi hj
  have hdiv : I.cellVar i j / I.size = i := I.cellVar_div hj
  have hmod : I.cellVar i j % I.size = j := I.cellVar_mod hj
  have h1 : (List.range I.size).countP
      (fun i' => I.baseInRow (I.cellVar i j) (I.rowRow i')) = 1 := by
    refine countP_range_eq_one hi ?_
    intro b hb
    rw [I.baseInRow_rowRow hb, hdiv]
    exact ⟨fun h => h.2.symm, fun h => ⟨hlt, h.symm⟩⟩
  have h2 : (List.range I.size).countP
      (fun j' => I.baseInRow (I.cellVar i j) (I.colRow j')) = 1 := by
    refine countP_range_eq_one hj ?_
    intro b hb
    rw [I.baseInRow_colRow hb, hmod]
    exact ⟨fun h => h.2.symm, fun h => ⟨hlt, h.symm⟩⟩
  have h3 : (List.range (2 * I.ndiags)).countP
      (fun e => I.baseInRow (I.cellVar i j) (I.slackRow e))
      = (List.range (2 * I.ndiags)).countP (fun e => I.onSlack i j e) := by
    refine List.countP_congr fun e he => ?_
    rw [I.baseInRow_slackRow (List.mem_range.mp he), hdiv, hmod]
    constructor
    · rintro (⟨-, h⟩ | h)
      · exact h
      · exfalso; simp only [Instance.slackVar] at h; omega
    · exact fun h => Or.inl ⟨hlt, h⟩
  have h4 : (List.range I.ngivens).countP
      (fun k => I.baseInRow (I.cellVar i j) (I.givRow k))
      = I.givens.toList.countP (fun p => p == (i, j)) := by
    rw [← countP_range_getD (fun p => p == (i, j)) ((0, 0) : Nat × Nat) I.givens.toList,
      show I.givens.toList.length = I.ngivens from by simp [Instance.ngivens]]
    refine List.countP_congr fun k hk => ?_
    have hk' : k < I.givens.size := List.mem_range.mp hk
    have hp : I.givens[k]? = some I.givens[k] := Array.getElem?_eq_getElem hk'
    have hgetD : I.givens.toList.getD k ((0, 0) : Nat × Nat) = I.givens[k] := by
      rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, hp]; rfl
    rw [I.baseInRow_givRow hp, hdiv, hmod, hgetD]
    simp only [beq_iff_eq, Prod.ext_iff]
    exact ⟨fun h => ⟨h.2.1, h.2.2⟩, fun h => ⟨hlt, h.1, h.2⟩⟩
  rw [I.rowsOf_size, baseRowList_length_split, h1, h2, h3, h4]

/-! ## The diagonal count: `1` at a corner, `2` elsewhere -/

/-- The `2D` diagonal rows split into the `D` difference diagonals and the `D` sum diagonals. -/
private theorem countP_onSlack_split (i j : Nat) :
    (List.range (2 * I.ndiags)).countP (fun e => I.onSlack i j e)
      = (List.range I.ndiags).countP (fun e => I.onSlack i j e)
        + (List.range I.ndiags).countP (fun t => I.onSlack i j (I.ndiags + t)) := by
  rw [show 2 * I.ndiags = I.ndiags + I.ndiags from by omega, List.range_add,
    List.countP_append, List.countP_map]
  simp only [Function.comp_def]

/-- The **difference** direction contributes one row unless the cell is one of the two corners
`(0, N−1)`, `(N−1, 0)` whose difference diagonal has length one. -/
private theorem countP_onSlack_lo (i j : Nat) (hN : 2 ≤ I.size) :
    (List.range I.ndiags).countP (fun e => I.onSlack i j e)
      = if j + 2 ≤ i + I.size ∧ i + 1 < I.size + j then 1 else 0 := by
  have hnd : I.ndiags = 2 * I.size - 3 := rfl
  by_cases h : j + 2 ≤ i + I.size ∧ i + 1 < I.size + j
  · rw [if_pos h]
    refine countP_range_eq_one (a := i + I.size - 2 - j) (by omega) ?_
    intro e he
    rw [I.onSlack_lo he]
    omega
  · rw [if_neg h]
    exact countP_range_eq_zero fun e he => eq_false_of_iff (I.onSlack_lo he) (by omega)

/-- The **sum** direction contributes one row unless the cell is one of the two corners `(0,0)`,
`(N−1, N−1)` whose anti-diagonal has length one. -/
private theorem countP_onSlack_hi (i j : Nat) (hN : 2 ≤ I.size) :
    (List.range I.ndiags).countP (fun t => I.onSlack i j (I.ndiags + t))
      = if 1 ≤ i + j ∧ i + j + 2 < 2 * I.size then 1 else 0 := by
  have hnd : I.ndiags = 2 * I.size - 3 := rfl
  by_cases h : 1 ≤ i + j ∧ i + j + 2 < 2 * I.size
  · rw [if_pos h]
    refine countP_range_eq_one (a := i + j - 1) (by omega) ?_
    intro t ht
    rw [I.onSlack_hi (by omega : ¬ (I.ndiags + t < I.ndiags))]
    omega
  · rw [if_neg h]
    exact countP_range_eq_zero fun t ht =>
      eq_false_of_iff (I.onSlack_hi (by omega : ¬ (I.ndiags + t < I.ndiags))) (by omega)

/-- **(c) The diagonal count is `1` at a corner and `2` elsewhere.** Each direction contributes
`0` or `1`, and the two directions fail on disjoint pairs of corners. -/
theorem countP_onSlack_eq {i j : Nat} (hN : 2 ≤ I.size) (hi : i < I.size) (hj : j < I.size) :
    (List.range (2 * I.ndiags)).countP (fun e => I.onSlack i j e)
      = if (i = 0 ∧ j = 0) ∨ (i = 0 ∧ j = I.size - 1) ∨ (i = I.size - 1 ∧ j = 0)
            ∨ (i = I.size - 1 ∧ j = I.size - 1) then 1 else 2 := by
  rw [countP_onSlack_split, countP_onSlack_lo I i j hN, countP_onSlack_hi I i j hN]
  split_ifs <;> omega

/-! ## `Âᵀ Â` off the diagonal -/
variable (I : Instance)

/-! ## A `countP ≤ 1` criterion -/

/-- **At most one witness.** In a duplicate-free list, if any two elements satisfying `p` are
equal, then at most one element satisfies `p`. -/
theorem countP_le_one_of_unique {p : Nat → Bool} :
    ∀ {l : List Nat}, l.Nodup →
      (∀ a ∈ l, ∀ b ∈ l, p a = true → p b = true → a = b) → l.countP p ≤ 1 := by
  intro l
  induction l with
  | nil => intro _ _; simp
  | cons a t ih =>
    intro hnd huniq
    have hnd' := List.nodup_cons.mp hnd
    by_cases ha : p a = true
    · -- `a` is the witness, so no element of `t` can be one
      have hz : t.countP p = 0 := by
        refine List.countP_eq_zero.mpr fun b hb hpb => hnd'.1 ?_
        have hab : a = b :=
          huniq a (List.mem_cons_self ..) b (List.mem_cons_of_mem _ hb) ha hpb
        exact hab ▸ hb
      simp [hz, ha]
    · have hle := ih hnd'.2 fun x hx y hy =>
        huniq x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)
      simp only [Bool.not_eq_true] at ha
      simpa [List.countP_cons, ha] using hle

namespace Instance

/-! ## Which row a neuron can sit in -/

/-- **An auxiliary neuron sits in exactly one row**, namely its own slack row: `2N + (u − N²)`.
Board rows, column rows and given rows contain cell variables only. -/
theorem slack_row_eq {u r : Nat} (hu : ¬ u < I.ncells) (hr : r < I.nbase)
    (h : I.baseInRow u r = true) : r = 2 * I.size + (u - I.ncells) := by
  rcases I.eq_rowKind hr with ⟨a, ha, he⟩ | ⟨a, ha, he⟩ | ⟨e, hd, he⟩ | ⟨m, hm, he⟩
  · rw [he, I.baseInRow_rowRow ha] at h; exact absurd h.1 hu
  · rw [he, I.baseInRow_colRow ha] at h; exact absurd h.1 hu
  · rw [he, I.baseInRow_slackRow hd] at h
    simp only [slackRow] at he
    rcases h with ⟨hc, -⟩ | hc
    · exact absurd hc hu
    · simp only [slackVar] at hc
      omega
  · have hm' : m < I.givens.size := hm
    rw [he, I.baseInRow_givRow (Array.getElem?_eq_getElem hm')] at h
    exact absurd h.1 hu

/-- **What a row shared by two distinct cell variables can be.**

A row holding both `cellVar i j` and `cellVar k l` is a board row (and then `i = k`), a column row
(`j = l`), a difference-diagonal row (`i − j = k − l`, written additively) or a sum-diagonal row
(`i + j = k + l`); in each case its index is *determined* by `(i, j)`. It is never a given row:
a given row pins one cell, so it cannot hold two distinct ones — which is why no hypothesis about
the givens (duplicate-freeness in particular) is needed anywhere here. -/
theorem shared_kind {i j k l r : Nat} (hi : i < I.size) (hj : j < I.size) (hk : k < I.size)
    (hl : l < I.size) (hne : ¬ (i = k ∧ j = l)) (hr : r < I.nbase)
    (h1 : I.baseInRow (I.cellVar i j) r = true)
    (h2 : I.baseInRow (I.cellVar k l) r = true) :
    (r = i ∧ i = k) ∨ (r = I.size + j ∧ j = l)
      ∨ (r = 2 * I.size + (i + I.size - 2 - j) ∧ i + l = k + j)
      ∨ (r = 2 * I.size + (I.ndiags + (i + j - 1)) ∧ i + j = k + l) := by
  have hdu : I.cellVar i j / I.size = i := I.cellVar_div hj
  have hmu : I.cellVar i j % I.size = j := I.cellVar_mod hj
  have hdv : I.cellVar k l / I.size = k := I.cellVar_div hl
  have hmv : I.cellVar k l % I.size = l := I.cellVar_mod hl
  have hcu : I.cellVar i j < I.ncells := I.cellVar_lt hi hj
  have hcv : I.cellVar k l < I.ncells := I.cellVar_lt hk hl
  rcases I.eq_rowKind hr with ⟨a, ha, he⟩ | ⟨a, ha, he⟩ | ⟨e, hlt, he⟩ | ⟨m, hm, he⟩
  · -- board row `a`: it sees the cells of row `a`, so `i = a = k`
    rw [he, I.baseInRow_rowRow ha] at h1 h2
    simp only [rowRow] at he
    obtain ⟨-, h1⟩ := h1
    obtain ⟨-, h2⟩ := h2
    rw [hdu] at h1
    rw [hdv] at h2
    exact Or.inl ⟨by omega, by omega⟩
  · -- column row `a`: `j = a = l`
    rw [he, I.baseInRow_colRow ha] at h1 h2
    simp only [colRow] at he
    obtain ⟨-, h1⟩ := h1
    obtain ⟨-, h2⟩ := h2
    rw [hmu] at h1
    rw [hmv] at h2
    exact Or.inr (Or.inl ⟨by omega, by omega⟩)
  · -- diagonal row `e`: neither cell is the slack of that row, so both lie on the diagonal
    rw [he, I.baseInRow_slackRow hlt] at h1 h2
    simp only [slackRow] at he
    have hs1 : I.onSlack i j e = true := by
      rcases h1 with ⟨-, hs⟩ | hs
      · rwa [hdu, hmu] at hs
      · simp only [slackVar] at hs; omega
    have hs2 : I.onSlack k l e = true := by
      rcases h2 with ⟨-, hs⟩ | hs
      · rwa [hdv, hmv] at hs
      · simp only [slackVar] at hs; omega
    by_cases hd : e < I.ndiags
    · rw [I.onSlack_lo hd] at hs1 hs2
      exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))
    · rw [I.onSlack_hi hd] at hs1 hs2
      exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))
  · -- given row: it pins one cell, so it cannot hold two distinct ones
    have hm' : m < I.givens.size := hm
    rw [he, I.baseInRow_givRow (Array.getElem?_eq_getElem hm')] at h1 h2
    obtain ⟨-, hd1, hm1⟩ := h1
    obtain ⟨-, hd2, hm2⟩ := h2
    rw [hdu] at hd1
    rw [hmu] at hm1
    rw [hdv] at hd2
    rw [hmv] at hm2
    exact absurd ⟨by omega, by omega⟩ hne

/-! ## The bound -/

/-- Two distinct **cell** variables share at most one row: any two of the four possible
agreements (`i = k`, `j = l`, `i − j = k − l`, `i + j = k + l`) force `(i, j) = (k, l)`, and two
rows of the same kind have the same index. -/
theorem countP_shared_cells_le_one {i j k l : Nat} (hi : i < I.size) (hj : j < I.size)
    (hk : k < I.size) (hl : l < I.size) (hne : ¬ (i = k ∧ j = l)) :
    (List.range I.nbase).countP
        (fun r => I.baseInRow (I.cellVar i j) r && I.baseInRow (I.cellVar k l) r) ≤ 1 := by
  refine countP_le_one_of_unique List.nodup_range ?_
  intro r hr r' hr' hp hp'
  rw [List.mem_range] at hr hr'
  simp only [Bool.and_eq_true] at hp hp'
  have k1 := I.shared_kind hi hj hk hl hne hr hp.1 hp.2
  have k2 := I.shared_kind hi hj hk hl hne hr' hp'.1 hp'.2
  rcases k1 with ⟨e1, a1⟩ | ⟨e1, a1⟩ | ⟨e1, a1⟩ | ⟨e1, a1⟩ <;>
    rcases k2 with ⟨e2, a2⟩ | ⟨e2, a2⟩ | ⟨e2, a2⟩ | ⟨e2, a2⟩ <;> omega

end Instance

/-- **No two distinct neurons occur together in more than one row**: off its diagonal, `Aᵀ A`
has only the entries `0` and `1`.

No hypothesis on the givens is needed — not even duplicate-freeness — because a given row holds
exactly one cell variable. Neither `hN` nor the two range hypotheses are needed either; they are
part of the requested interface and recorded in the first line of the proof. -/
theorem countP_shared_le_one {u v : Nat} (hN : 2 ≤ I.size)
    (hu : u < I.nvars) (hv : v < I.nvars) (huv : u ≠ v) :
    (List.range I.nbase).countP (fun r => I.baseInRow u r && I.baseInRow v r) ≤ 1 := by
  have _interface : 2 ≤ I.size ∧ u < I.nvars ∧ v < I.nvars := ⟨hN, hu, hv⟩
  by_cases hcu : u < I.ncells
  · by_cases hcv : v < I.ncells
    · -- both are cell variables: rewrite each as `cellVar (u / N) (u % N)`
      have hN0 : 0 < I.size := by omega
      have hiu : u / I.size < I.size := Nat.div_lt_of_lt_mul (by simpa [Instance.ncells] using hcu)
      have hiv : v / I.size < I.size := Nat.div_lt_of_lt_mul (by simpa [Instance.ncells] using hcv)
      have hju : u % I.size < I.size := Nat.mod_lt _ hN0
      have hjv : v % I.size < I.size := Nat.mod_lt _ hN0
      have eu : I.cellVar (u / I.size) (u % I.size) = u := by
        simp only [Instance.cellVar]; exact Nat.div_add_mod u I.size
      have ev : I.cellVar (v / I.size) (v % I.size) = v := by
        simp only [Instance.cellVar]; exact Nat.div_add_mod v I.size
      have hne : ¬ (u / I.size = v / I.size ∧ u % I.size = v % I.size) := by
        rintro ⟨hd, hm⟩
        exact huv (by rw [← eu, ← ev, hd, hm])
      rw [← eu, ← ev]
      exact I.countP_shared_cells_le_one hiu hju hiv hjv hne
    · -- `v` is auxiliary: only its own slack row can be shared
      refine countP_le_one_of_unique List.nodup_range ?_
      intro r hr r' hr' hp hp'
      rw [List.mem_range] at hr hr'
      simp only [Bool.and_eq_true] at hp hp'
      have e1 := I.slack_row_eq hcv hr hp.2
      have e2 := I.slack_row_eq hcv hr' hp'.2
      omega
  · -- `u` is auxiliary
    refine countP_le_one_of_unique List.nodup_range ?_
    intro r hr r' hr' hp hp'
    rw [List.mem_range] at hr hr'
    simp only [Bool.and_eq_true] at hp hp'
    have e1 := I.slack_row_eq hcu hr hp.1
    have e2 := I.slack_row_eq hcu hr' hp'.1
    omega

/-- `countP_shared_le_one` with distinctness given as the `Bool` `u != v`. -/
theorem countP_shared_le_one' {u v : Nat} (hN : 2 ≤ I.size)
    (hu : u < I.nvars) (hv : v < I.nvars) (huv : (u != v) = true) :
    (List.range I.nbase).countP (fun r => I.baseInRow u r && I.baseInRow v r) ≤ 1 :=
  countP_shared_le_one I hN hu hv (by simpa using huv)

end Queens
end QUBO
