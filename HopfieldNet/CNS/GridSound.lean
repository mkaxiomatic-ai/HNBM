/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.CNS.Sound
import HopfieldNet.CNS.ReduceSound

/-!
# From the encoding to grids

`CNS.Sound` proves `p(x) = 0` iff every constraint row of `A` holds exactly one set variable.
`CNS.ReduceSound` proves things about `Grid`. This module joins them, so that

  "the search reached `p(x) = 0`"   and   "this grid solves the puzzle"

are the same statement rather than two properties checked separately at run time.

The bridge is arithmetic on indices. Since `varIdx i j k = cellIdx i j * n + k`, a variable's
index splits as cell `v / n` and digit `v % n`; so counting set variables along a *unit's*
family of variables is literally counting cells of that unit holding the digit, which is what
`Grid.isConsistent` constrains.

This file needs both halves, and neither `Sound` nor `ReduceSound` imports the other, so it
lives on its own.
-/

namespace CNS

/-- `varIdx` splits into cell and digit. -/
theorem varIdx_split {i j k : Nat} (hi : i < n) (hj : j < n) (hk : k < n) :
    varIdx i j k / n = cellIdx i j ∧ varIdx i j k % n = k := by
  have h : varIdx i j k = cellIdx i j * n + k := by
    simp only [varIdx, cellIdx, n] at *; omega
  rw [h]
  constructor <;> (simp only [n] at *; omega)

/-- A variable index of a unit's family is below `numVars`. -/
private theorem varIdx_lt {i j k : Nat} (hi : i < n) (hj : j < n) (hk : k < n) :
    varIdx i j k < numVars := by
  simp only [varIdx, numVars, n] at *; omega

/-- The encoding bit at `x_{ijk}` is exactly "cell `(i,j)` holds digit `k`". -/
theorem encode_at {g : Grid} {i j k : Nat} (hi : i < n) (hj : j < n) (hk : k < n) :
    (encode g).getD (varIdx i j k) false = (g.get (cellIdx i j) == some k) := by
  obtain ⟨hd, hm⟩ := varIdx_split hi hj hk
  rw [encode_getD (varIdx_lt hi hj hk), hd, hm]

/-- Counting in `Int` agrees with counting in `Nat`. -/
theorem foldl_count_cast (F : Nat → Bool) : ∀ (l : List Nat) (a : Nat),
    ((l.foldl (fun acc x => if F x then acc + 1 else acc) a : Nat) : Int)
      = l.foldl (fun acc x => if F x then acc + 1 else acc) (a : Int) := by
  intro l
  induction l with
  | nil => intro a; rfl
  | cons x rest ih =>
    intro a
    simp only [List.foldl_cons]
    cases hx : F x with
    | true  => simpa using ih (a + 1)
    | false => simpa using ih a

/-- **A unit's variable family counts exactly the cells of that unit holding the digit.**

The left side is the constraint row of `A`; the right side is what `Grid.isConsistent`
constrains. They are the same sum. -/
theorem countOn_unit_eq {g : Grid} (y : Array Bool) (cells : Nat → Nat) (vars : Nat → Nat)
    {k : Nat}
    (hagree : ∀ t, t < n → y.getD (vars t) false = (g.get (cells t) == some k)) :
    countOn y ((List.range n).map vars)
      = (((List.range n).map cells).foldl
          (fun acc c => if g.get c == some k then acc + 1 else acc) 0 : Nat) := by
  rw [foldl_count_cast]
  unfold countOn
  rw [List.foldl_map, List.foldl_map]
  -- both sides now fold over `range n` with pointwise-equal predicates
  have : ∀ (l : List Nat) (a : Int), (∀ t ∈ l, t < n) →
      l.foldl (fun acc t => if y.getD (vars t) false then acc + 1 else acc) a
        = l.foldl (fun acc t => if g.get (cells t) == some k then acc + 1 else acc) a := by
    intro l
    induction l with
    | nil => intro a _; rfl
    | cons t rest ih =>
      intro a hlt
      have ht : t < n := hlt t (List.mem_cons_self ..)
      simp only [List.foldl_cons, hagree t ht]
      exact ih _ (fun y hy => hlt y (List.mem_cons_of_mem _ hy))
  exact this (List.range n) 0 (fun t ht => List.mem_range.mp ht)

/-- Column units: the paper's constraint (10b) is `Grid.isConsistent` on `colCells`. -/
theorem countOn_colVars {g : Grid} (hcons : g.isConsistent = true) {j k : Nat}
    (hj : j < n) (hk : k < n) : countOn (encode g) (colVars j k) = 1 := by
  have hunit : colCells j ∈ units := colCells_mem_units hj
  have hcount := consistent_at hcons hunit hk
  have hcells : (colCells j).toList = (List.range n).map (fun r => cellIdx r j) := by
    unfold colCells; simp
  rw [hcells] at hcount
  unfold colVars
  rw [countOn_unit_eq (encode g) (fun r => cellIdx r j) (fun i => varIdx i j k)
    (fun t ht => encode_at ht hj hk), hcount]
  rfl

/-- Row units: constraint (10c). -/
theorem countOn_rowVars {g : Grid} (hcons : g.isConsistent = true) {i k : Nat}
    (hi : i < n) (hk : k < n) : countOn (encode g) (rowVars i k) = 1 := by
  have hunit : rowCells i ∈ units := rowCells_mem_units hi
  have hcount := consistent_at hcons hunit hk
  have hcells : (rowCells i).toList = (List.range n).map (fun c => cellIdx i c) := by
    unfold rowCells; simp
  rw [hcells] at hcount
  unfold rowVars
  rw [countOn_unit_eq (encode g) (fun c => cellIdx i c) (fun j => varIdx i j k)
    (fun t ht => encode_at hi ht hk), hcount]
  rfl

/-- Block units: constraint (10d). -/
theorem countOn_boxVars {g : Grid} (hcons : g.isConsistent = true) {b k : Nat}
    (hb : b < n) (hk : k < n) : countOn (encode g) (boxVars b k) = 1 := by
  have hunit : boxCells b ∈ units := boxCells_mem_units hb
  have hcount := consistent_at hcons hunit hk
  have hcells : (boxCells b).toList
      = (List.range n).map (fun t => cellIdx ((b / blk) * blk + t / blk)
          ((b % blk) * blk + t % blk)) := by
    unfold boxCells; simp
  rw [hcells] at hcount
  unfold boxVars
  rw [countOn_unit_eq (encode g)
      (fun t => cellIdx ((b / blk) * blk + t / blk) ((b % blk) * blk + t % blk))
      (fun t => varIdx ((b / blk) * blk + t / blk) ((b % blk) * blk + t % blk) k)
      (fun t ht => encode_at (by simp only [blk, n] at *; omega)
        (by simp only [blk, n] at *; omega) hk), hcount]
  rfl

/-- Row and column of a cell index recover the index. -/
theorem rowOf_colOf_cellIdx {i j : Nat} (hi : i < n) (hj : j < n) :
    rowOf (cellIdx i j) = i ∧ colOf (cellIdx i j) = j := by
  simp only [rowOf, colOf, cellIdx, n] at *
  constructor <;> omega

/-- Every cell of a solved grid carries a legal digit. -/
theorem exists_digit_of_solution {g : Grid} (hsol : g.isSolution = true) {c : Nat}
    (hc : c < numCells) : ∃ k, k < n ∧ g.get c = some k := by
  simp only [Grid.isSolution, Grid.hasSize, Grid.isComplete, Grid.digitsInRange,
    Bool.and_eq_true] at hsol
  obtain ⟨⟨⟨hsz, hrange⟩, hcomp⟩, _⟩ := hsol
  have hsz' : g.cells.size = numCells := by simpa using hsz
  have hlt : c < g.cells.size := by rw [hsz']; exact hc
  have hmem : g.cells[c] ∈ g.cells := Array.getElem_mem hlt
  have hget : g.get c = g.cells[c] := by
    unfold Grid.get
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt]
    rfl
  rw [Array.all_eq_true_iff_forall_mem] at hcomp hrange
  have h1 := hcomp _ hmem
  have h2 := hrange _ hmem
  cases hv : g.cells[c] with
  | none => rw [hv] at h1; simp at h1
  | some k =>
    refine ⟨k, ?_, by rw [hget, hv]⟩
    rw [hv] at h2
    simpa using h2

/-- **A solved grid encodes to zero penalty.**

Together with `penalty_zero_iff_families` this closes the loop between the paper's objective and
the puzzle: `p(x) = 0` is not merely correlated with solving the Sudoku, it *is* solving it. -/
theorem penalty_encode_eq_zero {g : Grid} (hsol : g.isSolution = true) :
    penaltyDoubled (encode g) = 0 := by
  have hcons : g.isConsistent = true := by
    simp only [Grid.isSolution, Bool.and_eq_true] at hsol
    exact hsol.2
  rw [penalty_zero_iff_families]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi j hj
    have hc : cellIdx i j < numCells := by simp only [cellIdx, numCells, n] at *; omega
    obtain ⟨k, hk, hgk⟩ := exists_digit_of_solution hsol hc
    obtain ⟨hr, hcl⟩ := rowOf_colOf_cellIdx hi hj
    have := countOn_cellVars hc hk hgk
    rwa [hr, hcl] at this
  · intro j hj k hk; exact countOn_colVars hcons hj hk
  · intro i hi k hk; exact countOn_rowVars hcons hi hk
  · intro b hb k hk; exact countOn_boxVars hcons hb hk

end CNS
