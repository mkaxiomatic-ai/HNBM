/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.QUBO.Instances.Queens.Basic

/-!
# A classical baseline for `n`-Queens Completion

An ordinary chronological-backtracking completion search, written independently of the QUBO: it
never mentions `Problem`, `penaltyDoubled` or the network, and shares with the rest of the
development only the `Instance` record and the `isQueens` checker it is measured against. This is
the queens analogue of `QUBO.Instances.ColouringBaseline`'s first-fit and DSATUR.

Two entry points:

* `solve` — the first completion in lexicographic column order, or `none`;
* `count` — **all** completions. `n`-Queens Completion is `#P`-complete as well as `NP`-complete
  (Gent, Jefferson & Nightingale, JAIR 59 (2017), 815–848), so "how many completions" is a
  meaningful question and not merely a stronger form of "is there one".

## What is proved here

`solve_isQueens`: **every board the baseline returns passes the checker.** The search is therefore
a certified source of positive answers, which is what lets `Queens.Bench` use it as the reference
column without trusting it.

What is *not* proved is the converse — that `solve` returning `none` means no completion exists.
The search is exhaustive by construction, but that is an argument about the code, not a theorem
about it, so `Bench` certifies its negative answers separately by kernel enumeration wherever the
board is small enough (`Queens.Examples.blocked4_no_queens` and friends) and reports them as
observations otherwise. The distinction is stated in the table rather than glossed.
-/

namespace QUBO
namespace Queens
namespace Baseline

open Instance

variable (I : Instance)

/-! ## The search -/

/-- The columns admissible at board row `r` given the instance's givens.

A row with no given admits every column; a row with a given admits only that column; a row with
two *conflicting* givens admits none, which is the right answer and is why this is a `filter`
over all columns rather than a lookup of the first matching given. -/
def candidates (r : Nat) : List Nat :=
  (List.range I.size).filter fun c =>
    I.givens.toList.all fun p => (p.1 != r) || (p.2 == c)

/-- Is column `c` compatible with the queens already placed in rows `0 … placed.size − 1`?

The three clauses are `isQueens`'s three, at `i' := placed.size`: distinct columns, distinct
difference diagonals, distinct sum diagonals — all written additively. -/
def compat (placed : Array Nat) (c : Nat) : Bool :=
  (List.range placed.size).all fun i =>
    let a := placed.getD i 0
    (a != c) && (i + c != placed.size + a) && (i + a != placed.size + c)

/-- Chronological backtracking: extend `placed` one row at a time. `fuel` is the number of rows
still to fill, so the recursion is structural. -/
def extend : Nat → Array Nat → Option (Array Nat)
  | 0, placed => if placed.size == I.size then some placed else none
  | f + 1, placed =>
      if placed.size == I.size then some placed
      else (candidates I placed.size).findSome? fun c =>
        if compat placed c then extend f (placed.push c) else none

/-- **The baseline.** The lexicographically first completion, or `none`. -/
def solve : Option (Array Nat) := extend I I.size #[]

/-- The same search, counting every completion instead of stopping at the first. -/
def countFrom : Nat → Array Nat → Nat
  | 0, placed => if placed.size == I.size then 1 else 0
  | f + 1, placed =>
      if placed.size == I.size then 1
      else (candidates I placed.size).foldl
        (fun acc c => if compat placed c then acc + countFrom f (placed.push c) else acc) 0

/-- **The number of completions** of the instance. -/
def count : Nat := countFrom I I.size #[]

/-! ## Soundness

The invariant is that `placed` is a legal partial placement: in range, pairwise non-attacking,
and agreeing with every given whose row it has reached. `extend` preserves it, and a `placed` of
full size satisfying it passes `isQueens`. -/

/-- A legal partial placement of the first `placed.size` rows. -/
structure Partial (placed : Array Nat) : Prop where
  /-- Only the first `I.size` rows are ever filled. -/
  size_le : placed.size ≤ I.size
  /-- Every placed queen is on the board. -/
  lt : ∀ i < placed.size, placed.getD i 0 < I.size
  /-- No two placed queens attack. -/
  pair : ∀ i < placed.size, ∀ i' < placed.size, i ≠ i' →
    placed.getD i 0 ≠ placed.getD i' 0
      ∧ i + placed.getD i' 0 ≠ i' + placed.getD i 0
      ∧ i + placed.getD i 0 ≠ i' + placed.getD i' 0
  /-- Every given whose row has been reached is honoured. -/
  giv : ∀ p ∈ I.givens.toList, p.1 < placed.size → placed.getD p.1 0 = p.2

theorem partial_empty : Partial I #[] where
  size_le := Nat.zero_le _
  lt := by intro i hi; simp at hi
  pair := by intro i hi; simp at hi
  giv := by intro p _ h; simp at h

/-- Reading an entry of a `push` below the join. -/
private theorem push_getD_lt {a : Array Nat} {i : Nat} (h : i < a.size) (c : Nat) :
    (a.push c).getD i 0 = a.getD i 0 := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
    Array.getElem?_eq_getElem (by simp; omega), Array.getElem?_eq_getElem h, Array.getElem_push_lt]

/-- …and at the join. -/
private theorem push_getD_self (a : Array Nat) (c : Nat) : (a.push c).getD a.size 0 = c := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simp)]
  simp

theorem compat_spec {placed : Array Nat} {c : Nat} (h : compat placed c = true)
    {i : Nat} (hi : i < placed.size) :
    placed.getD i 0 ≠ c
      ∧ i + c ≠ placed.size + placed.getD i 0
      ∧ i + placed.getD i 0 ≠ placed.size + c := by
  simp only [compat, List.all_eq_true, List.mem_range, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  exact ⟨(h i hi).1.1, (h i hi).1.2, (h i hi).2⟩

/-- The step preserves the invariant. -/
theorem partial_push {placed : Array Nat} (hP : Partial I placed) (hlt : placed.size < I.size)
    {c : Nat} (hc : c ∈ candidates I placed.size) (hcom : compat placed c = true) :
    Partial I (placed.push c) := by
  have hcs : c < I.size := by
    simp only [candidates, List.mem_filter, List.mem_range] at hc
    exact hc.1
  have hgiv : ∀ p ∈ I.givens.toList, p.1 = placed.size → p.2 = c := by
    simp only [candidates, List.mem_filter, List.all_eq_true, Bool.or_eq_true, bne_iff_ne,
      beq_iff_eq, ne_eq] at hc
    intro p hp hp1
    rcases hc.2 p hp with h | h
    · exact absurd hp1 h
    · exact h
  refine ⟨by simp; omega, ?_, ?_, ?_⟩
  · intro i hi
    rcases Nat.lt_or_ge i placed.size with h | h
    · rw [push_getD_lt h]; exact hP.lt i h
    · have : i = placed.size := by simp at hi; omega
      subst this; rw [push_getD_self]; exact hcs
  · intro i hi i' hi' hne
    have hsz : (placed.push c).size = placed.size + 1 := by simp
    rw [hsz] at hi hi'
    rcases Nat.lt_or_ge i placed.size with h | h <;> rcases Nat.lt_or_ge i' placed.size with h' | h'
    · rw [push_getD_lt h, push_getD_lt h']; exact hP.pair i h i' h' hne
    · have hi'e : i' = placed.size := by omega
      subst hi'e
      rw [push_getD_lt h, push_getD_self]
      obtain ⟨a, b, d⟩ := compat_spec hcom h
      exact ⟨a, by omega, by omega⟩
    · have hie : i = placed.size := by omega
      subst hie
      rw [push_getD_lt h', push_getD_self]
      obtain ⟨a, b, d⟩ := compat_spec hcom h'
      exact ⟨fun hx => a hx.symm, by omega, by omega⟩
    · exact absurd (by omega : i = i') hne
  · intro p hp hp1
    have hsz : (placed.push c).size = placed.size + 1 := by simp
    rw [hsz] at hp1
    rcases Nat.lt_or_ge p.1 placed.size with h | h
    · rw [push_getD_lt h]; exact hP.giv p hp h
    · have : p.1 = placed.size := by omega
      rw [this, push_getD_self]
      exact (hgiv p hp this).symm

/-- A full legal placement passes the checker. -/
theorem isQueens_of_partial (hG : I.givensOk = true) {q : Array Nat} (hP : Partial I q)
    (hs : q.size = I.size) : I.isQueens q = true := by
  have hd : ∀ i < I.size, q.getD i I.size = q.getD i 0 := by
    intro i hi
    rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem (by omega)]
    simp
  refine I.isQueens_of hs (fun i hi => ?_) (fun i hi i' hi' hne => ?_) (fun p hp => ?_)
  · rw [hd i hi]; exact hP.lt i (by omega)
  · rw [hd i hi, hd i' hi']; exact hP.pair i (by omega) i' (by omega) hne
  · obtain ⟨h1, -⟩ := givensOk_lt hG hp
    rw [hd p.1 h1]; exact hP.giv p hp (by omega)

/-- `extend` returns only boards satisfying the invariant, at full size. -/
theorem extend_sound (hG : I.givensOk = true) :
    ∀ (f : Nat) (placed : Array Nat), Partial I placed → ∀ {q : Array Nat},
      extend I f placed = some q → I.isQueens q = true := by
  intro f
  induction f with
  | zero =>
    intro placed hP q hq
    simp only [extend] at hq
    split at hq
    · rename_i hsz
      cases hq
      exact isQueens_of_partial I hG hP (by simpa using hsz)
    · exact absurd hq (by simp)
  | succ f ih =>
    intro placed hP q hq
    simp only [extend] at hq
    split at hq
    · rename_i hsz
      cases hq
      exact isQueens_of_partial I hG hP (by simpa using hsz)
    · rename_i hsz
      obtain ⟨c, hcmem, hcsome⟩ := List.exists_of_findSome?_eq_some hq
      split at hcsome
      · rename_i hcom
        have hlt : placed.size < I.size := by
          have := hP.size_le
          have : placed.size ≠ I.size := by simpa using hsz
          omega
        exact ih (placed.push c) (partial_push I hP hlt hcmem hcom) hcsome
      · exact absurd hcsome (by simp)

/-- **The baseline is sound: every board it returns is a genuine completion.** -/
theorem solve_isQueens (hG : I.givensOk = true) {q : Array Nat} (h : solve I = some q) :
    I.isQueens q = true :=
  extend_sound I hG I.size #[] (partial_empty I) h

/-- **Hence a board the baseline solves really is completable** — the classical half of the
comparison, with no reference to the QUBO. -/
theorem exists_isQueens_of_solve (hG : I.givensOk = true) {q : Array Nat} (h : solve I = some q) :
    ∃ b, I.isQueens b = true :=
  ⟨q, solve_isQueens I hG h⟩

end Baseline
end Queens
end QUBO
