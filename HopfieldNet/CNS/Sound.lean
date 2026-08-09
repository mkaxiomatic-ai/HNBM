/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.CNS.Encoding

/-!
# Soundness of the QUBO encoding

Everything else in `CNS` is executable and checked at runtime (`cns encoding`, `cns reduced`,
and the certificate test inside `cns solve`). Those are tests. This file *proves*:

  `p(x) = 0`  ↔  every constraint row of `A` is satisfied.

Without it, "the search reached `p(x) = 0`" is a fact about an arithmetic expression. With it,
it is a fact about Sudoku, because the rows of `A` are by construction exactly the constraints
(10a)-(10d): one digit per cell, and each digit once per column, row and block.

The mathematical content is that a sum of squares of integers vanishes only if every term does
— there is no cancellation to hide a violated constraint behind a satisfied one. That is what
makes the penalty a faithful encoding rather than merely a heuristic score.

## Scope, precisely

Two limits, stated because they are easy to overstate:

* These theorems are about `CNS.penaltyDoubled` — the **unreduced** `‖Ax − e‖²` over all `n³`
  variables. The solver descends `Problem.penaltyDoubled`, the **reduced** `‖Âx̂ − b̂‖²` with
  `b̂ = e − A_F s` (`Problem.lean`). Nothing here yet applies to it, and nothing yet proves that
  Algorithm 1 (`reduce`) preserves the solution set. That is the largest remaining gap.
* The right-hand side is a statement about the `n³` encoding *variables*, not about `Grid`.
  `Grid.isSolution`, `Grid.extends'`, `encode` and `decode` occur in no theorem, so constraint
  (10e) — the givens — is unformalised, and the runtime certificate
  `sol.isSolution && g.extends' sol` is not yet connected to any of this by proof.

Kept Mathlib-free, like everything under `CNS` except `CNS.Spec`, so it costs nothing to
rebuild.
-/

namespace CNS

/-! ## Arithmetic groundwork -/

/-- `a * a` is never negative. -/
theorem int_mul_self_nonneg (a : Int) : 0 ≤ a * a := by
  rcases Int.le_total 0 a with h | h
  · exact Int.mul_nonneg h h
  · have h' : 0 ≤ -a := by omega
    have : 0 ≤ (-a) * (-a) := Int.mul_nonneg h' h'
    simpa [Int.neg_mul_neg] using this

/-- Folding a non-negative summand over a list gives zero exactly when the accumulator and
every summand are zero.

Stated for a general `f` because the penalty folds over row *indices*, not over values. -/
theorem foldl_add_eq_zero_iff (f : Nat → Int) (hf : ∀ r, 0 ≤ f r) :
    ∀ (l : List Nat) (acc : Int), 0 ≤ acc →
      (l.foldl (fun a r => a + f r) acc = 0 ↔ acc = 0 ∧ ∀ r ∈ l, f r = 0) := by
  intro l
  induction l with
  | nil => intro acc _; simp
  | cons r rest ih =>
    intro acc hacc
    have hfr : 0 ≤ f r := hf r
    have hstep : 0 ≤ acc + f r := by omega
    rw [List.foldl_cons, ih (acc + f r) hstep]
    constructor
    · rintro ⟨hz, hall⟩
      refine ⟨by omega, ?_⟩
      intro w hw
      rcases List.mem_cons.mp hw with rfl | hw'
      · omega
      · exact hall w hw'
    · rintro ⟨hacc0, hall⟩
      have hr0 : f r = 0 := hall r (List.mem_cons_self ..)
      exact ⟨by omega, fun w hw => hall w (List.mem_cons_of_mem _ hw)⟩

/-! ## Encoding soundness -/

/-- **The penalty vanishes exactly on constraint-satisfying assignments.**

`‖Ax − b‖² = 0` iff every one of the `4n²` rows of `A` has zero residual. Since those rows are
precisely the constraints (10a)-(10d) — one digit per cell, and each digit exactly once per
column, row and block — a zero penalty *is* a solved grid, and conversely. -/
theorem penaltyDoubled_eq_zero_iff (x : Array Bool) :
    penaltyDoubled x = 0 ↔ ∀ r < numRows, residual x r = 0 := by
  have hf : ∀ r, 0 ≤ residual x r * residual x r := fun r => int_mul_self_nonneg _
  unfold penaltyDoubled
  rw [foldl_add_eq_zero_iff (fun r => residual x r * residual x r) hf _ 0 (by omega)]
  constructor
  · rintro ⟨_, hall⟩ r hr
    have := hall r (List.mem_range.mpr hr)
    have hnz : residual x r * residual x r = 0 := this
    rcases Int.mul_eq_zero.mp hnz with h | h <;> exact h
  · intro h
    refine ⟨rfl, ?_⟩
    intro r hr
    have hr' : r < numRows := List.mem_range.mp hr
    rw [h r hr']
    simp

/-- The penalty is never negative: it is a sum of squares. -/
theorem penaltyDoubled_nonneg (x : Array Bool) : 0 ≤ penaltyDoubled x := by
  have hf : ∀ r, 0 ≤ residual x r * residual x r := fun r => int_mul_self_nonneg _
  unfold penaltyDoubled
  suffices h : ∀ (l : List Nat) (acc : Int), 0 ≤ acc →
      0 ≤ l.foldl (fun a r => a + residual x r * residual x r) acc by
    exact h _ 0 (by omega)
  intro l
  induction l with
  | nil => intro acc hacc; simpa using hacc
  | cons r rest ih =>
    intro acc hacc
    have := hf r
    exact ih (acc + residual x r * residual x r) (by omega)

/-- A row has zero residual exactly when it holds precisely one set variable. -/
theorem residual_eq_zero_iff (x : Array Bool) (r : Nat) :
    residual x r = 0 ↔ rowCount x r = 1 := by
  unfold residual; omega

/-- **Encoding soundness, in Sudoku terms.**

`p(x) = 0` exactly when every constraint row of `A` contains precisely one set variable: one
digit in every cell (10a), and each digit exactly once in every column (10b), row (10c) and
block (10d).

This is the sense in which the QUBO of (11)-(13) *is* Sudoku rather than a score correlated
with it. That the `4n²` rows of `varsOfRow` do enumerate those constraints — 324 rows, nine
variables each, four rows per variable — is checked by `cns encoding`. -/
theorem penaltyDoubled_eq_zero_iff_rowCount (x : Array Bool) :
    penaltyDoubled x = 0 ↔ ∀ r < numRows, rowCount x r = 1 := by
  rw [penaltyDoubled_eq_zero_iff]
  constructor
  · intro h r hr; exact (residual_eq_zero_iff x r).mp (h r hr)
  · intro h r hr; exact (residual_eq_zero_iff x r).mpr (h r hr)

/-! ## The four constraint families

`rowCount x r` is by definition `countOn x (varsOfRowSpec r)`, and `varsOfRowSpec` is literally
the case split over (10a)-(10d). What remains is index arithmetic: that the `4n²` row indices
enumerate the four families exactly once each. With `n = 9` the indices are concrete, so
`omega` discharges the divisions and remainders. -/

private theorem spec_cell {i j : Nat} (hi : i < n) (hj : j < n) :
    varsOfRowSpec (i * n + j) = cellVars i j := by
  have hlt : i * n + j < n * n := by simp only [n] at *; omega
  have hd : (i * n + j) / n = i := by simp only [n] at *; omega
  have hm : (i * n + j) % n = j := by simp only [n] at *; omega
  unfold varsOfRowSpec
  rw [if_pos hlt, hd, hm]

private theorem spec_col {j k : Nat} (hj : j < n) (hk : k < n) :
    varsOfRowSpec (n * n + (j * n + k)) = colVars j k := by
  have h1 : ¬ (n * n + (j * n + k) < n * n) := by simp only [n] at *; omega
  have h2 : n * n + (j * n + k) < 2 * n * n := by simp only [n] at *; omega
  have hd : (n * n + (j * n + k) - n * n) / n = j := by simp only [n] at *; omega
  have hm : (n * n + (j * n + k) - n * n) % n = k := by simp only [n] at *; omega
  unfold varsOfRowSpec
  rw [if_neg h1, if_pos h2, hd, hm]

private theorem spec_row {i k : Nat} (hi : i < n) (hk : k < n) :
    varsOfRowSpec (2 * n * n + (i * n + k)) = rowVars i k := by
  have h1 : ¬ (2 * n * n + (i * n + k) < n * n) := by simp only [n] at *; omega
  have h2 : ¬ (2 * n * n + (i * n + k) < 2 * n * n) := by simp only [n] at *; omega
  have h3 : 2 * n * n + (i * n + k) < 3 * n * n := by simp only [n] at *; omega
  have hd : (2 * n * n + (i * n + k) - 2 * n * n) / n = i := by simp only [n] at *; omega
  have hm : (2 * n * n + (i * n + k) - 2 * n * n) % n = k := by simp only [n] at *; omega
  unfold varsOfRowSpec
  rw [if_neg h1, if_neg h2, if_pos h3, hd, hm]

private theorem spec_box {b k : Nat} (hb : b < n) (hk : k < n) :
    varsOfRowSpec (3 * n * n + (b * n + k)) = boxVars b k := by
  have h1 : ¬ (3 * n * n + (b * n + k) < n * n) := by simp only [n] at *; omega
  have h2 : ¬ (3 * n * n + (b * n + k) < 2 * n * n) := by simp only [n] at *; omega
  have h3 : ¬ (3 * n * n + (b * n + k) < 3 * n * n) := by simp only [n] at *; omega
  have hd : (3 * n * n + (b * n + k) - 3 * n * n) / n = b := by simp only [n] at *; omega
  have hm : (3 * n * n + (b * n + k) - 3 * n * n) % n = k := by simp only [n] at *; omega
  unfold varsOfRowSpec
  rw [if_neg h1, if_neg h2, if_neg h3, hd, hm]

/-- **Encoding soundness in Sudoku terms.**

`p(x) = 0` exactly when each cell holds one digit (10a) and each digit occurs once in every
column (10b), row (10c) and block (10d). This is what makes the QUBO of (11)-(13) an *encoding*
of Sudoku rather than a score correlated with it: the search's stopping condition and the
puzzle's win condition are the same proposition. -/
theorem penalty_zero_iff_families (x : Array Bool) :
    penaltyDoubled x = 0 ↔
      ((∀ i < n, ∀ j < n, countOn x (cellVars i j) = 1) ∧
       (∀ j < n, ∀ k < n, countOn x (colVars j k) = 1) ∧
       (∀ i < n, ∀ k < n, countOn x (rowVars i k) = 1) ∧
       (∀ b < n, ∀ k < n, countOn x (boxVars b k) = 1)) := by
  rw [penaltyDoubled_eq_zero_iff_rowCount]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i hi j hj
      have hb : i * n + j < numRows := by simp only [n, numRows] at *; omega
      have := h _ hb
      unfold rowCount at this
      rwa [spec_cell hi hj] at this
    · intro j hj k hk
      have hb : n * n + (j * n + k) < numRows := by simp only [n, numRows] at *; omega
      have := h _ hb
      unfold rowCount at this
      rwa [spec_col hj hk] at this
    · intro i hi k hk
      have hb : 2 * n * n + (i * n + k) < numRows := by simp only [n, numRows] at *; omega
      have := h _ hb
      unfold rowCount at this
      rwa [spec_row hi hk] at this
    · intro b hb' k hk
      have hb : 3 * n * n + (b * n + k) < numRows := by simp only [n, numRows] at *; omega
      have := h _ hb
      unfold rowCount at this
      rwa [spec_box hb' hk] at this
  · rintro ⟨hcell, hcol, hrow, hbox⟩ r hr
    unfold rowCount varsOfRowSpec
    rcases Nat.lt_or_ge r (n * n) with h1 | h1
    · rw [if_pos h1]
      exact hcell (r / n) (by simp only [n] at *; omega) (r % n) (by simp only [n] at *; omega)
    · rw [if_neg (by omega : ¬ r < n * n)]
      rcases Nat.lt_or_ge r (2 * n * n) with h2 | h2
      · rw [if_pos h2]
        exact hcol _ (by simp only [n] at *; omega) _ (by simp only [n] at *; omega)
      · rw [if_neg (by omega : ¬ r < 2 * n * n)]
        rcases Nat.lt_or_ge r (3 * n * n) with h3 | h3
        · rw [if_pos h3]
          exact hrow _ (by simp only [n] at *; omega) _ (by simp only [n] at *; omega)
        · rw [if_neg (by omega : ¬ r < 3 * n * n)]
          exact hbox _ (by simp only [n, numRows] at *; omega)
            _ (by simp only [n] at *; omega)

/-! ## From grids to the encoding

`penalty_zero_iff_families` speaks about the `n³` encoding variables. These lemmas connect it to
`Grid`, so that "the search reached `p(x) = 0`" and "this grid solves the puzzle" are provably
the same statement rather than two things checked separately at runtime. -/

/-- `encode` reads off the grid at each variable index. -/
theorem encode_getD {g : Grid} {v : Nat} (hv : v < numVars) :
    (encode g).getD v false = (g.get (v / n) == some (v % n)) := by
  unfold encode
  have hsz : ((Array.range numVars).map
      (fun v => g.get (v / n) == some (v % n))).size = numVars := by simp
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by rw [hsz]; exact hv)]
  simp

/-- The variable index of digit `k` in cell `c`, split back into cell and digit. -/
theorem cellDigit_of_varIdx {c k : Nat} (hc : c < numCells) (hk : k < n) :
    (varIdx (rowOf c) (colOf c) k) / n = c ∧ (varIdx (rowOf c) (colOf c) k) % n = k := by
  have h : varIdx (rowOf c) (colOf c) k = c * n + k := by
    simp only [varIdx, rowOf, colOf, n, numCells] at *; omega
  rw [h]
  constructor <;> (simp only [n] at *; omega)

/-- The encoding bit of digit `t` at cell `c`. -/
private theorem encode_cell_bit {g : Grid} {c : Nat} (hc : c < numCells) {k : Nat}
    (hgc : g.get c = some k) {t : Nat} (ht : t < n) :
    (encode g).getD (varIdx (rowOf c) (colOf c) t) false = (t == k) := by
  have hlt : varIdx (rowOf c) (colOf c) t < numVars := by
    simp only [varIdx, rowOf, colOf, numVars, numCells, n] at *; omega
  obtain ⟨hd, hm⟩ := cellDigit_of_varIdx hc ht
  rw [encode_getD hlt, hd, hm, hgc]
  cases hteq : t == k with
  | true  => simp [(beq_iff_eq).mp hteq]
  | false =>
    have hne : t ≠ k := (beq_eq_false_iff_ne).mp hteq
    simp [Ne.symm hne]

/-- Digits other than the cell's own contribute nothing. -/
private theorem countOn_absent {g : Grid} {c : Nat} (hc : c < numCells) {k : Nat}
    (hgc : g.get c = some k) :
    ∀ (l : List Nat) (a : Int), (∀ s ∈ l, s < n) → k ∉ l →
      (l.map (fun s => varIdx (rowOf c) (colOf c) s)).foldl
        (fun a v => if (encode g).getD v false then a + 1 else a) a = a := by
  intro l
  induction l with
  | nil => intro a _ _; rfl
  | cons s rest ih =>
    intro a hlt hni
    have hsn : s < n := hlt s (List.mem_cons_self ..)
    have hsk : s ≠ k := fun h => hni (h ▸ List.mem_cons_self ..)
    simp only [List.map_cons, List.foldl_cons, encode_cell_bit hc hgc hsn,
      (beq_eq_false_iff_ne).mpr hsk, Bool.false_eq_true, if_false]
    exact ih a (fun y hy => hlt y (List.mem_cons_of_mem _ hy))
      (fun hy => hni (List.mem_cons_of_mem _ hy))

/-- On a grid, the `n` variables of an assigned cell carry exactly one `1`.

This is constraint (10a) holding automatically for any grid: a cell has one digit. -/
theorem countOn_cellVars {g : Grid} {c : Nat} (hc : c < numCells) {k : Nat} (hk : k < n)
    (hgc : g.get c = some k) :
    countOn (encode g) (cellVars (rowOf c) (colOf c)) = 1 := by
  unfold countOn cellVars
  suffices h : ∀ (l : List Nat) (acc : Int), (∀ t ∈ l, t < n) → k ∈ l → l.Nodup →
      (l.map (fun t => varIdx (rowOf c) (colOf c) t)).foldl
        (fun a v => if (encode g).getD v false then a + 1 else a) acc = acc + 1 by
    exact h (List.range n) 0 (fun t ht => List.mem_range.mp ht)
      (List.mem_range.mpr hk) List.nodup_range
  intro l
  induction l with
  | nil => intro acc _ hk0 _; exact absurd hk0 (by simp)
  | cons t rest ih =>
    intro acc hlt hmem hnd
    have htn : t < n := hlt t (List.mem_cons_self ..)
    simp only [List.map_cons, List.foldl_cons, encode_cell_bit hc hgc htn]
    rcases List.mem_cons.mp hmem with heq | hmem'
    · -- the head is the cell's digit; nothing after it contributes
      subst heq
      simp only [beq_self_eq_true, if_true]
      exact countOn_absent hc hgc rest (acc + 1)
        (fun y hy => hlt y (List.mem_cons_of_mem _ hy)) (List.nodup_cons.mp hnd).1
    · have hne : t ≠ k := fun h => (List.nodup_cons.mp hnd).1 (h ▸ hmem')
      simp only [(beq_eq_false_iff_ne).mpr hne, Bool.false_eq_true, if_false]
      exact ih acc (fun y hy => hlt y (List.mem_cons_of_mem _ hy)) hmem'
        (List.nodup_cons.mp hnd).2

/-- A zero penalty forces the residual of every individual row to vanish — the direction the
certificate check relies on. -/
theorem residual_eq_zero_of_penalty_zero {x : Array Bool} (h : penaltyDoubled x = 0)
    {r : Nat} (hr : r < numRows) : residual x r = 0 :=
  (penaltyDoubled_eq_zero_iff x).mp h r hr

end CNS
