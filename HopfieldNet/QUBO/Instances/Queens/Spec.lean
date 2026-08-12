/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.QUBO.Instances.Queens.Basic

/-!
# The checker is the problem

`Queens.exists_zero_iff_queens` says the objective has a zero exactly when `Instance.isQueens` has
a witness. That is only worth having if `isQueens` really is the $n$-queens condition, and nothing
proved so far establishes it: `isQueens` is a `Bool`-valued function we wrote, and every theorem
above it is conditional on our having written it correctly.

Two things make this more than pedantry here.

First, `isQueens` tests the diagonals in a *rearranged* form. Two queens at `(i,a)` and `(k,b)`
share a diagonal when `i - a = k - b`, but subtraction on `ℕ` is truncated --- `2 - 5` is `0` --- so
the literal transcription is wrong, and we use `i + b = k + a` instead. That rearrangement is
correct over `ℤ` and is the kind of step that is easy to get backwards.

Second, the givens clause and the bound `q i < N` are stated in terms of `Array.getD` with a
default of `I.size`, chosen so that a missing entry is out of range and fails. That is a coding
convenience, not a statement about chess.

So this file states the condition the way a textbook would --- over `ℤ`, with real subtraction, and
with the pairwise condition quantified over distinct rows --- and proves the two agree. After
`isQueens_iff` the specification a reader has to trust is `IsCompletion`, which mentions no arrays,
no defaults and no truncated arithmetic.
-/

namespace QUBO
namespace Queens

/-- **Two queens attack each other.** Rows `i, k` and columns `a, b`, over `ℤ` so that the two
diagonal conditions are literal differences and sums. -/
def Attack (i a k b : ℤ) : Prop := a = b ∨ i - a = k - b ∨ i + a = k + b

/-- **A completion of the instance.**

One queen per row is built into the representation --- `q i` is the column of the queen in row `i`
--- so what remains is that the board has the right size, that every queen is on it, that no two
queens attack, and that every given queen is present. -/
def IsCompletion (I : Instance) (q : Array Nat) : Prop :=
  q.size = I.size
    ∧ (∀ i < I.size, q.getD i I.size < I.size)
    ∧ (∀ i < I.size, ∀ k < I.size, i ≠ k →
        ¬ Attack i (q.getD i I.size) k (q.getD k I.size))
    ∧ (∀ p ∈ I.givens.toList, q.getD p.1 I.size = p.2)

/-- **The executable checker decides exactly that condition.**

This is the bridge between the encoding's correctness theorems and a statement about chessboards.
Together with `exists_zero_iff_queens` it gives
`(∃ x, penaltyDoubled x = 0) ↔ (∃ q, IsCompletion I q)`, in which nothing on the right mentions the
QUBO, the array representation, or `ℕ`-subtraction. -/
theorem isQueens_iff (I : Instance) (q : Array Nat) :
    I.isQueens q = true ↔ IsCompletion I q := by
  constructor
  · intro h
    refine ⟨Instance.isQueens_size h, fun i hi => Instance.isQueens_lt h hi,
      fun i hi k hk hne => ?_, fun p hp => Instance.isQueens_given h hp⟩
    obtain ⟨hc, hd, ha⟩ := Instance.isQueens_pair h hi hk hne
    rintro (hx | hx | hx)
    · exact hc (by exact_mod_cast hx)
    · exact hd (by omega)
    · exact ha (by omega)
  · rintro ⟨hs, hlt, hp, hg⟩
    refine I.isQueens_of hs hlt (fun i hi k hk hne => ?_) hg
    have h := hp i hi k hk hne
    refine ⟨fun hx => h (Or.inl (by exact_mod_cast hx)),
      fun hx => h (Or.inr (Or.inl (by omega))),
      fun hx => h (Or.inr (Or.inr (by omega)))⟩

/-- **The decision equivalence, with the chess condition on the right.** -/
theorem exists_zero_iff_completion (I : Instance) (hG : I.givensOk = true) :
    (∃ x, (problem I).penaltyDoubled x = 0) ↔ ∃ q, IsCompletion I q := by
  rw [exists_zero_iff_queens I hG]
  exact ⟨fun ⟨q, hq⟩ => ⟨q, (isQueens_iff I q).mp hq⟩,
         fun ⟨q, hq⟩ => ⟨q, (isQueens_iff I q).mpr hq⟩⟩

/-! ## The encoding has the shape it should

`problem_wf` says the incidence is well formed, but not that it is the *queens* incidence. These
`#guard`s pin the structure of `Â` the way `cns encoding` does for Sudoku: they fail during
elaboration if a row family is ever dropped or double-counted. -/

/-! A cell's rows: its board row, its column, and each diagonal through it that is long enough to
carry one. So four for an interior square and three at a corner, whose one-square diagonal has no
row. -/
#guard
  let I : Instance := ⟨8, #[]⟩
  (I.rowsOf (I.cellVar 3 3)).size == 4        -- interior
    && (I.rowsOf (I.cellVar 0 0)).size == 3   -- corner: no anti-diagonal row
    && (I.rowsOf (I.cellVar 7 7)).size == 3
    && (I.rowsOf (I.cellVar 0 7)).size == 3   -- corner: no difference-diagonal row
    && (I.rowsOf (I.cellVar 7 0)).size == 3
    && (I.rowsOf (I.slackVar 0)).size == 1    -- a slack constrains one diagonal

/-! Row counts by family: `N` board rows, `N` columns, `2N-3` diagonals each way. -/
#guard
  let I : Instance := ⟨8, #[]⟩
  I.nrows == 8 + 8 + 13 + 13 && I.ndiags == 13 && I.nvars == 64 + 26

/-! Each board row of `Â` contains the `N` cells of that row of the board, and each column row the
`N` cells of that column. -/
#guard
  let I : Instance := ⟨6, #[]⟩
  (List.range I.size).all fun i =>
    ((List.range I.size).all fun j => (I.rowsOf (I.cellVar i j)).contains (I.rowRow i))
      && ((List.range I.size).all fun j => (I.rowsOf (I.cellVar j i)).contains (I.colRow i))

/-! Every given contributes exactly one extra row, containing exactly that one cell. -/
#guard
  let I : Instance := ⟨6, #[(0, 1), (2, 3)]⟩
  I.nrows == 6 * 6 - 6 + 2
    && (I.rowsOf (I.cellVar 0 1)).contains (I.givRow 0)
    && (I.rowsOf (I.cellVar 2 3)).contains (I.givRow 1)
    && !(I.rowsOf (I.cellVar 0 2)).contains (I.givRow 0)

/-! ## Agreement with an independent checker

`isQueens` is compared against a deliberately different implementation: a list-based pairwise scan
over `ℤ` using real subtraction, with no `Array`, no `getD` default and no rearrangement. Checked
exhaustively over every board of the given size by kernel reduction. This is the same idea as
`Baseline.count` reproducing OEIS A000170, but at the level of the predicate rather than the count.
-/

/-- An independent rendering of the condition: pairwise over a list, differences over `ℤ`. -/
def naive (n : Nat) (cols : List Nat) : Bool :=
  cols.length == n
    && cols.all (fun c => c < n)
    && (List.range cols.length).all fun i =>
        (List.range cols.length).all fun k =>
          i == k ||
            (let a : ℤ := cols.getD i 0
             let b : ℤ := cols.getD k 0
             !(a == b) && !((i : ℤ) - a == (k : ℤ) - b) && !((i : ℤ) + a == (k : ℤ) + b))

/-- The two checkers agree on every one of the `4^4 = 256` boards of size four. -/
theorem isQueens_eq_naive_four : ∀ a < 4, ∀ b < 4, ∀ c < 4, ∀ d < 4,
    Instance.isQueens ⟨4, #[]⟩ #[a, b, c, d] = naive 4 [a, b, c, d] := by decide +kernel

/-- And on every one of the `5^5 = 3125` boards of size five. -/
theorem isQueens_eq_naive_five : ∀ a < 5, ∀ b < 5, ∀ c < 5, ∀ d < 5, ∀ e < 5,
    Instance.isQueens ⟨5, #[]⟩ #[a, b, c, d, e] = naive 5 [a, b, c, d, e] := by decide +kernel

end Queens
end QUBO
