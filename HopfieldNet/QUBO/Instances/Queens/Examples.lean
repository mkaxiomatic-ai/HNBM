/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.QUBO.Instances.Queens.Basic

/-!
# Worked `n`-Queens Completion instances

Five boards, exercising both directions of `exists_zero_iff_queens`.

| instance      | board | givens          | verdict                                   |
| ------------- | ----- | --------------- | ----------------------------------------- |
| `classic8`    | 8×8   | none            | solvable — the classic 8-queens puzzle    |
| `completion8` | 8×8   | 3 queens        | completable, uniquely                     |
| `small6`      | 6×6   | 1 queen         | completable, uniquely                     |
| `attacking`   | 8×8   | 2 attacking     | **blocked**, and visibly so               |
| `blocked4`    | 4×4   | a corner queen  | **blocked** — `4`-queens has 2 solutions  |
| `blocked6`    | 6×6   | a corner queen  | **blocked** — `6`-queens has 4 solutions  |

The positive verdicts are read off `exists_zero_iff_queens` from an explicit board, so no search
is needed to certify them. The negative ones are the point of the exercise: they are statements
**about boards**, `¬ ∃ q, isQueens q`, not about the QUBO, and by completeness they are exactly
what entitles a solver reporting "no zero" to say the placement is blocked.

## How the negative results are proved

`isQueens` reads a board only through its size and its first `size` entries
(`Instance.isQueens_congr`), so a hypothetical completion of an `N × N` instance is one of the
finitely many `N`-tuples with entries `< N`. Pinning the given queen fixes one coordinate, and
`decide +kernel` refutes the remaining `N^(N-1)` tuples: `4³ = 64` for `blocked4` and
`6⁵ = 7776` for `blocked6`. This is ordinary kernel reduction — no `native_decide`.

`attacking` needs no enumeration at all: its two givens share a diagonal, so the checker's
diagonal clause refutes any board directly.
-/

namespace QUBO
namespace Queens

open QUBO.Problem

/-! ## The boards -/

/-- The classic 8-queens puzzle: an empty `8 × 8` board. Completion with no givens, kept as the
familiar reference point — `92` solutions. -/
def classic8 : Instance := ⟨8, #[]⟩

/-- One of the 92 solutions of 8-queens: entry `i` is the column of the queen in row `i`. -/
def sol8 : Array Nat := #[0, 4, 7, 5, 2, 6, 1, 3]

/-- **A completion instance that succeeds**: three queens of `sol8` given, and `sol8` is in fact
its unique completion. -/
def completion8 : Instance := ⟨8, #[(0, 0), (1, 4), (2, 7)]⟩

/-- A small completion instance: one queen at `(0,1)` on a `6 × 6` board, uniquely completable
(`6`-queens has exactly four solutions and only one starts in column `1`). -/
def small6 : Instance := ⟨6, #[(0, 1)]⟩

/-- The unique completion of `small6`. -/
def sol6 : Array Nat := #[1, 3, 5, 0, 2, 4]

/-- **Blocked, visibly**: the two given queens `(0,0)` and `(1,1)` share a diagonal. -/
def attacking : Instance := ⟨8, #[(0, 0), (1, 1)]⟩

/-- **Blocked, less visibly**: a single queen in the corner of a `4 × 4` board. `4`-queens has
exactly the two solutions `(1,3,0,2)` and `(2,0,3,1)`, neither of which starts in column `0`. -/
def blocked4 : Instance := ⟨4, #[(0, 0)]⟩

/-- **Blocked, one of the `6 × 6` cases**: a single queen in the corner. `6`-queens has exactly
the four solutions `(1,3,5,0,2,4)`, `(2,5,1,4,0,3)`, `(3,0,4,1,5,2)`, `(4,2,0,5,3,1)`, none of
which starts in column `0`. One queen, placed legally, and the puzzle is already dead — which is
the phenomenon that makes Completion hard and plain `n`-queens easy. -/
def blocked6 : Instance := ⟨6, #[(0, 0)]⟩

/-! ## The instances are well formed -/

theorem classic8_ok : classic8.givensOk = true := by decide
theorem completion8_ok : completion8.givensOk = true := by decide
theorem small6_ok : small6.givensOk = true := by decide
theorem attacking_ok : attacking.givensOk = true := by decide
theorem blocked4_ok : blocked4.givensOk = true := by decide
theorem blocked6_ok : blocked6.givensOk = true := by decide

/-! ## Sizes

`nvars = N² + 2(2N − 3) = N² + 4N − 6` and `nrows = 2N + 2(2N − 3) + #givens = 6N − 6 + #givens`.
-/

-- `(90, 42)`: 64 cells + 26 slacks; 8 board rows, 8 columns, 13 diagonals, 13 anti-diagonals
#eval (classic8.nvars, classic8.nrows)
-- `(90, 45)`: the same board, three extra one-variable rows for the givens
#eval (completion8.nvars, completion8.nrows)
-- `(54, 31)` and `(26, 19)` and `(54, 31)`
#eval ((small6.nvars, small6.nrows), (blocked4.nvars, blocked4.nrows),
  (blocked6.nvars, blocked6.nrows))

example : classic8.nvars = 90 ∧ classic8.nrows = 42 := by decide
example : completion8.nvars = 90 ∧ completion8.nrows = 45 := by decide
example : blocked4.nvars = 26 ∧ blocked4.nrows = 19 := by decide
example : blocked6.nvars = 54 ∧ blocked6.nrows = 31 := by decide

/-! ## The incidence is far from regular

An interior cell meets four rows — its board row, its column, its diagonal and its
anti-diagonal. A cell on a *corner* diagonal meets only three, because that diagonal has length
one and carries no row. A cell holding a given queen meets one more. A slack meets exactly one.

The degree-free statement of `Wf.theta_eq`, together with `Problem.theta` being stored doubled,
is what makes all of these representable at once: the odd degrees `3` and `1` would not be
`ℤ`-valued under a halved threshold. -/

-- `(3, 3, 4, 1)`: corner `(0,0)`, corner `(0,7)`, interior `(3,3)`, and a slack
#eval ((classic8.rowsOf (classic8.cellVar 0 0)).size,
       (classic8.rowsOf (classic8.cellVar 0 7)).size,
       (classic8.rowsOf (classic8.cellVar 3 3)).size,
       (classic8.rowsOf (classic8.slackVar 0)).size)

/-- Four distinct column degrees in one instance, two of them odd. -/
example : (classic8.rowsOf (classic8.cellVar 0 0)).size = 3
    ∧ (classic8.rowsOf (classic8.cellVar 3 3)).size = 4
    ∧ (classic8.rowsOf (classic8.slackVar 0)).size = 1 := by decide +kernel

/-- **`theta u = −deg(u)`**, the whole content of the `b̂ ≡ 1` calculation, read off the built
problem. The odd values `−3` and `−1` are the ones a halved `theta` could not hold. -/
example : (problem classic8).theta.getD (classic8.cellVar 0 0) 0 = -3
    ∧ (problem classic8).theta.getD (classic8.cellVar 3 3) 0 = -4
    ∧ (problem classic8).theta.getD (classic8.slackVar 0) 0 = -1
    ∧ (problem classic8).constDoubled = 42 := by decide +kernel

/-- The corner cell `(0,0)` sits in its board row, its column and one diagonal — the sum diagonal
through it has length one, so there is no row for it. -/
example : classic8.rowsOf (classic8.cellVar 0 0)
    = #[classic8.rowRow 0, classic8.colRow 0, classic8.diagRow 6] := by decide +kernel

/-- A given queen adds exactly one row to its cell, and touches nothing else. -/
example : (completion8.rowsOf (completion8.cellVar 0 0)).size = 4
    ∧ (completion8.rowsOf (completion8.cellVar 3 3)).size = 4 := by decide +kernel

/-! ## The positive instances

`isQueens` is cheap to check, so the witnesses are certified directly and the existence of a zero
of the objective follows from completeness — no search, and no kernel evaluation of the QUBO. -/

/-- `sol8` is a solution of 8-queens. -/
theorem sol8_isQueens : classic8.isQueens sol8 = true := by decide

/-- …and of the completion instance, whose givens it extends. -/
theorem sol8_isQueens' : completion8.isQueens sol8 = true := by decide

/-- `sol6` is the completion of `small6`. -/
theorem sol6_isQueens : small6.isQueens sol6 = true := by decide

/-- **The classic 8-queens QUBO has a zero**, by completeness at `sol8`. -/
theorem classic8_exists_zero : ∃ x, (problem classic8).penaltyDoubled x = 0 :=
  (exists_zero_iff_queens classic8 classic8_ok).mpr ⟨sol8, sol8_isQueens⟩

/-- **The 8×8 completion instance has a zero**: the three given queens can be extended. -/
theorem completion8_exists_zero : ∃ x, (problem completion8).penaltyDoubled x = 0 :=
  (exists_zero_iff_queens completion8 completion8_ok).mpr ⟨sol8, sol8_isQueens'⟩

/-- **The 6×6 completion instance has a zero.** -/
theorem small6_exists_zero : ∃ x, (problem small6).penaltyDoubled x = 0 :=
  (exists_zero_iff_queens small6 small6_ok).mpr ⟨sol6, sol6_isQueens⟩

/-! Running the encoder and the objective: the witness above really is a zero of `‖Âx̂ − b̂‖²`,
and moving one queen off its square is not. Prints `0`, `0`, `0`, then a positive number. -/
#eval (problem classic8).penaltyDoubled (classic8.encode sol8)
#eval (problem completion8).penaltyDoubled (completion8.encode sol8)
#eval (problem small6).penaltyDoubled (small6.encode sol6)
#eval (problem classic8).penaltyDoubled (classic8.encode #[0, 4, 7, 5, 2, 6, 3, 1])

/-! And the round trip: decoding the encoded board returns it. Prints `#[0, 4, 7, 5, 2, 6, 1, 3]`
and `true`. -/
#eval classic8.decode (classic8.encode sol8)
#eval classic8.decode (classic8.encode sol8) == sol8

/-- The round trip, as a theorem rather than an evaluation. -/
example : classic8.decode (classic8.encode sol8) = sol8 := decode_encode classic8 sol8_isQueens

/-- Soundness, run on the encoded solution: the decoder's output passes the checker. -/
example : classic8.isQueens (classic8.decode (classic8.encode sol8)) = true :=
  decode_isQueens classic8 classic8_ok (encode_penalty_zero classic8 classic8_ok sol8_isQueens)

/-! ## The negative instances

### Two givens already attacking

No enumeration: the checker's diagonal clause is contradicted outright. -/

/-- **`attacking` cannot be completed** — a statement about boards. -/
theorem attacking_no_queens : ¬ ∃ q, attacking.isQueens q = true := by
  rintro ⟨q, hq⟩
  have h0 : q.getD 0 attacking.size = 0 :=
    Instance.isQueens_given hq (p := (0, 0)) (by decide)
  have h1 : q.getD 1 attacking.size = 1 :=
    Instance.isQueens_given hq (p := (1, 1)) (by decide)
  obtain ⟨-, hd, -⟩ :=
    Instance.isQueens_pair hq (i := 0) (i' := 1) (by decide) (by decide) (by decide)
  rw [h0, h1] at hd
  exact hd (by omega)

/-- …hence its QUBO has no zero, over **every** bit vector: the finite statement about boards,
upgraded through the equivalence. -/
theorem attacking_no_zero : ¬ ∃ x, (problem attacking).penaltyDoubled x = 0 :=
  fun h => attacking_no_queens ((exists_zero_iff_queens attacking attacking_ok).mp h)

/-! ### A corner queen on a 4×4 board

The given fixes column `0` of board row `0`; the remaining `4³ = 64` tuples are refuted by
kernel reduction. -/

private theorem blocked4_aux : ∀ b < 4, ∀ c < 4, ∀ d < 4,
    blocked4.isQueens #[0, b, c, d] = false := by decide +kernel

/-- **`blocked4` cannot be completed.** A single queen at `(0,0)` on a `4 × 4` board is legal, and
already fatal. -/
theorem blocked4_no_queens : ¬ ∃ q, blocked4.isQueens q = true := by
  rintro ⟨q, hq⟩
  have hs : q.size = 4 := Instance.isQueens_size hq
  have hg : q.getD 0 4 = 0 := Instance.isQueens_given hq (p := (0, 0)) (by decide)
  have hb : ∀ i, i < 4 → q.getD i 4 < 4 := fun _ hi => Instance.isQueens_lt hq hi
  have hq' : blocked4.isQueens #[0, q.getD 1 4, q.getD 2 4, q.getD 3 4] = true := by
    refine Instance.isQueens_congr blocked4 blocked4_ok (by simp [hs]) (fun i hi => ?_) hq
    have hi4 : i < 4 := hi
    interval_cases i <;> simp [hg, blocked4]
  have hno := blocked4_aux _ (hb 1 (by omega)) _ (hb 2 (by omega)) _ (hb 3 (by omega))
  rw [hq'] at hno
  exact Bool.noConfusion hno

/-- …hence no bit vector at all reaches penalty zero. -/
theorem blocked4_no_zero : ¬ ∃ x, (problem blocked4).penaltyDoubled x = 0 :=
  fun h => blocked4_no_queens ((exists_zero_iff_queens blocked4 blocked4_ok).mp h)

/-! ### A corner queen on a 6×6 board

The same argument at `N = 6`: `6⁵ = 7776` tuples. -/

private theorem blocked6_aux : ∀ b < 6, ∀ c < 6, ∀ d < 6, ∀ e < 6, ∀ f < 6,
    blocked6.isQueens #[0, b, c, d, e, f] = false := by decide +kernel

/-- **`blocked6` cannot be completed** — one of the `6 × 6` blocked cases. -/
theorem blocked6_no_queens : ¬ ∃ q, blocked6.isQueens q = true := by
  rintro ⟨q, hq⟩
  have hs : q.size = 6 := Instance.isQueens_size hq
  have hg : q.getD 0 6 = 0 := Instance.isQueens_given hq (p := (0, 0)) (by decide)
  have hb : ∀ i, i < 6 → q.getD i 6 < 6 := fun _ hi => Instance.isQueens_lt hq hi
  have hq' : blocked6.isQueens
      #[0, q.getD 1 6, q.getD 2 6, q.getD 3 6, q.getD 4 6, q.getD 5 6] = true := by
    refine Instance.isQueens_congr blocked6 blocked6_ok (by simp [hs]) (fun i hi => ?_) hq
    have hi6 : i < 6 := hi
    interval_cases i <;> simp [hg, blocked6]
  have hno := blocked6_aux _ (hb 1 (by omega)) _ (hb 2 (by omega)) _ (hb 3 (by omega))
    _ (hb 4 (by omega)) _ (hb 5 (by omega))
  rw [hq'] at hno
  exact Bool.noConfusion hno

/-- …hence no bit vector at all reaches penalty zero. -/
theorem blocked6_no_zero : ¬ ∃ x, (problem blocked6).penaltyDoubled x = 0 :=
  fun h => blocked6_no_queens ((exists_zero_iff_queens blocked6 blocked6_ok).mp h)

/-! Moving the corner queen one square along makes the same board completable, which is the
contrast worth having: the two instances differ in one given. Prints `true` then `0`. -/
#eval small6.isQueens sol6
#eval (problem small6).penaltyDoubled (small6.encode sol6)

/-! ## The degenerate boards

`exists_zero_iff_queens` carries no lower bound on the board size, and these are why it need not.
At `N = 0` there are no variables and no rows, so the objective is vacuously zero and the empty
board is vacuously a solution — `givensOk` is what rules out the one bad case, an off-board given
such as `(0,0)` on a `0 × 0` board, whose row would contain no variable at all. At `N = 1` there is
one cell, two rows (its board row and its column) and no diagonal long enough to carry one, since
`ndiags = 2·1 − 3 = 0`. At `N = 2` there are `4 + 2 = 6` variables and `4 + 2 = 6` rows, and no
solution: the two queens must share the single diagonal or the single anti-diagonal. -/

/-- The empty board. -/
def board0 : Instance := ⟨0, #[]⟩

/-- The `1 × 1` board, whose unique solution is the single cell. -/
def board1 : Instance := ⟨1, #[]⟩

/-- The `2 × 2` board — no solution, the smallest interesting failure. -/
def board2 : Instance := ⟨2, #[]⟩

-- `((0, 0), (1, 2), (6, 6))`: `nvars = N² + 4N − 6` and `nrows = 6N − 6` throughout
#eval ((board0.nvars, board0.nrows), (board1.nvars, board1.nrows),
  (board2.nvars, board2.nrows))
-- `(true, true, 0)` twice, then `(false, 1)`: the two degenerate boards are solved, `2 × 2` is not
#eval (board0.givensOk, board0.isQueens #[], (problem board0).penaltyDoubled #[])
#eval (board1.givensOk, board1.isQueens #[0], (problem board1).penaltyDoubled (board1.encode #[0]))
#eval (board2.isQueens #[0, 1], (problem board2).penaltyDoubled (board2.encode #[0, 1]))

/-- The equivalence at `N = 0`, with no size hypothesis anywhere. -/
example : ∃ x, (problem board0).penaltyDoubled x = 0 :=
  (exists_zero_iff_queens board0 (by decide)).mpr ⟨#[], by decide⟩

/-- …and at `N = 1`. -/
example : ∃ x, (problem board1).penaltyDoubled x = 0 :=
  (exists_zero_iff_queens board1 (by decide)).mpr ⟨#[0], by decide⟩

/-! ## The network

`QUBO.Net` turns any `Wf` problem into a `{0,1}` Hopfield/Boltzmann network whose energy is the
objective. Instantiated here, the ground states of the 8-queens network are its 92 solutions. -/

instance : Nonempty (Fin (problem classic8).nvars) := ⟨⟨0, by decide +kernel⟩⟩

/-- **The queens QUBO is a Hopfield/Boltzmann network**, at the classic 8-queens board:
`E(x̂) = (‖Âx̂ − b̂‖² − ‖b̂‖²)/2`, so minimising the network energy is solving the puzzle. -/
theorem classic8_zeroOneHamiltonian_eq (x : Fin (problem classic8).nvars → Bool) :
    HopfieldEnergy.zeroOneHamiltonian (netParams (problem classic8))
        (stateOfBits (problem classic8) x)
      = (penaltyR (problem classic8) x - constR (problem classic8)) / 2 :=
  zeroOneHamiltonian_eq (problem classic8) (problem_wf classic8) x

/-! ## Axioms

The three headline theorems, and the six instance-level results, use nothing beyond the three
axioms of Lean's own logic. -/

#print axioms decode_isQueens
#print axioms encode_penalty_zero
#print axioms exists_zero_iff_queens
#print axioms blocked4_no_queens
#print axioms blocked6_no_queens
#print axioms attacking_no_queens
#print axioms classic8_exists_zero
#print axioms completion8_exists_zero
#print axioms small6_exists_zero

end Queens
end QUBO
