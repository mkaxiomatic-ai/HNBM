/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.QUBO.Refine

/-!
# `n`-Queens Completion as a 0/1 QUBO in canonical form

`QUBO.Problem` is the objective `‖Â x̂ − b̂‖²` with `Â` a 0/1 matrix. This module builds one from
an **`n`-Queens Completion** instance — an `N × N` board together with a partial placement of
queens — so that a zero of the objective *is* an extension of the given placement to a full
solution, and proves it in both directions.

## Why *completion* and not plain `n`-queens

Plain `n`-queens is not a decision problem worth reducing: for every `N ≥ 4` a solution exists,
by a closed-form construction, so `∃ x, penaltyDoubled x = 0` would be a theorem and the
equivalence below vacuous. **Completion** — "can this partial placement be extended?" — is
NP-complete and `#P`-complete (Gent, Jefferson & Nightingale, *Complexity of n-Queens
Completion*, JAIR **59** (2017), 815–848), and its negative instances are genuine: `blocked4`
and `blocked6` in `Queens.Examples` are partial placements with **no** completion, proved so.

## What is proved

* `problem_wf` — the built `Problem` satisfies `Problem.Wf`, hence is a Hopfield/Boltzmann
  network with the objective as its energy, by `QUBO.Problem.zeroOneHamiltonian_eq`;
* `problem_refines` — it is the (trivial, no column deleted) column restriction of `incidence`;
* `decode_isQueens` — soundness: a zero of the objective decodes to a completion;
* `encode_penalty_zero` — completeness: a completion encodes to a zero;
* `exists_zero_iff_queens` — hence the QUBO has a zero **iff** the placement can be completed,
  the only hypothesis being `givensOk`, i.e. that the given queens sit on the board.

## The encoding

One variable `x_{i,j}` per cell, plus one binary slack per diagonal. Every constraint is an
equality or an at-most-one, so it fits `Problem` with no reduction machinery at all:

| constraint            | count     | row                                    |
| --------------------- | --------- | -------------------------------------- |
| one queen per row     | `N`       | `Σ_j x_{i,j} = 1`                      |
| one queen per column  | `N`       | `Σ_i x_{i,j} = 1`                      |
| ≤ 1 per diagonal      | `2N − 3`  | `Σ x + s_d = 1`                        |
| ≤ 1 per anti-diagonal | `2N − 3`  | `Σ x + s_a = 1`                        |
| each given queen      | `#givens` | `x_{i,j} = 1`, a one-variable row      |

**One slack per diagonal is enough, whatever the diagonal's length.** The row `Σ x + s = 1` is
met when `Σ x = 0, s = 1` and when `Σ x = 1, s = 0`; if two or more queens share the diagonal the
residual is at least `1` whatever `s` does, and is penalised. There is no need for a slack per
*pair* of cells, nor for a unary encoding of the count.

Only the `2N − 3` diagonals of length `≥ 2` get a row: the two length-one corner diagonals
(`(0, N−1)` and `(N−1, 0)` for the difference direction, `(0,0)` and `(N−1,N−1)` for the sum
direction) cannot host a conflict, so a row for them would only add a variable and a constraint
that any assignment satisfies. That is `2N − 1` diagonals in each direction less the two corners.

**Givens are pinned by single-variable rows.** The row for the given `(i,j)` contains the one
variable `x_{i,j}` and has `b̂ = 1`, so its residual `(x_{i,j} − 1)²` vanishes exactly when the
queen is there. No fixing of variables, no reduction step, no change to the incidence machinery.

### Index layout

Write `N = size`, `D = ndiags = 2N − 3`, `G = ngivens`. Variables (`nvars = N² + 2D`):

| range                    | name         | index            |
| ------------------------ | ------------ | ---------------- |
| `i, j < N`               | `cellVar i j`| `N·i + j`        |
| `e < 2D`                 | `slackVar e` | `N² + e`         |

A slack with `e < D` guards the diagonal `i − j` numbered `e`; one with `D ≤ e < 2D` guards the
anti-diagonal `i + j` numbered `e − D`. Rows (`nrows = nbase = 2N + 2D + G`):

| range        | name         | index            | equation                        |
| ------------ | ------------ | ---------------- | ------------------------------- |
| `i < N`      | `rowRow i`   | `i`              | `Σ_j x_{i,j} = 1`               |
| `j < N`      | `colRow j`   | `N + j`          | `Σ_i x_{i,j} = 1`               |
| `e < 2D`     | `slackRow e` | `2N + e`         | `Σ x + s_e = 1`                 |
| `k < G`      | `givRow k`   | `2N + 2D + k`    | `x_{givens k} = 1`              |

The two diagonal families share one row block and one slack block, which is what makes
`onSlack` a single predicate and the slack half of the incidence the single clause
`u = slackVar e`: the map `slack e ↦ row 2N + e` is the identity shift either way.

### Diagonal membership without subtraction

The natural indices are `i − j + (N−1)` and `i + j`, of which the first is not a `Nat`. Both are
recorded here as **additive** equations, which is what keeps `omega` in play throughout:

* difference direction, slack `e < D`: cell `(i,j)` lies on it iff `i + N = e + 2 + j`;
* sum direction, slack `D ≤ e < 2D`: cell `(i,j)` lies on it iff `i + j + D = e + 1`.

Reading the first: `e = (i − j) + (N − 2)`, so `e ≥ 0` excludes the corner `(N−1, 0)` and
`e < D = 2N−3` excludes the corner `(0, N−1)`. Reading the second: `e = D + (i + j − 1)`, whose
bounds `D ≤ e < 2D` excludes `(0,0)` and `(N−1,N−1)`. So the arithmetic *is* the "length ≥ 2"
condition; nothing has to be checked separately.

## Why the rows are not doubled, and the degrees

`Wf.theta_eq` reads `theta u = deg(u) − 2 Σ_{r ∋ u} b̂_r`: `Problem.theta` holds `2θ̂_u`, not
`θ̂_u`. Here `b̂ ≡ 1` — every row is an "exactly one" equation — so `Σ_{r ∋ u} b̂_r = deg(u)` and

    theta u = deg(u) − 2·deg(u) = −deg(u) = −|baseRowList u|,

an integer whatever the parity of the degree, and `constDoubled = Σ_r b̂_r² = nrows = nbase`.
That matters here more than anywhere else in the library, because the degrees are wildly
irregular: an interior cell variable meets `4` rows (its row, its column, its two diagonals), a
corner cell meets `3` (one of its diagonals is a length-one corner), a cell carrying `m` given
queens meets `m` more, and a slack meets exactly `1`. Under a halved `theta` the odd-degree
columns would not be representable in `ℤ` at all, and forcing every degree even would mean
writing every row twice.
-/

namespace QUBO
namespace Queens

open QUBO.Problem

/-- **An `n`-Queens Completion instance.** The board is `size × size`, cells indexed
`(i, j)` with `i` the board row and `j` the column; `givens` is the partial placement to be
extended. `Instance.givensOk` is the well-formedness the theorems need — every given queen is on
the board. Repeated givens are harmless: they produce duplicate rows, each with the same
one-variable content. -/
structure Instance where
  /-- Board size `N`. -/
  size : Nat
  /-- The queens already placed, as `(row, column)` pairs. -/
  givens : Array (Nat × Nat)
deriving Inhabited, Repr

namespace Instance

variable (I : Instance)

/-! ## The index layout -/

/-- `G`, the number of pre-placed queens. -/
def ngivens : Nat := I.givens.size

/-- `N²`, the number of cell variables; the slacks start here. -/
def ncells : Nat := I.size * I.size

/-- `D = 2N − 3`, the number of diagonals of length `≥ 2` in one direction. Truncated
subtraction gives `0` for `N ≤ 1`, which is right: a `1 × 1` board has no diagonal that could
host a conflict. -/
def ndiags : Nat := 2 * I.size - 3

/-- `N² + 2D`: one variable per cell, one slack per diagonal and per anti-diagonal. -/
def nvars : Nat := I.ncells + 2 * I.ndiags

/-- `2N + 2D + G`: a row per board row, per column, per diagonal, per anti-diagonal and per
given queen. -/
def nbase : Nat := 2 * I.size + 2 * I.ndiags + I.ngivens

/-- The number of rows. Every constraint is written once, so this is `nbase`. -/
def nrows : Nat := I.nbase

/-- The variable "there is a queen in row `i`, column `j`". -/
def cellVar (i j : Nat) : Nat := I.size * i + j

/-- The slack of the `e`-th diagonal row: `e < D` is a difference diagonal, `D ≤ e < 2D` a sum
diagonal. -/
def slackVar (e : Nat) : Nat := I.ncells + e

/-- The slack of the difference diagonal numbered `d`. -/
def diagSlack (d : Nat) : Nat := I.slackVar d

/-- The slack of the sum (anti-)diagonal numbered `d`. -/
def antiSlack (d : Nat) : Nat := I.slackVar (I.ndiags + d)

/-- The row `Σ_j x_{i,j} = 1`. Board rows come first, so this is the identity; the `Instance`
argument is carried only so that dot notation reads like the other four. -/
def rowRow (_I : Instance) (i : Nat) : Nat := i

/-- The row `Σ_i x_{i,j} = 1`. -/
def colRow (j : Nat) : Nat := I.size + j

/-- The row `Σ x + s_e = 1` of the `e`-th diagonal. -/
def slackRow (e : Nat) : Nat := 2 * I.size + e

/-- The row of the difference diagonal numbered `d`. -/
def diagRow (d : Nat) : Nat := I.slackRow d

/-- The row of the sum (anti-)diagonal numbered `d`. -/
def antiRow (d : Nat) : Nat := I.slackRow (I.ndiags + d)

/-- The row `x_{givens k} = 1` pinning the `k`-th given queen. -/
def givRow (k : Nat) : Nat := 2 * I.size + 2 * I.ndiags + k

/-- **Whether the cell `(i,j)` lies on the diagonal that slack row `e` constrains.**

Both directions in one predicate, written additively — see the module docstring. The bounds on
`e` are exactly the "length `≥ 2`" condition, so a corner cell simply has no `e`. -/
def onSlack (i j e : Nat) : Bool :=
  if e < I.ndiags then i + I.size == e + 2 + j else i + j + I.ndiags == e + 1

/-! ## Arithmetic of the layout -/

theorem pack_lt {j a b : Nat} (hj : j < I.size) (hab : a < b) :
    I.size * a + j < I.size * b := by
  have h1 : I.size * a + I.size = I.size * (a + 1) := by ring
  have h2 : I.size * (a + 1) ≤ I.size * b := Nat.mul_le_mul_left _ (by omega)
  omega

theorem cellVar_lt {i j : Nat} (hi : i < I.size) (hj : j < I.size) :
    I.cellVar i j < I.ncells :=
  I.pack_lt hj hi

theorem cellVar_lt_nvars {i j : Nat} (hi : i < I.size) (hj : j < I.size) :
    I.cellVar i j < I.nvars := by
  have := I.cellVar_lt hi hj
  simp only [nvars] at *
  omega

theorem cellVar_div {i j : Nat} (hj : j < I.size) : I.cellVar i j / I.size = i := by
  have hN : 0 < I.size := by omega
  simp only [cellVar]
  rw [Nat.mul_add_div hN, Nat.div_eq_of_lt hj, Nat.add_zero]

theorem cellVar_mod {i j : Nat} (hj : j < I.size) : I.cellVar i j % I.size = j := by
  simp only [cellVar]
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hj]

/-- The cell index is determined by its coordinates: `cellVar` is injective on the board. -/
theorem cellVar_inj {i j i' j' : Nat} (hj : j < I.size) (hj' : j' < I.size)
    (h : I.cellVar i j = I.cellVar i' j') : i = i' ∧ j = j' := by
  have hi : i = i' := by
    rcases Nat.lt_trichotomy i i' with hlt | heq | hgt
    · exact absurd h (by have := I.pack_lt hj hlt; simp only [cellVar]; omega)
    · exact heq
    · exact absurd h (by have := I.pack_lt hj' hgt; simp only [cellVar]; omega)
  subst hi
  simp only [cellVar] at h
  exact ⟨rfl, by omega⟩

theorem slackVar_lt_nvars {e : Nat} (he : e < 2 * I.ndiags) : I.slackVar e < I.nvars := by
  simp only [slackVar, nvars]; omega

/-- A slack row exists only on a board of size at least two: `D = 2N − 3` is `0` below that. -/
theorem two_le_size_of_slack {e : Nat} (he : e < 2 * I.ndiags) : 2 ≤ I.size := by
  have hnd : I.ndiags = 2 * I.size - 3 := rfl
  omega

theorem rowRow_lt_nbase {i : Nat} (hi : i < I.size) : I.rowRow i < I.nbase := by
  simp only [rowRow, nbase]; omega

theorem colRow_lt_nbase {j : Nat} (hj : j < I.size) : I.colRow j < I.nbase := by
  simp only [colRow, nbase]; omega

theorem slackRow_lt_nbase {e : Nat} (he : e < 2 * I.ndiags) : I.slackRow e < I.nbase := by
  simp only [slackRow, nbase]; omega

theorem givRow_lt_nbase {k : Nat} (hk : k < I.ngivens) : I.givRow k < I.nbase := by
  simp only [givRow, nbase]; omega

theorem onSlack_lo {i j e : Nat} (hd : e < I.ndiags) :
    I.onSlack i j e = true ↔ i + I.size = e + 2 + j := by
  unfold onSlack; rw [if_pos hd]; simp

theorem onSlack_hi {i j e : Nat} (hd : ¬ e < I.ndiags) :
    I.onSlack i j e = true ↔ i + j + I.ndiags = e + 1 := by
  unfold onSlack; rw [if_neg hd]; simp

/-- **Two cells on a common diagonal share a slack row.**

Given two distinct board rows whose queens have equal `i − j`, the difference diagonal they lie on
has length `≥ 2`, so it is one of the `D` that carry a row. Both bounds come out of `omega`: if
`i − j` were `±(N−1)` the diagonal would be a corner and the two cells would coincide. -/
theorem exists_diag_slack {i j i' j' : Nat} (hi : i < I.size) (hj : j < I.size)
    (hi' : i' < I.size) (hj' : j' < I.size) (hne : i ≠ i') (hd : i + j' = i' + j) :
    ∃ e, e < 2 * I.ndiags ∧ I.onSlack i j e = true ∧ I.onSlack i' j' e = true := by
  have hnd : I.ndiags = 2 * I.size - 3 := rfl
  have hlt : i + I.size - 2 - j < I.ndiags := by omega
  refine ⟨i + I.size - 2 - j, by omega, ?_, ?_⟩
  · rw [I.onSlack_lo hlt]; omega
  · rw [I.onSlack_lo hlt]; omega

/-- **Two cells on a common anti-diagonal share a slack row.** The sum direction of
`exists_diag_slack`; here `i + j = 0` or `2N − 2` would force the two cells to coincide. -/
theorem exists_anti_slack {i j i' j' : Nat} (hi : i < I.size) (hj : j < I.size)
    (hi' : i' < I.size) (hj' : j' < I.size) (hne : i ≠ i') (ha : i + j = i' + j') :
    ∃ e, e < 2 * I.ndiags ∧ I.onSlack i j e = true ∧ I.onSlack i' j' e = true := by
  have hnd : I.ndiags = 2 * I.size - 3 := rfl
  have hge : ¬ (I.ndiags + (i + j - 1) < I.ndiags) := by omega
  refine ⟨I.ndiags + (i + j - 1), by omega, ?_, ?_⟩
  · rw [I.onSlack_hi hge]; omega
  · rw [I.onSlack_hi hge]; omega

/-! ## The incidence

`baseInRow u r` decides membership of column `u` in row `r`, dispatching on the *row* first and
the column second; the row set of a column is then the `List.filter` of that predicate over the
index range — never a scatter loop. `nodup` is inherited from `List.nodup_range` and membership
is `List.mem_filter`, whereas a `set!` loop could only be characterised by induction on its trip
count. -/

/-- **The incidence.** A board row or a column row sees the cell variables of that line; a slack
row sees the cell variables on its diagonal together with its own slack; a given row sees the one
cell variable of the given queen. -/
def baseInRow (u r : Nat) : Bool :=
  if r < I.size then
    (u < I.ncells) && (r == u / I.size)
  else if r < 2 * I.size then
    (u < I.ncells) && (r == I.size + u % I.size)
  else if r < 2 * I.size + 2 * I.ndiags then
    if u < I.ncells then I.onSlack (u / I.size) (u % I.size) (r - 2 * I.size)
    else u == I.ncells + (r - 2 * I.size)
  else
    match I.givens[r - (2 * I.size + 2 * I.ndiags)]? with
    | none => false
    | some p => (u < I.ncells) && (p.1 == u / I.size) && (p.2 == u % I.size)

/-- The rows of column `u`, as a duplicate-free increasing list. -/
def baseRowList (u : Nat) : List Nat :=
  (List.range I.nbase).filter (fun r => I.baseInRow u r)

/-- The rows of column `u`. Every constraint is written once, so this is `baseRowList`. -/
def rowList (u : Nat) : List Nat := I.baseRowList u

/-- The rows of column `u`, as an array — the `rowsOf` of the `Problem` below. -/
def rowsOf (u : Nat) : Array Nat := (I.rowList u).toArray

theorem mem_baseRowList {u r : Nat} :
    r ∈ I.baseRowList u ↔ r < I.nbase ∧ I.baseInRow u r = true := by
  simp [baseRowList, List.mem_filter, List.mem_range]

theorem baseRowList_nodup (u : Nat) : (I.baseRowList u).Nodup :=
  List.Nodup.filter _ (List.nodup_range)

theorem rowList_nodup (u : Nat) : (I.rowList u).Nodup := I.baseRowList_nodup u

theorem rowList_lt {u r : Nat} (hr : r ∈ I.rowList u) : r < I.nrows := by
  have := ((I.mem_baseRowList).mp hr).1
  simp only [nrows]; omega

theorem rowsOf_size (u : Nat) : (I.rowsOf u).size = (I.baseRowList u).length := by
  simp only [rowsOf, rowList, List.size_toArray]

theorem mem_rowsOf {u r : Nat} : r ∈ I.rowsOf u ↔ r ∈ I.rowList u := by
  simp [rowsOf]

/-- Membership in the row set of a column is the incidence. -/
theorem contains_base {u r : Nat} (hr : r < I.nbase) :
    (I.rowsOf u).contains r = true ↔ I.baseInRow u r = true := by
  rw [Array.contains_iff_mem, I.mem_rowsOf, rowList]
  exact ⟨fun h => ((I.mem_baseRowList).mp h).2, fun h => (I.mem_baseRowList).mpr ⟨hr, h⟩⟩

/-! ### Reading the incidence

Each row kind gets an *iff*, not merely an implication: to know that a row is satisfied one must
know **every** variable in it, which is what completeness needs. -/

/-- A board row sees exactly the cell variables of that row. -/
theorem baseInRow_rowRow {u i : Nat} (hi : i < I.size) :
    I.baseInRow u (I.rowRow i) = true ↔ (u < I.ncells ∧ u / I.size = i) := by
  unfold baseInRow rowRow
  rw [if_pos hi]
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  exact ⟨fun h => ⟨h.1, h.2.symm⟩, fun h => ⟨h.1, h.2.symm⟩⟩

/-- A column row sees exactly the cell variables of that column. -/
theorem baseInRow_colRow {u j : Nat} (hj : j < I.size) :
    I.baseInRow u (I.colRow j) = true ↔ (u < I.ncells ∧ u % I.size = j) := by
  unfold baseInRow colRow
  rw [if_neg (by omega : ¬ (I.size + j < I.size)),
    if_pos (by omega : I.size + j < 2 * I.size)]
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  exact ⟨fun h => ⟨h.1, by omega⟩, fun h => ⟨h.1, by omega⟩⟩

/-- **The full content of a slack row**: the cell variables on its diagonal, and its own slack —
nothing else. -/
theorem baseInRow_slackRow {u e : Nat} (he : e < 2 * I.ndiags) :
    I.baseInRow u (I.slackRow e) = true ↔
      ((u < I.ncells ∧ I.onSlack (u / I.size) (u % I.size) e = true) ∨ u = I.slackVar e) := by
  have h2 : 2 ≤ I.size := I.two_le_size_of_slack he
  unfold baseInRow slackRow slackVar
  rw [if_neg (by omega : ¬ (2 * I.size + e < I.size)),
    if_neg (by omega : ¬ (2 * I.size + e < 2 * I.size)),
    if_pos (by omega : 2 * I.size + e < 2 * I.size + 2 * I.ndiags),
    show 2 * I.size + e - 2 * I.size = e from by omega]
  by_cases h : u < I.ncells
  · rw [if_pos h]
    refine ⟨fun hh => Or.inl ⟨h, hh⟩, ?_⟩
    rintro (⟨-, hh⟩ | hh)
    · exact hh
    · exact absurd h (by omega)
  · rw [if_neg h]
    simp only [beq_iff_eq]
    refine ⟨fun hh => Or.inr hh, ?_⟩
    rintro (⟨hc, -⟩ | hh)
    · exact absurd hc h
    · exact hh

/-- **The full content of a given row**: the single cell variable it pins. -/
theorem baseInRow_givRow {u k : Nat} {p : Nat × Nat} (hp : I.givens[k]? = some p) :
    I.baseInRow u (I.givRow k) = true ↔
      (u < I.ncells ∧ p.1 = u / I.size ∧ p.2 = u % I.size) := by
  unfold baseInRow givRow
  rw [if_neg (by omega : ¬ (2 * I.size + 2 * I.ndiags + k < I.size)),
    if_neg (by omega : ¬ (2 * I.size + 2 * I.ndiags + k < 2 * I.size)),
    if_neg (by omega : ¬ (2 * I.size + 2 * I.ndiags + k < 2 * I.size + 2 * I.ndiags)),
    show 2 * I.size + 2 * I.ndiags + k - (2 * I.size + 2 * I.ndiags) = k from by omega, hp]
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  exact ⟨fun h => ⟨h.1.1, h.1.2, h.2⟩, fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩⟩

/-- …read as an equation on the variable index, which is how the proofs use it. -/
theorem baseInRow_givRow_eq {u k : Nat} {p : Nat × Nat} (hp : I.givens[k]? = some p)
    (h1 : p.1 < I.size) (h2 : p.2 < I.size) :
    I.baseInRow u (I.givRow k) = true ↔ u = I.cellVar p.1 p.2 := by
  rw [I.baseInRow_givRow hp]
  constructor
  · rintro ⟨-, hd, hm⟩
    simp only [cellVar, hd, hm]
    exact (Nat.div_add_mod u I.size).symm
  · rintro rfl
    exact ⟨I.cellVar_lt h1 h2, (I.cellVar_div h2).symm, (I.cellVar_mod h2).symm⟩

/-- **Every row is one of the four kinds**, with its index in range. -/
theorem eq_rowKind {r : Nat} (hr : r < I.nbase) :
    (∃ i, i < I.size ∧ r = I.rowRow i) ∨ (∃ j, j < I.size ∧ r = I.colRow j)
      ∨ (∃ e, e < 2 * I.ndiags ∧ r = I.slackRow e)
      ∨ (∃ k, k < I.ngivens ∧ r = I.givRow k) := by
  simp only [nbase] at hr
  unfold rowRow colRow slackRow givRow
  by_cases h1 : r < I.size
  · exact Or.inl ⟨r, h1, rfl⟩
  by_cases h2 : r < 2 * I.size
  · exact Or.inr (Or.inl ⟨r - I.size, by omega, by omega⟩)
  by_cases h3 : r < 2 * I.size + 2 * I.ndiags
  · exact Or.inr (Or.inr (Or.inl ⟨r - 2 * I.size, by omega, by omega⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨r - (2 * I.size + 2 * I.ndiags), by omega, by omega⟩))

end Instance

/-! ## The QUBO

Every field is a `map` or a `filter` over an index range, as in `CNS.Problem.ofReduced`: field
projections are then `rfl` and entries are read off by `Array.getElem_map`. -/

/-- Reading off a field built as a `map` over an index range. -/
theorem map_range_getD {α : Type _} (n : Nat) (f : Nat → α) (d : α) {i : Nat} (hi : i < n) :
    ((Array.range n).map f).getD i d = f i := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa using hi)]
  simp

/-- **The `n`-queens-completion QUBO.** `b̂ ≡ 1`, since every constraint is an "exactly one"
equation, so `Σ_{r ∋ u} b̂_r = deg(u)` and the stored (doubled) threshold is
`2θ̂_u = deg(u) − 2deg(u) = −deg(u) = −|baseRowList u|`. -/
def problem (I : Instance) : Problem where
  nvars := I.nvars
  nrows := I.nrows
  varOf := Array.range I.nvars
  rowsOf := (Array.range I.nvars).map I.rowsOf
  varsOf := (Array.range I.nrows).map fun r =>
    ((List.range I.nvars).filter fun u => (I.rowsOf u).contains r).toArray
  bhat := Array.replicate I.nrows 1
  -- stored doubled: `2θ̂_u = deg(u) − 2 Σ_{r ∋ u} b̂_r = deg(u) − 2·deg(u) = −deg(u)`
  theta := (Array.range I.nvars).map fun u => -((I.baseRowList u).length : Int)
  constDoubled := (I.nbase : Int)
  base := #[]

variable (I : Instance)

@[simp] theorem problem_nvars : (problem I).nvars = I.nvars := rfl
@[simp] theorem problem_nrows : (problem I).nrows = I.nrows := rfl

theorem problem_rowsOf {u : Nat} (hu : u < I.nvars) :
    (problem I).rowsOf.getD u #[] = I.rowsOf u :=
  map_range_getD _ _ _ hu

theorem problem_bhat {r : Nat} (hr : r < I.nrows) : (problem I).bhat.getD r 0 = 1 := by
  show (Array.replicate I.nrows (1 : Int)).getD r 0 = 1
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa using hr)]
  simp

theorem problem_theta {u : Nat} (hu : u < I.nvars) :
    (problem I).theta.getD u 0 = -((I.baseRowList u).length : Int) :=
  map_range_getD _ _ _ hu

theorem problem_varOf {u : Nat} (hu : u < I.nvars) : (problem I).varOf.getD u 0 = u := by
  show (Array.range I.nvars).getD u 0 = u
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa using hu)]
  simp

/-- The queens constraint system as a `QUBO.Incidence`. -/
def incidence (I : Instance) : Incidence where
  nvars := I.nvars
  nrows := I.nrows
  rowsOf := I.rowsOf
  nodup := fun u _ => by simpa [Instance.rowsOf] using I.rowList_nodup u
  mem_lt := fun u _ r hr => I.rowList_lt (I.mem_rowsOf.mp hr)

/-- The QUBO is the (trivial, no columns deleted) restriction of that incidence. -/
theorem problem_refines : Problem.Refines (incidence I) (problem I) where
  nrows_eq := rfl
  varOf_lt := fun u hu => by rw [problem_varOf I hu]; exact hu
  rowsOf_eq := fun u hu => by rw [problem_rowsOf I hu, problem_varOf I hu]; rfl
  varOf_inj := fun u hu v hv h => by rwa [problem_varOf I hu, problem_varOf I hv] at h

/-! ## Well-formedness -/

/-- Summing `b̂` over the indicator of a column is its degree, because `b̂ ≡ 1`. -/
theorem sum_bhat_indicator {u : Nat} (hu : u < I.nvars) :
    ∑ r ∈ Finset.range (problem I).nrows,
        (if ((problem I).rowsOf.getD u #[]).contains r then (problem I).bhat.getD r 0 else 0)
      = ((I.rowsOf u).size : Int) := by
  have hnd : (I.rowsOf u).toList.Nodup := by simpa [Instance.rowsOf] using I.rowList_nodup u
  have hlt : ∀ r ∈ I.rowsOf u, r < I.nrows := fun r hr => I.rowList_lt (I.mem_rowsOf.mp hr)
  rw [problem_rowsOf I hu]
  have hone : ∀ r ∈ Finset.range (problem I).nrows,
      (if (I.rowsOf u).contains r then (problem I).bhat.getD r 0 else 0)
        = (if (I.rowsOf u).contains r then (1 : Int) else 0) := by
    intro r hr
    rw [problem_bhat I (by simpa using hr)]
  rw [Finset.sum_congr rfl hone]
  show ∑ r ∈ Finset.range I.nrows, (if (I.rowsOf u).contains r then (1 : Int) else 0) = _
  rw [sum_indicator_weighted (N := I.nrows) (I.rowsOf u) (fun _ => (1 : Int)) hnd hlt,
    Array.foldl_add_eq_sum (I.rowsOf u) (fun _ => (1 : Int)) 0]
  simp

/-- **The queens QUBO is a well-formed 0/1 QUBO in canonical form**, hence a
Hopfield/Boltzmann network by `QUBO.Problem.zeroOneHamiltonian_eq`. -/
theorem problem_wf : (problem I).Wf where
  nodup := fun u hu => by
    rw [problem_rowsOf I hu]
    simpa [Instance.rowsOf] using I.rowList_nodup u
  mem_lt := fun u hu r hr => by
    rw [problem_rowsOf I hu] at hr
    exact I.rowList_lt (I.mem_rowsOf.mp hr)
  theta_eq := fun u hu => by
    rw [problem_theta I hu, sum_bhat_indicator I hu, problem_rowsOf I hu, I.rowsOf_size]
    ring
  const_eq := by
    show (I.nbase : Int) = ∑ r ∈ Finset.range I.nrows, (problem I).bhat.getD r 0 ^ 2
    rw [Finset.sum_congr rfl (fun r hr => by rw [problem_bhat I (by simpa using hr)])]
    simp [Instance.nrows]

/-! ## A zero penalty satisfies every row

`penaltyDoubled` is a fold of squares over the row indices, so it vanishes exactly when each
residual does. This part is about an arbitrary `Problem`. -/

private theorem foldl_add_eq_zero_iff (f : Nat → Int) (hf : ∀ r, 0 ≤ f r) :
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

/-- **A zero objective means every constraint row is met exactly.** -/
theorem penalty_zero_row (P : Problem) {x : Array Bool} (h : P.penaltyDoubled x = 0)
    {r : Nat} (hr : r < P.nrows) : (P.rowSums x).getD r 0 = P.bhat.getD r 0 := by
  set d : Nat → Int := fun s => (P.rowSums x).getD s 0 - P.bhat.getD s 0 with hd
  have hf : ∀ s, 0 ≤ d s * d s := fun s => mul_self_nonneg _
  have hrw : P.penaltyDoubled x = (Array.range P.nrows).foldl (fun a s => a + d s * d s) 0 := rfl
  rw [hrw, ← Array.foldl_toList, Array.toList_range] at h
  have hall := (foldl_add_eq_zero_iff (fun s => d s * d s) hf _ 0 (le_refl 0)).mp h
  have hzero : d r * d r = 0 := hall.2 r (List.mem_range.mpr hr)
  have hdr : d r = 0 := by rcases mul_eq_zero.mp hzero with h1 | h1 <;> exact h1
  simp only [hd] at hdr
  omega

/-- **The converse: meeting every row exactly makes the objective vanish.** -/
theorem penalty_zero_of_rowSums (P : Problem) {x : Array Bool}
    (h : ∀ r < P.nrows, (P.rowSums x).getD r 0 = P.bhat.getD r 0) :
    P.penaltyDoubled x = 0 := by
  have hf : ∀ s : Nat, 0 ≤ ((P.rowSums x).getD s 0 - P.bhat.getD s 0)
      * ((P.rowSums x).getD s 0 - P.bhat.getD s 0) := fun _ => mul_self_nonneg _
  have hrw : P.penaltyDoubled x = (Array.range P.nrows).foldl
      (fun a s => a + ((P.rowSums x).getD s 0 - P.bhat.getD s 0)
        * ((P.rowSums x).getD s 0 - P.bhat.getD s 0)) 0 := rfl
  rw [hrw, ← Array.foldl_toList, Array.toList_range]
  refine (foldl_add_eq_zero_iff _ hf _ 0 (le_refl 0)).mpr ⟨rfl, fun r hr => ?_⟩
  rw [h r (List.mem_range.mp hr)]
  ring

/-! ## Boards, the checker, and the two maps

A board is an `Array Nat` of length `N`: entry `i` is the column of the queen in board row `i`.
"One queen per row" is then structural, and "one per column" is the pairwise distinctness the
checker demands — the same shape as `Colouring.decode`, one colour per vertex. -/

namespace Instance

/-- The columns `x` gives to board row `i`. -/
def hitsAt (I : Instance) (x : Array Bool) (i : Nat) : List Nat :=
  (List.range I.size).filter fun j => x.getD (I.cellVar i j) false

/-- **The decoder**: one column per board row, `size` (an illegal column) if the bit vector puts
no queen in that row. -/
def decode (I : Instance) (x : Array Bool) : Array Nat :=
  (Array.range I.size).map fun i => (I.hitsAt x i).headD I.size

/-- **The checker**: `N` queens, one per row (structural) and one per column, no two sharing a
diagonal, and every given queen present.

The three pairwise clauses are, in order: same column, same difference diagonal
(`i − c = i' − c'`, written additively), same sum diagonal (`i + c = i' + c'`). -/
def isQueens (I : Instance) (q : Array Nat) : Bool :=
  (q.size == I.size)
    && ((List.range I.size).all fun i => q.getD i I.size < I.size)
    && ((List.range I.size).all fun i => (List.range I.size).all fun i' =>
          (i == i')
            || ((q.getD i I.size != q.getD i' I.size)
                && (i + q.getD i' I.size != i' + q.getD i I.size)
                && (i + q.getD i I.size != i' + q.getD i' I.size)))
    && (I.givens.toList.all fun p => q.getD p.1 I.size == p.2)

/-- The instances the encoding is faithful on: every given queen is on the board. An off-board
given is invisible to the incidence — its row would contain no variable at all — so it is
excluded rather than silently dropped. -/
def givensOk (I : Instance) : Bool :=
  I.givens.toList.all fun p => (p.1 < I.size) && (p.2 < I.size)

/-- The set variables of one row. -/
def hitList (I : Instance) (x : Array Bool) (r : Nat) : List Nat :=
  (List.range I.nvars).filter fun u => x.getD u false && (I.rowsOf u).contains r

theorem mem_hitList {I : Instance} {x : Array Bool} {r u : Nat} :
    u ∈ I.hitList x r
      ↔ u < I.nvars ∧ x.getD u false = true ∧ (I.rowsOf u).contains r = true := by
  simp [hitList, List.mem_filter, List.mem_range]

theorem hitList_nodup (I : Instance) (x : Array Bool) (r : Nat) : (I.hitList x r).Nodup :=
  List.Nodup.filter _ List.nodup_range

theorem decode_getD (I : Instance) (x : Array Bool) {i : Nat} (hi : i < I.size) :
    (I.decode x).getD i I.size = (I.hitsAt x i).headD I.size :=
  map_range_getD _ _ _ hi

theorem decode_size (I : Instance) (x : Array Bool) : (I.decode x).size = I.size := by
  simp [decode]

/-! ### Reading and building the checker

Two lemmas, so that the `simp` normalisation of a four-fold `&&` with a nested `||` happens in
exactly one place each way. -/

/-- **Well-formedness of the input**, as a `Prop`: every given queen is on the board.

The `Bool` form `givensOk` is what the theorems take, so that concrete instances discharge it by
`decide`; this is the same condition stated for reading. Note what is *not* required: the givens
need not be duplicate-free (a repeated given is a repeated one-variable row, which changes
nothing), and there is no lower bound on the board size. -/
structure Wf (I : Instance) : Prop where
  /-- Every given queen has both coordinates on the board. -/
  mem_lt : ∀ p ∈ I.givens.toList, p.1 < I.size ∧ p.2 < I.size

/-- A checked instance has every given queen on the board. -/
theorem givensOk_lt {I : Instance} (hG : I.givensOk = true) {p : Nat × Nat}
    (hp : p ∈ I.givens.toList) : p.1 < I.size ∧ p.2 < I.size := by
  have h := (List.all_eq_true.mp hG) p hp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h

/-- The `Prop` and `Bool` forms of well-formedness agree. -/
theorem wf_iff_givensOk (I : Instance) : I.Wf ↔ I.givensOk = true := by
  constructor
  · intro h
    refine List.all_eq_true.mpr fun p hp => ?_
    obtain ⟨h1, h2⟩ := h.mem_lt p hp
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨h1, h2⟩
  · exact fun h => ⟨fun _ hp => givensOk_lt h hp⟩

theorem isQueens_size {I : Instance} {q : Array Nat} (h : I.isQueens q = true) :
    q.size = I.size := by
  simp only [isQueens, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.1

theorem isQueens_lt {I : Instance} {q : Array Nat} (h : I.isQueens q = true) {i : Nat}
    (hi : i < I.size) : q.getD i I.size < I.size := by
  simp only [isQueens, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  exact h.1.1.2 i hi

theorem isQueens_pair {I : Instance} {q : Array Nat} (h : I.isQueens q = true) {i i' : Nat}
    (hi : i < I.size) (hi' : i' < I.size) (hne : i ≠ i') :
    q.getD i I.size ≠ q.getD i' I.size
      ∧ i + q.getD i' I.size ≠ i' + q.getD i I.size
      ∧ i + q.getD i I.size ≠ i' + q.getD i' I.size := by
  simp only [isQueens, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq,
    Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
  rcases h.1.2 i hi i' hi' with hc | hc
  · exact absurd hc hne
  · exact ⟨hc.1.1, hc.1.2, hc.2⟩

theorem isQueens_given {I : Instance} {q : Array Nat} (h : I.isQueens q = true) {p : Nat × Nat}
    (hp : p ∈ I.givens.toList) : q.getD p.1 I.size = p.2 := by
  simp only [isQueens, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  exact h.2 p hp

/-- The checker, built from its four obligations. -/
theorem isQueens_of (I : Instance) {q : Array Nat} (hs : q.size = I.size)
    (hlt : ∀ i < I.size, q.getD i I.size < I.size)
    (hp : ∀ i < I.size, ∀ i' < I.size, i ≠ i' →
        q.getD i I.size ≠ q.getD i' I.size
          ∧ i + q.getD i' I.size ≠ i' + q.getD i I.size
          ∧ i + q.getD i I.size ≠ i' + q.getD i' I.size)
    (hg : ∀ p ∈ I.givens.toList, q.getD p.1 I.size = p.2) :
    I.isQueens q = true := by
  simp only [isQueens, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq,
    Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
  refine ⟨⟨⟨hs, fun i hi => hlt i hi⟩, fun i hi i' hi' => ?_⟩, fun p hpm => hg p hpm⟩
  by_cases hii : i = i'
  · exact Or.inl hii
  · obtain ⟨a, b, c⟩ := hp i hi i' hi' hii
    exact Or.inr ⟨⟨a, b⟩, c⟩

/-- **The checker reads a board only through its size and its first `size` entries**, so a checked
board transfers along any array agreeing with it there. This is what turns "no board passes" into
a finite check over `size`-tuples; see `Queens.Examples`. -/
theorem isQueens_congr (I : Instance) (hG : I.givensOk = true) {q q' : Array Nat}
    (hs : q.size = q'.size) (h : ∀ i < I.size, q.getD i I.size = q'.getD i I.size)
    (hq : I.isQueens q = true) : I.isQueens q' = true := by
  refine I.isQueens_of (by rw [← hs]; exact isQueens_size hq) (fun i hi => ?_)
    (fun i hi i' hi' hne => ?_) (fun p hp => ?_)
  · rw [← h i hi]; exact isQueens_lt hq hi
  · rw [← h i hi, ← h i' hi']; exact isQueens_pair hq hi hi' hne
  · obtain ⟨h1, -⟩ := givensOk_lt hG hp
    rw [← h p.1 h1]; exact isQueens_given hq hp

end Instance

/-! ## Every row of a zero-penalty vector holds exactly one set variable -/

theorem hitList_length (I : Instance) {x : Array Bool}
    (hx : (problem I).penaltyDoubled x = 0) {r : Nat} (hr : r < I.nrows) :
    (I.hitList x r).length = 1 := by
  have h := penalty_zero_row (problem I) hx (r := r) hr
  rw [rowSums_spec (problem I) (problem_wf I) x hr, problem_bhat I hr] at h
  have hcp : ((List.range I.nvars).countP
      fun u => x.getD u false && ((problem I).rowsOf.getD u #[]).contains r) = 1 := by
    exact_mod_cast h
  rw [List.countP_eq_length_filter] at hcp
  rw [Instance.hitList,
    List.filter_congr (q := fun u => x.getD u false && ((problem I).rowsOf.getD u #[]).contains r)
      (fun u hu => by rw [problem_rowsOf I (List.mem_range.mp hu)])]
  exact hcp

theorem hitList_unique (I : Instance) {x : Array Bool}
    (hx : (problem I).penaltyDoubled x = 0) {r : Nat} (hr : r < I.nrows) {u w : Nat}
    (hu : u ∈ I.hitList x r) (hw : w ∈ I.hitList x r) : u = w := by
  obtain ⟨c, hc⟩ := List.length_eq_one_iff.mp (hitList_length I hx hr)
  rw [hc, List.mem_singleton] at hu hw
  rw [hu, hw]

theorem hitList_exists (I : Instance) {x : Array Bool}
    (hx : (problem I).penaltyDoubled x = 0) {r : Nat} (hr : r < I.nrows) :
    ∃ u, u ∈ I.hitList x r := by
  obtain ⟨c, hc⟩ := List.length_eq_one_iff.mp (hitList_length I hx hr)
  exact ⟨c, by rw [hc]; exact List.mem_singleton_self c⟩

/-! ## Soundness of the decoder -/

/-- **The decoded column of a board row is one the bit vector actually uses.**

The row `Σ_j x_{i,j} = 1` is met, and its only variables are the cell variables of row `i`, so
`hitsAt` is nonempty and its head is a column of `i`. -/
theorem decode_mem_hitsAt (I : Instance) {x : Array Bool}
    (hx : (problem I).penaltyDoubled x = 0) {i : Nat} (hi : i < I.size) :
    (I.decode x).getD i I.size ∈ I.hitsAt x i := by
  have hN : 0 < I.size := by omega
  have hrb : I.rowRow i < I.nbase := I.rowRow_lt_nbase hi
  have hrr : I.rowRow i < I.nrows := by simpa only [Instance.nrows] using hrb
  obtain ⟨u, hu⟩ := hitList_exists I hx hrr
  obtain ⟨hult, hux, hurow⟩ := Instance.mem_hitList.mp hu
  obtain ⟨hcell, hdiv⟩ := (I.baseInRow_rowRow hi).mp ((I.contains_base hrb).mp hurow)
  have hmod : u % I.size < I.size := Nat.mod_lt _ hN
  have hpack : I.cellVar i (u % I.size) = u := by
    simp only [Instance.cellVar, ← hdiv]
    exact Nat.div_add_mod u I.size
  have hin : u % I.size ∈ I.hitsAt x i := by
    simp only [Instance.hitsAt, List.mem_filter, List.mem_range, hpack]
    exact ⟨hmod, hux⟩
  rw [I.decode_getD x hi]
  cases hl : I.hitsAt x i with
  | nil => rw [hl] at hin; cases hin
  | cons a t => simp

/-- The decoded column is on the board. -/
theorem decode_lt (I : Instance) {x : Array Bool} (hx : (problem I).penaltyDoubled x = 0)
    {i : Nat} (hi : i < I.size) : (I.decode x).getD i I.size < I.size := by
  have := decode_mem_hitsAt I hx hi
  simp only [Instance.hitsAt, List.mem_filter, List.mem_range] at this
  exact this.1

/-- The bit vector really puts a queen where the decoder says. -/
theorem decode_set (I : Instance) {x : Array Bool} (hx : (problem I).penaltyDoubled x = 0)
    {i : Nat} (hi : i < I.size) :
    x.getD (I.cellVar i ((I.decode x).getD i I.size)) false = true := by
  have := decode_mem_hitsAt I hx hi
  simp only [Instance.hitsAt, List.mem_filter, List.mem_range] at this
  exact this.2

/-- **No two decoded queens share a column**: they would be two set variables of the same column
row `Σ_i x_{i,j} = 1`. -/
theorem decode_col (I : Instance) {x : Array Bool} (hx : (problem I).penaltyDoubled x = 0)
    {i i' : Nat} (hi : i < I.size) (hi' : i' < I.size) (hne : i ≠ i') :
    (I.decode x).getD i I.size ≠ (I.decode x).getD i' I.size := by
  intro heq
  have hclt : (I.decode x).getD i I.size < I.size := decode_lt I hx hi
  have hset1 : x.getD (I.cellVar i ((I.decode x).getD i I.size)) false = true :=
    decode_set I hx hi
  have hset2 : x.getD (I.cellVar i' ((I.decode x).getD i I.size)) false = true := by
    have := decode_set I hx hi'; rwa [← heq] at this
  have hrb : I.colRow ((I.decode x).getD i I.size) < I.nbase := I.colRow_lt_nbase hclt
  have hrr : I.colRow ((I.decode x).getD i I.size) < I.nrows := by
    simpa only [Instance.nrows] using hrb
  have hm1 : I.cellVar i ((I.decode x).getD i I.size)
      ∈ I.hitList x (I.colRow ((I.decode x).getD i I.size)) :=
    Instance.mem_hitList.mpr ⟨I.cellVar_lt_nvars hi hclt, hset1,
      (I.contains_base hrb).mpr
        ((I.baseInRow_colRow hclt).mpr ⟨I.cellVar_lt hi hclt, I.cellVar_mod hclt⟩)⟩
  have hm2 : I.cellVar i' ((I.decode x).getD i I.size)
      ∈ I.hitList x (I.colRow ((I.decode x).getD i I.size)) :=
    Instance.mem_hitList.mpr ⟨I.cellVar_lt_nvars hi' hclt, hset2,
      (I.contains_base hrb).mpr
        ((I.baseInRow_colRow hclt).mpr ⟨I.cellVar_lt hi' hclt, I.cellVar_mod hclt⟩)⟩
  exact hne (I.cellVar_inj hclt hclt (hitList_unique I hx hrr hm1 hm2)).1

/-- Two decoded queens on a common diagonal would be two set variables of that diagonal's row. -/
private theorem decode_slack (I : Instance) {x : Array Bool}
    (hx : (problem I).penaltyDoubled x = 0) {i i' : Nat} (hi : i < I.size) (hi' : i' < I.size)
    (hne : i ≠ i') {e : Nat} (he : e < 2 * I.ndiags)
    (h1 : I.onSlack i ((I.decode x).getD i I.size) e = true)
    (h2 : I.onSlack i' ((I.decode x).getD i' I.size) e = true) : False := by
  have hc : (I.decode x).getD i I.size < I.size := decode_lt I hx hi
  have hc' : (I.decode x).getD i' I.size < I.size := decode_lt I hx hi'
  have hrb : I.slackRow e < I.nbase := I.slackRow_lt_nbase he
  have hrr : I.slackRow e < I.nrows := by simpa only [Instance.nrows] using hrb
  have hm1 : I.cellVar i ((I.decode x).getD i I.size) ∈ I.hitList x (I.slackRow e) :=
    Instance.mem_hitList.mpr ⟨I.cellVar_lt_nvars hi hc, decode_set I hx hi,
      (I.contains_base hrb).mpr ((I.baseInRow_slackRow he).mpr (Or.inl ⟨I.cellVar_lt hi hc, by
        rw [I.cellVar_div hc, I.cellVar_mod hc]; exact h1⟩))⟩
  have hm2 : I.cellVar i' ((I.decode x).getD i' I.size) ∈ I.hitList x (I.slackRow e) :=
    Instance.mem_hitList.mpr ⟨I.cellVar_lt_nvars hi' hc', decode_set I hx hi',
      (I.contains_base hrb).mpr ((I.baseInRow_slackRow he).mpr (Or.inl ⟨I.cellVar_lt hi' hc', by
        rw [I.cellVar_div hc', I.cellVar_mod hc']; exact h2⟩))⟩
  exact hne (I.cellVar_inj hc hc' (hitList_unique I hx hrr hm1 hm2)).1

/-- **No two decoded queens share a difference diagonal.** -/
theorem decode_diag (I : Instance) {x : Array Bool} (hx : (problem I).penaltyDoubled x = 0)
    {i i' : Nat} (hi : i < I.size) (hi' : i' < I.size) (hne : i ≠ i') :
    i + (I.decode x).getD i' I.size ≠ i' + (I.decode x).getD i I.size := by
  intro heq
  obtain ⟨e, he, h1, h2⟩ := I.exists_diag_slack hi (decode_lt I hx hi) hi'
    (decode_lt I hx hi') hne heq
  exact decode_slack I hx hi hi' hne he h1 h2

/-- **No two decoded queens share a sum diagonal.** -/
theorem decode_anti (I : Instance) {x : Array Bool} (hx : (problem I).penaltyDoubled x = 0)
    {i i' : Nat} (hi : i < I.size) (hi' : i' < I.size) (hne : i ≠ i') :
    i + (I.decode x).getD i I.size ≠ i' + (I.decode x).getD i' I.size := by
  intro heq
  obtain ⟨e, he, h1, h2⟩ := I.exists_anti_slack hi (decode_lt I hx hi) hi'
    (decode_lt I hx hi') hne heq
  exact decode_slack I hx hi hi' hne he h1 h2

/-- **The decoded board extends the given placement.**

The given row `x_{i,j} = 1` has exactly one variable, so a zero of the objective sets it; the
board row `i` then has two set variables unless the decoder read off the same column. -/
theorem decode_given (I : Instance) (hG : I.givensOk = true) {x : Array Bool}
    (hx : (problem I).penaltyDoubled x = 0) {p : Nat × Nat} (hp : p ∈ I.givens.toList) :
    (I.decode x).getD p.1 I.size = p.2 := by
  obtain ⟨h1, h2⟩ := Instance.givensOk_lt hG hp
  obtain ⟨k, hk, hke⟩ := Array.getElem_of_mem (Array.mem_toList_iff.mp hp)
  have hpk : I.givens[k]? = some p := by rw [Array.getElem?_eq_getElem hk, hke]
  have hrb : I.givRow k < I.nbase := I.givRow_lt_nbase (by simpa [Instance.ngivens] using hk)
  have hrr : I.givRow k < I.nrows := by simpa only [Instance.nrows] using hrb
  obtain ⟨u, hu⟩ := hitList_exists I hx hrr
  obtain ⟨hult, hux, hurow⟩ := Instance.mem_hitList.mp hu
  have hueq : u = I.cellVar p.1 p.2 :=
    (I.baseInRow_givRow_eq hpk h1 h2).mp ((I.contains_base hrb).mp hurow)
  have hset : x.getD (I.cellVar p.1 p.2) false = true := by rw [← hueq]; exact hux
  have hclt : (I.decode x).getD p.1 I.size < I.size := decode_lt I hx h1
  have hrb2 : I.rowRow p.1 < I.nbase := I.rowRow_lt_nbase h1
  have hrr2 : I.rowRow p.1 < I.nrows := by simpa only [Instance.nrows] using hrb2
  have hm1 : I.cellVar p.1 p.2 ∈ I.hitList x (I.rowRow p.1) :=
    Instance.mem_hitList.mpr ⟨I.cellVar_lt_nvars h1 h2, hset,
      (I.contains_base hrb2).mpr
        ((I.baseInRow_rowRow h1).mpr ⟨I.cellVar_lt h1 h2, I.cellVar_div h2⟩)⟩
  have hm2 : I.cellVar p.1 ((I.decode x).getD p.1 I.size) ∈ I.hitList x (I.rowRow p.1) :=
    Instance.mem_hitList.mpr ⟨I.cellVar_lt_nvars h1 hclt, decode_set I hx h1,
      (I.contains_base hrb2).mpr
        ((I.baseInRow_rowRow h1).mpr ⟨I.cellVar_lt h1 hclt, I.cellVar_div hclt⟩)⟩
  exact ((I.cellVar_inj h2 hclt (hitList_unique I hx hrr2 hm1 hm2)).2).symm

/-- **Soundness of the encoding.**

A zero of the QUBO decodes to a completion of the given placement. With `QUBO.Net`'s energy
bridge this says the ground states of the Hopfield/Boltzmann network built from `problem I` are
exactly the solutions of the completion instance. -/
theorem decode_isQueens (I : Instance) (hG : I.givensOk = true) {x : Array Bool}
    (hx : (problem I).penaltyDoubled x = 0) : I.isQueens (I.decode x) = true :=
  I.isQueens_of (I.decode_size x) (fun _ hi => decode_lt I hx hi)
    (fun _ hi _ hi' hne => ⟨decode_col I hx hi hi' hne, decode_diag I hx hi hi' hne,
      decode_anti I hx hi hi' hne⟩)
    (fun _ hp => decode_given I hG hx hp)

/-! ## Completeness: a completion *is* a zero

The encoder is the obvious one on the cell variables, `x_{i,j} = [q i = j]`, and on a slack takes
the only value that can close its row: `s_e = 1` exactly when no queen lies on the diagonal that
row constrains. Row by row:

* the board row `Σ_j x_{i,j} = 1` holds because `q i` is one legal column;
* the column row `Σ_i x_{i,j} = 1` holds because `i ↦ q i` is injective on `N` rows into `N`
  columns, hence a bijection — this is the one place a **pigeonhole** argument is needed, and it
  is why the column constraints may be equalities rather than at-most-ones;
* a slack row `Σ x + s_e = 1` holds because at most one queen lies on each diagonal, and the
  slack supplies the missing `1` exactly when none does;
* a given row `x_{i,j} = 1` holds because the board extends the placement.
-/

namespace Instance

/-- **The encoder.** A cell variable is set iff the board puts its queen there; a slack is set iff
no queen lies on the diagonal its row constrains. -/
def encode (I : Instance) (q : Array Nat) : Array Bool :=
  (Array.range I.nvars).map fun u =>
    if u < I.ncells then q.getD (u / I.size) I.size == u % I.size
    else (List.range I.size).all fun i => !I.onSlack i (q.getD i I.size) (u - I.ncells)

theorem encode_getD (I : Instance) (q : Array Nat) {u : Nat} (hu : u < I.nvars) :
    (I.encode q).getD u false =
      (if u < I.ncells then q.getD (u / I.size) I.size == u % I.size
       else (List.range I.size).all fun i => !I.onSlack i (q.getD i I.size) (u - I.ncells)) :=
  map_range_getD _ _ _ hu

/-- `x_{i,j} = 1` iff the board puts the queen of row `i` in column `j`. -/
theorem encode_cellVar (I : Instance) (q : Array Nat) {i j : Nat} (hi : i < I.size)
    (hj : j < I.size) :
    (I.encode q).getD (I.cellVar i j) false = (q.getD i I.size == j) := by
  rw [I.encode_getD q (I.cellVar_lt_nvars hi hj), if_pos (I.cellVar_lt hi hj),
    I.cellVar_div hj, I.cellVar_mod hj]

/-- `s_e = 1` iff no queen lies on the diagonal that slack row `e` constrains. -/
theorem encode_slackVar (I : Instance) (q : Array Nat) {e : Nat} (he : e < 2 * I.ndiags) :
    (I.encode q).getD (I.slackVar e) false
      = ((List.range I.size).all fun i => !I.onSlack i (q.getD i I.size) e) := by
  have hnot : ¬ (I.slackVar e < I.ncells) := by simp only [slackVar]; omega
  rw [I.encode_getD q (I.slackVar_lt_nvars he), if_neg hnot,
    show I.slackVar e - I.ncells = e from by simp only [slackVar]; omega]

end Instance

/-- A duplicate-free list all of whose elements equal one of its members is a singleton. -/
private theorem length_eq_one_of_all_eq : ∀ (L : List Nat), L.Nodup → ∀ a, a ∈ L →
    (∀ b ∈ L, b = a) → L.length = 1 := by
  intro L
  match L with
  | [] => intro _ a ha _; exact absurd ha (by simp)
  | [_] => intro _ _ _ _; rfl
  | b :: c :: t =>
    intro hnd a _ hall
    have hb : b = a := hall b (by simp)
    have hc : c = a := hall c (by simp)
    exact absurd (show b ∈ c :: t by rw [hb, ← hc]; exact List.mem_cons_self ..)
      ((List.nodup_cons.mp hnd).1)

/-- …and it is the singleton on that member. -/
private theorem eq_singleton_of_all_eq {L : List Nat} (hnd : L.Nodup) {a : Nat} (ha : a ∈ L)
    (hall : ∀ b ∈ L, b = a) : L = [a] := by
  obtain ⟨c, hc⟩ := List.length_eq_one_iff.mp (length_eq_one_of_all_eq L hnd a ha hall)
  rw [hc] at ha ⊢
  rw [List.mem_singleton] at ha
  rw [ha]

/-- **Pigeonhole: every column of a checked board carries a queen.**

`i ↦ q i` is an injection of the `N` board rows into the `N` columns, so its image is all of
them. This is the only non-formal step in the completeness proof, and the reason the column
constraints can be equalities: at-most-one plus one-queen-per-row already forces exactly one per
column, so the `N` column rows need no slacks. -/
theorem exists_row_of_col (I : Instance) {q : Array Nat} (hq : I.isQueens q = true) {j : Nat}
    (hj : j < I.size) : ∃ i, i < I.size ∧ q.getD i I.size = j := by
  classical
  set f : Nat → Nat := fun i => q.getD i I.size with hf
  have hinj : Set.InjOn f ↑(Finset.range I.size) := by
    intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    by_contra hne
    exact (Instance.isQueens_pair hq ha hb hne).1 hab
  have himg : (Finset.range I.size).image f = Finset.range I.size := by
    refine Finset.eq_of_subset_of_card_le (fun y hy => ?_) ?_
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
      exact Finset.mem_range.mpr (Instance.isQueens_lt hq (Finset.mem_range.mp hi))
    · rw [Finset.card_image_of_injOn hinj]
  have hjm : j ∈ (Finset.range I.size).image f := by
    rw [himg]; exact Finset.mem_range.mpr hj
  obtain ⟨i, hi, hfi⟩ := Finset.mem_image.mp hjm
  exact ⟨i, Finset.mem_range.mp hi, hfi⟩

/-- Two queens of a checked board cannot share a slack row. -/
theorem onSlack_clash (I : Instance) {q : Array Nat} (hq : I.isQueens q = true) {i i' e : Nat}
    (hi : i < I.size) (hi' : i' < I.size) (hne : i ≠ i')
    (h1 : I.onSlack i (q.getD i I.size) e = true)
    (h2 : I.onSlack i' (q.getD i' I.size) e = true) : False := by
  obtain ⟨-, hdiag, hanti⟩ := Instance.isQueens_pair hq hi hi' hne
  by_cases hd : e < I.ndiags
  · rw [I.onSlack_lo hd] at h1 h2
    exact hdiag (by omega)
  · rw [I.onSlack_hi hd] at h1 h2
    exact hanti (by omega)

/-- **A board row of an encoded completion holds exactly one set variable**, namely `x_{i, q i}`. -/
theorem encode_hitList_rowRow (I : Instance) {q : Array Nat} (hq : I.isQueens q = true)
    {i : Nat} (hi : i < I.size) : (I.hitList (I.encode q) (I.rowRow i)).length = 1 := by
  have hN : 0 < I.size := by omega
  have hc : q.getD i I.size < I.size := Instance.isQueens_lt hq hi
  have hrb : I.rowRow i < I.nbase := I.rowRow_lt_nbase hi
  refine length_eq_one_of_all_eq _ (I.hitList_nodup _ _) (I.cellVar i (q.getD i I.size)) ?_ ?_
  · refine Instance.mem_hitList.mpr ⟨I.cellVar_lt_nvars hi hc, ?_, ?_⟩
    · rw [I.encode_cellVar q hi hc]; simp
    · exact (I.contains_base hrb).mpr
        ((I.baseInRow_rowRow hi).mpr ⟨I.cellVar_lt hi hc, I.cellVar_div hc⟩)
  · intro b hb
    obtain ⟨hblt, hbx, hbrow⟩ := Instance.mem_hitList.mp hb
    obtain ⟨hbcell, hbdiv⟩ := (I.baseInRow_rowRow hi).mp ((I.contains_base hrb).mp hbrow)
    have hmod : b % I.size < I.size := Nat.mod_lt _ hN
    have hbeq : I.cellVar i (b % I.size) = b := by
      simp only [Instance.cellVar, ← hbdiv]; exact Nat.div_add_mod b I.size
    rw [← hbeq, I.encode_cellVar q hi hmod] at hbx
    simp only [beq_iff_eq] at hbx
    rw [← hbeq, hbx]

/-- **A column row of an encoded completion holds exactly one set variable.** Existence is the
pigeonhole `exists_row_of_col`, uniqueness the checker's column clause. -/
theorem encode_hitList_colRow (I : Instance) {q : Array Nat} (hq : I.isQueens q = true)
    {j : Nat} (hj : j < I.size) : (I.hitList (I.encode q) (I.colRow j)).length = 1 := by
  obtain ⟨i0, hi0, hq0⟩ := exists_row_of_col I hq hj
  have hrb : I.colRow j < I.nbase := I.colRow_lt_nbase hj
  refine length_eq_one_of_all_eq _ (I.hitList_nodup _ _) (I.cellVar i0 j) ?_ ?_
  · refine Instance.mem_hitList.mpr ⟨I.cellVar_lt_nvars hi0 hj, ?_, ?_⟩
    · rw [I.encode_cellVar q hi0 hj, hq0]; simp
    · exact (I.contains_base hrb).mpr
        ((I.baseInRow_colRow hj).mpr ⟨I.cellVar_lt hi0 hj, I.cellVar_mod hj⟩)
  · intro b hb
    obtain ⟨hblt, hbx, hbrow⟩ := Instance.mem_hitList.mp hb
    obtain ⟨hbcell, hbmod⟩ := (I.baseInRow_colRow hj).mp ((I.contains_base hrb).mp hbrow)
    have hbdiv : b / I.size < I.size :=
      Nat.div_lt_of_lt_mul (by simpa only [Instance.ncells] using hbcell)
    have hbeq : I.cellVar (b / I.size) j = b := by
      simp only [Instance.cellVar, ← hbmod]; exact Nat.div_add_mod b I.size
    rw [← hbeq, I.encode_cellVar q hbdiv hj] at hbx
    simp only [beq_iff_eq] at hbx
    have hii : b / I.size = i0 := by
      by_contra hne
      exact (Instance.isQueens_pair hq hbdiv hi0 hne).1 (by rw [hbx, hq0])
    rw [← hbeq, hii]

/-- **A slack row of an encoded completion holds exactly one set variable**: either the one queen
on its diagonal, or — if the diagonal is empty — its slack. -/
theorem encode_hitList_slackRow (I : Instance) {q : Array Nat} (hq : I.isQueens q = true)
    {e : Nat} (he : e < 2 * I.ndiags) :
    (I.hitList (I.encode q) (I.slackRow e)).length = 1 := by
  have h2 : 2 ≤ I.size := I.two_le_size_of_slack he
  have hN : 0 < I.size := by omega
  have hrb : I.slackRow e < I.nbase := I.slackRow_lt_nbase he
  have hchar : ∀ b, b ∈ I.hitList (I.encode q) (I.slackRow e) ↔
      ((∃ i, i < I.size ∧ b = I.cellVar i (q.getD i I.size)
              ∧ I.onSlack i (q.getD i I.size) e = true)
        ∨ (b = I.slackVar e ∧ ∀ i < I.size, I.onSlack i (q.getD i I.size) e = false)) := by
    intro b
    rw [Instance.mem_hitList]
    constructor
    · rintro ⟨hblt, hbx, hbrow⟩
      rcases (I.baseInRow_slackRow he).mp ((I.contains_base hrb).mp hbrow) with
        ⟨hbcell, hbon⟩ | hbs
      · have hbdiv : b / I.size < I.size :=
          Nat.div_lt_of_lt_mul (by simpa only [Instance.ncells] using hbcell)
        have hbmod : b % I.size < I.size := Nat.mod_lt _ hN
        have hbeq : I.cellVar (b / I.size) (b % I.size) = b := by
          simp only [Instance.cellVar]; exact Nat.div_add_mod b I.size
        rw [← hbeq, I.encode_cellVar q hbdiv hbmod] at hbx
        simp only [beq_iff_eq] at hbx
        exact Or.inl ⟨b / I.size, hbdiv, by rw [hbx]; exact hbeq.symm, by rw [hbx]; exact hbon⟩
      · subst hbs
        rw [I.encode_slackVar q he] at hbx
        refine Or.inr ⟨rfl, fun i hi => ?_⟩
        simpa using (List.all_eq_true.mp hbx) i (List.mem_range.mpr hi)
    · rintro (⟨i, hi, rfl, hon⟩ | ⟨rfl, hall⟩)
      · have hci : q.getD i I.size < I.size := Instance.isQueens_lt hq hi
        refine ⟨I.cellVar_lt_nvars hi hci, by rw [I.encode_cellVar q hi hci]; simp, ?_⟩
        refine (I.contains_base hrb).mpr
          ((I.baseInRow_slackRow he).mpr (Or.inl ⟨I.cellVar_lt hi hci, ?_⟩))
        rw [I.cellVar_div hci, I.cellVar_mod hci]; exact hon
      · refine ⟨I.slackVar_lt_nvars he, ?_, ?_⟩
        · rw [I.encode_slackVar q he]
          exact List.all_eq_true.mpr fun i hi => by
            rw [hall i (List.mem_range.mp hi)]; simp
        · exact (I.contains_base hrb).mpr ((I.baseInRow_slackRow he).mpr (Or.inr rfl))
  by_cases hocc : ∃ i, i < I.size ∧ I.onSlack i (q.getD i I.size) e = true
  · obtain ⟨i0, hi0, hon0⟩ := hocc
    refine length_eq_one_of_all_eq _ (I.hitList_nodup _ _) (I.cellVar i0 (q.getD i0 I.size))
      ((hchar _).mpr (Or.inl ⟨i0, hi0, rfl, hon0⟩)) ?_
    intro b hb
    rcases (hchar b).mp hb with ⟨i, hi, rfl, hon⟩ | ⟨-, hall⟩
    · by_cases hii : i = i0
      · rw [hii]
      · exact (onSlack_clash I hq hi hi0 hii hon hon0).elim
    · exact absurd hon0 (by rw [hall i0 hi0]; simp)
  · have hall : ∀ i < I.size, I.onSlack i (q.getD i I.size) e = false := by
      intro i hi
      by_contra hcon
      exact hocc ⟨i, hi, by simpa using hcon⟩
    refine length_eq_one_of_all_eq _ (I.hitList_nodup _ _) (I.slackVar e)
      ((hchar _).mpr (Or.inr ⟨rfl, hall⟩)) ?_
    intro b hb
    rcases (hchar b).mp hb with ⟨i, hi, rfl, hon⟩ | ⟨hb', -⟩
    · exact absurd hon (by rw [hall i hi]; simp)
    · exact hb'

/-- **A given row of an encoded completion holds exactly one set variable**: its own, since the
board extends the placement. -/
theorem encode_hitList_givRow (I : Instance) (hG : I.givensOk = true) {q : Array Nat}
    (hq : I.isQueens q = true) {k : Nat} (hk : k < I.ngivens) :
    (I.hitList (I.encode q) (I.givRow k)).length = 1 := by
  have hk' : k < I.givens.size := by simpa [Instance.ngivens] using hk
  obtain ⟨p, hp, hpmem⟩ : ∃ p, I.givens[k]? = some p ∧ p ∈ I.givens.toList :=
    ⟨I.givens[k], Array.getElem?_eq_getElem hk', Array.mem_toList_iff.mpr (Array.getElem_mem hk')⟩
  obtain ⟨h1, h2⟩ := Instance.givensOk_lt hG hpmem
  have hqp : q.getD p.1 I.size = p.2 := Instance.isQueens_given hq hpmem
  have hrb : I.givRow k < I.nbase := I.givRow_lt_nbase hk
  refine length_eq_one_of_all_eq _ (I.hitList_nodup _ _) (I.cellVar p.1 p.2) ?_ ?_
  · refine Instance.mem_hitList.mpr ⟨I.cellVar_lt_nvars h1 h2, ?_, ?_⟩
    · rw [I.encode_cellVar q h1 h2, hqp]; simp
    · exact (I.contains_base hrb).mpr ((I.baseInRow_givRow_eq hp h1 h2).mpr rfl)
  · intro b hb
    obtain ⟨-, -, hbrow⟩ := Instance.mem_hitList.mp hb
    exact (I.baseInRow_givRow_eq hp h1 h2).mp ((I.contains_base hrb).mp hbrow)

/-- **Every row of an encoded completion holds exactly one set variable.** -/
theorem encode_hitList_length (I : Instance) (hG : I.givensOk = true) {q : Array Nat}
    (hq : I.isQueens q = true) {r : Nat} (hr : r < I.nrows) :
    (I.hitList (I.encode q) r).length = 1 := by
  have hr' : r < I.nbase := by simpa only [Instance.nrows] using hr
  rcases I.eq_rowKind hr' with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨e, he, rfl⟩ | ⟨k, hk, rfl⟩
  · exact encode_hitList_rowRow I hq hi
  · exact encode_hitList_colRow I hq hj
  · exact encode_hitList_slackRow I hq he
  · exact encode_hitList_givRow I hG hq hk

/-- **An encoded completion meets every row exactly**: `ρ_r = 1 = b̂_r`. -/
theorem encode_rowSum (I : Instance) (hG : I.givensOk = true) {q : Array Nat}
    (hq : I.isQueens q = true) {r : Nat} (hr : r < I.nrows) :
    ((problem I).rowSums (I.encode q)).getD r 0 = (problem I).bhat.getD r 0 := by
  rw [rowSums_spec (problem I) (problem_wf I) _ hr, problem_bhat I hr]
  have hcount : ((List.range I.nvars).countP
      fun u => (I.encode q).getD u false
        && ((problem I).rowsOf.getD u #[]).contains r) = 1 := by
    rw [List.countP_eq_length_filter,
      List.filter_congr (q := fun u => (I.encode q).getD u false && (I.rowsOf u).contains r)
        (fun u hu => by rw [problem_rowsOf I (List.mem_range.mp hu)])]
    exact encode_hitList_length I hG hq hr
  exact_mod_cast hcount

/-- **Completeness of the encoding.**

A completion of the given placement encodes to a zero of the objective. Together with
`decode_isQueens` this makes the QUBO an exact reduction, not merely a sound one; the only
hypothesis is `givensOk`, that the given queens are on the board. -/
theorem encode_penalty_zero (I : Instance) (hG : I.givensOk = true) {q : Array Nat}
    (hq : I.isQueens q = true) : (problem I).penaltyDoubled (I.encode q) = 0 :=
  penalty_zero_of_rowSums (problem I) fun _ hr => encode_rowSum I hG hq hr

/-- **The round trip.** `encode` and `decode` are mutually inverse on completions: decoding an
encoded board returns it on the nose. -/
theorem decode_encode (I : Instance) {q : Array Nat} (hq : I.isQueens q = true) :
    I.decode (I.encode q) = q := by
  have hgetD : ∀ (a : Array Nat) (j d : Nat) (hj : j < a.size), a.getD j d = a[j] := by
    intro a j d hj
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj]
    rfl
  have hsize : (I.decode (I.encode q)).size = q.size := by
    rw [I.decode_size, Instance.isQueens_size hq]
  refine Array.ext hsize ?_
  intro i hi1 hi2
  have hi : i < I.size := by rw [I.decode_size] at hi1; exact hi1
  have hci : q.getD i I.size < I.size := Instance.isQueens_lt hq hi
  have hhits : I.hitsAt (I.encode q) i = [q.getD i I.size] := by
    refine eq_singleton_of_all_eq (List.Nodup.filter _ List.nodup_range) ?_ ?_
    · simp only [List.mem_filter, List.mem_range]
      exact ⟨hci, by rw [I.encode_cellVar q hi hci]; simp⟩
    · intro b hb
      simp only [List.mem_filter, List.mem_range] at hb
      rw [I.encode_cellVar q hi hb.1] at hb
      exact (beq_iff_eq.mp hb.2).symm
  rw [← hgetD _ _ I.size hi1, ← hgetD _ _ I.size hi2, I.decode_getD _ hi, hhits]
  rfl

/-- **The headline: the QUBO has a zero exactly when the placement can be completed.**

Left to right is `decode_isQueens`, right to left is `encode_penalty_zero`. So a solver report of
"no zero" is a proof that the partial placement is *blocked* — which is what `blocked4_no_queens`
and `blocked6_no_queens` in `Queens.Examples` extract.

The only hypothesis is `givensOk`. No lower bound on the board size is needed: at `N = 0`
`givensOk` already forces the placement to be empty and both sides hold, and at `N = 1` the
single cell is the unique solution. -/
theorem exists_zero_iff_queens (I : Instance) (hG : I.givensOk = true) :
    (∃ x, (problem I).penaltyDoubled x = 0) ↔ (∃ q, I.isQueens q = true) :=
  ⟨fun ⟨_, hx⟩ => ⟨_, decode_isQueens I hG hx⟩,
   fun ⟨_, hq⟩ => ⟨_, encode_penalty_zero I hG hq⟩⟩

end Queens
end QUBO
