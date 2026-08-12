/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.QUBO.Instances.Queens.Baseline
import HopfieldNet.QUBO.Instances.Queens.Widget

/-!
# `n`-Queens Completion: the measured results

The queens counterpart of `QUBO.Instances.ColouringBench`. Three tables:

1. **Completable instances** — the classical backtracking baseline, the collaborative search of
   eq. (7), and a single annealed Boltzmann machine of eq. (6), on the same boards.
2. **Blocked instances** — placements with no completion. The search must find no zero, and by
   `exists_zero_iff_queens` that failure is a statement about the board.
3. **Certified outputs** — the baseline's boards, checked by `Instance.isQueens`, and the
   resulting zeros of the QUBO obtained through completeness.

Everything is deterministic: `QUBO.Rng` is `splitmix64`, seeded from `seed0`, and nothing reads a
clock. Elaborating this file runs the search a few hundred times in the Lean interpreter and takes
on the order of ten minutes.

## The headline, stated before the numbers

**A single annealed Boltzmann machine is a poor `n`-queens solver and the swarm is a good one.**
That gap is much wider here than for graph colouring, and it is the most interesting thing the
corpus shows. It is not a defect of the encoding: `Queens.Converge.classic8_stationary_infeasible_tendsto_zero`
proves the chain's equilibrium law concentrates on the completions, so what fails is the schedule,
not the objective.

**The baseline wins outright**, as DSATUR does for colouring. Backtracking solves every completable
board in the corpus in microseconds and refutes every blocked one. The claim here is not speed; it
is that the neurodynamic solver's answers are theorems in both directions.
-/

namespace QUBO
namespace Queens
namespace Bench

open QUBO.Queens.Baseline

/-! ## Corpus -/

/-- An empty `n × n` board. -/
def empty (n : Nat) : Instance := ⟨n, #[]⟩

/-- A harder completion: five queens of `sol8` given, leaving three rows open. -/
def completion8b : Instance := ⟨8, #[(0, 0), (1, 4), (2, 7), (3, 5), (4, 2)]⟩

/-- A `7 × 7` completion with a corner queen. A corner queen is fatal at `N = 4` and `N = 6` and
harmless everywhere else in the corpus — `Baseline.count` on `⟨n, #[(0,0)]⟩` for `n = 4 … 10` is
`0, 2, 0, 4, 4, 28, 64` — so this row is completable, and is here to make that contrast visible
next to `Blk4` and `Blk6`. -/
def corner7 : Instance := ⟨7, #[(0, 0)]⟩

/-- **Blocked without an attack.** Two given queens on a `7 × 7` board that do not attack each
other — different columns, different diagonals — and yet admit no completion. This is the
phenomenon that makes Completion hard: legality of the givens is not the obstruction. Five rows
stay open, so `7^5 = 16807` tuples refute it by kernel reduction. -/
def blocked7 : Instance := ⟨7, #[(0, 0), (1, 6)]⟩

/-- The same at `N = 8`, where the refutation is out of reach of enumeration (`8^6 = 262144`
tuples) and the row is an observation rather than a theorem. -/
def blocked8 : Instance := ⟨8, #[(0, 0), (1, 2)]⟩

/-- One row of the tables. -/
structure Row where
  /-- Display name. -/
  name : String
  /-- The instance. -/
  I : Instance
  /-- Seeds used by the swarm columns. -/
  seeds : Nat := 10
  /-- Seeds used by the single-anneal column. -/
  aseeds : Nat := 20
deriving Inhabited

/-- The completable corpus, in increasing order of board size. -/
def corpus : Array Row := #[
  ⟨"Q4",     empty 4,      10, 20⟩,
  ⟨"Q5",     empty 5,      10, 20⟩,
  ⟨"Q6",     empty 6,      10, 20⟩,
  ⟨"Q7",     empty 7,      10, 20⟩,
  ⟨"Q8",     empty 8,      10, 20⟩,
  ⟨"Q9",     empty 9,       5, 20⟩,
  ⟨"Q10",    empty 10,      5, 20⟩,
  ⟨"Comp6",  small6,       10, 20⟩,
  ⟨"Comp7",  corner7,      10, 20⟩,
  ⟨"Comp8",  completion8,  10, 20⟩,
  ⟨"Comp8b", completion8b, 10, 20⟩]

/-- Placements with no completion. -/
def blockedCorpus : Array Row := #[
  ⟨"Q2",     empty 2,   5, 10⟩,
  ⟨"Q3",     empty 3,   5, 10⟩,
  ⟨"Blk4",   blocked4,  5, 10⟩,
  ⟨"Blk6",   blocked6,  5, 10⟩,
  ⟨"Blk7",   blocked7,  5, 10⟩,
  ⟨"Blk8",   blocked8,  5, 10⟩,
  ⟨"Attack", attacking, 5, 10⟩]

/-! ## Configuration -/

/-- The model settings, shared with the colouring bench so the two are comparable.

**`tabulate` is not optional here.** `Problem.netVec` returns *twice* the local field (`theta` is
stored doubled), and `ModelConfig.tabulate` builds the logistic table at `2·T₀` to cancel that
exactly. The untabulated `Float` fallback in `bmmRun` divides by `T` rather than `2T`, so an
untabulated run at nominal `T₀` is really annealing from `T₀/2` — verified bit-for-bit: tabulated at
`T₀ = 3.0` is byte-identical to untabulated at `T₀ = 6.0`. `ColouringBench` and every `CNS` config
tabulate, so omitting it here would have made this table both wrong and incomparable with theirs.
`levels = 64 > innerIters = 40`, so the table covers the whole anneal. -/
def benchModel : ModelConfig :=
  ModelConfig.tabulate { innerIters := 40, levels := 64, T0 := 3.0, eta := 0.9 }

/-- Base seed. Fixed, so the table is reproducible. -/
def seed0 : Nat := 20260806

/-- One run of the collaborative search of eq. (7). -/
def runOne (I : Instance) (seed : Nat) : SearchResult :=
  search (problem I) Model.bmm
    { N := 20, M := 20, maxOuter := 60, model := benchModel,
      captureBoards := false, oneHotInit := true, groups := cellGroups I }
    (Rng.seed seed.toUInt64)

/-- The same search driven by **DHNm, eq. (3)** instead of BMm.

Two differences from `runOne`, both forced. `Model.dhnm` is the hard-threshold recurrence with
momentum, so it consumes no randomness at all — `dhnmRun` ignores the generator, and the swarm's
only stochasticity is initialisation, the PSO coefficients and mutation. And the diversity
threshold is `0.9` rather than BMm's `0.4`: that model-specific split was recovered on Sudoku, and
it transfers — at `0.4` DHNm fails on the empty `8 × 8` where at `0.9` it succeeds, which is
evidence the constant is principled rather than an artifact of the instance it was tuned on. -/
def runOneD (I : Instance) (seed : Nat) : SearchResult :=
  search (problem I) Model.dhnm
    { N := 20, M := 20, maxOuter := 60, model := benchModel, divThreshold := 0.9,
      captureBoards := false, oneHotInit := true, groups := cellGroups I }
    (Rng.seed seed.toUInt64)

/-- DHNm successes over `n` seeds. -/
def dhnmSolved (I : Instance) (n : Nat) : Nat :=
  (Array.range n).foldl (fun a i => if (runOneD I (seed0 + i)).solved then a + 1 else a) 0

/-- `(solved at seed0, outer at seed0, #solved over `n` seeds, total outer over `n` seeds)`. -/
def runSeeds (I : Instance) (n : Nat) : Bool × Nat × Nat × Nat :=
  let rs := (Array.range n).map fun i => runOne I (seed0 + i)
  let r0 := rs.getD 0 default
  (r0.solved, r0.outer,
   rs.foldl (fun a r => if r.solved then a + 1 else a) 0,
   rs.foldl (fun a r => a + r.outer) 0)

/-- How many of `n` single annealed runs of eq. (6) land on a completion, at the widget's
schedule `T = 3·0.99ᵗ` over 400 sweeps. -/
def annealHits (I : Instance) (n : Nat) : Nat :=
  (Array.range n).foldl (fun acc s =>
    let (x0, g) := randomStart I (Rng.seed (seed0 + s).toUInt64)
    if I.isQueens (I.decode (anneal (problem I) 400 3.0 0.99 g x0).back!) then acc + 1 else acc) 0

/-- Did the classical baseline find a completion? -/
def baseSolved (I : Instance) : Bool := (Baseline.solve I).isSome

/-- The baseline's board, checked by the library's own checker. `Baseline.solve_isQueens` proves
this cannot be `false`; printing it is a running check of that theorem. -/
def baseOk (I : Instance) : Bool :=
  match Baseline.solve I with
  | some q => I.isQueens q
  | none => true

/-! ## Printing -/

/-- Right-align in `w` columns. -/
def rpad (s : String) (w : Nat) : String := "".pushn ' ' (w - s.length) ++ s

/-- Left-align in `w` columns. -/
def lpad (s : String) (w : Nat) : String := s ++ "".pushn ' ' (w - s.length)

/-- `y`/`n`. -/
def yn (b : Bool) : String := if b then "y" else "n"

/-- `tot / n` to two decimals, without touching `Float`. -/
def mean2 (tot n : Nat) : String :=
  if n = 0 then "-" else
    let h := (100 * tot + n / 2) / n
    s!"{h / 100}." ++ (if h % 100 < 10 then "0" else "") ++ toString (h % 100)

/-- Header of the main table. -/
def header : String :=
  lpad "board" 8 ++ rpad "N" 3 ++ rpad "giv" 5 ++ rpad "vars" 6 ++ rpad "rows" 6
    ++ "  |" ++ rpad "sol" 5 ++ rpad "ok" 4 ++ rpad "count" 8
    ++ "  |" ++ rpad "hit" 5 ++ rpad "out" 5 ++ rpad "s/k" 7 ++ rpad "avg" 7
    ++ "  |" ++ rpad "dhnm" 7
    ++ "  |" ++ rpad "anneal" 8

/-- One row of the main table. -/
def line (r : Row) : String :=
  let (s1, o1, k1, t1) := runSeeds r.I r.seeds
  lpad r.name 8 ++ rpad (toString r.I.size) 3 ++ rpad (toString r.I.ngivens) 5
    ++ rpad (toString r.I.nvars) 6 ++ rpad (toString r.I.nrows) 6
    ++ "  |" ++ rpad (yn (baseSolved r.I)) 5 ++ rpad (yn (baseOk r.I)) 4
    ++ rpad (toString (Baseline.count r.I)) 8
    ++ "  |" ++ rpad (yn s1) 5 ++ rpad (toString o1) 5
    ++ rpad s!"{k1}/{r.seeds}" 7 ++ rpad (mean2 t1 r.seeds) 7
    ++ "  |" ++ rpad s!"{dhnmSolved r.I r.seeds}/{r.seeds}" 7
    ++ "  |" ++ rpad s!"{annealHits r.I r.aseeds}/{r.aseeds}" 8

/-- **The results table, on boards that can be completed.**

Columns: the board; `N`; the number of given queens; the QUBO's variable and row counts; then the
classical baseline — whether it found a completion, whether `Instance.isQueens` accepts the board
it returned, and the total number of completions; then the collaborative search of eq. (7) driving
**BMm, eq. (6)** — hit at `seed0`, its outer-iteration count, successes over the row's seeds, and
mean outer count; then the same swarm driving **DHNm, eq. (3)**, successes over the row's seeds;
then the fraction of single annealed runs of eq. (6), with no swarm at all, that landed on a
completion.

Both of Li & Wang's models therefore appear: eq. (3) and eq. (6) under eq. (7), plus eq. (6) alone.
The `anneal` column is the one that isolates a single machine, and it is the one that fails. -/
def table : IO Unit := do
  IO.println
    s!"BMm, N=20, M=20, maxOuter=60, inner=40, T0=3.0, eta=0.9, oneHotInit, base seed {seed0}"
  IO.println s!"anneal column: one BMm run, 400 sweeps, T = 3.0*0.99^t, same base seed"
  IO.println (lpad "" 28 ++ "  |" ++ lpad "     backtracking" 17 ++ "  |"
    ++ lpad "    swarm/BMm, eq. (6)+(7)" 24 ++ "  |" ++ lpad " eq.(3)" 7 ++ "  |"
    ++ " one anneal")
  IO.println header
  IO.println ("".pushn '-' header.length)
  for r in corpus do IO.println (line r)

#eval table

/-! ## Where there is nothing to find

The same measurement on placements with no completion. `count` is `0` on every row — that is the
baseline's exhaustive verdict — and the swarm correctly reports no zero. The `cert` column says
whether the *impossibility* is a theorem in this development rather than an observation: the small
boards are refuted below, and in `Queens.Examples`, by kernel enumeration over the tuples the
givens leave open. Only `Blk8` is out of reach (`8^6 = 262144`), and its row is marked accordingly
rather than quietly presented as if it carried the same weight.

`Blk7` is the row worth reading: its two given queens do not attack each other, and the board is
dead anyway. -/

/-- Is this row's impossibility proved in this development? -/
def certified (name : String) : Bool := name != "Blk8"

/-- Header of the blocked table. -/
def headerBlocked : String :=
  lpad "board" 8 ++ rpad "N" 3 ++ rpad "giv" 5 ++ rpad "vars" 6 ++ rpad "rows" 6
    ++ "  |" ++ rpad "count" 7 ++ rpad "cert" 6
    ++ "  |" ++ rpad "zero" 6 ++ rpad "out" 5 ++ rpad "s/k" 7 ++ rpad "bestpen" 9

/-- One row of the blocked table. -/
def lineBlocked (r : Row) : String :=
  let res := runOne r.I seed0
  let (_, o1, k1, _) := runSeeds r.I r.seeds
  lpad r.name 8 ++ rpad (toString r.I.size) 3 ++ rpad (toString r.I.ngivens) 5
    ++ rpad (toString r.I.nvars) 6 ++ rpad (toString r.I.nrows) 6
    ++ "  |" ++ rpad (toString (Baseline.count r.I)) 7 ++ rpad (yn (certified r.name)) 6
    ++ "  |" ++ rpad (yn res.solved) 6 ++ rpad (toString o1) 5
    ++ rpad s!"{k1}/{r.seeds}" 7 ++ rpad (toString res.penaltyDoubled) 9

/-- **The results table, on boards that cannot be completed.** -/
def tableBlocked : IO Unit := do
  IO.println s!"no completion exists on any row; `zero` and `s/k` must read n and 0/k"
  IO.println headerBlocked
  IO.println ("".pushn '-' headerBlocked.length)
  for r in blockedCorpus do IO.println (lineBlocked r)

#eval tableBlocked

/-! ## The counts, against the classical sequence

`Baseline.count` on the empty boards is the number of solutions of `n`-queens, OEIS A000170. The
published values for `n = 0 … 10` are `1, 1, 0, 0, 2, 10, 4, 40, 92, 352, 724`; the search
reproduces them. This is a check on the baseline, not a result — but it is the check that makes
the `count` column of the tables above worth printing. -/
#eval (List.range 11).map fun n => Baseline.count (empty n)

/-! ## Certified outputs

The tables report what ran. This section turns the positive rows into theorems: each board below
is the literal array the baseline returned, `isQueens` accepts it by kernel reduction, and
`encode_penalty_zero` turns that into a zero of the very objective the neurodynamics minimises.
No search is trusted — the arrays are data, and the checker is the one the soundness theorem
targets. -/

/-- The baseline's `8 × 8` board. -/
def bQ8 : Array Nat := #[0, 4, 7, 5, 2, 6, 1, 3]

/-- The baseline's `10 × 10` board. -/
def bQ10 : Array Nat := #[0, 2, 5, 7, 9, 4, 8, 1, 3, 6]

/-- The baseline's board for the five-given completion instance. -/
def bComp8b : Array Nat := #[0, 4, 7, 5, 2, 6, 1, 3]

theorem bQ8_isQueens : (empty 8).isQueens bQ8 = true := by decide +kernel
theorem bQ10_isQueens : (empty 10).isQueens bQ10 = true := by decide +kernel
theorem bComp8b_isQueens : completion8b.isQueens bComp8b = true := by decide +kernel

/-- **The 8-queens QUBO has a zero**, from the baseline's board through completeness. -/
theorem bQ8_zero : (problem (empty 8)).penaltyDoubled ((empty 8).encode bQ8) = 0 :=
  encode_penalty_zero (empty 8) (by decide) bQ8_isQueens

/-- **The 10-queens QUBO has a zero.** `nvars = 134`, well past what enumeration could reach. -/
theorem bQ10_zero : (problem (empty 10)).penaltyDoubled ((empty 10).encode bQ10) = 0 :=
  encode_penalty_zero (empty 10) (by decide) bQ10_isQueens

/-- **The five-given completion instance has a zero.** -/
theorem bComp8b_zero :
    (problem completion8b).penaltyDoubled (completion8b.encode bComp8b) = 0 :=
  encode_penalty_zero completion8b (by decide) bComp8b_isQueens

/-- …and therefore that board is completable, as a statement about boards. -/
theorem completion8b_completable : ∃ q, completion8b.isQueens q = true :=
  ⟨bComp8b, bComp8b_isQueens⟩

/-! ## Certified refutations

The `cert` column of the blocked table, discharged. Each is a statement **about boards** —
`¬ ∃ q, isQueens q` — and by `exists_zero_iff_queens` each upgrades to "no bit vector reaches
penalty zero", which is what makes the solver's negative answer meaningful. `Blk4`, `Blk6` and
`Attack` are in `Queens.Examples`; the three below complete the column. -/

private theorem q2_aux : ∀ a < 2, ∀ b < 2, (empty 2).isQueens #[a, b] = false := by decide +kernel

/-- **The `2 × 2` board has no solution** — the two queens must share a diagonal. -/
theorem q2_no_queens : ¬ ∃ q, (empty 2).isQueens q = true := by
  rintro ⟨q, hq⟩
  have hs : q.size = 2 := Instance.isQueens_size hq
  have hb : ∀ i, i < 2 → q.getD i 2 < 2 := fun _ hi => Instance.isQueens_lt hq hi
  have hq' : (empty 2).isQueens #[q.getD 0 2, q.getD 1 2] = true := by
    refine Instance.isQueens_congr (empty 2) (by decide) (by simp [hs]) (fun i hi => ?_) hq
    have hi2 : i < 2 := hi
    interval_cases i <;> simp [empty]
  exact Bool.noConfusion (hq' ▸ q2_aux _ (hb 0 (by omega)) _ (hb 1 (by omega)))

private theorem q3_aux : ∀ a < 3, ∀ b < 3, ∀ c < 3,
    (empty 3).isQueens #[a, b, c] = false := by decide +kernel

/-- **The `3 × 3` board has no solution.** -/
theorem q3_no_queens : ¬ ∃ q, (empty 3).isQueens q = true := by
  rintro ⟨q, hq⟩
  have hs : q.size = 3 := Instance.isQueens_size hq
  have hb : ∀ i, i < 3 → q.getD i 3 < 3 := fun _ hi => Instance.isQueens_lt hq hi
  have hq' : (empty 3).isQueens #[q.getD 0 3, q.getD 1 3, q.getD 2 3] = true := by
    refine Instance.isQueens_congr (empty 3) (by decide) (by simp [hs]) (fun i hi => ?_) hq
    have hi3 : i < 3 := hi
    interval_cases i <;> simp [empty]
  exact Bool.noConfusion
    (hq' ▸ q3_aux _ (hb 0 (by omega)) _ (hb 1 (by omega)) _ (hb 2 (by omega)))

private theorem blk7_aux : ∀ c < 7, ∀ d < 7, ∀ e < 7, ∀ f < 7, ∀ g < 7,
    blocked7.isQueens #[0, 6, c, d, e, f, g] = false := by decide +kernel

/-- **`blocked7` cannot be completed**, and its two given queens do not attack each other.

`7^5 = 16807` tuples, by kernel reduction. This is the corpus's cleanest illustration of why
Completion is hard while plain `n`-queens is easy: nothing local is wrong with the givens. -/
theorem blk7_no_queens : ¬ ∃ q, blocked7.isQueens q = true := by
  rintro ⟨q, hq⟩
  have hs : q.size = 7 := Instance.isQueens_size hq
  have hg0 : q.getD 0 7 = 0 := Instance.isQueens_given hq (p := (0, 0)) (by decide)
  have hg1 : q.getD 1 7 = 6 := Instance.isQueens_given hq (p := (1, 6)) (by decide)
  have hb : ∀ i, i < 7 → q.getD i 7 < 7 := fun _ hi => Instance.isQueens_lt hq hi
  have hq' : blocked7.isQueens
      #[0, 6, q.getD 2 7, q.getD 3 7, q.getD 4 7, q.getD 5 7, q.getD 6 7] = true := by
    refine Instance.isQueens_congr blocked7 (by decide) (by simp [hs]) (fun i hi => ?_) hq
    have hi7 : i < 7 := hi
    interval_cases i <;> simp [hg0, hg1, blocked7]
  exact Bool.noConfusion (hq' ▸ blk7_aux _ (hb 2 (by omega)) _ (hb 3 (by omega))
    _ (hb 4 (by omega)) _ (hb 5 (by omega)) _ (hb 6 (by omega)))

/-- …and hence no bit vector reaches penalty zero on `blocked7`'s QUBO. -/
theorem blk7_no_zero : ¬ ∃ x, (problem blocked7).penaltyDoubled x = 0 :=
  fun h => blk7_no_queens ((exists_zero_iff_queens blocked7 (by decide)).mp h)

/-! ## Sizes

`nvars = N² + 4N − 6` and `nrows = 6N − 6 + #givens`, checked at the corpus's extremes. -/

example : (empty 4).nvars = 26 ∧ (empty 4).nrows = 18 := by decide
example : (empty 10).nvars = 134 ∧ (empty 10).nrows = 54 := by decide
example : completion8b.nvars = 90 ∧ completion8b.nrows = 47 := by decide

/-! ## Axioms -/

#print axioms bQ10_zero
#print axioms completion8b_completable
#print axioms q2_no_queens
#print axioms q3_no_queens
#print axioms blk7_no_queens
#print axioms blk7_no_zero

end Bench
end Queens
end QUBO
