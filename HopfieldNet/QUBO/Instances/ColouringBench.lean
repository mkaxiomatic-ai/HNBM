/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.QUBO.Instances.ColouringBaseline
import HopfieldNet.QUBO.Search

/-!
# The results table: collaborative neurodynamics against greedy and DSATUR

One runner, one table. For every graph of the corpus below it reports

* `n`, `|E|`, the chromatic number `χ` (a cited fact, never proved here), and `Δ+1`, the palette
  size the baselines are *proved* to fit in (`Baseline.greedy_countColours_le`);
* how many colours `Baseline.greedy` and `Baseline.dsatur` actually use, and whether each output
  passes `Instance.isColouring` — the library's own checker, the same `Bool` that
  `Colouring.decode_isColouring` discharges for the neurodynamics;
* whether `QUBO.search` (Algorithm 2, BMm) drives the objective `‖Âx̂ − b̂‖²` of
  `Colouring.problem` to zero at palette `χ` — the decision problem *at* the chromatic number,
  where the feasible set is as thin as it ever gets — and at palette `χ+1`;
* the outer-iteration count it needed, at a fixed seed and averaged over several seeds.

A separate second table runs the same search at palette `χ−1`, where no colouring exists. It is
there for two reasons: to show that an infeasible instance terminates (it does, on the
stall criterion, not on the `maxOuter` cap), and as a cross-check on the `χ` column — a zero
found at `χ−1` would have *disproved* the chromatic number quoted for that row, since a zero
decodes to a proper colouring by `decode_isColouring`.

## The configuration, in full

`Model.bmm`, `N = 20`, `M = 20`, `maxOuter = 60`, `innerIters = 40`, `T₀ = 3.0`, `η = 0.9`,
`captureBoards := false`, `oneHotInit := true` with one group per vertex (its `ncolours` colour
variables, `Bench.cellGroups` — the same thing `Demo.lean` passes), everything else at the
`SearchConfig` default, i.e. `c₀ = 0.5`, `c₁ = 2.0`, `c₂ = 0.25`, `Pₘ = 0.05`, `𝒯 = 0.4`,
synchronous neuron updates. Seed `Bench.seed0 = 20260806`; the reliability columns use
`seed0, seed0+1, …`. Every number below is reproducible by re-elaborating this file: the PRNG is
`splitmix64` (`QUBO.Rng`) and nothing reads a clock.

The configuration is uniform across the corpus, deliberately: the per-instance tuning that
`Search.lean` documents for Sudoku (`T₀` in `3`-`8`, `innerIters ≈ nvars/3`) would make the rows
incomparable. `innerIters = 40` is a little generous for the small graphs and a little tight for
the largest (`nvars/3 ≈ 157` on `Myc3`), so the largest row is, if anything, flattered by the
baselines rather than by the search.

## Cost

Elaborating this file runs the search 300-odd times in the Lean interpreter and takes about ten
minutes, most of it on the two `Myc3` columns. That is why the corpus stops at 23 vertices.
-/

namespace QUBO
namespace Colouring
namespace Bench

open Baseline

/-! ## Four graph families, and the corpus

`Baseline.lean` already supplies `gK3`-`gWheel6`. Its eleven graphs are all easy: the search
below solves every one of them at `χ`, so on their own they separate nothing. The four
constructions here extend the corpus upwards while keeping `χ` a *known* quantity rather than a
guess:

* `cycle n` — `χ = 2` for even `n`, `3` for odd `n ≥ 3`;
* `crown k` — `K_{k,k}` minus a perfect matching, bipartite, so `χ = 2` for `k ≥ 2`; the standard
  adversarial input for first-fit, which it drags to `k` colours;
* `cocktail k` — the complete multipartite graph `K_{2,…,2}` on `k` parts, `χ = k`;
* `mycielskian` — Mycielski's construction (J. Mycielski, *Sur le coloriage des graphes*, Colloq.
  Math. 3 (1955) 161-162), which satisfies `χ(M(G)) = χ(G) + 1` and preserves triangle-freeness.
  `M(K₂) = C₅` and `M(C₅)` is the Grötzsch graph, so `M(Grötzsch)` is the next graph of that
  chain: triangle-free, 23 vertices, `χ = 5`.

None of `χ = 2`, `χ = 3`, `χ = k`, `χ(M(G)) = χ(G)+1` is proved here; they are cited. What *is*
mechanically checked is that the constructions reproduce the hand-written graphs they overlap
with (`cycle 5 = gC5`, `cycle 6 = gC6`, `crown 4 = gCrown4`, on the nose, including edge order)
and that every graph in the corpus is `edgesOk`. -/

/-- The `n`-cycle `C_n`, vertices in cyclic order. -/
def cycle (n : Nat) : Instance :=
  ⟨n, 3, (Array.range n).map fun i => (i, (i + 1) % n)⟩

/-- The **crown graph** on `2k` vertices: `K_{k,k}` minus a perfect matching, numbered
`L i = 2i`, `R j = 2j+1`, with `L i ~ R j` iff `i ≠ j`. Bipartite, so `χ = 2`; first-fit in this
interleaved order is forced to `k` colours. -/
def crown (k : Nat) : Instance :=
  ⟨2 * k, 2, (Array.range k).flatMap fun i =>
    ((Array.range k).filter (· != i)).map fun j => (2 * i, 2 * j + 1)⟩

/-- The **cocktail-party graph** `K_{2,…,2}` on `k` parts `{2i, 2i+1}`: complete multipartite,
so `χ = k`, and `(2k-2)`-regular. The densest thing in the corpus for its size. -/
def cocktail (k : Nat) : Instance :=
  ⟨2 * k, k, (Array.range (2 * k)).flatMap fun u =>
    ((Array.range (2 * k)).filter (fun v => u < v && u / 2 != v / 2)).map fun v => (u, v)⟩

/-- **Mycielski's construction.** From `G` on `n` vertices: keep `v_i = i`, add a shadow
`u_i = n + i` adjacent to every neighbour of `v_i`, and a hub `w = 2n` adjacent to every shadow.
`χ(M(G)) = χ(G) + 1`, and `M(G)` is triangle-free whenever `G` is. The palette is bumped by one
to match, though every run below sets it explicitly through `withPalette`. -/
def mycielskian (I : Instance) : Instance :=
  let n := I.nverts
  { nverts := 2 * n + 1, ncolours := I.ncolours + 1,
    edges := I.edges
      ++ I.edges.flatMap (fun e => #[(n + e.1, e.2), (n + e.2, e.1)])
      ++ (Array.range n).map (fun i => (2 * n, n + i)) }

/-- `C₉`: an odd cycle large enough that a colouring has to be found rather than stumbled on. -/
def gC9 : Instance := cycle 9

/-- The crown graph on 12 vertices. `χ = 2`; first-fit uses six colours. -/
def gCrown6 : Instance := crown 6

/-- `K_{2,2,2,2}`: eight vertices, 24 edges, `χ = 4`, `Δ+1 = 7`. -/
def gCocktail8 : Instance := cocktail 4

/-- `M(Grötzsch) = M³(K₂)`: triangle-free, 23 vertices, 71 edges, `χ = 5`. The hard row. -/
def gMyc3 : Instance := mycielskian gGrotzsch

set_option maxHeartbeats 4000000 in
/-- The constructions agree with `Baseline`'s hand-written graphs where they overlap. -/
example : (cycle 5).edges = gC5.edges ∧ (cycle 6).edges = gC6.edges
    ∧ (crown 4).edges = gCrown4.edges := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- Every new graph is simple with endpoints in range, so `Baseline`'s theorems and
`Colouring`'s soundness and completeness results all apply to them. -/
example : gC9.edgesOk = true ∧ gCrown6.edgesOk = true ∧ gCocktail8.edgesOk = true
    ∧ gMyc3.edgesOk = true := by decide +kernel

/-! ## The corpus -/

/-- One row: a graph, a display name, its chromatic number, and how many seeds the reliability
columns average over. The seed count is per-row only because the largest instance costs about a
minute per run; it is shown as the denominator of the `s/k` column, so no row can quietly report
a success rate over a different sample size than it looks. -/
structure Row where
  /-- Display name. -/
  name : String
  /-- The graph. Its `ncolours` field is irrelevant: every run sets the palette explicitly. -/
  I : Instance
  /-- The chromatic number. Cited, not proved. -/
  chi : Nat
  /-- Seeds used by the `s/k` and `avg` columns. -/
  seeds : Nat := 10
deriving Inhabited

/-- The corpus, in increasing order of `nvars` at palette `χ`. -/
def corpus : Array Row := #[
  ⟨"K3",        gK3,        3, 10⟩,
  ⟨"K4",        gK4,        4, 10⟩,
  ⟨"K5",        gK5,        5, 10⟩,
  ⟨"Path5",     gPath5,     2, 10⟩,
  ⟨"C5",        gC5,        3, 10⟩,
  ⟨"C6",        gC6,        2, 10⟩,
  ⟨"C9",        gC9,        3, 10⟩,
  ⟨"K33",       gK33,       2, 10⟩,
  ⟨"Crown4",    gCrown4,    2, 10⟩,
  ⟨"Crown6",    gCrown6,    2, 10⟩,
  ⟨"Wheel6",    gWheel6,    3, 10⟩,
  ⟨"Cocktail8", gCocktail8, 4, 10⟩,
  ⟨"Petersen",  gPetersen,  3, 10⟩,
  ⟨"Grotzsch",  gGrotzsch,  4, 10⟩,
  ⟨"Myc3",      gMyc3,      5, 3⟩]

/-! ## Checking a baseline output

The `ok` columns are not decoration. `Baseline.seqColour_isColouring` proves both rules produce a
proper colouring inside a palette of `Δ+1`, but the *number of colours* they use is measured, and
`properAt` re-checks properness against exactly that number — so a row claiming "2 colours, ok"
is claiming that `Instance.isColouring` returned `true` for a two-colour palette. -/

/-- `1 +` the largest colour in `col`: the smallest palette the array fits in. -/
def paletteOf (col : Array Nat) : Nat := col.foldl max 0 + 1

/-- Is `col` a proper colouring of `I` using no more colours than it names? Decided by the
library's checker, at the palette the measurement reports. -/
def properAt (I : Instance) (col : Array Nat) : Bool :=
  (withPalette I (paletteOf col)).isColouring col

/-! ## The run -/

/-- One group per vertex: its `ncolours` colour variables, exactly one of which a feasible point
sets. This is what `SearchConfig.oneHotInit` needs, and is the colouring analogue of Sudoku's
`openCellGroups`; `Demo.lean` builds the same thing. -/
def cellGroups (I : Instance) : Array (Array Nat) :=
  (Array.range I.nverts).map fun v => (Array.range I.ncolours).map fun i => I.colVar v i

/-- The BMm settings, shared by every run in this file. `levels = 64 > innerIters = 40`, so the
fixed-point logistic table of `ModelConfig.tabulate` covers the whole anneal and no run falls back
to `Float.exp`. -/
def benchModel : ModelConfig :=
  ModelConfig.tabulate { innerIters := 40, levels := 64, T0 := 3.0, eta := 0.9 }

/-- The seed. Every run in this file uses `seed0` or a small offset from it. -/
def seed0 : Nat := 20260806

/-- Number of variables of the QUBO for `I` at palette `k`: `k·(n + |E|)`. -/
def varsAt (I : Instance) (k : Nat) : Nat := k * (I.nverts + I.nedges)

/-- Algorithm 2 on `I` with a palette of `k` colours. -/
def runOne (I : Instance) (k seed : Nat) : SearchResult :=
  let J := withPalette I k
  search (problem J) Model.bmm
    { N := 20, M := 20, maxOuter := 60, model := benchModel,
      captureBoards := false, oneHotInit := true, groups := cellGroups J }
    (Rng.seed seed.toUInt64)

/-- `(solved at seed0, outer at seed0, #solved over `n` seeds, total outer over `n` seeds)`. -/
def runSeeds (I : Instance) (k n : Nat) : Bool × Nat × Nat × Nat :=
  let rs := (Array.range n).map fun i => runOne I k (seed0 + i)
  let r0 := rs.getD 0 default
  (r0.solved, r0.outer,
   rs.foldl (fun a r => if r.solved then a + 1 else a) 0,
   rs.foldl (fun a r => a + r.outer) 0)

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
  lpad "graph" 10 ++ rpad "n" 3 ++ rpad "|E|" 5 ++ rpad "chi" 5 ++ rpad "D+1" 5
    ++ "  |" ++ rpad "grdy" 6 ++ rpad "ok" 4 ++ rpad "dsat" 6 ++ rpad "ok" 4
    ++ "  |" ++ rpad "vars" 6 ++ rpad "hit" 5 ++ rpad "out" 5 ++ rpad "s/k" 7 ++ rpad "avg" 7
    ++ "  |" ++ rpad "vars" 6 ++ rpad "hit" 5 ++ rpad "out" 5 ++ rpad "s/k" 7 ++ rpad "avg" 7

/-- One row of the main table. -/
def line (r : Row) : String :=
  let g := greedy r.I
  let d := dsatur r.I
  let (s1, o1, k1, t1) := runSeeds r.I r.chi r.seeds
  let (s2, o2, k2, t2) := runSeeds r.I (r.chi + 1) r.seeds
  lpad r.name 10 ++ rpad (toString r.I.nverts) 3 ++ rpad (toString r.I.nedges) 5
    ++ rpad (toString r.chi) 5 ++ rpad (toString (maxDegree r.I + 1)) 5
    ++ "  |" ++ rpad (toString (countColours g)) 6 ++ rpad (yn (properAt r.I g)) 4
    ++ rpad (toString (countColours d)) 6 ++ rpad (yn (properAt r.I d)) 4
    ++ "  |" ++ rpad (toString (varsAt r.I r.chi)) 6 ++ rpad (yn s1) 5 ++ rpad (toString o1) 5
    ++ rpad s!"{k1}/{r.seeds}" 7 ++ rpad (mean2 t1 r.seeds) 7
    ++ "  |" ++ rpad (toString (varsAt r.I (r.chi + 1))) 6 ++ rpad (yn s2) 5
    ++ rpad (toString o2) 5 ++ rpad s!"{k2}/{r.seeds}" 7 ++ rpad (mean2 t2 r.seeds) 7

/-- **The results table.**

Columns, left to right: the graph; `n`; `|E|`; the cited `χ`; the proved baseline palette bound
`Δ+1`; then colours used by `greedy` and by `dsatur`, each with the verdict of
`Instance.isColouring` at that number of colours; then two blocks for the neurodynamics, at
palette `χ` and at palette `χ+1`, each giving the QUBO's variable count, whether the run at
`seed0` reached `p(x̂) = 0`, its outer-iteration count, how many of the row's seeds succeeded, and
the mean outer count over those seeds (a failed run contributes the iterations it burned before
the stall criterion fired). -/
def table : IO Unit := do
  IO.println
    s!"BMm, N=20, M=20, maxOuter=60, inner=40, T0=3.0, eta=0.9, oneHotInit, base seed {seed0}"
  IO.println (lpad "" 46 ++ "  |" ++ lpad "  palette chi" 30 ++ "  |" ++ "  palette chi+1")
  IO.println header
  IO.println ("".pushn '-' header.length)
  for r in corpus do IO.println (line r)

#eval table

/-! ## The same search where there is nothing to find -/

/-- One row of the infeasible table: palette `χ−1`, one seed. -/
def lineBelow (r : Row) : String :=
  let k := r.chi - 1
  let res := runOne r.I k seed0
  lpad r.name 10 ++ rpad (toString k) 4 ++ rpad (toString (varsAt r.I k)) 7
    ++ rpad (yn res.solved) 6 ++ rpad (toString res.outer) 7
    ++ rpad (toString res.penaltyDoubled) 7

/-- **Palette `χ−1`: an instance with no colouring at all.**

Every row must read `n` in the `hit` column, and does. Two things follow. First, the search
terminates on infeasible input — always on the stall criterion `M = 20`, never on the `maxOuter`
cap, so the cap is a safety net rather than the thing that stops these runs. Second, this is a
one-sided check on the `χ` column of the main table: a `y` here would have exhibited a proper
`(χ−1)`-colouring, by `decode_isColouring`, and refuted the chromatic number cited for that row.
A `n` proves nothing — the search failing is not the same as no colouring existing — except on
`K4` at palette 3, where `Colouring.k4_no_zero` already proves no bit vector whatever reaches
zero, and on `K5` at 4, `C5`/`C9` at 2, and the bipartite rows at 1, where the graph theory is
immediate. The `pen` column is `‖Âx̂ − b̂‖²` at the incumbent, i.e. twice the objective; `2` means
a single constraint row is off by one. -/
def tableBelow : IO Unit := do
  IO.println s!"palette chi-1 (infeasible), single seed {seed0}"
  IO.println (lpad "graph" 10 ++ rpad "chi-" 4 ++ rpad "vars" 7 ++ rpad "hit" 6
    ++ rpad "out" 7 ++ rpad "pen" 7)
  IO.println ("".pushn '-' 41)
  for r in corpus do IO.println (lineBelow r)

#eval tableBelow

/-! ## What the search found, certified

The tables are measurements: `#eval` runs compiled/interpreted code, and nothing in them is a
proof. This section closes that gap for four of the rows. The colour arrays below were *read off
the runs above* — they are `(withPalette I k).decode (runOne I k seed0).best` — and are then
pasted in as literals so that the kernel can check them.

What the kernel then certifies for each is a chain the measurement cannot supply on its own:

  `isColouring col = true` (`decide +kernel`)
    → `∃ x, (problem (withPalette I k)).penaltyDoubled x = 0` (`encode_penalty_zero`)
    → the Hopfield/Boltzmann network of `problem (withPalette I k)` has a ground state
      (`QUBO.Net`'s energy bridge, and `Colouring.exists_zero_iff_colourable` in the other
      direction).

So the search's output stops being a claim about a run and becomes a theorem about the instance.
That is the whole difference this file is here to show: the *number* in the table is only as good
as the interpreter, the *theorem* is checked by the kernel from a literal. -/

/-- BMm's 3-colouring of the Petersen graph, from `runOne gPetersen 3 seed0` (outer 1). -/
def wPetersen : Array Nat := #[0, 2, 0, 1, 2, 1, 1, 2, 0, 0]

/-- BMm's 4-colouring of the Grötzsch graph, from `runOne gGrotzsch 4 seed0` (outer 1). -/
def wGrotzsch : Array Nat := #[0, 3, 0, 2, 3, 1, 3, 1, 1, 1, 0]

/-- BMm's 2-colouring of the crown graph on 12 vertices, from `runOne gCrown6 2 seed0`
(outer 2) — the instance on which first-fit uses six colours. -/
def wCrown6 : Array Nat := #[0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]

/-- BMm's 6-colouring of `M(Grötzsch)`, from `runOne gMyc3 6 seed0` (outer 15). Six, not the
optimal five: at palette 5 the search failed on every seed, while both baselines succeed
(`myc3_greedy_five`). -/
def wMyc3 : Array Nat := #[5, 2, 3, 4, 3, 5, 0, 0, 0, 0, 4, 5, 1, 5, 1, 3, 1, 2, 0, 1, 3, 3, 4]

set_option maxHeartbeats 4000000 in
/-- The four search outputs are proper colourings in the palettes they were found in. -/
theorem witnesses_isColouring :
    (withPalette gPetersen 3).isColouring wPetersen = true
    ∧ (withPalette gGrotzsch 4).isColouring wGrotzsch = true
    ∧ (withPalette gCrown6 2).isColouring wCrown6 = true
    ∧ (withPalette gMyc3 6).isColouring wMyc3 = true := by
  decide +kernel

/-- **A 3-colouring of the Petersen graph is a zero of its 3-colour QUBO**, hence a ground state
of the corresponding Boltzmann network. Found by the neurodynamics; certified here. -/
theorem petersen_three_colour_zero :
    ∃ x, (problem (withPalette gPetersen 3)).penaltyDoubled x = 0 :=
  ⟨_, encode_penalty_zero (withPalette gPetersen 3) (by decide +kernel) witnesses_isColouring.1⟩

/-- The Grötzsch graph's 4-colour QUBO has a zero, from BMm's output. Optimal: `χ = 4`. -/
theorem grotzsch_four_colour_zero :
    ∃ x, (problem (withPalette gGrotzsch 4)).penaltyDoubled x = 0 :=
  ⟨_, encode_penalty_zero (withPalette gGrotzsch 4) (by decide +kernel)
    witnesses_isColouring.2.1⟩

/-- **The crown graph on 12 vertices is 2-colourable, certified from a search run.** First-fit
uses six colours here (`crown6_greedy_six`), so this is the clearest separation in the file: the
neurodynamics reaches `χ = 2` where the greedy baseline is off by a factor of three. DSATUR also
reaches 2. -/
theorem crown6_two_colour_zero :
    ∃ x, (problem (withPalette gCrown6 2)).penaltyDoubled x = 0 :=
  ⟨_, encode_penalty_zero (withPalette gCrown6 2) (by decide +kernel)
    witnesses_isColouring.2.2.1⟩

/-- `M(Grötzsch)` is 6-colourable, certified from a search run. Not optimal — `χ = 5`. -/
theorem myc3_six_colour_zero :
    ∃ x, (problem (withPalette gMyc3 6)).penaltyDoubled x = 0 :=
  ⟨_, encode_penalty_zero (withPalette gMyc3 6) (by decide +kernel)
    witnesses_isColouring.2.2.2⟩

set_option maxHeartbeats 4000000 in
/-- **Where the baselines win, also certified.** First-fit is dragged to six colours on the
bipartite crown graph, and DSATUR is not. -/
theorem crown6_greedy_six :
    countColours (greedy gCrown6) = 6 ∧ countColours (dsatur gCrown6) = 2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- **Both baselines 5-colour `M(Grötzsch)`, which the neurodynamics could not.** First-fit's
output is checked by the kernel against a palette of five, so the 5-colour QUBO of the instance
BMm failed on does have a zero (`myc3_five_colour_zero`). Since `χ = 5`, this is optimal, and it
is obtained with no search at all. -/
theorem myc3_greedy_five : (withPalette gMyc3 5).isColouring (greedy gMyc3) = true := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem myc3_baselines_five :
    countColours (greedy gMyc3) = 5 ∧ countColours (dsatur gMyc3) = 5 := by
  decide +kernel

/-- **The instance BMm failed on is feasible**, and a `Δ+1 = 12` argument is not what shows it:
first-fit happens to land on the optimum. So the failure at palette 5 in the table is a failure
of the search, not of the encoding. -/
theorem myc3_five_colour_zero :
    ∃ x, (problem (withPalette gMyc3 5)).penaltyDoubled x = 0 :=
  ⟨_, encode_penalty_zero (withPalette gMyc3 5) (by decide +kernel) myc3_greedy_five⟩

/-! ## What the numbers say

**Where the neurodynamics matches the baselines.** On all fourteen graphs up to 12 vertices it
reaches `χ` — `10/10` seeds, usually in one or two outer iterations — and so ties DSATUR
everywhere and beats first-fit on the two crown graphs, where first-fit uses `4` and `6` colours
against `χ = 2`. `Crown6` is the honest headline: `crown6_two_colour_zero` against
`crown6_greedy_six`. It is a headline about first-fit's worst case, though, not about search: the
crown graph is exactly the input first-fit is known to fail on, and DSATUR gets it right for free.

**Where it loses.** On `Myc3` (`M(Grötzsch)`, 23 vertices, `χ = 5`) the search does not solve the
decision problem at the chromatic number on any seed; it stalls at `penaltyDoubled = 2`, one
constraint row short. It needs a sixth colour to succeed. Both baselines use five —
`myc3_baselines_five`, and `myc3_greedy_five` certifies first-fit's five-colouring against the
kernel, which by `myc3_five_colour_zero` means the very QUBO the search failed on has a zero. So
on the one instance in this corpus that is large enough to be interesting, **the greedy baseline
wins outright**: it is optimal, instantaneous, and its output is certified by the same checker.
The `χ+1` column shows the same thing more quietly — the search needs 15 outer iterations at
palette 6 on that row, against `≤ 2` almost everywhere else.

The `Cocktail8` row is the other place the search visibly works for its answer: 10 outer
iterations at palette `4 = χ` on a graph with `Δ+1 = 7`, where both baselines are immediate.

So the ranking on this corpus is: DSATUR ≥ neurodynamics ≥ first-fit, with DSATUR never worse
than either and strictly better than the search on the largest instance. Nothing here suggests
Algorithm 2 is a good way to colour a graph.

**What the certification buys that a greedy colourer does not have.** Two distinct things, and
it is worth keeping them apart.

1. *The baselines are certified too, and that is the point of `Baseline.lean`, not of this file.*
   `Baseline.greedy_isColouring` and `seqColour_countColours_le` are theorems about first-fit for
   an arbitrary instance: its output is always proper and always fits in `Δ+1` colours. A greedy
   colourer written in C has no such guarantee, and `Baseline.greedy_exists_zero` turns it into a
   feasibility certificate for the objective this file's search minimises. Certification is not
   the neurodynamics' privilege.

2. *What the neurodynamics gets, and greedy cannot get, is a statement about the QUBO — hence
   about a physical machine.* `decode_isColouring` says every zero of `‖Âx̂ − b̂‖²` decodes to a
   proper colouring and `exists_zero_iff_colourable` says the converse, so the ground states of
   the Hopfield/Boltzmann network built from `problem I` are *exactly* the colourings of `I`. A
   run of Algorithm 2 is then a search over that network's state space, and whatever it returns is
   checkable by `Instance.isColouring` with the outcome guaranteed by a theorem rather than by
   inspection of the solver. That is what the witness section does: the arrays came out of an
   interpreted run whose correctness nobody has proved — the PSO rule, the annealing schedule, the
   PRNG — and the kernel certifies the results anyway, from literals, with the solver out of the
   loop. An unverified heuristic plus a verified encoding and checker is a verified decision
   procedure; that is the trade this whole directory makes, and it is what makes it safe for the
   heuristic to lose to DSATUR.

What none of this gives is a lower bound. Every `χ` in the table is cited, the `χ−1` table is
one-sided evidence at best, and neither baseline nor search can certify that a graph is *not*
`k`-colourable — for that the library has only the exhaustive `Colouring.triangle2_no_zero` and
`k4_no_zero`, at 3 and 4 vertices. "Solved the decision problem at `χ`" throughout means "found a
`χ`-colouring, `χ` being known from the literature", not "computed the chromatic number". -/

end Bench
end Colouring
end QUBO
