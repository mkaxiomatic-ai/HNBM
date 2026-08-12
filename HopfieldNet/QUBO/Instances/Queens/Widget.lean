/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.QUBO.Instances.Queens.Examples
import HopfieldNet.QUBO.Search
import HopfieldNet.QUBO.Widget

/-!
# Watching a board fill with queens

The `"board"` renderer of `quboPlayer.js`, driven by the `n`-Queens Completion QUBO. A frame is
one character per board row — `'.'` for "no queen in this row", otherwise the column index in
base 36 — so `PlayerProps` needs no new field: `nverts` carries the board size and `edges` the
given queens as `(row, column)` pairs.

Two views, as for graph colouring:

* `props` / `animate` — the collaborative search of eq. (7), one frame per **outer iteration**.
  Reliable, and the right thing for answering "is this placement completable?", but coarse.
* `fireProps` / `fireAt` — one annealed run of the Boltzmann machine of eq. (6), one frame per
  **sweep**. This is the one to press play on: queens flicker across the board while the
  temperature is high and the attacking pairs burn off as it falls.

Everything here runs during **elaboration**, so a widget costs its solver run every time the file
is opened. `fireAt` takes an explicit seed and performs exactly one anneal, which is what keeps
`Queens.Gallery` cheap; `fire` restarts until a run settles, which is friendlier interactively
and much slower in a file full of widgets.
-/

namespace QUBO
namespace Queens

open Lean ProofWidgets

/-- One decoded board as the renderer's frame encoding: `'.'` where the decoder found no queen,
otherwise the column index in base 36. -/
def frameOf (I : Instance) (x : Array Bool) : String :=
  let q := I.decode x
  colouringFrame ((Array.range I.size).map fun i =>
    let c := q.getD i I.size
    if c < I.size then some c else none)

/-- One group per board row: its `N` cell variables, exactly one of which should be set.

This is what `SearchConfig.oneHotInit` needs. Seeding one queen per row starts every model on the
feasible manifold of the `N` row constraints, leaving the dynamics to work on the columns, the
diagonals and the givens — the queens analogue of Sudoku's `openCellGroups`. -/
def cellGroups (I : Instance) : Array (Array Nat) :=
  (Array.range I.size).map fun i => (Array.range I.size).map fun j => I.cellVar i j

/-- A caption fragment describing the instance. -/
private def titleOf (I : Instance) : String :=
  s!"{I.size}×{I.size} board, {I.ngivens} given, {I.nvars} variables, {I.nrows} rows"

/-- Run the collaborative search and package it for the player. -/
def props (I : Instance) (seed : Nat := 1) (cfg : SearchConfig := {}) : PlayerProps :=
  let cfg := { cfg with captureBoards := true, oneHotInit := true, groups := cellGroups I }
  let r := search (problem I) Model.bmm cfg (Rng.seed seed.toUInt64)
  let frames := r.boards.map (frameOf I)
  let ok := I.isQueens (I.decode r.best)
  { title := titleOf I
    kind := "board"
    frames := if frames.isEmpty then #[frameOf I r.best] else frames
    phase := frames.map fun _ => 1
    pen := r.boardsE
    outer := (Array.range frames.size).map (fun k : Nat => (k : Int))
    solved := ok
    note :=
      if ok then
        s!"p(x̂) = 0 after {r.outer} outer iterations, and the decoded board was checked to be " ++
        s!"a completion — `decode_isQueens` says the check cannot fail."
      else
        s!"no zero found in {r.outer} outer iterations; best p(x̂) = {r.penaltyDoubled}. " ++
        s!"For a blocked placement that is the expected outcome, not a bug: " ++
        s!"`exists_zero_iff_queens` makes the negative answer mean something."
    nverts := I.size
    edges := I.givens
    ncolours := I.size }

/-- The collaborative-search player for one board. -/
def animate (I : Instance) (seed : Nat := 1) : Html := player (props I seed)

/-- For a **blocked** placement: a deliberately small budget.

There is no zero to find, so the search runs to its termination criterion whatever the budget —
at the default `N = 40`, `M = 50` that is by far the most expensive thing in a demo file. The
point being made is only that it stops without a zero, which a small population shows just as
well, and `blocked4_no_queens` / `blocked6_no_queens` are what make the negative answer a fact
about boards rather than a failure of the solver. -/
def refute (I : Instance) : Html :=
  player (props I 1 { N := 10, M := 8, maxOuter := 25 })

/-! ## Watching the machine fire, sweep by sweep

`props` above shows the *swarm*. `fireProps` shows the *network*: one annealed run of eq. (6),
one frame per synchronous sweep, temperature falling geometrically. -/

/-- One annealed BMm run, keeping every sweep rather than only the endpoint.

Drives `QUBO.bmmStep` directly. Deliberately not a variant of `bmmRun`: capture in the hot loop
would slow every search in the library for the sake of a demo. -/
def anneal (P : Problem) (steps : Nat) (T0 eta : Float) (g0 : Rng) (x0 : Array Bool) :
    Array (Array Bool) := Id.run do
  let mut u : Array Int := Array.replicate P.nvars 0
  let mut x := x0
  let mut g := g0
  -- `T0` is the *effective* temperature, matching `ModelConfig.tabulate`'s convention.
  -- `bmmStep` divides the accumulated net input by the temperature it is handed, and
  -- `Problem.netVec` returns twice the local field (`theta` is stored doubled), so the value
  -- passed down must be `2·T` for `exp(2·field / 2T) = exp(field / T)` to hold. Without this the
  -- schedule reported in the caption would be twice as cold as the one advertised, and this
  -- animation would not be comparable with the swarm columns of `Queens.Bench`.
  let mut T := 2.0 * T0
  let mut out : Array (Array Bool) := #[x0]
  for _ in [0:steps] do
    let (u', x', g') := bmmStep P T g u x
    u := u'; x := x'; g := g'
    T := T * eta
    out := out.push x
  return out

/-- A one-queen-per-row random start, so the first frame is a full (usually attacking) placement
rather than an empty board. -/
def randomStart (I : Instance) (g0 : Rng) : Array Bool × Rng := Id.run do
  let mut bs : Array Bool := Array.replicate (problem I).nvars false
  let mut g := g0
  for i in [0:I.size] do
    let (k, g') := g.nextBelow I.size
    g := g'
    bs := bs.set! (I.cellVar i k) true
  return (bs, g)

/-- Props for the sweep-by-sweep view.

A single annealed run settles on a completion only sometimes; that is not a defect of the demo,
it is the reason Li & Wang's method is *collaborative* — one Boltzmann machine is a weak solver
and the swarm of eq. (7) is what makes it reliable. So this tries seeds `seed, seed+1, …` and
animates the first that settles, reporting in the caption which seed that was. Pass `tries := 1`
(as `fireAt` does) to see exactly one run and keep a file of widgets cheap.

Queens is markedly harder for a single machine than graph colouring is, and harder than an earlier
version of this docstring claimed. Measured over **seeds `0…39`** at the *default* schedule below
(400 sweeps, `T = 3·0.99ᵗ`): `9/60` seeds settle on an empty `5 × 5`, and **none at all** on
`small6` or on `completion8` in `[0,60)`. Slowing to 2000 sweeps at `T = 2·0.998ᵗ` — what `fireAt`
uses — gives `7/40`, `1/40`, `1/40` respectively, and still `0` on the empty `8 × 8` under either.
The swarm of eq. (7) solves that same `8 × 8` in three outer iterations. That contrast is the demo's
real content, so a failing run is reported in the caption rather than hidden.

**Two provenance warnings.** First, figures recorded before the `2·T₀` correction in `anneal` (see
its docstring) were taken at *half* the advertised temperature and are not comparable with these; a
colder anneal freezes into a solution more readily, which is why the old numbers looked better.
Second, `QUBO.Queens.Bench` measures from base seed `20260806` over 20 seeds and is the
authoritative source: `0/20` from `N = 6` upward and on every completion instance. Cite the bench,
not this docstring, in anything that reports a rate. -/
def fireProps (I : Instance) (seed : Nat := 1) (steps : Nat := 400)
    (T0 : Float := 3.0) (eta : Float := 0.99) (tries : Nat := 40) : PlayerProps :=
  let P := problem I
  let attempt (s : Nat) : Array (Array Bool) :=
    let (x0, g) := randomStart I (Rng.seed s.toUInt64)
    anneal P steps T0 eta g x0
  let pick : Nat × Array (Array Bool) := Id.run do
    let mut chosen := (seed, attempt seed)
    for k in [0:tries] do
      let s := seed + k
      let xs := attempt s
      if I.isQueens (I.decode xs.back!) then
        chosen := (s, xs)
        break
    return chosen
  let (usedSeed, xs) := pick
  let frames := xs.map (frameOf I)
  let pens := xs.map P.penaltyDoubled
  let ok := I.isQueens (I.decode xs.back!)
  { title := titleOf I ++ s!" — BMm, {steps} sweeps"
    kind := "board"
    frames := frames
    phase := frames.map fun _ => 1
    pen := pens
    outer := (Array.range frames.size).map (fun k : Nat => (k : Int))
    solved := ok
    note :=
      s!"One annealed run of eq. (6), seed {usedSeed} of {tries} tried: T = {T0}·{eta}^t, " ++
      s!"every neuron resampled from the logistic of its accumulated field each sweep. " ++
      s!"Final p(x̂) = {pens.back!}" ++
      (if ok then ", a completion. Press play: attacking pairs burn off as T falls."
       else s!" — no seed settled. A single machine is a weak solver; the swarm view runs eq. (7).")
    nverts := I.size
    edges := I.givens
    ncolours := I.size }

/-- The sweep-by-sweep player, searching for a seed that settles. -/
def fire (I : Instance) (seed : Nat := 1) : Html := player (fireProps I seed)

/-- The sweep-by-sweep player on **one** given seed, no restart search. Where a settling seed is
already known, pin it with this and the cost is a single anneal.

**The schedule here is deliberately much slower than `fireProps`'s default** — 2000 sweeps at
`T = 2·0.998ᵗ` rather than 400 at `3·0.99ᵗ`. At the faster schedule *no* seed in `[0,60)` settles on
`small6` or on `completion8`; at this one, seeds `11` and `5` respectively do. One anneal costs about
a second, which is the price of the widget showing a completion rather than a stall.

Do not read the pinned seeds as typical. Over 40 seeds this schedule settles `7/40` on an empty
`5 × 5`, `1/40` on `small6` and `1/40` on `completion8` — the pinned seeds are the lucky ones, chosen
so the animation ends on a solved board. The honest summary of a single machine's ability is the
`s/20` anneal column of `QUBO.Queens.Bench`, not this. -/
def fireAt (I : Instance) (seed : Nat) : Html :=
  player (fireProps I seed 2000 2.0 0.998 1)

end Queens
end QUBO
