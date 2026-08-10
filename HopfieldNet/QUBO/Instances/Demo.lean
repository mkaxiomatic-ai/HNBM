/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.QUBO.Instances.Colouring
import HopfieldNet.QUBO.Instances.ExactCover
import HopfieldNet.QUBO.Instances.EdgeColouring
import HopfieldNet.QUBO.Search
import HopfieldNet.QUBO.Widget

/-!
# Watching a graph colour itself

`#colour` runs the collaborative neurodynamic search on a graph-colouring QUBO and animates the
incumbent in the infoview, one frame per outer iteration.

```lean
import HopfieldNet.QUBO.Instances.Demo

#colour triangle       -- K₃ with 3 colours: feasible
#colour petersen       -- the Petersen graph with 3 colours
#colour k4             -- K₄ with 3 colours: infeasible, watch it fail to settle

#cover ex1             -- exact cover, drawn as its incidence matrix
#cover pentomino       -- a small tiling instance
#cover ex2             -- infeasible: no subfamily covers `{0,1,2}` exactly once

#edgecolour k3         -- edge colouring, shown on the line graph
#edgecolour path4      -- a path needs only two edge colours
```

Nothing about this is Sudoku. The search (`QUBO.search`), the dynamics of eqs (3) and (6), and
the player are all shared with `HopfieldNet.CNS`; only the `Incidence` differs. That is the
point of the split — a second problem costs an encoding and a decoder, not a second solver.

The frames are computed during elaboration and shipped as props; nothing streams. Keep the
graphs small while editing.
-/

namespace QUBO
namespace Colouring

open Lean ProofWidgets

/-! ## Some graphs to look at -/

/-- The Petersen graph: 3-chromatic, and the standard small counterexample to a lot of
plausible-sounding conjectures. -/
def petersen : Instance where
  nverts := 10
  ncolours := 3
  edges :=
    -- outer 5-cycle, spokes, inner pentagram
    #[(0,1),(1,2),(2,3),(3,4),(4,0),
      (0,5),(1,6),(2,7),(3,8),(4,9),
      (5,7),(7,9),(9,6),(6,8),(8,5)]

/-- A 5-cycle with 3 colours: feasible, but not with 2. -/
def c5 : Instance := ⟨5, 3, #[(0,1),(1,2),(2,3),(3,4),(4,0)]⟩

/-- A 5-cycle with 2 colours: infeasible, an odd cycle. -/
def c5two : Instance := ⟨5, 2, #[(0,1),(1,2),(2,3),(3,4),(4,0)]⟩

/-! ## From a run to frames -/

/-- One vertex colouring as the renderer's frame encoding: `'.'` where the decoder found no
colour, otherwise the colour index in base 36. -/
def frameOf (I : Instance) (x : Array Bool) : String :=
  let col := I.decode x
  colouringFrame ((Array.range I.nverts).map fun v =>
    let c := col.getD v I.ncolours
    if c < I.ncolours then some c else none)

/-- One group per vertex: its `ncolours` colour variables, exactly one of which should be set.
This is what `SearchConfig.oneHotInit` needs, and the colouring analogue of Sudoku's
`openCellGroups`. -/
def cellGroups (I : Instance) : Array (Array Nat) :=
  (Array.range I.nverts).map fun v => (Array.range I.ncolours).map fun i => I.colVar v i

/-- Run the search and package it for the player. -/
def props (I : Instance) (seed : Nat := 1) (cfg : SearchConfig := {}) : PlayerProps :=
  let cfg := { cfg with captureBoards := true, oneHotInit := true, groups := cellGroups I }
  let r := search (problem I) Model.bmm cfg (Rng.seed seed.toUInt64)
  let frames := r.boards.map (frameOf I)
  let ok := I.isColouring (I.decode r.best)
  { title := s!"{I.nverts} vertices, {I.nedges} edges, {I.ncolours} colours"
    kind := "graph"
    frames := if frames.isEmpty then #[frameOf I r.best] else frames
    phase := frames.map fun _ => 1
    pen := r.boardsE
    outer := (Array.range frames.size).map (fun k : Nat => (k : Int))
    solved := ok
    note :=
      if ok then
        s!"p(x̂) = 0 after {r.outer} outer iterations, and the decoded colouring was checked " ++
        s!"proper — `decode_isColouring` says the check cannot fail."
      else
        s!"no zero found in {r.outer} outer iterations; best p(x̂) = {r.penaltyDoubled}. " ++
        s!"For an infeasible instance that is the expected outcome, not a bug."
    nverts := I.nverts
    edges := I.edges
    ncolours := I.ncolours }

/-- The player for one graph, as an infoview `Html`. -/
def animate (I : Instance) (seed : Nat := 1) : Html := player (props I seed)

/-! ## Watching the machine fire, sweep by sweep

`props` above shows the *swarm*: one frame per outer iteration of `QUBO.search`. On an easy graph
the search finds a zero in one or two outer iterations, so there is nothing to watch.

`fireProps` shows the *network* instead: one annealed run of the Boltzmann machine of eq. (6),
one frame per synchronous sweep, temperature falling geometrically. Every neuron is resampled from
the logistic of its accumulated field each sweep, so early frames flicker and late ones settle —
which is the thing worth seeing, and what the swarm view hides. -/

/-- One annealed BMm run, keeping every sweep rather than only the endpoint.

Drives `QUBO.bmmStep` directly. Deliberately *not* a variant of `bmmRun`: capture in the hot loop
would slow every search in the library for the sake of a demo. -/
def anneal (P : Problem) (steps : Nat) (T0 eta : Float) (g0 : Rng) (x0 : Array Bool) :
    Array (Array Bool) := Id.run do
  let mut u : Array Int := Array.replicate P.nvars 0
  let mut x := x0
  let mut g := g0
  let mut T := T0
  let mut out : Array (Array Bool) := #[x0]
  for _ in [0:steps] do
    let (u', x', g') := bmmStep P T g u x
    u := u'; x := x'; g := g'
    T := T * eta
    out := out.push x
  return out

/-- A one-hot random start: exactly one colour per vertex, so the first frame is a (usually
improper) total colouring rather than a blank board. -/
def randomStart (I : Instance) (g0 : Rng) : Array Bool × Rng := Id.run do
  let mut bs : Array Bool := Array.replicate (problem I).nvars false
  let mut g := g0
  for v in [0:I.nverts] do
    let (k, g') := g.nextBelow I.ncolours
    g := g'
    bs := bs.set! (I.colVar v k) true
  return (bs, g)

/-- Props for the sweep-by-sweep view.

A single annealed run of eq. (6) settles on a proper colouring only sometimes — measured over
eight seeds: 4/8 on `triangle`, 3/8 on `c5`, 1/8 on `petersen`. That is not a defect of the
demo, it is the reason Li & Wang's method is *collaborative*: one Boltzmann machine is a weak
solver, and the swarm of eq. (7) is what makes it reliable. `#colour` shows the swarm.

So that the animation shows a run that finishes, this tries seeds `seed, seed+1, …` and animates
the first that settles, reporting in the caption which seed that was and how many were tried.
The failing runs are not hidden — `#fire` with an explicit `tries := 1` shows exactly one.

One measurement worth keeping, because it is the argument for the swarm in miniature: on `wheel6`
and `crown4` a single anneal needs about forty restarts to hit a proper colouring, and making the
schedule *longer* instead does not help at all — 250 or 400 sweeps at slower cooling still stall
at `p(x̂) = 2`, while 40 restarts of the 120-sweep schedule succeed. The failure is not
impatience, it is that each run has a roughly fixed success probability; restarts beat patience,
which is exactly why eq. (7) runs a population rather than one long chain. -/
def fireProps (I : Instance) (seed : Nat := 1) (steps : Nat := 120)
    (T0 : Float := 2.0) (eta : Float := 0.97) (tries : Nat := 40) : PlayerProps :=
  let P := problem I
  let attempt (s : Nat) : Array (Array Bool) :=
    let (x0, g) := randomStart I (Rng.seed s.toUInt64)
    anneal P steps T0 eta g x0
  let pick : Nat × Array (Array Bool) := Id.run do
    let mut chosen := (seed, attempt seed)
    for k in [0:tries] do
      let s := seed + k
      let xs := attempt s
      if I.isColouring (I.decode xs.back!) then
        chosen := (s, xs)
        break
    return chosen
  let (usedSeed, xs) := pick
  let frames := xs.map (frameOf I)
  let pens := xs.map P.penaltyDoubled
  let ok := I.isColouring (I.decode xs.back!)
  { title := s!"{I.nverts} vertices, {I.nedges} edges, {I.ncolours} colours — BMm, {steps} sweeps"
    kind := "graph"
    frames := frames
    phase := frames.map fun _ => 1
    pen := pens
    outer := (Array.range frames.size).map (fun k : Nat => (k : Int))
    solved := ok
    note :=
      s!"One annealed run of eq. (6), seed {usedSeed} of {tries} tried: T = {T0}·{eta}^t, every " ++
      s!"neuron resampled from the logistic of its accumulated field each sweep. Final p(x̂) = " ++
      s!"{pens.back!}" ++
      (if ok then ", a proper colouring. Press play: early sweeps flicker, late ones settle."
       else s!" — no seed settled. A single machine is a weak solver; `#colour` runs the swarm.")
    nverts := I.nverts
    edges := I.edges
    ncolours := I.ncolours }

/-- The sweep-by-sweep player. -/
def fire (I : Instance) (seed : Nat := 1) : Html := player (fireProps I seed)

end Colouring
end QUBO

/-! ## The `#colour` command

`#html` attaches its widget to its own syntax node, and a node produced by macro expansion is
synthetic — the infoview then has no source position to hang the panel on and silently renders
nothing. Marking the expansion canonical is what makes a macro over `#html` display at all;
the same dance as `CNS`'s `#animate`. -/

private def Lean.SourceInfo.mkCanonical' : SourceInfo → SourceInfo
  | .synthetic s e _ => .synthetic s e true
  | si => si

private def Lean.Syntax.mkInfoCanonical' : Syntax → Syntax
  | .missing => .missing
  | .node i k a => .node i.mkCanonical' k a
  | .atom i v => .atom i.mkCanonical' v
  | .ident i r v p => .ident i.mkCanonical' r v p

private def Lean.TSyntax.mkInfoCanonical' : TSyntax k → TSyntax k :=
  (.mk ·.raw.mkInfoCanonical')

/-- `#colour triangle` — run the full search and watch the incumbent, one frame per outer
iteration. -/
macro "#colour " g:term : command =>
  Lean.TSyntax.mkInfoCanonical' <$> `(#html QUBO.Colouring.animate $g)

/-- `#fire petersen` — watch the Boltzmann machine anneal, one frame per sweep. This is the one
to press play on. -/
macro "#fire " g:term : command =>
  Lean.TSyntax.mkInfoCanonical' <$> `(#html QUBO.Colouring.fire $g)

/-! ## Exact cover

Drawn as the incidence matrix — one row per ground-set element, one column per subset, a mark
where the element lies in the subset. The margin gives each row's coverage: `1` satisfied, `0`
uncovered, `2+` over-covered. That number *is* the residual `ρ_r − b̂_r` the objective squares,
so the picture is of the constraint rather than of a paraphrase of it.

The displayed matrix is the instance's own `m × k` incidence, not the QUBO's `2m` rows —
`ExactCover.qubo` duplicates every row so that column degrees are even, which is an artefact of
the encoding and not something worth drawing. (Since `QUBO.Problem.theta` is stored doubled that
duplication is no longer necessary; removing it is a separate change.)
-/

namespace QUBO
namespace ExactCover

open Lean ProofWidgets

/-- Knuth's small example: cover `{0,…,5}` with the rows of the standard 6×7 matrix. -/
def knuth : Instance := ⟨6, #[#[0, 3], #[0, 2, 5], #[1, 4], #[2, 5], #[1, 3, 4], #[1]]⟩

/-- Tile a 2×3 board with dominoes: six cells, the seven placements. Two exact covers. -/
def pentomino : Instance :=
  ⟨6, #[#[0, 1], #[1, 2], #[3, 4], #[4, 5], #[0, 3], #[1, 4], #[2, 5]]⟩

/-- The `(row, column)` pairs of the displayed incidence matrix. -/
def matCells (I : Instance) : Array (Nat × Nat) :=
  (Array.range I.numSets).flatMap fun i => (I.setOf i).map fun a => (a, i)

/-- Run the search and package it for the player. -/
def props (I : Instance) (seed : Nat := 1) (cfg : SearchConfig := {}) : PlayerProps :=
  let cfg := { cfg with captureBoards := true }
  let r := search (qubo I) Model.bmm cfg (Rng.seed seed.toUInt64)
  let frames := r.boards.map (selectionFrame I.numSets)
  let ok := coversExactly I (decode I r.best)
  { title := s!"{I.groundSize} elements, {I.numSets} subsets"
    kind := "matrix"
    frames := if frames.isEmpty then #[selectionFrame I.numSets r.best] else frames
    phase := frames.map fun _ => 1
    pen := r.boardsE
    outer := (Array.range frames.size).map (fun k : Nat => (k : Int))
    solved := ok
    note :=
      if ok then
        s!"p(x̂) = 0 after {r.outer} outer iterations; the selection {decode I r.best} was " ++
        s!"checked to cover every element exactly once — `decode_coversExactly` says the " ++
        s!"check cannot fail."
      else
        s!"no zero found in {r.outer} outer iterations; best p(x̂) = {r.penaltyDoubled}. " ++
        s!"For an instance with no exact cover that is the expected outcome."
    mrows := I.groundSize
    mcols := I.numSets
    cells := matCells I }

/-- The player for one instance, as an infoview `Html`. -/
def animate (I : Instance) (seed : Nat := 1) : Html := player (props I seed)

end ExactCover
end QUBO

/-- `#cover ex1` — run the neurodynamics on an exact-cover QUBO and watch the matrix. -/
macro "#cover " i:term : command =>
  Lean.TSyntax.mkInfoCanonical' <$> `(#html QUBO.ExactCover.animate $i)

/-! ## Edge colouring

Shown on the **line graph**: one drawn vertex per edge of `G`, adjacent when the edges share an
endpoint. That is not a compromise, it is the reduction — a proper edge colouring of `G` *is* a
proper vertex colouring of `L(G)`, definitionally, by `EdgeColouring.isColouring_lineGraph`. So
the existing graph renderer shows it with nothing added.
-/

namespace QUBO
namespace EdgeColouring

open Lean ProofWidgets

/-- Run the search on the line graph and package it for the player. -/
def props (I : Problem') (seed : Nat := 1) : PlayerProps :=
  let L := I.lineGraph
  let p := Colouring.props L seed
  { p with
    title := s!"edge colouring: {I.nverts} vertices, {I.nedges} edges, {I.ncolours} colours (drawn as L(G))"
    note := p.note ++
      " Vertices of the picture are edges of G; adjacency is sharing an endpoint." }

/-- The player for one edge-colouring instance. -/
def animate (I : Problem') (seed : Nat := 1) : Html := player (props I seed)

end EdgeColouring
end QUBO

/-- `#edgecolour k3` — edge-colour a graph, shown on its line graph. -/
macro "#edgecolour " g:term : command =>
  Lean.TSyntax.mkInfoCanonical' <$> `(#html QUBO.EdgeColouring.animate $g)
