/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.QUBO.Instances.Colouring
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

/-- `#colour triangle` — run the neurodynamics on a graph-colouring QUBO and watch it. -/
macro "#colour " g:term : command =>
  Lean.TSyntax.mkInfoCanonical' <$> `(#html QUBO.Colouring.animate $g)
