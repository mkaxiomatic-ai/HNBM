/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.CNS.Search
import HopfieldNet.CNS.Instances
import ProofWidgets.Component.HtmlDisplay

/-!
# Watching the solver run, in the infoview

`#animate "Sabuncu4"` elaborates to a player showing the whole pipeline as one timeline:
Algorithm 1's deductions frame by frame, then Algorithm 2's incumbent at each outer iteration.

```lean
import HopfieldNet.CNS.Widget

#animate "Sabuncu1"      -- 41 frames, Algorithm 1 only: Table I gives 0 variables remaining
#animate "Sabuncu4"      -- 24 reduction frames, then 14 search frames
#animate "Sabuncu9" 3    -- from search seed 3
```

The frames are computed during elaboration — `reduceFrames` for the first segment and
`SearchConfig.captureBoards` for the second — and shipped to the infoview as props. Nothing
streams: the search has already finished by the time anything renders. That is deliberate.
A `#animate` on a 209-variable instance can take a minute of elaboration, so prefer the
smaller ones while editing.

This module is the only part of `CNS` that depends on ProofWidgets, and nothing in the
execution path imports it.
-/

open Lean ProofWidgets
open scoped ProofWidgets.Jsx

namespace CNS

open QUBO
open QUBO.Problem

/-- Props of `sudokuPlayer.js`. Boards travel as 81-character strings, `'.'` for an empty
cell, which is exactly `Grid.toString`. -/
structure PlayerProps where
  /-- Heading, e.g. `Sabuncu4 · 24 givens`. -/
  title : String
  /-- One 81-character board per frame. -/
  frames : Array String
  /-- The original givens, so the player can set them in bold ink. -/
  givens : String
  /-- `0` if frame `i` belongs to Algorithm 1, `1` if to Algorithm 2. -/
  phase : Array Nat
  /-- `‖Âx̂ − b̂‖²` of the incumbent, or `-1` on a reduction frame where it is undefined. -/
  pen : Array Int
  /-- Outer-iteration index of a search frame, `-1` on a reduction frame. -/
  outer : Array Int
  /-- Whether the last frame was checked to be a valid completion of the givens. -/
  solved : Bool
  /-- Footnote under the board. -/
  note : String
  deriving ToJson, FromJson, Inhabited

@[widget_module]
def SudokuPlayer : Component PlayerProps where
  javascript := include_str "sudokuPlayer.js"

/-- Build the props for one instance: reduce, then search from `seed` if anything is left.

The final frame is checked with `isSolution && extends'` exactly as `lake exe cns complete`
does, and `solved` records that check — not merely whether `p(x)` reached `0`. -/
def playerProps (nm : String) (seed : Nat := 1) (cfg : SearchConfig := {}) : PlayerProps :=
  match Instances.find? nm with
  | none => { title := s!"no instance named '{nm}'", frames := #[], givens := "",
              phase := #[], pen := #[], outer := #[], solved := false, note := "" }
  | some e =>
  match Grid.ofString e.givens with
  | none => { title := s!"{nm}: unparseable givens", frames := #[], givens := "",
              phase := #[], pen := #[], outer := #[], solved := false, note := "" }
  | some g =>
    let redFrames := reduceFrames g
    let redBoards := redFrames.map Grid.toString
    let R := reduce g
    if R.remaining == 0 then
      { title := s!"{nm} · {g.numGivens} givens"
        frames := redBoards
        givens := e.givens
        phase := redBoards.map (fun _ => 0)
        pen := redBoards.map (fun _ => (-1 : Int))
        outer := redBoards.map (fun _ => (-1 : Int))
        solved := R.grid.isSolution && g.extends' R.grid
        note := s!"Algorithm 1 alone closes this instance in {R.rounds} deductions; \
                  Table I records 0 variables remaining, so Algorithm 2 never runs." }
    else
      let P := Problem.ofGrid g
      let r := search P Model.bmm { cfg with captureBoards := true } (Rng.seed (UInt64.ofNat seed))
      let searchBoards := r.boards.map (fun x => (P.toGrid x).toString)
      let final := P.toGrid r.best
      { title := s!"{nm} · {g.numGivens} givens"
        frames := redBoards ++ searchBoards
        givens := e.givens
        phase := redBoards.map (fun _ => 0) ++ searchBoards.map (fun _ => 1)
        pen := redBoards.map (fun _ => (-1 : Int)) ++ r.boardsE
        outer := redBoards.map (fun _ => (-1 : Int))
                   ++ (Array.range r.boards.size).map Int.ofNat
        solved := r.solved && final.isSolution && g.extends' final
        note := s!"Algorithm 1 fixes {numVars - P.nvars} of {numVars} variables in \
                  {R.rounds} deductions, leaving {P.nvars} (Table I: {e.table1}). \
                  Algorithm 2 then ran {r.outer} outer iterations from seed {seed}." }

/-- The player for one instance, as an infoview `Html`. -/
def animate (nm : String) (seed : Nat := 1) : Html :=
  Html.ofComponent SudokuPlayer (playerProps nm seed) #[]

end CNS

/-! ## The `#animate` command

`#html` attaches its widget to its own syntax node, and a node produced by macro expansion is
synthetic — `savePanelWidgetInfo` then has no source position to hang the panel on and the
infoview silently renders nothing. Marking the expansion canonical is what makes a macro over
`#html` display at all. See `ProofWidgets.Demos.Macro`, where these two helpers come from; they
are not exported by the library. -/

private def Lean.SourceInfo.mkCanonical : SourceInfo → SourceInfo
  | .synthetic s e _ => .synthetic s e true
  | si => si

private def Lean.Syntax.mkInfoCanonical : Syntax → Syntax
  | .missing => .missing
  | .node i k a => .node i.mkCanonical k a
  | .atom i v => .atom i.mkCanonical v
  | .ident i r v p => .ident i.mkCanonical r v p

private def Lean.TSyntax.mkInfoCanonical : TSyntax k → TSyntax k :=
  (.mk ·.raw.mkInfoCanonical)

/-- `#animate "Sabuncu4"` — run the pipeline and show it in the infoview. -/
macro "#animate " nm:str : command =>
  Lean.TSyntax.mkInfoCanonical <$> `(#html CNS.animate $nm)

/-- `#animate "Sabuncu4" 7` — as above, from a given search seed. -/
macro "#animate " nm:str ppSpace seed:num : command =>
  Lean.TSyntax.mkInfoCanonical <$> `(#html CNS.animate $nm $seed)
