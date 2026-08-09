/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.QUBO.Problem
import ProofWidgets.Component.HtmlDisplay

/-!
# Watching a QUBO solve, in the infoview

One player, several renderers. A run is shipped to the infoview as a list of *frames*, each a
short string, together with the incumbent objective at each frame; the `kind` field picks how a
frame is drawn:

* `"sudoku"` — an 81-character board, `'.'` for an empty cell (`CNS.Grid.toString`);
* `"graph"`  — one character per vertex, `'.'` for uncoloured and otherwise a colour index in
  base 36, drawn on a circular layout with monochromatic edges highlighted.

Frames are computed during elaboration and shipped as props; nothing streams. That is
deliberate — the search has already finished by the time anything renders — but it does mean a
large instance costs elaboration time, so prefer small ones while editing.

`CNS.Widget` predates this and carries its own copy for Sudoku; new instances should use this
one.
-/

namespace QUBO

open Lean ProofWidgets

/-- Props of `quboPlayer.js`.

The graph fields are ignored unless `kind = "graph"`. Keeping one prop structure rather than a
sum type keeps the `ToJson` derivation and the JS entry point trivial; the cost is a few unused
fields per run, which is nothing next to the frames themselves. -/
structure PlayerProps where
  /-- Heading, e.g. `petersen · 3 colours`. -/
  title : String
  /-- Which renderer to use: `"sudoku"` or `"graph"`. -/
  kind : String := "sudoku"
  /-- One frame per step, in the encoding `kind` implies. -/
  frames : Array String
  /-- For Sudoku, the original givens, set in bold ink. Empty for other kinds. -/
  givens : String := ""
  /-- `0` if frame `i` belongs to a propagation phase, `1` if to the neurodynamic search. -/
  phase : Array Nat
  /-- `‖Âx̂ − b̂‖²` of the incumbent, or `-1` where it is undefined. -/
  pen : Array Int
  /-- Outer-iteration index of a search frame, `-1` otherwise. -/
  outer : Array Int
  /-- Whether the final frame was *checked* to be a solution — not merely whether `p(x)` hit `0`. -/
  solved : Bool
  /-- Footnote under the picture. -/
  note : String := ""
  /-- `kind = "graph"`: number of vertices. -/
  nverts : Nat := 0
  /-- `kind = "graph"`: the edge list. -/
  edges : Array (Nat × Nat) := #[]
  /-- `kind = "graph"`: size of the palette. -/
  ncolours : Nat := 0
  deriving ToJson, FromJson, Inhabited

@[widget_module]
def QuboPlayer : Component PlayerProps where
  javascript := include_str "quboPlayer.js"

/-- Render a run. -/
def player (p : PlayerProps) : Html := Html.ofComponent QuboPlayer p #[]

/-- A colour index as the single character the graph renderer expects: base 36, `'.'` for
"no colour yet". -/
def colourChar : Option Nat → Char
  | none   => '.'
  | some k =>
    if k < 10 then Char.ofNat ('0'.toNat + k)
    else if k < 36 then Char.ofNat ('a'.toNat + (k - 10))
    else '?'

/-- A vertex colouring as one frame string. -/
def colouringFrame (cols : Array (Option Nat)) : String :=
  String.mk (cols.toList.map colourChar)

end QUBO
