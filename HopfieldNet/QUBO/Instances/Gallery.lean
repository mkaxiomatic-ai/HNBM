/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.QUBO.Instances.Demo

/-!
# Gallery: watch a Hopfield/Boltzmann machine colour a graph

Open this file in an editor with the Lean infoview. Put the cursor on any `#fire` or `#colour`
line and a player appears; press **▶** to watch.

Two views of the same solver:

* **`#fire g`** — one annealed run of the Boltzmann machine of eq. (6), **one frame per sweep**.
  This is the one to press play on. Every neuron is resampled from the logistic of its
  accumulated field each sweep, with the temperature falling geometrically, so the early frames
  flicker and the late ones settle. Monochromatic edges are drawn thick and red, so you watch
  conflicts burn off.
* **`#colour g`** — the full collaborative search of eq. (7), **one frame per outer iteration**.
  Reliable but coarse: on an easy graph it finds a zero in one or two iterations, so there is
  little to see. Use it to check *whether* a graph is colourable at a given palette; use `#fire`
  to see the machine work.

A caveat stated plainly, because the demo would otherwise be misleading: a *single* annealed run
settles on a proper colouring only sometimes — 4 times in 8 seeds on `triangle`, 3 in 8 on `c5`,
1 in 8 on `petersen`. That is exactly why Li & Wang's method is collaborative. `#fire` therefore
tries up to twelve seeds and animates the first that settles, saying in the caption which seed it
used. To see an honest single run, pass `tries := 1`.

## Making your own

An instance is `⟨nverts, ncolours, edges⟩` with vertices numbered `0 … nverts-1`:

```lean
def mine : Instance := ⟨5, 3, #[(0,1),(1,2),(2,3),(3,4),(4,0)]⟩
#fire mine
```

The palette is an *input*: set `ncolours := 3` to ask "is this 3-colourable?". If the search
reports no zero, that is meaningful — `exists_zero_iff_colourable'` proves the objective has a
zero exactly when a proper colouring exists.

The run happens during **elaboration**, so a large graph will make the editor wait. Everything in
this file is instant except `myc3`, which is deliberately at the end.
-/

namespace QUBO
namespace Colouring
namespace Gallery

/-! ## Small and instant -/

/-- A triangle needs three colours. The smallest thing that is not trivially colourable. -/
def k3 : Instance := ⟨3, 3, #[(0,1),(1,2),(0,2)]⟩

/-- A square needs only two, and the two-colouring is forced up to swapping. -/
def c4 : Instance := ⟨4, 2, #[(0,1),(1,2),(2,3),(3,0)]⟩

/-- An odd cycle needs three. Watch the conflict chase itself around the ring before settling. -/
def c7 : Instance := ⟨7, 3, #[(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,0)]⟩

/-- A 6-wheel: a hub adjacent to everything, so the hub takes its own colour and the rim
alternates. `χ = 3`, but `Δ+1 = 7` — greedy's bound is badly loose here. -/
def wheel6 : Instance :=
  ⟨7, 3, #[(0,1),(1,2),(2,3),(3,4),(4,5),(5,0),(6,0),(6,1),(6,2),(6,3),(6,4),(6,5)]⟩

/-! ## The interesting ones -/

/-- The Petersen graph. `χ = 3`, `Δ+1 = 4`, and no short cycles — the classic small graph on
which easy heuristics look better than they are. -/
def petersen : Instance :=
  ⟨10, 3, #[(0,1),(1,2),(2,3),(3,4),(4,0),
            (0,5),(1,6),(2,7),(3,8),(4,9),
            (5,7),(7,9),(9,6),(6,8),(8,5)]⟩

/-- The **crown graph** on 8 vertices: `K₄,₄` minus a perfect matching, with the two sides
interleaved. Bipartite, so `χ = 2` — but in this vertex order first-fit greedy is dragged to
four colours. The certified separation is `Baseline.dsatur_lt_greedy_gCrown4`. -/
def crown4 : Instance :=
  ⟨8, 2, #[(0,3),(0,5),(0,7),(2,1),(2,5),(2,7),(4,1),(4,3),(4,7),(6,1),(6,3),(6,5)]⟩

/-- The **Grötzsch graph**: 11 vertices, triangle-free, and yet `χ = 4`. The standard witness
that triangle-freeness does not bound the chromatic number, and the most interesting graph that
fits comfortably in this demo. Its χ was verified independently, not cited. -/
def grotzsch : Instance :=
  ⟨11, 4, #[(0,1),(1,2),(2,3),(3,4),(4,0),
            (5,1),(5,4),(6,2),(6,0),(7,3),(7,1),(8,4),(8,2),(9,0),(9,3),
            (10,5),(10,6),(10,7),(10,8),(10,9)]⟩

/-! ## Infeasible, on purpose

These have no colouring at the palette given, and the search correctly fails to find a zero. That
the failure *means* something is the content of `exists_zero_iff_colourable'`: no zero exists iff
no proper colouring does. -/

/-- A triangle with two colours. Impossible — `triangle_not_two_colourable` is a theorem. -/
def k3two : Instance := ⟨3, 2, #[(0,1),(1,2),(0,2)]⟩

/-- `K₄` with three colours. Impossible — `k4_not_three_colourable` is a theorem. -/
def k4three : Instance := ⟨4, 3, #[(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]⟩

/-- An odd cycle with two colours. Impossible: odd cycles are not bipartite. -/
def c7two : Instance := ⟨7, 2, #[(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,0)]⟩

/-! ## Edge colouring

A proper edge colouring of `G` is a proper vertex colouring of its line graph, so `#edgecolour`
reuses everything and draws `L(G)` — the vertices you see are edges of `G`. -/

/-- `K₃`'s three edges are mutually adjacent, so its chromatic index is 3. -/
def ek3 : EdgeColouring.Problem' := ⟨3, 3, #[(0,1),(1,2),(0,2)]⟩

/-- A path's edges need only two colours. -/
def epath4 : EdgeColouring.Problem' := ⟨4, 2, #[(0,1),(1,2),(2,3)]⟩

end Gallery
end Colouring
end QUBO

/-! ## Press play

Put the cursor on a line; the player appears in the infoview. -/

open QUBO.Colouring.Gallery

section Fire
/-! ### One Boltzmann anneal, one frame per sweep -/

#fire k3
#fire c4
#fire c7
#fire wheel6
#fire crown4
#fire petersen
#fire grotzsch

end Fire

section Swarm
/-! ### The collaborative search, one frame per outer iteration -/

#colour petersen
#colour grotzsch
#colour crown4

end Swarm

section Infeasible
/-! ### No colouring exists — the search correctly finds no zero -/

#colour k3two
#colour k4three
#colour c7two

end Infeasible

section Edges
/-! ### Edge colouring, drawn on the line graph -/

#edgecolour ek3
#edgecolour epath4

end Edges
