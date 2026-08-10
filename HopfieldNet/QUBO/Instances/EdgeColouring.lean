/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.QUBO.Instances.Colouring

/-!
# Edge colouring, for free, via the line graph

A proper edge colouring of `G` is a proper *vertex* colouring of its line graph `L(G)`: one
vertex of `L(G)` per edge of `G`, adjacent when the edges share an endpoint. So this module
needs no new QUBO, no new `Wf` proof and no new soundness argument — it is a data transform
plus the observation that the two checkers are the same function.

That observation is the whole content, and it is deliberately arranged to be `rfl`:
`adjPairs` is used both as `L(G)`'s edge list and as the list `isProperEdgeColouring` quantifies
over, so `Colouring.isColouring (lineGraph I)` and `isProperEdgeColouring I` are *definitionally*
equal rather than provably-after-work.

The pay-off is a second graph problem at the cost of one file, which is the point of having the
theory stated against `QUBO.Incidence` rather than against a puzzle.
-/

namespace QUBO
namespace EdgeColouring

open QUBO.Colouring (Instance)

/-- A graph together with a palette, to be **edge**-coloured. Same data as
`Colouring.Instance`; the difference is what gets coloured. -/
structure Problem' where
  /-- Number of vertices of `G`. -/
  nverts : Nat
  /-- Size of the colour palette. -/
  ncolours : Nat
  /-- The edge list of `G`. -/
  edges : Array (Nat × Nat)
deriving Inhabited, Repr

namespace Problem'

variable (I : Problem')

/-- `|E|`, which is the number of *vertices* of the line graph. -/
def nedges : Nat := I.edges.size

/-- Do edges `e` and `f` of `G` share an endpoint? -/
def shares (e f : Nat) : Bool :=
  match I.edges[e]?, I.edges[f]? with
  | some p, some q => p.1 == q.1 || p.1 == q.2 || p.2 == q.1 || p.2 == q.2
  | _, _ => false

/-- The edges of the line graph: pairs `e < f` of edges of `G` sharing an endpoint.

Built as a `filter` over a range of index pairs, never as a scatter loop, for the usual
reason — a filter is characterised pointwise by `List.mem_filter`. -/
def adjPairs : Array (Nat × Nat) :=
  ((List.range I.nedges).flatMap fun e =>
    ((List.range I.nedges).filter fun f => e < f && I.shares e f).map fun f => (e, f)).toArray

/-- **The line graph**, as a vertex-colouring instance. -/
def lineGraph : Instance where
  nverts := I.nedges
  ncolours := I.ncolours
  edges := I.adjPairs

/-- A proper edge colouring: every edge gets an in-range colour, and edges sharing an endpoint
get different ones. -/
def isProperEdgeColouring (col : Array Nat) : Bool :=
  (col.size == I.nedges)
    && ((List.range I.nedges).all fun e => col.getD e I.ncolours < I.ncolours)
    && I.adjPairs.toList.all fun p => col.getD p.1 I.ncolours != col.getD p.2 I.ncolours

/-- **Edge colouring `G` is vertex colouring `L(G)`** — definitionally, by construction. -/
theorem isColouring_lineGraph (col : Array Nat) :
    Colouring.Instance.isColouring I.lineGraph col = I.isProperEdgeColouring col := rfl

end Problem'

/-- **Soundness**: a zero of the line graph's QUBO decodes to a proper edge colouring of `G`.

Inherited from `Colouring.decode_isColouring`; the only step is the checker identity above. -/
theorem decode_isProperEdgeColouring (I : Problem') (hc : 0 < I.ncolours)
    (hE : I.lineGraph.edgesOk = true) {x : Array Bool}
    (hx : (Colouring.problem I.lineGraph).penaltyDoubled x = 0) :
    I.isProperEdgeColouring (I.lineGraph.decode x) = true := by
  rw [← I.isColouring_lineGraph]
  exact Colouring.decode_isColouring I.lineGraph hc hE hx

/-! ## Examples

`edgesOk` on the line graph is a real side condition: it asks that `adjPairs` has no loop and
that every entry is in range. Both hold by construction of `adjPairs` (`e < f` rules out loops),
and for concrete instances `decide` settles it. -/

/-- `K₃`: three mutually adjacent edges, so its chromatic index is 3. -/
def k3 : Problem' := ⟨3, 3, #[(0, 1), (1, 2), (0, 2)]⟩

/-- `K₃` with two colours for the edges — infeasible. -/
def k3two : Problem' := ⟨3, 2, #[(0, 1), (1, 2), (0, 2)]⟩

/-- A path on four vertices: three edges, chromatic index 2. -/
def path4 : Problem' := ⟨4, 2, #[(0, 1), (1, 2), (2, 3)]⟩

/-- The line graph of `K₃` is again a triangle. -/
example : k3.lineGraph.edges = #[(0, 1), (0, 2), (1, 2)] := by decide

example : k3.lineGraph.edgesOk = true := by decide
example : path4.lineGraph.edgesOk = true := by decide
example : k3two.lineGraph.edgesOk = true := by decide

/-- Colouring the three edges of `K₃` with three colours is proper. -/
example : k3.isProperEdgeColouring #[0, 1, 2] = true := by decide

/-- Two of them the same is not. -/
example : k3.isProperEdgeColouring #[0, 1, 0] = false := by decide

/-- On a path the two ends may share a colour. -/
example : path4.isProperEdgeColouring #[0, 1, 0] = true := by decide

end EdgeColouring
end QUBO
