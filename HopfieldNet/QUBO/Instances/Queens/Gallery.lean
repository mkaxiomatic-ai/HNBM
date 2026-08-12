/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.QUBO.Instances.Demo

/-!
# Gallery: watch a Hopfield/Boltzmann machine place queens

Open this file in an editor with the Lean infoview. Put the cursor on any `#queensAt`, `#queens`
or `#queensRefute` line and a player appears; press **▶** to watch.

Three views of the same solver, on the same QUBO:

* **`#queensAt b s`** — one annealed run of the Boltzmann machine of eq. (6) on seed `s`, **one
  frame per sweep**. The seeds below are pinned to ones that settle, so opening this file costs one
  anneal per widget. This is the one to press play on: every neuron is resampled from the logistic
  of its accumulated field each sweep with the temperature falling geometrically, so early frames
  scatter queens across the board and late ones settle. Attacking pairs are joined by a dashed
  segment, so you watch the conflicts burn off.
* **`#queens b`** — the full collaborative search of eq. (7), **one frame per outer iteration**.
  Coarse but reliable, and the one that answers "is this placement completable?".
* **`#queensRefute b`** — the same on a placement with **no** completion, on a small population.
  The search correctly finds no zero, and by `exists_zero_iff_queens` that is a proof of nothing
  less than the blockedness of the placement — `blocked4_no_queens` and `blocked6_no_queens` state
  it directly about boards.

## A caveat stated plainly

A *single* annealed run is a poor `n`-queens solver, much poorer than it is a graph colourer, and
the boards below understate that because their seeds were **chosen** to settle.

At `#queensAt`'s schedule — 2000 sweeps, `T = 2·0.998ᵗ` — the fraction of 40 seeds that settle is:

| board                | single anneal | swarm, eq. (7)   |
| -------------------- | ------------- | ---------------- |
| empty `5 × 5`        | 7/40          | solves           |
| `small6`             | **1/40**      | solves           |
| `completion8`        | **1/40**      | solves           |
| empty `8 × 8`        | **0/40**      | 3 outer iters    |

At the *faster* schedule `T = 3·0.99ᵗ` over 400 sweeps, `small6` and `completion8` settle on **no**
seed in `[0,60)` at all, which is why `#queensAt` anneals slowly. The empty `8 × 8` settles on
nothing under either, so its entry below uses `#queens` — the swarm — rather than `#queensAt`.

That contrast is the point, not an embarrassment: it is why Li & Wang's method is *collaborative*.
The authoritative measurement is `QUBO.Queens.Bench`'s anneal column (`0/20` from `N = 6` upward),
not this gallery.

Historical note, because it nearly misled us: before the `2·T₀` correction in `Queens.Widget.anneal`
this file's pinned seeds worked at the *fast* schedule. They only did so because the anneal was
running at half the advertised temperature, and a colder anneal freezes into a solution more
readily. Numbers measured before that fix are not comparable with these.

## Making your own

An instance is `⟨size, givens⟩`, with cells `(row, column)` numbered from `0`:

```lean
def mine : Queens.Instance := ⟨6, #[(0, 1)]⟩
#queens mine
```

The givens are an *input*: an empty array asks "does this board have a solution at all?", a
partial placement asks "can this be extended?". The second question is the interesting one —
NP-complete, and with genuinely negative instances.

The run happens during **elaboration**, so every widget here is executed when the file is opened.
It is tuned to open in about fifteen seconds; a larger board, or `#queensFire` (which restarts
until a run settles), will make the editor wait.
-/

namespace QUBO
namespace Queens
namespace Gallery

/-! ## Boards on which one anneal settles -/

/-- An empty `5 × 5` board: 10 solutions, and the largest board on which a single anneal settles
with any regularity. -/
def q5 : Instance := ⟨5, #[]⟩

/-- `small6` again: one given queen at `(0,1)` on a `6 × 6` board, uniquely completable. -/
def g6 : Instance := small6

/-- `completion8` again: three queens of `sol8` given, uniquely completable. -/
def g8 : Instance := completion8

/-! ## Blocked, on purpose

No completion exists, and the search correctly fails to find a zero. -/

/-- A corner queen on a `4 × 4` board. Blocked — `blocked4_no_queens` is a theorem. -/
def b4 : Instance := blocked4

/-- A corner queen on a `6 × 6` board. Blocked — `blocked6_no_queens` is a theorem. -/
def b6 : Instance := blocked6

/-- Two givens already attacking. Blocked — `attacking_no_queens` is a theorem. -/
def bx : Instance := attacking

/-! ### The pinned seeds are checked, not trusted

Each `#queensAt` below is pinned to a seed on which one annealed run happens to settle. Those
seeds are fragile: they depend on the board, the schedule, and the *exact* temperature. When the
`2·T₀` correction was made to `Queens.Widget.anneal` all three silently stopped settling, and the
gallery began showing stalled boards with no indication that anything had changed --- the widgets
still rendered, they just rendered failure.

`#guard` errors during elaboration when its argument is not `true`, unlike a `#eval` that prints
`false` and is scrolled past. So opening this file now *fails* rather than misleads if a seed stops
working. The schedule below must stay in step with `fireAt`'s. -/
private def settlesAt (I : Instance) (seed : Nat) : Bool :=
  let (x0, g) := randomStart I (Rng.seed seed.toUInt64)
  I.isQueens (I.decode (anneal (problem I) 2000 2.0 0.998 g x0).back!)

#guard settlesAt q5 9
#guard settlesAt g6 11
#guard settlesAt g8 5

end Gallery
end Queens
end QUBO

/-! ## Press play

Put the cursor on a line; the player appears in the infoview. -/

open QUBO.Queens.Gallery

section Fire
/-! ### One Boltzmann anneal, one frame per sweep, on a pinned seed -/

#queensAt q5 9
#queensAt g6 11
#queensAt g8 5

end Fire

section Swarm
/-! ### The collaborative search, one frame per outer iteration

The empty `8 × 8` board, which no single anneal solved. -/

#queens QUBO.Queens.classic8

end Swarm

section Blocked
/-! ### No completion exists — the search correctly finds no zero -/

#queensRefute b4
#queensRefute b6

end Blocked
