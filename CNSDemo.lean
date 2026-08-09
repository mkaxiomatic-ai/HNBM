/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.CNS.Widget

/-!
# Watch the CNS Sudoku solver run

Open this file in VS Code and **put the cursor on an `#animate` line** — the player appears in
the infoview panel on the right. Press `▶`, or drag the scrubber, or click the `‖Ax−b‖²` trace
to jump to an outer iteration.

Bold black digits are the puzzle's givens, blue digits are deductions made by Algorithm 1, and
orange digits are values proposed by Algorithm 2. Cells that clash on a row, column or block
get a dashed ring; the count is printed in the caption.

This file is its own `lean_lib` target, and deliberately not a default one: the frames are
computed during elaboration, so anything in the `CNS` glob would re-run the solver on every
`lake build`.

Elaboration is not instant — the solver runs to completion before the first frame appears.
Sabuncu1 is quick; Sabuncu4 takes a second or two. If the infoview shows a progress bar, wait.
-/

/-! ### Algorithm 1 alone

Five of the ten instances never reach the neurodynamic search: constraint propagation closes
them outright, which is what Li & Wang's Table I records as `0` variables remaining. Pure
deduction, one cell per frame.

The next two lines render the same thing by two different routes. `#html` is ProofWidgets'
own command; `#animate` is the sugar defined in `HopfieldNet.CNS.Widget`, which has to mark
its macro expansion canonical for the panel to attach to a source position at all. If the
first shows a board and the second does not, that canonicality handling is the culprit. -/

#html CNS.animate "Sabuncu1"

#animate "Sabuncu1"

/-! ### Both phases

Sabuncu4 is the smallest instance that Algorithm 1 cannot finish. Watch the timeline change
colour at frame 25: the blue segment is the reduction reaching its fixpoint at 95 remaining
variables, and the orange segment is Algorithm 2 driving `‖Ax−b‖²` down to `0` from there. -/

#animate "Sabuncu4"

/-! ### The remaining Table II instances

Sabuncu3, 6, 7 and 9 are the other Table II rows, and all four now close.
`lake exe cns complete all 8` solves and verifies **all ten** instances -- every one on the
first seed except Sabuncu4, which takes the second.

An earlier revision of this file recorded these as near-total failures. That was measured
before two hyperparameters the paper never states were corrected, and the note is kept here
because the failure mode is worth recognising:

* `c₂`, the social learning factor, was at the conventional `c₁ = c₂ = 1`. The social term then
  drags every particle onto the incumbent, which settles on a plateau within a couple of outer
  iterations, so the whole swarm collapses onto the stuck point. `c₁ = 2`, `c₂ = 0.25` fixes it.
* `𝒯`, the diversity threshold, was absolute. Eq. (8)'s `δ` has maximum `1/√n`, so a fixed `𝒯`
  means something different on every instance; on Sabuncu3 it fired mutation on literally every
  iteration. It is now a fraction of `δ_max`.

A third correction was the neuron update: `ModelConfig.sequential` now defaults to `false`, the
synchronous reading the paper specifies. The asynchronous variant costs the DHNm badly (6/10
against 10/10 on Sabuncu3).

The old symptom — incumbent drops fast, flattens at `‖Ax−b‖²` of 4 to 8, then the board stops
changing while the outer counter climbs — is what a collapsed swarm looks like, and is still
reproducible by passing the old constants explicitly:
`lake exe cns solve Sabuncu4 bmm 50 50 30 200 90 1 50 50 0 50 100 100 1`.

The second argument is the seed. -/

#animate "Sabuncu9" 1
#animate "Sabuncu7" 1

-- Slower: 171 and 209 free variables respectively.
-- #animate "Sabuncu3" 1
-- #animate "Sabuncu6" 1
