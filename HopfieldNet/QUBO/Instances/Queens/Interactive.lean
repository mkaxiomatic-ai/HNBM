/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.QUBO.Instances.Queens.Baseline
import HopfieldNet.QUBO.Instances.Queens.Widget

/-!
# A board you can actually play with

Every other widget in this repository is a *replay*: the search runs during elaboration and the
frames are shipped to the infoview as static props (`QUBO.Widget`, and the module docstring there
says so explicitly). This one is live. You click squares to build a partial placement and press a
solver; the browser calls back into the Lean **language server**, which runs the real
`QUBO.search`, `QUBO.Queens.anneal` or `QUBO.Queens.Baseline.solve` and returns the frames.

The mechanism is Lean core's `@[server_rpc_method]`, which registers a handler for the LSP request
`$/lean/rpc/call`. That handler runs inside the file worker, so it fires while you are editing
rather than when the file was elaborated. Two reference examples live in the vendored ProofWidgets:
`ProofWidgets/Demos/LazyComputation.lean` (button → Lean → string) and
`ProofWidgets/Demos/InteractiveSvg.lean` (mouse → Lean → new SVG).

## What this does and does not demonstrate

It runs *the code the theorems are about*. `Queens.decode_isQueens` says a zero of the objective
decodes to a board `isQueens` accepts, and the widget reports the checker's verdict rather than the
solver's opinion. `Queens.exists_zero_iff_queens` is what makes "no zero found" mean something on a
blocked board.

It is **not** a web page: the RPC resolves only while a file importing this module is open in the
editor. And RPC bodies run in the Lean interpreter, so a solve costs roughly what the corresponding
`#eval` costs — seconds for the swarm on an `8 × 8`. The buttons disable while a call is in flight.

## The honest caveat, which is also the point

A single annealed run is a weak `n`-queens solver: measured over 20 seeds at the bench's schedule,
`0/20` settle on an empty `8 × 8` (`QUBO.Queens.Bench`). So the `anneal` button will usually *fail*
on the boards a reader will try first, and the `swarm` button will usually succeed. That contrast is
the demonstration, not a defect — and `Queens.classic8_stationary_infeasible_tendsto_zero` is what
lets us say the failure is a property of the cooling schedule rather than of the encoding.
-/

namespace QUBO
namespace Queens
namespace Interactive

open Lean Server ProofWidgets

/-! ## The wire types

Both are plain `ToJson`/`FromJson` records, which is enough: Lean core provides
`instance [FromJson α] [ToJson α] : RpcEncodable α`, so no `deriving RpcEncodable` is needed. -/

/-- What the board asks for: a partial placement, which solver, and a seed. -/
structure SolveParams where
  /-- Board size `N`. -/
  size : Nat
  /-- The partial placement, as `(row, column)` pairs. These become the instance's `givens`. -/
  givens : Array (Nat × Nat)
  /-- `"anneal"`, `"swarm"` or `"backtrack"`. -/
  mode : String
  /-- Seed for the stochastic modes. -/
  seed : Nat
  deriving ToJson, FromJson, Inhabited

/-- What comes back: frames in the usual one-character-per-board-row encoding, the objective at
each frame, the checker's verdict, a caption, and the number of completions when it is cheap
enough to count. -/
structure SolveResult where
  /-- One frame per step. -/
  frames : Array String
  /-- `‖Âx̂ − b̂‖²` at each frame. -/
  pens : Array Int
  /-- Whether `Instance.isQueens` accepted the final decoded board. -/
  solved : Bool
  /-- Caption text. -/
  note : String
  /-- Number of completions, or `-1` when not computed. -/
  count : Int
  deriving ToJson, FromJson, Inhabited

/-! ## Running a solver

Each branch reuses the existing entry points unchanged — `anneal` and `randomStart` from
`Queens.Widget`, `QUBO.search` from `QUBO.Search`, `Baseline.solve` from `Queens.Baseline`. -/

/-- Counting is exponential, so only do it on boards where it is instant. -/
def countBudget : Nat := 8

/-- One annealed run of eq. (6), one frame per sweep. -/
def runAnneal (I : Instance) (seed : Nat) : SolveResult :=
  let P := problem I
  let (x0, g) := randomStart I (Rng.seed seed.toUInt64)
  let xs := anneal P 400 3.0 0.99 g x0
  let ok := I.isQueens (I.decode xs.back!)
  { frames := xs.map (frameOf I)
    pens := xs.map P.penaltyDoubled
    solved := ok
    note :=
      s!"One annealed Boltzmann machine, eq. (6): 400 sweeps, T = 3.0·0.99^t, seed {seed}. " ++
      (if ok then "It settled on a completion." else
        "It did not settle — expected: a single machine is a weak solver. Try `swarm`.")
    count := -1 }

/-- The collaborative search of eq. (7), one frame per outer iteration. -/
def runSwarm (I : Instance) (seed : Nat) : SolveResult :=
  let P := problem I
  -- `tabulate` matters: `netVec` is twice the local field, and the table is built at `2·T₀` to
  -- cancel that. Without it the run anneals from `T₀/2` and would not match `Queens.Bench`.
  let r := search P Model.bmm
    { N := 20, M := 20, maxOuter := 60,
      model := ModelConfig.tabulate { innerIters := 40, levels := 64, T0 := 3.0, eta := 0.9 },
      captureBoards := true, oneHotInit := true, groups := cellGroups I }
    (Rng.seed seed.toUInt64)
  let frames := r.boards.map (frameOf I)
  let ok := I.isQueens (I.decode r.best)
  { frames := if frames.isEmpty then #[frameOf I r.best] else frames
    pens := if r.boardsE.isEmpty then #[r.penaltyDoubled] else r.boardsE
    solved := ok
    note :=
      if ok then
        s!"The swarm of eq. (7) reached p(x̂) = 0 after {r.outer} outer iterations, and the " ++
        "decoded board passed the checker."
      else
        s!"No zero in {r.outer} outer iterations; best p(x̂) = {r.penaltyDoubled}. On a blocked " ++
        "placement that is the correct answer, and `exists_zero_iff_queens` is what makes it one."
    count := -1 }

/-- The certified classical baseline: one frame, and the completion count when affordable. -/
def runBacktrack (I : Instance) : SolveResult :=
  let cnt : Int := if I.size ≤ countBudget then (Baseline.count I : Int) else -1
  match Baseline.solve I with
  | some q =>
    { frames := #[frameOf I (I.encode q)]
      pens := #[(problem I).penaltyDoubled (I.encode q)]
      solved := I.isQueens q
      note :=
        "Backtracking found a completion. `Baseline.solve_isQueens` proves every board it " ++
        "returns passes the checker, so this answer is certified without trusting the search."
      count := cnt }
  | none =>
    { frames := #[frameOf I (Array.replicate (problem I).nvars false)]
      pens := #[]
      solved := false
      note :=
        "Backtracking found no completion. Soundness of the baseline does not cover this " ++
        "direction — see `Queens.Bench` for the boards where the impossibility is a theorem."
      count := cnt }

/-- Dispatch, with the one hypothesis the theorems need checked up front. -/
def runSolve (p : SolveParams) : SolveResult :=
  let I : Instance := ⟨p.size, p.givens⟩
  if I.givensOk then
    match p.mode with
    | "swarm" => runSwarm I p.seed
    | "backtrack" => runBacktrack I
    | _ => runAnneal I p.seed
  else
    { frames := #[], pens := #[], solved := false, count := -1
      note :=
        "A given queen is off the board. `givensOk` is the single hypothesis of " ++
        "`exists_zero_iff_queens`, and it is exactly what rules this out." }

/-! ## The RPC method

`RequestM.asTask` runs the body on the request's task, so a slow solve does not block the editor.
Nothing here touches `MetaM` or the environment — the solvers are pure functions, which is why no
`WithRpcRef` is needed. -/

@[server_rpc_method]
def queensSolve (p : SolveParams) : RequestM (RequestTask SolveResult) :=
  RequestM.asTask do
    return runSolve p

/-! ## The component -/

/-- Props of `queensBoard.js`: the board to start from. -/
structure BoardProps where
  /-- Initial board size. -/
  size : Nat := 8
  /-- Initial partial placement. -/
  givens : Array (Nat × Nat) := #[]
  deriving ToJson, FromJson, Inhabited

@[widget_module]
def QueensBoard : Component BoardProps where
  javascript := include_str "queensBoard.js"

/-- **The interactive board.** Click squares to place queens, then press a solver. -/
def board (size : Nat := 8) (givens : Array (Nat × Nat) := #[]) : Html :=
  Html.ofComponent QueensBoard { size := size, givens := givens } #[]

end Interactive
end Queens
end QUBO
