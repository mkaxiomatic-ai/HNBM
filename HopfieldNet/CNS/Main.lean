/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.CNS.Search
import HopfieldNet.CNS.Exact
import HopfieldNet.CNS.Instances
import HopfieldNet.CNS.Solver

/-!
# `lake exe cns` — reproduce the paper's results

Subcommands:

| command | what it does |
|---|---|
| `table1` | Algorithm 1 on all ten instances, against Li & Wang's Table I |
| `encoding` | structure behind the `W`/`θ` derivation; `p(x)=0` on the known solutions |
| `reduced` | net input of the reduced problem vs finite differences of its penalty |
| `table2 [runs] [instance]` | Table II: both algorithms, every solution certificate-checked |
| `complete [instance/all] [attempts] ...` | end to end from givens to a verified grid |
| `hard [count] [minDim] [seed] ...` | generated corpus of hard proper puzzles, certified solver, route breakdown |
| `prototype "<81 chars>" ...` | solve one puzzle end to end, always certificate-checked |
| `solve <inst> <dhnm/bmm> [N M inner T0 eta runs Pm T annealOuter c0 c1 c2 seq]` | one configuration, repeated |
| `trace <inst> <model> [N M inner T0 eta seed]` | per-outer-iteration swarm diagnostics |
| `inner <inst> <model> [inner T0 eta seed]` | Fig. 2: inner-loop transient |
| `fig3 <inst> <model> [seed]` | Fig. 3: outer-loop convergence of `p(x*)` |
| `fig9 <inst> <model> [runs] [Ns] [Ms]` | Fig. 9: Monte Carlo over an `(M,N)` grid |
| `count` | solution counts, and the exact solver as a baseline |
| `figs` | Figs 4-8: givens / after reduction with candidates / solved |
| `puzzle <81 chars> [model] [seeds]` | validate, reduce and solve your own grid |
| `bench` | microbenchmarks of the primitives the inner loops depend on |
| `all` | `table1` then `encoding` |

Omitted arguments take the recovered defaults, per instance where one applies. Numeric
arguments are fixed point: `T0`/`c0`/`c1`/`c2` in hundredths, `Pm`/`T` in thousandths.
-/

open CNS

private def pad (s : String) (w : Nat) : String :=
  if s.length ≥ w then s ++ " " else s ++ "".pushn ' ' (w - s.length)

/-- Algorithm 1 against Table I. -/
def runTable1 : IO Bool := do
  IO.println "Table I -- variables remaining after Algorithm 1 (of n^3 = 729)"
  IO.println ""
  IO.println (pad "instance" 12 ++ pad "givens" 8 ++ pad "remaining" 11
    ++ pad "Table I" 9 ++ pad "rounds" 8 ++ "match")
  let mut ok := true
  for e in Instances.all do
    match Grid.ofString e.givens with
    | none =>
      IO.println s!"{e.name}: could not parse givens"
      ok := false
    | some g =>
      let r := reduce g
      let hit := r.remaining == e.table1
      if !hit then ok := false
      IO.println (pad e.name 12 ++ pad (toString g.numGivens) 8
        ++ pad (toString r.remaining) 11 ++ pad (toString e.table1) 9
        ++ pad (toString r.rounds) 8 ++ (if hit then "yes" else "NO"))
  IO.println ""
  IO.println (if ok then "All ten agree with Table I."
              else "MISMATCH against Table I.")
  return ok

/-- Structural checks on `A`, `W`, `θ`, and the canonical-form identity. -/
def runEncoding : IO Bool := do
  IO.println "QUBO encoding -- structure of A, W, theta"
  IO.println ""
  let mut ok := true
  let check (name : String) (b : Bool) : IO Unit := do
    IO.println (pad name 46 ++ (if b then "yes" else "NO"))
  let nbr := neighbourCount 0
  let allNbr := (Array.range numVars).all fun v => neighbourCount v == 28
  let thetaAll := (Array.range numVars).all fun v => theta v == -2
  ok := ok && colsHave4 && rowsHaveN && weightSymm && weightDiagZero && allNbr && thetaAll
          && specMatchesTable
  check "A is 4n^2 x n^3 = 324 x 729" (numRows == 324 && numVars == 729)
  check "every column of A has exactly 4 nonzeros" colsHave4
  check "every row of A has exactly n = 9 nonzeros" rowsHaveN
  check s!"every variable has exactly 28 neighbours (v0 = {nbr})" allNbr
  check "W is symmetric" weightSymm
  check "W has zero diagonal (required by TwoState.ZeroOne)" weightDiagZero
  check "theta = -2 uniformly" thetaAll
  check "varsOfRowSpec agrees with the computed varsOfRow" specMatchesTable
  IO.println (pad "additive constant  (1/2)||b||^2" 46 ++ toString (penaltyConst / 2))
  IO.println ""
  IO.println "p(x) on the known solutions, and the canonical-form identity"
  IO.println ""
  IO.println (pad "instance" 12 ++ pad "||Ax-b||^2" 12 ++ pad "p(x)" 8
    ++ pad "canonical" 11 ++ "agree")
  for e in Instances.all do
    match Grid.ofString e.solution with
    | none =>
      IO.println s!"{e.name}: could not parse solution"
      ok := false
    | some s =>
      let x := encode s
      let d := penaltyDoubled x
      let c := canonicalDoubled x
      let agree := d == c
      if !agree || d != 0 then ok := false
      IO.println (pad e.name 12 ++ pad (toString d) 12
        ++ pad (toString (d / 2)) 8 ++ pad (toString c) 11
        ++ (if agree then "yes" else "NO"))
  IO.println ""
  IO.println (if ok then "Encoding verified: p(x) = 0 on every solution, and -x'Wx + 2*theta'x + ||b||^2 agrees with ||Ax-b||^2."
              else "Encoding check FAILED.")
  return ok

/-- Check the reduced problem's net input against a finite difference of its penalty.

With `W` symmetric and zero-diagonal, `p2` depends on `x_u` only through `-2*x_u*net_u`, so
setting `x_u` from 0 to 1 must change `p2` by exactly `-2*net_u`. If `theta_hat` or `netVec`
were wrong, the dynamics would descend a different function from the one being reported. -/
def runReduced : IO Bool := do
  IO.println "Reduced problem: netVec vs finite difference of p2"
  IO.println ""
  IO.println (pad "instance" 12 ++ pad "nvars" 8 ++ pad "checks" 10 ++ "all agree")
  let mut ok := true
  for e in Instances.all do
    if e.table1 == 0 then continue
    let some g := Grid.ofString e.givens | pure ()
    let P := Problem.ofGrid g
    let mut agree := true
    let mut checks := 0
    let mut rng := Rng.seed 7
    for _ in [0:20] do
      let (x, r1) := rng.bits P.nvars
      rng := r1
      let net := P.netVec x
      for u in [0:P.nvars] do
        let x0 := x.set! u false
        let x1 := x.set! u true
        let d := P.penaltyDoubled x1 - P.penaltyDoubled x0
        if d != -2 * (net.getD u 0) then agree := false
        checks := checks + 1
    if !agree then ok := false
    IO.println (pad e.name 12 ++ pad (toString P.nvars) 8 ++ pad (toString checks) 10
      ++ (if agree then "yes" else "NO"))
  IO.println ""
  IO.println (if ok then "Reduced dynamics descend exactly the reported objective."
              else "MISMATCH: netVec disagrees with the penalty it is supposed to minimise.")
  -- the bridge: does the reduced objective agree with the unreduced one under `embed`?
  IO.println ""
  IO.println "Bridge: Problem.penaltyDoubled P x  vs  CNS.penaltyDoubled (embed P x)"
  IO.println ""
  IO.println (pad "instance" 12 ++ pad "trials" 9 ++ "agree")
  let mut bok := true
  for e in Instances.all do
    if e.table1 == 0 then continue
    let some g := Grid.ofString e.givens | pure ()
    let R := reduce g
    let P := Problem.ofReduced R
    let mut agree := true
    let mut rng := Rng.seed 11
    for _ in [0:200] do
      let (x, r1) := rng.bits P.nvars
      rng := r1
      if P.penaltyDoubled x != CNS.penaltyDoubled (P.embed R.fixedVal x) then agree := false
    if !agree then bok := false
    IO.println (pad e.name 12 ++ pad "200" 9 ++ (if agree then "yes" else "NO"))
  IO.println ""
  IO.println (if bok then "Bridge holds: the solver's objective is the paper's p(x) under `embed`."
              else "BRIDGE FAILS.")
  return (ok && bok)

/-- Restrict a known full solution to the reduced variables, as a sanity target. -/
private def solutionOf (P : Problem) (sol : Grid) : Array Bool :=
  (Array.range P.nvars).map fun u =>
    let v := P.varOf.getD u 0
    sol.get (v / n) == some (v % n)

/-- Solve one instance a number of times and report the distribution of `p(x*)`. -/
def runSolve (nm : String) (mdl : Model) (cfg : SearchConfig) (runs : Nat) (seed0 : Nat) :
    IO Bool := do
  let some e := Instances.find? nm | do IO.println s!"no such instance '{nm}'"; return false
  let some g := Grid.ofString e.givens | do IO.println "bad givens"; return false
  let P := Problem.ofGrid g
  let some sol := Grid.ofString e.solution | do IO.println "bad solution"; return false
  let target := P.penaltyDoubled (solutionOf P sol)
  IO.println s!"{nm}: nvars={P.nvars} (Table I {e.table1}); p2 at a known solution = {target}"
  let mut solved := 0
  let mut worst : Int := 0
  let mut best : Int := 1000000
  let mut totalMs := 0
  let mut totalOuter := 0
  let mut certOk := true
  for k in [0:runs] do
    let t0 ← IO.monoMsNow
    -- `search` is pure and therefore lazy: force it *before* reading the clock, or the
    -- measurement records nothing and the work happens later.
    let r := search P mdl cfg (Rng.seed (UInt64.ofNat (seed0 + k)))
    let pd := r.penaltyDoubled
    let ou := r.outer
    if pd < 0 then IO.println "unreachable"
    if ou > 1000000 then IO.println "unreachable"
    let t1 ← IO.monoMsNow
    totalMs := totalMs + (t1 - t0)
    totalOuter := totalOuter + ou
    if pd == 0 then
      -- Certificate check: p(x)=0 must correspond to a genuine completion of the givens.
      -- The search is untrusted; this is the part that has to be right.
      let sol := P.toGrid r.best
      if sol.isSolution && g.extends' sol then
        solved := solved + 1
      else
        IO.println s!"  *** p(x)=0 but the decoded grid is not a valid completion (seed {seed0 + k})"
        certOk := false
    if pd > worst then worst := pd
    if pd < best then best := pd
  IO.println s!"{mdl.name}  N={cfg.N} M={cfg.M} inner={cfg.model.innerIters} T0={cfg.model.T0} eta={cfg.model.eta}"
  IO.println s!"  runs={runs} solved={solved}/{runs}  best p2={best} worst p2={worst}  avg {totalMs / max runs 1} ms/run  avg {totalOuter / max runs 1} outer"
  IO.println (if certOk then "  every p(x)=0 result verified as a valid completion of the givens"
              else "  *** CERTIFICATE FAILURE")
  return (solved == runs && certOk)

/-- Trace one search, printing the swarm state each outer iteration. -/
def runTrace (nm : String) (mdl : Model) (cfg : SearchConfig) (seed : Nat) : IO Bool := do
  let some e := Instances.find? nm | do IO.println "no such instance"; return false
  let some g := Grid.ofString e.givens | do IO.println "bad givens"; return false
  let P := Problem.ofGrid g
  let r := search P mdl { cfg with trace := true } (Rng.seed (UInt64.ofNat seed))
  IO.println s!"{nm} nvars={P.nvars} seed={seed} -> p2={r.penaltyDoubled} outer={r.outer}"
  -- anatomy of the final state: distance to a true solution, and which rows are violated
  if let some sol := Grid.ofString e.solution then
    let tgt := solutionOf P sol
    let mut ham := 0
    for u in [0:P.nvars] do
      if r.best.getD u false != tgt.getD u false then ham := ham + 1
    let ρ := P.rowSums r.best
    let mut viol : Array String := #[]
    for rr in [0:numRows] do
      let d := (ρ.getD rr 0) - (P.bhat.getD rr 0)
      if d != 0 then
        let fam := if rr < 81 then "cell" else if rr < 162 then "col" else if rr < 243 then "row" else "box"
        viol := viol.push s!"{fam}#{rr} resid={d}"
    IO.println s!"  hamming(best, true solution) = {ham} of {P.nvars} free vars"
    IO.println s!"  violated rows: {viol.toList}"
    IO.println s!"  grid:"
    IO.println ((P.toGrid r.best).pretty)
  IO.println (pad "outer" 8 ++ pad "starE" 8 ++ pad "bestPb" 8 ++ pad "meanPb" 9
    ++ pad "diversity" 12 ++ pad "mutated" 9 ++ "distinctPbest")
  for (o, sE, bE, mE, d, mu, dc) in r.trace do
    IO.println (pad (toString o) 8 ++ pad (toString sE) 8 ++ pad (toString bE) 8
      ++ pad (toString mE) 9 ++ pad (toString d) 12 ++ pad (if mu then "yes" else "no") 9
      ++ toString dc)
  return r.solved

/-- Reproduce Fig. 2: the inner-loop transient of a single model. -/
def runInner (nm : String) (mdl : Model) (cfg : ModelConfig) (seed : Nat) : IO Bool := do
  let some e := Instances.find? nm | do IO.println "no such instance"; return false
  let some g := Grid.ofString e.givens | do IO.println "bad givens"; return false
  let P := Problem.ofGrid g
  let (x0, g1) := (Rng.seed (UInt64.ofNat seed)).bits P.nvars
  IO.println s!"{nm} nvars={P.nvars}: p2 per inner iteration (paper Fig. 2 falls monotonically)"
  -- replay the recurrence one sweep at a time
  let mut u : Array Int := Array.replicate P.nvars 0
  let mut x := x0
  let mut gg := g1
  let mut T := cfg.T0
  let mut line := s!"  t=0 p2={P.penaltyDoubled x}"
  for t in [0:cfg.innerIters] do
    match mdl with
    | .dhnm =>
        let (u', x') := dhnmStep P u x
        u := u'; x := x'
    | .bmm =>
        let (u', x', g') := bmmStep P T gg u x
        u := u'; x := x'; gg := g'
    T := T * cfg.eta
    line := line ++ s!"  t={t+1} p2={P.penaltyDoubled x}"
    if (t + 1) % 6 == 0 then
      IO.println line
      line := " "
  IO.println line
  return true

/-- Li & Wang's Table II settings, together with the hyperparameters recovered here.

`N` and `M` are the paper's, per row. `inner` is the number of inner iterations, which the
paper does not state; it tracks problem size (the paper's own Fig. 2 shows Sabuncu6 needing
~100 sweeps where the others need ~30). Everything else is shared across all rows. -/
structure Row where
  /-- Instance name. -/
  name : String
  /-- Population size for CNS/DHNm, from Table II. -/
  nDhnm : Nat
  /-- Population size for CNS/BMm, from Table II. -/
  nBmm : Nat
  /-- Termination criterion `M`, from Table II. -/
  M : Nat
  /-- Inner iterations (recovered). -/
  inner : Nat
  /-- Initial temperature `T₀` for CNS/BMm (recovered, per instance).

  Unlike `inner` (which tracks `nvars/3`) and `𝒯` (a fixed fraction of `1/√n`), this does not
  reduce to a size rule: Sabuncu9 at 163 variables wants a hotter start than Sabuncu3 at 171.
  It is reported as a recovered constant rather than dressed up as a formula. -/
  T0 : Float
  /-- Bit-flip rate `P_m` for CNS/DHNm (recovered, per instance).

  The DHNm is deterministic, so mutation supplies all of its exploration and the right rate is
  instance-dependent in the same way `T₀` is for the BMm: Sabuncu9 wants `0.1` (14/15 against
  8/10 at `0.05`) while Sabuncu3 wants `0.05` (10/10 against 13/15 at `0.1`). -/
  pmDhnm : Float

/-- The five rows of Table II. -/
def table2Rows : Array Row := #[
  { name := "Sabuncu3", nDhnm := 200,  nBmm := 40,  M := 50,  inner := 60,  T0 := 3.0, pmDhnm := 0.05 },
  { name := "Sabuncu4", nDhnm := 200,  nBmm := 50,  M := 50,  inner := 30,  T0 := 3.0, pmDhnm := 0.05 },
  { name := "Sabuncu6", nDhnm := 2000, nBmm := 500, M := 200, inner := 100, T0 := 3.0, pmDhnm := 0.05 },
  { name := "Sabuncu7", nDhnm := 1000, nBmm := 200, M := 200, inner := 80,  T0 := 8.0, pmDhnm := 0.05 },
  { name := "Sabuncu9", nDhnm := 300,  nBmm := 100, M := 150, inner := 80,  T0 := 5.0, pmDhnm := 0.10 }]

/-- Reproduce Table II: every row, both algorithms, `runs` Monte Carlo repetitions. -/
def runTable2 (runs : Nat) (only : String) : IO Bool := do
  IO.println s!"Table II -- CNS/DHNm and CNS/BMm, {runs} runs per cell"
  IO.println "(paper reports best/worst = 0/0 and mean+-std = 0.00 +- 0.00 for every cell"
  IO.println " except CNS/DHNm on Sabuncu7, whose published row is internally inconsistent)"
  IO.println ""
  IO.println (pad "instance" 11 ++ pad "dim" 6 ++ pad "algorithm" 11 ++ pad "N" 7
    ++ pad "M" 6 ++ pad "solved" 10 ++ pad "best/worst" 12 ++ "ms/run")
  let mut allOk := true
  for row in table2Rows do
    for mdl in #[Model.dhnm, Model.bmm] do
      if only != "" && only != row.name then continue
      let n := if mdl == Model.dhnm then row.nDhnm else row.nBmm
      let some e := Instances.find? row.name | pure ()
      let some g := Grid.ofString e.givens | pure ()
      let P := Problem.ofGrid g
      -- The diversity threshold differs by model, and for a principled reason: the BMm has its
      -- own stochasticity (the "local hill-climbing capability" the paper credits it with), so
      -- mutation need only fire when the swarm has collapsed. The DHNm is deterministic -- each
      -- particle descends to a fixed point of the same map -- so mutation supplies *all* of its
      -- exploration and must fire almost every iteration. This is the same asymmetry the paper
      -- invokes when it observes that CNS/BMm needs a much smaller population than CNS/DHNm.
      let tau := if mdl == Model.dhnm then 0.9 else 0.4
      let pm := if mdl == Model.dhnm then row.pmDhnm else 0.05
      let cfg : SearchConfig :=
        { N := n, M := row.M, divThreshold := tau, Pm := pm,
          model := ModelConfig.tabulate { innerIters := row.inner, T0 := row.T0, eta := 0.9 } }
      let mut solved := 0
      let mut best : Int := 1000000
      let mut worst : Int := 0
      let mut ms := 0
      for k in [0:runs] do
        let t0 ← IO.monoMsNow
        let r := search P mdl cfg (Rng.seed (UInt64.ofNat (1 + k)))
        let pd := r.penaltyDoubled
        if pd < 0 then IO.println "unreachable"
        let t1 ← IO.monoMsNow
        ms := ms + (t1 - t0)
        if pd < best then best := pd
        if pd > worst then worst := pd
        if pd == 0 then
          let sol := P.toGrid r.best
          if sol.isSolution && g.extends' sol then solved := solved + 1
          else IO.println "  *** certificate failure"; allOk := false
      if solved != runs then allOk := false
      IO.println (pad row.name 11 ++ pad (toString P.nvars) 6 ++ pad mdl.name 11
        ++ pad (toString n) 7 ++ pad (toString row.M) 6
        ++ pad s!"{solved}/{runs}" 10
        ++ pad s!"{best / 2}/{worst / 2}" 12 ++ toString (ms / max runs 1))
  IO.println ""
  IO.println (if allOk then "All cells solved in every run; every solution certificate-checked."
              else "Some cells did not reach p(x)=0 in every run.")
  return allOk

/-- Reproduce the incumbent curve of Fig. 3: outer-loop convergence of `p(x*)`.

The paper's plots also show `N` faint per-particle `f(x⁽ⁱ⁾)` trajectories behind the incumbent.
Those are *not* reproduced: `SearchResult.trace` aggregates the population to best and mean, so
recovering the individual trajectories needs a new trace channel. -/
def runFig3 (nm : String) (mdl : Model) (seed : Nat) : IO Bool := do
  let some row := table2Rows.find? (fun r => r.name == nm)
    | do IO.println s!"no Table II row for '{nm}'"; return false
  let some e := Instances.find? nm | do IO.println "no instance"; return false
  let some g := Grid.ofString e.givens | do IO.println "bad givens"; return false
  let P := Problem.ofGrid g
  let n := if mdl == Model.dhnm then row.nDhnm else row.nBmm
  let tau := if mdl == Model.dhnm then 0.9 else 0.4
  let cfg : SearchConfig :=
    { N := n, M := row.M, divThreshold := tau, trace := true,
      model := ModelConfig.tabulate { innerIters := row.inner, T0 := row.T0, eta := 0.9 } }
  let r := search P mdl cfg (Rng.seed (UInt64.ofNat seed))
  IO.println s!"Fig. 3 -- {nm}, {mdl.name}, M = {row.M} and N = {n}"
  IO.println s!"final p(x*) = {r.penaltyDoubled / 2} after {r.outer} outer iterations"
  IO.println ""
  IO.println (pad "outer" 8 ++ "p(x*)")
  for (o, sE, _, _, _, _, _) in r.trace do
    IO.println (pad (toString o) 8 ++ toString (sE / 2))
  return r.solved

/-- Reproduce Fig. 9: Monte Carlo over a grid of `M` and `N`.

Fig. 9 is ten subplots, each with its *own* 5x5 grid of `(M, N)` pairs -- not one shared grid;
the axes differ by instance and by algorithm. At the paper's 100 repetitions that is
250 cells x 100 = 25,000 CNS runs, on the order of 5.6e8 neurodynamic equilibrations and weeks
of single-core time, with the Sabuncu6 DHNm subplot alone accounting for nearly half. `runs`
and both axes are therefore exposed so the sweep can be run at reduced fidelity. -/
def runFig9 (nm : String) (mdl : Model) (runs : Nat) (ns ms : List Nat) : IO Bool := do
  let some e := Instances.find? nm | do IO.println "no instance"; return false
  let some g := Grid.ofString e.givens | do IO.println "bad givens"; return false
  let some row := table2Rows.find? (fun r => r.name == nm) | do IO.println "no row"; return false
  let P := Problem.ofGrid g
  let tau := if mdl == Model.dhnm then 0.9 else 0.4
  IO.println s!"Fig. 9 -- {nm}, {mdl.name}, {runs} runs per cell; entries are median p(x*)"
  IO.println ""
  IO.print (pad "N / M" 9)
  for m in ms do IO.print (pad (toString m) 8)
  IO.println ""
  for nn in ns do
    IO.print (pad (toString nn) 9)
    for m in ms do
      let cfg : SearchConfig :=
        { N := nn, M := m, divThreshold := tau,
          model := ModelConfig.tabulate { innerIters := row.inner, T0 := row.T0, eta := 0.9 } }
      let mut vals : Array Int := #[]
      for k in [0:runs] do
        let r := search P mdl cfg (Rng.seed (UInt64.ofNat (1 + k)))
        vals := vals.push (r.penaltyDoubled / 2)
      let sorted := vals.qsort (· < ·)
      IO.print (pad (toString (sorted.getD (runs / 2) 0)) 8)
    IO.println ""
  return true

/-- Count completions of every benchmark instance, and time the exact solver against the
neurodynamic search.

The paper's Table II column headed "# of solutions" is `2^dim`, the size of the reduced search
space; these are the actual solution counts. -/
def runCount : IO Bool := do
  IO.println "Solution counts, and exact solver vs. the neurodynamic search"
  IO.println ""
  IO.println (pad "instance" 12 ++ pad "givens" 8 ++ pad "2^dim (paper)" 15
    ++ pad "solutions" 11 ++ pad "exact ms" 10 ++ "status")
  let mut ok := true
  for e in Instances.all do
    match Grid.ofString e.givens with
    | none => IO.println s!"{e.name}: bad givens"; ok := false
    | some g =>
      let t0 ← IO.monoMsNow
      let st := classify g 100
      let cnt := countSolutions g 100
      if cnt == 0 then ok := false
      let t1 ← IO.monoMsNow
      let dim := if e.table1 == 0 then "1" else s!"2^{e.table1}"
      IO.println (pad e.name 12 ++ pad (toString g.numGivens) 8 ++ pad dim 15
        ++ pad (toString cnt) 11 ++ pad (toString (t1 - t0)) 10 ++ st.describe)
  IO.println ""
  IO.println (if ok then "Every instance has at least one completion."
              else "An instance has no completion -- the recovered data would be wrong.")
  return ok

/-- Solve an arbitrary 81-character puzzle supplied on the command line. -/
def runPuzzle (spec : String) (mdl : Model) (runs : Nat) : IO Bool := do
  match Grid.ofString spec with
  | none =>
    IO.println s!"expected {numCells} characters ('1'-'9' for a given, any other for empty); got {spec.length}"
    return false
  | some g =>
    IO.println s!"puzzle: {g.numGivens} givens"
    IO.println g.pretty
    IO.println ""
    let st := classify g 100
    IO.println s!"exact solver: {st.describe}"
    if st == Status.unsolvable then return false
    let R := reduce g
    IO.println s!"Algorithm 1: {R.rounds} deductions, {R.remaining} of {numVars} variables remain"
    if R.remaining == 0 then
      IO.println "solved by constraint propagation alone"
      IO.println R.grid.pretty
      return R.grid.isSolution && g.extends' R.grid
    let P := Problem.ofReduced R
    let inner := max 30 (P.nvars / 3)
    let cfg : SearchConfig :=
      { N := 50, M := 100,
        model := ModelConfig.tabulate { innerIters := inner, T0 := 3.0, eta := 0.9 } }
    let mut solved := false
    for k in [0:runs] do
      if !solved then
        let r := search P mdl cfg (Rng.seed (UInt64.ofNat (1 + k)))
        if r.penaltyDoubled == 0 then
          let sol := P.toGrid r.best
          if sol.isSolution && g.extends' sol then
            IO.println s!"{mdl.name}: solved on seed {k + 1}"
            IO.println sol.pretty
            solved := true
    if !solved then IO.println s!"{mdl.name}: not solved in {runs} seeds"
    return solved

/-- Render one board in the style of Figs 4-8: a given or fixed digit, or the candidate list of
an open cell. -/
private def figBoard (g : Grid) (showCands : Bool) : String :=
  String.intercalate "\n" <|
    (List.range n).map fun i =>
      String.intercalate " " <|
        (List.range n).map fun j =>
          let c := cellIdx i j
          match g.get c with
          | some k => pad (Nat.repr (k + 1)) 10
          | none =>
            if !showCands then pad "." 10
            else
              let cs := candidatesAt g c
              pad (String.join ((cs.toList.map (fun k => Nat.repr (k + 1))))) 10

/-- Reproduce Figs 4-8: for each Table II instance, the three boards the paper prints --
the puzzle, the state after Algorithm 1 with the surviving candidate lists, and the solution.

The paper renders these as coloured grids; here the middle board shows each open cell's
candidate list, which is the information those figures carry. -/
def runFigs (which : String) : IO Bool := do
  let mut ok := true
  for e in Instances.all do
    if e.table1 == 0 then continue
    if which != "" && which != e.name then continue
    match Grid.ofString e.givens with
    | none => IO.println s!"{e.name}: bad givens"; ok := false
    | some g =>
      let R := reduce g
      IO.println s!"=== {e.name} ({g.numGivens} givens; Algorithm 1 leaves {R.remaining} of {numVars} variables) ==="
      IO.println ""
      IO.println "-- given (left board)"
      IO.println (figBoard g false)
      IO.println ""
      IO.println s!"-- after Algorithm 1, with candidate lists (middle board): {R.rounds} deductions"
      IO.println (figBoard R.grid true)
      IO.println ""
      match solveExact g with
      | none => IO.println "-- no solution"; ok := false
      | some sol =>
        IO.println "-- solved (right board)"
        IO.println (figBoard sol false)
        if !(sol.isSolution && g.extends' sol) then ok := false
      IO.println ""
  IO.println (if ok then "All boards rendered and verified." else "A board failed to verify.")
  return ok

/-- Microbenchmark the primitives the inner loops depend on. -/
def runBench : IO Unit := do
  let N := 10000000
  IO.println s!"{N} iterations of each primitive"
  let t0 ← IO.monoMsNow
  let mut ai : Int := 0
  for _ in [0:N] do ai := ai + 1
  if ai < 0 then IO.println "x"
  let t1 ← IO.monoMsNow
  IO.println (pad "Int add" 24 ++ s!"{t1 - t0} ms")
  let mut af : Float := 0.0
  for _ in [0:N] do af := af + 1.0
  if af < 0.0 then IO.println "x"
  let t2 ← IO.monoMsNow
  IO.println (pad "Float add" 24 ++ s!"{t2 - t1} ms")
  let mut ac : Float := 0.0
  let mut k : Int := 0
  for _ in [0:N] do
    k := k + 1
    ac := ac + Float.ofInt k
  if ac < 0.0 then IO.println "x"
  let t3 ← IO.monoMsNow
  IO.println (pad "Int add + Float.ofInt" 24 ++ s!"{t3 - t2} ms")
  let mut ae : Float := 0.0
  for _ in [0:N] do ae := ae + Float.exp 0.5
  if ae < 0.0 then IO.println "x"
  let t4 ← IO.monoMsNow
  IO.println (pad "Float.exp" 24 ++ s!"{t4 - t3} ms")
  let mut st : UInt64 := 1
  for _ in [0:N] do
    st := st + 0x9E3779B97F4A7C15
    let mut z := st
    z := (z ^^^ (z >>> 30)) * 0xBF58476D1CE4E5B9
    z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
    st := st ^^^ (z >>> 31)
  if st == 12345 then IO.println "x"
  let t5 ← IO.monoMsNow
  IO.println (pad "splitmix64" 24 ++ s!"{t5 - t4} ms")
  let mut arr : Array Int := Array.replicate 400 0
  for i in [0:N] do
    arr := arr.set! (i % 400) 1
  if arr.getD 0 0 < 0 then IO.println "x"
  let t6 ← IO.monoMsNow
  IO.println (pad "Array Int set!" 24 ++ s!"{t6 - t5} ms")
  let mut tot : Int := 0
  for _ in [0:N / 400] do
    let a : Array Int := Array.replicate 400 0
    tot := tot + a.getD 0 0
  if tot < 0 then IO.println "x"
  let t7 ← IO.monoMsNow
  IO.println (pad "Array.replicate 400" 24 ++ s!"{t7 - t6} ms  (x{N / 400} allocs)")

/-- Produce a completed grid for one instance and check it.

Algorithm 1 finishes five of the ten on its own; the rest go to Algorithm 2, retried across
seeds until `p(x) = 0`. The search is untrusted — `Grid.isSolution` and `Grid.extends'` are
what make the printed grid mean anything. -/
private def completeOne (e : Instances.Entry) (attempts : Nat) (cfg : SearchConfig) :
    IO Bool := do
  let some g := Grid.ofString e.givens
    | do IO.println s!"{e.name}: bad givens"; return false
  let t0 ← IO.monoMsNow
  let R := reduce g
  if R.remaining == 0 then
    let ok := R.grid.isSolution && g.extends' R.grid
    let t1 ← IO.monoMsNow
    IO.println s!"{e.name}  {g.numGivens} givens -> Algorithm 1 alone, {R.rounds} rounds, {t1 - t0} ms"
    IO.println (if ok then "  verified: a valid completion of the givens"
                else "  *** NOT a valid completion")
    IO.println R.grid.pretty
    return ok
  let P := Problem.ofGrid g
  let mut k := 0
  while k < attempts do
    k := k + 1
    let r := search P Model.bmm cfg (Rng.seed (UInt64.ofNat k))
    if r.solved then
      let sol := P.toGrid r.best
      let ok := sol.isSolution && g.extends' sol
      let t1 ← IO.monoMsNow
      IO.println s!"{e.name}  {g.numGivens} givens -> Algorithm 1 leaves {P.nvars} vars, then Algorithm 2 on seed {k} of {k} tried, {t1 - t0} ms"
      IO.println (if ok then "  verified: a valid completion of the givens"
                  else "  *** p(x)=0 but NOT a valid completion")
      IO.println sol.pretty
      return ok
  let t1 ← IO.monoMsNow
  IO.println s!"{e.name}  {g.numGivens} givens -> Algorithm 1 leaves {P.nvars} vars; no seed of {attempts} reached p(x)=0 ({t1 - t0} ms)"
  return false

/-- `lake exe cns complete [instance] [attempts] ...` — a finished, verified grid for each
instance, end to end from the paper's givens. -/
def runComplete (which : Option String) (attempts : Nat) (cfg : SearchConfig) : IO Bool := do
  let entries : Array Instances.Entry := match which with
    | some nm => Instances.all.filter (fun e => e.name == nm)
    | none    => Instances.all
  if entries.isEmpty then
    IO.println "no such instance"
    return false
  IO.println s!"Completing {entries.size} instance(s); up to {attempts} seeds each."
  IO.println ""
  let mut nOk := 0
  for e in entries do
    if ← completeOne e attempts cfg then nOk := nOk + 1
    IO.println ""
  IO.println s!"{nOk}/{entries.size} completed and verified against their givens."
  return nOk == entries.size

/-! ## A harder corpus, and the certified solver

`table1`–`table2` reproduce the paper. These two commands answer the question the paper does not
ask: how does the method do on instances that are actually hard, and what happens when it
fails? -/

/-- Generate a corpus and run the certified solver on it, reporting which stage succeeded.

The point of the table is the `route` column. Every row is a *verified* completion regardless of
which stage produced it, so the neurodynamic column measures reach, not correctness. -/
def runHard (count : Nat) (minDim : Nat) (seedN : Nat) (mdl : Model) (restarts : Nat) :
    IO Bool := do
  IO.println s!"Generated corpus -- {count} proper puzzles with post-reduction dimension >= {minDim}"
  IO.println s!"model {mdl.name}, {restarts} restart(s) before the exact fallback"
  IO.println ""
  IO.println "  #  givens   dim   route                     ms   verified"
  let mut g := Rng.seed (UInt64.ofNat (seedN + 1))
  let mut nNeuro := 0
  let mut nProp := 0
  let mut nFall := 0
  let mut nOk := 0
  let mut made := 0
  for i in [0:count] do
    let (p?, g') := genHard g minDim 40
    g := g'
    match p? with
    | none => IO.println s!"  {i}  (no instance at that dimension in 40 tries)"
    | some q =>
      made := made + 1
      let t0 ← IO.monoMsNow
      let out := solveCertified q.grid mdl restarts
      -- force the whole computation inside the timed region: `out` is a pure `let`, and
      -- inspecting a field is what actually runs the search
      let verified :=
        match out.solution with
        | some sol => accepts q.grid sol
        | none => false
      let t1 ← IO.monoMsNow
      match out.route with
      | .propagation => nProp := nProp + 1
      | .neurodynamic _ => nNeuro := nNeuro + 1
      | .exactFallback => nFall := nFall + 1
      | .unsolvable => pure ()
      if verified then nOk := nOk + 1
      IO.println s!"  {i}  {pad (Nat.repr q.givens) 6} {pad (Nat.repr q.dim) 5}   \
        {pad out.route.name 22} {pad (Nat.repr (t1 - t0)) 5}   {if verified then "yes" else "NO"}"
  IO.println ""
  IO.println s!"solved by propagation alone   {nProp}/{made}"
  IO.println s!"solved by the neurodynamics   {nNeuro}/{made}"
  IO.println s!"needed the exact fallback     {nFall}/{made}"
  IO.println s!"verified completions          {nOk}/{made}"
  IO.println ""
  IO.println "Every reported completion passes `accepts` -- `isSolution` together with the givens."
  return nOk == made && made == count

/-- Solve one user-supplied puzzle end to end, always verified. -/
def runPrototype (spec : String) (mdl : Model) (restarts : Nat) : IO Bool := do
  match Grid.ofString spec with
  | none =>
    IO.println s!"expected {numCells} characters ('1'-'9' for a given, any other for empty); \
      got {spec.length}"
    return false
  | some g =>
    IO.println s!"puzzle: {g.numGivens} givens"
    IO.println g.pretty
    IO.println ""
    let t0 ← IO.monoMsNow
    let out := solveCertified g mdl restarts
    let ok := match out.solution with | some sol => accepts g sol | none => false
    let t1 ← IO.monoMsNow
    IO.println s!"post-reduction dimension: {out.dim}"
    IO.println s!"route: {out.route.name}   ({t1 - t0} ms)"
    match out.solution with
    | none =>
      IO.println "no completion exists (exact solver)"
      return false
    | some sol =>
      IO.println ""
      IO.println sol.pretty
      IO.println ""
      IO.println s!"certificate: {if ok then "valid completion of the givens" else "REJECTED"}"
      return ok

def main (args : List String) : IO UInt32 := do
  let cmd := args.headD "all"
  let ok ←
    match cmd with
    | "table1"   => runTable1
    | "encoding" => runEncoding
    | "reduced"  => runReduced
    | "bench"    => do runBench; pure true
    | "count"    => runCount
    | "figs"     => runFigs ((args.tail).headD "")
    | "puzzle"   =>
        let a := args.tail
        runPuzzle (a.headD "")
          (if a.getD 1 "bmm" == "dhnm" then Model.dhnm else Model.bmm)
          (((a.getD 2 "").toNat?).getD 8)
    | "fig3"     =>
        let a := args.tail
        runFig3 (a.headD "Sabuncu4")
          (if a.getD 1 "bmm" == "dhnm" then Model.dhnm else Model.bmm)
          (((a.getD 2 "").toNat?).getD 1)
    | "fig9"     =>
        let a := args.tail
        let nats (str : String) : List Nat :=
          (str.splitOn ",").filterMap (fun t => t.toNat?)
        runFig9 (a.headD "Sabuncu4")
          (if a.getD 1 "bmm" == "dhnm" then Model.dhnm else Model.bmm)
          (((a.getD 2 "").toNat?).getD 5)
          (nats (a.getD 3 "5,10,30,40,50")) (nats (a.getD 4 "10,20,30,40,50"))
    | "table2"   =>
        let a := args.tail
        runTable2 (((a.getD 0 "").toNat?).getD 20) (a.getD 1 "")
    | "inner"    =>
        let a := args.tail
        let nat (i : Nat) (d : Nat) : Nat := ((a.getD i "").toNat?).getD d
        let flt (i : Nat) (d : Float) : Float :=
          match (a.getD i "").toNat? with | some v => Float.ofNat v / 100.0 | none => d
        runInner (a.headD "Sabuncu4")
          (if a.getD 1 "bmm" == "dhnm" then Model.dhnm else Model.bmm)
          { innerIters := nat 2 30, T0 := flt 3 10.0, eta := flt 4 0.9 } (nat 5 1)
    | "trace"    =>
        let a := args.tail
        let nat (i : Nat) (d : Nat) : Nat := ((a.getD i "").toNat?).getD d
        let flt (i : Nat) (d : Float) : Float :=
          match (a.getD i "").toNat? with | some v => Float.ofNat v / 100.0 | none => d
        runTrace (a.headD "Sabuncu4")
          (if a.getD 1 "bmm" == "dhnm" then Model.dhnm else Model.bmm)
          { N := nat 2 50, M := nat 3 50,
            model := ModelConfig.tabulate
              { innerIters := nat 4 30, T0 := flt 5 2.0, eta := flt 6 0.9 } }
          (nat 7 1)
    | "solve"    =>
        -- solve <instance> <dhnm|bmm> <N> <M> <inner> <T0> <eta> <runs>
        let a := args.tail
        let nm := a.headD "Sabuncu4"
        let mdl := if a.getD 1 "bmm" == "dhnm" then Model.dhnm else Model.bmm
        let nat (i : Nat) (d : Nat) : Nat := ((a.getD i "").toNat?).getD d
        let flt (i : Nat) (d : Float) : Float :=
          match (a.getD i "").toNat? with | some v => Float.ofNat v / 100.0 | none => d
        let mille (i : Nat) (d : Float) : Float :=
          match (a.getD i "").toNat? with
          | some v => Float.ofNat v / 1000.0
          | none   => d
        -- Defaults are the *recovered* configuration, with `N`/`M`/`inner`/`T0` taken from the
        -- instance's Table II row when it has one. These previously hard-coded the
        -- pre-correction values, so `cns solve <instance>` failed out of the box.
        let row := table2Rows.find? (fun r => r.name == nm)
        let dInner := (row.map (·.inner)).getD 30
        let dT0 := (row.map (·.T0)).getD 3.0
        let dN := (row.map (fun r => if mdl == Model.dhnm then r.nDhnm else r.nBmm)).getD 50
        let dM := (row.map (·.M)).getD 50
        let dTau := if mdl == Model.dhnm then 0.9 else 0.4
        runSolve nm mdl
          { N := nat 2 dN, M := nat 3 dM,
            Pm := mille 8 0.05, divThreshold := mille 9 dTau,
            c0 := flt 11 0.5, c1 := flt 12 2.0, c2 := flt 13 0.25,
            model := ModelConfig.tabulate
              { innerIters := nat 4 dInner, T0 := flt 5 dT0, eta := flt 6 0.9,
                annealOuter := nat 10 0 == 1, sequential := nat 14 0 == 1 } }
          (nat 7 1) 1
    | "complete" =>
        -- complete [instance|all] [attempts] [N] [M] [inner] [T0*100] [eta*100]
        let a := args.tail
        let nat (i : Nat) (d : Nat) : Nat := ((a.getD i "").toNat?).getD d
        let flt (i : Nat) (d : Float) : Float :=
          match (a.getD i "").toNat? with | some v => Float.ofNat v / 100.0 | none => d
        let nm := a.headD "all"
        runComplete (if nm == "all" then none else some nm) (nat 1 24)
          { N := nat 2 50, M := nat 3 100,
            model := ModelConfig.tabulate
              { innerIters := nat 4 80, T0 := flt 5 5.0, eta := flt 6 0.95 } }
    | "hard"     =>
        -- hard [count] [minDim] [seed] [dhnm|bmm] [restarts]
        let a := args.tail
        let nat (i : Nat) (d : Nat) : Nat := ((a.getD i "").toNat?).getD d
        runHard (nat 0 10) (nat 1 300) (nat 2 0)
          (if a.getD 3 "bmm" == "dhnm" then Model.dhnm else Model.bmm) (nat 4 4)
    | "prototype" =>
        -- prototype "<81 chars>" [dhnm|bmm] [restarts]
        let a := args.tail
        runPrototype (a.headD "")
          (if a.getD 1 "bmm" == "dhnm" then Model.dhnm else Model.bmm)
          (((a.getD 2 "").toNat?).getD 4)
    | "all"      => do
        let a ← runTable1
        IO.println ""
        IO.println (String.pushn "" '-' 72)
        IO.println ""
        let b ← runEncoding
        pure (a && b)
    | other      => do
        IO.println s!"unknown subcommand '{other}'; expected one of: \
          table1, encoding, reduced, table2, complete, count, figs, puzzle, solve, trace, inner, fig3, fig9, bench, hard, prototype, all"
        pure false
  return (if ok then 0 else 1)
