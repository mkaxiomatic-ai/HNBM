/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.CNS.Dynamics

/-!
# Algorithm 2: the collaborative neurodynamic search

A population of `N` neurodynamic models (DHNm or BMm) is run to equilibrium in parallel; the
best state found re-seeds the population through a particle-swarm rule (7); a diversity measure
(8) triggers bit-flip mutation (9) when the swarm collapses. Termination is `M` consecutive
outer iterations without improving the incumbent.

## Under-specifications

Li & Wang give no numerical value anywhere for `T₀`, `η`, the inner-iteration count, the
mutation probability `P_m`, the diversity threshold `𝒯`, or the PSO constants `c₀, c₁, c₂`.
They are exposed here as `SearchConfig` and recovered empirically. The recovered values, and
what governs each:

| parameter | value | notes |
|---|---|---|
| `c₀` | `0.5` | flat over `0.3`-`0.7` |
| `c₁` | `2.0` | see `c2`; the balance is what matters, not the magnitudes |
| `c₂` | `0.25` | **decisive**; at `c₁ = c₂` the swarm collapses onto the incumbent |
| `P_m` | `0.05` | flat over `0.02`-`0.2` |
| `𝒯` | `0.4` (BMm), `0.9` (DHNm) | as a fraction of `δ_max = 1/√n`; the model split is principled, see `c2` and `divThreshold` |
| `η` | `0.9` | flat over `0.85`-`0.95` |
| `innerIters` | `≈ nvars / 3` | 95→30, 163/168→80, 171→60, 209→100; tracks size, as the paper's own Fig. 2 implies |
| `T₀` | per instance, `3`-`8` | does *not* reduce to a size rule; see `Main.Row.T0` |

Two of these were not tuning but bug-fixing, and both are documented at their fields: `c₂`
(swarm collapse) and `𝒯` (which had to be made scale-free, since eq. (8)'s `δ` has maximum
`1/√n` and a fixed threshold therefore means something different on every instance).

A third correction lives in `ModelConfig.sequential`: the neuron update is synchronous, per the
paper, and switching it to asynchronous costs the DHNm badly (6/10 against 10/10 on Sabuncu3).

Two further choices the paper leaves open, resolved as follows and flagged rather than hidden:

* **What the mutation acts on.** Step 23 says only "perform the bit-flip mutation according to
  Eq. (9)". It is applied here to the freshly re-initialised seeds `x⁽ⁱ⁾(0)`, leaving the
  incumbent `x*` untouched — mutating the incumbent would forfeit the best solution found.
* **What the diversity is measured over.** Equation (8) writes `x⁽ⁱ⁾` for "the i-th particle".
  The personal bests are used, matching step 5 where `x⁽ⁱ⁾` is updated.

Note that (8) uses `‖·‖₂` *unsquared*, so for binary vectors each term is `√(Hamming)`.

## Deviation in step 16

Step 16 reads `v⁽ⁱ⁾ = c₀v⁽ⁱ⁾ + c₁U(0,1)(x⁽ⁱ⁾ − x̄⁽ⁱ⁾) + c₂U(0,1)(x* − x̄⁽ⁱ⁾)`, which is eq. (7)
with the current position taken to be the just-computed equilibrium `x̄⁽ⁱ⁾` and `x⁽ⁱ⁾` read as
the personal best. That reading is used here.
-/

namespace CNS

open QUBO
open QUBO.Problem

/-- Hyperparameters of Algorithm 2. -/
structure SearchConfig where
  /-- Population size `N`. -/
  N : Nat := 40
  /-- Termination criterion `M`: consecutive non-improving outer iterations. -/
  M : Nat := 50
  /-- Per-model settings. -/
  model : ModelConfig := {}
  /-- Inertia weight `c₀`. -/
  c0 : Float := 0.5
  /-- Cognitive learning factor `c₁`. Recovered empirically; see the note on `c₂`. -/
  c1 : Float := 2.0
  /-- Social learning factor `c₂`.

  **This is the parameter that decides whether the search works**, and the paper gives no value
  for it. With `c₂` comparable to `c₁` the social term drags every particle onto the incumbent;
  when the incumbent sits on a plateau -- which on these instances it does almost immediately --
  the whole swarm collapses onto it and never leaves. Success on Sabuncu4 at `N=50, M=50` goes
  from ~55% at `c₁=c₂=1` to ~87% at `c₁=2, c₂=0.25`, and the runs also get faster (21 vs 36
  outer iterations). It also explains why success was *non-monotonic* in `N` before: with a
  strong social pull, extra particles are just extra copies of the same stuck point. -/
  c2 : Float := 0.25
  /-- Bit-flip mutation probability `P_m` of eq. (9). -/
  Pm : Float := 0.05
  /-- Diversity threshold `𝒯` of step 22, as a **fraction of the maximum attainable
  diversity** rather than an absolute value.

  Eq. (8) defines `δ = (1/(Nn)) Σ ‖x⁽ⁱ⁾ − x*‖₂`, whose maximum is `√n/n = 1/√n`, so a fixed
  `𝒯` means something different on every instance: `δ_max` is 0.103 at `n = 95` but 0.077 at
  `n = 171`, and the same `𝒯` therefore fires mutation far more readily on the larger problem.
  On Sabuncu3 an absolute `𝒯 = 0.05` mutates on literally every iteration and success collapses
  to 7/20, against 18/20 at `𝒯 = 0.03`.

  The effective threshold used is `divThreshold / √n`, so this is a scale-free number in
  `[0,1]`. `𝒯` is never given numerically in the paper, so this only fixes what the paper
  leaves open; eq. (8) itself is unchanged. -/
  divThreshold : Float := 0.4
  /-- Apply the bit-flip mutation of step 23 to the personal bests `x⁽ⁱ⁾` as well as to the
  seeds `x⁽ⁱ⁾(0)`.

  Step 23 says only "perform the bit-flip mutation according to Eq. (9)" without naming a
  target. Eq. (8) calls `x⁽ⁱ⁾` "the i-th particle", so the `x_j` of eq. (9) most naturally
  refers to the same vector the diversity is measured over — the personal bests.

  Measured effect on Sabuncu4: none (11/20 with, 12/20 without). The personal-best ratchet is
  real -- `pbestE` only ever decreases -- but releasing it is not what unsticks the swarm; the
  `c₁`/`c₂` balance is (see the note on `c2`). Kept as an option, defaulted on, because it is
  the reading most consistent with eq. (8). The incumbent `x*` is never mutated. -/
  mutatePbest : Bool := false
  /-- Hard cap on outer iterations, so a run always terminates. -/
  maxOuter : Nat := 1000000
  /-- Draw the initial states `x⁽ⁱ⁾(0)` one-hot per open cell rather than as uniform bits.

  The paper says only `x⁽ⁱ⁾(0) ∈ {0,1}^{n²}`. Uniform bits set about half the variables, whereas
  a feasible point sets exactly one per open cell, so a uniformly-seeded run spends its whole
  anneal just reaching one-digit-per-cell and lands somewhere essentially arbitrary. Seeding
  one-hot starts every model on the feasible manifold of the cell constraints (11a), leaving the
  dynamics to work on the row, column and block constraints. -/
  oneHotInit : Bool := false
  /-- Record a per-outer-iteration trace into `SearchResult.trace`. -/
  trace : Bool := false
  /-- Record the incumbent `x*` at every outer iteration into `SearchResult.boards`, for
  animation. Off by default: each frame is a full copy of `x*`. -/
  captureBoards : Bool := false
  deriving Inhabited

/-- Outcome of one run of Algorithm 2. -/
structure SearchResult where
  /-- Best assignment found. -/
  best : Array Bool
  /-- `‖Âx̂ − b̂‖²` of `best`, i.e. twice `p(x*)`. Zero iff the puzzle was solved. -/
  penaltyDoubled : Int
  /-- Outer iterations executed. -/
  outer : Nat
  /-- Whether `p(x*) = 0` was reached. -/
  solved : Bool
  /-- Per-outer-iteration diagnostics when `SearchConfig.trace` is set:
  `(outer, starE, bestParticleE, meanParticleE, diversity, mutated, distinctPbest)`. -/
  trace : Array (Nat × Int × Int × Int × Float × Bool × Nat) := #[]
  /-- The incumbent `x*` after each outer iteration, when `SearchConfig.captureBoards` is set.
  Frame `0` is the incumbent chosen from the initial population, so `boards.size = outer + 1`
  on a run that is not cut short. -/
  boards : Array (Array Bool) := #[]
  /-- `p(x*)` doubled, one entry per frame of `boards`. -/
  boardsE : Array Int := #[]
  deriving Inhabited

/-- Round a clamped position coordinate to a bit, per steps 18-19. -/
@[inline] def roundBit (z : Float) : Bool :=
  let c := if z < 0.0 then 0.0 else if z > 1.0 then 1.0 else z
  c ≥ 0.5

/-- Diversity of the swarm, eq. (8): `δ = (1/(Nn)) Σ_i ‖x⁽ⁱ⁾ − x*‖₂`. -/
def diversity (pop : Array (Array Bool)) (star : Array Bool) (nvars : Nat) : Float :=
  if pop.size == 0 || nvars == 0 then 0.0
  else
    let total := pop.foldl (fun acc p =>
      let ham := (Array.range nvars).foldl (fun a i =>
        if p.getD i false != star.getD i false then a + 1 else a) 0
      acc + Float.sqrt (Float.ofNat ham)) 0.0
    total / (Float.ofNat pop.size * Float.ofNat nvars)

/-- Algorithm 2. Returns the incumbent together with its objective value. -/
def search (P : Problem) (m : Model) (cfg : SearchConfig) (g0 : Rng) : SearchResult := Id.run do
  let nv := P.nvars
  let mut g := g0
  -- initial states x⁽ⁱ⁾(0) and velocities v⁽ⁱ⁾ ∈ [−1,1]^n
  let mut pos : Array (Array Float) := Array.replicate cfg.N #[]
  let mut vel : Array (Array Float) := Array.replicate cfg.N #[]
  let mut pbest : Array (Array Bool) := Array.replicate cfg.N #[]
  let mut pbestE : Array Int := Array.replicate cfg.N 0
  let groups := P.openCellGroups
  for i in [0:cfg.N] do
    let mut bs : Array Bool := Array.replicate nv false
    if cfg.oneHotInit then
      for grp in groups do
        let (k, g') := g.nextBelow grp.size
        g := g'
        bs := bs.set! (grp.getD k 0) true
    else
      let (rnd, g') := g.bits nv
      g := g'
      bs := rnd
    pos := pos.set! i (bs.map (fun b => if b then 1.0 else 0.0))
    let mut v : Array Float := Array.replicate nv 0.0
    for j in [0:nv] do
      let (r, g'') := g.nextFloat
      g := g''
      v := v.set! j (2.0 * r - 1.0)
    vel := vel.set! i v
    pbest := pbest.set! i bs
    pbestE := pbestE.set! i (P.penaltyDoubled bs)
  -- incumbent
  let mut star := pbest.getD 0 #[]
  let mut starE := pbestE.getD 0 0
  for i in [0:cfg.N] do
    if pbestE.getD i 0 < starE then
      starE := pbestE.getD i 0
      star := pbest.getD i #[]
  let mut stall := 0
  let mut outer := 0
  let mut tr : Array (Nat × Int × Int × Int × Float × Bool × Nat) := #[]
  let mut boards : Array (Array Bool) := if cfg.captureBoards then #[star] else #[]
  let mut boardsE : Array Int := if cfg.captureBoards then #[starE] else #[]
  while stall ≤ cfg.M && outer < cfg.maxOuter && starE != 0 do
    outer := outer + 1
    -- steps 2-7: run the population to equilibrium
    let mut equil : Array (Array Bool) := Array.replicate cfg.N #[]
    for i in [0:cfg.N] do
      let seed := (pos.getD i #[]).map roundBit
      let (xb, g') := m.run P cfg.model (outer - 1) g seed
      g := g'
      equil := equil.set! i xb
      let e := P.penaltyDoubled xb
      if e < pbestE.getD i 0 then
        pbestE := pbestE.set! i e
        pbest := pbest.set! i xb
    -- steps 8-14: update the incumbent
    let mut bi := 0
    for i in [0:cfg.N] do
      if pbestE.getD i 0 < pbestE.getD bi 0 then bi := i
    if pbestE.getD bi 0 < starE then
      starE := pbestE.getD bi 0
      star := pbest.getD bi #[]
      stall := 0
    else
      stall := stall + 1
    if cfg.captureBoards then
      boards := boards.push star
      boardsE := boardsE.push starE
    if starE == 0 then
      break
    -- steps 15-20: particle-swarm re-initialisation
    for i in [0:cfg.N] do
      let (r1, ga) := g.nextFloat
      let (r2, gb) := ga.nextFloat
      g := gb
      let vi := vel.getD i #[]
      let pb := pbest.getD i #[]
      let eq := equil.getD i #[]
      let pi := pos.getD i #[]
      let mut v' : Array Float := Array.replicate nv 0.0
      let mut p' : Array Float := Array.replicate nv 0.0
      for j in [0:nv] do
        let bpb := if pb.getD j false then 1.0 else 0.0
        let beq := if eq.getD j false then 1.0 else 0.0
        let bst := if star.getD j false then 1.0 else 0.0
        let nv' := cfg.c0 * vi.getD j 0.0
          + cfg.c1 * r1 * (bpb - beq)
          + cfg.c2 * r2 * (bst - beq)
        v' := v'.set! j nv'
        p' := p'.set! j (if roundBit (pi.getD j 0.0 + nv') then 1.0 else 0.0)
      vel := vel.set! i v'
      pos := pos.set! i p'
    -- steps 21-24: diversity-triggered bit-flip mutation
    let δ := diversity pbest star nv
    -- compare against a fraction of δ_max = 1/√n (see `divThreshold`)
    let mutated := δ * Float.sqrt (Float.ofNat nv) < cfg.divThreshold
    if mutated then
      for i in [0:cfg.N] do
        let pi := pos.getD i #[]
        let mut p' := pi
        for j in [0:nv] do
          let (κ, g') := g.nextFloat
          g := g'
          if κ ≤ cfg.Pm then
            p' := p'.set! j (if pi.getD j 0.0 ≥ 0.5 then 0.0 else 1.0)
        pos := pos.set! i p'
        if cfg.mutatePbest then
          -- release the personal-best ratchet, so the swarm can leave a plateau
          let pb := pbest.getD i #[]
          let mut q := pb
          for j in [0:nv] do
            let (κ, g') := g.nextFloat
            g := g'
            if κ ≤ cfg.Pm then
              q := q.set! j (!(pb.getD j false))
          pbest := pbest.set! i q
          pbestE := pbestE.set! i (P.penaltyDoubled q)
    if cfg.trace then
      let mut bE : Int := 1000000
      let mut sumE : Int := 0
      let mut distinct : Array (Array Bool) := #[]
      for i in [0:cfg.N] do
        let e := pbestE.getD i 0
        if e < bE then bE := e
        sumE := sumE + e
        let pb := pbest.getD i #[]
        if !distinct.any (fun q => q == pb) then distinct := distinct.push pb
      tr := tr.push (outer, starE, bE, sumE / (cfg.N : Int), δ, mutated, distinct.size)
  return { best := star, penaltyDoubled := starE, outer := outer, solved := starE == 0,
           trace := tr, boards := boards, boardsE := boardsE }

end CNS
