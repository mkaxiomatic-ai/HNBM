/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.QUBO.Problem
import HopfieldNet.QUBO.Prng

/-!
# DHNm and BMm: the two neurodynamic models

Equation (3), a discrete Hopfield network with a momentum term:

  `u(t+1) = u(t) + W x(t) − θ`,   `x(t) = σ(u(t))`,   `u(0) = 0`,

with `σ(u) = 1` if `u > 0` and `0` if `u ≤ 0` (eq. 2). Equation (6) replaces the threshold by a
stochastic acceptance,

  `p(x_i(t) = 1) = 1 / (1 + exp(−u_i(t)/T))`,   `T = T₀ ηᵗ`.

The paper says the models are "activated synchronously" and "operated in fully parallel", but
that sentence is about the *population* of networks, so the neuron-level update is ambiguous.
Both readings are implemented and selected by `ModelConfig.sequential`. Measured on Sabuncu4
they perform the same (synchronous 11/20, asynchronous 7-10/20 at `N=50, M=50`), so the choice
is not what governs success. It does govern which theory applies: every convergence, Lyapunov
and detailed-balance result in HNBM is stated for the single-site `NeuralNetwork.State.Up`, so
only the asynchronous reading can inherit them.

## Two under-specifications, and what is done about them

*Initial state.* Equation (3) fixes `u(0) = 0`, which with `x(t) = σ(u(t))` would force
`x(0) = 0` and make Algorithm 2's per-particle initial states `x⁽ⁱ⁾(0)` inert. The reading taken
here keeps both: `u(0) = 0` and `x(0)` is the supplied seed, so the first update is
`u(1) = W x(0) − θ`. This is the only reading under which Algorithm 2's PSO re-initialisation
does anything.

*Equilibrium.* Step 3 of Algorithm 2 asks for "the equilibrium state" of a BMm without defining
one, and no inner-iteration count is given anywhere in the paper. Fig. 2 shows the transients
settling within roughly 30 inner iterations (about 100 for Sabuncu6), so the count is exposed as
`Config.innerIters` and defaulted accordingly.

`T₀`, `η`, and the inner count are likewise never stated numerically; they are recovered
empirically. See `HopfieldNet.CNS.Search`.

## Arithmetic

`W`, `θ` and `x` are integral, so the DHNm is **exact integer arithmetic** — no floating point
anywhere on that path. Only the BMm's logistic needs `Float`, and only to compare against a
uniform draw.
-/

namespace QUBO


/-! ## Fixed-point logistic

Measured on this toolchain (`cns bench`, 10M iterations): `Int` addition costs 1.7 ns and an
`Array Int` store 2.1 ns, but a bare `Float` addition costs **580 ns** — every intermediate is
heap-boxed. `Float.exp` costs 573 ns, i.e. the same, so the expense is the boxing rather than
the transcendental. Any `Float` in the inner loop therefore dominates everything else.

It can be removed entirely. The acceptance probability `1/(1 + exp(−u/T))` depends on just two
things: the integer `u`, and the inner-iteration index `t` (since `T = T₀ηᵗ` takes only
`innerIters` values). Tabulating it once per configuration as 53-bit fixed-point thresholds
turns the inner test into a single `UInt64` comparison against the raw generator output, and the
whole BMm sweep becomes integer arithmetic.

The table holds `⌊2⁵³ · p⌋`, compared against the top 53 bits of a `splitmix64` draw — the same
quantity `Rng.nextFloat` would have produced, so the accept/reject decision is unchanged except
for the final ulp. Values of `|u|` beyond `uMax` fall back to the `Float` path; that is rare and
keeps the tabulation from having to bound `u` a priori. -/

/-- Largest `|u|` covered by the fixed-point logistic table. -/
def uMax : Nat := 2048

/-- Width of one temperature row of the table. -/
def uSpan : Nat := 2 * uMax + 1

/-- Hyperparameters of a single neurodynamic run. -/
structure ModelConfig where
  /-- Inner iterations before the state is read off as an "equilibrium". -/
  innerIters : Nat := 30
  /-- Initial temperature `T₀` of the annealing schedule (BMm only). -/
  T0 : Float := 2.0
  /-- Cooling factor `0 < η < 1` (BMm only). -/
  eta : Float := 0.9
  /-- Fixed-point logistic thresholds `⌊2⁵³/(1 + exp(−u/T_t))⌋`, flattened as
  `t * uSpan + (u + uMax)`. Empty means "evaluate in `Float`". -/
  sigTable : Array UInt64 := #[]
  /-- Return the best state visited rather than the final equilibrium.

  **Off by default, because it is unfaithful and actively harmful.** Step 3 of Algorithm 2 asks
  for "the equilibrium state `x̄⁽ⁱ⁾`", and the PSO rule (step 16) drives the swarm through
  `(x⁽ⁱ⁾ − x̄⁽ⁱ⁾)` and `(x* − x̄⁽ⁱ⁾)`. Substituting the best-visited state makes `x̄⁽ⁱ⁾`
  coincide with `x*` once the swarm converges, so both differences vanish, the velocity decays
  to zero, and the seeds freeze — the search collapses into "`x*` plus a few mutated bits" and
  stops exploring. Returning the true stochastic endpoint keeps those terms alive. -/
  useBestVisited : Bool := false
  /-- Number of tabulated temperature levels. -/
  levels : Nat := 256
  /-- Anneal `T = T0*eta^t` on the **outer** index rather than the inner one.

  Eq. (5) calls `T(t)` the temperature "at iteration t" of the Boltzmann machine's own update,
  which reads as the inner index -- that is the default. But under that reading every BMm run
  re-heats to `T0` and cools identically, so Algorithm 2 has no global annealing and no way to
  search harder when the swarm is stuck on a plateau. Under the outer reading `T` is constant
  within a run and cools across Algorithm 2. Both are tested. -/
  annealOuter : Bool := false
  /-- Update neurons **asynchronously** (sequential scan) instead of synchronously.

  The paper says the models are "activated synchronously" and "operated in fully parallel", but
  that sentence is about the *population* of networks, not the neurons inside one. Under the
  asynchronous reading each neuron sees the neurons already updated in the same sweep, which is
  ordinary Gibbs sampling -- and is what every convergence, Lyapunov and detailed-balance result
  in HNBM assumes (they are all stated for the single-site `NeuralNetwork.State.Up`).

  Cost is unchanged: flipping `x_u` touches only the four rows containing `u`, so the row sums
  are maintained incrementally in `O(1)` per neuron.

  **Off by default, but the reason is speed, not reliability.**

  The asynchronous reading is the one that *is* an HNBM network: `CNS.Refine.netVec_eq_localField`
  shows the net input is `ZeroOne`'s local field, so the single-site sweep is a `State.Up`
  sequence and inherits the detailed-balance and ergodicity results of
  `HopfieldNet.Quiver.BM`. `CNS.Minimizers` then says the objective it descends has the solved
  grids as its exact minimisers, with an energy gap of at least `1/2`.

  Its cost is that it needs a slower annealing schedule. The paper's `inner = 60, η = 0.9` drops
  `T` by a factor of 600 in 60 sweeps, which is far too fast for a single-site sampler; under it
  the asynchronous BMm solves 5/6 on Sabuncu3 where the synchronous one solves 6/6. Measured
  over six seeds on Sabuncu3 (BMm, `N = 40`, `M = 50`):

  | configuration | solved | ms/run |
  |---|---|---|
  | synchronous, `inner = 60`, `η = 0.9` | 6/6 | 721 |
  | asynchronous, `inner = 60`, `η = 0.9` | 5/6 | 1923 |
  | asynchronous, `inner = 200`, `η = 0.97` | **6/6** | 2340 |
  | asynchronous, `inner = 300`, `T₀ = 2`, `η = 0.98` | **6/6** | 2240 |
  | asynchronous, `inner = 100`, `η = 0.94` | 4/6 | 1981 |
  | asynchronous, `inner = 120`, `η = 0.95`, `N = 20` | 4/6 | 1263 |

  So slowing the schedule closes the *reliability* gap exactly, and nothing tried closes the
  ~3x *wall-clock* gap: cutting sweeps or shrinking the swarm loses runs immediately. That is
  the expected shape of the trade. The momentum term of eq. (3) is precisely the device Takefuji
  and Lee introduced to tame the oscillation a synchronous update would otherwise suffer, so
  discarding synchrony discards the reason the momentum is there, and the sweeps have to be paid
  for instead.

  The choice is therefore explicit rather than hidden: `sequential := false` is faster,
  `sequential := true` with `inner ≈ 200, η ≈ 0.97` is equally reliable and is the variant the
  theory covers. -/
  sequential : Bool := false
  deriving Inhabited

/-- Build the fixed-point logistic table for a configuration. Costs `innerIters * uSpan`
`Float.exp` evaluations once, replacing millions in the inner loop. -/
def mkSigTable (levels : Nat) (T0 eta : Float) : Array UInt64 := Id.run do
  let scale := 9007199254740992.0  -- 2^53
  let mut tbl : Array UInt64 := Array.replicate (levels * uSpan) 0
  let mut T := T0
  for t in [0:levels] do
    for j in [0:uSpan] do
      let u := Float.ofNat j - Float.ofNat uMax
      let p := 1.0 / (1.0 + Float.exp (-u / T))
      tbl := tbl.set! (t * uSpan + j) (Float.toUInt64 (p * scale))
    T := T * eta
  return tbl

/-- Attach the precomputed logistic table to a configuration. -/
def ModelConfig.tabulate (cfg : ModelConfig) : ModelConfig :=
  { cfg with sigTable := mkSigTable cfg.levels cfg.T0 cfg.eta }

/-- The activation `σ` of eq. (2): `1` if the net input is strictly positive, else `0`. -/
@[inline] def sigma (u : Int) : Bool := u > 0

/-- One synchronous DHNm sweep: `u ← u + (Wx − θ)`, then `x ← σ(u)`. -/
@[inline] def dhnmStep (P : Problem) (u : Array Int) (x : Array Bool) :
    Array Int × Array Bool := Id.run do
  let net := P.netVec x
  let mut u' : Array Int := Array.replicate P.nvars 0
  let mut x' : Array Bool := Array.replicate P.nvars false
  for i in [0:P.nvars] do
    let ui := (u.getD i 0) + (net.getD i 0)
    u' := u'.set! i ui
    x' := x'.set! i (sigma ui)
  return (u', x')

/-- Run the DHNm of eq. (3) from a seed state, returning the best state visited.

The momentum recurrence is an undamped accumulator, so it need not converge; the paper's Fig. 2
shows it settling in practice. Tracking the best state visited makes the routine robust to the
2-cycles a synchronous update can fall into. -/
def dhnmRun (P : Problem) (cfg : ModelConfig) (x0 : Array Bool) : Array Bool := Id.run do
  let mut u : Array Int := Array.replicate P.nvars 0
  let mut x := x0
  let mut best := x0
  let mut bestE := P.penaltyDoubled x0
  for _ in [0:cfg.innerIters] do
    let (u', x') := dhnmStep P u x
    u := u'
    x := x'
    if cfg.useBestVisited then
      let e := P.penaltyDoubled x
      if e < bestE then
        bestE := e
        best := x
  return (if cfg.useBestVisited then best else x)

/-- One synchronous BMm sweep at temperature `T`: `u ← u + (Wx − θ)`, then each `x_i` is
resampled from the logistic of `u_i / T`. -/
@[inline] def bmmStep (P : Problem) (T : Float) (g : Rng) (u : Array Int) (x : Array Bool) :
    Array Int × Array Bool × Rng := Id.run do
  let net := P.netVec x
  let mut u' : Array Int := Array.replicate P.nvars 0
  let mut x' : Array Bool := Array.replicate P.nvars false
  let mut gg := g
  for i in [0:P.nvars] do
    let ui := (u.getD i 0) + (net.getD i 0)
    u' := u'.set! i ui
    let p := 1.0 / (1.0 + Float.exp (-(Float.ofInt ui) / T))
    let (r, g') := gg.nextFloat
    gg := g'
    x' := x'.set! i (r < p)
  return (u', x', gg)

/-- Run the BMm of eq. (6) with the geometric schedule `T = T₀ηᵗ`, returning the best state
visited.

`splitmix64` is inlined and its state kept in a raw `UInt64` local, rather than going through
`Rng.nextFloat`: the latter allocates both a tuple and an `Rng` structure per neuron per sweep.

A `FloatArray` variant of the whole numeric path was tried and is **20× slower** — `FloatArray`
has no bulk fill, so building one costs a `push` across the extern boundary per element, where
`Array.replicate` is a single allocation. Boxed `Array Int` wins here. -/
def bmmRun (P : Problem) (cfg : ModelConfig) (lvl0 : Nat) (g : Rng) (x0 : Array Bool) :
    Array Bool × Rng := Id.run do
  let mut u : Array Int := Array.replicate P.nvars 0
  let mut x := x0
  let mut st : UInt64 := g.s
  let mut best := x0
  let mut bestE := P.penaltyDoubled x0
  let tbl := cfg.sigTable
  let tabulated := tbl.size == cfg.levels * uSpan
  let mut T := cfg.T0
  for t in [0:cfg.innerIters] do
    let net := P.netVec x
    -- inner annealing walks down the levels; outer annealing pins to `lvl0`
    let lvl := if cfg.annealOuter then min lvl0 (cfg.levels - 1) else min t (cfg.levels - 1)
    let base := lvl * uSpan
    let mut u' : Array Int := Array.replicate P.nvars 0
    let mut x' : Array Bool := Array.replicate P.nvars false
    for i in [0:P.nvars] do
      let ui := (u.getD i 0) + (net.getD i 0)
      u' := u'.set! i ui
      -- splitmix64, inlined to keep the generator state in a scalar
      st := st + 0x9E3779B97F4A7C15
      let mut z := st
      z := (z ^^^ (z >>> 30)) * 0xBF58476D1CE4E5B9
      z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
      z := z ^^^ (z >>> 31)
      let draw := z >>> 11
      let j := ui + (uMax : Int)
      let acc :=
        if tabulated && 0 ≤ j && j < (uSpan : Int) then
          draw < tbl.getD (base + j.toNat) 0
        else
          -- fallback: |u| outside the tabulated window
          let r := Float.ofNat draw.toNat * (1.0 / 9007199254740992.0)
          r < 1.0 / (1.0 + Float.exp (-(Float.ofInt ui) / T))
      x' := x'.set! i acc
    u := u'
    x := x'
    T := T * cfg.eta
    if cfg.useBestVisited then
      let e := P.penaltyDoubled x
      if e < bestE then
        bestE := e
        best := x
  return (if cfg.useBestVisited then best else x, ⟨st⟩)

/-- Asynchronous (sequential-scan) sweep shared by both models.

`rho` holds the current row sums and is updated incrementally on each accepted flip. `stoch`
selects Boltzmann sampling (BMm) over the hard threshold (DHNm). -/
def seqRun (P : Problem) (cfg : ModelConfig) (stoch : Bool) (lvl0 : Nat) (g : Rng)
    (x0 : Array Bool) : Array Bool × Rng := Id.run do
  let tbl := cfg.sigTable
  let tabulated := tbl.size == cfg.levels * uSpan
  let mut rho := P.rowSums x0
  let mut u : Array Int := Array.replicate P.nvars 0
  let mut x := x0
  let mut st : UInt64 := g.s
  let mut T := cfg.T0
  for t in [0:cfg.innerIters] do
    let lvl := if cfg.annealOuter then min lvl0 (cfg.levels - 1) else min t (cfg.levels - 1)
    let base := lvl * uSpan
    for i in [0:P.nvars] do
      let rows := P.rowsOf.getD i #[]
      let mut sum : Int := 0
      for r in rows do
        sum := sum + rho.getD r 0
      let xi := x.getD i false
      let wx := (if xi then (rows.size : Int) else 0) - sum
      let ui := (u.getD i 0) + (wx - P.theta.getD i 0)
      u := u.set! i ui
      let mut nb : Bool := ui > 0
      if stoch then
        st := st + 0x9E3779B97F4A7C15
        let mut z := st
        z := (z ^^^ (z >>> 30)) * 0xBF58476D1CE4E5B9
        z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
        z := z ^^^ (z >>> 31)
        let draw := z >>> 11
        let j := ui + (uMax : Int)
        nb :=
          if tabulated && 0 ≤ j && j < (uSpan : Int) then
            draw < tbl.getD (base + j.toNat) 0
          else
            let r := Float.ofNat draw.toNat * (1.0 / 9007199254740992.0)
            r < 1.0 / (1.0 + Float.exp (-(Float.ofInt ui) / T))
      if nb != xi then
        x := x.set! i nb
        for r in rows do
          rho := rho.set! r ((rho.getD r 0) + (if nb then 1 else -1))
    T := T * cfg.eta
  return (x, ⟨st⟩)

/-- Which neurodynamic model a run uses. -/
inductive Model where
  /-- Discrete Hopfield network with momentum, eq. (3). -/
  | dhnm
  /-- Boltzmann machine with momentum, eq. (6). -/
  | bmm
  deriving Inhabited, Repr, BEq

/-- Name used in reports. -/
def Model.name : Model → String
  | .dhnm => "CNS/DHNm"
  | .bmm  => "CNS/BMm"

/-- Run whichever model is selected. -/
def Model.run (m : Model) (P : Problem) (cfg : ModelConfig) (lvl : Nat) (g : Rng)
    (x0 : Array Bool) : Array Bool × Rng :=
  match m with
  | .dhnm => if cfg.sequential then seqRun P cfg false lvl g x0 else (dhnmRun P cfg x0, g)
  | .bmm  => if cfg.sequential then seqRun P cfg true lvl g x0 else bmmRun P cfg lvl g x0

end QUBO
