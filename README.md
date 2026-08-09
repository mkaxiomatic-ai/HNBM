# HNBM — Hopfield networks and Boltzmann machines in Lean 4

A Lean 4 formalization of Hopfield networks, Boltzmann machines, Markov-chain Monte Carlo and
Perron–Frobenius theory, together with `HopfieldNet/CNS/`: a formalized and executable
reproduction of Li & Wang, *Collaborative Neurodynamic Algorithms for Solving Sudoku Puzzles*
(ICIST 2022).

## Building

Lean **v4.32.2** and Mathlib **v4.32.2** (both pinned in `lean-toolchain` and `lakefile.lean`).
Install via [elan](https://leanprover-community.github.io/get_started.html), then:

```bash
lake exe cache get     # Mathlib build cache — run this first; building Mathlib from source takes hours
lake build             # default target: the HopfieldNet library
```

Other targets: `lake build MCMC`, `lake build PF`, `lake build CNS`, `lake build CNSDemo`.

## Layout

| Target | Contents |
|---|---|
| `HopfieldNet` | neural-network core (`Quiver/NeuralNetwork`), Hopfield nets (`Quiver/HN`), Boltzmann machines (`Quiver/BM`), Boltzmann learning |
| `MCMC` | Markov kernels, Gibbs, Metropolis–Hastings, detailed balance, total variation, convergence |
| `PF` | Perron–Frobenius: irreducibility, primitivity, Collatz–Wielandt, uniqueness, spectrum |
| `CNS` | collaborative neurodynamic Sudoku — see below |
| `CNSDemo` | `#animate` infoview demos; not a default target, since the frames are computed during elaboration |

Known gap: `MCMC/Gibbs.lean` contains 22 `sorry`s and is not reachable from the default target.
Nothing else in the repository uses `sorry` or declares an `axiom`.

## `HopfieldNet/CNS` — collaborative neurodynamic Sudoku

Reproduces the paper's algorithms and results, and proves the parts that carry the meaning.

### Running

```bash
lake exe cns table1        # Algorithm 1 vs the paper's Table I
lake exe cns encoding      # structure of A, W, θ; p(x)=0 on every known solution
lake exe cns reduced       # net input vs finite differences; the reduced/unreduced bridge
lake exe cns table2 10     # Table II: both algorithms, every solution certificate-checked
lake exe cns complete all  # solve and verify all ten instances end to end
lake exe cns count         # solution counts, and the exact solver as a baseline
lake exe cns figs          # Figs 4-8: givens / after reduction with candidates / solved
lake exe cns puzzle "<81 chars>"   # your own puzzle: validate, reduce, search
lake exe cns hard 6 170 1  # generated hard corpus, certified solver, route breakdown
lake exe cns prototype "<81 chars>"   # solve one puzzle end to end, always certificate-checked
```

`solve`, `trace`, `inner`, `fig3`, `fig9` and `bench` expose individual experiments; run
`lake exe cns` with no argument for the list.

### What is reproduced

* **Table I** exactly on all ten Sabuncu instances, and it is now a *theorem* — see below.
* **Table II** with the paper's `N` and `M`: 7 of 10 cells at 10/10 with `best/worst = 0/0`;
  three at 9/10. Measured over 10 runs per cell, not the paper's 100.
* **Figs 2, 3 and 4–8**; solution counts (Sabuncu3 has 27 completions, so it is not a proper
  Sudoku); all ten instances solved end to end and certificate-checked.
* **Fig. 9 is not reproduced.** It is ten distinct 5×5 `(M,N)` grids at 100 repetitions —
  about 25,000 runs, on the order of weeks of single-core time.

### What is proved

Everything below is proved outright — no `sorry`, and `#print axioms` reports only
`propext`, `Classical.choice`, `Quot.sound`.

**The reduction and the encoding**

| Theorem | Statement |
|---|---|
| `reduce_completions` | Algorithm 1 preserves the solution set exactly, so Table I counts variables safely deleted rather than solutions discarded |
| `penalty_zero_iff_families` | `p(x) = 0` iff each cell holds one digit and each digit occurs once per row, column and block — constraints (10a)–(10d) |
| `penalty_encode_eq_zero` | a solved grid encodes to zero penalty |

**The network** — the search is not *modelled by* an HNBM network, it *is* one

| Theorem | Statement |
|---|---|
| `Problem.netParams` | the **reduced** QUBO — the instance the solver actually runs on — is a `TwoState.ZeroOne ℝ (Fin nvars)`, with `pm` (symmetry, zero diagonal) discharged structurally |
| `Problem.ofGrid_valid` | every instance the pipeline builds satisfies the structural invariants the above needs, so the bridge is unconditional rather than hypothetical |
| `Problem.zeroOneHamiltonian_eq` | HNBM's `{0,1}` Boltzmann Hamiltonian at those parameters **is** the paper's objective: `E(x̂) = ½‖Âx̂ − b̂‖² − ½‖b̂‖²` |
| `Problem.netVec_eq_localField` | the `O(nvars)` integer routine in the inner loop computes exactly `s.net − θ̂`, HNBM's local field — the object that runs is the object proved about |
| `Problem.rowSums_spec` | the row-sum scatter counts the set variables of each constraint row |
| `Problem.stateOfBits_stepAt` | one memoryless single-site update on the bit array **is** `NeuralNetwork.State.Up` |
| `Problem.stateOfBits_workPhase` | a scan over a list of neurons is the library's `workPhase` |
| `mem_varsOfRowSpec_iff` | `A` read by rows agrees with `A` read by columns — what `cns encoding` checked numerically as `specMatchesTable` |
| `Problem.penaltyDoubled_embed` | the reduced objective the search descends **is** the paper's `‖Ax − e‖²` under `embed` |

**The consequence** — minimising the HNBM energy *is* solving the puzzle

| Theorem | Statement |
|---|---|
| `Problem.energy_eq_min_iff` | a state attains the minimum energy exactly when its reduced penalty vanishes: the global minimisers are exactly the feasible assignments |
| `Problem.half_le_energy_sub_min` | the energy gap is at least `1/2` — the objective is integer-valued, so a miss is never by a small amount |
| `Problem.boltzmann_ratio_le` | an infeasible state's Boltzmann weight is suppressed by at least `exp(−1/2T)` relative to a feasible one, and that factor → 0 as `T` → 0 |

Together with `Ergodicity.RSrow_stationary_unique_eq_πBoltzVec` — the random-scan Gibbs chain has
a unique stationary distribution and it is the Boltzmann measure of this energy — that is the
sense in which the annealed Boltzmann machine concentrates on the solutions.

Verified executably but **not** proved: the converse `p(x) = 0 → isSolution` at grid level
(exercised by the certificate check on every solve; the variable-level direction is
`penalty_zero_iff_families`).

Not formalized: the paper's three theoretical claims about convergence. Those are about the
*momentum* recurrences of eqs (3) and (6), which are undamped accumulators, are not `Up` of any
HNBM network, and for which no theory exists — the classical results (Goles–Chacc for
synchronous threshold networks, Little–Peretto for the parallel Boltzmann machine) do not apply.
Everything proved above concerns the memoryless single-site reading. Note that
`Dynamics.seqRun` keeps the accumulator even in its asynchronous mode; `Problem.stepAt` is the
memoryless step the refinement theorems are about, and the distinction is stated at both.

### Synchronous or asynchronous: a measured trade

Only the asynchronous reading is an HNBM network, so only it inherits the theory. Six seeds on
Sabuncu3 (BMm, `N = 40`, `M = 50`):

| configuration | solved | ms/run |
|---|---|---|
| synchronous, `inner = 60`, `η = 0.9` (the paper's) | 6/6 | 721 |
| asynchronous, same schedule | 5/6 | 1923 |
| asynchronous, `inner = 200`, `η = 0.97` | 6/6 | 2340 |

Slowing the schedule closes the reliability gap exactly; nothing tried closes the ~3× wall-clock
gap, and cutting sweeps or swarm size loses runs immediately. That is the honest shape of it:
the covered-by-theory variant costs about 3× the time. Details at `ModelConfig.sequential`.

### A corpus hard enough to test the solver, and a solver that is never wrong

Four of the ten Sabuncu instances are closed by propagation alone, so "10/10" on that set says
little. `cns hard` generates proper puzzles from a seed — no external data — and reports which
stage solved each one. On six generated instances of post-reduction dimension 170–210:

```
solved by propagation alone   0/6
solved by the neurodynamics   4/6
needed the exact fallback     2/6
verified completions          6/6
```

`solveCertified` accepts a search result only if it passes `accepts` (`isSolution` together with
the givens), and falls back to the exact solver otherwise. So the neurodynamics changes how
often the fast path succeeds, never whether the answer is right. For calibration: the exact
solver finishes these in tens of milliseconds where the neurodynamic route takes 2–10 seconds.

### What the paper omits, and what we had to supply

The paper never writes down `W` or `θ`, and states no value for any hyperparameter. Derived and
verified here:

```
W = −(AᵀA − 4I)      θ = −2·𝟙      p(x) = −½xᵀWx + θᵀx + 162
```

with `A` of size `4n² × n³`, exactly four nonzeros per column and 28 neighbours per variable.
`W` is symmetric with zero diagonal, which is precisely what `TwoState.ZeroOne` requires.

Two recovered hyperparameters decide whether the method works at all, and both are documented at
their definitions in `Search.lean`: `c₂` (with `c₁ = c₂` the social term collapses the swarm onto
a stuck incumbent) and `𝒯` (eq. 8's diversity has maximum `1/√n`, so a fixed threshold means
something different on every instance).

Errata found in the paper are documented at the affected definitions: the index shift in eq. (12),
the missing `Σ_k` in (11b)–(11d), several index slips in Algorithm 1, the mislabelled
"# of solutions" column, the internally inconsistent Sabuncu7 CNS/DHNm row, and the Figs 4–8
middle boards not being at the reduction fixpoint.

### Build times

Everything under `CNS/` except `CNS.Spec` is deliberately Mathlib-free and rebuilds in seconds;
`lake exe cns` takes about two seconds from a touched source file. `CNS.Spec` is the single
module that imports Mathlib and `HopfieldNet.Quiver`, in order to exhibit the QUBO as an HNBM
network; it is slow to build and nothing in the executable pipeline depends on it.
