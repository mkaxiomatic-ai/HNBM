# HNBM — Hopfield networks and Boltzmann machines in Lean 4

A Lean 4 formalization of Hopfield networks, Boltzmann machines, Markov-chain Monte Carlo and
Perron–Frobenius theory, together with `HopfieldNet/CNS/`: a formalized and executable
reproduction of Li & Wang, *Collaborative Neurodynamic Algorithms for Solving Sudoku Puzzles*
(ICIST 2022).

## Building

Lean **v4.30.0** and Mathlib **v4.30.0** (both pinned in `lean-toolchain` and `lakefile.lean`).
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

| Theorem | Statement |
|---|---|
| `reduce_completions` | Algorithm 1 preserves the solution set exactly, so Table I counts variables safely deleted rather than solutions discarded |
| `penalty_zero_iff_families` | `p(x) = 0` iff each cell holds one digit and each digit occurs once per row, column and block — constraints (10a)–(10d) |
| `penalty_encode_eq_zero` | a solved grid encodes to zero penalty |
| `Spec.quboParams` | the QUBO is an instance of the repository's `TwoState.ZeroOne` network, with `pm` (symmetry and zero diagonal) discharged |

Verified executably but **not** proved: the reduced-objective bridge
`Problem.penaltyDoubled P x = CNS.penaltyDoubled (P.embed x)` (1000 random trials per instance,
re-checked by `cns reduced`), and the converse `p(x) = 0 → isSolution` (exercised by the
certificate check on every solve).

Not formalized: the paper's three theoretical claims about convergence. For the *momentum*
variants of eqs (3) and (6) the corresponding theory does not exist in the literature — the
classical results (Goles–Chacc for synchronous threshold networks, Little–Peretto for the
parallel Boltzmann machine) do not apply to an undamped accumulator.

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
