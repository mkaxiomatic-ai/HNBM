# A certified neurodynamic graph colourer

Draft material for an LPAR short paper. Every claim below names the Lean declaration that
supports it; anything without one is marked **TODO** and must not go in the paper until it does.

Status key: **✓** proved and axiom-clean (`propext`, `Classical.choice`, `Quot.sound` only);
**⧗** in progress; **TODO** not started.

---

## 1. The claim

A graph colourer built from a Hopfield/Boltzmann network, where the *encoding* is proved correct
in both directions and the *solver* is proved to be minimising the objective the encoding
defines. Not a faster colourer — a colourer whose answers are theorems.

Colouring by Hopfield network is old (Dahl 1987; Takefuji–Lee 1991) and on the graph sizes here a
greedy method wins outright. The contribution is that nothing in the chain is taken on trust:

```
proper colouring  ⟷  p(x) = 0  ⟷  minimiser of the HNBM energy  ←  what the code iterates
      ↑ §3                ↑ §4                    ↑ §4
```

The left equivalence makes the encoding faithful; the right one makes the network's energy *be*
the objective; the last arrow makes the theorems statements about the running program rather than
about an idealisation of it.

The left equivalence is `exists_zero_iff_colourable'`, and it carries **no** side condition —
not even a non-empty palette. The degenerate case is discharged rather than excluded: an empty
palette admits no vertex row, forcing `nverts = 0`, and `edgesOk` then forces no edges, so `#[]`
is a proper colouring. Worth a sentence in the paper, because "we assume a non-empty palette" is
the kind of hypothesis a reader assumes is hiding something.

## 2. What is actually proved

| Claim | Declaration | Status |
|---|---|---|
| The encoding is a well-formed 0/1 QUBO | `Colouring.problem_wf` | ✓ |
| …and refines the colouring incidence | `Colouring.problem_refines` | ✓ |
| Soundness: `p(x) = 0` → the decoded colouring is proper | `Colouring.decode_isColouring` | ✓ |
| Completeness: a proper colouring encodes to `p = 0` | `Colouring.encode_penalty_zero` | ✓ |
| Decision equivalence: `∃` zero ↔ `∃` proper colouring | `Colouring.exists_zero_iff_colourable'` | ✓ |
| K₄ is not 3-colourable (about the *graph*, not the QUBO) | `Colouring.k4_not_three_colourable` | ✓ |
| Same for exact cover: completeness, the iff, `ex2_no_cover` | `ExactCover.encode_penalty_zero`, `exists_zero_iff_coverable` | ✓ |
| The QUBO **is** an HNBM Boltzmann energy | `QUBO.Problem.zeroOneHamiltonian_eq` | ✓ |
| The running inner loop computes that network's local field | `QUBO.Problem.netVec_eq_localField` | ✓ |
| Global minimisers are exactly the feasible assignments | `QUBO.Problem.energy_eq_min_iff` | ✓ |
| The energy gap is ≥ ½ (the objective is integer-valued) | `QUBO.Problem.half_le_energy_sub_min` | ✓ |
| Infeasible states are Boltzmann-suppressed by `exp(−1/2T)` → 0 | `boltzmann_ratio_le`, `tendsto_suppression` | ✓ |
| Edge colouring, by reduction to the line graph | `EdgeColouring.isColouring_lineGraph` (`rfl`), `decode_isProperEdgeColouring` | ✓ |

The last row is worth a paragraph of its own: the reduction is arranged so that the two checkers
are *definitionally* equal, because `adjPairs` serves both as `L(G)`'s edge list and as what
`isProperEdgeColouring` quantifies over. Edge colouring therefore costs one file and inherits
soundness in two lines.

## 3. The encoding (§3 of the paper)

Lucas's Hamiltonian (Frontiers in Physics 2:5, 2014, §6.1) is

    H = A·Σ_v (1 − Σ_i x_{v,i})² + B·Σ_{(uv)∈E} Σ_i x_{u,i} x_{v,i}

The second term is a **bare product**, not a squared residual, so it is not of the canonical form
`‖Ax − b‖²` the library is stated against. One slack per (edge, colour) fixes that:

    x_{u,i} + x_{v,i} + s_{e,i} = 1

zero exactly when not both endpoints take colour `i`. Equivalent to Lucas §6.1, *not identical* —
say so explicitly, and give the variable count: `n(N + |E|)` against his `nN`.

Two honest notes for this section:

* the encoding writes every row twice, so column degrees come out even. That was forced by
  `theta : Array Int` storing `θ̂ = ½·deg(u) − Σ b̂`, which is a half-integer at odd degree. Since
  `theta` is now stored doubled (`QUBO.Problem.toyOdd` is the witness) the duplication is
  removable — **TODO**, and until then the reported row counts are 2× the natural ones;
* colour variables have degree `2(1 + deg_G(v))` and slacks degree `2`, so this instance exercises
  the degree-free algebra hard. Sudoku, at constant degree 4, never did.

## 4. The solver (§4)

`QUBO.search` is the collaborative neurodynamic scheme of Li & Wang (ICIST 2022) — a particle
swarm of Hopfield/Boltzmann networks — applied unchanged. Nothing in it is colouring-specific;
the only hook is `SearchConfig.groups`, the mutually exclusive variable groups used for one-hot
initialisation, which is a fact about the encoding rather than the QUBO.

The point to make: `netVec_eq_localField` is what stops this being a lookalike. The `O(nvars)`
integer routine in the inner loop is proved equal to the network's local field, so the descent
and concentration results in `QUBO.Minimizers` are about the code.

## 5. Results (§5)

Measured. `QUBO.search` with BMm, `N = M = 20`, `maxOuter = 60`, `inner = 40`, `T0 = 3.0`,
`η = 0.9`, one-hot initialisation, base seed 20260806. Baselines are first-fit greedy in index
order and DSATUR. `vars` is the QUBO's variable count at that palette.

| graph | n | \|E\| | χ | Δ+1 | greedy | DSATUR | vars@χ | neuro@χ | avg out | neuro@χ+1 |
|---|---|---|---|---|---|---|---|---|---|---|
| K3 | 3 | 3 | 3 | 3 | 3 | 3 | 18 | 10/10 | 1.0 | 10/10 |
| K4 | 4 | 6 | 4 | 4 | 4 | 4 | 40 | 10/10 | 1.0 | 10/10 |
| K5 | 5 | 10 | 5 | 5 | 5 | 5 | 75 | 10/10 | 1.3 | 10/10 |
| Path5 | 5 | 4 | 2 | 3 | 2 | 2 | 18 | 10/10 | 0.2 | 10/10 |
| C5 | 5 | 5 | 3 | 3 | 3 | 3 | 30 | 10/10 | 1.0 | 10/10 |
| C6 | 6 | 6 | 2 | 3 | 2 | 2 | 24 | 10/10 | 0.5 | 10/10 |
| C9 | 9 | 9 | 3 | 3 | 3 | 3 | 54 | 10/10 | 1.0 | 10/10 |
| K33 | 6 | 9 | 2 | 4 | 2 | 2 | 30 | 10/10 | 0.4 | 10/10 |
| Crown4 | 8 | 12 | 2 | 4 | **4** | 2 | 40 | 10/10 | 0.8 | 10/10 |
| Crown6 | 12 | 30 | 2 | 6 | **6** | 2 | 84 | 10/10 | 2.1 | 10/10 |
| Wheel6 | 7 | 12 | 3 | 7 | 3 | 3 | 57 | 10/10 | 1.7 | 10/10 |
| Cocktail8 | 8 | 24 | 4 | 7 | 4 | 4 | 128 | 9/10 | 8.1 | 10/10 |
| Petersen | 10 | 15 | 3 | 4 | 3 | 3 | 75 | 10/10 | 1.6 | 10/10 |
| Grötzsch | 11 | 20 | 4 | 6 | 4 | 4 | 124 | 10/10 | 2.3 | 10/10 |
| Myc3 | 23 | 71 | 5 | 12 | 5 | 5 | 470 | **0/3** | 36.7 | 3/3 |

A fourth column set, at palette χ−1 where the instance is provably infeasible: the search finds
no zero on any of the fifteen, terminating with residual penalty 2–12. That column is only
*meaningful* because of `exists_zero_iff_colourable'` — without completeness, "found no zero"
would say nothing about colourability.

### What the numbers say

**DSATUR wins outright.** It attains χ on all fifteen instances, in microseconds. Greedy attains
it on thirteen, losing exactly where it is known to — the crown graphs, bipartite but adversarially
ordered, where first-fit is dragged to the full Δ+1 (4 and 6 against an optimum of 2). The
neurodynamics attains χ on fourteen of fifteen and misses the largest: on M(Grötzsch), 470 binary
variables, it finds nothing at palette 5 in three seeds, though it succeeds at 6.

So the paper cannot claim a performance result, and should not try. What it can claim is that this
is a colourer whose answers are theorems in both directions, on a corpus where the reference values
are independently checked. Presented honestly, "a certified solver that is competitive with
DSATUR on 14 of 15 instances and slower by orders of magnitude" is a defensible short-paper
result; presented as a speed claim it would be indefensible.

### Provenance of the reference values

The χ column is not cited — it was computed independently, by a backtracking exact colouring
search written separately from the Lean development, and cross-checked against the claimed values.
The same check confirmed every graph is simple with no duplicate edges, and that Grötzsch (11
vertices, 20 edges) and M(Grötzsch) (23 vertices, 71 edges) are genuinely triangle-free. The
greedy and DSATUR columns and Δ+1 were likewise recomputed independently and agree on every row.

The two neurodynamics columns are the only numbers with a single implementation behind them; they
are observations of a stochastic heuristic, and the seed and configuration are given above so they
can be reproduced.

### Instances verified end to end elsewhere

| instance | palette | result |
|---|---|---|
| K₃ edge colouring | 3 | solved, `[2,1,0]` |
| P₄ edge colouring | 2 | solved, `[1,0,1]` |
| K₃ edge colouring | 2 | no zero — correct, χ′(K₃) = 3 |

## 6. The artifact (§6)

`#colour g` and `#edgecolour g` animate a run in the Lean infoview: one frame per outer
iteration, vertices filled by colour, monochromatic edges highlighted. `#cover` shows the
exact-cover sibling as an incidence matrix with per-row coverage in the margin, which is the
residual the objective squares.

Keep this short. The widgets make the artifact evaluable; they are not a contribution.

## 7. What we do not claim

State these plainly rather than letting a referee find them:

* no performance claim — see §5;
* the search is a heuristic. Nothing proves it *finds* a zero when one exists; the proved content
  is that its positive answers are correct and (with completeness) that its objective has a zero
  exactly when the graph is colourable;
* nothing is proved about the *momentum* recurrences of Li & Wang's eqs (3) and (6). Those are
  undamped accumulators, are not `Up` of any HNBM network, and no theory covers them —
  Goles–Chacc and Little–Peretto do not apply. Everything proved here concerns the memoryless
  single-site reading;
* the slack encoding is equivalent to, not identical to, Lucas §6.1.

## 8. Related work

All page/volume details below were checked against sources, not recalled.

* A. Lucas, *Ising formulations of many NP problems*, **Frontiers in Physics 2**:5 (2014);
  arXiv:1302.5843. §6.1 is the colouring Hamiltonian, §4.1 exact cover. Read directly.
* E. D. Dahl, *Neural network algorithm for an NP-complete problem: map and graph coloring*,
  Proc. IEEE First International Conference on Neural Networks, Vol. III, San Diego, June 1987,
  pp. 113–120.
* Y. Takefuji, K.-C. Lee, *Artificial neural networks for four-coloring map problems and
  K-colorability problems*, **IEEE Trans. Circuits and Systems 38**(3) (1991), pp. 326–333;
  doi:10.1109/31.101328.
* D. Brélaz, *New methods to color the vertices of a graph*, **CACM 22**(4) (April 1979),
  pp. 251–256; doi:10.1145/359094.359101. DSATUR, the baseline.
* R. M. Karp, *Reducibility among combinatorial problems*, in *Complexity of Computer
  Computations* (1972), pp. 85–103. Chromatic number is NP-complete.
* Y. Li, J. Wang, *Collaborative Neurodynamic Algorithms for Solving Sudoku Puzzles*, ICIST
  (2022). The solver, and the origin of the shared library.
* J. Mycielski, *Sur le coloriage des graphes*, Colloq. Math. **3** (1955), pp. 161–162. The
  construction behind the two hardest corpus instances.

Dahl and Takefuji–Lee are the papers this one has to distinguish itself from: both colour graphs
with a Hopfield network, three decades earlier. The distinction is not the method, it is that
here the encoding is proved faithful in both directions and the solver is proved to be
minimising the objective that encoding defines.

## 9. Open items before submission

1. Remove the row duplication — §3. The reported `vars` counts are 2× the natural ones.
2. Regenerate the results table once the row duplication is gone — row counts and penalty values
   both halve — and give Myc3 more than three seeds while doing it.
5. Decide the fate of the Sudoku reproducibility material. It is the strongest self-contained
   story in the repository (the paper states no `W`, no `θ` and no hyperparameter; two recovered
   constants decide success; Table I is now a theorem; proving it caught real specification bugs)
   and it does not belong in this paper. Currently earmarked as the motivating case study for the
   CPP submission.
