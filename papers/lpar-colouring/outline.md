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

The left equivalence makes the encoding faithful. The right one makes the network's energy *be*
the objective. The last arrow makes the theorems statements about the running program rather than
about an idealisation of it.

## 2. What is actually proved

| Claim | Declaration | Status |
|---|---|---|
| The encoding is a well-formed 0/1 QUBO | `Colouring.problem_wf` | ✓ |
| …and refines the colouring incidence | `Colouring.problem_refines` | ✓ |
| Soundness: `p(x) = 0` → the decoded colouring is proper | `Colouring.decode_isColouring` | ✓ |
| Completeness: a proper colouring encodes to `p = 0` | `Colouring.encode_penalty_zero` | ⧗ |
| Decision equivalence: `∃` zero ↔ `∃` proper colouring | `Colouring.exists_zero_iff_colourable` | ⧗ |
| K₄ is not 3-colourable (about the *graph*, not the QUBO) | `Colouring.k4_not_three_colourable` | ⧗ |
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

## 5. Results (§5) — **pending**

Corpus, greedy/DSATUR baselines and the measured table are being generated. The table must
report, per instance: `n`, `|E|`, known χ, colours used by greedy and DSATUR, and whether the
neurodynamics finds a zero at palette size χ and at χ+1.

Expected shape of the finding, to be confirmed or contradicted by the numbers: DSATUR matches or
beats the neurodynamics everywhere at this scale. Write that down if it holds. The results section
is evidence that the certified solver *works*, not that it is fast.

Instances verified working end to end so far:

| instance | palette | result |
|---|---|---|
| K₃ | 3 | solved, `210` |
| C₅ | 3 | solved, `21020` |
| Petersen | 3 | solved, `2020111022` |
| K₄ | 3 | no zero — correctly infeasible |
| C₅ | 2 | no zero — correctly infeasible |
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

* A. Lucas, *Ising formulations of many NP problems*, Frontiers in Physics **2**:5 (2014),
  arXiv:1302.5843. §6.1 is the colouring Hamiltonian; §4.1 exact cover. Verified against the
  published text.
* Y. Takefuji, K.-C. Lee, *Artificial neural networks for four-coloring map problems and
  K-colorability problems*, IEEE TCAS **38** (1991). The direct ancestor. **TODO** verify volume
  and pages against the original.
* J. Dahl, *Neural network algorithm for an NP-complete problem: map and graph coloring*, IEEE
  ICNN (1987). **TODO** verify.
* D. Brélaz, *New methods to color the vertices of a graph*, CACM **22** (1979). DSATUR, the
  baseline.
* R. Karp, *Reducibility among combinatorial problems* (1972). Chromatic number is NP-complete.
* Li & Wang, *Collaborative Neurodynamic Algorithms for Solving Sudoku Puzzles*, ICIST (2022).
  The solver, and the source of the shared library.

## 9. Open items before submission

1. **Completeness** — §2, in progress. Without it the paper cannot claim a decision procedure.
2. Results table — §5, in progress.
3. Remove the row duplication — §3.
4. Verify the two 1980s–90s citations against the originals.
5. Decide the fate of the Sudoku reproducibility material. It is the strongest self-contained
   story in the repository (the paper states no `W`, no `θ` and no hyperparameter; two recovered
   constants decide success; Table I is now a theorem; proving it caught real specification bugs)
   and it does not belong in this paper. Currently earmarked as the motivating case study for the
   CPP submission.
