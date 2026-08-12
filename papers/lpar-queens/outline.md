# Certified n-Queens Completion on a Hopfield/Boltzmann network

Draft material for a **self-contained LPAR short paper, 4–5 pages**, positioned as an application
of the formalisation in our accepted LPAR paper. Every claim below names the Lean declaration that
supports it; anything without one is marked **TODO** and must not go in the paper until it does.

Status key: **✓** proved and axiom-clean (`propext`, `Classical.choice`, `Quot.sound` only);
**⧗** in progress; **TODO** not started.

---

## 0. Relation to the main paper

The accepted paper formalises the machinery: `NeuralNetwork`, `TwoState.ZeroOne`, the Boltzmann
machine, Lyapunov descent, Gibbs stationarity, ergodicity (`HopfieldNet/Quiver/`). **None of it is
re-argued here.** This paper is one sentence long in outline: *here is that formalisation applied,
end to end, to an NP-complete problem it was not built for, and here is what the application buys
you that an unverified implementation could not claim.*

**TODO** — the main paper's exact title, authors and citation, and a check of which of §4's
results are already stated there versus new here. This gates §1 and cannot be written around.

The pitch, in one paragraph: n-Queens Completion is NP-complete *and* #P-complete (Gent, Jefferson
& Nightingale, JAIR 59 (2017), 815–848). We encode it as a 0/1 QUBO in canonical form, prove the
encoding faithful **in both directions**, prove the resulting network's energy minimisers are
*exactly* the completions, and inherit — with no new argument — the descent and Gibbs-concentration
results of the main paper. The running solver computes that network's **local field** — proved, not
asserted — though its update rule around that field is not the memoryless chain the theorems cover;
§4 and §7 state the boundary precisely, and it must not be blurred here. A reader can
watch it run in the Lean infoview.

## 1. The catalogue, the instances, and why Completion

### 1.1 What `‖Âx̂ − b̂‖²` admits from Lucas's catalogue

Lucas (*Ising formulations of many NP problems*, Frontiers in Physics **2**:5, 2014) is the
reference catalogue. State the scope limit in one paragraph rather than letting a referee find it:
the canonical form admits exactly the **feasibility problems whose constraints are equalities**.

* §4.1 exact cover fits with **no slack at all**.
* §6.1 graph colouring fits **after one slack per (edge, colour)**: `x_{u,i} + x_{v,i} + s = 1` is
  zero exactly when not both endpoints take colour `i`. This is *equivalent to, not identical to*,
  Lucas's Hamiltonian, whose conflict term is a bare product `x_{u,i} x_{v,i}` and is therefore not
  of the form `‖Âx̂ − b̂‖²`. Variable count `n(N + |E|)` against his `nN`.
* Optimisation problems — vertex cover, TSP, graph partitioning, §8 trees — **do not fit** without
  bounding the objective as a further constraint. Say so; it is the honest boundary of the method.

**TODO** — check whether Lucas gives an `n`-queens Hamiltonian, and if so how the slack form here
relates to it. Verify against the source, do not cite from memory.

### 1.2 The instances instantiated so far

| problem | Lucas | encoding cost | slacks | status |
|---|---|---|---|---|
| Sudoku (9×9) | — | `HopfieldNet/CNS/`, the original development | none | ✓ §1.3 |
| Exact cover | §4.1 | one `Incidence` value + a `Wf` proof | none | ✓ |
| Graph colouring | §6.1 | one file | one per (edge, colour) | ✓ §1.4 |
| Edge colouring | §6.1 | reduction to the line graph, two lines | inherited | ✓ |
| **n-Queens Completion** | — | one file | one per diagonal | ✓ §2–§6, in depth |

The point of the table is that after the first one, each costs *an encoding and a decoder*, not a
development. Queens is the one worked end to end below, because it is the only entry that is both
NP-complete **and** #P-complete, and the one whose column degrees exercise the library's
degree-free algebra hardest (three distinct values, two odd) --- see the correction in the
library itself (§2).

### 1.3 Sudoku, and what formalising it caught

The original application, and the one that shows what the exercise is *for*: Li & Wang (ICIST 2022)
is not reproducible as published, and the formalisation is what recovers it. All of the following is
verified by `lake exe cns`, re-run 2026-08-11:

* **The paper never writes down `W` or `θ`.** Recovered and checked: `Â` is `324 × 729` with
  exactly 4 nonzeros per column and 9 per row, every variable has exactly 28 off-diagonal
  neighbours, `W = −(ÂᵀÂ − 4I)`, `θ = −2·𝟙`, additive constant `162`. `W` is symmetric with zero
  diagonal — which is precisely the `pm W` that `TwoState.ZeroOne` requires, so the fit to the
  network is not arranged, it falls out. `p(x) = 0` on all ten published solutions and the
  canonical-form identity agrees on each (`cns encoding`).
* **Table I reproduces exactly**, all ten Sabuncu grids: candidates remaining after Algorithm 1 are
  `0, 0, 171, 95, 0, 209, 168, 0, 163, 0` (`cns table1`).
* **The reduced dynamics descend the paper's own objective**: `netVec` agrees with finite
  differences of `p` on 3420/1900/4180/3360/3260 checks across the five non-trivial instances, and
  the `embed` bridge between the reduced and unreduced objectives holds on 200 trials each
  (`cns reduced`).
* **Table II's "# of solutions" column is not a solution count** — it is `2^dim`, the size of the
  search space. Counted exactly: every instance has a unique solution except **Sabuncu3, which has
  27** and is therefore not a proper Sudoku (`cns count`).

Plus an errata list a formaliser cannot avoid: eq. (12) sums `p_b..p_e` where (11) defines
`p_a..p_d`; (11b,c,d) are missing `Σ_k`; (12),(13) say `{0,1}^n` for `{0,1}^{n³}`; Algorithm 1
line 26 has `(i,k,k)` for `(i,j,k)` and lines 18/22 zero the given's variable instead of the empty
cell's; the Sabuncu7 DHNm row of Table II is internally inconsistent; and Figs 4–8's middle boards
are not at the reduction fixpoint.

**Keep this to one tight paragraph plus the errata as a footnote.** The full story is the CPP
paper's motivating case study; here it is evidence that the library is not a toy.

### 1.4 Graph colouring — **⧗ table being re-run**

Proofs complete and axiom-clean: `Colouring.decode_isColouring`, `encode_penalty_zero`,
`exists_zero_iff_colourable'` (no side condition, not even a non-empty palette), and
`k4_not_three_colourable` as a statement about the *graph*. Edge colouring inherits soundness in two
lines because `adjPairs` serves both as `L(G)`'s edge list and as what `isProperEdgeColouring`
quantifies over, making the two checkers **definitionally** equal.

Measured against first-fit greedy and DSATUR on a fifteen-graph corpus. Numbers pending a re-run;
see §9. The finding to report is that **DSATUR wins outright** and the neurodynamics attains `χ` on
fourteen of fifteen, missing only `M(Grötzsch)` at palette 5 — presented as certification, not
speed.

### 1.5 Why Completion, and not n-queens

Load-bearing, and worth a full paragraph rather than a footnote. Plain n-queens has a closed-form
solution for every `N ≥ 4`, so a decision equivalence about it would be **vacuous** — the answer is
always yes. Completion — given a partial placement, can it be extended? — is the variant that is
actually hard, and it is the variant where "the solver found no zero" is a claim worth certifying.

The corpus makes the distinction concrete: a queen in the corner is fatal at `N = 4` and `N = 6`
and harmless at `N = 5, 7, 8, 9, 10` (`Baseline.count` on `⟨n, #[(0,0)]⟩` gives
`0, 2, 0, 4, 4, 28, 64`). And `Bench.blocked7` — two given queens that **do not attack each
other**, on a 7×7 board — admits no completion at all. Nothing local is wrong with those givens;
that is the whole difficulty of Completion in one picture, and it is what the widget should show.

## 2. The encoding (§2 of the paper, ~1.25 pages)

One variable per cell. Every constraint is an equality or an at-most-one, so it fits the canonical
form `‖Âx̂ − b̂‖²` directly.

| constraint | count | row |
|---|---|---|
| one queen per board row | `N` | `Σⱼ x_{i,j} = 1` |
| one per column | `N` | `Σᵢ x_{i,j} = 1` |
| ≤ 1 per diagonal of length ≥ 2 | `2N−3` | `Σ x + s_d = 1` |
| ≤ 1 per anti-diagonal of length ≥ 2 | `2N−3` | `Σ x + s_a = 1` |
| each given queen | `#givens` | a one-variable row, `b̂ = 1` |

`nvars = N² + 4N − 6`, `nrows = 6N − 6 + #givens` (`Queens.Instance.nvars`, `.nrows`).

Three points, each worth a paragraph:

* **One binary slack per diagonal expresses at-most-one regardless of the diagonal's length.**
  `Σx = 0 ⟹ s = 1`; `Σx = 1 ⟹ s = 0`; `Σx ≥ 2` leaves a residual of at least one, which is
  penalised. No new `Problem` field was needed. Say this plainly — the natural expectation is that
  at-most-one constraints require an at-most-one *row kind*, and they do not.
* **`b̂ ≡ 1` throughout, so `θ̂_u = −deg(u)`** (`Queens.problem`, and the `theta` field comment).
  Degrees are `4` (interior cell), `3` (a cell whose sum diagonal is a length-one corner) and `1`
  (a slack) — **two of them odd**. This is the instance that makes the doubled-`theta` field
  load-bearing rather than tidy: a halved threshold is a half-integer at odd degree and could not
  represent this encoding at all. Sudoku, at constant degree 4, never exposed it.
  Witness: `Queens.Examples`, the `theta = -3, -4, -1` example.
* **Givens are pinned as one-variable rows**, so `Problem.base` stays empty and no reduction
  machinery is involved.

Also worth two sentences: diagonals are indexed **additively** (`i + N = e + 2 + j` for the
difference direction, `i + j + D = e + 1` for the sum direction), so no truncated `Nat` subtraction
appears anywhere and the bounds on `e` *are* the "length ≥ 2" condition. This is a small thing that
saves a large amount of case analysis, and is the kind of detail a formalisation paper should
report.

## 3. Faithfulness, both directions (~0.75 pages)

| Claim | Declaration | Status |
|---|---|---|
| Well-formed 0/1 QUBO; refines the queens incidence | `Queens.problem_wf`, `Queens.problem_refines` | ✓ |
| Soundness: `p(x̂) = 0` → the decoded board is a completion | `Queens.decode_isQueens` | ✓ |
| Completeness: a completion encodes to `p(x̂) = 0` | `Queens.encode_penalty_zero` | ✓ |
| Decision equivalence | `Queens.exists_zero_iff_queens` | ✓ |
| Blocked boards, *about the board*: `¬ ∃ q, isQueens q` | `Queens.blocked4_no_queens`, `blocked6_no_queens`, `attacking_no_queens`, `Bench.blk7_no_queens`, `Bench.q2_no_queens`, `Bench.q3_no_queens` | ✓ |

The equivalence carries **one** hypothesis — `givensOk`, every given queen on the board — and no
lower bound on `N`. Say so explicitly: "we assume a non-empty board" is exactly the kind of side
condition a referee assumes is hiding something. The degenerate cases are *discharged*: at `N = 0`
there are no variables and no rows, the objective is vacuously zero and the empty board is
vacuously a completion; `givensOk` is what rules out the single bad case, an off-board given whose
row would contain no variable at all.

The blocked instances are the point of the exercise. They are statements about **boards**, not
about the QUBO, and by completeness they are what entitles a solver reporting "no zero" to say the
placement is dead. They are proved by kernel enumeration over the tuples the givens leave open
(`4³`, `6⁵`, `7⁵`) — ordinary kernel reduction, no `native_decide`.

## 4. The network (~0.75 pages)

Everything here is the main paper's machinery, instantiated. That is the point, so the section
should be short and should *say* it is short because nothing new was needed.

| Claim | Declaration | Status |
|---|---|---|
| The QUBO **is** an HNBM Boltzmann energy | `QUBO.Problem.zeroOneHamiltonian_eq`, `Queens.Examples.classic8_zeroOneHamiltonian_eq` | ✓ |
| The running inner loop computes that network's local field | `QUBO.Problem.netVec_eq_localField` | ✓ |
| Energy minimisers are **exactly** the completions | `Queens.exists_minEnergy_iff` | ✓ |
| Descent terminates | `Queens.classic8_exists_stable` | ✓ |
| The Gibbs equilibrium law concentrates on the completions | `Queens.classic8_stationary_infeasible_tendsto_zero` | ✓ |

`exists_minEnergy_iff` is the one genuinely new theorem in this section and deserves the emphasis:
the generic theory knows the minimisers are the zero-penalty assignments, but nothing connects that
to *boards*. Both directions are proved — a completion encodes to a minimiser
(`Queens.energy_stateOf`), and every minimiser decodes to a board the checker accepts
(`Queens.isQueens_decode_of_minEnergy`).

Two reusable bridges fell out of this and should get one sentence, because they are the part other
instances will want: `QUBO.Problem.penaltyR_bitsOf_eq_zero_iff` (the executable objective and the
abstract one vanish together) and `bitsOfState_stateOfBits`.

`netVec_eq_localField` is what stops all of this being about a lookalike: the `O(nvars)` integer
routine in the inner loop is *proved equal* to the network's local field, so the descent and
concentration results apply to that field computation.

**The boundary, stated exactly, because §0 must not overclaim it.** `netVec_eq_localField` certifies
the *field*, not the update rule wrapped around it. Every run path in `Dynamics.lean` accumulates
momentum — `ui := u_prev + (Wx − θ)` at `dhnmStep`:185, `bmmStep`:220 and `seqRun`:306 — and
`ModelConfig` has no flag to switch it off. So **no configuration of the running solver is the
memoryless `State.Up` chain** the descent and Gibbs results are stated for, not even
`sequential := true`; they coincide only on the first inner iteration, where `u` is still `0`. Add
`Float.exp` in the acceptance test and synchrony in `bmmStep`, and the honest claim is: the
*objective* is the network's energy (`zeroOneHamiltonian_eq`), the *field* the code computes is the
network's field (`netVec_eq_localField`), and the minimisers are exactly the completions
(`exists_minEnergy_iff`) — while the *trajectory* the solver follows is eq. (3)/(6)'s momentum
recurrence, which no theorem here covers. §7's momentum bullet says this; §0 and this section must
agree with it.

## 5. Measurements (~0.75 pages) — ✓ measured

`QUBO.Instances.Queens.Bench`, built 2026-08-11 (**11.5 min**, exit 0, via `lake build` so no stale
`.olean` can be picked up — `lake env lean` does *not* check dependency freshness and silently used
a stale one once during this work). Configuration, stated once: `N = M = 20`, `maxOuter = 60`,
`inner = 40`, `T₀ = 3.0`, `η = 0.9`, one-hot initialisation, base seed **20260806**; the anneal
column is one BMm run of 400 sweeps at `T = 3·0.99ᵗ` from the same base seed. `QUBO.Rng` is
`splitmix64` and nothing reads a clock.

`T₀` is the **effective** temperature. This has to be said once and got right: `Problem.theta` is
stored doubled so odd column degrees stay integral, hence `netVec` returns twice the local field,
hence `ModelConfig.tabulate` builds the logistic table at `2·T₀`. Every config in `Bench`,
`ColouringBench` and `CNS` tabulates, so all three corpora share one convention and are comparable.

**Table for the paper** — compressed from the bench's eleven rows to seven. `sol`/`ok` are the
baseline's verdict and the *checker's* verdict on the board it returned; `cnt` is the number of
completions; `hit`/`out` the swarm at the base seed; `s/k` its successes over `k` seeds; `dhnm` the
same swarm driving **eq. (3)** instead of eq. (6); `ann` a single anneal over 20 seeds.

| board | N | giv | vars | rows | sol | ok | cnt | hit | out | s/k | dhnm | ann |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| Q4 | 4 | 0 | 26 | 18 | y | y | 2 | y | 1 | 10/10 | 10/10 | 7/20 |
| Q6 | 6 | 0 | 54 | 30 | y | y | 4 | y | 4 | 9/10 | 8/10 | **0/20** |
| Q8 | 8 | 0 | 90 | 42 | y | y | 92 | y | 3 | 10/10 | 9/10 | **0/20** |
| Q10 | 10 | 0 | 134 | 54 | y | y | 724 | n | 31 | 0/5 | 1/5 | **0/20** |
| Comp6 | 6 | 1 | 54 | 31 | y | y | 1 | n | 22 | 6/10 | 7/10 | **0/20** |
| Comp8 | 8 | 3 | 90 | 45 | y | y | 1 | y | 14 | 6/10 | 3/10 | **0/20** |
| Comp8b | 8 | 5 | 90 | 47 | y | y | 1 | y | 4 | 10/10 | 10/10 | **0/20** |

(`Q5` `10/10`, `Q7` `10/10`, `Q9` `4/5` omitted for space.)

Blocked boards, as a second compact block. `cnt = 0` on every row is the baseline's exhaustive
verdict; `cert` says whether the impossibility is a *theorem* here; `pen` is the best objective the
swarm reached.

| board | N | giv | vars | cnt | cert | zero | s/k | pen |
|---|---|---|---|---|---|---|---|---|
| Blk4 | 4 | 1 | 26 | 0 | y | n | 0/5 | 1 |
| Blk6 | 6 | 1 | 54 | 0 | y | n | 0/5 | 1 |
| Blk7 | 7 | 2 | 71 | 0 | y | n | 0/5 | 1 |
| Blk8 | 8 | 2 | 90 | 0 | **n** | n | 0/5 | 1 |
| Attack | 8 | 2 | 90 | 0 | y | n | 0/5 | 1 |

(`Q2`, `Q3` also measured and also certified; drop them from the paper's table for space and
mention in a clause.)

Four findings to report:

1. **The classical baseline wins outright**, as DSATUR does in the colouring companion. It solves
   every completable row and refutes every blocked one, in microseconds. Say it in the section's
   first sentence. The claim is certification, not speed. The `ok` column is `y` on every row — a
   running confirmation of `Baseline.solve_isQueens` rather than a separate check.
2. **A single annealed Boltzmann machine solves nothing above `5 × 5`.** `7/20` at `N = 4`, `5/20`
   at `N = 5`, and **`0/20` on every board from `N = 6` upward and on every completion instance** —
   while the swarm solves ten of the eleven. This gap is far wider for queens than for colouring and
   is the most interesting thing the corpus shows. (Measured twice: at half this temperature the
   anneal got `1/20` on Q6 and Q7, so the correct, hotter schedule is *worse* for a single machine.
   Report the correct one and do not present the fix as an improvement.)

2a. **Both of Wang's models, and the model choice matters per problem.** Under eq. (7), DHNm
   (eq. 3) matches BMm on the empty boards but degrades on the many-givens completions —
   `3/10` against `6/10` on `Comp8`, `1/5` against `0/5` on `Q10`. On the colouring corpus the two
   are *indistinguishable*: DHNm is `10/10` on all fourteen solvable graphs and `0/3` on Myc3,
   exactly BMm's record. So which neurodynamic model you pick is irrelevant for colouring and
   matters for queens — a finding neither corpus alone would give.

2b. **The diversity threshold `𝒯` is a principled constant, not a fit.** `𝒯 = 0.9` for DHNm against
   `0.4` for BMm was recovered on Sudoku; it transfers. At BMm's `0.4`, DHNm *fails* on the empty
   `8 × 8`; at `0.9` it gets `9/10`. A recovered constant that reproduces on two unrelated problems
   is a much stronger claim than a tuned one, and this is the place to make it.
3. **That failure is a schedule problem, not an encoding problem**, and §4 is what licenses saying
   so: `classic8_stationary_infeasible_tendsto_zero` proves the equilibrium law concentrates on the
   completions. Be careful — it is a limit of the equilibrium law as `T → 0⁺`, *not* a statement
   about any cooling schedule, and the paper must not let the two blur.
4. **`pen = 1` on every blocked row**, never a small fraction. That is
   `QUBO.Problem.one_le_penaltyR_of_ne_zero` — "there is no state whose penalty is a small positive
   number" — showing up in the measurements. Worth one sentence: it is the same fact as the energy
   gap `≥ ½` (`half_le_energy_sub_min`), which is what drives the Boltzmann suppression in §4.

One sentence on the count column: `Baseline.count` on empty boards reproduces OEIS A000170 —
`1, 1, 0, 0, 2, 10, 4, 40, 92, 352, 724` for `n = 0 … 10`, including 92 at `N = 8` — which is the
check that makes the column worth printing, and exercises the #P-complete half of the problem.
`Comp6`, `Comp8` and `Comp8b` each have exactly **one** completion, which is why they are the right
instances to demo.

### Seed provenance — do not mix the two measurements

All figures in the queens tree have been regenerated at the corrected temperature; the bench is the
authoritative source and the `Widget`/`Gallery` docstrings now defer to it explicitly. **Quote the
bench, and give the sample size.**

The gallery episode is worth one sentence in §5 as extra evidence for finding (ii), because it is a
sharper version of the same point. The `#queensAt` widgets are pinned to seeds that settle; at the
demo's original schedule (400 sweeps, `T = 3·0.99ᵗ`) **no seed in `[0,60)` settles on `small6` or on
`completion8`**, and the animation had to be slowed to 2000 sweeps at `T = 2·0.998ᵗ` before any did
— at which point `1/40` seeds succeed on each. Those seeds worked before only because the anneal was
running at half the advertised temperature. A single machine needs a five-times-longer anneal *and* a
one-in-forty seed to show a completed `6 × 6` board; the swarm does it every time.

### Algorithm 1 does not apply, and the paper should say so

Li & Wang's pipeline is *Algorithm 1 then Algorithm 2*. Algorithm 1 is a deterministic
variable-reduction presolve — Sudoku naked/hidden singles to a fixpoint (`CNS/Reduce.lean`), and
exactly what their Table I measures; on five of the ten Sabuncu instances it reduces the problem to
nothing and Algorithm 2 never runs. **Queens uses Algorithm 2 alone**: `Queens.problem` sets
`base := #[]`, nothing is pre-assigned, and the widget's `phase` is uniformly `1` so the player's
"Algorithm 1, *n* deductions" caption is dead code here.

A queens analogue exists and is unimplemented: place a queen wherever a row or column has exactly one
square not attacked by a given, and iterate. It would shrink the encoding on heavily constrained
completions such as `Comp8b`. State it as a difference between the two pipelines, not as a gap in
correctness. Also worth one clause: `#queens` animates the **incumbent** `x*` once per outer
iteration, so the other 19 particles are never drawn — the animation looks like a single trajectory
even though it is the full swarm.

The baseline is certified in the direction that matters: `Baseline.solve_isQueens` proves every
board it returns is a genuine completion. Its converse is **not** proved (see §7). One sentence on
the count column: `Baseline.count` reproduces OEIS A000170 on empty boards — `1, 1, 0, 0, 2, 10, 4,
40, 92, 352, 724` for `n = 0 … 10`, including 92 at `N = 8` — which is the check that makes the
column worth printing, and exercises the #P-complete half of the problem.

## 6. The artifact (~0.4 pages) — ✓ built

Today: `#queens`, `#queensAt`, `#queensFire`, `#queensRefute` animate a run in the infoview, one
frame per outer iteration or per sweep, on an `N × N` chequerboard with attacking pairs joined by a
dashed segment and both squares washed. Given queens are ringed; the search's are in slot-2 orange.
The picture is of the *constraint*: a segment is drawn exactly when one of `isQueens`'s three
pairwise clauses fails, which is exactly when a column or diagonal row of `Â` carries two set
variables.

**And now live**: `#queensBoard` (`Queens.Interactive`) renders a board you *click* to build a
partial placement, then `anneal` / `swarm` / `backtrack` call back into the Lean language server via
Lean core's `@[server_rpc_method]`, which runs the real solver and returns the frames. This is the
repository's only non-elaboration-time widget; every other one ships precomputed props. Two
constraints to state: the file must be open in the editor (it is a development artifact, not a web
page), and RPC bodies run interpreted, so a solve costs what the corresponding `#eval` costs.

Design note, from the measurements: an interactive "place queens, press solve" that runs a *single
anneal* will mostly fail, because a single anneal mostly fails. Either it runs the swarm, or the
failure has to be the point being demonstrated rather than an embarrassment.

Keep this section short. The widget makes the artifact evaluable; it is not the contribution.

## 7. What we do not claim (~0.2 pages)

State these plainly rather than letting a referee find them.

* **No performance claim.** Backtracking beats the neurodynamics on every instance in the corpus,
  by orders of magnitude.
* **No algorithmic novelty.** Hopfield/Boltzmann approaches to constraint problems are decades old;
  the solver is Li & Wang's collaborative neurodynamic scheme, applied unchanged. What is new is
  that the encoding, the objective identification and the negative answers are proved.
* **The search is a heuristic.** Nothing proves it *finds* a zero when one exists. The proved
  content is that its positive answers are correct and, via completeness, that its objective has a
  zero exactly when the board is completable.
* **No completeness claim for the classical baseline.** `Baseline.solve_isQueens` proves every
  board it returns is a completion; it does *not* prove that `none` means none exists. The search is
  exhaustive by construction, but that is an argument about the code, not a theorem about it — so
  the blocked instances are refuted separately by kernel enumeration where the board is small
  enough, and are marked as observations otherwise.
* **Nothing about cooling schedules.** See §5, point 3.
* **Nothing about the momentum recurrences of eqs (3) and (6).** Those are undamped accumulators,
  are not `Up` of any HNBM network, and no theory here covers them. Everything proved concerns the
  memoryless single-site reading.

## 8. Related work

* A. Lucas, *Ising formulations of many NP problems*, **Frontiers in Physics 2**:5 (2014);
  arXiv:1302.5843. The catalogue. **TODO** — check whether Lucas gives an n-queens Hamiltonian and,
  if so, how the slack form here relates to it, as was done for §6.1 colouring.
* I. P. Gent, C. Jefferson, P. Nightingale, *Complexity of n-Queens Completion*, **JAIR 59** (2017),
  pp. 815–848. NP-completeness and #P-completeness of the variant this paper encodes. Verified.
* Y. Li, J. Wang, *Collaborative Neurodynamic Algorithms for Solving Sudoku Puzzles*, ICIST (2022).
  The solver, and the origin of the shared library.
* **TODO** — the accepted main LPAR paper.
* **TODO** — prior neural/Hopfield approaches to n-queens specifically. There is a literature
  (Takefuji et al. on n-queens with Hopfield networks in the late 1980s/early 1990s) and it must be
  cited as the reason the *algorithmic* contribution is nil, exactly as Dahl and Takefuji–Lee are
  cited in the colouring companion. **Do not cite from memory — verify against sources.**

## 9. Open items before submission

1. **§0/§8 TODO**: the accepted paper's citation. Blocks the framing.
2. **§8 TODO**: verify the prior-art citations for neural n-queens against sources.
3. **§5**: fold in the bench numbers and compress to one table.
4. **§6**: settle the interactive widget, or write the fallback.
5. **Artifact hygiene**, none of it addressed:
   * `MCMC/Gibbs.lean` carries **22 `sorry`s** — the only ones in the repository. Fence or drop it.
   * `HopfieldNet/QUBO/Converge.lean` and `Gibbs.lean` are untracked and were never in any build
     until 2026-08-11, yet they carry the results §4 cites. Commit them.
   * `lakefile.lean` requires `CertifiedReals` at `@ "main"`. Pin a tag.
6. **Page budget.** At 4–5 pages this is tight. If it overruns, cut in this order: §5's second
   table, then §2's third bullet, then §4's "reusable bridges" sentence. Do **not** cut §7.
