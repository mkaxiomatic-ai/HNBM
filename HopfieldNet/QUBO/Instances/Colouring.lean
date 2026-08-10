/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.QUBO.Refine

/-!
# Graph `n`-colouring as a 0/1 QUBO in canonical form

`QUBO.Problem` is the objective `‖Â x̂ − b̂‖²` with `Â` a 0/1 matrix. This module builds one from
a graph `G = (V,E)` and a palette of `n` colours, so that a zero of the objective *is* a proper
`n`-colouring of `G`, and proves it: `Problem.Wf` for the instance, and a decoder whose output
passes a `Bool` colouring checker whenever the penalty vanishes.

Both directions are proved, so the reduction is exact and not merely sound:

* `decode_isColouring` — a zero of the objective decodes to a proper colouring;
* `encode_penalty_zero` — a proper colouring encodes to a zero of the objective;
* `exists_zero_iff_colourable` — hence the QUBO has a zero **iff** `G` is `n`-colourable, with
  `decode_encode` identifying the two directions on the nose.

The point of the second direction is that a *negative* answer now means something: `k4_no_zero`
says the `K₄` QUBO has no zero, and `k4_not_three_colourable` upgrades that to the graph
statement `¬ ∃ col, k4.isColouring col`.

## Relation to Lucas §6.1

Lucas writes

    H = A · Σ_v (1 − Σ_i x_{v,i})² + B · Σ_{(uv) ∈ E} Σ_i x_{u,i} x_{v,i}.

This is *equivalent to*, but not *identical to*, what is built here, in two respects.

1. **The edge term is not a squared residual.** `x_{u,i} x_{v,i}` is a bare product, so the second
   sum is not of the form `‖Ax − b‖²` and does not fit `Problem` at all. It is converted by
   introducing one slack per (edge, colour),

       x_{u,i} + x_{v,i} + s_{e,i} = 1        for e = (u,v) ∈ E and i < n,

   whose residual is `0` exactly when at most one endpoint of `e` takes colour `i` (if both do,
   the left side is `2` or `3`, never `1`, whatever the slack). The whole Hamiltonian is then a
   sum of squared residuals of *linear* equations. The price is `n·|E|` extra variables; the
   feasible sets correspond, since for any 0/1 point with `x_{u,i} + x_{v,i} ≤ 1` the slack is
   determined, and conversely.
2. **There are no coefficients `A`, `B`.** The canonical form carries a single global weight, and
   both families of constraints are hard, so `A = B = 1`.

## Index layout

Write `N = nverts`, `n = ncolours`, `E = |edges|`. Variables (`nvars = n·N + n·E`):

| range              | name        | index                  |
| ------------------ | ----------- | ---------------------- |
| `v < N`, `i < n`   | `colVar v i`| `n·v + i`              |
| `e < E`, `i < n`   | `slackVar`  | `n·N + n·e + i`        |

Constraints (`nrows = nbase = N + n·E`), each written **once**, each with `b̂ = 1`:

| range              | name         | index            | equation                              |
| ------------------ | ------------ | ---------------- | ------------------------------------- |
| `v < N`            | vertex row   | `v`              | `Σ_i x_{v,i} = 1`                     |
| `e < E`, `i < n`   | `edgeRow e i`| `N + n·e + i`    | `x_{u,i} + x_{v,i} + s_{e,i} = 1`     |

## Why the rows are *not* doubled

`Wf.theta_eq` reads

    θ (as stored) = deg(u) − 2 Σ_{r ∋ u} b̂_r,

i.e. `Problem.theta` holds `2 θ̂_u`, not `θ̂_u`. The mathematical threshold
`θ̂_u = ½deg(u) − Σ_{r ∋ u} b̂_r` is a half-integer whenever `deg(u)` is odd, and an earlier
version of this file stored `θ̂` itself; the only way to stay in `ℤ` was then to force every
column degree even, which was done by writing every constraint *twice* (row `r` and row
`r + nbase` carrying the same equation, `nrows = 2·nbase`). With `theta` stored doubled there is
no parity condition left, so the duplication has been removed: it doubled `nrows`, the objective
value and the work per sweep, and bought nothing. `QUBO.Problem.toyOdd` is a minimal instance of
odd degree.

Here every `b̂_r = 1`, so `Σ_{r ∋ u} b̂_r = deg(u)` and the stored threshold is simply

    theta u = deg(u) − 2·deg(u) = −deg(u) = −|rowList u|,

an integer whatever the parity, and `constDoubled = Σ_r b̂_r² = nrows = nbase`.

Note how far the incidence is from regular: a colour variable `(v,i)` has degree `1 + deg_G(v)`,
which varies with `v`, and a slack has degree `1`. The degree-free statement of `Wf.theta_eq` is
what makes this expressible; see `QUBO.Incidence`.
-/

namespace QUBO
namespace Colouring

open QUBO.Problem

/-- **A graph-colouring instance.** Vertices are `0, …, nverts-1`; an edge is a pair of vertex
indices. `edgesOk` is the well-formedness the soundness theorem needs (endpoints in range and
no loops); nothing else assumes it. -/
structure Instance where
  /-- Number of vertices `N`. -/
  nverts : Nat
  /-- Size `n` of the colour palette. -/
  ncolours : Nat
  /-- The edge list `E`; parallel edges are harmless, loops are excluded by `edgesOk`. -/
  edges : Array (Nat × Nat)
deriving Inhabited, Repr

namespace Instance

variable (I : Instance)

/-! ## The index layout -/

/-- `|E|`. -/
def nedges : Nat := I.edges.size

/-- The number of colour variables, `n·N`; the slacks start here. -/
def ncolVars : Nat := I.ncolours * I.nverts

/-- `n·N + n·E`: one variable per (vertex, colour) and one per (edge, colour). -/
def nvars : Nat := I.ncolours * I.nverts + I.ncolours * I.nedges

/-- `N + n·E`: one vertex row per vertex and one edge row per (edge, colour). -/
def nbase : Nat := I.nverts + I.ncolours * I.nedges

/-- The number of rows. Every constraint is written once, so this is `nbase`. -/
def nrows : Nat := I.nbase

/-- The variable "vertex `v` takes colour `i`". -/
def colVar (v i : Nat) : Nat := I.ncolours * v + i

/-- The slack of edge `e` at colour `i`. -/
def slackVar (e i : Nat) : Nat := I.ncolVars + I.ncolours * e + i

/-- The row `x_{u,i} + x_{v,i} + s_{e,i} = 1` for `e = (u,v)`. -/
def edgeRow (e i : Nat) : Nat := I.nverts + I.ncolours * e + i

/-! ## Arithmetic of the layout -/

theorem div_pack {i a : Nat} (hc : 0 < I.ncolours) (hi : i < I.ncolours) :
    (I.ncolours * a + i) / I.ncolours = a := by
  rw [Nat.mul_add_div hc, Nat.div_eq_of_lt hi, Nat.add_zero]

theorem mod_pack {i a : Nat} (_hc : 0 < I.ncolours) (hi : i < I.ncolours) :
    (I.ncolours * a + i) % I.ncolours = i := by
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hi]

theorem pack_lt {i a b : Nat} (hi : i < I.ncolours) (hab : a < b) :
    I.ncolours * a + i < I.ncolours * b := by
  have h1 : I.ncolours * a + I.ncolours = I.ncolours * (a + 1) := by ring
  have h2 : I.ncolours * (a + 1) ≤ I.ncolours * b :=
    Nat.mul_le_mul_left _ (by omega)
  omega

theorem colVar_lt {v i : Nat} (hv : v < I.nverts) (hi : i < I.ncolours) :
    I.colVar v i < I.ncolVars :=
  I.pack_lt hi hv

theorem colVar_lt_nvars {v i : Nat} (hv : v < I.nverts) (hi : i < I.ncolours) :
    I.colVar v i < I.nvars := by
  have := I.colVar_lt hv hi
  simp only [ncolVars, nvars] at *
  omega

theorem edgeRow_lt {e i : Nat} (he : e < I.nedges) (hi : i < I.ncolours) :
    I.edgeRow e i < I.nbase := by
  have := I.pack_lt hi he
  simp only [edgeRow, nbase]
  omega

/-! ## The incidence

`baseInRow u r` decides membership of column `u` in row `r`, and the row set of a column is the
`List.filter` of that predicate over the index range — never a scatter loop: `nodup` is then
inherited from `List.nodup_range` and membership is `List.mem_filter`, whereas a `set!` loop
could only be characterised by induction on its trip count. -/

/-- **The incidence.** For a colour variable `u = n·v + i`: the vertex row `v`, and the edge
row of every (incident edge, `i`). For a slack `u = n·N + n·e + i`: the single edge row
`N + n·e + i`. -/
def baseInRow (u r : Nat) : Bool :=
  if u < I.ncolVars then
    if r < I.nverts then r == u / I.ncolours
    else
      match I.edges[(r - I.nverts) / I.ncolours]? with
      | none => false
      | some p =>
          ((r - I.nverts) % I.ncolours == u % I.ncolours)
            && (p.1 == u / I.ncolours || p.2 == u / I.ncolours)
  else
    r + I.ncolVars == u + I.nverts

/-- The rows of column `u`, as a duplicate-free increasing list. -/
def baseRowList (u : Nat) : List Nat :=
  (List.range I.nbase).filter (fun r => I.baseInRow u r)

/-- The rows of column `u`. Every constraint is written once, so this is `baseRowList`. -/
def rowList (u : Nat) : List Nat := I.baseRowList u

/-- The rows of column `u`, as an array — the `rowsOf` of the `Problem` below. -/
def rowsOf (u : Nat) : Array Nat := (I.rowList u).toArray

theorem mem_baseRowList {u r : Nat} :
    r ∈ I.baseRowList u ↔ r < I.nbase ∧ I.baseInRow u r = true := by
  simp [baseRowList, List.mem_filter, List.mem_range]

theorem baseRowList_nodup (u : Nat) : (I.baseRowList u).Nodup :=
  List.Nodup.filter _ (List.nodup_range)

theorem rowList_nodup (u : Nat) : (I.rowList u).Nodup := I.baseRowList_nodup u

theorem rowList_lt {u r : Nat} (hr : r ∈ I.rowList u) : r < I.nrows := by
  have := ((I.mem_baseRowList).mp hr).1
  simp only [nrows]; omega

theorem rowsOf_size (u : Nat) : (I.rowsOf u).size = (I.baseRowList u).length := by
  simp only [rowsOf, rowList, List.size_toArray]

theorem mem_rowsOf {u r : Nat} : r ∈ I.rowsOf u ↔ r ∈ I.rowList u := by
  simp [rowsOf]

/-- Membership in the row set of a column is the incidence. -/
theorem contains_base {u r : Nat} (hr : r < I.nbase) :
    (I.rowsOf u).contains r = true ↔ I.baseInRow u r = true := by
  rw [Array.contains_iff_mem, I.mem_rowsOf, rowList]
  exact ⟨fun h => ((I.mem_baseRowList).mp h).2, fun h => (I.mem_baseRowList).mpr ⟨hr, h⟩⟩

/-! ## Reading the incidence -/

/-- A vertex row sees exactly the colour variables of that vertex. -/
theorem baseInRow_vertex {u v : Nat} (hv : v < I.nverts) :
    I.baseInRow u v = true ↔ (u < I.ncolVars ∧ u / I.ncolours = v) := by
  unfold baseInRow
  by_cases h : u < I.ncolVars
  · rw [if_pos h, if_pos hv]
    simp only [beq_iff_eq]
    exact ⟨fun hh => ⟨h, hh.symm⟩, fun hh => hh.2.symm⟩
  · rw [if_neg h]
    simp only [beq_iff_eq]
    exact ⟨fun hcon => absurd hcon (by omega), fun hh => absurd hh.1 h⟩

/-- A colour variable of an endpoint of `e` sits in the edge row of `e` at its own colour. -/
theorem baseInRow_edge {a i e : Nat} (hc : 0 < I.ncolours) (ha : a < I.nverts)
    (hi : i < I.ncolours) {p : Nat × Nat} (hp : I.edges[e]? = some p)
    (hend : p.1 = a ∨ p.2 = a) :
    I.baseInRow (I.colVar a i) (I.edgeRow e i) = true := by
  have hlt : I.colVar a i < I.ncolVars := I.colVar_lt ha hi
  have hdiv : (I.colVar a i) / I.ncolours = a := I.div_pack hc hi
  have hmod : (I.colVar a i) % I.ncolours = i := I.mod_pack hc hi
  have hsub : I.edgeRow e i - I.nverts = I.ncolours * e + i := by simp only [edgeRow]; omega
  have hnot : ¬ (I.edgeRow e i < I.nverts) := by simp only [edgeRow]; omega
  unfold baseInRow
  rw [if_pos hlt, if_neg hnot, hsub, I.div_pack hc hi, I.mod_pack hc hi, hp, hdiv, hmod]
  rcases hend with h | h <;> simp [h]

/-- A slack sits in exactly one row, its own edge row. -/
theorem baseInRow_slack {e i : Nat} :
    I.baseInRow (I.slackVar e i) (I.edgeRow e i) = true := by
  have hnot : ¬ (I.slackVar e i < I.ncolVars) := by simp only [slackVar]; omega
  unfold baseInRow
  rw [if_neg hnot]
  simp only [edgeRow, slackVar, beq_iff_eq]
  omega

theorem slackVar_lt_nvars {e i : Nat} (he : e < I.nedges) (hi : i < I.ncolours) :
    I.slackVar e i < I.nvars := by
  have := I.pack_lt hi he
  simp only [slackVar, ncolVars, nvars] at *
  omega

/-- **The full content of an edge row.** Its variables are the colour variables of the two
endpoints at colour `i`, and the slack `s_{e,i}` — nothing else. This is the converse of
`baseInRow_edge` and `baseInRow_slack` together, and it is what completeness needs: to know a
row is satisfied one must know *every* variable in it. -/
theorem baseInRow_edgeRow {e i u : Nat} (hc : 0 < I.ncolours) (hi : i < I.ncolours)
    {p : Nat × Nat} (hp : I.edges[e]? = some p) :
    I.baseInRow u (I.edgeRow e i) = true ↔
      ((u < I.ncolVars ∧ u % I.ncolours = i ∧ (p.1 = u / I.ncolours ∨ p.2 = u / I.ncolours))
        ∨ u = I.slackVar e i) := by
  have hnot : ¬ (I.edgeRow e i < I.nverts) := by simp only [edgeRow]; omega
  have hsub : I.edgeRow e i - I.nverts = I.ncolours * e + i := by simp only [edgeRow]; omega
  unfold baseInRow
  by_cases h : u < I.ncolVars
  · rw [if_pos h, if_neg hnot, hsub, I.div_pack hc hi, I.mod_pack hc hi, hp]
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true]
    constructor
    · rintro ⟨h1, h2⟩; exact Or.inl ⟨h, h1.symm, h2⟩
    · rintro (⟨-, h1, h2⟩ | h1)
      · exact ⟨h1.symm, h2⟩
      · exact absurd h (by simp only [h1, slackVar]; omega)
  · rw [if_neg h]
    simp only [beq_iff_eq]
    constructor
    · intro heq; exact Or.inr (by simp only [slackVar, edgeRow] at heq ⊢; omega)
    · rintro (⟨h1, -, -⟩ | h1)
      · exact absurd h1 h
      · simp only [h1, slackVar, edgeRow]; omega

/-- Every row past the vertex rows is an edge row, with both indices in range. -/
theorem eq_edgeRow {r : Nat} (h1 : I.nverts ≤ r) (h2 : r < I.nbase) :
    ∃ e i, e < I.nedges ∧ i < I.ncolours ∧ r = I.edgeRow e i := by
  have hc : 0 < I.ncolours := by
    rcases Nat.eq_zero_or_pos I.ncolours with h | h
    · simp only [nbase, h, Nat.zero_mul] at h2; omega
    · exact h
  have hlt : r - I.nverts < I.ncolours * I.nedges := by simp only [nbase] at h2; omega
  refine ⟨(r - I.nverts) / I.ncolours, (r - I.nverts) % I.ncolours,
    Nat.div_lt_of_lt_mul hlt, Nat.mod_lt _ hc, ?_⟩
  have hdm := Nat.div_add_mod (r - I.nverts) I.ncolours
  simp only [edgeRow]
  omega

end Instance

/-! ## The QUBO

Every field is a `map` or a `filter` over an index range, as in `CNS.Problem.ofReduced`: field
projections are then `rfl` and entries are read off by `Array.getElem_map`. -/

open Instance

/-- **The colouring QUBO.** `b̂ ≡ 1`, since every constraint is an "exactly one" equation, so
`Σ_{r ∋ u} b̂_r = deg(u)` and the stored (doubled) threshold is
`2θ̂_u = deg(u) − 2deg(u) = −deg(u) = −|baseRowList u|`. -/
def problem (I : Instance) : Problem where
  nvars := I.nvars
  nrows := I.nrows
  varOf := Array.range I.nvars
  rowsOf := (Array.range I.nvars).map I.rowsOf
  varsOf := (Array.range I.nrows).map fun r =>
    ((List.range I.nvars).filter fun u => (I.rowsOf u).contains r).toArray
  bhat := Array.replicate I.nrows 1
  -- stored doubled: `2θ̂_u = deg(u) − 2 Σ_{r ∋ u} b̂_r = deg(u) − 2·deg(u) = −deg(u)`
  theta := (Array.range I.nvars).map fun u => -((I.baseRowList u).length : Int)
  constDoubled := (I.nbase : Int)
  base := #[]

variable (I : Instance)

@[simp] theorem problem_nvars : (problem I).nvars = I.nvars := rfl
@[simp] theorem problem_nrows : (problem I).nrows = I.nrows := rfl

theorem problem_rowsOf {u : Nat} (hu : u < I.nvars) :
    (problem I).rowsOf.getD u #[] = I.rowsOf u := by
  show ((Array.range I.nvars).map I.rowsOf).getD u #[] = _
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa using hu)]
  simp

theorem problem_bhat {r : Nat} (hr : r < I.nrows) : (problem I).bhat.getD r 0 = 1 := by
  show (Array.replicate I.nrows (1 : Int)).getD r 0 = 1
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa using hr)]
  simp

theorem problem_theta {u : Nat} (hu : u < I.nvars) :
    (problem I).theta.getD u 0 = -((I.baseRowList u).length : Int) := by
  show ((Array.range I.nvars).map fun u => -((I.baseRowList u).length : Int)).getD u 0 = _
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa using hu)]
  simp

theorem problem_varOf {u : Nat} (hu : u < I.nvars) : (problem I).varOf.getD u 0 = u := by
  show (Array.range I.nvars).getD u 0 = u
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa using hu)]
  simp

/-- The colouring constraint system as a `QUBO.Incidence`. -/
def incidence (I : Instance) : Incidence where
  nvars := I.nvars
  nrows := I.nrows
  rowsOf := I.rowsOf
  nodup := fun u _ => by simpa [Instance.rowsOf] using I.rowList_nodup u
  mem_lt := fun u _ r hr => I.rowList_lt (I.mem_rowsOf.mp hr)

/-- The QUBO is the (trivial, no columns deleted) restriction of that incidence. -/
theorem problem_refines : Problem.Refines (incidence I) (problem I) where
  nrows_eq := rfl
  varOf_lt := fun u hu => by rw [problem_varOf I hu]; exact hu
  rowsOf_eq := fun u hu => by rw [problem_rowsOf I hu, problem_varOf I hu]; rfl
  varOf_inj := fun u hu v hv h => by rwa [problem_varOf I hu, problem_varOf I hv] at h

/-! ## Well-formedness -/

/-- Summing `b̂` over the indicator of a column is its degree, because `b̂ ≡ 1`. -/
theorem sum_bhat_indicator {u : Nat} (hu : u < I.nvars) :
    ∑ r ∈ Finset.range (problem I).nrows,
        (if ((problem I).rowsOf.getD u #[]).contains r then (problem I).bhat.getD r 0 else 0)
      = ((I.rowsOf u).size : Int) := by
  have hnd : (I.rowsOf u).toList.Nodup := by simpa [Instance.rowsOf] using I.rowList_nodup u
  have hlt : ∀ r ∈ I.rowsOf u, r < I.nrows := fun r hr => I.rowList_lt (I.mem_rowsOf.mp hr)
  rw [problem_rowsOf I hu]
  have hone : ∀ r ∈ Finset.range (problem I).nrows,
      (if (I.rowsOf u).contains r then (problem I).bhat.getD r 0 else 0)
        = (if (I.rowsOf u).contains r then (1 : Int) else 0) := by
    intro r hr
    rw [problem_bhat I (by simpa using hr)]
  rw [Finset.sum_congr rfl hone]
  show ∑ r ∈ Finset.range I.nrows, (if (I.rowsOf u).contains r then (1 : Int) else 0) = _
  rw [sum_indicator_weighted (N := I.nrows) (I.rowsOf u) (fun _ => (1 : Int)) hnd hlt,
    Array.foldl_add_eq_sum (I.rowsOf u) (fun _ => (1 : Int)) 0]
  simp

/-- **The colouring QUBO is a well-formed 0/1 QUBO.** -/
theorem problem_wf : (problem I).Wf where
  nodup := fun u hu => by
    rw [problem_rowsOf I hu]
    simpa [Instance.rowsOf] using I.rowList_nodup u
  mem_lt := fun u hu r hr => by
    rw [problem_rowsOf I hu] at hr
    exact I.rowList_lt (I.mem_rowsOf.mp hr)
  theta_eq := fun u hu => by
    rw [problem_theta I hu, sum_bhat_indicator I hu, problem_rowsOf I hu, I.rowsOf_size]
    ring
  const_eq := by
    show (I.nbase : Int) = ∑ r ∈ Finset.range I.nrows, (problem I).bhat.getD r 0 ^ 2
    rw [Finset.sum_congr rfl (fun r hr => by rw [problem_bhat I (by simpa using hr)])]
    simp [Instance.nrows]

/-! ## A zero penalty satisfies every row

`penaltyDoubled` is a fold of squares over the row indices, so it vanishes only if each residual
does. This part is about an arbitrary `Problem`. -/

private theorem foldl_add_eq_zero_iff (f : Nat → Int) (hf : ∀ r, 0 ≤ f r) :
    ∀ (l : List Nat) (acc : Int), 0 ≤ acc →
      (l.foldl (fun a r => a + f r) acc = 0 ↔ acc = 0 ∧ ∀ r ∈ l, f r = 0) := by
  intro l
  induction l with
  | nil => intro acc _; simp
  | cons r rest ih =>
    intro acc hacc
    have hfr : 0 ≤ f r := hf r
    have hstep : 0 ≤ acc + f r := by omega
    rw [List.foldl_cons, ih (acc + f r) hstep]
    constructor
    · rintro ⟨hz, hall⟩
      refine ⟨by omega, ?_⟩
      intro w hw
      rcases List.mem_cons.mp hw with rfl | hw'
      · omega
      · exact hall w hw'
    · rintro ⟨hacc0, hall⟩
      have hr0 : f r = 0 := hall r (List.mem_cons_self ..)
      exact ⟨by omega, fun w hw => hall w (List.mem_cons_of_mem _ hw)⟩

/-- **A zero objective means every constraint row is met exactly.** -/
theorem penalty_zero_row (P : Problem) {x : Array Bool} (h : P.penaltyDoubled x = 0)
    {r : Nat} (hr : r < P.nrows) : (P.rowSums x).getD r 0 = P.bhat.getD r 0 := by
  set d : Nat → Int := fun s => (P.rowSums x).getD s 0 - P.bhat.getD s 0 with hd
  have hf : ∀ s, 0 ≤ d s * d s := fun s => mul_self_nonneg _
  have hrw : P.penaltyDoubled x = (Array.range P.nrows).foldl (fun a s => a + d s * d s) 0 := rfl
  rw [hrw, ← Array.foldl_toList, Array.toList_range] at h
  have hall := (foldl_add_eq_zero_iff (fun s => d s * d s) hf _ 0 (le_refl 0)).mp h
  have hzero : d r * d r = 0 := hall.2 r (List.mem_range.mpr hr)
  have hdr : d r = 0 := by rcases mul_eq_zero.mp hzero with h1 | h1 <;> exact h1
  simp only [hd] at hdr
  omega

/-- **The converse: meeting every row exactly makes the objective vanish.**

Each residual is zero, hence so is each square, hence so is the fold. This is the half
completeness needs; `penalty_zero_row` is the half soundness needs. Also about an arbitrary
`Problem`. -/
theorem penalty_zero_of_rowSums (P : Problem) {x : Array Bool}
    (h : ∀ r < P.nrows, (P.rowSums x).getD r 0 = P.bhat.getD r 0) :
    P.penaltyDoubled x = 0 := by
  have hf : ∀ s : Nat, 0 ≤ ((P.rowSums x).getD s 0 - P.bhat.getD s 0)
      * ((P.rowSums x).getD s 0 - P.bhat.getD s 0) := fun _ => mul_self_nonneg _
  have hrw : P.penaltyDoubled x = (Array.range P.nrows).foldl
      (fun a s => a + ((P.rowSums x).getD s 0 - P.bhat.getD s 0)
        * ((P.rowSums x).getD s 0 - P.bhat.getD s 0)) 0 := rfl
  rw [hrw, ← Array.foldl_toList, Array.toList_range]
  refine (foldl_add_eq_zero_iff _ hf _ 0 (le_refl 0)).mpr ⟨rfl, fun r hr => ?_⟩
  rw [h r (List.mem_range.mp hr)]
  ring

/-! ## Decoding

`hitsAt x v` lists the colours `v` is assigned by `x`; the vertex row forces the list to be a
singleton, and the decoder reads its head. -/

namespace Instance

/-- The colours `x` gives to vertex `v`. -/
def hitsAt (I : Instance) (x : Array Bool) (v : Nat) : List Nat :=
  (List.range I.ncolours).filter fun i => x.getD (I.colVar v i) false

/-- **The decoder**: one colour per vertex, `ncolours` (an illegal value) if the bit vector
gives that vertex none. -/
def decode (I : Instance) (x : Array Bool) : Array Nat :=
  (Array.range I.nverts).map fun v => (I.hitsAt x v).headD I.ncolours

/-- **The checker**: one legal colour per vertex, and no monochromatic edge. -/
def isColouring (I : Instance) (col : Array Nat) : Bool :=
  (col.size == I.nverts)
    && ((List.range I.nverts).all fun v => col.getD v I.ncolours < I.ncolours)
    && I.edges.toList.all fun e => col.getD e.1 I.ncolours != col.getD e.2 I.ncolours

/-- The instances the encoding is faithful on: a simple graph with endpoints in range. A loop
`(v,v)` is invisible to the encoding — the two occurrences of `x_{v,i}` in its row collapse to
one, since `Â` is `0/1` — and no colouring can satisfy it, so it is excluded. -/
def edgesOk (I : Instance) : Bool :=
  I.edges.toList.all fun e => (e.1 < I.nverts) && (e.2 < I.nverts) && (e.1 != e.2)

/-- The set variables of one row. -/
def hitList (I : Instance) (x : Array Bool) (r : Nat) : List Nat :=
  (List.range I.nvars).filter fun u => x.getD u false && (I.rowsOf u).contains r

theorem mem_hitList {I : Instance} {x : Array Bool} {r u : Nat} :
    u ∈ I.hitList x r
      ↔ u < I.nvars ∧ x.getD u false = true ∧ (I.rowsOf u).contains r = true := by
  simp [hitList, List.mem_filter, List.mem_range]

theorem decode_getD (I : Instance) (x : Array Bool) {v : Nat} (hv : v < I.nverts) :
    (I.decode x).getD v I.ncolours = (I.hitsAt x v).headD I.ncolours := by
  show ((Array.range I.nverts).map fun v => (I.hitsAt x v).headD I.ncolours).getD v _ = _
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa using hv)]
  simp

theorem decode_size (I : Instance) (x : Array Bool) : (I.decode x).size = I.nverts := by
  simp [decode]

theorem hitList_nodup (I : Instance) (x : Array Bool) (r : Nat) : (I.hitList x r).Nodup :=
  List.Nodup.filter _ List.nodup_range

/-! ### Reading the checker -/

/-- The size of a checked colouring. -/
theorem isColouring_size {I : Instance} {col : Array Nat} (h : I.isColouring col = true) :
    col.size = I.nverts := by
  simp only [isColouring, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1

/-- A checked colouring gives every vertex a colour from the palette. -/
theorem isColouring_lt {I : Instance} {col : Array Nat} (h : I.isColouring col = true) {v : Nat}
    (hv : v < I.nverts) : col.getD v I.ncolours < I.ncolours := by
  simp only [isColouring, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  exact h.1.2 v hv

/-- A checked colouring is proper. -/
theorem isColouring_edge {I : Instance} {col : Array Nat} (h : I.isColouring col = true)
    {p : Nat × Nat} (hp : p ∈ I.edges.toList) :
    col.getD p.1 I.ncolours ≠ col.getD p.2 I.ncolours := by
  simp only [isColouring, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq] at h
  exact h.2 p hp

/-- A checked instance has both endpoints of every edge in range. -/
theorem edgesOk_lt {I : Instance} (hE : I.edgesOk = true) {p : Nat × Nat}
    (hp : p ∈ I.edges.toList) : p.1 < I.nverts ∧ p.2 < I.nverts := by
  have h := (List.all_eq_true.mp hE) p hp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

end Instance

/-- **Every row of a zero-penalty vector holds exactly one set variable.** -/
theorem hitList_length (I : Instance) {x : Array Bool}
    (hx : (problem I).penaltyDoubled x = 0) {r : Nat} (hr : r < I.nrows) :
    (I.hitList x r).length = 1 := by
  have h := penalty_zero_row (problem I) hx (r := r) hr
  rw [rowSums_spec (problem I) (problem_wf I) x hr, problem_bhat I hr] at h
  have hcp : ((List.range I.nvars).countP
      fun u => x.getD u false && ((problem I).rowsOf.getD u #[]).contains r) = 1 := by
    exact_mod_cast h
  rw [List.countP_eq_length_filter] at hcp
  rw [Instance.hitList,
    List.filter_congr (q := fun u => x.getD u false && ((problem I).rowsOf.getD u #[]).contains r)
      (fun u hu => by rw [problem_rowsOf I (List.mem_range.mp hu)])]
  exact hcp

/-- Two set variables in the same row of a zero-penalty vector are the same variable. -/
theorem hitList_unique (I : Instance) {x : Array Bool}
    (hx : (problem I).penaltyDoubled x = 0) {r : Nat} (hr : r < I.nrows) {u w : Nat}
    (hu : u ∈ I.hitList x r) (hw : w ∈ I.hitList x r) : u = w := by
  obtain ⟨c, hc⟩ := List.length_eq_one_iff.mp (hitList_length I hx hr)
  rw [hc, List.mem_singleton] at hu hw
  rw [hu, hw]

/-- Every row of a zero-penalty vector holds a set variable. -/
theorem hitList_exists (I : Instance) {x : Array Bool}
    (hx : (problem I).penaltyDoubled x = 0) {r : Nat} (hr : r < I.nrows) :
    ∃ u, u ∈ I.hitList x r := by
  obtain ⟨c, hc⟩ := List.length_eq_one_iff.mp (hitList_length I hx hr)
  exact ⟨c, by rw [hc]; exact List.mem_singleton_self c⟩

/-! ## Soundness of the decoder -/

/-- **The decoded colour of a vertex is one the bit vector actually gives it.**

The vertex row `Σ_i x_{v,i} = 1` is met, and its only variables are the colour variables of `v`,
so `hitsAt` is nonempty and its head is a colour of `v`. -/
theorem decode_mem_hitsAt (I : Instance) (hc : 0 < I.ncolours) {x : Array Bool}
    (hx : (problem I).penaltyDoubled x = 0) {v : Nat} (hv : v < I.nverts) :
    (I.decode x).getD v I.ncolours ∈ I.hitsAt x v := by
  have hvb : v < I.nbase := by simp only [Instance.nbase]; omega
  have hvr : v < I.nrows := by simp only [Instance.nrows]; omega
  obtain ⟨u, hu⟩ := hitList_exists I hx hvr
  obtain ⟨hult, hux, hurow⟩ := Instance.mem_hitList.mp hu
  obtain ⟨hcol, hdiv⟩ := (I.baseInRow_vertex hv).mp ((I.contains_base hvb).mp hurow)
  have hmod : u % I.ncolours < I.ncolours := Nat.mod_lt _ hc
  have hpack : I.colVar v (u % I.ncolours) = u := by
    simp only [Instance.colVar, ← hdiv]
    exact Nat.div_add_mod u I.ncolours
  have hin : u % I.ncolours ∈ I.hitsAt x v := by
    simp only [Instance.hitsAt, List.mem_filter, List.mem_range, hpack]
    exact ⟨hmod, hux⟩
  rw [I.decode_getD x hv]
  cases hl : I.hitsAt x v with
  | nil => rw [hl] at hin; cases hin
  | cons a t => simp

/-- The decoded colour is a legal colour. -/
theorem decode_lt (I : Instance) (hc : 0 < I.ncolours) {x : Array Bool}
    (hx : (problem I).penaltyDoubled x = 0) {v : Nat} (hv : v < I.nverts) :
    (I.decode x).getD v I.ncolours < I.ncolours := by
  have := decode_mem_hitsAt I hc hx hv
  simp only [Instance.hitsAt, List.mem_filter, List.mem_range] at this
  exact this.1

/-- The bit vector sets the variable the decoded colour names. -/
theorem decode_set (I : Instance) (hc : 0 < I.ncolours) {x : Array Bool}
    (hx : (problem I).penaltyDoubled x = 0) {v : Nat} (hv : v < I.nverts) :
    x.getD (I.colVar v ((I.decode x).getD v I.ncolours)) false = true := by
  have := decode_mem_hitsAt I hc hx hv
  simp only [Instance.hitsAt, List.mem_filter, List.mem_range] at this
  exact this.2

/-- **No edge of the decoded colouring is monochromatic.**

If both endpoints took colour `i`, the two colour variables `x_{u,i}` and `x_{v,i}` would both
sit in the edge row `x_{u,i} + x_{v,i} + s_{e,i} = 1` and both be set, so that row would hold two
set variables rather than one. -/
theorem decode_edge (I : Instance) (hc : 0 < I.ncolours) (hE : I.edgesOk = true)
    {x : Array Bool} (hx : (problem I).penaltyDoubled x = 0) {p : Nat × Nat}
    (hp : p ∈ I.edges.toList) :
    (I.decode x).getD p.1 I.ncolours ≠ (I.decode x).getD p.2 I.ncolours := by
  have hok := (List.all_eq_true.mp hE) p hp
  simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hok
  obtain ⟨⟨h1, h2⟩, hne⟩ := hok
  obtain ⟨e, he, hee⟩ := Array.getElem_of_mem (Array.mem_toList_iff.mp hp)
  have hpe : I.edges[e]? = some p := by rw [Array.getElem?_eq_getElem he, hee]
  intro heq
  set i := (I.decode x).getD p.1 I.ncolours with hi
  have hilt : i < I.ncolours := decode_lt I hc hx h1
  have hset1 : x.getD (I.colVar p.1 i) false = true := decode_set I hc hx h1
  have hset2 : x.getD (I.colVar p.2 i) false = true := by
    have := decode_set I hc hx h2
    rwa [← heq] at this
  have herow : I.edgeRow e i < I.nbase := I.edgeRow_lt (by simpa [Instance.nedges] using he) hilt
  have herows : I.edgeRow e i < I.nrows := by simp only [Instance.nrows]; omega
  have hmem1 : I.colVar p.1 i ∈ I.hitList x (I.edgeRow e i) :=
    Instance.mem_hitList.mpr ⟨I.colVar_lt_nvars h1 hilt, hset1,
      (I.contains_base herow).mpr (I.baseInRow_edge hc h1 hilt hpe (Or.inl rfl))⟩
  have hmem2 : I.colVar p.2 i ∈ I.hitList x (I.edgeRow e i) :=
    Instance.mem_hitList.mpr ⟨I.colVar_lt_nvars h2 hilt, hset2,
      (I.contains_base herow).mpr (I.baseInRow_edge hc h2 hilt hpe (Or.inr rfl))⟩
  have := hitList_unique I hx herows hmem1 hmem2
  simp only [Instance.colVar] at this
  exact hne (Nat.eq_of_mul_eq_mul_left hc (by omega))

/-- **Soundness of the encoding.**

A zero of the QUBO decodes to a proper `n`-colouring of the graph. With `QUBO.Net`'s energy
bridge this says the ground states of the Hopfield/Boltzmann network built from `problem I` are
exactly the `n`-colourings of `I`. -/
theorem decode_isColouring (I : Instance) (hc : 0 < I.ncolours) (hE : I.edgesOk = true)
    {x : Array Bool} (hx : (problem I).penaltyDoubled x = 0) :
    I.isColouring (I.decode x) = true := by
  simp only [Instance.isColouring, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    List.mem_range, decide_eq_true_eq, bne_iff_ne, ne_eq]
  exact ⟨⟨I.decode_size x, fun v hv => decode_lt I hc hx hv⟩,
    fun p hp => decode_edge I hc hE hx hp⟩

/-! ## Completeness: a colouring *is* a zero

`decode_isColouring` says a zero of the objective is a colouring. This section proves the
converse — a colouring encodes to a zero — which is what turns the encoding from a sound
reduction into a decision procedure: `exists_zero_iff_colourable` below.

The encoder is the obvious one on the colour variables, `x_{v,i} = [col v = i]`, and on a slack
takes the only value that can close its row, `s_{e,i} = [col u ≠ i ∧ col v ≠ i]`. Row by row:

* the vertex row `Σ_i x_{v,i} = 1` holds because `col v` is one legal colour, so exactly one of
  the `n` colour variables of `v` is set;
* the edge row `x_{u,i} + x_{v,i} + s_{e,i} = 1` holds because `col u ≠ col v`, so *at most* one
  endpoint carries colour `i`, and the slack supplies the missing `1` exactly when neither does.

The work is in "exactly one", i.e. in knowing every variable of a row: that is
`baseInRow_edgeRow` (the converse of `baseInRow_edge`). -/

namespace Instance

/-- **The encoder.** Colour variables read off `col`; each slack takes the value that closes its
edge row, i.e. `s_{e,i} = 1` exactly when neither endpoint of `e` has colour `i`. -/
def encode (I : Instance) (col : Array Nat) : Array Bool :=
  (Array.range I.nvars).map fun u =>
    if u < I.ncolVars then col.getD (u / I.ncolours) I.ncolours == u % I.ncolours
    else
      match I.edges[(u - I.ncolVars) / I.ncolours]? with
      | none => false
      | some p =>
          (col.getD p.1 I.ncolours != (u - I.ncolVars) % I.ncolours)
            && (col.getD p.2 I.ncolours != (u - I.ncolVars) % I.ncolours)

theorem encode_getD (I : Instance) (col : Array Nat) {u : Nat} (hu : u < I.nvars) :
    (I.encode col).getD u false =
      (if u < I.ncolVars then col.getD (u / I.ncolours) I.ncolours == u % I.ncolours
       else
         match I.edges[(u - I.ncolVars) / I.ncolours]? with
         | none => false
         | some p =>
             (col.getD p.1 I.ncolours != (u - I.ncolVars) % I.ncolours)
               && (col.getD p.2 I.ncolours != (u - I.ncolVars) % I.ncolours)) := by
  show ((Array.range I.nvars).map _).getD u false = _
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa using hu)]
  simp only [Option.getD_some, Array.getElem_map, Array.getElem_range]

/-- `x_{v,i} = 1` iff `col v = i`. -/
theorem encode_colVar (I : Instance) (col : Array Nat) {v i : Nat} (hc : 0 < I.ncolours)
    (hv : v < I.nverts) (hi : i < I.ncolours) :
    (I.encode col).getD (I.colVar v i) false = (col.getD v I.ncolours == i) := by
  rw [I.encode_getD col (I.colVar_lt_nvars hv hi), if_pos (I.colVar_lt hv hi)]
  simp only [colVar]
  rw [I.div_pack hc hi, I.mod_pack hc hi]

/-- `s_{e,i} = 1` iff neither endpoint of `e` has colour `i`. -/
theorem encode_slackVar (I : Instance) (col : Array Nat) {e i : Nat} (hc : 0 < I.ncolours)
    (he : e < I.nedges) (hi : i < I.ncolours) {p : Nat × Nat} (hp : I.edges[e]? = some p) :
    (I.encode col).getD (I.slackVar e i) false =
      ((col.getD p.1 I.ncolours != i) && (col.getD p.2 I.ncolours != i)) := by
  have hnot : ¬ (I.slackVar e i < I.ncolVars) := by simp only [slackVar]; omega
  have hsub : I.slackVar e i - I.ncolVars = I.ncolours * e + i := by simp only [slackVar]; omega
  rw [I.encode_getD col (I.slackVar_lt_nvars he hi), if_neg hnot, hsub,
    I.div_pack hc hi, I.mod_pack hc hi, hp]

end Instance

/-- A duplicate-free list all of whose elements equal one of its members is a singleton. -/
private theorem length_eq_one_of_all_eq : ∀ (L : List Nat), L.Nodup → ∀ a, a ∈ L →
    (∀ b ∈ L, b = a) → L.length = 1 := by
  intro L
  match L with
  | [] => intro _ a ha _; exact absurd ha (by simp)
  | [_] => intro _ _ _ _; rfl
  | b :: c :: t =>
    intro hnd a _ hall
    have hb : b = a := hall b (by simp)
    have hc : c = a := hall c (by simp)
    exact absurd (show b ∈ c :: t by rw [hb, ← hc]; exact List.mem_cons_self ..)
      ((List.nodup_cons.mp hnd).1)

/-- …and it is the singleton on that member. -/
private theorem eq_singleton_of_all_eq {L : List Nat} (hnd : L.Nodup) {a : Nat} (ha : a ∈ L)
    (hall : ∀ b ∈ L, b = a) : L = [a] := by
  obtain ⟨c, hc⟩ := List.length_eq_one_iff.mp (length_eq_one_of_all_eq L hnd a ha hall)
  rw [hc] at ha ⊢
  rw [List.mem_singleton] at ha
  rw [ha]

/-- **The vertex row of an encoded colouring holds exactly one set variable**, namely
`x_{v, col v}`: the row sees only the colour variables of `v`, and `col v` is the one colour
`col` gives it. -/
theorem encode_hitList_vertex (I : Instance) {col : Array Nat} (hcol : I.isColouring col = true)
    {v : Nat} (hv : v < I.nverts) : (I.hitList (I.encode col) v).length = 1 := by
  have hcv : col.getD v I.ncolours < I.ncolours := Instance.isColouring_lt hcol hv
  have hc : 0 < I.ncolours := by omega
  have hvb : v < I.nbase := by simp only [Instance.nbase]; omega
  refine length_eq_one_of_all_eq _ (I.hitList_nodup _ v) (I.colVar v (col.getD v I.ncolours))
    ?_ ?_
  · refine Instance.mem_hitList.mpr ⟨I.colVar_lt_nvars hv hcv, ?_, ?_⟩
    · rw [I.encode_colVar col hc hv hcv]; simp
    · exact (I.contains_base hvb).mpr
        ((I.baseInRow_vertex hv).mpr ⟨I.colVar_lt hv hcv, I.div_pack hc hcv⟩)
  · intro b hb
    obtain ⟨hblt, hbx, hbrow⟩ := Instance.mem_hitList.mp hb
    obtain ⟨hbcol, hbdiv⟩ := (I.baseInRow_vertex hv).mp ((I.contains_base hvb).mp hbrow)
    have hmod : b % I.ncolours < I.ncolours := Nat.mod_lt _ hc
    have hbeq : I.colVar v (b % I.ncolours) = b := by
      simp only [Instance.colVar, ← hbdiv]
      exact Nat.div_add_mod b I.ncolours
    rw [← hbeq, I.encode_colVar col hc hv hmod] at hbx
    simp only [beq_iff_eq] at hbx
    rw [← hbeq, hbx]

/-- **The edge row of an encoded colouring holds exactly one set variable.**

`col p.1 ≠ col p.2`, so of the three variables of the row `x_{p.1,i} + x_{p.2,i} + s_{e,i} = 1`
the first is set iff `col p.1 = i`, the second iff `col p.2 = i` — never both — and the slack iff
neither. Exactly one of the three cases occurs. -/
theorem encode_hitList_edge (I : Instance) (hE : I.edgesOk = true) {col : Array Nat}
    (hcol : I.isColouring col = true) {e i : Nat} (he : e < I.nedges) (hi : i < I.ncolours) :
    (I.hitList (I.encode col) (I.edgeRow e i)).length = 1 := by
  have hc : 0 < I.ncolours := by omega
  have he' : e < I.edges.size := by simpa [Instance.nedges] using he
  obtain ⟨p, hp, hpmem⟩ : ∃ p, I.edges[e]? = some p ∧ p ∈ I.edges.toList :=
    ⟨I.edges[e], Array.getElem?_eq_getElem he', Array.mem_toList_iff.mpr (Array.getElem_mem he')⟩
  obtain ⟨h1, h2⟩ := Instance.edgesOk_lt hE hpmem
  have hne := Instance.isColouring_edge hcol hpmem
  have herow : I.edgeRow e i < I.nbase := I.edgeRow_lt he hi
  have hchar : ∀ b, b ∈ I.hitList (I.encode col) (I.edgeRow e i) ↔
      ((b = I.colVar p.1 i ∧ col.getD p.1 I.ncolours = i)
        ∨ (b = I.colVar p.2 i ∧ col.getD p.2 I.ncolours = i)
        ∨ (b = I.slackVar e i ∧ col.getD p.1 I.ncolours ≠ i
            ∧ col.getD p.2 I.ncolours ≠ i)) := by
    intro b
    rw [Instance.mem_hitList]
    constructor
    · rintro ⟨hblt, hbx, hbrow⟩
      rcases (I.baseInRow_edgeRow hc hi hp).mp ((I.contains_base herow).mp hbrow) with
        ⟨hbc, hbm, hbd⟩ | hbs
      · have hbeq : I.colVar (b / I.ncolours) i = b := by
          simp only [Instance.colVar, ← hbm]
          exact Nat.div_add_mod b I.ncolours
        rcases hbd with hd | hd
        · have hb' : b = I.colVar p.1 i := by rw [hd]; exact hbeq.symm
          rw [hb', I.encode_colVar col hc h1 hi] at hbx
          simp only [beq_iff_eq] at hbx
          exact Or.inl ⟨hb', hbx⟩
        · have hb' : b = I.colVar p.2 i := by rw [hd]; exact hbeq.symm
          rw [hb', I.encode_colVar col hc h2 hi] at hbx
          simp only [beq_iff_eq] at hbx
          exact Or.inr (Or.inl ⟨hb', hbx⟩)
      · rw [hbs, I.encode_slackVar col hc he hi hp] at hbx
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hbx
        exact Or.inr (Or.inr ⟨hbs, hbx.1, hbx.2⟩)
    · rintro (⟨rfl, hval⟩ | ⟨rfl, hval⟩ | ⟨rfl, hv1, hv2⟩)
      · exact ⟨I.colVar_lt_nvars h1 hi, by rw [I.encode_colVar col hc h1 hi, hval]; simp,
          (I.contains_base herow).mpr (I.baseInRow_edge hc h1 hi hp (Or.inl rfl))⟩
      · exact ⟨I.colVar_lt_nvars h2 hi, by rw [I.encode_colVar col hc h2 hi, hval]; simp,
          (I.contains_base herow).mpr (I.baseInRow_edge hc h2 hi hp (Or.inr rfl))⟩
      · refine ⟨I.slackVar_lt_nvars he hi, ?_,
          (I.contains_base herow).mpr I.baseInRow_slack⟩
        rw [I.encode_slackVar col hc he hi hp]
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq]
        exact ⟨hv1, hv2⟩
  by_cases hA : col.getD p.1 I.ncolours = i
  · refine length_eq_one_of_all_eq _ (I.hitList_nodup _ _) (I.colVar p.1 i)
      ((hchar _).mpr (Or.inl ⟨rfl, hA⟩)) ?_
    intro b hb
    rcases (hchar b).mp hb with ⟨hb', -⟩ | ⟨-, hB⟩ | ⟨-, hn1, -⟩
    · exact hb'
    · exact absurd (hA.trans hB.symm) hne
    · exact absurd hA hn1
  · by_cases hB : col.getD p.2 I.ncolours = i
    · refine length_eq_one_of_all_eq _ (I.hitList_nodup _ _) (I.colVar p.2 i)
        ((hchar _).mpr (Or.inr (Or.inl ⟨rfl, hB⟩))) ?_
      intro b hb
      rcases (hchar b).mp hb with ⟨-, hA'⟩ | ⟨hb', -⟩ | ⟨-, -, hn2⟩
      · exact absurd hA' hA
      · exact hb'
      · exact absurd hB hn2
    · refine length_eq_one_of_all_eq _ (I.hitList_nodup _ _) (I.slackVar e i)
        ((hchar _).mpr (Or.inr (Or.inr ⟨rfl, hA, hB⟩))) ?_
      intro b hb
      rcases (hchar b).mp hb with ⟨-, hA'⟩ | ⟨-, hB'⟩ | ⟨hb', -, -⟩
      · exact absurd hA' hA
      · exact absurd hB' hB
      · exact hb'

/-- **Every row of an encoded colouring holds exactly one set variable**: the vertex rows and the
edge rows are the two cases above. -/
theorem encode_hitList_length (I : Instance) (hE : I.edgesOk = true) {col : Array Nat}
    (hcol : I.isColouring col = true) {r : Nat} (hr : r < I.nrows) :
    (I.hitList (I.encode col) r).length = 1 := by
  have hr' : r < I.nbase := by simpa only [Instance.nrows] using hr
  rcases Nat.lt_or_ge r I.nverts with h | h
  · exact encode_hitList_vertex I hcol h
  · obtain ⟨e, i, he, hi, rfl⟩ := I.eq_edgeRow h hr'
    exact encode_hitList_edge I hE hcol he hi

/-- **An encoded colouring meets every row exactly**: `ρ_r = 1 = b̂_r`. -/
theorem encode_rowSum (I : Instance) (hE : I.edgesOk = true) {col : Array Nat}
    (hcol : I.isColouring col = true) {r : Nat} (hr : r < I.nrows) :
    ((problem I).rowSums (I.encode col)).getD r 0 = (problem I).bhat.getD r 0 := by
  rw [rowSums_spec (problem I) (problem_wf I) _ hr, problem_bhat I hr]
  have hcount : ((List.range I.nvars).countP
      fun u => (I.encode col).getD u false
        && ((problem I).rowsOf.getD u #[]).contains r) = 1 := by
    rw [List.countP_eq_length_filter,
      List.filter_congr (q := fun u => (I.encode col).getD u false && (I.rowsOf u).contains r)
        (fun u hu => by rw [problem_rowsOf I (List.mem_range.mp hu)])]
    exact encode_hitList_length I hE hcol hr
  exact_mod_cast hcount

/-- **Completeness of the encoding.**

A proper `n`-colouring of `I` encodes to a zero of the objective. Together with
`decode_isColouring` this makes the QUBO an exact reduction, not merely a sound one: the only
hypothesis is `edgesOk`, i.e. that the edge list names real vertices, and `isColouring col`
itself rules out loops. In particular no lower bound on `ncolours` or `nverts` is needed. -/
theorem encode_penalty_zero (I : Instance) (hE : I.edgesOk = true) {col : Array Nat}
    (hcol : I.isColouring col = true) :
    (problem I).penaltyDoubled (I.encode col) = 0 :=
  penalty_zero_of_rowSums (problem I) fun _ hr => encode_rowSum I hE hcol hr

/-- **The round trip.** `encode` and `decode` are mutually inverse on colourings: decoding an
encoded colouring returns it on the nose. (Not needed for the equivalence below, which pairs
`encode` with the checker directly, but it says the two directions name the same object.) -/
theorem decode_encode (I : Instance) {col : Array Nat} (hcol : I.isColouring col = true) :
    I.decode (I.encode col) = col := by
  have hgetD : ∀ (a : Array Nat) (j d : Nat) (hj : j < a.size), a.getD j d = a[j] := by
    intro a j d hj
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj]
    rfl
  have hsize : (I.decode (I.encode col)).size = col.size := by
    rw [I.decode_size, Instance.isColouring_size hcol]
  refine Array.ext hsize ?_
  intro v hv1 hv2
  have hv : v < I.nverts := by rw [I.decode_size] at hv1; exact hv1
  have hcv : col.getD v I.ncolours < I.ncolours := Instance.isColouring_lt hcol hv
  have hc : 0 < I.ncolours := by omega
  have hhits : I.hitsAt (I.encode col) v = [col.getD v I.ncolours] := by
    refine eq_singleton_of_all_eq (List.Nodup.filter _ List.nodup_range) ?_ ?_
    · simp only [List.mem_filter, List.mem_range]
      exact ⟨hcv, by rw [I.encode_colVar col hc hv hcv]; simp⟩
    · intro b hb
      simp only [List.mem_filter, List.mem_range] at hb
      rw [I.encode_colVar col hc hv hb.1] at hb
      exact (beq_iff_eq.mp hb.2).symm
  rw [← hgetD _ _ I.ncolours hv1, ← hgetD _ _ I.ncolours hv2, I.decode_getD _ hv, hhits]
  rfl

/-- **The headline: the QUBO has a zero exactly when the graph is `n`-colourable.**

Left to right is `decode_isColouring`, right to left is `encode_penalty_zero`. So a solver
report of "no zero" is a proof of non-colourability, which is what `triangle_not_two_colourable`
and `k4_not_three_colourable` below extract. -/
theorem exists_zero_iff_colourable (I : Instance) (hc : 0 < I.ncolours) (hE : I.edgesOk = true) :
    (∃ x, (problem I).penaltyDoubled x = 0) ↔ (∃ col, I.isColouring col = true) :=
  ⟨fun ⟨_, hx⟩ => ⟨_, decode_isColouring I hc hE hx⟩,
   fun ⟨_, hcol⟩ => ⟨_, encode_penalty_zero I hE hcol⟩⟩

/-- **The empty palette is not a real exception.** `decode_isColouring` needs `0 < ncolours` to
name a colour; with no colours at all a zero still forces the graph to be colourable, because
then there are no variables, so a vertex row cannot be met and there can be no vertex either —
and the empty colouring of the empty graph is proper. -/
theorem colourable_of_zero (I : Instance) (hE : I.edgesOk = true) {x : Array Bool}
    (hx : (problem I).penaltyDoubled x = 0) : ∃ col, I.isColouring col = true := by
  rcases Nat.eq_zero_or_pos I.ncolours with hc | hc
  · rcases Nat.eq_zero_or_pos I.nverts with hv | hv
    · refine ⟨#[], ?_⟩
      simp only [Instance.isColouring, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
        List.mem_range, decide_eq_true_eq, bne_iff_ne, ne_eq]
      exact ⟨⟨by simp [hv], fun v hvlt => absurd hvlt (by omega)⟩,
        fun p hp => absurd (Instance.edgesOk_lt hE hp).1 (by omega)⟩
    · exfalso
      have hr : 0 < I.nrows := by
        simp only [Instance.nrows, Instance.nbase, hc, Nat.zero_mul]; omega
      obtain ⟨u, hu⟩ := hitList_exists I hx hr
      have hult := (Instance.mem_hitList.mp hu).1
      simp only [Instance.nvars, hc, Nat.zero_mul] at hult
      omega
  · exact ⟨I.decode x, decode_isColouring I hc hE hx⟩

/-- The equivalence with no hypothesis on the palette: for any instance whose edges name real
vertices, the QUBO has a zero iff the graph is colourable. -/
theorem exists_zero_iff_colourable' (I : Instance) (hE : I.edgesOk = true) :
    (∃ x, (problem I).penaltyDoubled x = 0) ↔ (∃ col, I.isColouring col = true) :=
  ⟨fun ⟨_, hx⟩ => colourable_of_zero I hE hx,
   fun ⟨_, hcol⟩ => ⟨_, encode_penalty_zero I hE hcol⟩⟩

/-! ## Worked examples

A triangle is 3-colourable but not 2-colourable, and `K₄` is not 3-colourable. The positive
direction is exhibited by an explicit bit vector; the negative ones are first proved *about the
QUBO* — no bit vector whatever reaches penalty zero — and then, by completeness, transferred to
the graphs themselves. -/

/-- `K₃` with three colours. -/
def triangle : Instance := ⟨3, 3, #[(0, 1), (1, 2), (0, 2)]⟩

/-- `K₃` with two colours — infeasible. -/
def triangle2 : Instance := ⟨3, 2, #[(0, 1), (1, 2), (0, 2)]⟩

/-- `K₄` with three colours — infeasible. -/
def k4 : Instance := ⟨4, 3, #[(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]⟩

-- 18 = 3·3 colour variables + 3·3 slacks, 12 = 3 + 3·3 rows
#eval (triangle.nvars, triangle.nrows)
-- the two column degrees: 1 + deg_G v = 3 for a colour variable, 1 for a slack
#eval ((triangle.rowsOf (triangle.colVar 0 0)).size, (triangle.rowsOf (triangle.slackVar 0 0)).size)
-- a proper 3-colouring of the triangle is a zero of the objective, and decodes back to itself
#eval (problem triangle).penaltyDoubled (triangle.encode #[0, 1, 2])   -- 0
#eval triangle.decode (triangle.encode #[0, 1, 2])                      -- #[0, 1, 2]
-- a monochromatic edge is not
#eval (problem triangle).penaltyDoubled (triangle.encode #[0, 1, 0])   -- 1

/-- The incidence is *not* regular: a colour variable of the triangle has degree `3`, a slack
degree `1` — and both are odd, which is exactly what the doubled `theta` field and the
degree-free `Wf.theta_eq` buy. -/
example : (triangle.rowsOf (triangle.colVar 0 0)).size = 3
    ∧ (triangle.rowsOf (triangle.slackVar 0 0)).size = 1 := by decide

/-- `#[0,1,2]` is a proper colouring of the triangle and `#[0,1,0]` is not. -/
example : triangle.isColouring #[0, 1, 2] = true := by decide

example : triangle.isColouring #[0, 1, 0] = false := by decide

/-- Both example instances are simple graphs with endpoints in range. -/
example : triangle.edgesOk = true ∧ triangle2.edgesOk = true ∧ k4.edgesOk = true := by decide

/-- **The triangle is not 2-colourable, as a statement about the QUBO**: *no* bit vector at all
reaches penalty zero in the two-colour encoding. -/
theorem triangle2_no_zero (x : Array Bool) : (problem triangle2).penaltyDoubled x ≠ 0 := by
  intro h
  have h0 : (triangle2.decode x).getD 0 triangle2.ncolours < 2 :=
    decode_lt triangle2 (by decide) h (by decide)
  have h1 : (triangle2.decode x).getD 1 triangle2.ncolours < 2 :=
    decode_lt triangle2 (by decide) h (by decide)
  have h2 : (triangle2.decode x).getD 2 triangle2.ncolours < 2 :=
    decode_lt triangle2 (by decide) h (by decide)
  have e01 : (triangle2.decode x).getD 0 triangle2.ncolours
      ≠ (triangle2.decode x).getD 1 triangle2.ncolours :=
    decode_edge triangle2 (by decide) (by decide) h (p := (0, 1)) (by decide)
  have e12 : (triangle2.decode x).getD 1 triangle2.ncolours
      ≠ (triangle2.decode x).getD 2 triangle2.ncolours :=
    decode_edge triangle2 (by decide) (by decide) h (p := (1, 2)) (by decide)
  have e02 : (triangle2.decode x).getD 0 triangle2.ncolours
      ≠ (triangle2.decode x).getD 2 triangle2.ncolours :=
    decode_edge triangle2 (by decide) (by decide) h (p := (0, 2)) (by decide)
  omega

/-- **`K₄` is not 3-colourable, as a statement about the QUBO.** -/
theorem k4_no_zero (x : Array Bool) : (problem k4).penaltyDoubled x ≠ 0 := by
  intro h
  have hlt : ∀ v, v < 4 → (k4.decode x).getD v k4.ncolours < 3 := by
    intro v hv
    exact decode_lt k4 (by decide) h (by simpa [k4] using hv)
  have h0 := hlt 0 (by omega)
  have h1 := hlt 1 (by omega)
  have h2 := hlt 2 (by omega)
  have h3 := hlt 3 (by omega)
  have e01 : (k4.decode x).getD 0 k4.ncolours ≠ (k4.decode x).getD 1 k4.ncolours :=
    decode_edge k4 (by decide) (by decide) h (p := (0, 1)) (by decide)
  have e02 : (k4.decode x).getD 0 k4.ncolours ≠ (k4.decode x).getD 2 k4.ncolours :=
    decode_edge k4 (by decide) (by decide) h (p := (0, 2)) (by decide)
  have e03 : (k4.decode x).getD 0 k4.ncolours ≠ (k4.decode x).getD 3 k4.ncolours :=
    decode_edge k4 (by decide) (by decide) h (p := (0, 3)) (by decide)
  have e12 : (k4.decode x).getD 1 k4.ncolours ≠ (k4.decode x).getD 2 k4.ncolours :=
    decode_edge k4 (by decide) (by decide) h (p := (1, 2)) (by decide)
  have e13 : (k4.decode x).getD 1 k4.ncolours ≠ (k4.decode x).getD 3 k4.ncolours :=
    decode_edge k4 (by decide) (by decide) h (p := (1, 3)) (by decide)
  have e23 : (k4.decode x).getD 2 k4.ncolours ≠ (k4.decode x).getD 3 k4.ncolours :=
    decode_edge k4 (by decide) (by decide) h (p := (2, 3)) (by decide)
  omega

/-! ### …and as statements about the graphs

Completeness turns the two theorems above into theorems about colourings: if the graph had one,
`encode` would give the bit vector the QUBO is proved not to have. Nothing here mentions the
encoding — these are the facts a solver run is now entitled to report. -/

/-- **The triangle is not 2-colourable.** -/
theorem triangle_not_two_colourable : ¬ ∃ col, triangle2.isColouring col = true := by
  rintro ⟨col, hcol⟩
  exact triangle2_no_zero (triangle2.encode col)
    (encode_penalty_zero triangle2 (by decide) hcol)

/-- **`K₄` is not 3-colourable.** -/
theorem k4_not_three_colourable : ¬ ∃ col, k4.isColouring col = true := by
  rintro ⟨col, hcol⟩
  exact k4_no_zero (k4.encode col) (encode_penalty_zero k4 (by decide) hcol)

/-- The same two facts as the failure of the equivalence's right-hand side, i.e. read off
`exists_zero_iff_colourable` rather than from `encode` directly. -/
example : ¬ (∃ col, triangle2.isColouring col = true)
    ∧ ¬ (∃ col, k4.isColouring col = true) :=
  ⟨fun h => triangle2_no_zero _
      ((exists_zero_iff_colourable triangle2 (by decide) (by decide)).mpr h).choose_spec,
   fun h => k4_no_zero _
      ((exists_zero_iff_colourable k4 (by decide) (by decide)).mpr h).choose_spec⟩

/-- The triangle *is* 3-colourable, and the witness is the encoded colouring: the positive side
of `exists_zero_iff_colourable`. -/
theorem triangle_exists_zero : ∃ x, (problem triangle).penaltyDoubled x = 0 :=
  (exists_zero_iff_colourable triangle (by decide) (by decide)).mpr
    ⟨#[0, 1, 2], by decide⟩

/-! ## The network

`QUBO.Net` turns any `Wf` problem into a `{0,1}` Hopfield/Boltzmann network whose energy is the
objective. Instantiated here, the ground states of the triangle's network are its 3-colourings. -/

instance : Nonempty (Fin (problem triangle).nvars) := ⟨⟨0, by decide⟩⟩

/-- **The colouring QUBO is a Hopfield/Boltzmann network**, at the triangle. -/
theorem triangle_zeroOneHamiltonian_eq (x : Fin (problem triangle).nvars → Bool) :
    HopfieldEnergy.zeroOneHamiltonian (netParams (problem triangle))
        (stateOfBits (problem triangle) x)
      = (penaltyR (problem triangle) x - constR (problem triangle)) / 2 :=
  zeroOneHamiltonian_eq (problem triangle) (problem_wf triangle) x

end Colouring
end QUBO
