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

## Relation to Lucas §6.1

Lucas writes

    H = A · Σ_v (1 − Σ_i x_{v,i})² + B · Σ_{(uv) ∈ E} Σ_i x_{u,i} x_{v,i}.

This is *equivalent to*, but not *identical to*, what is built here, in three respects.

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
3. **Every constraint is written twice.** See the parity discussion below. This multiplies the
   objective by `2`; its zero set is unchanged.

## Index layout

Write `N = nverts`, `n = ncolours`, `E = |edges|`. Variables (`nvars = n·N + n·E`):

| range              | name        | index                  |
| ------------------ | ----------- | ---------------------- |
| `v < N`, `i < n`   | `colVar v i`| `n·v + i`              |
| `e < E`, `i < n`   | `slackVar`  | `n·N + n·e + i`        |

Base constraints (`nbase = N + n·E`), each with `b̂ = 1`:

| range              | name         | index            | equation                              |
| ------------------ | ------------ | ---------------- | ------------------------------------- |
| `v < N`            | vertex row   | `v`              | `Σ_i x_{v,i} = 1`                     |
| `e < E`, `i < n`   | `edgeRow e i`| `N + n·e + i`    | `x_{u,i} + x_{v,i} + s_{e,i} = 1`     |

and the real row set is *two* copies of that: row `r` and row `r + nbase` carry the same
equation, so `nrows = 2·nbase`.

## Why the rows are doubled

`Wf.theta_eq` reads `2 θ̂_u = deg(u) − 2 Σ_{r ∋ u} b̂_r`, i.e. `θ̂_u = ½deg(u) − Σ_{r ∋ u} b̂_r`
with `θ̂_u : ℤ`. With `b̂` integral this forces **every column degree to be even** — the `x² = x`
fold that produces `θ̂` divides the diagonal `deg(u)` by two. In the single-copy encoding a
colour variable `(v,i)` has degree `1 + deg_G(v)` and a slack has degree `1`, both odd for most
graphs, so the single-copy encoding is not a `Problem` at all.

Doubling is the minimal repair. A colour variable's degree is
`(#vertex rows for v) + (#edge rows per incident edge)·deg_G(v)`; for this to be even for every
graph the second factor must be even (else the parity tracks `deg_G(v)`, which varies) and then
the first must be even too. Two copies of each row realise both bounds, and the slacks then have
degree `2`. The objective becomes `2‖Âx̂ − b̂‖²` for the single-copy `Â`, with the same zero set.

Note how far the incidence is from regular: colour variables have degree `2(1 + deg_G(v))`,
which varies with `v`, and slacks have degree `2`. The degree-free statement of `Wf.theta_eq` is
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

/-- `N + n·E`: the base constraints, before the rows are doubled. -/
def nbase : Nat := I.nverts + I.ncolours * I.nedges

/-- Twice `nbase`: every constraint is written twice. -/
def nrows : Nat := 2 * I.nbase

/-- The variable "vertex `v` takes colour `i`". -/
def colVar (v i : Nat) : Nat := I.ncolours * v + i

/-- The slack of edge `e` at colour `i`. -/
def slackVar (e i : Nat) : Nat := I.ncolVars + I.ncolours * e + i

/-- The base row `x_{u,i} + x_{v,i} + s_{e,i} = 1` for `e = (u,v)`. -/
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

`baseInRow u r` decides membership of column `u` in base row `r`; the doubled row set is then
`baseRowList` together with its translate by `nbase`. Both are built with `List.filter` over an
index range, never with a scatter loop: `nodup` is then inherited from `List.nodup_range` and
membership is `List.mem_filter`, whereas a `set!` loop could only be characterised by induction
on its trip count. -/

/-- **The base incidence.** For a colour variable `u = n·v + i`: the vertex row `v`, and the edge
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

/-- The base rows of column `u`, as a duplicate-free increasing list. -/
def baseRowList (u : Nat) : List Nat :=
  (List.range I.nbase).filter (fun r => I.baseInRow u r)

/-- The rows of column `u`: the base rows and their translates, since every constraint is
written twice. -/
def rowList (u : Nat) : List Nat :=
  I.baseRowList u ++ (I.baseRowList u).map (· + I.nbase)

/-- The rows of column `u`, as an array — the `rowsOf` of the `Problem` below. -/
def rowsOf (u : Nat) : Array Nat := (I.rowList u).toArray

theorem mem_baseRowList {u r : Nat} :
    r ∈ I.baseRowList u ↔ r < I.nbase ∧ I.baseInRow u r = true := by
  simp [baseRowList, List.mem_filter, List.mem_range]

theorem baseRowList_nodup (u : Nat) : (I.baseRowList u).Nodup :=
  List.Nodup.filter _ (List.nodup_range)

theorem rowList_nodup (u : Nat) : (I.rowList u).Nodup := by
  refine List.Nodup.append (I.baseRowList_nodup u)
    (List.Nodup.map (fun a b h => by omega) (I.baseRowList_nodup u)) ?_
  intro a ha hb
  have h1 : a < I.nbase := ((I.mem_baseRowList).mp ha).1
  obtain ⟨b, hb', rfl⟩ := List.mem_map.mp hb
  omega

theorem rowList_lt {u r : Nat} (hr : r ∈ I.rowList u) : r < I.nrows := by
  rcases List.mem_append.mp hr with h | h
  · have := ((I.mem_baseRowList).mp h).1
    simp only [nrows]; omega
  · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp h
    have := ((I.mem_baseRowList).mp hb).1
    simp only [nrows]; omega

theorem rowsOf_size (u : Nat) : (I.rowsOf u).size = 2 * (I.baseRowList u).length := by
  simp only [rowsOf, rowList, List.size_toArray, List.length_append, List.length_map]
  omega

theorem mem_rowsOf {u r : Nat} : r ∈ I.rowsOf u ↔ r ∈ I.rowList u := by
  simp [rowsOf]

/-- On a base row, membership in the doubled row set is the base incidence. -/
theorem contains_base {u r : Nat} (hr : r < I.nbase) :
    (I.rowsOf u).contains r = true ↔ I.baseInRow u r = true := by
  rw [Array.contains_iff_mem, I.mem_rowsOf, rowList, List.mem_append]
  constructor
  · rintro (h | h)
    · exact ((I.mem_baseRowList).mp h).2
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp h
      omega
  · intro h; exact Or.inl ((I.mem_baseRowList).mpr ⟨hr, h⟩)

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

/-- A slack sits in exactly one base row, its own. -/
theorem baseInRow_slack {e i : Nat} :
    I.baseInRow (I.slackVar e i) (I.edgeRow e i) = true := by
  have hnot : ¬ (I.slackVar e i < I.ncolVars) := by simp only [slackVar]; omega
  unfold baseInRow
  rw [if_neg hnot]
  simp only [edgeRow, slackVar, beq_iff_eq]
  omega

end Instance

/-! ## The QUBO

Every field is a `map` or a `filter` over an index range, as in `CNS.Problem.ofReduced`: field
projections are then `rfl` and entries are read off by `Array.getElem_map`. -/

open Instance

/-- **The colouring QUBO.** `b̂ ≡ 1`, since every constraint is an "exactly one" equation, and
therefore `θ̂_u = ½deg(u) − deg(u) = −½deg(u) = −|baseRowList u|`. -/
def problem (I : Instance) : Problem where
  nvars := I.nvars
  nrows := I.nrows
  varOf := Array.range I.nvars
  rowsOf := (Array.range I.nvars).map I.rowsOf
  varsOf := (Array.range I.nrows).map fun r =>
    ((List.range I.nvars).filter fun u => (I.rowsOf u).contains r).toArray
  bhat := Array.replicate I.nrows 1
  -- stored doubled: `2θ̂_u = deg(u) − 2 Σ_{r ∋ u} b̂_r = deg(u) − 2·deg(u)`
  theta := (Array.range I.nvars).map fun u => -2 * ((I.baseRowList u).length : Int)
  constDoubled := (I.nrows : Int)
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
    (problem I).theta.getD u 0 = -2 * ((I.baseRowList u).length : Int) := by
  show ((Array.range I.nvars).map fun u => -2 * ((I.baseRowList u).length : Int)).getD u 0 = _
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
    push_cast
    ring
  const_eq := by
    show (I.nrows : Int) = ∑ r ∈ Finset.range I.nrows, (problem I).bhat.getD r 0 ^ 2
    rw [Finset.sum_congr rfl (fun r hr => by rw [problem_bhat I (by simpa using hr)])]
    simp

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

/-! ## Worked examples

A triangle is 3-colourable but not 2-colourable, and `K₄` is not 3-colourable. The positive
direction is exhibited by an explicit bit vector; the negative ones are *theorems about the
QUBO*, obtained from `decode_isColouring`: no bit vector whatever reaches penalty zero. -/

namespace Instance

/-- Encode a colouring as a bit vector: colour variables read off `col`, and each slack takes the
value that closes its edge row. Only used to exhibit examples. -/
def encode (I : Instance) (col : Array Nat) : Array Bool :=
  (Array.range I.nvars).map fun u =>
    if u < I.ncolVars then col.getD (u / I.ncolours) I.ncolours == u % I.ncolours
    else
      match I.edges[(u - I.ncolVars) / I.ncolours]? with
      | none => false
      | some p =>
          (col.getD p.1 I.ncolours != (u - I.ncolVars) % I.ncolours)
            && (col.getD p.2 I.ncolours != (u - I.ncolVars) % I.ncolours)

end Instance

/-- `K₃` with three colours. -/
def triangle : Instance := ⟨3, 3, #[(0, 1), (1, 2), (0, 2)]⟩

/-- `K₃` with two colours — infeasible. -/
def triangle2 : Instance := ⟨3, 2, #[(0, 1), (1, 2), (0, 2)]⟩

/-- `K₄` with three colours — infeasible. -/
def k4 : Instance := ⟨4, 3, #[(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]⟩

-- 18 = 3·3 colour variables + 3·3 slacks, 24 = 2·(3 + 3·3) rows
#eval (triangle.nvars, triangle.nrows)
-- the two column degrees: 2·(1 + deg_G v) = 6 for a colour variable, 2 for a slack
#eval ((triangle.rowsOf (triangle.colVar 0 0)).size, (triangle.rowsOf (triangle.slackVar 0 0)).size)
-- a proper 3-colouring of the triangle is a zero of the objective, and decodes back to itself
#eval (problem triangle).penaltyDoubled (triangle.encode #[0, 1, 2])   -- 0
#eval triangle.decode (triangle.encode #[0, 1, 2])                      -- #[0, 1, 2]
-- a monochromatic edge is not
#eval (problem triangle).penaltyDoubled (triangle.encode #[0, 1, 0])   -- 2

/-- The incidence is *not* regular: a colour variable of the triangle has degree `6`, a slack
degree `2`. This is what the degree-free `Wf.theta_eq` buys. -/
example : (triangle.rowsOf (triangle.colVar 0 0)).size = 6
    ∧ (triangle.rowsOf (triangle.slackVar 0 0)).size = 2 := by decide

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
