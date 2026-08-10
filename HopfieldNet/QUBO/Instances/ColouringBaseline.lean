/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.QUBO.Instances.Colouring

/-!
# Classical baselines: first-fit and DSATUR, certified

`QUBO.Colouring` reduces graph colouring to a 0/1 QUBO and proves the reduction exact. What a
referee will ask next is *what the neurodynamics is being compared against*, and the answer is
not another QUBO: it is the two textbook sequential heuristics. This file implements them purely
and executably, and proves what they promise.

Both are instances of one driver, `seqColour`, which repeatedly

* asks a **selection rule** for an uncoloured vertex,
* gives it the least colour no already-coloured neighbour has (`mex` of the neighbour colours),

and stops after `nverts` rounds. The two baselines differ only in the rule:

* `firstFitSel` — the least-indexed uncoloured vertex, i.e. **first-fit in vertex order**;
* `dsaturSel` — an uncoloured vertex of maximum *saturation degree* (number of distinct colours
  among its neighbours), ties broken by larger graph degree, i.e. **DSATUR**
  (D. Brélaz, *New methods to color the vertices of a graph*, Comm. ACM **22** (1979) 251-256).

Sharing the driver means the correctness proofs are shared too. Everything below is proved for
an arbitrary rule satisfying `Selects` (it names an uncoloured vertex whenever one exists) and
then instantiated twice.

## What is proved

For every instance `I` with `edgesOk` (endpoints in range, no loops) and every rule satisfying
`Selects`:

| statement | content |
| --- | --- |
| `seqColour_size` | the output has one entry per vertex |
| `seqColour_le_degree` | vertex `v` receives a colour `≤ deg(v)` |
| `seqColour_proper` | the endpoints of an edge receive different colours |
| `seqColour_isColouring` | the output passes the library's own checker with palette `Δ+1` |
| `seqColour_countColours_le` | at most `Δ+1` distinct colours are used |
| `exists_zero_of_maxDegree_succ` | hence the `Δ+1`-colour QUBO of `I` has a zero |

`seqColour_le_degree` is the classical first-fit bound in its sharp local form; summing it up
gives the `Δ+1` palette, which is the greedy half of Brooks' theorem. The last row closes the
loop with `Colouring.encode_penalty_zero`: a baseline run is a *proof* that the QUBO the
neurodynamics is solving is feasible, with no search at all.

`greedy_proper`, `greedy_isColouring`, `dsatur_proper`, `dsatur_isColouring` are the two
instantiations.

## What is **not** proved

* Nothing here says DSATUR is optimal on any class of graphs — it is exact on bipartite graphs
  and on a few other families, and that is *not* formalised. The `Δ+1` bound is all that is
  proved, and it is proved for both rules, because it holds for any sequential rule.
* Nothing here bounds the number of colours from below, so no statement of the form "the
  baseline is within a factor of the chromatic number" is available.
* No theorem, and no measurement, in this file compares the baselines with `QUBO.search`. What is
  measured here is only `report`: the proved bound `Δ+1` against the number of colours each
  baseline actually uses. On the eleven graphs at the bottom the two baselines agree everywhere
  except on the crown graph, where greedy is dragged to `Δ+1 = 4` colours on a bipartite graph
  and DSATUR uses the optimal `2`; that single separation is the only evidence here that DSATUR
  is worth its extra cost.
-/

namespace QUBO
namespace Colouring

/-! Classical sequential colouring lives in its own namespace, so that nothing here can collide
with the encoding in `QUBO.Colouring`. -/

namespace Baseline

/-! ## Reading an array with a default

Two throwaway lemmas; `getD` is the codebase's way of reading an array without carrying a bound,
and both branches are needed below. -/

private theorem getD_of_lt {α : Type} (a : Array α) (i : Nat) (d : α) (h : i < a.size) :
    a.getD i d = a[i] := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h]; rfl

private theorem getD_of_ge {α : Type} (a : Array α) (i : Nat) (d : α) (h : a.size ≤ i) :
    a.getD i d = d := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none h]; rfl

/-! ## The least fresh colour

`mex used` is the least natural not in `used`. It is computed by a bounded linear scan rather
than by `Nat.find`, so that it is a structural recursion and both facts about it — that it misses
`used`, and that it is at most `used.length` — are ordinary inductions. Those two facts are
respectively where properness and the `Δ+1` bound come from. -/

/-- The least `c ≥ start` outside `used`, searching at most `fuel` candidates; on exhaustion it
returns `start + fuel`. -/
def freeFrom (used : List Nat) (fuel start : Nat) : Nat :=
  match fuel with
  | 0 => start
  | f + 1 => if start ∈ used then freeFrom used f (start + 1) else start

@[simp] theorem freeFrom_zero (used : List Nat) (start : Nat) :
    freeFrom used 0 start = start := rfl

theorem freeFrom_succ (used : List Nat) (f start : Nat) :
    freeFrom used (f + 1) start =
      if start ∈ used then freeFrom used f (start + 1) else start := rfl

/-- The scan never runs past its fuel. -/
theorem freeFrom_le (used : List Nat) :
    ∀ fuel start, freeFrom used fuel start ≤ start + fuel := by
  intro fuel
  induction fuel with
  | zero => intro start; simp
  | succ f ih =>
    intro start
    rw [freeFrom_succ]
    split
    · have := ih (start + 1); omega
    · omega

/-- **If the scan fails, the whole interval it scanned was occupied.** -/
theorem freeFrom_mem_all (used : List Nat) :
    ∀ fuel start, freeFrom used fuel start ∈ used →
      ∀ c, start ≤ c → c ≤ start + fuel → c ∈ used := by
  intro fuel
  induction fuel with
  | zero =>
    intro start h c h1 h2
    have : c = start := by omega
    rw [this]; simpa using h
  | succ f ih =>
    intro start h c h1 h2
    rw [freeFrom_succ] at h
    by_cases hs : start ∈ used
    · rw [if_pos hs] at h
      rcases Nat.eq_or_lt_of_le h1 with rfl | h3
      · exact hs
      · exact ih (start + 1) h c (by omega) (by omega)
    · rw [if_neg hs] at h; exact absurd h hs

/-- **The least colour nobody in `used` has.** -/
def mex (used : List Nat) : Nat := freeFrom used used.length 0

/-- `mex` is fresh. -/
theorem mex_not_mem (used : List Nat) : mex used ∉ used := by
  intro hmem
  have hall := freeFrom_mem_all used used.length 0 hmem
  have hsub : ((List.range (used.length + 1)).map (fun k => k)) ⊆ used := by
    intro c hc
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hc
    exact hall _ (Nat.zero_le _) (by simp only [List.mem_range] at hk; omega)
  have hnd : ((List.range (used.length + 1)).map (fun k => k)).Nodup :=
    List.Nodup.map (fun a b h => h) List.nodup_range
  have hle := (List.subperm_of_subset hnd hsub).length_le
  simp only [List.length_map, List.length_range] at hle
  omega

/-- `mex` fits in a palette of size `used.length + 1`; this is the whole content of the `Δ+1`
bound. -/
theorem mex_le (used : List Nat) : mex used ≤ used.length := by
  have h := freeFrom_le used used.length 0
  simp only [mex]
  omega

/-! ## Adjacency and degrees

The instance stores an edge list; `adj` symmetrises it. Everything is a `filter` or a `map` over
an index range, per the codebase convention, so membership is `List.mem_filter` and lengths are
`List.countP`. -/

/-- `u` and `v` are joined by an edge, in either orientation. -/
def adj (I : Instance) (u v : Nat) : Bool :=
  I.edges.toList.any fun p => (p.1 == u && p.2 == v) || (p.1 == v && p.2 == u)

theorem adj_comm (I : Instance) (u v : Nat) : adj I u v = adj I v u := by
  rw [Bool.eq_iff_iff]
  simp only [adj, List.any_eq_true, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
  constructor <;> (rintro ⟨p, hp, h⟩; exact ⟨p, hp, by tauto⟩)

theorem adj_of_mem_edges (I : Instance) {p : Nat × Nat} (hp : p ∈ I.edges.toList) :
    adj I p.1 p.2 = true := by
  simp only [adj, List.any_eq_true, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
  exact ⟨p, hp, Or.inl ⟨rfl, rfl⟩⟩

/-- The neighbours of `v` inside the vertex range. -/
def nbrs (I : Instance) (v : Nat) : List Nat :=
  (List.range I.nverts).filter fun u => adj I v u

/-- `deg(v)`. -/
def degree (I : Instance) (v : Nat) : Nat := (nbrs I v).length

/-- `Δ`, the maximum degree. -/
def maxDegree (I : Instance) : Nat := ((List.range I.nverts).map (degree I)).foldr max 0

private theorem le_foldr_max (x : Nat) :
    ∀ l : List Nat, x ∈ l → x ≤ l.foldr max 0 := by
  intro l
  induction l with
  | nil => intro h; cases h
  | cons a t ih =>
    intro h
    rcases List.mem_cons.mp h with rfl | h'
    · exact le_max_left _ _
    · exact le_trans (ih h') (le_max_right _ _)

theorem degree_le_maxDegree (I : Instance) {v : Nat} (hv : v < I.nverts) :
    degree I v ≤ maxDegree I :=
  le_foldr_max _ _ (List.mem_map.mpr ⟨v, List.mem_range.mpr hv, rfl⟩)

/-! ## Partial colourings

A partial colouring is an `Array (Option Nat)` of length `nverts`. Updates go through `assign`,
which is a `map` over an index range rather than a `set!`, so that its two `getD` equations are
proved by the same three-line pattern as everything else in `QUBO`. -/

/-- The all-uncoloured partial colouring. -/
def blank (I : Instance) : Array (Option Nat) := Array.replicate I.nverts none

@[simp] theorem blank_size (I : Instance) : (blank I).size = I.nverts := by simp [blank]

@[simp] theorem blank_getD (I : Instance) (v : Nat) : (blank I).getD v none = none := by
  rcases Nat.lt_or_ge v I.nverts with h | h
  · rw [getD_of_lt _ _ _ (by simpa using h)]; simp [blank]
  · exact getD_of_ge _ _ _ (by simpa using h)

/-- Give vertex `v` colour `c`. -/
def assign (col : Array (Option Nat)) (v c : Nat) : Array (Option Nat) :=
  (Array.range col.size).map fun u => if u = v then some c else col.getD u none

@[simp] theorem assign_size (col : Array (Option Nat)) (v c : Nat) :
    (assign col v c).size = col.size := by simp [assign]

theorem assign_getD_self {col : Array (Option Nat)} {v : Nat} (c : Nat) (hv : v < col.size) :
    (assign col v c).getD v none = some c := by
  rw [getD_of_lt _ _ _ (by simpa using hv)]
  simp [assign]

theorem assign_getD_of_ne (col : Array (Option Nat)) {u v : Nat} (c : Nat) (h : u ≠ v) :
    (assign col v c).getD u none = col.getD u none := by
  rcases Nat.lt_or_ge u col.size with hu | hu
  · rw [getD_of_lt _ _ _ (by simpa using hu)]
    simp [assign, h]
  · rw [getD_of_ge _ _ _ (by simpa using hu), getD_of_ge _ _ _ hu]

/-- The colours already worn by neighbours of `v`. -/
def usedNbr (I : Instance) (col : Array (Option Nat)) (v : Nat) : List Nat :=
  ((List.range I.nverts).filter fun u => adj I v u && (col.getD u none).isSome).map
    fun u => (col.getD u none).getD 0

/-- Every coloured neighbour contributes its colour. -/
theorem mem_usedNbr (I : Instance) {col : Array (Option Nat)} {v u y : Nat} (hu : u < I.nverts)
    (hadj : adj I v u = true) (hy : col.getD u none = some y) : y ∈ usedNbr I col v := by
  refine List.mem_map.mpr ⟨u, ?_, ?_⟩
  · simp only [List.mem_filter, List.mem_range, Bool.and_eq_true, hy]
    exact ⟨hu, hadj, rfl⟩
  · rw [hy]; rfl

/-- …and only neighbours do, so there are at most `deg(v)` of them. -/
theorem usedNbr_length_le (I : Instance) (col : Array (Option Nat)) (v : Nat) :
    (usedNbr I col v).length ≤ degree I v := by
  simp only [usedNbr, List.length_map, degree, nbrs, ← List.countP_eq_length_filter]
  exact List.countP_mono_left fun x _ h => by
    simp only [Bool.and_eq_true] at h; exact h.1

/-- The uncoloured vertices, in increasing order. -/
def uncoloured (I : Instance) (col : Array (Option Nat)) : List Nat :=
  (List.range I.nverts).filter fun v => (col.getD v none).isNone

theorem mem_uncoloured (I : Instance) {col : Array (Option Nat)} {v : Nat} :
    v ∈ uncoloured I col ↔ v < I.nverts ∧ col.getD v none = none := by
  simp [uncoloured, List.mem_filter, List.mem_range, Option.isNone_iff_eq_none]

/-! ## The driver

One `Selects` rule, one step, `nverts` steps. The rule is a parameter, and the correctness proofs
below quantify over it; `firstFitSel` and `dsaturSel` are the two instances. -/

/-- **What a selection rule must do**: name an uncoloured vertex, and name one whenever one
exists. Both baselines satisfy this because both are defined from `uncoloured`. -/
structure Selects (I : Instance) (sel : Array (Option Nat) → Option Nat) : Prop where
  /-- A named vertex is uncoloured and in range. -/
  some_mem : ∀ col v, sel col = some v → v ∈ uncoloured I col
  /-- Naming nothing means there is nothing to name. -/
  none_nil : ∀ col, sel col = none → uncoloured I col = []

/-- One round: colour the selected vertex with the least colour its coloured neighbours miss. -/
def seqStep (I : Instance) (sel : Array (Option Nat) → Option Nat)
    (col : Array (Option Nat)) : Array (Option Nat) :=
  match sel col with
  | none => col
  | some v => assign col v (mex (usedNbr I col v))

theorem seqStep_none (I : Instance) {sel : Array (Option Nat) → Option Nat}
    {col : Array (Option Nat)} (h : sel col = none) : seqStep I sel col = col := by
  unfold seqStep; rw [h]

theorem seqStep_some (I : Instance) {sel : Array (Option Nat) → Option Nat}
    {col : Array (Option Nat)} {v : Nat} (h : sel col = some v) :
    seqStep I sel col = assign col v (mex (usedNbr I col v)) := by
  unfold seqStep; rw [h]

/-- `k` rounds from blank. -/
def seqRun (I : Instance) (sel : Array (Option Nat) → Option Nat) : Nat → Array (Option Nat)
  | 0 => blank I
  | k + 1 => seqStep I sel (seqRun I sel k)

/-- **The sequential colouring**: `nverts` rounds, then forget the `Option`. Vertices left
uncoloured — which `seqRun_isSome` shows cannot happen — would read as colour `0`. -/
def seqColour (I : Instance) (sel : Array (Option Nat) → Option Nat) : Array Nat :=
  (seqRun I sel I.nverts).map fun o => o.getD 0

theorem seqRun_size (I : Instance) (sel : Array (Option Nat) → Option Nat) :
    ∀ k, (seqRun I sel k).size = I.nverts := by
  intro k
  induction k with
  | zero => simp [seqRun]
  | succ k ih =>
    show (seqStep I sel (seqRun I sel k)).size = I.nverts
    cases hs : sel (seqRun I sel k) with
    | none => rw [seqStep_none I hs]; exact ih
    | some v => rw [seqStep_some I hs, assign_size]; exact ih

@[simp] theorem seqColour_size (I : Instance) (sel : Array (Option Nat) → Option Nat) :
    (seqColour I sel).size = I.nverts := by simp [seqColour, seqRun_size]

theorem seqColour_getD (I : Instance) (sel : Array (Option Nat) → Option Nat) {v : Nat}
    (hv : v < I.nverts) (d : Nat) :
    (seqColour I sel).getD v d = ((seqRun I sel I.nverts).getD v none).getD 0 := by
  have h1 : v < (seqColour I sel).size := by simpa using hv
  have h2 : v < (seqRun I sel I.nverts).size := by rw [seqRun_size]; exact hv
  rw [getD_of_lt _ _ _ h1, getD_of_lt _ _ _ h2]
  simp [seqColour]

/-! ### Properness -/

/-- A partial colouring is **proper** when no edge has two coloured endpoints of one colour. -/
def Proper (I : Instance) (col : Array (Option Nat)) : Prop :=
  ∀ a b x y, a ≠ b → adj I a b = true → col.getD a none = some x →
    col.getD b none = some y → x ≠ y

theorem proper_blank (I : Instance) : Proper I (blank I) := by
  intro a b x y _ _ ha
  rw [blank_getD] at ha
  exact absurd ha (by simp)

/-- **The step preserves properness.** The freshly coloured vertex takes `mex` of its coloured
neighbours' colours, which by `mex_not_mem` is none of them; the other vertices are untouched. -/
theorem proper_seqStep (I : Instance) {sel : Array (Option Nat) → Option Nat}
    (hsel : Selects I sel) {col : Array (Option Nat)} (hsz : col.size = I.nverts)
    (hp : Proper I col) : Proper I (seqStep I sel col) := by
  cases hs : sel col with
  | none => rw [seqStep_none I hs]; exact hp
  | some v =>
    obtain ⟨hvlt, hvnone⟩ := (mem_uncoloured I).mp (hsel.some_mem col v hs)
    set c := mex (usedNbr I col v) with hc
    have hfresh : c ∉ usedNbr I col v := mex_not_mem _
    have hin : ∀ u y, u ≠ v → col.getD u none = some y → adj I v u = true → y ≠ c := by
      intro u y _ hy hadj hyc
      refine hfresh ?_
      have hu : u < I.nverts := by
        by_contra hcon
        rw [getD_of_ge _ _ _ (by omega)] at hy
        exact absurd hy (by simp)
      rw [← hyc]
      exact mem_usedNbr I hu hadj hy
    rw [seqStep_some I hs]
    intro a b x y hab hadj ha hb
    by_cases hav : a = v
    · subst hav
      have hbv : b ≠ a := fun h => hab h.symm
      rw [assign_getD_self c (by omega)] at ha
      rw [assign_getD_of_ne _ _ hbv] at hb
      have := hin b y hbv hb hadj
      simp only [Option.some.injEq] at ha
      omega
    · by_cases hbv : b = v
      · subst hbv
        rw [assign_getD_self c (by omega)] at hb
        rw [assign_getD_of_ne _ _ hav] at ha
        have := hin a x hav ha (by rw [adj_comm]; exact hadj)
        simp only [Option.some.injEq] at hb
        omega
      · rw [assign_getD_of_ne _ _ hav] at ha
        rw [assign_getD_of_ne _ _ hbv] at hb
        exact hp a b x y hab hadj ha hb

theorem proper_seqRun (I : Instance) {sel : Array (Option Nat) → Option Nat}
    (hsel : Selects I sel) : ∀ k, Proper I (seqRun I sel k) := by
  intro k
  induction k with
  | zero => exact proper_blank I
  | succ k ih => exact proper_seqStep I hsel (seqRun_size I sel k) ih

/-! ### Every vertex ends up coloured

Each round colours one new vertex, so after `nverts` rounds nothing is left. -/

theorem uncoloured_assign (I : Instance) {col : Array (Option Nat)} {v : Nat} (c : Nat)
    (hv : v < col.size) :
    uncoloured I (assign col v c) = (uncoloured I col).filter fun u => u != v := by
  unfold uncoloured
  rw [List.filter_filter]
  refine List.filter_congr fun u _ => ?_
  by_cases huv : u = v
  · subst huv
    rw [assign_getD_self c hv]
    simp
  · rw [assign_getD_of_ne _ _ huv]
    simp [huv]

private theorem length_filter_ne_lt {l : List Nat} {v : Nat} (hv : v ∈ l) :
    (l.filter fun u => u != v).length < l.length := by
  have h1 : l.length = (List.countP (fun u => u != v) l)
      + (List.countP (fun u => decide ¬((u != v) = true)) l) :=
    List.length_eq_countP_add_countP _
  have h2 : 0 < List.countP (fun u => decide ¬((u != v) = true)) l :=
    List.countP_pos_iff.mpr ⟨v, hv, by simp⟩
  rw [List.countP_eq_length_filter] at h1
  omega

/-- The uncoloured set shrinks by at least one per round. -/
theorem uncoloured_seqRun_length (I : Instance) {sel : Array (Option Nat) → Option Nat}
    (hsel : Selects I sel) : ∀ k, (uncoloured I (seqRun I sel k)).length ≤ I.nverts - k := by
  intro k
  induction k with
  | zero =>
    show (uncoloured I (blank I)).length ≤ I.nverts - 0
    have := List.length_filter_le (fun v => ((blank I).getD v none).isNone)
      (List.range I.nverts)
    simp only [uncoloured, List.length_range] at *
    omega
  | succ k ih =>
    show (uncoloured I (seqStep I sel (seqRun I sel k))).length ≤ I.nverts - (k + 1)
    cases hs : sel (seqRun I sel k) with
    | none =>
      rw [seqStep_none I hs, hsel.none_nil _ hs]
      simp
    | some v =>
      have hv := hsel.some_mem _ v hs
      have hvs : v < (seqRun I sel k).size := by
        rw [seqRun_size]; exact ((mem_uncoloured I).mp hv).1
      rw [seqStep_some I hs, uncoloured_assign I _ hvs]
      have := length_filter_ne_lt (l := uncoloured I (seqRun I sel k)) (v := v) hv
      omega

/-- **After `nverts` rounds every vertex has a colour.** -/
theorem seqRun_isSome (I : Instance) {sel : Array (Option Nat) → Option Nat}
    (hsel : Selects I sel) {v : Nat} (hv : v < I.nverts) :
    ∃ x, (seqRun I sel I.nverts).getD v none = some x := by
  have hlen := uncoloured_seqRun_length I hsel I.nverts
  have hnil : uncoloured I (seqRun I sel I.nverts) = [] := by
    rw [← List.length_eq_zero_iff]; omega
  cases hx : (seqRun I sel I.nverts).getD v none with
  | none =>
    exact absurd ((mem_uncoloured I).mpr ⟨hv, hx⟩) (by rw [hnil]; simp)
  | some x => exact ⟨x, rfl⟩

/-! ### The palette

Each vertex's colour is at most its own degree — the sharp local form of the first-fit bound. -/

/-- Every colour used so far is at most the degree of the vertex wearing it. -/
def Bounded (I : Instance) (col : Array (Option Nat)) : Prop :=
  ∀ v x, col.getD v none = some x → x ≤ degree I v

theorem bounded_blank (I : Instance) : Bounded I (blank I) := by
  intro v x hx
  rw [blank_getD] at hx
  exact absurd hx (by simp)

theorem bounded_seqStep (I : Instance) {sel : Array (Option Nat) → Option Nat}
    (hsel : Selects I sel) {col : Array (Option Nat)} (hb : Bounded I col) :
    Bounded I (seqStep I sel col) := by
  cases hs : sel col with
  | none => rw [seqStep_none I hs]; exact hb
  | some v =>
    have hvlt := ((mem_uncoloured I).mp (hsel.some_mem col v hs)).1
    rw [seqStep_some I hs]
    intro u x hx
    by_cases huv : u = v
    · subst huv
      rcases Nat.lt_or_ge u col.size with hu | hu
      · rw [assign_getD_self _ hu, Option.some.injEq] at hx
        rw [← hx]
        exact le_trans (mex_le _) (usedNbr_length_le I col u)
      · rw [getD_of_ge _ _ _ (by simpa using hu)] at hx
        exact absurd hx (by simp)
    · rw [assign_getD_of_ne _ _ huv] at hx
      exact hb u x hx

theorem bounded_seqRun (I : Instance) {sel : Array (Option Nat) → Option Nat}
    (hsel : Selects I sel) : ∀ k, Bounded I (seqRun I sel k) := by
  intro k
  induction k with
  | zero => exact bounded_blank I
  | succ k ih => exact bounded_seqStep I hsel ih

/-! ## The two rules -/

/-- **First-fit**: the least-indexed uncoloured vertex. -/
def firstFitSel (I : Instance) (col : Array (Option Nat)) : Option Nat :=
  (uncoloured I col).head?

theorem selects_firstFit (I : Instance) : Selects I (firstFitSel I) where
  some_mem := by
    intro col v h
    refine List.mem_of_mem_head? ?_
    rw [Option.mem_def]
    exact h
  none_nil := by
    intro col h
    exact List.head?_eq_none_iff.mp h

/-- The **saturation degree** of `v`: the number of *distinct* colours among its neighbours. -/
def satDeg (I : Instance) (col : Array (Option Nat)) (v : Nat) : Nat :=
  (usedNbr I col v).dedup.length

/-- DSATUR's comparison: strictly larger saturation degree, or equal saturation degree and
strictly larger graph degree. -/
def dsaturBetter (I : Instance) (col : Array (Option Nat)) (u b : Nat) : Bool :=
  (satDeg I col b < satDeg I col u)
    || ((satDeg I col b == satDeg I col u) && (degree I b < degree I u))

/-- **DSATUR** (Brélaz 1979): an uncoloured vertex of maximum saturation degree, ties broken by
larger graph degree, and remaining ties by smaller index (the fold only moves on a strict
improvement, so it is deterministic). -/
def dsaturSel (I : Instance) (col : Array (Option Nat)) : Option Nat :=
  match uncoloured I col with
  | [] => none
  | v :: vs => some (vs.foldl (fun b u => if dsaturBetter I col u b then u else b) v)

private theorem foldl_pick_mem {α : Type} (f : α → α → Bool) :
    ∀ (l : List α) (a : α), l.foldl (fun b u => if f u b then u else b) a ∈ a :: l := by
  intro l
  induction l with
  | nil => intro a; simp
  | cons x xs ih =>
    intro a
    show xs.foldl _ (if f x a then x else a) ∈ a :: x :: xs
    rcases List.mem_cons.mp (ih (if f x a then x else a)) with h | h
    · rw [h]
      by_cases hf : f x a
      · simp [hf]
      · simp [hf]
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)

theorem selects_dsatur (I : Instance) : Selects I (dsaturSel I) where
  some_mem := by
    intro col v h
    cases hl : uncoloured I col with
    | nil => rw [dsaturSel, hl] at h; exact absurd h (by simp)
    | cons a t =>
      rw [dsaturSel, hl, Option.some.injEq] at h
      rw [← h]
      exact foldl_pick_mem _ t a
  none_nil := by
    intro col h
    cases hl : uncoloured I col with
    | nil => rfl
    | cons a t => rw [dsaturSel, hl] at h; exact absurd h (by simp)

/-- **The greedy (first-fit) colouring**, in vertex order. -/
def greedy (I : Instance) : Array Nat := seqColour I (firstFitSel I)

/-- **The DSATUR colouring.** -/
def dsatur (I : Instance) : Array Nat := seqColour I (dsaturSel I)

/-- The number of distinct colours a colouring uses. The palette is an *output* of a baseline,
not an input, so this is how the caller counts it. -/
def countColours (col : Array Nat) : Nat := col.toList.dedup.length

theorem countColours_le {col : Array Nat} {B : Nat} (h : ∀ x ∈ col.toList, x ≤ B) :
    countColours col ≤ B + 1 := by
  have hsub : col.toList.dedup ⊆ List.range (B + 1) := fun x hx =>
    List.mem_range.mpr (Nat.lt_succ_of_le (h x (List.mem_dedup.mp hx)))
  have := (List.subperm_of_subset (List.nodup_dedup _) hsub).length_le
  simpa [countColours] using this

/-! ## The theorems

Everything is proved for an arbitrary `Selects` rule and then instantiated. -/

/-- **Each vertex gets a colour at most its own degree.** -/
theorem seqColour_le_degree (I : Instance) {sel : Array (Option Nat) → Option Nat}
    (hsel : Selects I sel) {v : Nat} (hv : v < I.nverts) (d : Nat) :
    (seqColour I sel).getD v d ≤ degree I v := by
  obtain ⟨x, hx⟩ := seqRun_isSome I hsel hv
  rw [seqColour_getD I sel hv, hx]
  exact bounded_seqRun I hsel I.nverts v x hx

/-- **…hence a colour from a palette of size `Δ+1`.** This is the classical greedy bound, and it
holds for every sequential rule, DSATUR included. -/
theorem seqColour_lt_maxDegree_succ (I : Instance) {sel : Array (Option Nat) → Option Nat}
    (hsel : Selects I sel) {v : Nat} (hv : v < I.nverts) (d : Nat) :
    (seqColour I sel).getD v d < maxDegree I + 1 := by
  have h1 := seqColour_le_degree I hsel hv d
  have h2 := degree_le_maxDegree I hv
  omega

/-- **The colouring is proper**: adjacent vertices get different colours. -/
theorem seqColour_proper_adj (I : Instance) {sel : Array (Option Nat) → Option Nat}
    (hsel : Selects I sel) {a b : Nat} (ha : a < I.nverts) (hb : b < I.nverts) (hab : a ≠ b)
    (hadj : adj I a b = true) (d : Nat) :
    (seqColour I sel).getD a d ≠ (seqColour I sel).getD b d := by
  obtain ⟨x, hx⟩ := seqRun_isSome I hsel ha
  obtain ⟨y, hy⟩ := seqRun_isSome I hsel hb
  rw [seqColour_getD I sel ha, seqColour_getD I sel hb, hx, hy]
  exact proper_seqRun I hsel I.nverts a b x y hab hadj hx hy

/-- **The colouring is proper, on the instance's own edge list.** -/
theorem seqColour_proper (I : Instance) {sel : Array (Option Nat) → Option Nat}
    (hsel : Selects I sel) (hE : I.edgesOk = true) {p : Nat × Nat} (hp : p ∈ I.edges.toList)
    (d : Nat) : (seqColour I sel).getD p.1 d ≠ (seqColour I sel).getD p.2 d := by
  have hok := (List.all_eq_true.mp hE) p hp
  simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hok
  obtain ⟨⟨h1, h2⟩, hne⟩ := hok
  exact seqColour_proper_adj I hsel h1 h2 hne (adj_of_mem_edges I hp) d

/-- The same instance with a different palette; the graph and `edgesOk` are untouched. -/
def withPalette (I : Instance) (n : Nat) : Instance := { I with ncolours := n }

@[simp] theorem withPalette_nverts (I : Instance) (n : Nat) : (withPalette I n).nverts = I.nverts :=
  rfl

@[simp] theorem withPalette_ncolours (I : Instance) (n : Nat) :
    (withPalette I n).ncolours = n := rfl

@[simp] theorem withPalette_edges (I : Instance) (n : Nat) :
    (withPalette I n).edges = I.edges := rfl

@[simp] theorem withPalette_edgesOk (I : Instance) (n : Nat) :
    (withPalette I n).edgesOk = I.edgesOk := rfl

/-- **The baseline output passes the library's own checker**, with palette `Δ+1`.

This is the statement the paper quotes: `Instance.isColouring` is the same `Bool` checker that
`Colouring.decode_isColouring` discharges for the neurodynamics, so baseline and solver are
certified against one predicate rather than two. -/
theorem seqColour_isColouring (I : Instance) {sel : Array (Option Nat) → Option Nat}
    (hsel : Selects I sel) (hE : I.edgesOk = true) :
    (withPalette I (maxDegree I + 1)).isColouring (seqColour I sel) = true := by
  simp only [Instance.isColouring, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    List.mem_range, decide_eq_true_eq, bne_iff_ne, ne_eq, withPalette_nverts,
    withPalette_ncolours, withPalette_edges]
  refine ⟨⟨seqColour_size I sel, fun v hv => ?_⟩, fun p hp => ?_⟩
  · exact seqColour_lt_maxDegree_succ I hsel hv _
  · exact seqColour_proper I hsel hE hp _

/-- **At most `Δ+1` distinct colours are used.** -/
theorem seqColour_countColours_le (I : Instance) {sel : Array (Option Nat) → Option Nat}
    (hsel : Selects I sel) : countColours (seqColour I sel) ≤ maxDegree I + 1 := by
  refine countColours_le fun x hx => ?_
  obtain ⟨v, hv, hvx⟩ := Array.getElem_of_mem (Array.mem_toList_iff.mp hx)
  have hvn : v < I.nverts := by simpa using hv
  have := seqColour_lt_maxDegree_succ I hsel hvn 0
  rw [getD_of_lt _ _ _ hv, hvx] at this
  omega

/-- **A baseline run proves the `Δ+1`-colour QUBO feasible.**

`encode_penalty_zero` turns the checked colouring into a bit vector of penalty zero, so this is a
certificate of feasibility for the very objective `QUBO.search` minimises — obtained without any
search. -/
theorem exists_zero_of_maxDegree_succ (I : Instance) {sel : Array (Option Nat) → Option Nat}
    (hsel : Selects I sel) (hE : I.edgesOk = true) :
    ∃ x, (problem (withPalette I (maxDegree I + 1))).penaltyDoubled x = 0 :=
  ⟨_, encode_penalty_zero (withPalette I (maxDegree I + 1)) (by simpa using hE)
      (seqColour_isColouring I hsel hE)⟩

/-! ### The two baselines -/

/-- **Greedy first-fit is proper.** -/
theorem greedy_proper (I : Instance) (hE : I.edgesOk = true) {p : Nat × Nat}
    (hp : p ∈ I.edges.toList) (d : Nat) :
    (greedy I).getD p.1 d ≠ (greedy I).getD p.2 d :=
  seqColour_proper I (selects_firstFit I) hE hp d

/-- **DSATUR is proper.** -/
theorem dsatur_proper (I : Instance) (hE : I.edgesOk = true) {p : Nat × Nat}
    (hp : p ∈ I.edges.toList) (d : Nat) :
    (dsatur I).getD p.1 d ≠ (dsatur I).getD p.2 d :=
  seqColour_proper I (selects_dsatur I) hE hp d

/-- Greedy colours vertex `v` with a colour `≤ deg(v)`. -/
theorem greedy_le_degree (I : Instance) {v : Nat} (hv : v < I.nverts) (d : Nat) :
    (greedy I).getD v d ≤ degree I v :=
  seqColour_le_degree I (selects_firstFit I) hv d

/-- DSATUR colours vertex `v` with a colour `≤ deg(v)`. -/
theorem dsatur_le_degree (I : Instance) {v : Nat} (hv : v < I.nverts) (d : Nat) :
    (dsatur I).getD v d ≤ degree I v :=
  seqColour_le_degree I (selects_dsatur I) hv d

/-- **Greedy is a proper `Δ+1`-colouring**, by the library's checker. -/
theorem greedy_isColouring (I : Instance) (hE : I.edgesOk = true) :
    (withPalette I (maxDegree I + 1)).isColouring (greedy I) = true :=
  seqColour_isColouring I (selects_firstFit I) hE

/-- **DSATUR is a proper `Δ+1`-colouring**, by the library's checker. -/
theorem dsatur_isColouring (I : Instance) (hE : I.edgesOk = true) :
    (withPalette I (maxDegree I + 1)).isColouring (dsatur I) = true :=
  seqColour_isColouring I (selects_dsatur I) hE

theorem greedy_countColours_le (I : Instance) : countColours (greedy I) ≤ maxDegree I + 1 :=
  seqColour_countColours_le I (selects_firstFit I)

theorem dsatur_countColours_le (I : Instance) : countColours (dsatur I) ≤ maxDegree I + 1 :=
  seqColour_countColours_le I (selects_dsatur I)

/-- **Every graph with maximum degree `Δ` is `Δ+1`-colourable**, certified through the QUBO: the
greedy colouring encodes to a zero of the objective. -/
theorem greedy_exists_zero (I : Instance) (hE : I.edgesOk = true) :
    ∃ x, (problem (withPalette I (maxDegree I + 1))).penaltyDoubled x = 0 :=
  exists_zero_of_maxDegree_succ I (selects_firstFit I) hE

/-! ## Measurements

A handful of graphs, defined here rather than imported so that this file stands alone. The
chromatic numbers quoted are textbook facts about the graphs; they are *not* proved here (except
where the QUBO already settles them, e.g. `Colouring.k4_not_three_colourable`).

`report I = (Δ+1, colours used by greedy, colours used by DSATUR)`. Measured, verbatim from the
`#eval`s below:

| graph | `χ` | `Δ+1` | greedy | DSATUR |
| --- | --- | --- | --- | --- |
| `gK3` | 3 | 3 | 3 | 3 |
| `gK4` | 4 | 4 | 4 | 4 |
| `gK5` | 5 | 5 | 5 | 5 |
| `gPath5` | 2 | 3 | 2 | 2 |
| `gC5` | 3 | 3 | 3 | 3 |
| `gC6` | 2 | 3 | 2 | 2 |
| `gK33` | 2 | 4 | 2 | 2 |
| `gCrown4` | 2 | 4 | **4** | **2** |
| `gPetersen` | 3 | 4 | 3 | 3 |
| `gGrotzsch` | 4 | 6 | 4 | 4 |
| `gWheel6` | 3 | 7 | 3 | 3 |

So on ten of the eleven the two rules agree, and both are optimal on all of them except greedy on
`gCrown4`. The `Δ+1` bound is attained on the complete graphs and on `gCrown4`, and is loose
elsewhere — worst on `gWheel6`, where it says 7 and 3 suffice. -/

/-- `(Δ+1, #colours greedy, #colours DSATUR)`. The first component is the proved bound
(`greedy_countColours_le`, `dsatur_countColours_le`); the other two are measured. -/
def report (I : Instance) : Nat × Nat × Nat :=
  (maxDegree I + 1, countColours (greedy I), countColours (dsatur I))

/-- `K₃`. -/
def gK3 : Instance := ⟨3, 3, #[(0,1),(1,2),(0,2)]⟩

/-- `K₄`. -/
def gK4 : Instance := ⟨4, 4, #[(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]⟩

/-- `K₅`. -/
def gK5 : Instance := ⟨5, 5, #[(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]⟩

/-- A path on five vertices; `χ = 2`. -/
def gPath5 : Instance := ⟨5, 2, #[(0,1),(1,2),(2,3),(3,4)]⟩

/-- The 5-cycle; `χ = 3`, `Δ+1 = 3`, so the bound is tight. -/
def gC5 : Instance := ⟨5, 3, #[(0,1),(1,2),(2,3),(3,4),(4,0)]⟩

/-- The 6-cycle; `χ = 2` while `Δ+1 = 3`. -/
def gC6 : Instance := ⟨6, 3, #[(0,1),(1,2),(2,3),(3,4),(4,5),(5,0)]⟩

/-- `K_{3,3}`, with the two sides interleaved in the numbering; `χ = 2`. -/
def gK33 : Instance := ⟨6, 3, #[(0,1),(0,3),(0,5),(2,1),(2,3),(2,5),(4,1),(4,3),(4,5)]⟩

/-- The **crown graph** on `2·4` vertices — `K_{4,4}` minus a perfect matching — numbered
`L i = 2i`, `R i = 2i+1`, with `L i ~ R j` iff `i ≠ j`.

This is the standard adversarial input for first-fit: the graph is bipartite, so `χ = 2`, but in
this vertex order greedy is forced up to `Δ+1 = 4`. DSATUR is not fooled. See the `#eval`s
below; this is the one graph in the set where the two baselines differ. -/
def gCrown4 : Instance :=
  ⟨8, 4, #[(0,3),(0,5),(0,7),(2,1),(2,5),(2,7),(4,1),(4,3),(4,7),(6,1),(6,3),(6,5)]⟩

/-- The Petersen graph; `χ = 3`, `Δ+1 = 4`. -/
def gPetersen : Instance :=
  ⟨10, 3, #[(0,1),(1,2),(2,3),(3,4),(4,0),
            (0,5),(1,6),(2,7),(3,8),(4,9),
            (5,7),(7,9),(9,6),(6,8),(8,5)]⟩

/-- The Grötzsch graph (the Mycielskian of `C₅`): triangle-free with `χ = 4`, `Δ+1 = 6`. -/
def gGrotzsch : Instance :=
  ⟨11, 4, #[(0,1),(1,2),(2,3),(3,4),(4,0),
            (5,1),(5,4),(6,2),(6,0),(7,3),(7,1),(8,4),(8,2),(9,0),(9,3),
            (10,5),(10,6),(10,7),(10,8),(10,9)]⟩

/-- The 6-wheel: a 6-cycle plus a hub; `χ = 3`, `Δ+1 = 7`. -/
def gWheel6 : Instance :=
  ⟨7, 3, #[(0,1),(1,2),(2,3),(3,4),(4,5),(5,0),
           (6,0),(6,1),(6,2),(6,3),(6,4),(6,5)]⟩

/-- All the sample graphs are simple with endpoints in range, so every theorem above applies to
them. -/
example : gK3.edgesOk = true ∧ gK4.edgesOk = true ∧ gK5.edgesOk = true
    ∧ gPath5.edgesOk = true ∧ gC5.edgesOk = true ∧ gC6.edgesOk = true ∧ gK33.edgesOk = true
    ∧ gCrown4.edgesOk = true ∧ gPetersen.edgesOk = true ∧ gGrotzsch.edgesOk = true
    ∧ gWheel6.edgesOk = true := by decide

-- (Δ+1, greedy, DSATUR)
#eval report gK3
#eval report gK4
#eval report gK5
#eval report gPath5
#eval report gC5
#eval report gC6
#eval report gK33
#eval report gCrown4
#eval report gPetersen
#eval report gGrotzsch
#eval report gWheel6

-- the crown graph in detail: greedy is dragged to 4 colours on a bipartite graph, DSATUR is not
#eval greedy gCrown4
#eval dsatur gCrown4

-- degrees, for the bound
#eval (maxDegree gCrown4, maxDegree gPetersen, maxDegree gGrotzsch, maxDegree gWheel6)

/-- The general theorems, spot-checked against the kernel on two of the graphs. -/
example : (withPalette gCrown4 (maxDegree gCrown4 + 1)).isColouring (greedy gCrown4) = true := by
  decide +kernel

example : (withPalette gPetersen (maxDegree gPetersen + 1)).isColouring (dsatur gPetersen)
    = true := by
  decide +kernel

/-- **The `Δ+1` bound is attained**, so `greedy_countColours_le` cannot be improved: on `K₅`
greedy needs all `Δ+1 = 5` colours because the graph does, and on the crown graph it needs all
`Δ+1 = 4` although the graph needs `2`. -/
example : countColours (greedy gK5) = maxDegree gK5 + 1 := by decide +kernel

example : countColours (greedy gCrown4) = maxDegree gCrown4 + 1 := by decide +kernel

/-- **DSATUR strictly beats first-fit on the crown graph.** This is the one certified separation
between the two baselines in this file; on the other ten graphs above they tie. -/
theorem dsatur_lt_greedy_gCrown4 : countColours (dsatur gCrown4) < countColours (greedy gCrown4) :=
  by decide +kernel

/-- **A baseline run as a feasibility certificate.** DSATUR 2-colours the crown graph, so by
`Colouring.encode_penalty_zero` the *two*-colour QUBO of that graph has a zero — a witness for the
objective `QUBO.search` minimises, produced with no search. The palette here is `2`, not the
`Δ+1 = 4` of the general theorem, because the measured DSATUR output happens to be optimal; that
is a fact about this instance and not a theorem about DSATUR. -/
theorem gCrown4_two_colour_zero :
    ∃ x, (problem (withPalette gCrown4 2)).penaltyDoubled x = 0 :=
  ⟨(withPalette gCrown4 2).encode (dsatur gCrown4),
    encode_penalty_zero (withPalette gCrown4 2) (by decide)
      (show (withPalette gCrown4 2).isColouring (dsatur gCrown4) = true by decide +kernel)⟩

end Baseline
end Colouring
end QUBO
