/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.QUBO.Refine

/-!
# Exact cover as a 0/1 QUBO in canonical form

Lucas, *Ising formulations of many NP problems*, §4.1. Given a ground set `U = {0,…,m-1}` and a
family `S₀,…,S_{k-1} ⊆ U`, decide whether some subfamily covers every element of `U` exactly
once. Lucas's Hamiltonian is

  `H = A · Σ_{α ∈ U} (1 − Σ_{i : α ∈ Sᵢ} xᵢ)²`,

which is already `‖Â x − b̂‖²` with `b̂ = 1`: one row per ground-set element, one column per
subset, `Â_{α i} = 1` iff `α ∈ Sᵢ`. **No slack variables.** The variable count is `k`, the number
of subsets, independent of `m`.

## Why the rows are duplicated

`Problem.theta` is `Array Int` and `Wf.theta_eq` reads

  `2 θ̂_u = deg(u) − 2 Σ_{r ∋ u} b̂_r`,

so `θ̂_u ∈ ℤ` forces `deg(u)` to be **even**. With one row per ground-set element the degree of
column `i` is `|Sᵢ|`, which is odd whenever `Sᵢ` is. The theory is degree-*free* but not
parity-free, so we take two copies of every ground-set row: rows `α` and `α + m` both carry the
constraint "element `α` is covered once". Then `deg(i) = 2|Sᵢ|` and `θ̂_i = −|Sᵢ|`, and the
objective is `2H/A` — the same zero set, twice the value. This is not a slack variable: no new
column is introduced, only a repeated equation.

The degrees still vary from column to column whenever the subsets have different sizes, so this
is a genuine exercise of the degree-free theory of `QUBO.Net`, like `QUBO.ToyQubo`.

## Well-formedness of the input

An `Instance` is *not* normalised on construction: `Instance.Wf` demands, as a hypothesis, that
each `Sᵢ` be duplicate-free and contained in `{0,…,m-1}`. Duplicates would make `Â` an integer
matrix rather than a 0/1 one, and out-of-range elements would be silently dropped. All three
example instances below discharge `Wf` by `decide`.

## What is proved

* `qubo_wf` : the built `Problem` satisfies `Problem.Wf`, hence is a Hopfield/Boltzmann network
  by `QUBO.Problem.zeroOneHamiltonian_eq` (instantiated in `ex1_energy`).
* `decode_coversExactly` : `penaltyDoubled x = 0 → coversExactly (decode x)`, the soundness of
  the encoding.
* `refines` : the problem is the (trivial, no-column-deleted) restriction of `inc`, its
  `QUBO.Incidence`.
-/

namespace QUBO
namespace ExactCover

open Finset

/-! ## Generic scaffolding

Two facts about `Problem` that are not in the library yet and are not about exact cover: a
zero penalty forces every row residual to vanish, and the indicator of a duplicate-free array
sums to its size over `ℤ` (the library has the `ℝ` version, `Problem.sum_indicator_contains`). -/

/-- A fold of squares vanishes exactly when the accumulator and every summand do. Integers, so
there is no cancellation to hide a violated constraint behind a satisfied one. -/
private theorem foldl_sq_zero_iff (f : Nat → Int) :
    ∀ (l : List Nat) (acc : Int), 0 ≤ acc →
      (l.foldl (fun a r => a + f r * f r) acc = 0 ↔ acc = 0 ∧ ∀ r ∈ l, f r = 0) := by
  intro l
  induction l with
  | nil => intro acc _; simp
  | cons r0 t ih =>
    intro acc hacc
    have hsq : 0 ≤ f r0 * f r0 := mul_self_nonneg _
    rw [List.foldl_cons, ih (acc + f r0 * f r0) (by omega)]
    constructor
    · rintro ⟨hz, hall⟩
      have h0 : f r0 * f r0 = 0 := by omega
      have hr0 : f r0 = 0 := by rcases Int.mul_eq_zero.mp h0 with h | h <;> exact h
      refine ⟨by omega, fun w hw => ?_⟩
      rcases List.mem_cons.mp hw with rfl | hw'
      · exact hr0
      · exact hall w hw'
    · rintro ⟨rfl, hall⟩
      have h0 : f r0 = 0 := hall r0 (List.mem_cons_self ..)
      exact ⟨by rw [h0]; ring, fun w hw => hall w (List.mem_cons_of_mem _ hw)⟩

/-- **A zero penalty means every constraint row is met on the nose**: `ρ_r = b̂_r`. -/
theorem rowSums_eq_bhat_of_penalty_zero (P : Problem) (x : Array Bool)
    (h : P.penaltyDoubled x = 0) {r : Nat} (hr : r < P.nrows) :
    (P.rowSums x).getD r 0 = P.bhat.getD r 0 := by
  have hpen : P.penaltyDoubled x
      = (Array.range P.nrows).foldl
          (fun acc r => acc + ((P.rowSums x).getD r 0 - P.bhat.getD r 0) *
            ((P.rowSums x).getD r 0 - P.bhat.getD r 0)) 0 := rfl
  rw [hpen, ← Array.foldl_toList, Array.toList_range] at h
  have := (foldl_sq_zero_iff (fun r => (P.rowSums x).getD r 0 - P.bhat.getD r 0)
    (List.range P.nrows) 0 le_rfl).mp h
  have := this.2 r (List.mem_range.mpr hr)
  omega

/-- The `ℤ` companion of `Problem.sum_indicator_contains`: summing the membership indicator of a
duplicate-free array over a containing range returns its size. -/
theorem sum_indicator_card {N : Nat} (a : Array Nat) (hnd : a.toList.Nodup)
    (hlt : ∀ r ∈ a, r < N) :
    ∑ r ∈ Finset.range N, (if a.contains r then (1 : Int) else 0) = (a.size : Int) := by
  rw [sum_indicator_weighted a (fun _ => (1 : Int)) hnd hlt,
    Array.foldl_add_eq_sum a (fun _ => (1 : Int)) 0]
  simp

/-- Reading off a field built as a `map` over an index range. Every non-trivial field of `qubo`
below is of this shape, so this single lemma is the whole of the array bookkeeping. -/
theorem map_range_getD {α : Type _} (n : Nat) (f : Nat → α) (d : α) {i : Nat} (hi : i < n) :
    ((Array.range n).map f).getD i d = f i := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa using hi)]
  simp

/-! ## The instance -/

/-- An exact-cover instance: the ground set is `{0,…,groundSize-1}` and `sets` is the family.
Nothing is normalised; `Wf` is the hypothesis that the data is sane. -/
structure Instance where
  /-- The ground set is `{0, …, groundSize - 1}`. -/
  groundSize : Nat
  /-- The family of subsets, each a duplicate-free array of ground-set elements. -/
  sets : Array (Array Nat)
  deriving Inhabited

namespace Instance

/-- The number of subsets — and, below, the number of decision variables. -/
def numSets (I : Instance) : Nat := I.sets.size

/-- The `i`-th subset, `#[]` out of range. -/
def setOf (I : Instance) (i : Nat) : Array Nat := I.sets.getD i #[]

/-- The input is sane: every subset is duplicate-free and inside the ground set. Duplicates
would make `Â` integer-valued rather than 0/1. -/
structure Wf (I : Instance) : Prop where
  /-- No subset repeats an element. -/
  nodup : ∀ i < I.numSets, (I.setOf i).toList.Nodup
  /-- Every listed element is a ground-set element. -/
  mem_lt : ∀ i < I.numSets, ∀ a ∈ I.setOf i, a < I.groundSize

/-! ### The columns and rows

`rowsOfSet i` is `Sᵢ` together with its shift by `m`: the two copies of each ground-set row. -/

/-- The constraint rows met by column `i`: element `α ∈ Sᵢ` gives rows `α` and `α + m`. -/
def rowsOfSet (I : Instance) (i : Nat) : Array Nat :=
  I.setOf i ++ (I.setOf i).map (· + I.groundSize)

/-- The columns meeting row `r`: the subsets containing the ground-set element `r % m`.

Built with `List.filter` and not `Array.filter`: the latter carries an optional
`stop := as.size` argument whose unification forces `(Array.range _).size` to whnf. -/
def colsOfRow (I : Instance) (r : Nat) : Array Nat :=
  ((List.range I.numSets).filter fun i => (I.setOf i).contains (r % I.groundSize)).toArray

end Instance

/-! ## The QUBO -/

open Instance

/-- **Exact cover as a `QUBO.Problem`.**

`k = |sets|` variables, `2m` rows, `b̂ ≡ 1`, `θ̂_i = −|Sᵢ|`, `‖b̂‖² = 2m`. Every field is a `map`
over an index range — never a `for` loop with `set!` — so each is characterised pointwise by
`map_range_getD`. -/
def qubo (I : Instance) : Problem where
  nvars := I.numSets
  nrows := 2 * I.groundSize
  varOf := Array.range I.numSets
  rowsOf := (Array.range I.numSets).map I.rowsOfSet
  varsOf := (Array.range (2 * I.groundSize)).map I.colsOfRow
  bhat := (Array.range (2 * I.groundSize)).map fun _ => 1
  theta := (Array.range I.numSets).map fun i => -((I.setOf i).size : Int)
  constDoubled := 2 * I.groundSize
  base := #[]

@[simp] theorem qubo_nvars (I : Instance) : (qubo I).nvars = I.numSets := rfl
@[simp] theorem qubo_nrows (I : Instance) : (qubo I).nrows = 2 * I.groundSize := rfl

theorem qubo_rowsOf (I : Instance) {u : Nat} (hu : u < I.numSets) :
    (qubo I).rowsOf.getD u #[] = I.rowsOfSet u :=
  map_range_getD _ _ _ hu

theorem qubo_bhat (I : Instance) {r : Nat} (hr : r < 2 * I.groundSize) :
    (qubo I).bhat.getD r 0 = 1 :=
  map_range_getD _ _ _ hr

theorem qubo_theta (I : Instance) {u : Nat} (hu : u < I.numSets) :
    (qubo I).theta.getD u 0 = -((I.setOf u).size : Int) :=
  map_range_getD _ _ _ hu

theorem qubo_varOf (I : Instance) {u : Nat} (hu : u < I.numSets) :
    (qubo I).varOf.getD u 0 = u := by
  show (Array.range I.numSets).getD u 0 = u
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa using hu)]
  simp

/-! ### Structure of a column -/

/-- A column is `Sᵢ` and its shifted copy, and nothing else. -/
theorem mem_rowsOfSet (I : Instance) (i r : Nat) :
    r ∈ I.rowsOfSet i ↔ (r ∈ I.setOf i ∨ ∃ a ∈ I.setOf i, a + I.groundSize = r) := by
  unfold Instance.rowsOfSet
  rw [Array.mem_append]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · obtain ⟨a, ha, rfl⟩ := Array.mem_map.mp h
      exact Or.inr ⟨a, ha, rfl⟩
  · rintro (h | ⟨a, ha, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (Array.mem_map.mpr ⟨a, ha, rfl⟩)

/-- Each column has twice the size of its subset — in particular an even degree, which is what
lets `θ̂` be an integer. -/
theorem rowsOfSet_size (I : Instance) (i : Nat) :
    (I.rowsOfSet i).size = 2 * (I.setOf i).size := by
  simp [Instance.rowsOfSet, Nat.two_mul]

/-- The two copies of a row are distinct, so a column meets each of its rows exactly once. -/
theorem rowsOfSet_nodup (I : Instance) (hI : I.Wf) {i : Nat} (hi : i < I.numSets) :
    (I.rowsOfSet i).toList.Nodup := by
  have hnd := hI.nodup i hi
  have hlt := hI.mem_lt i hi
  rw [Instance.rowsOfSet, Array.toList_append, Array.toList_map, List.nodup_append]
  refine ⟨hnd, hnd.map (fun a b h => by omega), ?_⟩
  intro a ha b hb
  obtain ⟨c, _, rfl⟩ := List.mem_map.mp hb
  have h1 : a < I.groundSize := hlt a (Array.mem_toList_iff.mp ha)
  omega

/-- Every listed row is a real row. -/
theorem rowsOfSet_mem_lt (I : Instance) (hI : I.Wf) {i : Nat} (hi : i < I.numSets) :
    ∀ r ∈ I.rowsOfSet i, r < 2 * I.groundSize := by
  intro r hr
  rcases (mem_rowsOfSet I i r).mp hr with h | ⟨a, ha, rfl⟩
  · have := hI.mem_lt i hi r h; omega
  · have := hI.mem_lt i hi a ha; omega

/-- **On the lower copy of the rows, membership in the column is membership in the subset.**

This is what makes the first `m` rows readable as Lucas's constraints. -/
theorem contains_rowsOfSet_lo (I : Instance) (i : Nat) {a : Nat} (ha : a < I.groundSize) :
    (I.rowsOfSet i).contains a = (I.setOf i).contains a := by
  have hiff : a ∈ I.rowsOfSet i ↔ a ∈ I.setOf i := by
    rw [mem_rowsOfSet]
    refine ⟨fun h => ?_, Or.inl⟩
    rcases h with h | ⟨b, _, hb⟩
    · exact h
    · omega
  have h1 : ((I.rowsOfSet i).contains a = true) ↔ ((I.setOf i).contains a = true) := by
    rw [Array.contains_iff_mem, Array.contains_iff_mem]; exact hiff
  cases hr : (I.rowsOfSet i).contains a <;> cases hc : (I.setOf i).contains a <;> simp_all

/-! ### Well-formedness -/

/-- **The exact-cover QUBO is a well-formed 0/1 QUBO in canonical form.**

Hence `QUBO.Problem.zeroOneHamiltonian_eq` applies: the HNBM `{0,1}` Boltzmann energy of
`netParams (qubo I)` is `(‖Âx−b̂‖² − ‖b̂‖²)/2`. -/
theorem qubo_wf (I : Instance) (hI : I.Wf) : (qubo I).Wf where
  nodup := by
    intro u hu
    rw [qubo_rowsOf I hu]
    exact rowsOfSet_nodup I hI hu
  mem_lt := by
    intro u hu r hr
    rw [qubo_rowsOf I hu] at hr
    exact rowsOfSet_mem_lt I hI hu r hr
  theta_eq := by
    intro u hu
    have hrows : (qubo I).rowsOf.getD u #[] = I.rowsOfSet u := qubo_rowsOf I hu
    have hsum : ∑ r ∈ Finset.range (qubo I).nrows,
          (if ((qubo I).rowsOf.getD u #[]).contains r then (qubo I).bhat.getD r 0 else 0)
        = ((I.rowsOfSet u).size : Int) := by
      rw [show (qubo I).nrows = 2 * I.groundSize from rfl]
      rw [Finset.sum_congr rfl (fun r hr => by
        rw [hrows, qubo_bhat I (Finset.mem_range.mp hr)])]
      exact sum_indicator_card (I.rowsOfSet u) (rowsOfSet_nodup I hI hu)
        (rowsOfSet_mem_lt I hI hu)
    rw [qubo_theta I hu, hsum, hrows, rowsOfSet_size]
    push_cast
    ring
  const_eq := by
    show (2 * I.groundSize : Int) = _
    rw [Finset.sum_congr rfl (fun r hr => by
      rw [qubo_bhat I (Finset.mem_range.mp (by simpa using hr))])]
    simp [mul_comm]

/-! ## The incidence

Exact cover as a value of `QUBO.Incidence`, with `qubo I` its (trivial) column restriction: no
column is deleted, so `varOf` is the identity. -/

/-- **The exact-cover incidence**: `2m` rows, one column per subset. -/
def inc (I : Instance) (hI : I.Wf) : Incidence where
  nvars := I.numSets
  nrows := 2 * I.groundSize
  rowsOf := I.rowsOfSet
  nodup := fun _ h => rowsOfSet_nodup I hI h
  mem_lt := fun _ h => rowsOfSet_mem_lt I hI h

/-- The problem refines its incidence along the identity. -/
theorem refines (I : Instance) (hI : I.Wf) : Problem.Refines (inc I hI) (qubo I) where
  nrows_eq := rfl
  varOf_lt := fun u hu => by rw [qubo_varOf I hu]; exact hu
  rowsOf_eq := fun u hu => by rw [qubo_rowsOf I hu, qubo_varOf I hu]; rfl
  varOf_inj := fun u hu v hv h => by rwa [qubo_varOf I hu, qubo_varOf I hv] at h

/-! ## Decoding and checking -/

/-- **The decoder**: the chosen subfamily, as the array of indices `i` with `xᵢ = 1`. -/
def decode (I : Instance) (x : Array Bool) : Array Nat :=
  ((List.range I.numSets).filter fun i => x.getD i false).toArray

/-- **The checker**: every ground-set element is covered exactly once by the chosen subfamily. -/
def coversExactly (I : Instance) (sel : Array Nat) : Bool :=
  (List.range I.groundSize).all fun a =>
    sel.toList.countP (fun i => (I.setOf i).contains a) == 1

/-! ## Soundness -/

/-- The count of chosen subsets containing `a`, as it appears in the checker, is the row sum of
row `a`. -/
theorem countP_decode (I : Instance) (x : Array Bool) (a : Nat) :
    (decode I x).toList.countP (fun i => (I.setOf i).contains a)
      = (List.range I.numSets).countP
          (fun i => x.getD i false && (I.setOf i).contains a) := by
  show ((List.range I.numSets).filter (fun i => x.getD i false)).countP _ = _
  rw [List.countP_filter]
  exact List.countP_congr (fun i _ => by simp [Bool.and_comm])

/-- **Soundness of the encoding**: a zero of the objective decodes to an exact cover.

`penaltyDoubled = 0` says every one of the `2m` rows has row sum `1`; reading the lower `m`
rows through `contains_rowsOfSet_lo` says every ground-set element lies in exactly one chosen
subset, which is exactly what `coversExactly` checks. -/
theorem decode_coversExactly (I : Instance) (hI : I.Wf) (x : Array Bool)
    (hx : (qubo I).penaltyDoubled x = 0) :
    coversExactly I (decode I x) = true := by
  have hW := qubo_wf I hI
  rw [coversExactly, List.all_eq_true]
  intro a ha
  have ha' : a < I.groundSize := List.mem_range.mp ha
  have harow : a < (qubo I).nrows := by simpa using by omega
  -- the row sum of row `a` is `b̂_a = 1`
  have hrow := rowSums_eq_bhat_of_penalty_zero (qubo I) x hx harow
  rw [Problem.rowSums_spec (qubo I) hW x harow, qubo_bhat I (by simpa using harow)] at hrow
  -- rewrite the count into the checker's count
  have hcnt : (List.range (qubo I).nvars).countP
        (fun u => x.getD u false && ((qubo I).rowsOf.getD u #[]).contains a)
      = (List.range I.numSets).countP (fun i => x.getD i false && (I.setOf i).contains a) := by
    refine List.countP_congr (fun i hi => ?_)
    have hi' : i < I.numSets := List.mem_range.mp hi
    rw [qubo_rowsOf I hi', contains_rowsOfSet_lo I i ha']
  rw [hcnt] at hrow
  rw [beq_iff_eq, countP_decode]
  exact_mod_cast hrow

/-! ## Worked examples

The `decide`s below are `decide +kernel`: `Problem.rowSums` scatters through a
`for u in [0:P.nvars]`, and `Std.Range.forIn` — like `Array.map` and `Array.contains` — is
defined by well-founded recursion, so it does not reduce in the elaborator's `whnf`. Kernel
reduction handles it; this is ordinary `decide`, not `native_decide`. -/

/-- A solvable instance: `U = {0,1,2,3}` with five subsets. `S₀ ∪ S₁` and `S₂ ∪ S₃` are the two
exact covers; `S₄ = {1,2}` is a decoy that meets every other set. -/
def ex1 : Instance := ⟨4, #[#[0, 1], #[2, 3], #[0, 2], #[1, 3], #[1, 2]]⟩

theorem ex1_wf : ex1.Wf := by
  constructor
  · decide
  · decide

/-- Five variables, eight rows (two copies of four ground-set elements). -/
example : (qubo ex1).nvars = 5 ∧ (qubo ex1).nrows = 8 := by decide +kernel

/-- `θ̂ᵢ = −|Sᵢ| = −2` for every column here; `ex3` below has columns of different degrees. -/
example : ∀ i < 5, (qubo ex1).theta.getD i 0 = -2 := by decide +kernel

/-- `S₀ ∪ S₁ = {0,1} ∪ {2,3} = U` is an exact cover, and the encoding sees it. -/
example : (qubo ex1).penaltyDoubled #[true, true, false, false, false] = 0 := by decide +kernel

example : decode ex1 #[true, true, false, false, false] = #[0, 1] := by decide +kernel

example : coversExactly ex1 #[0, 1] = true := by decide +kernel

/-- `S₂ ∪ S₃ = {0,2} ∪ {1,3} = U` is the other exact cover. -/
example : (qubo ex1).penaltyDoubled #[false, false, true, true, false] = 0 := by decide +kernel

/-- A *cover* that is not exact — `S₀ ∪ S₄ ∪ S₁` covers `1` and `2` twice — is not a zero. -/
example : (qubo ex1).penaltyDoubled #[true, true, false, false, true] ≠ 0 := by decide +kernel

/-- Soundness, run on the first solution. -/
example : coversExactly ex1 (decode ex1 #[true, true, false, false, false]) = true :=
  decode_coversExactly ex1 ex1_wf _ (by decide +kernel)

/-! The whole search space of `ex1`: at each of the `2⁵` assignments the objective is zero
exactly when the decoded subfamily is an exact cover. `decode_coversExactly` is the `→` half of
this, proved for every instance; the scan also exhibits the converse here. Prints `true`. -/
#eval (List.range 32).all fun m =>
  let x := (Array.range 5).map m.testBit
  ((qubo ex1).penaltyDoubled x == 0) == coversExactly ex1 (decode ex1 x)

/-! The two zeros are `S₀ ∪ S₁` and `S₂ ∪ S₃`. Prints `#[#[0, 1], #[2, 3]]`. -/
#eval ((List.range 32).filterMap fun m =>
  let x := (Array.range 5).map m.testBit
  if (qubo ex1).penaltyDoubled x == 0 then some (decode ex1 x) else none).toArray

/-- An unsolvable instance: `U = {0,1,2}`, `S₀ = {0,1}`, `S₁ = {1,2}`. Element `0` forces `S₀`
and element `2` forces `S₁`, but then `1` is covered twice. -/
def ex2 : Instance := ⟨3, #[#[0, 1], #[1, 2]]⟩

theorem ex2_wf : ex2.Wf := by
  constructor
  · decide
  · decide

/-- **No assignment reaches zero.** Only the first `nvars = 2` entries of the bit vector are
read, so these four arrays exhaust the search space. -/
example : ∀ x ∈ [#[false, false], #[true, false], #[false, true], #[true, true]],
    (qubo ex2).penaltyDoubled x ≠ 0 := by decide +kernel

/-! The same scan as for `ex1`: nothing is an exact cover and nothing reaches zero.
Prints `true`. -/
#eval (List.range 4).all fun m =>
  let x := (Array.range 2).map m.testBit
  ((qubo ex2).penaltyDoubled x != 0) && !coversExactly ex2 (decode ex2 x)

/-- An instance with columns of **different** degrees — `|S₀| = 1` and `|S₁| = 3`, so degrees
`2` and `6`. Any proof that smuggled in regularity would fail here. -/
def ex3 : Instance := ⟨4, #[#[0], #[1, 2, 3], #[0, 1], #[2, 3]]⟩

theorem ex3_wf : ex3.Wf := by
  constructor
  · decide
  · decide

example : ((qubo ex3).rowsOf.getD 0 #[]).size ≠ ((qubo ex3).rowsOf.getD 1 #[]).size := by decide +kernel

/-- `S₀ ∪ S₁ = {0} ∪ {1,2,3} = U`: an exact cover with an odd-sized subset, which is exactly the
case the row duplication exists to handle. -/
example : (qubo ex3).penaltyDoubled #[true, true, false, false] = 0 := by decide +kernel

example : coversExactly ex3 (decode ex3 #[true, true, false, false]) = true :=
  decode_coversExactly ex3 ex3_wf _ (by decide +kernel)

/-! ## The network

`ex1` on the repository's `{0,1}` Boltzmann machine, via the degree-free bridge of `QUBO.Net`. -/

instance : Nonempty (Fin (qubo ex1).nvars) := ⟨⟨0, by decide +kernel⟩⟩

/-- **The energy bridge at an exact-cover instance.** The HNBM `{0,1}` Boltzmann Hamiltonian of
`netParams (qubo ex1)` is `(‖Âx−b̂‖² − ‖b̂‖²)/2`, so minimising the network energy is solving the
exact-cover instance. -/
theorem ex1_energy (x : Fin (qubo ex1).nvars → Bool) :
    HopfieldEnergy.zeroOneHamiltonian (Problem.netParams (qubo ex1))
        (Problem.stateOfBits (qubo ex1) x)
      = (Problem.penaltyR (qubo ex1) x - Problem.constR (qubo ex1)) / 2 :=
  Problem.zeroOneHamiltonian_eq (qubo ex1) (qubo_wf ex1 ex1_wf) x

end ExactCover
end QUBO

