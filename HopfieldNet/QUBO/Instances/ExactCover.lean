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

## Why `theta` has to be stored doubled — the sharpest case in the library

`Problem.theta` is an `Array Int`, and it holds `2 θ̂_u`, not `θ̂_u`: `Wf.theta_eq` reads

  `theta u = deg(u) − 2 Σ_{r ∋ u} b̂_r`.

Exact cover is where that convention earns its keep. One row per ground-set element makes the
degree of column `i` equal to `|Sᵢ|`, and with `b̂ ≡ 1` we get `Σ_{r ∋ i} b̂_r = |Sᵢ|`, hence

  `theta i = |Sᵢ| − 2|Sᵢ| = −|Sᵢ|`,

an integer **whatever the parity of `|Sᵢ|`**. Had `theta` stored `θ̂` directly it would have to
hold `½|Sᵢ| − |Sᵢ| = −|Sᵢ|/2`, which is not an integer as soon as some subset has odd size — and
`ex3` below contains the singleton `S₀ = {0}`. Nothing about exact cover controls the parity of a
subset's size, so under the halved convention this encoding is only representable at all after
taking **two** copies of every ground-set row (rows `α` and `α + m` both asserting "element `α` is
covered once") to force every degree even, at the price of doubling `nrows`, the objective value
and the work per sweep. The doubled `theta` removes that entirely: one row per element, `nrows =
m`, `θ̂` exact. `Problem.thetaR` halves on the way to `ℝ`, where halving is free.

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
* `encode_penalty_zero` : `coversExactly sel → penaltyDoubled (encode sel) = 0`, its
  completeness, with no hypothesis on `sel`.
* `exists_zero_iff_coverable` : the two combined — the QUBO has a zero **iff** the instance has an
  exact cover. Hence `ex2_no_cover`: `ex2` has no exact cover, upgraded from the finite search of
  `ex2_no_zero_of_size_two`.
* `encode_decode`, `decode_encode_perm` : the two maps are mutually inverse (bitwise, resp. up to
  the order of the listed indices).
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

/-- **The converse: hitting every target makes the objective vanish.**

The easy direction — each summand of `‖Âx−b̂‖²` is separately zero — and the half that turns the
encoding into a decision procedure rather than a one-sided test. -/
theorem penalty_zero_of_rowSums_eq (P : Problem) (x : Array Bool)
    (h : ∀ r < P.nrows, (P.rowSums x).getD r 0 = P.bhat.getD r 0) :
    P.penaltyDoubled x = 0 := by
  have hpen : P.penaltyDoubled x
      = (Array.range P.nrows).foldl
          (fun acc r => acc + ((P.rowSums x).getD r 0 - P.bhat.getD r 0) *
            ((P.rowSums x).getD r 0 - P.bhat.getD r 0)) 0 := rfl
  rw [hpen, ← Array.foldl_toList, Array.toList_range]
  refine (foldl_sq_zero_iff (fun r => (P.rowSums x).getD r 0 - P.bhat.getD r 0)
    (List.range P.nrows) 0 le_rfl).mpr ⟨rfl, fun r hr => ?_⟩
  have := h r (List.mem_range.mp hr)
  omega

/-- **A unique witness in an arbitrary array is a unique witness in the range.**

If exactly one entry of `sel` — counted *with multiplicity*, as `List.countP` does — satisfies a
predicate `p` whose witnesses are all `< N`, then exactly one `i < N` both occurs in `sel` and
satisfies `p`. This is what lets completeness be proved with **no** hypothesis on `sel`: a
repeated index would be counted twice by `countP`, so `countP p = 1` already rules out any
duplicate that `p` can see, and an out-of-range index is invisible to `p`. -/
theorem countP_range_of_countP_eq_one {N : Nat} (sel : Array Nat) (p : Nat → Bool)
    (hp : ∀ i, p i = true → i < N) (h : sel.toList.countP p = 1) :
    (List.range N).countP (fun i => sel.contains i && p i) = 1 := by
  rw [List.countP_eq_length_filter] at h
  obtain ⟨y, hy⟩ := List.length_eq_one_iff.mp h
  have hymem : y ∈ sel.toList ∧ p y = true :=
    List.mem_filter.mp (by rw [hy]; exact List.mem_singleton_self y)
  have huniq : ∀ z ∈ sel.toList, p z = true → z = y := by
    intro z hz hpz
    have hzf : z ∈ sel.toList.filter p := List.mem_filter.mpr ⟨hz, hpz⟩
    rw [hy] at hzf
    exact List.mem_singleton.mp hzf
  have hnd : ((List.range N).filter (fun i => sel.contains i && p i)).Nodup :=
    List.Nodup.filter _ List.nodup_range
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup hnd]
  have hfin : ((List.range N).filter (fun i => sel.contains i && p i)).toFinset = {y} := by
    ext z
    simp only [List.mem_toFinset, List.mem_filter, List.mem_range, Bool.and_eq_true,
      Array.contains_iff_mem, Finset.mem_singleton]
    constructor
    · rintro ⟨-, hz, hpz⟩
      exact huniq z (Array.mem_toList_iff.mpr hz) hpz
    · rintro rfl
      exact ⟨hp _ hymem.2, Array.mem_toList_iff.mp hymem.1, hymem.2⟩
  rw [hfin]
  simp

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

/-- Out of range there is no subset: an index `≥ numSets` names the empty set, so it can never
help cover anything. Used to see that `coversExactly` ignores out-of-range indices. -/
theorem setOf_of_le (I : Instance) {i : Nat} (hi : I.numSets ≤ i) : I.setOf i = #[] := by
  unfold Instance.setOf
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by simpa [Instance.numSets] using hi)]
  rfl

/-- The input is sane: every subset is duplicate-free and inside the ground set. Duplicates
would make `Â` integer-valued rather than 0/1. -/
structure Wf (I : Instance) : Prop where
  /-- No subset repeats an element. -/
  nodup : ∀ i < I.numSets, (I.setOf i).toList.Nodup
  /-- Every listed element is a ground-set element. -/
  mem_lt : ∀ i < I.numSets, ∀ a ∈ I.setOf i, a < I.groundSize

/-! ### The columns and rows

`Â` is the incidence matrix of the family itself: row `α` per ground-set element, column `i` per
subset, `Â_{α i} = 1` iff `α ∈ Sᵢ`. So the rows met by column `i` are literally the elements of
`Sᵢ` — there is no separate `rowsOfSet`, and `qubo.rowsOf` is `Instance.setOf`. Only `colsOfRow`,
the transpose, needs computing. -/

/-- The columns meeting row `r`: the subsets containing the ground-set element `r`.

Built with `List.filter` and not `Array.filter`: the latter carries an optional
`stop := as.size` argument whose unification forces `(Array.range _).size` to whnf. -/
def colsOfRow (I : Instance) (r : Nat) : Array Nat :=
  ((List.range I.numSets).filter fun i => (I.setOf i).contains r).toArray

end Instance

/-! ## The QUBO -/

open Instance

/-- **Exact cover as a `QUBO.Problem`.**

`k = |sets|` variables, `m` rows, `b̂ ≡ 1`, `θ̂_i = −|Sᵢ|/2` (so `theta i = −|Sᵢ|`), `‖b̂‖² = m`.
Every field is a `map` over an index range — never a `for` loop with `set!` — so each is
characterised pointwise by `map_range_getD`. -/
def qubo (I : Instance) : Problem where
  nvars := I.numSets
  nrows := I.groundSize
  varOf := Array.range I.numSets
  rowsOf := (Array.range I.numSets).map I.setOf
  varsOf := (Array.range I.groundSize).map I.colsOfRow
  bhat := (Array.range I.groundSize).map fun _ => 1
  -- stored doubled: `2θ̂_i = deg(i) − 2 Σ_{r ∋ i} b̂_r = |Sᵢ| − 2|Sᵢ|`, integer at any parity
  theta := (Array.range I.numSets).map fun i => -((I.setOf i).size : Int)
  constDoubled := (I.groundSize : Int)
  base := #[]

@[simp] theorem qubo_nvars (I : Instance) : (qubo I).nvars = I.numSets := rfl
@[simp] theorem qubo_nrows (I : Instance) : (qubo I).nrows = I.groundSize := rfl

theorem qubo_rowsOf (I : Instance) {u : Nat} (hu : u < I.numSets) :
    (qubo I).rowsOf.getD u #[] = I.setOf u :=
  map_range_getD _ _ _ hu

theorem qubo_bhat (I : Instance) {r : Nat} (hr : r < I.groundSize) :
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

/-! ### Structure of a column

There is nothing left to say. Under the duplicated encoding this section held six lemmas —
`mem_rowsOfSet`, `rowsOfSet_size`, `rowsOfSet_nodup`, `rowsOfSet_mem_lt` and the shift
dictionary `contains_rowsOfSet_lo` / `contains_rowsOfSet_hi` / `contains_rowsOfSet`, which
translated "row `r < 2m`" into "ground-set element `r % m`". With one row per element the column
of `qubo I` *is* `I.setOf i` (`qubo_rowsOf`), its size is `|Sᵢ|`, and the two structural facts
about it — duplicate-freeness and in-rangeness — are verbatim the two fields of `Instance.Wf`.
So the whole dictionary is `qubo_rowsOf`, and every proof below reads a row index directly. -/

/-! ### Well-formedness -/

/-- **The exact-cover QUBO is a well-formed 0/1 QUBO in canonical form.**

Hence `QUBO.Problem.zeroOneHamiltonian_eq` applies: the HNBM `{0,1}` Boltzmann energy of
`netParams (qubo I)` is `(‖Âx−b̂‖² − ‖b̂‖²)/2`. -/
theorem qubo_wf (I : Instance) (hI : I.Wf) : (qubo I).Wf where
  nodup := by
    intro u hu
    rw [qubo_rowsOf I hu]
    exact hI.nodup u hu
  mem_lt := by
    intro u hu r hr
    rw [qubo_rowsOf I hu] at hr
    exact hI.mem_lt u hu r hr
  theta_eq := by
    intro u hu
    have hrows : (qubo I).rowsOf.getD u #[] = I.setOf u := qubo_rowsOf I hu
    have hsum : ∑ r ∈ Finset.range (qubo I).nrows,
          (if ((qubo I).rowsOf.getD u #[]).contains r then (qubo I).bhat.getD r 0 else 0)
        = ((I.setOf u).size : Int) := by
      rw [show (qubo I).nrows = I.groundSize from rfl]
      rw [Finset.sum_congr rfl (fun r hr => by
        rw [hrows, qubo_bhat I (Finset.mem_range.mp hr)])]
      exact sum_indicator_card (I.setOf u) (hI.nodup u hu) (hI.mem_lt u hu)
    -- `theta u = |Sᵢ| − 2|Sᵢ| = −|Sᵢ|`: no parity condition, and no factor of two to divide out
    rw [qubo_theta I hu, hsum, hrows]
    ring
  const_eq := by
    show (I.groundSize : Int) = _
    rw [Finset.sum_congr rfl (fun r hr => by
      rw [qubo_bhat I (Finset.mem_range.mp (by simpa using hr))])]
    simp

/-! ## The incidence

Exact cover as a value of `QUBO.Incidence`, with `qubo I` its (trivial) column restriction: no
column is deleted, so `varOf` is the identity. -/

/-- **The exact-cover incidence**: `m` rows, one column per subset, column `i` being `Sᵢ`. -/
def inc (I : Instance) (hI : I.Wf) : Incidence where
  nvars := I.numSets
  nrows := I.groundSize
  rowsOf := I.setOf
  nodup := fun _ h => hI.nodup _ h
  mem_lt := fun _ h => hI.mem_lt _ h

/-- The problem refines its incidence along the identity. -/
theorem refines (I : Instance) (hI : I.Wf) : Problem.Refines (inc I hI) (qubo I) where
  nrows_eq := rfl
  varOf_lt := fun u hu => by rw [qubo_varOf I hu]; exact hu
  rowsOf_eq := fun u hu => by rw [qubo_rowsOf I hu, qubo_varOf I hu]; rfl
  varOf_inj := fun u hu v hv h => by rwa [qubo_varOf I hu, qubo_varOf I hv] at h

/-! ## Encoding, decoding and checking -/

/-- **The decoder**: the chosen subfamily, as the array of indices `i` with `xᵢ = 1`. -/
def decode (I : Instance) (x : Array Bool) : Array Nat :=
  ((List.range I.numSets).filter fun i => x.getD i false).toArray

/-- **The encoder**: the characteristic vector of a subfamily, one bit per subset. -/
def encode (I : Instance) (sel : Array Nat) : Array Bool :=
  (Array.range I.numSets).map fun i => sel.contains i

/-- **The checker**: every ground-set element is covered exactly once by the chosen subfamily. -/
def coversExactly (I : Instance) (sel : Array Nat) : Bool :=
  (List.range I.groundSize).all fun a =>
    sel.toList.countP (fun i => (I.setOf i).contains a) == 1

/-- The encoder has one bit per decision variable. -/
@[simp] theorem encode_size (I : Instance) (sel : Array Nat) :
    (encode I sel).size = I.numSets := by simp [encode]

/-- Reading the encoder: bit `i` is set exactly when subset `i` is chosen. -/
theorem encode_getD (I : Instance) (sel : Array Nat) {i : Nat} (hi : i < I.numSets) :
    (encode I sel).getD i false = sel.contains i :=
  map_range_getD _ _ _ hi

/-- Reading the decoder. -/
theorem mem_decode (I : Instance) (x : Array Bool) (i : Nat) :
    i ∈ decode I x ↔ (i < I.numSets ∧ x.getD i false = true) := by
  rw [← Array.mem_toList_iff]
  show i ∈ ((List.range I.numSets).filter (fun i => x.getD i false)).toArray.toList ↔ _
  simp [List.mem_filter]

/-- **The decoder produces a duplicate-free selection** — it is a sublist of `range numSets`. -/
theorem decode_nodup (I : Instance) (x : Array Bool) : (decode I x).toList.Nodup := by
  show ((List.range I.numSets).filter _).toArray.toList.Nodup
  simpa using List.Nodup.filter (fun i => x.getD i false) List.nodup_range

/-- **The decoder produces an in-range selection.** -/
theorem decode_mem_lt (I : Instance) (x : Array Bool) : ∀ i ∈ decode I x, i < I.numSets :=
  fun _ hi => ((mem_decode I x _).mp hi).1

/-! ### Round trips

`encode` and `decode` are mutually inverse on the data they are meant for: bitwise on the
variables, and up to the order of the listed indices on duplicate-free in-range selections. -/

/-- **`encode ∘ decode = id`** on the bits that the objective reads. (It is not the identity on
all of `Array Bool`: `encode` truncates to `numSets` entries.) -/
theorem encode_decode (I : Instance) (x : Array Bool) {i : Nat} (hi : i < I.numSets) :
    (encode I (decode I x)).getD i false = x.getD i false := by
  rw [encode_getD I _ hi]
  by_cases h : x.getD i false = true
  · rw [h]; exact Array.contains_iff_mem.mpr ((mem_decode I x i).mpr ⟨hi, h⟩)
  · simp only [Bool.not_eq_true] at h
    rw [h, Bool.eq_false_iff, ne_eq, Array.contains_iff_mem]
    intro hm
    rw [((mem_decode I x i).mp hm).2] at h
    exact absurd h (by simp)

/-- **`decode ∘ encode = id` up to order** on duplicate-free, in-range selections: `decode`
returns the same indices, in increasing order. -/
theorem decode_encode_perm (I : Instance) {sel : Array Nat} (hnd : sel.toList.Nodup)
    (hlt : ∀ i ∈ sel, i < I.numSets) :
    (decode I (encode I sel)).toList.Perm sel.toList := by
  have hfil : (decode I (encode I sel)).toList
      = (List.range I.numSets).filter (fun i => sel.contains i) := by
    show ((List.range I.numSets).filter (fun i => (encode I sel).getD i false)).toArray.toList = _
    rw [List.toList_toArray]
    exact List.filter_congr (fun i hi => by rw [encode_getD I sel (List.mem_range.mp hi)])
  rw [hfil]
  refine List.perm_of_nodup_nodup_toFinset_eq (List.Nodup.filter _ List.nodup_range) hnd ?_
  ext i
  simp only [List.mem_toFinset, List.mem_filter, List.mem_range, Array.contains_iff_mem,
    Array.mem_toList_iff]
  exact ⟨fun h => h.2, fun h => ⟨hlt i h, h⟩⟩

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

`penaltyDoubled = 0` says every one of the `m` rows has row sum `1`, and row `a` *is* the
constraint "element `a` is covered once" — column `i` meets it exactly when `a ∈ Sᵢ`
(`qubo_rowsOf`). That is exactly what `coversExactly` checks. -/
theorem decode_coversExactly (I : Instance) (hI : I.Wf) (x : Array Bool)
    (hx : (qubo I).penaltyDoubled x = 0) :
    coversExactly I (decode I x) = true := by
  have hW := qubo_wf I hI
  rw [coversExactly, List.all_eq_true]
  intro a ha
  have ha' : a < I.groundSize := List.mem_range.mp ha
  have harow : a < (qubo I).nrows := by simpa using ha'
  -- the row sum of row `a` is `b̂_a = 1`
  have hrow := rowSums_eq_bhat_of_penalty_zero (qubo I) x hx harow
  rw [Problem.rowSums_spec (qubo I) hW x harow, qubo_bhat I ha'] at hrow
  -- rewrite the count into the checker's count
  have hcnt : (List.range (qubo I).nvars).countP
        (fun u => x.getD u false && ((qubo I).rowsOf.getD u #[]).contains a)
      = (List.range I.numSets).countP (fun i => x.getD i false && (I.setOf i).contains a) := by
    refine List.countP_congr (fun i hi => ?_)
    rw [qubo_rowsOf I (List.mem_range.mp hi)]
  rw [hcnt] at hrow
  rw [beq_iff_eq, countP_decode]
  exact_mod_cast hrow

/-! ## Completeness

The converse of `decode_coversExactly`: an exact cover encodes to a zero. Together the two give
`exists_zero_iff_coverable`, which is what makes a *negative* answer from the QUBO mean
something about exact cover. -/

/-- **Completeness of the encoding**: an exact cover encodes to a zero of the objective.

No hypothesis whatsoever on `sel` — not duplicate-freeness, not in-rangeness. That looks too
good, since `coversExactly` counts with `List.countP`, i.e. *with multiplicity*; the point is
that this makes `coversExactly` self-policing. If `sel` repeated an index `i` with
`a ∈ Sᵢ` then element `a` would be counted twice and the checker would already be `false`, and an
index `i ≥ numSets` has `Sᵢ = ∅` (`Instance.setOf_of_le`) so it is invisible to the checker and to
`encode`'s characteristic vector alike. `countP_range_of_countP_eq_one` is where this is used.

The one hypothesis is `hI : I.Wf` on the *instance* — a real restriction, but the same one
`qubo_wf` and `decode_coversExactly` already carry: out-of-range elements of a subset would be
dropped by the row construction, and a repeated element would make `Â` non-`0/1`. -/
theorem encode_penalty_zero (I : Instance) (hI : I.Wf) {sel : Array Nat}
    (hsel : coversExactly I sel = true) :
    (qubo I).penaltyDoubled (encode I sel) = 0 := by
  have hW := qubo_wf I hI
  refine penalty_zero_of_rowSums_eq (qubo I) _ (fun r hr => ?_)
  have hr' : r < I.groundSize := by simpa using hr
  rw [Problem.rowSums_spec (qubo I) hW _ hr, qubo_bhat I hr']
  -- the row sum of row `r` counts the chosen subsets containing the element `r`
  have hcnt : (List.range (qubo I).nvars).countP
        (fun u => (encode I sel).getD u false && ((qubo I).rowsOf.getD u #[]).contains r)
      = (List.range I.numSets).countP
          (fun i => sel.contains i && (I.setOf i).contains r) := by
    refine List.countP_congr (fun i hi => ?_)
    have hi' : i < I.numSets := List.mem_range.mp hi
    rw [encode_getD I sel hi', qubo_rowsOf I hi']
  rw [hcnt]
  -- and the checker says that count is one
  have hcov : sel.toList.countP (fun i => (I.setOf i).contains r) = 1 := by
    simpa using (List.all_eq_true.mp hsel) r (List.mem_range.mpr hr')
  have hp : ∀ i, ((I.setOf i).contains r) = true → i < I.numSets := by
    intro i hi
    by_contra hcon
    rw [setOf_of_le I (by omega)] at hi
    simp at hi
  rw [countP_range_of_countP_eq_one sel _ hp hcov]
  rfl

/-- **The headline: the QUBO has a zero iff the instance has an exact cover.**

`→` is `decode_coversExactly`, `←` is `encode_penalty_zero`. No round trip is needed because
neither side of the equivalence mentions the other's witness; `decode_encode_perm` and
`encode_decode` record that the two maps are nevertheless mutually inverse.

Read from right to left this says the encoding is complete; read from left to right, that it is
sound. Contrapositive of `←`: *no zero of the objective* is a proof that no exact cover
exists (`ex2_no_cover` below). -/
theorem exists_zero_iff_coverable (I : Instance) (hI : I.Wf) :
    (∃ x, (qubo I).penaltyDoubled x = 0) ↔ (∃ sel, coversExactly I sel = true) :=
  ⟨fun ⟨x, hx⟩ => ⟨decode I x, decode_coversExactly I hI x hx⟩,
   fun ⟨sel, hsel⟩ => ⟨encode I sel, encode_penalty_zero I hI hsel⟩⟩

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

/-- Five variables, four rows — one per ground-set element. -/
example : (qubo ex1).nvars = 5 ∧ (qubo ex1).nrows = 4 := by decide +kernel

/-- `2θ̂ᵢ = −|Sᵢ| = −2` for every column here, since every subset of `ex1` has size two
(`theta` is stored doubled); `ex3` below has columns of different degrees, one of them odd. -/
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

/-- Completeness, run on the same solution given as a subfamily. -/
example : (qubo ex1).penaltyDoubled (encode ex1 #[0, 1]) = 0 :=
  encode_penalty_zero ex1 ex1_wf (by decide +kernel)

example : encode ex1 #[0, 1] = #[true, true, false, false, false] := by decide +kernel

/-- The iff, right to left: `ex1` is coverable, so its QUBO has a zero. -/
example : ∃ x, (qubo ex1).penaltyDoubled x = 0 :=
  (exists_zero_iff_coverable ex1 ex1_wf).mpr ⟨#[2, 3], by decide +kernel⟩

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
theorem ex2_no_zero_of_size_two :
    ∀ x ∈ [#[false, false], #[true, false], #[false, true], #[true, true]],
    (qubo ex2).penaltyDoubled x ≠ 0 := by decide +kernel

/-- **`ex2` has no exact cover** — a statement about exact covers, not about the QUBO.

This is the point of completeness. The finite check above says nothing about the infinitely many
`x : Array Bool`; `encode_penalty_zero` turns a *hypothetical cover* into one of these four
vectors, and the check then refutes it. No side condition on `sel`: literally no array of indices
passes `coversExactly ex2`. -/
theorem ex2_no_cover : ¬ ∃ sel, coversExactly ex2 sel = true := by
  rintro ⟨sel, hsel⟩
  have h0 := encode_penalty_zero ex2 ex2_wf hsel
  have henc : encode ex2 sel = #[sel.contains 0, sel.contains 1] := by
    show (Array.range ex2.numSets).map _ = _
    rw [show ex2.numSets = 2 from rfl]
    simp [Array.range_succ, show Array.range 0 = #[] from rfl]
  rw [henc] at h0
  revert h0
  cases hb0 : sel.contains 0 <;> cases hb1 : sel.contains 1 <;> decide +kernel

/-- **And hence no zero at all**, over every `x : Array Bool` — the finite check above upgraded
through the iff. -/
theorem ex2_no_zero : ¬ ∃ x, (qubo ex2).penaltyDoubled x = 0 :=
  fun h => ex2_no_cover ((exists_zero_iff_coverable ex2 ex2_wf).mp h)

/-! The same scan as for `ex1`: nothing is an exact cover and nothing reaches zero.
Prints `true`. -/
#eval (List.range 4).all fun m =>
  let x := (Array.range 2).map m.testBit
  ((qubo ex2).penaltyDoubled x != 0) && !coversExactly ex2 (decode ex2 x)

/-- An instance with columns of **different, and odd, degrees** — `|S₀| = 1` and `|S₁| = 3`, so
`theta 0 = −1` and `theta 1 = −3`. Any proof that smuggled in regularity would fail here, and
under the halved `theta` of the module docstring this instance would not be representable at all:
`θ̂₀ = −1/2 ∉ ℤ`. -/
def ex3 : Instance := ⟨4, #[#[0], #[1, 2, 3], #[0, 1], #[2, 3]]⟩

theorem ex3_wf : ex3.Wf := by
  constructor
  · decide
  · decide

example : ((qubo ex3).rowsOf.getD 0 #[]).size ≠ ((qubo ex3).rowsOf.getD 1 #[]).size := by decide +kernel

/-- The odd degrees, and the odd doubled thresholds they produce. -/
example : (qubo ex3).theta.getD 0 0 = -1 ∧ (qubo ex3).theta.getD 1 0 = -3 := by decide +kernel

/-- `S₀ ∪ S₁ = {0} ∪ {1,2,3} = U`: an exact cover with odd-sized subsets, which is exactly the
case the doubled `theta` exists to handle. -/
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

