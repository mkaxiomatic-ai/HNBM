/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.CNS.DecodeSound

/-!
# From a zero reduced penalty to a verified completion

`CNS.Embed` proves the reduced objective is the paper's `‖Ax − e‖²` under `embed`, and
`CNS.DecodeSound` proves a zero penalty *decodes* to a solved grid. This module closes the last
step the solver actually takes: it writes its answer back with `Problem.toGrid`, not with
`decode`, and it must extend the puzzle it was given.

  `(Problem.ofGrid g).penaltyDoubled x = 0  →  (P.toGrid x).isSolution ∧ g.extends' (P.toGrid x)`

That conjunction is exactly `CNS.accepts`, the certificate `Solver.solveCertified` checks at run
time. With `toGrid_completes` the check is provably redundant on a zero-penalty result — the
search cannot report `p(x) = 0` on anything but a genuine completion of the original grid.

The counting toolkit, the row/column duality and the `embed` bridge are imported rather than
reproved; what is new here is the `toGrid` scatter, the well-formedness of Algorithm 1's output,
and reading `isSolution` off the four families for an arbitrary grid.
-/

namespace CNS

open QUBO
open QUBO.Problem
namespace Complete

open CNS

/-! ## List counting preliminaries -/

theorem countP_congr' {p q : Nat → Bool} :
    ∀ l : List Nat, (∀ v ∈ l, p v = q v) → l.countP p = l.countP q := CNS.countP_congr


theorem countOn_eq_countP (x : Array Bool) (l : List Nat) :
    countOn x l = (l.countP (fun v => x.getD v false) : Int) := by
  unfold countOn
  rw [CNS.countOn_foldl x l 0, zero_add]

theorem find?_eq_some_of_unique {p : Nat → Bool} :
    ∀ (l : List Nat) (u : Nat), u ∈ l → p u = true → (∀ w ∈ l, p w = true → w = u) →
      l.find? p = some u := by
  intro l
  induction l with
  | nil => intro u hu; exact absurd hu (by simp)
  | cons w t ih =>
    intro u hu hpu huniq
    by_cases hw : p w = true
    · rw [List.find?_cons_of_pos hw, huniq w (List.mem_cons_self ..) hw]
    · rw [List.find?_cons_of_neg (by simpa using hw)]
      have hne : u ≠ w := by rintro rfl; exact hw hpu
      refine ih u ?_ hpu (fun z hz => huniq z (List.mem_cons_of_mem _ hz))
      rcases List.mem_cons.mp hu with h | h
      · exact absurd h hne
      · exact h

/-! ## The reduced instance, pointwise -/


def survList (R : Reduced) : List Nat :=
  (List.range numVars).filter fun v => !(R.isFixed.getD v false)

theorem getD_map_range {β : Type _} [Inhabited β] (N : Nat) (f : Nat → β) {i : Nat} (hi : i < N)
    (d : β) : ((Array.range N).map f).getD i d = f i := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa using hi)]
  simp

theorem getD_toArray (l : List Nat) (i d : Nat) : (l.toArray).getD i d = l.getD i d := by
  rw [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
  simp

variable (R : Reduced)

theorem oR_nvars : (Problem.ofReduced R).nvars = (survList R).length := by
  simp only [Problem.ofReduced, Problem.survivors, survList, List.size_toArray]

theorem oR_varOf (u : Nat) : (Problem.ofReduced R).varOf.getD u 0 = (survList R).getD u 0 := by
  simp only [Problem.ofReduced, Problem.survivors, survList]
  exact getD_toArray _ _ _


theorem oR_base : (Problem.ofReduced R).base = R.grid.cells := by simp only [Problem.ofReduced]

theorem mem_survList {v : Nat} :
    v ∈ survList R ↔ (v < numVars ∧ R.isFixed.getD v false = false) := by
  simp only [survList, List.mem_filter, List.mem_range, Bool.not_eq_true']

theorem varOf_mem_survList {u : Nat} (hu : u < (Problem.ofReduced R).nvars) :
    (Problem.ofReduced R).varOf.getD u 0 ∈ survList R := by
  rw [oR_varOf]
  have hlt : u < (survList R).length := by rwa [← oR_nvars]
  rw [← List.getElem_eq_getD (h := hlt)]
  exact List.getElem_mem hlt

/-- Every survivor is named by exactly one reduced index. -/
theorem exists_index_of_mem_survList {v : Nat} (hv : v ∈ survList R) :
    ∃ u, u < (Problem.ofReduced R).nvars ∧ (Problem.ofReduced R).varOf.getD u 0 = v := by
  obtain ⟨u, hu, hget⟩ := List.getElem_of_mem hv
  exact ⟨u, by rw [oR_nvars]; exact hu, by rw [oR_varOf, ← List.getElem_eq_getD (h := hu), hget]⟩

theorem redIndex_varOf {u : Nat} (hu : u < (Problem.ofReduced R).nvars) :
    (Problem.ofReduced R).redIndex ((Problem.ofReduced R).varOf.getD u 0) = some u := by
  refine find?_eq_some_of_unique _ u (List.mem_range.mpr hu) (by simp) ?_
  intro w hw hpw
  exact (Problem.ofReduced_valid R).varOf_inj w (List.mem_range.mp hw) u hu (by simpa using hpw)

theorem redIndex_fixed {v : Nat} (hfix : R.isFixed.getD v false = true) :
    (Problem.ofReduced R).redIndex v = none := by
  refine List.find?_eq_none.mpr ?_
  intro w hw hpw
  have hmem := varOf_mem_survList R (List.mem_range.mp hw)
  rw [(by simpa using hpw : (Problem.ofReduced R).varOf.getD w 0 = v)] at hmem
  have hfalse := ((mem_survList R).mp hmem).2
  rw [hfix] at hfalse
  exact Bool.noConfusion hfalse

/-! ## The embedding -/

theorem embed_getD_varOf (x : Array Bool) {u : Nat} (hu : u < (Problem.ofReduced R).nvars) :
    ((Problem.ofReduced R).embed R.fixedVal x).getD ((Problem.ofReduced R).varOf.getD u 0) false
      = x.getD u false := by
  have hlt : (Problem.ofReduced R).varOf.getD u 0 < numVars :=
    (Problem.ofReduced_valid R).varOf_lt u hu
  rw [Problem.embed, getD_map_range _ _ hlt, redIndex_varOf R hu]

theorem embed_getD_fixed (x : Array Bool) {v : Nat} (hv : v < numVars)
    (hfix : R.isFixed.getD v false = true) :
    ((Problem.ofReduced R).embed R.fixedVal x).getD v false = R.fixedVal.getD v false := by
  rw [Problem.embed, getD_map_range _ _ hv, redIndex_fixed R hfix]


theorem penalty_bridge (x : Array Bool) :
    (Problem.ofReduced R).penaltyDoubled x
      = CNS.penaltyDoubled ((Problem.ofReduced R).embed R.fixedVal x) :=
  Problem.penaltyDoubled_embed R x

/-! ## Algorithm 1's output -/

theorem reduceFuel_wf : ∀ (fuel : Nat) (g : Grid), g.WF → ∀ r : Nat, (reduceFuel fuel g r).1.WF := by
  intro fuel
  induction fuel with
  | zero => intro g hg r; exact hg
  | succ fuel ih =>
    intro g hg r
    show (reduceFuel (fuel + 1) g r).1.WF
    unfold reduceFuel
    cases hn : nakedSingle? g (buildFlags g).2 with
    | some ck =>
      obtain ⟨c, k⟩ := ck
      simp only [hn]
      exact ih _ (assign_wf hg c k) _
    | none =>
      cases hh : hiddenSingle? g (buildFlags g).2 with
      | some ck =>
        obtain ⟨c, k⟩ := ck
        simp only [hn, hh]
        exact ih _ (assign_wf hg c k) _
      | none => simp only [hn, hh]; exact hg

theorem reduce_wf {g : Grid} (hg : g.WF) : (reduce g).grid.WF :=
  reduceFuel_wf numCells g hg 0

theorem reduce_fixedVal (g : Grid) : (reduce g).fixedVal = (buildFlags (reduce g).grid).1 := rfl

theorem reduce_isFixed (g : Grid) : (reduce g).isFixed = (buildFlags (reduce g).grid).2 := rfl

theorem buildFlags_fst (G : Grid) {v : Nat} (hv : v < numVars) :
    (buildFlags G).1.getD v false = (flagOf G v).1 := getD_map_range _ _ hv _

theorem fixedVal_getD (g : Grid) {v : Nat} (hv : v < numVars) :
    (reduce g).fixedVal.getD v false = ((reduce g).grid.get (v / n) == some (v % n)) := by
  rw [reduce_fixedVal, buildFlags_fst _ hv]
  simp only [flagOf]
  cases hc : (reduce g).grid.get (v / n) with
  | none => simp only []; split <;> rfl
  | some kg =>
    simp only []
    by_cases hk : v % n = kg
    · simp [hk]
    · simp [hk, Ne.symm hk]

theorem isFixed_of_filled (g : Grid) {v : Nat} (hv : v < numVars) {kg : Nat}
    (hc : (reduce g).grid.get (v / n) = some kg) :
    (reduce g).isFixed.getD v false = true := by
  rw [reduce_isFixed, buildFlags_snd _ hv]
  simp only [flagOf, hc]

/-! ## The scatter that `toGrid` performs -/

/-- One step of `toGrid`'s loop. -/
def scatterStep (P : Problem) (x : Array Bool) (cells : Array (Option Nat)) (u : Nat) :
    Array (Option Nat) :=
  if x.getD u false then
    cells.set! ((P.varOf.getD u 0) / n) (some ((P.varOf.getD u 0) % n))
  else cells

/-- `toGrid` written as a fold, which induction can handle. -/
theorem toGrid_eq (P : Problem) (x : Array Bool) :
    P.toGrid x = ⟨(List.range P.nvars).foldl (scatterStep P x) P.base⟩ := by
  show (Id.run _ : Grid) = _
  unfold scatterStep
  simp only [Id.run, List.range_eq_range',
    ← apply_ite (fun s => (pure (ForInStep.yield s) : Id (ForInStep (Array (Option Nat)))))]
  simp
  rfl

theorem scatter_size (P : Problem) (x : Array Bool) :
    ∀ (l : List Nat) (cells : Array (Option Nat)),
      (l.foldl (scatterStep P x) cells).size = cells.size := by
  intro l
  induction l with
  | nil => intro cells; rfl
  | cons u t ih =>
    intro cells
    rw [List.foldl_cons, ih]
    unfold scatterStep
    split <;> simp

theorem scatter_miss (P : Problem) (x : Array Bool) (c : Nat) :
    ∀ (l : List Nat) (cells : Array (Option Nat)),
      (∀ u ∈ l, ¬ (x.getD u false = true ∧ (P.varOf.getD u 0) / n = c)) →
        (l.foldl (scatterStep P x) cells).getD c none = cells.getD c none := by
  intro l
  induction l with
  | nil => intro cells _; rfl
  | cons u t ih =>
    intro cells hall
    rw [List.foldl_cons, ih _ (fun w hw => hall w (List.mem_cons_of_mem _ hw))]
    unfold scatterStep
    by_cases hx : x.getD u false = true
    · rw [if_pos hx]
      have hne : (P.varOf.getD u 0) / n ≠ c := fun hcc =>
        hall u (List.mem_cons_self ..) ⟨hx, hcc⟩
      rw [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?,
        Array.getElem?_setIfInBounds_ne hne, Array.getD_eq_getD_getElem?]
    · rw [if_neg hx]

theorem scatter_hit (P : Problem) (x : Array Bool) (c : Nat) :
    ∀ (l : List Nat) (cells : Array (Option Nat)) (u₀ : Nat), l.Nodup → u₀ ∈ l →
      x.getD u₀ false = true → (P.varOf.getD u₀ 0) / n = c →
      (∀ u ∈ l, u ≠ u₀ → ¬ (x.getD u false = true ∧ (P.varOf.getD u 0) / n = c)) →
      c < cells.size →
        (l.foldl (scatterStep P x) cells).getD c none = some ((P.varOf.getD u₀ 0) % n) := by
  intro l
  induction l with
  | nil => intro cells u₀ _ hu; exact absurd hu (by simp)
  | cons u t ih =>
    intro cells u₀ hnd hmem hx0 hc0 huniq hsz
    rcases List.mem_cons.mp hmem with rfl | hmem'
    · have hstep : scatterStep P x cells u₀ = cells.set! c (some ((P.varOf.getD u₀ 0) % n)) := by
        unfold scatterStep; rw [if_pos hx0, hc0]
      have hmiss : ∀ w ∈ t, ¬ (x.getD w false = true ∧ (P.varOf.getD w 0) / n = c) := by
        intro w hw
        exact huniq w (List.mem_cons_of_mem _ hw)
          (by rintro rfl; exact (List.nodup_cons.mp hnd).1 hw)
      rw [List.foldl_cons, hstep, scatter_miss P x c t _ hmiss,
        Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds,
        Array.getElem?_setIfInBounds_self_of_lt hsz]
      rfl
    · rw [List.foldl_cons]
      refine ih _ u₀ (List.nodup_cons.mp hnd).2 hmem' hx0 hc0
        (fun w hw hwne => huniq w (List.mem_cons_of_mem _ hw) hwne) ?_
      unfold scatterStep
      split <;> simpa using hsz

theorem toGrid_size (P : Problem) (x : Array Bool) :
    (P.toGrid x).cells.size = P.base.size := by
  rw [toGrid_eq]; exact scatter_size P x _ _

theorem toGrid_get_miss (P : Problem) (x : Array Bool) {c : Nat}
    (hmiss : ∀ u < P.nvars, ¬ (x.getD u false = true ∧ (P.varOf.getD u 0) / n = c)) :
    (P.toGrid x).get c = (Grid.mk P.base).get c := by
  rw [toGrid_eq]
  exact scatter_miss P x c _ _ (fun u hu => hmiss u (List.mem_range.mp hu))

theorem toGrid_get_hit (P : Problem) (x : Array Bool) {c u₀ : Nat} (hu₀ : u₀ < P.nvars)
    (hx0 : x.getD u₀ false = true) (hc0 : (P.varOf.getD u₀ 0) / n = c)
    (huniq : ∀ u < P.nvars, u ≠ u₀ → ¬ (x.getD u false = true ∧ (P.varOf.getD u 0) / n = c))
    (hsz : c < P.base.size) :
    (P.toGrid x).get c = some ((P.varOf.getD u₀ 0) % n) := by
  rw [toGrid_eq]
  exact scatter_hit P x c _ _ u₀ List.nodup_range (List.mem_range.mpr hu₀) hx0 hc0
    (fun u hu => huniq u (List.mem_range.mp hu)) hsz

/-! ## From a zero penalty to a completed grid -/

theorem exists_unique_of_countP_eq_one {p : Nat → Bool} {l : List Nat} (h : l.countP p = 1) :
    ∃ a, a ∈ l ∧ p a = true ∧ ∀ b ∈ l, p b = true → b = a := by
  rw [List.countP_eq_length_filter] at h
  obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp h
  have hmem : a ∈ l.filter p := by rw [ha]; simp
  rw [List.mem_filter] at hmem
  refine ⟨a, hmem.1, hmem.2, ?_⟩
  intro b hb hpb
  have hbf : b ∈ l.filter p := List.mem_filter.mpr ⟨hb, hpb⟩
  rw [ha] at hbf
  simpa using hbf

/-- The full `n³` assignment that a reduced assignment stands for. -/
def full (g : Grid) (x : Array Bool) : Array Bool :=
  (Problem.ofReduced (reduce g)).embed (reduce g).fixedVal x

theorem full_def (g : Grid) (x : Array Bool) :
    full g x = (Problem.ofReduced (reduce g)).embed (reduce g).fixedVal x := rfl

theorem ofGrid_eq (g : Grid) : Problem.ofGrid g = Problem.ofReduced (reduce g) := rfl

/-- **The reduced penalty vanishes exactly when the unreduced one does at the embedding.** -/
theorem penalty_full_zero {g : Grid} {x : Array Bool}
    (hx : (Problem.ofGrid g).penaltyDoubled x = 0) : CNS.penaltyDoubled (full g x) = 0 := by
  rw [ofGrid_eq] at hx
  rw [full_def, ← penalty_bridge]
  exact hx

theorem cellvar_lt {c k : Nat} (hc : c < numCells) (hk : k < n) : c * n + k < numVars := by
  simp only [numCells, numVars, n] at *; omega

theorem cellvar_div {c k : Nat} (hk : k < n) : (c * n + k) / n = c ∧ (c * n + k) % n = k := by
  simp only [n] at *; exact ⟨by omega, by omega⟩

/-- **Constraint (10a), read backwards**: a zero penalty puts exactly one digit in each cell. -/
theorem cell_unique {g : Grid} {x : Array Bool} (hz : CNS.penaltyDoubled (full g x) = 0)
    {c : Nat} (hc : c < numCells) :
    ∃ k, k < n ∧ (full g x).getD (c * n + k) false = true ∧
      ∀ t, t < n → (full g x).getD (c * n + t) false = true → t = k := by
  obtain ⟨hcell, -, -, -⟩ := (penalty_zero_iff_families _).mp hz
  have hi : rowOf c < n := by simp only [rowOf, n, numCells] at *; omega
  have hj : colOf c < n := by simp only [colOf, n] at *; omega
  have h1 := hcell (rowOf c) hi (colOf c) hj
  rw [countOn_eq_countP] at h1
  unfold cellVars at h1
  rw [List.countP_map] at h1
  have hcong : (List.range n).countP
        ((fun v => (full g x).getD v false) ∘ (varIdx (rowOf c) (colOf c)))
      = (List.range n).countP (fun k => (full g x).getD (c * n + k) false) :=
    countP_congr' _ (fun t _ => by
      show (full g x).getD (varIdx (rowOf c) (colOf c) t) false = _
      rw [varIdx_of_cell hc])
  rw [hcong] at h1
  have h2 : (List.range n).countP (fun k => (full g x).getD (c * n + k) false) = 1 := by omega
  obtain ⟨a, hamem, hpa, huniq⟩ := exists_unique_of_countP_eq_one h2
  exact ⟨a, List.mem_range.mp hamem, hpa,
    fun t ht hpt => huniq t (List.mem_range.mpr ht) hpt⟩

theorem full_getD_filled {g : Grid} {x : Array Bool} {c k : Nat} (hc : c < numCells) (hk : k < n)
    {kg : Nat} (hbase : (reduce g).grid.get c = some kg) :
    (full g x).getD (c * n + k) false = ((reduce g).grid.get c == some k) := by
  obtain ⟨hd, hm⟩ := cellvar_div (c := c) hk
  have hv : c * n + k < numVars := cellvar_lt hc hk
  have hfix : (reduce g).isFixed.getD (c * n + k) false = true :=
    isFixed_of_filled g hv (by rw [hd]; exact hbase)
  rw [full_def, embed_getD_fixed _ x hv hfix, fixedVal_getD g hv, hd, hm]

theorem full_getD_empty_fixed {g : Grid} {x : Array Bool} {c k : Nat} (hc : c < numCells)
    (hk : k < n) (hbase : (reduce g).grid.get c = none)
    (hfix : (reduce g).isFixed.getD (c * n + k) false = true) :
    (full g x).getD (c * n + k) false = false := by
  obtain ⟨hd, hm⟩ := cellvar_div (c := c) hk
  have hv : c * n + k < numVars := cellvar_lt hc hk
  rw [full_def, embed_getD_fixed _ x hv hfix, fixedVal_getD g hv, hd, hm, hbase]
  rfl

/-- **`toGrid` writes the unique digit the embedded vector selects, in every cell.**

In a cell Algorithm 1 already filled no variable survives, so the base value is preserved; in an
open cell exactly one survivor is set and its digit is written. -/
theorem toGrid_cell {g : Grid} (hg : g.WF) {x : Array Bool}
    (hz : CNS.penaltyDoubled (full g x) = 0) {c : Nat} (hc : c < numCells) :
    ∃ k, k < n ∧ ((Problem.ofReduced (reduce g)).toGrid x).get c = some k ∧
      (∀ t, t < n → ((full g x).getD (c * n + t) false = true ↔ t = k)) ∧
      (∀ kg, (reduce g).grid.get c = some kg → kg = k) := by
  obtain ⟨k, hk, hon, huq⟩ := cell_unique hz hc
  have hsz : (reduce g).grid.cells.size = numCells := reduce_wf hg
  have hbasesz : c < (Problem.ofReduced (reduce g)).base.size := by
    rw [oR_base, hsz]; exact hc
  have hiff : ∀ t, t < n → ((full g x).getD (c * n + t) false = true ↔ t = k) :=
    fun t ht => ⟨huq t ht, by rintro rfl; exact hon⟩
  cases hbase : (reduce g).grid.get c with
  | some kg =>
    have h1 := full_getD_filled (x := x) hc hk hbase
    rw [hon, hbase] at h1
    have hkg : kg = k := by simpa using h1.symm
    have hmiss : ∀ u < (Problem.ofReduced (reduce g)).nvars,
        ¬ (x.getD u false = true
            ∧ ((Problem.ofReduced (reduce g)).varOf.getD u 0) / n = c) := by
      rintro u hu ⟨-, hcellu⟩
      obtain ⟨hlt, hfree⟩ :=
        (mem_survList (reduce g)).mp (varOf_mem_survList (reduce g) hu)
      have hfx := isFixed_of_filled g hlt (by rw [hcellu]; exact hbase)
      rw [hfree] at hfx
      exact Bool.noConfusion hfx
    refine ⟨k, hk, ?_, hiff, ?_⟩
    · rw [toGrid_get_miss _ x hmiss, oR_base, hbase, hkg]
    · intro kg' hkg'
      rw [← Option.some.inj hkg']
      exact hkg
  | none =>
    have hv : c * n + k < numVars := cellvar_lt hc hk
    obtain ⟨hd, hm⟩ := cellvar_div (c := c) hk
    have hfree : (reduce g).isFixed.getD (c * n + k) false = false := by
      cases hfx : (reduce g).isFixed.getD (c * n + k) false with
      | false => rfl
      | true =>
        have hcontra := full_getD_empty_fixed (x := x) hc hk hbase hfx
        rw [hon] at hcontra
        exact absurd hcontra (by simp)
    obtain ⟨u₀, hu₀, hvar⟩ := exists_index_of_mem_survList (reduce g)
      ((mem_survList (reduce g)).mpr ⟨hv, hfree⟩)
    have hemb := embed_getD_varOf (reduce g) x hu₀
    rw [hvar] at hemb
    have hx0 : x.getD u₀ false = true := by rw [← hemb]; exact hon
    have hc0 : ((Problem.ofReduced (reduce g)).varOf.getD u₀ 0) / n = c := by rw [hvar]; exact hd
    have hm0 : ((Problem.ofReduced (reduce g)).varOf.getD u₀ 0) % n = k := by rw [hvar]; exact hm
    have huniqhit : ∀ u < (Problem.ofReduced (reduce g)).nvars, u ≠ u₀ →
        ¬ (x.getD u false = true
            ∧ ((Problem.ofReduced (reduce g)).varOf.getD u 0) / n = c) := by
      rintro u hu hne ⟨hxu, hcu⟩
      have hfullw := embed_getD_varOf (reduce g) x hu
      have hwm : ((Problem.ofReduced (reduce g)).varOf.getD u 0) % n < n := by
        simp only [n]; omega
      have hweq : (Problem.ofReduced (reduce g)).varOf.getD u 0
          = c * n + ((Problem.ofReduced (reduce g)).varOf.getD u 0) % n := by
        simp only [n] at *; omega
      have hkk : ((Problem.ofReduced (reduce g)).varOf.getD u 0) % n = k := by
        refine huq _ hwm ?_
        rw [← hweq, full_def, hfullw]
        exact hxu
      refine hne ((Problem.ofReduced_valid (reduce g)).varOf_inj u hu u₀ hu₀ ?_)
      rw [hvar, hweq, hkk]
    refine ⟨k, hk, ?_, hiff, ?_⟩
    · rw [toGrid_get_hit _ x hu₀ hx0 hc0 huniqhit hbasesz, hm0]
    · intro kg' hkg'
      exact absurd hkg' (by simp)

/-! ## The written-back grid encodes the embedded vector -/

theorem encode_toGrid_getD {g : Grid} (hg : g.WF) {x : Array Bool}
    (hz : CNS.penaltyDoubled (full g x) = 0) {c k : Nat} (hc : c < numCells) (hk : k < n) :
    (encode ((Problem.ofReduced (reduce g)).toGrid x)).getD (c * n + k) false
      = (full g x).getD (c * n + k) false := by
  obtain ⟨hd, hm⟩ := cellvar_div (c := c) hk
  have hv : c * n + k < numVars := cellvar_lt hc hk
  obtain ⟨k₀, hk₀, hget, hiff, -⟩ := toGrid_cell hg hz hc
  rw [encode_getD hv, hd, hm, hget]
  by_cases h : k = k₀
  · rw [(hiff k hk).mpr h]
    simp [h]
  · have hf : (full g x).getD (c * n + k) false = false := by
      cases hb : (full g x).getD (c * n + k) false with
      | false => rfl
      | true => exact absurd ((hiff k hk).mp hb) h
    rw [hf]
    simp [Ne.symm h]

theorem encode_toGrid {g : Grid} (hg : g.WF) {x : Array Bool}
    (hz : CNS.penaltyDoubled (full g x) = 0) :
    encode ((Problem.ofReduced (reduce g)).toGrid x) = full g x := by
  have hsz1 : (encode ((Problem.ofReduced (reduce g)).toGrid x)).size = numVars := by
    simp [encode]
  have hsz2 : (full g x).size = numVars := by simp [full_def, Problem.embed]
  have hgetD : ∀ (a : Array Bool) (i : Nat) (h : i < a.size), a[i] = a.getD i false := by
    intro a i h
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h]
    rfl
  refine Array.ext (by rw [hsz1, hsz2]) ?_
  intro i hi1 hi2
  have hi : i < numVars := by rw [hsz1] at hi1; exact hi1
  have hc : i / n < numCells := by simp only [numVars, numCells, n] at *; omega
  have hk : i % n < n := by simp only [n]; omega
  have hieq : (i / n) * n + i % n = i := by simp only [n]; omega
  have hpt := encode_toGrid_getD hg hz hc hk
  rw [hieq] at hpt
  rw [hgetD _ i hi1, hgetD _ i hi2, hpt]

/-! ## Reading `isSolution` off the four families -/

theorem mem_units_cases {u : Array Nat} (hu : u ∈ units) :
    (∃ i, i < n ∧ u = rowCells i) ∨ (∃ j, j < n ∧ u = colCells j) ∨
      (∃ b, b < n ∧ u = boxCells b) := CNS.mem_units hu

/-- **Constraints (10b)-(10d), read backwards**: the three unit families force consistency. -/
theorem isConsistent_of_families {h : Grid}
    (hcol : ∀ j, j < n → ∀ k, k < n → countOn (encode h) (colVars j k) = 1)
    (hrow : ∀ i, i < n → ∀ k, k < n → countOn (encode h) (rowVars i k) = 1)
    (hbox : ∀ b, b < n → ∀ k, k < n → countOn (encode h) (boxVars b k) = 1) :
    h.isConsistent = true := by
  unfold Grid.isConsistent
  rw [Array.all_eq_true_iff_forall_mem]
  intro u hu
  rw [Array.all_eq_true_iff_forall_mem]
  intro kk hkkm
  have hk : kk < n := Array.mem_range.mp hkkm
  rw [beq_iff_eq]
  rcases mem_units_cases hu with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨b, hb, rfl⟩
  · have hcells : (rowCells i).toList = (List.range n).map (fun c => cellIdx i c) := by
      unfold rowCells; simp
    have heq := countOn_unit_eq (g := h) (encode h) (fun c => cellIdx i c) (fun j => varIdx i j kk)
      (fun t ht => encode_at hi ht hk)
    have h1 : countOn (encode h) (rowVars i kk) = 1 := hrow i hi kk hk
    unfold rowVars at h1
    rw [h1] at heq
    rw [hcells]
    omega
  · have hcells : (colCells j).toList = (List.range n).map (fun r => cellIdx r j) := by
      unfold colCells; simp
    have heq := countOn_unit_eq (g := h) (encode h) (fun r => cellIdx r j) (fun i => varIdx i j kk)
      (fun t ht => encode_at ht hj hk)
    have h1 : countOn (encode h) (colVars j kk) = 1 := hcol j hj kk hk
    unfold colVars at h1
    rw [h1] at heq
    rw [hcells]
    omega
  · have hcells : (boxCells b).toList
        = (List.range n).map (fun t => cellIdx ((b / blk) * blk + t / blk)
            ((b % blk) * blk + t % blk)) := by
      unfold boxCells; simp
    have heq := countOn_unit_eq (g := h) (encode h)
      (fun t => cellIdx ((b / blk) * blk + t / blk) ((b % blk) * blk + t % blk))
      (fun t => varIdx ((b / blk) * blk + t / blk) ((b % blk) * blk + t % blk) kk)
      (fun t ht => encode_at (by simp only [blk, n] at *; omega)
        (by simp only [blk, n] at *; omega) hk)
    have h1 : countOn (encode h) (boxVars b kk) = 1 := hbox b hb kk hk
    unfold boxVars at h1
    rw [h1] at heq
    rw [hcells]
    omega

theorem isSolution_of {h : Grid} (hsz : h.cells.size = numCells)
    (hcell : ∀ c, c < numCells → ∃ k, k < n ∧ h.get c = some k)
    (hcons : h.isConsistent = true) : h.isSolution = true := by
  have hget : ∀ (i : Nat) (hi : i < h.cells.size), h.get i = h.cells[i] := by
    intro i hi
    unfold Grid.get
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]
    rfl
  unfold Grid.isSolution Grid.hasSize Grid.digitsInRange Grid.isComplete
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨by simp [hsz], ?_⟩, ?_⟩, hcons⟩
  · rw [Array.all_eq_true_iff_forall_mem]
    intro o ho
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp ho
    obtain ⟨k, hkn, hk⟩ := hcell i (by rw [← hsz]; exact hi)
    rw [← hget i hi, hk]
    simpa using hkn
  · rw [Array.all_eq_true_iff_forall_mem]
    intro o ho
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp ho
    obtain ⟨k, hkn, hk⟩ := hcell i (by rw [← hsz]; exact hi)
    rw [← hget i hi, hk]
    rfl

/-! ## The main theorems -/

/-- **A zero reduced penalty yields a completion of the reduced puzzle.** -/
theorem completes_reduced {g : Grid} (hg : g.WF) {x : Array Bool}
    (hx : (Problem.ofGrid g).penaltyDoubled x = 0) :
    Completes (reduce g).grid ((Problem.ofGrid g).toGrid x) := by
  have hz := penalty_full_zero hx
  obtain ⟨-, hcol, hrow, hbox⟩ := (penalty_zero_iff_families (full g x)).mp hz
  have henc := encode_toGrid hg hz
  have hbasesz : (reduce g).grid.cells.size = numCells := reduce_wf hg
  have hsz : ((Problem.ofReduced (reduce g)).toGrid x).cells.size = numCells := by
    rw [toGrid_size, oR_base, hbasesz]
  have hcell : ∀ c, c < numCells →
      ∃ k, k < n ∧ ((Problem.ofReduced (reduce g)).toGrid x).get c = some k := by
    intro c hc
    obtain ⟨k, hk, hget, -, -⟩ := toGrid_cell hg hz hc
    exact ⟨k, hk, hget⟩
  have hcons : ((Problem.ofReduced (reduce g)).toGrid x).isConsistent = true := by
    refine isConsistent_of_families ?_ ?_ ?_ <;> rw [henc]
    · exact hcol
    · exact hrow
    · exact hbox
  refine ⟨hsz, isSolution_of hsz hcell hcons, ?_⟩
  rw [ofGrid_eq, extends'_iff]
  intro c hc k hk
  obtain ⟨k₀, hk₀, hget, -, hbase⟩ := toGrid_cell hg hz hc
  rw [hget, hbase k hk]

/-- **Completeness of the encoding**: a zero reduced penalty decodes to a completion of the
original puzzle. -/
theorem toGrid_completes {g : Grid} (hg : g.WF) {x : Array Bool}
    (hx : (Problem.ofGrid g).penaltyDoubled x = 0) :
    Completes g ((Problem.ofGrid g).toGrid x) :=
  (reduce_completions hg _).mpr (completes_reduced hg hx)

/-- **A zero penalty decodes to a solved grid.** -/
theorem solution_of_penalty_zero {g : Grid} (hg : g.WF) {x : Array Bool}
    (hx : (Problem.ofGrid g).penaltyDoubled x = 0) :
    ((Problem.ofGrid g).toGrid x).isSolution = true :=
  (toGrid_completes hg hx).2.1

/-- **A zero penalty decodes to a grid extending the givens** — constraint (10e). -/
theorem toGrid_extends {g : Grid} (hg : g.WF) {x : Array Bool}
    (hx : (Problem.ofGrid g).penaltyDoubled x = 0) :
    g.extends' ((Problem.ofGrid g).toGrid x) = true :=
  (toGrid_completes hg hx).2.2

end Complete
end CNS
