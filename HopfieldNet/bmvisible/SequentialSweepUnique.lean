/-
Copyright (c) 2025 HNBM contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.bmvisible.SequentialSweep
import HopfieldNet.Quiver.BM.Ergodicity
import MCMC.Core
import MCMC.Convergence
import MCMC.MetropolisHastings

/-!
# Unique stationary measure for sequential Gibbs sweep

Full site permutation (`IsFullSweep`) ⇒ unique stationary vector = negative phase.
-/

namespace BMVisible

open MeasureTheory ProbabilityTheory TwoState HopfieldBoltzmann Matrix CanonicalEnsemble Constants
open scoped ProbabilityTheory ENNReal BigOperators CanonicalEnsemble

variable {U : Type} [Fintype U] [DecidableEq U] [Nonempty U]
variable {part : VisibleHiddenPartition U}

local notation "State" => BMState ℝ U part

/-!
### Row-stochastic sweep matrices
-/

/-- Row-stochastic matrix for single-site Gibbs update at `u` (MCMC row convention). -/
noncomputable def SSrow (u : U) (p : BMParams ℝ U part) (T : Temperature) :
    Matrix State State ℝ :=
  fun s t => ((singleSiteKernel (NN := NN ℝ U part) (energySpec part) p T u) s {t}).toReal

/-- Sequential sweep as row-stochastic matrix product (head site updated first). -/
noncomputable def sweepRowMatrix (p : BMParams ℝ U part) (T : Temperature) :
    List U → Matrix State State ℝ
  | [] => 1
  | u :: us => SSrow u p T * sweepRowMatrix p T us

/-- Sweep order visits every site exactly once (full permutation of `U`). -/
def IsFullSweep (order : List U) : Prop :=
  order.Nodup ∧ order.length = Fintype.card U

/-- Align `cur` with `tgt` at site `u` (identity when already aligned). -/
noncomputable def alignCoord (u : U) (p : BMParams ℝ U part) (T : Temperature) (cur tgt : State) : State :=
  if h : cur.act u = tgt.act u then cur
  else
    Classical.choose (exists_single_flip_reduce (NN := NN ℝ U part) (energySpec part) p T
      (show u ∈ diffSites (NN := NN ℝ U part) cur tgt by simp [diffSites, h]))

private lemma alignCoord_diffOnly {u : U} (p : BMParams ℝ U part) (T : Temperature) {cur tgt : State}
    (hne : cur.act u ≠ tgt.act u) :
    DiffOnly (NN := NN ℝ U part) u (alignCoord u p T cur tgt) cur := by
  dsimp [alignCoord]
  split_ifs with heq
  · exact (hne heq).elim
  · exact (Classical.choose_spec (exists_single_flip_reduce (NN := NN ℝ U part) (energySpec part) p T
      (show u ∈ diffSites (NN := NN ℝ U part) cur tgt by simp [diffSites, heq]))).1

private lemma DiffOnly_symm {u : U} {s s' : State}
    (h : DiffOnly (NN := NN ℝ U part) u s s') :
    DiffOnly (NN := NN ℝ U part) u s' s :=
  ⟨fun v hv => (h.1 v hv).symm, h.2.symm⟩

private lemma diffOnly_act_eq_target (p : BMParams ℝ U part) (T : Temperature) {u : U} {s cur tgt : State}
    (h : DiffOnly (NN := NN ℝ U part) u s cur) (hmem : u ∈ diffSites (NN := NN ℝ U part) cur tgt) :
    s.act u = tgt.act u := by
  have hcur_ne : cur.act u ≠ tgt.act u := by simpa [diffSites] using hmem
  rcases (TwoStateExclusive.pact_iff (NN := NN ℝ U part) (a := tgt.act u)).1 (tgt.hp u) with htgt_pos | htgt_neg
  · rcases (TwoStateExclusive.pact_iff (NN := NN ℝ U part) (a := cur.act u)).1 (cur.hp u) with hcur_pos | hcur_neg
    · exact (hcur_ne (Eq.symm (htgt_pos.trans hcur_pos.symm))).elim
    · rcases (TwoStateExclusive.pact_iff (NN := NN ℝ U part) (a := s.act u)).1 (s.hp u) with hs_pos | hs_neg
      · simpa [hs_pos, htgt_pos]
      · exact (h.2 (by simpa [hcur_neg, hs_neg])).elim
  · rcases (TwoStateExclusive.pact_iff (NN := NN ℝ U part) (a := cur.act u)).1 (cur.hp u) with hcur_pos | hcur_neg
    · rcases (TwoStateExclusive.pact_iff (NN := NN ℝ U part) (a := s.act u)).1 (s.hp u) with hs_pos | hs_neg
      · exact (h.2 (by simpa [hcur_pos, hs_pos])).elim
      · simpa [hs_neg, htgt_neg]
    · exact (hcur_ne (Eq.symm (htgt_neg.trans hcur_neg.symm))).elim

private lemma alignCoord_act_u (u : U) (p : BMParams ℝ U part) (T : Temperature) (cur tgt : State) :
    (alignCoord u p T cur tgt).act u = tgt.act u := by
  dsimp [alignCoord]
  split_ifs with heq
  · exact heq
  · exact diffOnly_act_eq_target p T
      (Classical.choose_spec (exists_single_flip_reduce (NN := NN ℝ U part) (energySpec part) p T
        (show u ∈ diffSites (NN := NN ℝ U part) cur tgt by simp [diffSites, heq]))).1
      (by simp [diffSites, heq])

private lemma alignCoord_diffSites_sub {u : U} (p : BMParams ℝ U part) (T : Temperature) {cur tgt : State}
    (hne : cur.act u ≠ tgt.act u) :
    (diffSites (NN := NN ℝ U part) (alignCoord u p T cur tgt) tgt).card + 1 =
      (diffSites (NN := NN ℝ U part) cur tgt).card := by
  dsimp [alignCoord]
  split_ifs with heq
  · exact (hne heq).elim
  · exact (Classical.choose_spec (exists_single_flip_reduce (NN := NN ℝ U part) (energySpec part) p T
      (show u ∈ diffSites (NN := NN ℝ U part) cur tgt by simp [diffSites, heq]))).2

/-- Single-site row matrix entries are nonnegative. -/
lemma SSrow_nonneg (u : U) (p : BMParams ℝ U part) (T : Temperature) :
    ∀ s t, 0 ≤ SSrow u p T s t := by
  intro s t; dsimp [SSrow]; exact ENNReal.toReal_nonneg

/-- Single-site row matrix is row-stochastic. -/
lemma SSrow_isStochastic (u : U) (p : BMParams ℝ U part) (T : Temperature) :
    IsStochastic (SSrow u p T) := by
  constructor
  · exact SSrow_nonneg u p T
  · intro s
    let q := TwoState.gibbsUpdate (RingHom.id ℝ) p T s u
    have hsum : (∑ t, q t).toReal = 1 := by
      have h : (∑ t, q t) = (1 : ℝ≥0∞) := by simpa [tsum_fintype] using q.tsum_coe
      rw [h, ENNReal.toReal_one]
    calc
      ∑ t, SSrow u p T s t = ∑ t, (q t).toReal := by
        simp [SSrow, singleSiteKernel, pmfToKernel, q]
      _ = (∑ t, q t).toReal := by
        have hfin : ∀ t, q t ≠ ⊤ := fun t => (PMF.apply_lt_top q t).ne
        exact (ENNReal.toReal_sum (f := fun t => q t) (by intro t _; exact hfin t)).symm
      _ = 1 := hsum

/-- Sequential sweep row matrix is row-stochastic. -/
lemma sweepRowMatrix_isStochastic (order : List U) (p : BMParams ℝ U part) (T : Temperature) :
    IsStochastic (sweepRowMatrix p T order) := by
  induction order with
  | nil => simpa using isStochastic_one
  | cons u us ih =>
      simpa [sweepRowMatrix] using
        isStochastic_mul (hP := SSrow_isStochastic u p T) (hQ := ih)

private lemma SSrow_pos_of_diffOnly {u : U} {s s' : State} (p : BMParams ℝ U part) (T : Temperature)
    (h : DiffOnly (NN := NN ℝ U part) u s s') :
    0 < SSrow u p T s s' := by
  have hK : 0 < HopfieldBoltzmann.Kbm (NN := NN ℝ U part) p T u s s' := by
    have hkernel := singleSiteKernel_pos_of_diffOnly (NN := NN ℝ U part) (energySpec part) p T h
    rw [singleSiteKernel_singleton_eval (NN := NN ℝ U part) (energySpec part) p T u s s'] at hkernel
    exact ENNReal.ofReal_pos.mp hkernel
  have hpos : 0 < ENNReal.ofReal (HopfieldBoltzmann.Kbm (NN := NN ℝ U part) p T u s s') :=
    ENNReal.ofReal_pos.mpr hK
  dsimp [SSrow]
  rw [singleSiteKernel_singleton_eval (NN := NN ℝ U part) (energySpec part) p T u s s']
  exact ENNReal.toReal_pos (ne_of_gt hpos) (by simp)

private lemma SSrow_diag_pos (u : U) (p : BMParams ℝ U part) (T : Temperature) (s : State) :
    0 < SSrow u p T s s := by
  have hK : 0 < HopfieldBoltzmann.Kbm (NN := NN ℝ U part) p T u s s := by
    have hkernel := singleSiteKernel_diag_pos (NN := NN ℝ U part) (energySpec part) p T u s
    rw [singleSiteKernel_singleton_eval (NN := NN ℝ U part) (energySpec part) p T u s s] at hkernel
    exact ENNReal.ofReal_pos.mp hkernel
  have hpos : 0 < ENNReal.ofReal (HopfieldBoltzmann.Kbm (NN := NN ℝ U part) p T u s s) :=
    ENNReal.ofReal_pos.mpr hK
  dsimp [SSrow]
  rw [singleSiteKernel_singleton_eval (NN := NN ℝ U part) (energySpec part) p T u s s]
  exact ENNReal.toReal_pos (ne_of_gt hpos) (by simp)

private lemma SSrow_alignCoord_pos (u : U) (cur tgt : State) (p : BMParams ℝ U part) (T : Temperature) :
    0 < SSrow u p T cur (alignCoord u p T cur tgt) := by
  classical
  by_cases heq : cur.act u = tgt.act u
  · simpa [SSrow, alignCoord, heq] using SSrow_diag_pos u p T cur
  · have hne : cur.act u ≠ tgt.act u := fun h => heq h
    exact SSrow_pos_of_diffOnly (p := p) (T := T)
      (u := u) (s := cur) (s' := alignCoord u p T cur tgt)
      (DiffOnly_symm (alignCoord_diffOnly (u := u) (p := p) (T := T) (cur := cur) (tgt := tgt) hne))

private lemma fullSweep_cons {u : U} {us : List U} (h : IsFullSweep (u :: us)) :
    us.length + 1 = Fintype.card U := by
  simpa using h.2

/-- Sequential sweep row matrix entries are nonnegative. -/
lemma sweepRowMatrix_nonneg (order : List U) (p : BMParams ℝ U part) (T : Temperature)
    (s s' : State) :
    0 ≤ sweepRowMatrix p T order s s' := by
  induction order generalizing s s' with
  | nil =>
      simp [sweepRowMatrix, Matrix.one_apply]
      split_ifs <;> norm_num
  | cons u us ih =>
      dsimp [sweepRowMatrix, Matrix.mul_apply]
      refine Finset.sum_nonneg fun j _ => ?_
      exact mul_nonneg (SSrow_nonneg u p T s j) (ih j s')

private lemma SSrow_mul_one_sum_eq (w : U) (p : BMParams ℝ U part) (T : Temperature) (mid tgt : State) :
    (∑ j, SSrow w p T mid j * ((1 : Matrix State State ℝ) j tgt)) = SSrow w p T mid tgt := by
  rw [Finset.sum_eq_single tgt]
  · simp [Matrix.one_apply]
  · intro j _ hjt; simp [Matrix.one_apply, hjt]
  · simp [Matrix.one_apply]

private lemma sweepRowMatrix_pos_SSrow_mul_one (w : U) (p : BMParams ℝ U part) (T : Temperature)
    (mid tgt : State) (hpos : 0 < SSrow w p T mid tgt) :
    0 < (SSrow w p T * (1 : Matrix State State ℝ)) mid tgt := by
  dsimp [sweepRowMatrix, Matrix.mul_apply]
  simpa [SSrow_mul_one_sum_eq w p T mid tgt] using hpos

private lemma sweepRowMatrix_pos_mul_cons (u : U) (us : List U) (p : BMParams ℝ U part) (T : Temperature)
    (s tgt witness : State) (hstep : 0 < SSrow u p T s witness)
    (hrest : 0 < sweepRowMatrix p T us witness tgt) :
    0 < sweepRowMatrix p T (u :: us) s tgt := by
  dsimp [sweepRowMatrix]
  have hterm := mul_pos hstep hrest
  have hnn : ∀ j, 0 ≤ SSrow u p T s j * sweepRowMatrix p T us j tgt := fun j =>
    mul_nonneg (SSrow_nonneg u p T s j) (sweepRowMatrix_nonneg us p T j tgt)
  have hge : SSrow u p T s witness * sweepRowMatrix p T us witness tgt ≤
      ∑ j, SSrow u p T s j * sweepRowMatrix p T us j tgt :=
    Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ witness)
  exact lt_of_lt_of_le hterm (by simp [Matrix.mul_apply]; exact hge)

private lemma alignCoord_act_u_of_ne {u v : U} (p : BMParams ℝ U part) (T : Temperature)
    (mid tgt : State) (hvu : v ≠ u) (heq : mid.act v ≠ tgt.act v) (hu : mid.act u = tgt.act u) :
    (alignCoord v p T mid tgt).act u = tgt.act u := by
  have hoff_u : (alignCoord v p T mid tgt).act u = mid.act u :=
    (alignCoord_diffOnly (u := v) (p := p) (T := T) (cur := mid) (tgt := tgt) heq).1 u (Ne.symm hvu)
  simpa [hu] using hoff_u

private lemma alignCoord_act_self (v : U) (p : BMParams ℝ U part) (T : Temperature) (cur tgt : State) :
    (alignCoord v p T cur tgt).act v = tgt.act v := by
  dsimp [alignCoord]
  split_ifs with heq
  · exact heq
  · exact diffOnly_act_eq_target p T
      (Classical.choose_spec (exists_single_flip_reduce (NN := NN ℝ U part) (energySpec part) p T
        (show v ∈ diffSites (NN := NN ℝ U part) cur tgt by simp [diffSites, heq]))).1
      (by simp [diffSites, heq])

private lemma alignCoord_preserves_off {v w : U} (p : BMParams ℝ U part) (T : Temperature)
    (cur tgt : State) (hvw : v ≠ w) :
    (alignCoord v p T cur tgt).act w = cur.act w := by
  by_cases heq : cur.act v = tgt.act v
  · simp [alignCoord, heq]
  · simpa [alignCoord, heq] using
      (alignCoord_diffOnly (u := v) (p := p) (T := T) (cur := cur) (tgt := tgt) heq).1 w (Ne.symm hvw)

private lemma mem_tail_ne_head {u : U} {us : List U} (h : IsFullSweep (u :: us)) {v : U}
    (hv : v ∈ us) : v ≠ u :=
  fun huv => (List.nodup_cons.mp h.1).1 (huv ▸ hv)

private lemma not_mem_of_not_mem_cons {u v : U} {xs : List U} (h : u ∉ v :: xs) : u ∉ xs :=
  fun hmem => h (List.mem_cons.mpr (Or.inr hmem))

private lemma site_eq_u_or_mem_done {u : U} {done : List U} (h : IsFullSweep (u :: done)) (x : U) :
    x = u ∨ x ∈ done := by
  have hnd : (u :: done).Nodup := h.1
  have hfin : (u :: done).toFinset = (Finset.univ : Finset U) := by
    refine @Finset.eq_univ_of_card U _ (u :: done).toFinset ?_
    rw [List.toFinset_card_of_nodup hnd, h.2]
  have hx : x ∈ (u :: done).toFinset := by simpa [hfin] using Finset.mem_univ x
  simpa [List.mem_toFinset, List.mem_cons, List.mem_singleton] using hx

private lemma mem_done_append_not_mem_pending {u v : U} {done pending : List U}
    (h : IsFullSweep (u :: done ++ pending)) (hv : v ∈ pending) : v ∉ done := by
  intro hvd
  have hne : v ≠ v :=
    (List.nodup_append.mp (List.nodup_cons.mp h.1).2).2.2 v hvd v hv
  exact absurd rfl hne

private lemma sweepRowMatrix_pos_one_site_of_partial_align {u w : U} (hwu : w ≠ u)
    (p : BMParams ℝ U part) (T : Temperature) (mid tgt : State) (hu : mid.act u = tgt.act u)
    (halign : ∀ v, v ≠ u → v ≠ w → mid.act v = tgt.act v) :
    0 < sweepRowMatrix p T [w] mid tgt := by
  dsimp [sweepRowMatrix, Matrix.mul_apply]
  by_cases heqw : mid.act w = tgt.act w
  · have heq_act : ∀ x, mid.act x = tgt.act x := by
      intro x
      by_cases hxw : x = w
      · simpa [hxw] using heqw
      · by_cases hxu : x = u
        · simpa [hxu] using hu
        · simpa using halign x hxu hxw
    have heq_mid : mid = tgt := by ext x; exact heq_act x
    subst heq_mid
    simpa [SSrow_mul_one_sum_eq w p T mid mid] using SSrow_diag_pos w p T mid
  · have hdiff : DiffOnly (NN := NN ℝ U part) w mid tgt :=
      ⟨fun x hx => by
        by_cases hxu : x = u
        · simpa [hxu] using hu
        · by_cases hxw : x = w
          · exact (hx hxw).elim
          · exact halign x hxu hxw, heqw⟩
    simpa [SSrow_mul_one_sum_eq w p T mid tgt] using
      SSrow_pos_of_diffOnly (p := p) (T := T) hdiff

private lemma sweepRowMatrix_pos_tail_run {u : U} (p : BMParams ℝ U part) (T : Temperature)
    (mid tgt : State) (hu : mid.act u = tgt.act u) (done pending : List U)
    (h : IsFullSweep (u :: done ++ pending)) (hnu : u ∉ done) (halign : ∀ v ∈ done, mid.act v = tgt.act v) :
    0 < sweepRowMatrix p T pending mid tgt := by
  cases pending with
  | nil =>
      dsimp [sweepRowMatrix, Matrix.one_apply]
      have hdone : IsFullSweep (u :: done) := by simpa [List.append_nil] using h
      have heq : mid = tgt := by
        ext x
        rcases site_eq_u_or_mem_done (u := u) (done := done) hdone x with hxu | hxdone
        · simpa [hxu] using hu
        · exact halign x hxdone
      subst heq
      norm_num
  | cons s₀ rest =>
      have hsu : s₀ ≠ u :=
        mem_tail_ne_head h (List.mem_append_right done (by simp))
      set mid₁ := alignCoord s₀ p T mid tgt
      have hstep := SSrow_alignCoord_pos s₀ mid tgt p T
      have hu₁ : mid₁.act u = tgt.act u := by
        by_cases heq : mid.act s₀ = tgt.act s₀
        · simpa [mid₁, alignCoord, heq] using hu
        · exact alignCoord_act_u_of_ne p T mid tgt hsu heq hu
      have hsnotdone : s₀ ∉ done := mem_done_append_not_mem_pending h (by simp)
      have halign₁ : ∀ w ∈ done ++ [s₀], mid₁.act w = tgt.act w := by
        intro w hw
        simp [List.mem_append, List.mem_cons, List.mem_singleton] at hw
        rcases hw with hw | rfl
        · have hsw : s₀ ≠ w := fun hsw => hsnotdone (hsw ▸ hw)
          dsimp [mid₁]
          rw [alignCoord_preserves_off (v := s₀) (w := w) (p := p) (T := T) (cur := mid) (tgt := tgt) hsw]
          exact halign w hw
        · exact alignCoord_act_self (v := w) (p := p) (T := T) (cur := mid) (tgt := tgt)
      have h' : IsFullSweep (u :: ((done ++ [s₀]) ++ rest)) := by
        simpa [List.append_assoc] using h
      have hnu' : u ∉ done ++ [s₀] := by
        intro hmem
        simp [List.mem_append, List.mem_cons, List.mem_singleton] at hmem
        rcases hmem with hmem | hmem
        · exact hnu hmem
        · subst hmem; exact hsu rfl
      have hrest :=
        sweepRowMatrix_pos_tail_run (u := u) (p := p) (T := T) (mid := mid₁) (tgt := tgt) (hu := hu₁)
          (done := done ++ [s₀]) (pending := rest) (h := h') (hnu := hnu') (halign := halign₁)
      exact sweepRowMatrix_pos_mul_cons (u := s₀) (us := rest) (p := p) (T := T) (s := mid) (tgt := tgt)
        (witness := mid₁) hstep hrest

private lemma sweepRowMatrix_pos_of_tail {u : U} {us : List U}
    (h : IsFullSweep (u :: us)) (p : BMParams ℝ U part) (T : Temperature)
    (mid tgt : State) (hu : mid.act u = tgt.act u) :
    0 < sweepRowMatrix p T us mid tgt := by
  cases us with
  | nil =>
      simp only [sweepRowMatrix]
      have hcard : Fintype.card U = 1 := by
        have hlen := fullSweep_cons h
        simp at hlen
        exact hlen.symm
      haveI : Subsingleton U := Fintype.card_le_one_iff_subsingleton.mp (by omega)
      have heq : mid = tgt := by
        ext v
        have hv : v = u := Subsingleton.elim v u
        subst hv
        simpa using hu
      rw [heq, Matrix.one_apply]
      norm_num
  | cons v vs =>
      exact sweepRowMatrix_pos_tail_run (u := u) (p := p) (T := T) (mid := mid) (tgt := tgt)
        (hu := hu) (done := []) (pending := v :: vs) (h := h) (hnu := by simp)
        (halign := by intro w hw; simp at hw)

private lemma sweepRowMatrix_pos_of_fullSweep (order : List U) (h : IsFullSweep order)
    (p : BMParams ℝ U part) (T : Temperature) (s s' : State) :
    0 < sweepRowMatrix p T order s s' := by
  induction order generalizing s s' with
  | nil =>
      have h0 : (0 : ℕ) = Fintype.card U := by simpa using h.2
      have hpos : 0 < Fintype.card U := Fintype.card_pos_iff.mpr inferInstance
      omega
  | cons u us ih =>
      set mid := alignCoord u p T s s'
      have hstep : 0 < SSrow u p T s mid := SSrow_alignCoord_pos u s s' p T
      have hrest : 0 < sweepRowMatrix p T us mid s' :=
        sweepRowMatrix_pos_of_tail h p T mid s' (alignCoord_act_u u p T s s')
      dsimp [sweepRowMatrix]
      have hmul :
          (SSrow u p T * sweepRowMatrix p T us) s s'
            = ∑ j, SSrow u p T s j * sweepRowMatrix p T us j s' := by
        simp [Matrix.mul_apply]
      have hterm : 0 < SSrow u p T s mid * sweepRowMatrix p T us mid s' :=
        mul_pos hstep hrest
      have hnn :
          ∀ j, 0 ≤ SSrow u p T s j * sweepRowMatrix p T us j s' := by
        intro j
        exact mul_nonneg (SSrow_nonneg u p T s j)
          (sweepRowMatrix_nonneg us p T j s')
      have hge :
          SSrow u p T s mid * sweepRowMatrix p T us mid s'
            ≤ ∑ j, SSrow u p T s j * sweepRowMatrix p T us j s' := by
        refine Finset.single_le_sum (fun j _ => hnn j) ?_
        simp [mid]
      exact lt_of_lt_of_le hterm (by simpa [hmul] using hge)

private lemma sweepRowMatrix_pos_of_fullSweep_all (order : List U) (h : IsFullSweep order)
    (p : BMParams ℝ U part) (T : Temperature) :
    ∀ s s', 0 < sweepRowMatrix p T order s s' :=
  fun s s' => sweepRowMatrix_pos_of_fullSweep order h p T s s'

private lemma sweepRowMatrix_irred_of_fullSweep (order : List U) (h : IsFullSweep order)
    (p : BMParams ℝ U part) (T : Temperature) :
    Matrix.IsIrreducible (sweepRowMatrix p T order) :=
  Matrix.irreducible_of_all_entries_positive (A := sweepRowMatrix p T order)
    (sweepRowMatrix_pos_of_fullSweep_all order h p T)

private lemma sweepRowMatrix_primitive_of_fullSweep (order : List U) (h : IsFullSweep order)
    (p : BMParams ℝ U part) (T : Temperature) :
    Matrix.IsPrimitive (sweepRowMatrix p T order) := by
  refine Matrix.IsPrimitive.of_irreducible_pos_diagonal
    (A := sweepRowMatrix p T order)
    (fun i j => le_of_lt (sweepRowMatrix_pos_of_fullSweep_all order h p T i j))
    (sweepRowMatrix_irred_of_fullSweep order h p T) ?_
  intro i
  induction order with
  | nil =>
      have h0 : (0 : ℕ) = Fintype.card U := by simpa using h.2
      have hpos : 0 < Fintype.card U := Fintype.card_pos_iff.mpr inferInstance
      omega
  | cons u us ih =>
      have htail : IsFullSweep (u :: us) := h
      dsimp [sweepRowMatrix, Matrix.mul_apply]
      have hterm : 0 < SSrow u p T i i * sweepRowMatrix p T us i i :=
        mul_pos (SSrow_diag_pos u p T i)
          (sweepRowMatrix_pos_of_tail htail p T i i rfl)
      have hnn : ∀ j, 0 ≤ SSrow u p T i j * sweepRowMatrix p T us j i := fun j =>
        mul_nonneg (SSrow_nonneg u p T i j) (sweepRowMatrix_nonneg us p T j i)
      exact lt_of_lt_of_le hterm (Finset.single_le_sum (fun j _ => hnn j) (by simp))

/-!
### Stationary vector and uniqueness
-/

/-- Boltzmann probability vector on states (learning-layer form of `πBoltzVec`). -/
noncomputable def negativePhaseVec (temp : Temperature) (p : BMParams ℝ U part) : stdSimplex ℝ State :=
  πBoltzVec (NN := NN ℝ U part) (spec := energySpec part) p temp

/-- Entries of `negativePhaseVec` are Boltzmann probabilities $P_{p,T}(s)$. -/
lemma negativePhaseVec_val_eq_P (T : Temperature) (p : BMParams ℝ U part) (s : State) :
    (negativePhaseVec T p).val s =
      HopfieldBoltzmann.P (NN := NN ℝ U part) (spec := energySpec part) p T s := by
  dsimp [negativePhaseVec, πBoltzVec, μBoltz, modelProbability]
  rw [boltzmann_singleton_eval (NN := NN ℝ U part) (spec := energySpec part) p T s]
  exact ENNReal.toReal_ofReal (modelProbability_nonneg part T p s)

/-- `SSrow` entries agree with Quiver Boltzmann transition kernel `Kbm`. -/
lemma SSrow_eq_Kbm (u : U) (p : BMParams ℝ U part) (T : Temperature) (s t : State) :
    SSrow u p T s t = HopfieldBoltzmann.Kbm (NN := NN ℝ U part) p T u s t := by
  dsimp [SSrow]
  rw [singleSiteKernel_singleton_eval (NN := NN ℝ U part) (energySpec part) p T u s t]
  unfold HopfieldBoltzmann.Kbm
  exact ENNReal.toReal_ofReal ENNReal.toReal_nonneg

private lemma SSrow_isReversible_negativePhase (u : U) (T : Temperature) (p : BMParams ℝ U part) :
    IsReversible (SSrow u p T) (negativePhaseVec T p) := by
  intro s t
  rw [negativePhaseVec_val_eq_P T p s, negativePhaseVec_val_eq_P T p t,
    SSrow_eq_Kbm u p T s t, SSrow_eq_Kbm u p T t s]
  exact detailed_balance (NN := NN ℝ U part) (spec := energySpec part) p T u s t

private lemma IsStationary_mul {P Q : Matrix State State ℝ} (π : stdSimplex ℝ State)
    (hP : IsStationary P π) (hQ : IsStationary Q π) :
    IsStationary (P * Q) π := by
  dsimp [IsStationary] at *
  rw [Matrix.transpose_mul, ← Matrix.mulVec_mulVec, hP, hQ]

private lemma negativePhaseVec_is_stationary_SSrow (u : U) (T : Temperature) (p : BMParams ℝ U part) :
    IsStationary (SSrow u p T) (negativePhaseVec T p) :=
  IsReversible.is_stationary (SSrow_isStochastic u p T)
    (SSrow_isReversible_negativePhase u T p)

/-- `negativePhaseVec` is stationary for any sequential sweep row matrix. -/
lemma negativePhaseVec_is_stationary_sweepRow (order : List U) (T : Temperature)
    (p : BMParams ℝ U part) :
    IsStationary (sweepRowMatrix p T order) (negativePhaseVec T p) := by
  induction order with
  | nil =>
      ext s
      simp [IsStationary, sweepRowMatrix]
  | cons u us ih =>
      dsimp [sweepRowMatrix]
      exact IsStationary_mul (negativePhaseVec T p) (negativePhaseVec_is_stationary_SSrow u T p) ih

/-- Full sweep row matrix has a unique stationary distribution vector. -/
theorem sweepRow_exists_unique_stationary_of_fullSweep (order : List U) (h : IsFullSweep order)
    (T : Temperature) (p : BMParams ℝ U part) :
    ∃! v : stdSimplex ℝ State, IsStationary (sweepRowMatrix p T order) v :=
  exists_unique_stationary_distribution_of_irreducible
    (h_stoch := sweepRowMatrix_isStochastic order p T)
    (h_irred := sweepRowMatrix_irred_of_fullSweep order h p T)

/-- **Main result:** full sweep has unique stationary vector equal to Boltzmann negative phase. -/
theorem sequentialSweep_uniqueStationaryVec_of_fullSweep (order : List U) (h : IsFullSweep order)
    (T : Temperature) (p : BMParams ℝ U part) :
    ∃! v : stdSimplex ℝ State, IsStationary (sweepRowMatrix p T order) v ∧
      vecToMeasure v = negativePhaseMeasure part p T := by
  have huniq := sweepRow_exists_unique_stationary_of_fullSweep order h T p
  refine ExistsUnique.intro (negativePhaseVec T p) ⟨?_, ?_⟩ ?_
  · exact negativePhaseVec_is_stationary_sweepRow order T p
  · dsimp [negativePhaseVec, negativePhaseMeasure]
    exact vecToMeasure_eq_μBoltz (NN := NN ℝ U part) (spec := energySpec part) p T
  · intro y hy
    rcases hy with ⟨hy1, _⟩
    exact huniq.unique hy1 (negativePhaseVec_is_stationary_sweepRow order T p)

/-- Corollary: the unique stationary vector equals `negativePhaseVec`. -/
theorem sequentialSweep_uniqueStationaryVec_eq_negativePhase (order : List U) (h : IsFullSweep order)
    (T : Temperature) (p : BMParams ℝ U part) :
    (Classical.choose (sweepRow_exists_unique_stationary_of_fullSweep order h T p).exists)
      = negativePhaseVec T p := by
  have huniq := sweepRow_exists_unique_stationary_of_fullSweep order h T p
  exact (huniq.unique (negativePhaseVec_is_stationary_sweepRow order T p)
    (Classical.choose_spec huniq.exists)).symm

/-- Ergodicity package for full sequential sweep (mirrors `negativePhaseMeasure_is_gibbs_stationary`). -/
theorem negativePhaseMeasure_is_sequentialSweep_unique (order : List U) (h : IsFullSweep order)
    (T : Temperature) (p : BMParams ℝ U part) :
    Kernel.Invariant (sequentialSweepKernel part p T order) (negativePhaseMeasure part p T) ∧
      Matrix.IsIrreducible (sweepRowMatrix p T order) ∧
      Matrix.IsPrimitive (sweepRowMatrix p T order) ∧
      ∃! v : stdSimplex ℝ State, IsStationary (sweepRowMatrix p T order) v := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact sequentialSweepKernel_invariant_negativePhase part order p T
  · exact sweepRowMatrix_irred_of_fullSweep order h p T
  · exact sweepRowMatrix_primitive_of_fullSweep order h p T
  · exact sweepRow_exists_unique_stationary_of_fullSweep order h T p

/-- Verified `IsMCMC` instance for full sequential sweep; used in `CDConvergence`. -/
noncomputable instance sweepRowMatrix_isMCMC (order : List U) (h : IsFullSweep order)
    (T : Temperature) (p : BMParams ℝ U part) :
    IsMCMC (sweepRowMatrix p T order) (negativePhaseVec T p) where
  stochastic := sweepRowMatrix_isStochastic order p T
  stationary := negativePhaseVec_is_stationary_sweepRow order T p
  irreducible := sweepRowMatrix_irred_of_fullSweep order h p T
  primitive := sweepRowMatrix_primitive_of_fullSweep order h p T

end BMVisible

#lint only docBlame
