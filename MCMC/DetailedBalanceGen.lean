/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Order.CompletePartialOrder
import Mathlib.Probability.Kernel.Invariance
import Mathlib.Probability.ProbabilityMassFunction.Monad

/-!
# Detailed balance on finite types

Finite-sum expansions of restricted integrals and reversibility from pointwise balance.
-/

open MeasureTheory Filter Set
open scoped ProbabilityTheory ENNReal NNReal

variable {α : Type*} [MeasurableSpace α]

namespace ProbabilityTheory.Kernel

/-- Reversible kernels leave `π` invariant. -/
theorem Invariant.of_IsReversible
    {κ : Kernel α α} [IsMarkovKernel κ] {π : Measure α}
    (h_rev : IsReversible κ π) : Invariant κ π := by
  ext s hs
  have h' := (h_rev hs MeasurableSet.univ).symm
  have h'' : ∫⁻ x, κ x s ∂π = ∫⁻ x in s, κ x Set.univ ∂π := by
    simpa [Measure.restrict_univ] using h'
  have hπ : ∫⁻ x, κ x s ∂π = π s := h''.trans (by simp [measure_univ])
  calc
    (π.bind κ) s = ∫⁻ x, κ x s ∂π := ?_
    _ = π s := hπ
  · exact Measure.bind_apply hs (Kernel.aemeasurable _)
section ReversibilityFinite

open MeasureTheory ProbabilityTheory Classical

variable {α : Type*}
variable [Fintype α] [DecidableEq α]
variable [MeasurableSpace α] [MeasurableSingletonClass α]
variable (π : Measure α) (κ : Kernel α α)

section AuxFiniteSum

/-- General finite-type identity:
a sum over the whole type with an `if … ∈ S` guard can be rewritten
as a sum over the `Finset` of the elements that satisfy the guard. -/
lemma Finset.sum_if_mem_eq_sum_filter
    {α β : Type*} [Fintype α] [DecidableEq α] [AddCommMonoid β]
    (S : Set α) (f : α → β) :
    (∑ x : α, (if x ∈ S then f x else 0))
      = ∑ x ∈ S.toFinset, f x := by
  have h_univ :
      (∑ x : α, (if x ∈ S then f x else 0))
        = ∑ x ∈ (Finset.univ : Finset α), (if x ∈ S then f x else 0) := by
    simp
  have h_filter :
      (∑ x ∈ (Finset.univ : Finset α), (if x ∈ S then f x else 0))
        = ∑ x ∈ (Finset.univ.filter fun x : α => x ∈ S), f x := by
    simpa using
      (Finset.sum_filter
          (s := (Finset.univ : Finset α))
          (p := fun x : α => x ∈ S)
          (f := f)).symm
  have h_ident :
      (Finset.univ.filter fun x : α => x ∈ S) = S.toFinset := by
    ext x
    by_cases hx : x ∈ S
    · simp [hx, Finset.mem_filter, Set.mem_toFinset]
    · simp [hx, Finset.mem_filter, Set.mem_toFinset]
  simp [h_filter, h_ident]

lemma Finset.sum_subset_of_subset
    {α β : Type*} [Fintype α] [DecidableEq α] [AddCommMonoid β]
    (S : Set α) (f : α → β)
    (_h₁ : ∀ x, x ∈ S.toFinset → True)
    (_h₂ : ∀ x, x ∈ S.toFinset → False → False)
    (_h₃ : ∀ x, x ∈ S.toFinset → True) :
    (∑ x : α, (if x ∈ S then f x else 0))
      = ∑ x ∈ S.toFinset, f x :=
  Finset.sum_if_mem_eq_sum_filter S f

/-- Every subset of a finite type is finite. -/
lemma Set.finite_of_subsingleton_fintype {γ : Type*} [Fintype γ] (S : Set γ) : S.Finite :=
  Set.toFinite S

end AuxFiniteSum
section FiniteMeasureAPI

variable {α : Type*}

/-- On a finite discrete measurable space (⊤ σ–algebra), every set is measurable. -/
@[simp] lemma measurableSet_univ_of_fintype
    [Fintype α] [MeasurableSpace α] (hσ : ‹MeasurableSpace α› = ⊤)
    (s : Set α) : MeasurableSet s := by
  subst hσ; trivial

/-- For a finite type with counting measure, the (lower) integral
is the finite sum (specialization of the `tsum` version). -/
lemma lintegral_count_fintype
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype α] [DecidableEq α]
    (f : α → ℝ≥0∞) :
    ∫⁻ x, f x ∂(Measure.count : Measure α) = ∑ x : α, f x := by
  simpa [tsum_fintype] using MeasureTheory.lintegral_count f

-- Finite-type restricted lintegral as a weighted finite sum.
lemma lintegral_fintype_measure_restrict
    {α : Type*}
    [Fintype α] [DecidableEq α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure α) (A : Set α)
    (f : α → ℝ≥0∞) :
    ∫⁻ x in A, f x ∂μ
      = ∑ x : α, (if x ∈ A then μ {x} * f x else 0) := by
  have hRestr :
      ∫⁻ x in A, f x ∂μ
        = ∑ x : α, f x * (μ.restrict A) {x} := by
    simpa using (lintegral_fintype (μ:=μ.restrict A) (f:=f))
  have hSingleton :
      ∀ x : α, (μ.restrict A) {x} = (if x ∈ A then μ {x} else 0) := by
    intro x
    by_cases hx : x ∈ A
    · have hInter : ({x} : Set α) ∩ A = {x} := by
        ext y; constructor
        · intro hy; rcases hy with ⟨hy1, hy2⟩
          simp at hy1
          subst hy1
          simp
        · intro hy
          simp [hy]
          simp_all only [MeasurableSet.singleton, Measure.restrict_apply, mem_singleton_iff]
      simp [Measure.restrict_apply, hx, hInter]
    · have hInter : ({x} : Set α) ∩ A = (∅ : Set α) := by
        apply Set.eq_empty_iff_forall_notMem.2
        intro y hy
        rcases hy with ⟨hy1, hy2⟩
        have : y = x := by simpa [Set.mem_singleton_iff] using hy1
        subst this
        exact hx hy2
      simp [Measure.restrict_apply, hx, hInter]
  calc
    ∫⁻ x in A, f x ∂μ = ∑ x : α, f x * (μ.restrict A) {x} := ?_
    _ = ∑ x : α, f x * (if x ∈ A then μ {x} else 0) := ?_
    _ = ∑ x : α, if x ∈ A then μ {x} * f x else 0 := ?_
  · exact hRestr
  · simp [hSingleton]
  · refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : x ∈ A <;> simp [hx, mul_comm]

/-- Probability measure style formula for a finite type:
turn a restricted integral into a finite sum with point masses. -/
lemma lintegral_fintype_prob_restrict
    [Fintype α] [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure α) [IsFiniteMeasure μ]
    (A : Set α) (f : α → ℝ≥0∞) :
    ∫⁻ x in A, f x ∂μ
      = ∑ x : α, (if x ∈ A then μ {x} * f x else 0) := by
  simpa using lintegral_fintype_measure_restrict μ A f

/-- Restricted version over the counting measure (finite type). -/
lemma lintegral_count_restrict
    [MeasurableSpace α] [MeasurableSingletonClass α] [Fintype α] [DecidableEq α]
    (A : Set α) (f : α → ℝ≥0∞) :
    ∫⁻ x in A, f x ∂(Measure.count : Measure α) = ∑ x : α, if x ∈ A then f x else 0 := by
  have hμ : ∀ x : α, (Measure.count : Measure α) {x} = 1 := fun x => by simp
  simpa [hμ, one_mul] using
    lintegral_fintype_prob_restrict (μ := Measure.count) A f

/-- Convenience rewriting for the specific pattern used in detailed balance proofs:
move `μ {x}` factor to the left of function argument. -/
lemma lintegral_restrict_as_sum_if
    [Fintype α] [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure α) (A : Set α)
    (g : α → ℝ≥0∞) :
    ∫⁻ x in A, g x ∂μ
      = ∑ x : α, (if x ∈ A then μ {x} * g x else 0) :=
  lintegral_fintype_measure_restrict μ A g

end FiniteMeasureAPI

@[simp] lemma ofFunOfCountable_apply
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Countable α] [MeasurableSingletonClass α]
    (f : α → Measure β) (a : α) :
    Kernel.ofFunOfCountable f a = f a := rfl

omit [Fintype α] in
/-- Finite discrete expansion of a restricted lintegral of a kernel (measurable singletons). -/
lemma lintegral_kernel_restrict_fintype [Fintype α]
    (A : Set α) :
    ∫⁻ x in A, κ x A ∂π
      =
    ∑ x : α, (if x ∈ A then π {x} * κ x A else 0) := by
  simpa using
    (lintegral_restrict_as_sum_if (μ:=π) (A:=A) (g:=fun x => κ x A))

open MeasureTheory Set Finset Kernel

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- On a finite (any finite subset) space with measurable singletons, the measure of a finite
set under a kernel is the finite sum of the singleton masses. -/
lemma measure_eq_sum_finset
    [DecidableEq α] [MeasurableSpace α] [MeasurableSpace β] [MeasurableSingletonClass α]
    (κ : Kernel β α) (x : β) {B : Set α} (hB : B.Finite) :
    κ x B = ∑ y ∈ hB.toFinset, κ x {y} := by
  have hBset : B = (hB.toFinset : Set α) := by
    ext a; aesop
  set s : Finset α := hB.toFinset
  suffices H : κ x (s : Set α) = ∑ y ∈ s, κ x {y} by aesop
  refine s.induction_on ?h0 ?hstep
  · simp
  · intro a s ha_notin hIH
    have hDisj : Disjoint ({a} : Set α) (s : Set α) := by
      refine disjoint_left.mpr ?_
      intro y hy_in hy_in_s
      have : y = a := by simpa using hy_in
      subst this
      aesop
    have hMeas_s : MeasurableSet (s : Set α) := by
      refine s.induction_on ?m0 ?mstep
      · simp
      · intro b t hb_notin ht
        simpa [Finset.coe_insert, Set.image_eq_range, Set.union_comm, Set.union_left_comm,
               Set.union_assoc] using (ht.union (measurableSet_singleton b))
    have hMeas_a : MeasurableSet ({a} : Set α) := measurableSet_singleton a
    have hUnion :
        ((insert a s : Finset α) : Set α)
          = ({a} : Set α) ∪ (s : Set α) := by
      ext y; by_cases hy : y = a
      · subst hy; simp
      · simp [hy]
    have hAdd :
        κ x ((insert a s : Finset α) : Set α)
          = κ x ({a} : Set α) + κ x (s : Set α) := by
      rw [← measure_union_add_inter {a} hMeas_s]
      simp_rw [hUnion, measure_union_add_inter {a} hMeas_s]
      exact measure_union hDisj hMeas_s
    have hSum :
        ∑ y ∈ insert a s, κ x {y}
          = κ x ({a} : Set α) + ∑ y ∈ s, κ x {y} := by
      simp [Finset.sum_insert, ha_notin]
    calc
      κ x ((insert a s : Finset α) : Set α) = κ x ({a} : Set α) + κ x (s : Set α) := ?_
      _ = κ x ({a} : Set α) + ∑ y ∈ s, κ x {y} := ?_
      _ = ∑ y ∈ insert a s, κ x {y} := ?_
    · exact hAdd
    · rw [hIH]
    · simp [hSum]

/-- Finite discrete reversibility from pointwise detailed balance. -/
lemma isReversible_of_pointwise_fintype
    (hPoint :
      ∀ ⦃x y⦄, π {x} * κ x {y} = π {y} * κ y {x})
    : ProbabilityTheory.Kernel.IsReversible κ π := by
  intro A B hA hB
  have hFinA : A.Finite := Set.finite_of_subsingleton_fintype A
  have hFinB : B.Finite := Set.finite_of_subsingleton_fintype B
  have hAexp :
      ∫⁻ x in A, κ x B ∂π
        = ∑ x ∈ hFinA.toFinset, π {x} * κ x B := by
    have h1 :
        ∫⁻ x in A, κ x B ∂π
          = ∑ x : α,
              (if x ∈ A then π {x} * κ x B else 0) := by
      simpa using
        (lintegral_restrict_as_sum_if (μ:=π) (A:=A) (g:=fun x => κ x B))
    have :
        (∑ x : α, (if x ∈ A then π {x} * κ x B else 0))
          =
        ∑ x ∈ hFinA.toFinset, π {x} * κ x B := by
      simp_rw
        [(Finset.sum_if_mem_eq_sum_filter
            (S:=A) (f:=fun x => π {x} * κ x B))]
      rw [@toFinite_toFinset]
    simp [h1, this]
  have hBexp :
      ∫⁻ x in B, κ x A ∂π
        = ∑ x ∈ hFinB.toFinset, π {x} * κ x A := by
    have h1 :
        ∫⁻ x in B, κ x A ∂π
          = ∑ x : α,
              (if x ∈ B then π {x} * κ x A else 0) := by
      simpa using
        (lintegral_restrict_as_sum_if (μ:=π) (A:=B) (g:=fun x => κ x A))
    have :
        (∑ x : α, (if x ∈ B then π {x} * κ x A else 0))
          =
        ∑ x ∈ hFinB.toFinset, π {x} * κ x A := by
      simp_rw
        [(Finset.sum_if_mem_eq_sum_filter
            (S:=B) (f:=fun x => π {x} * κ x A))]
      rw [@toFinite_toFinset]
    simp [h1, this]
  have hκB :
      ∀ x, κ x B = ∑ y ∈ hFinB.toFinset, κ x {y} := by
    intro x; simpa using
      (Kernel.measure_eq_sum_finset (κ:=κ) x hFinB)
  have hκA :
      ∀ x, κ x A = ∑ y ∈ hFinA.toFinset, κ x {y} := by
    intro x; simpa using
      (Kernel.measure_eq_sum_finset (κ:=κ) x hFinA)
  have hL :
      ∑ x ∈ hFinA.toFinset, π {x} * κ x B
        =
      ∑ x ∈ hFinA.toFinset, ∑ y ∈ hFinB.toFinset, π {x} * κ x {y} := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    simp_rw [hκB x, Finset.mul_sum]
  have hR :
      ∑ x ∈ hFinB.toFinset, π {x} * κ x A
        =
      ∑ x ∈ hFinB.toFinset, ∑ y ∈ hFinA.toFinset, π {x} * κ x {y} := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    simp_rw [hκA x, Finset.mul_sum]
  erw [hAexp, hBexp, hL, hR]
  have hRew :
      ∑ x ∈ hFinA.toFinset, ∑ y ∈ hFinB.toFinset, π {x} * κ x {y}
        =
      ∑ x ∈ hFinA.toFinset, ∑ y ∈ hFinB.toFinset, π {y} * κ y {x} := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    refine Finset.sum_congr rfl ?_
    intro y hy
    exact hPoint (x:=x) (y:=y)
  calc
    ∑ x ∈ hFinA.toFinset, ∑ y ∈ hFinB.toFinset, π {x} * κ x {y} =
        ∑ x ∈ hFinA.toFinset, ∑ y ∈ hFinB.toFinset, π {y} * κ y {x} := ?_
    _ = ∑ y ∈ hFinB.toFinset, ∑ x ∈ hFinA.toFinset, π {y} * κ y {x} := ?_
    _ = ∑ x ∈ hFinB.toFinset, ∑ y ∈ hFinA.toFinset, π {x} * κ x {y} := rfl
  · exact hRew
  · simpa using
      Finset.sum_comm (s := hFinA.toFinset) (t := hFinB.toFinset)
        (f := fun x y => π {y} * κ y {x})

end ReversibilityFinite
end ProbabilityTheory.Kernel

/-- Singleton evaluation of a PMF turned into a measure. -/
@[simp]
lemma PMF.toMeasure_singleton
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (p : PMF α) (a : α) :
    p.toMeasure {a} = p a := by
  rw [toMeasure_apply_eq_toOuterMeasure, toOuterMeasure_apply_singleton]

/-- (Finite) evaluation of the measure of a set under a bind of PMFs. -/
lemma PMF.toMeasure_bind_fintype
    {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (p : PMF α) (f : α → PMF β) (B : Set β) (hB : MeasurableSet B) :
    (p.bind f).toMeasure B = ∑ a : α, p a * (f a).toMeasure B := by
  have hBind_apply : ∀ b : β, (p.bind f) b = ∑ a : α, p a * f a b := fun b => by
    simp [PMF.bind_apply, tsum_fintype]
  have hMeasure :
    (p.bind f).toMeasure B
      = ∑ b : β, (p.bind f) b * B.indicator (fun _ : β => (1 : ℝ≥0∞)) b := by
        have h0 :
          (p.bind f).toMeasure B
            = ∑ b : β, B.indicator (p.bind f) b := by
            simp [PMF.toMeasure, hB]
        refine h0.trans ?_
        refine Finset.sum_congr rfl ?_
        intro b _
        by_cases hb : b ∈ B
        · simp [hb]
        · simp [hb]
  calc
    (p.bind f).toMeasure B =
        ∑ b : β, (p.bind f) b * B.indicator (fun _ : β => (1 : ℝ≥0∞)) b := ?_
    _ = ∑ b : β, (∑ a : α, p a * f a b) * B.indicator (fun _ : β => (1 : ℝ≥0∞)) b := ?_
    _ = ∑ b : β, ∑ a : α, (p a * f a b) * B.indicator (fun _ : β => (1 : ℝ≥0∞)) b := ?_
    _ = ∑ a : α, ∑ b : β, (p a * f a b) * B.indicator (fun _ : β => (1 : ℝ≥0∞)) b := ?_
    _ = ∑ a : α, p a * (∑ b : β, f a b * B.indicator (fun _ : β => (1 : ℝ≥0∞)) b) := ?_
    _ = ∑ a : α, p a * (f a).toMeasure B := ?_
  · exact hMeasure
  · refine Finset.sum_congr rfl fun b _ => ?_
    simp [hBind_apply]
  · refine Finset.sum_congr rfl fun b _ => ?_
    simpa using Finset.sum_mul (s := Finset.univ) (f := fun a => p a * f a b)
      (a := B.indicator (fun _ : β => (1 : ℝ≥0∞)) b)
  · simpa using
      Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
        (f := fun b a => (p a * f a b) * B.indicator (fun _ : β => (1 : ℝ≥0∞)) b)
  · refine Finset.sum_congr rfl fun a _ => ?_
    have hTerm :
        ∑ b : β, (p a * f a b) * B.indicator (fun _ : β => (1 : ℝ≥0∞)) b =
          p a * ∑ b : β, f a b * B.indicator (fun _ : β => (1 : ℝ≥0∞)) b := by
      simpa [mul_assoc, Finset.mul_sum] using
        (Finset.mul_sum (a := p a) (s := Finset.univ)
          (f := fun b => f a b * B.indicator (fun _ : β => (1 : ℝ≥0∞)) b)).symm
    simp [hTerm]
  · refine Finset.sum_congr rfl fun a _ => ?_
    have hIndicator :
        (∑ b : β, f a b * B.indicator (fun _ : β => (1 : ℝ≥0∞)) b) =
          ∑ b : β, B.indicator (f a) b := by
      refine Finset.sum_congr rfl fun b _ => by
        by_cases hb : b ∈ B <;> simp [hb]
    simp [hIndicator, PMF.toMeasure, hB]
