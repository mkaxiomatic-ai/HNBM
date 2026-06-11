/-
Copyright (c) 2025 HNBM contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.BoltzmannLearningQuiver.VectorGibbsLearning
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.MeanInequalities

/-!
# Convexity of finite vector-parameter Gibbs objectives

`Z`, `log Z`, and single-sample NLL are convex in `θ`.
-/

namespace NeuralNetwork
namespace BoltzmannLearningQuiver
namespace VectorGibbs

open scoped BigOperators
open Finset InnerProductSpace Convex Real Set NNReal

variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
variable {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]

local notation "Θuniv" => (univ : Set Θ)

omit [DecidableEq X] [CompleteSpace Θ] in
/-- Gibbs weights are positive. -/
lemma weight_pos (stat : X → Θ) (θ : Θ) (x : X) :
    0 < weight (X := X) (Θ := Θ) stat θ x := by
  simp [weight, energy, Real.exp_pos]

omit [DecidableEq X] [CompleteSpace Θ] in
/-- The linear term `θ ↦ ⟪stat x, θ⟫` is convex on `univ`. -/
lemma convexOn_inner (stat : X → Θ) (x : X) :
    ConvexOn ℝ Θuniv (fun θ : Θ => inner ℝ (stat x) θ) := by
  refine ⟨convex_univ, fun θ₁ _ θ₂ _ a b ha hb hab => ?_⟩
  simp [inner_add_right, inner_smul_right, add_smul, smul_add, hab]

/-- Each unnormalized Gibbs weight is convex in `θ`. -/
lemma convexOn_weight (stat : X → Θ) (x : X) :
    ConvexOn ℝ Θuniv (fun θ : Θ => weight (X := X) (Θ := Θ) stat θ x) := by
  refine ⟨convex_univ, fun θ₁ _ θ₂ _ a b ha hb hab => ?_⟩
  have hcombo :
      energy (X := X) (Θ := Θ) stat (a • θ₁ + b • θ₂) x =
        a • energy (X := X) (Θ := Θ) stat θ₁ x + b • energy (X := X) (Θ := Θ) stat θ₂ x := by
    simp [energy, inner_add_right, inner_smul_right, add_smul, smul_add, hab]
    ac_rfl
  calc
    weight (X := X) (Θ := Θ) stat (a • θ₁ + b • θ₂) x
        = Real.exp (energy (X := X) (Θ := Θ) stat (a • θ₁ + b • θ₂) x) := rfl
    _ = Real.exp (a • energy (X := X) (Θ := Θ) stat θ₁ x +
          b • energy (X := X) (Θ := Θ) stat θ₂ x) := by rw [hcombo]
    _ ≤ a • Real.exp (energy (X := X) (Θ := Θ) stat θ₁ x) +
          b • Real.exp (energy (X := X) (Θ := Θ) stat θ₂ x) :=
      convexOn_exp.2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab
    _ = a • weight (X := X) (Θ := Θ) stat θ₁ x + b • weight (X := X) (Θ := Θ) stat θ₂ x := rfl

private lemma convexOn_finset_sum {ι : Type*} (s : Finset ι) (f : ι → Θ → ℝ)
    (hf : ∀ i ∈ s, ConvexOn ℝ Θuniv (f i)) :
    ConvexOn ℝ Θuniv (fun θ : Θ => ∑ i ∈ s, f i θ) := by
  classical
  revert hf
  refine Finset.induction_on s ?base ?step
  · intro _; simpa using convexOn_const (0 : ℝ) convex_univ
  · intro i s hi ih hf
    have hi' : ConvexOn ℝ Θuniv (f i) := hf i (mem_insert_self i s)
    have hs' : ∀ j ∈ s, ConvexOn ℝ Θuniv (f j) := fun j hj => hf j (mem_insert_of_mem hj)
    simpa [Finset.sum_insert hi] using hi'.add (ih hs')

omit [DecidableEq X] in
/-- The partition function `Z(θ) = ∑_x w_θ(x)` is convex in `θ`. -/
theorem convexOn_Z (stat : X → Θ) :
    ConvexOn ℝ Θuniv (fun θ : Θ => Z (X := X) (Θ := Θ) stat θ) := by
  classical
  simp only [Z]
  refine convexOn_finset_sum (s := univ) (f := fun x θ => weight (X := X) (Θ := Θ) stat θ x) ?_
  intro x hx
  exact convexOn_weight (X := X) (Θ := Θ) stat x

private lemma weight_convex_combo {stat : X → Θ} {θ₁ θ₂ : Θ} {a b : ℝ} (x : X) :
    weight (X := X) (Θ := Θ) stat (a • θ₁ + b • θ₂) x =
      Real.rpow (weight (X := X) (Θ := Θ) stat θ₁ x) a *
        Real.rpow (weight (X := X) (Θ := Θ) stat θ₂ x) b := by
  simp only [weight, energy, inner_add_right, inner_smul_right]
  have hexp (c : ℝ) (θ : Θ) :
      Real.exp (-(c * inner ℝ (stat x) θ)) = (Real.exp (-inner ℝ (stat x) θ)) ^ c := by
    rw [show -(c * inner ℝ (stat x) θ) = (-inner ℝ (stat x) θ) * c by ring, Real.exp_mul]
  rw [neg_add, Real.exp_add, hexp a, hexp b]
  simp [Real.rpow_eq_pow]

private lemma Z_combo_le {stat : X → Θ} {θ₁ θ₂ : Θ} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    Z (X := X) (Θ := Θ) stat (a • θ₁ + b • θ₂) ≤
      Real.rpow (Z (X := X) (Θ := Θ) stat θ₁) a *
        Real.rpow (Z (X := X) (Θ := Θ) stat θ₂) b := by
  classical
  have hpq : (a⁻¹).HolderConjugate b⁻¹ := Real.HolderConjugate.inv_inv ha hb hab
  have hweights :
      Z (X := X) (Θ := Θ) stat (a • θ₁ + b • θ₂) =
        ∑ x ∈ (univ : Finset X), Real.rpow (weight (X := X) (Θ := Θ) stat θ₁ x) a *
          Real.rpow (weight (X := X) (Θ := Θ) stat θ₂ x) b := by
    simp [Z, weight_convex_combo]
  have h_nonneg₁ :
      ∀ x ∈ (univ : Finset X), 0 ≤ Real.rpow (weight (X := X) (Θ := Θ) stat θ₁ x) a :=
    fun x _ => Real.rpow_nonneg (weight_pos stat θ₁ x).le _
  have h_nonneg₂ :
      ∀ x ∈ (univ : Finset X), 0 ≤ Real.rpow (weight (X := X) (Θ := Θ) stat θ₂ x) b :=
    fun x _ => Real.rpow_nonneg (weight_pos stat θ₂ x).le _
  have hf_pow (x : X) :
      Real.rpow (Real.rpow (weight (X := X) (Θ := Θ) stat θ₁ x) a) a⁻¹ =
        weight (X := X) (Θ := Θ) stat θ₁ x := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_mul (weight_pos stat θ₁ x).le, mul_inv_cancel₀ ha.ne', Real.rpow_one]
  have hg_pow (x : X) :
      Real.rpow (Real.rpow (weight (X := X) (Θ := Θ) stat θ₂ x) b) b⁻¹ =
        weight (X := X) (Θ := Θ) stat θ₂ x := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_mul (weight_pos stat θ₂ x).le, mul_inv_cancel₀ hb.ne', Real.rpow_one]
  have hholder :
      ∑ x ∈ (univ : Finset X), Real.rpow (weight (X := X) (Θ := Θ) stat θ₁ x) a *
          Real.rpow (weight (X := X) (Θ := Θ) stat θ₂ x) b ≤
        Real.rpow (∑ x ∈ (univ : Finset X), weight (X := X) (Θ := Θ) stat θ₁ x) a *
          Real.rpow (∑ x ∈ (univ : Finset X), weight (X := X) (Θ := Θ) stat θ₂ x) b := by
    have h1 := Real.inner_le_Lp_mul_Lq_of_nonneg (s := univ)
      (f := fun x => Real.rpow (weight (X := X) (Θ := Θ) stat θ₁ x) a)
      (g := fun x => Real.rpow (weight (X := X) (Θ := Θ) stat θ₂ x) b) hpq h_nonneg₁ h_nonneg₂
    calc
      ∑ x ∈ (univ : Finset X), Real.rpow (weight (X := X) (Θ := Θ) stat θ₁ x) a *
          Real.rpow (weight (X := X) (Θ := Θ) stat θ₂ x) b ≤
        Real.rpow (∑ x ∈ (univ : Finset X), Real.rpow (Real.rpow (weight (X := X) (Θ := Θ) stat θ₁ x) a) a⁻¹) a *
          Real.rpow (∑ x ∈ (univ : Finset X), Real.rpow (Real.rpow (weight (X := X) (Θ := Θ) stat θ₂ x) b) b⁻¹) b := by
        simpa [one_div, Real.rpow_eq_pow] using h1
      _ = Real.rpow (∑ x ∈ (univ : Finset X), weight (X := X) (Θ := Θ) stat θ₁ x) a *
            Real.rpow (∑ x ∈ (univ : Finset X), weight (X := X) (Θ := Θ) stat θ₂ x) b := by
        rw [Finset.sum_congr rfl (fun x _ => hf_pow x), Finset.sum_congr rfl (fun x _ => hg_pow x)]
  rw [hweights]
  exact hholder

/-- `θ ↦ log Z(θ)` is convex on `univ`. -/
theorem convexOn_logZ (stat : X → Θ) :
    ConvexOn ℝ Θuniv (fun θ : Θ => Real.log (Z (X := X) (Θ := Θ) stat θ)) := by
  refine ⟨convex_univ, fun θ₁ _ θ₂ _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  rcases eq_or_lt_of_le ha with (rfl | ha_pos)
  · have hb1 : b = 1 := by linarith
    simp [zero_smul, hb1, one_smul, zero_mul]
  rcases eq_or_lt_of_le hb with (rfl | hb_pos)
  · have ha1 : a = 1 := by linarith
    simp [zero_smul, ha1, one_smul, zero_mul]
  have hzpos : 0 < Z (X := X) (Θ := Θ) stat (a • θ₁ + b • θ₂) :=
    Z_pos (X := X) (Θ := Θ) stat _
  have hz1 : 0 < Z (X := X) (Θ := Θ) stat θ₁ := Z_pos (X := X) (Θ := Θ) stat θ₁
  have hz2 : 0 < Z (X := X) (Θ := Θ) stat θ₂ := Z_pos (X := X) (Θ := Θ) stat θ₂
  have hZ := Z_combo_le (stat := stat) (θ₁ := θ₁) (θ₂ := θ₂) ha_pos hb_pos hab
  have hsplit :
      Real.log (Real.rpow (Z (X := X) (Θ := Θ) stat θ₁) a *
          Real.rpow (Z (X := X) (Θ := Θ) stat θ₂) b) =
        a * Real.log (Z (X := X) (Θ := Θ) stat θ₁) + b * Real.log (Z (X := X) (Θ := Θ) stat θ₂) := by
    simp only [Real.rpow_eq_pow]
    rw [Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos hz1 a)) (ne_of_gt (Real.rpow_pos_of_pos hz2 b)),
      Real.log_rpow hz1, Real.log_rpow hz2]
  exact le_trans (Real.log_le_log hzpos hZ) (le_of_eq hsplit)

/-- Single-sample negative log-likelihood is convex in `θ`. -/
theorem convexOn_negLogLik (stat : X → Θ) (x : X) :
    ConvexOn ℝ Θuniv (fun θ : Θ => negLogLik (X := X) (Θ := Θ) stat x θ) := by
  simp [negLogLik]
  exact (convexOn_inner (X := X) (Θ := Θ) stat x).add (convexOn_logZ (X := X) (Θ := Θ) stat)

end VectorGibbs
end BoltzmannLearningQuiver
end NeuralNetwork

#lint only docBlame docBlameThm
