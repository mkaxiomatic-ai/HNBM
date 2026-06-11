/-
Copyright (c) 2025 HNBM contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Vector-parameter finite Gibbs identities

Finite exponential-family core: `∇ (log Z) θ = - E_θ[stat]`.
-/

namespace NeuralNetwork
namespace BoltzmannLearningQuiver
namespace VectorGibbs

open scoped BigOperators
open Finset InnerProductSpace

variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
variable {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]

/-- Linear energy `E_θ(x) = -⟪stat x, θ⟫`. -/
noncomputable def energy (stat : X → Θ) (θ : Θ) (x : X) : ℝ :=
  - inner ℝ (stat x) θ

/-- Unnormalized Gibbs weight `w_θ(x) = exp(E_θ(x))`. -/
noncomputable def weight (stat : X → Θ) (θ : Θ) (x : X) : ℝ :=
  Real.exp (energy stat θ x)

/-- Partition function `Z(θ) = ∑_x w_θ(x)`. -/
noncomputable def Z (stat : X → Θ) (θ : Θ) : ℝ :=
  ∑ x ∈ univ, weight stat θ x

omit [DecidableEq X] [CompleteSpace Θ] in
/-- Partition function is positive. -/
lemma Z_pos (stat : X → Θ) (θ : Θ) : 0 < Z stat θ := by
  refine Finset.sum_pos ?_ univ_nonempty
  intro x hx
  simp [weight, energy, Real.exp_pos]

omit [DecidableEq X] [CompleteSpace Θ] in
/-- Partition function is nonzero. -/
lemma Z_ne_zero (stat : X → Θ) (θ : Θ) : Z stat θ ≠ 0 :=
  ne_of_gt (Z_pos stat θ)

/-- Vector numerator `∑_x w_θ(x) • stat(x)`. -/
noncomputable def num (stat : X → Θ) (θ : Θ) : Θ :=
  ∑ x ∈ univ, weight stat θ x • stat x

/-- Gibbs expectation of `stat` under normalized weights. -/
noncomputable def expectation (stat : X → Θ) (θ : Θ) : Θ :=
  (Z stat θ)⁻¹ • num stat θ

omit [Fintype X] [DecidableEq X] [Nonempty X] in
/-- Fréchet derivative of a Gibbs weight. -/
lemma hasFDerivAt_weight (stat : X → Θ) (x : X) (θ : Θ) :
    HasFDerivAt (fun θ' => weight stat θ' x)
      (weight stat θ x • (-(toDual ℝ Θ (stat x)))) θ := by
  have hlin : HasFDerivAt (fun θ' => inner ℝ (stat x) θ') (toDual ℝ Θ (stat x)) θ := by
    simpa [InnerProductSpace.toDual_apply_apply] using (toDual ℝ Θ (stat x)).hasFDerivAt (x := θ)
  have hE : HasFDerivAt (fun θ' => energy stat θ' x) (-(toDual ℝ Θ (stat x))) θ := by
    simpa [energy] using hlin.neg
  simpa [weight] using
    (Real.hasDerivAt_exp (energy stat θ x)).comp_hasFDerivAt θ hE

omit [DecidableEq X] [Nonempty X] in
/-- Fréchet derivative of the partition function. -/
lemma hasFDerivAt_Z (stat : X → Θ) (θ : Θ) :
    HasFDerivAt (fun θ' => Z stat θ')
      (∑ x ∈ univ, weight stat θ x • (-(toDual ℝ Θ (stat x)))) θ := by
  classical
  simpa [Z] using
    HasFDerivAt.fun_sum (u := univ) (A := fun x θ' => weight stat θ' x)
      (A' := fun x => weight stat θ x • (-(toDual ℝ Θ (stat x)))) (x := θ)
      (fun x _ => hasFDerivAt_weight stat x θ)

omit [DecidableEq X] in
/-- `∇ (log Z) θ = - expectation stat θ`. -/
theorem hasGradientAt_logZ (stat : X → Θ) (θ : Θ) :
    HasGradientAt (fun θ' => Real.log (Z stat θ')) (-(expectation stat θ)) θ := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hlog := (hasFDerivAt_Z stat θ).log (Z_ne_zero stat θ)
  have hD :
      toDual ℝ Θ (-(expectation stat θ)) =
        (Z stat θ)⁻¹ • ∑ x ∈ univ, weight stat θ x • (-(toDual ℝ Θ (stat x))) := by
    ext h
    classical
    simp [expectation, num, Z, weight, energy, InnerProductSpace.toDual_apply_apply]
  rw [hD]
  exact hlog

end VectorGibbs
end BoltzmannLearningQuiver
end NeuralNetwork

#lint only docBlame docBlameThm
