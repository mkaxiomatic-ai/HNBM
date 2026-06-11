/-
Copyright (c) 2025 HNBM contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.BoltzmannLearningQuiver.VectorGibbs
import Mathlib.Analysis.Calculus.FDeriv.Add

/-!
# Vector-parameter Gibbs learning identities

`∇ (⟪stat x, θ⟫ + log Z(θ)) = stat x - E_θ[stat]`.
-/

namespace NeuralNetwork
namespace BoltzmannLearningQuiver
namespace VectorGibbs

open InnerProductSpace

variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
variable {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]

/-- Single-sample negative log-likelihood for `w_θ(x)=exp(-⟪stat x, θ⟫)`. -/
noncomputable def negLogLik (stat : X → Θ) (x : X) (θ : Θ) : ℝ :=
  inner ℝ (stat x) θ + Real.log (Z stat θ)

omit [DecidableEq X] in
/-- Gradient of single-sample negative log-likelihood. -/
theorem hasGradientAt_negLogLik (stat : X → Θ) (x : X) (θ : Θ) :
    HasGradientAt (fun θ' => negLogLik stat x θ') (stat x - expectation stat θ) θ := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h1 : HasFDerivAt (fun θ' => inner ℝ (stat x) θ') (toDual ℝ Θ (stat x)) θ := by
    simpa [InnerProductSpace.toDual_apply_apply] using (toDual ℝ Θ (stat x)).hasFDerivAt (x := θ)
  have h2 := (hasGradientAt_logZ stat θ).hasFDerivAt
  simpa [negLogLik, sub_eq_add_neg, map_add, map_neg] using h1.add h2

end VectorGibbs
end BoltzmannLearningQuiver
end NeuralNetwork

#lint only docBlame docBlameThm
