/-
Copyright (c) 2025 HNBM contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.BoltzmannLearningQuiver.Energy
import HopfieldNet.BoltzmannLearningQuiver.Phases
import HopfieldNet.BoltzmannLearningQuiver.BoltzmannBridge
import HopfieldNet.BoltzmannLearningQuiver.VectorGibbsLearning
import HopfieldNet.BoltzmannLearningQuiver.VectorGibbsConvexity
import HopfieldNet.BoltzmannLearningQuiver.VectorGibbsDescent

/-!
# Exact Boltzmann learning: gradient, convexity, descent

Specializes `VectorGibbs` to quiver `State ℝ U`.
-/

namespace NeuralNetwork
namespace BoltzmannLearningQuiver
namespace SymmetricBinary

open VectorGibbs Convex

variable {U : Type} [Fintype U] [DecidableEq U] [Nonempty U]

local notation "Θuniv" => (Set.univ : Set (Θ U))

/-- Single-sample negative log-likelihood. -/
noncomputable abbrev negLogLik (s₀ : State ℝ U) (θ : Θ U) : ℝ :=
  VectorGibbs.negLogLik (X := State ℝ U) (Θ := Θ U) stat s₀ θ

/-- Gradient identity: data statistic minus model statistic. -/
theorem hasGradientAt_negLogLik (s₀ : State ℝ U) (θ : Θ U) :
    HasGradientAt (fun θ' => negLogLik s₀ θ') (stat s₀ - VectorGibbs.expectation stat θ) θ :=
  by simpa [negLogLik] using VectorGibbs.hasGradientAt_negLogLik stat s₀ θ

/-- Gradient at `thetaFromParams p`. -/
theorem hasGradientAt_negLogLik_params (s₀ : State ℝ U) (p : Params ℝ U) :
    HasGradientAt (fun θ' => negLogLik s₀ θ')
      (stat s₀ - VectorGibbs.expectation stat (thetaFromParams p)) (thetaFromParams p) :=
  hasGradientAt_negLogLik s₀ (thetaFromParams p)

/-- Gradient equals `learningDirection` at `scaledTheta T p`. -/
theorem hasGradientAt_negLogLik_scaled (T : Temperature) (s₀ : State ℝ U) (p : Params ℝ U) :
    HasGradientAt (fun θ' => negLogLik s₀ θ') (learningDirection T p s₀) (scaledTheta T p) := by
  rw [learningDirection, ← vectorGibbsExpectationStat_eq_modelExpectationStat, vectorGibbsExpectationStat]
  exact hasGradientAt_negLogLik s₀ (scaledTheta T p)

/-- Single-sample NLL is convex in `θ`. -/
theorem convexOn_negLogLik (s₀ : State ℝ U) :
    ConvexOn ℝ Θuniv (fun θ => negLogLik s₀ θ) :=
  VectorGibbs.convexOn_negLogLik (X := State ℝ U) (Θ := Θ U) stat s₀

/-- One-step descent along a nonzero gradient direction. -/
theorem negLogLik_descent_step (s₀ : State ℝ U) (θ : Θ U) (grad : Θ U)
    (hgrad : HasGradientAt (fun θ' => negLogLik s₀ θ') grad θ) (hgrad_ne : grad ≠ 0) :
    ∃ (η : ℝ), 0 < η ∧ negLogLik s₀ (θ - η • grad) < negLogLik s₀ θ :=
  VectorGibbs.negLogLik_descent_step (X := State ℝ U) (Θ := Θ U) stat s₀ θ grad hgrad hgrad_ne

/-- Strict descent along the NLL gradient. -/
theorem negLogLik_descent_step_gradient (s₀ : State ℝ U) (θ : Θ U)
    (hne : stat s₀ ≠ VectorGibbs.expectation stat θ) :
    ∃ (η : ℝ), 0 < η ∧
      negLogLik s₀ (θ - η • (stat s₀ - VectorGibbs.expectation stat θ)) < negLogLik s₀ θ :=
  VectorGibbs.negLogLik_descent_step_gradient (X := State ℝ U) (Θ := Θ U) stat s₀ θ hne

/-- One-step descent along `learningDirection` at `scaledTheta T p`. -/
theorem negLogLik_descent_step_scaled (T : Temperature) (s₀ : State ℝ U) (p : Params ℝ U)
    (hne : stat s₀ ≠ modelExpectationStat T p) :
    ∃ (η : ℝ), 0 < η ∧
      negLogLik s₀ (scaledTheta T p - η • learningDirection T p s₀) <
        negLogLik s₀ (scaledTheta T p) := by
  have heq : VectorGibbs.expectation stat (scaledTheta T p) = modelExpectationStat T p := by
    rw [← vectorGibbsExpectationStat_eq_modelExpectationStat, vectorGibbsExpectationStat]
  obtain ⟨η, hη, hdec⟩ :=
    negLogLik_descent_step_gradient s₀ (scaledTheta T p) (by rwa [heq])
  exact ⟨η, hη, by simpa [learningDirection, heq] using hdec⟩

end SymmetricBinary
end BoltzmannLearningQuiver
end NeuralNetwork

#lint only docBlame docBlameThm
