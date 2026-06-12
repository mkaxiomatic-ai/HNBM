/-
Copyright (c) 2025 HNBM contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.bmvisible.Energy
import HopfieldNet.bmvisible.Phases
import HopfieldNet.bmvisible.BoltzmannBridge
import HopfieldNet.BoltzmannLearningQuiver.VectorGibbsLearning
import HopfieldNet.BoltzmannLearningQuiver.VectorGibbsConvexity
import HopfieldNet.BoltzmannLearningQuiver.VectorGibbsDescent

/-!
# Exact Boltzmann learning on visible/hidden BM states
-/

namespace BMVisible

open NeuralNetwork BoltzmannLearningQuiver ZeroOne VectorGibbs Convex

variable {U : Type} [Fintype U] [DecidableEq U] [Nonempty U]
variable (part : VisibleHiddenPartition U)

local notation "Θuniv" => (Set.univ : Set (Θ U))

/-- Single-sample negative log-likelihood at a clamped visible pattern. -/
noncomputable abbrev negLogLik (vp : VisiblePattern (R := ℝ) part) (θ : Θ U) : ℝ :=
  VectorGibbs.negLogLik (X := BMState ℝ U part) (Θ := Θ U) (bmStat part) (dataState part vp) θ

theorem hasGradientAt_negLogLik (vp : VisiblePattern (R := ℝ) part) (θ : Θ U) :
    HasGradientAt (fun θ' => negLogLik part vp θ')
      (bmStat part (dataState part vp) - VectorGibbs.expectation (bmStat part) θ) θ :=
  by simpa [negLogLik] using VectorGibbs.hasGradientAt_negLogLik (bmStat part) (dataState part vp) θ

theorem hasGradientAt_negLogLik_scaled (T : Temperature) (vp : VisiblePattern (R := ℝ) part)
    (p : BMParams ℝ U part) :
    HasGradientAt (fun θ' => negLogLik part vp θ') (learningDirection part T p vp)
      (bmScaledTheta part T p) := by
  dsimp [learningDirection]
  rw [← vectorGibbsExpectationStat_eq_modelExpectationStat, vectorGibbsExpectationStat]
  exact hasGradientAt_negLogLik part vp (bmScaledTheta part T p)

theorem convexOn_negLogLik (vp : VisiblePattern (R := ℝ) part) :
    ConvexOn ℝ Θuniv (fun θ => negLogLik part vp θ) :=
  VectorGibbs.convexOn_negLogLik (X := BMState ℝ U part) (Θ := Θ U) (bmStat part) (dataState part vp)

theorem negLogLik_descent_step_scaled (T : Temperature) (vp : VisiblePattern (R := ℝ) part)
    (p : BMParams ℝ U part) (hne : bmStat part (dataState part vp) ≠ modelExpectationStat part T p) :
    ∃ (η : ℝ), 0 < η ∧
      negLogLik part vp (bmScaledTheta part T p - η • learningDirection part T p vp) <
        negLogLik part vp (bmScaledTheta part T p) := by
  have heq : VectorGibbs.expectation (bmStat part) (bmScaledTheta part T p) = modelExpectationStat part T p := by
    rw [← vectorGibbsExpectationStat_eq_modelExpectationStat, vectorGibbsExpectationStat]
  obtain ⟨η, hη, hdec⟩ :=
    VectorGibbs.negLogLik_descent_step_gradient (X := BMState ℝ U part) (Θ := Θ U) (bmStat part)
      (dataState part vp) (bmScaledTheta part T p) (by rwa [heq])
  exact ⟨η, hη, by simpa [learningDirection, heq] using hdec⟩

end BMVisible

#lint only docBlame
