/-
Copyright (c) 2025 HNBM contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.BoltzmannLearningQuiver.VectorGibbsLearning
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# One-step gradient descent for vector Gibbs objectives

A nonzero gradient yields a strict one-step decrease along `-grad`.
-/

namespace NeuralNetwork
namespace BoltzmannLearningQuiver
namespace VectorGibbs

open scoped Topology
open InnerProductSpace Filter Asymptotics

variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
variable {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]

omit [DecidableEq X] in
/-- Strict descent step along a nonzero gradient. -/
theorem negLogLik_descent_step (stat : X → Θ) (x : X) (θ : Θ) (grad : Θ)
    (hgrad : HasGradientAt (fun θ' => negLogLik stat x θ') grad θ) (hgrad_ne : grad ≠ 0) :
    ∃ (η : ℝ), 0 < η ∧ negLogLik stat x (θ - η • grad) < negLogLik stat x θ := by
  set f : Θ → ℝ := fun θ' => negLogLik stat x θ'
  have hnorm_pos : 0 < ‖grad‖ := norm_pos_iff.mpr hgrad_ne
  have hsq_pos : 0 < ⟪grad, grad⟫_ℝ := by
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℝ) (E := Θ)]
    exact pow_pos hnorm_pos 2
  have ho : (fun h => f (θ + h) - f θ - ⟪grad, h⟫_ℝ) =o[𝓝 0] (fun h => h) :=
    (hasGradientAt_iff_isLittleO_nhds_zero (𝕜 := ℝ) (F := Θ)).1 hgrad
  set c := ⟪grad, grad⟫_ℝ / (2 * ‖grad‖)
  have hc_pos : 0 < c := div_pos hsq_pos (mul_pos (by norm_num) hnorm_pos)
  obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff.mp (IsLittleO.def ho hc_pos)
  set η := δ / (2 * ‖grad‖)
  have hηpos : 0 < η := div_pos hδpos (mul_pos (by norm_num) hnorm_pos)
  have hη_norm : η * ‖grad‖ < δ := by
    calc
      η * ‖grad‖ = (δ / (2 * ‖grad‖)) * ‖grad‖ := by simp [η]
      _ = δ / 2 := by field_simp [hgrad_ne]
      _ < δ := half_lt_self hδpos
  have hnorm : ‖(-η • grad)‖ = η * ‖grad‖ := by
    simp [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hηpos]
  have ho_bound :
      ‖f (θ - η • grad) - f θ - ⟪grad, -η • grad⟫_ℝ‖ ≤ c * ‖(-η • grad)‖ := by
    have hdist : dist (-η • grad) 0 < δ := by
      rw [dist_eq_norm, sub_zero, hnorm]
      exact hη_norm
    simpa [sub_eq_add_neg] using hδ hdist
  have hinner : ⟪grad, -η • grad⟫_ℝ = -η * ⟪grad, grad⟫_ℝ := by
    simp [inner_neg_right, inner_smul_right]
  have hf_diff :
      f (θ - η • grad) - f θ =
        (f (θ - η • grad) - f θ - ⟪grad, -η • grad⟫_ℝ) - η * ⟪grad, grad⟫_ℝ := by
    rw [hinner]; ring
  have hc_eq : c * (η * ‖grad‖) = η * ⟪grad, grad⟫_ℝ / 2 := by
    simp [c, inner_self_eq_norm_sq_to_K (𝕜 := ℝ) (E := Θ)]
    field_simp [hgrad_ne]
  have hdecrease : f (θ - η • grad) - f θ ≤ -η * ⟪grad, grad⟫_ℝ / 2 := by
    rw [hf_diff]
    have herr_le := le_trans (le_abs_self _) ho_bound
    rw [hnorm] at herr_le
    linarith [hc_eq]
  have hlt : -η * ⟪grad, grad⟫_ℝ / 2 < 0 := by
    have : 0 < η * ⟪grad, grad⟫_ℝ / 2 := div_pos (mul_pos hηpos hsq_pos) (by norm_num)
    linarith
  exact ⟨η, hηpos, by simpa [f] using lt_of_le_of_lt hdecrease hlt⟩

omit [DecidableEq X] in
/-- Descent along the NLL gradient from `hasGradientAt_negLogLik`. -/
theorem negLogLik_descent_step_gradient (stat : X → Θ) (x : X) (θ : Θ)
    (hne : stat x ≠ expectation stat θ) :
    ∃ (η : ℝ), 0 < η ∧
      negLogLik stat x (θ - η • (stat x - expectation stat θ)) < negLogLik stat x θ :=
  negLogLik_descent_step stat x θ (stat x - expectation stat θ)
    (hasGradientAt_negLogLik stat x θ) (sub_ne_zero.mpr hne)

end VectorGibbs
end BoltzmannLearningQuiver
end NeuralNetwork

#lint only docBlame docBlameThm
