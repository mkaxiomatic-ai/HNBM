/-
Copyright (c) 2025 HNBM contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.bmvisible.Phases
import HopfieldNet.bmvisible.Dynamics

/-!
# Contrastive divergence (CD-k) for visible/hidden BMs

**Positive phase:** `k` hidden-only Gibbs sweeps with visible clamped (`positiveCdPMF`).

**Negative phase:** `k` full-network Gibbs sweeps from start state `s₀` (`cdNegativePMF`).
-/

namespace BMVisible

open MeasureTheory TwoState NeuralNetwork.BoltzmannLearningQuiver ZeroOne

variable {U : Type} [Fintype U] [DecidableEq U] [Nonempty U]
variable (part : VisibleHiddenPartition U)

/-- One full-network CD step on the negative phase chain. -/
noncomputable def cdStepPMF (order : List U) (p : BMParams ℝ U part) (T : Temperature)
    (μ : PMF (BMState ℝ U part)) : PMF (BMState ℝ U part) :=
  μ.bind fun s => gibbsSweep part order p T s

/-- CD-$k$ negative-phase distribution from start state `s₀`. -/
noncomputable def cdNegativePMF (k : ℕ) (order : List U) (p : BMParams ℝ U part) (T : Temperature)
    (s₀ : BMState ℝ U part) : PMF (BMState ℝ U part) :=
  Nat.rec (PMF.pure s₀) (fun _ μ => cdStepPMF part order p T μ) k

/-- CD-$k$ negative phase as a measure. -/
noncomputable def cdNegativePhaseMeasure (k : ℕ) (order : List U) (p : BMParams ℝ U part)
    (T : Temperature) (s₀ : BMState ℝ U part) : Measure (BMState ℝ U part) :=
  (cdNegativePMF part k order p T s₀).toMeasure

/-- CD-$k$ learning direction (visible clamped exactly; `k` full-network negative sweeps). -/
noncomputable def cdLearningDirection (k : ℕ) (order : List U) (T : Temperature) (p : BMParams ℝ U part)
    (vp : VisiblePattern (R := ℝ) part) : Θ U :=
  learningRule part |>.updateDir (Measure.dirac (dataState part vp))
    (cdNegativePhaseMeasure part k order p T (dataState part vp))

/-- CD-$k$ with both phases run for `k` steps (paper hidden positive + full negative). -/
noncomputable def cdLearningDirection_full (k : ℕ) (order : List U) (T : Temperature) (p : BMParams ℝ U part)
    (vp : VisiblePattern (R := ℝ) part) : Θ U :=
  learningRule part |>.updateDir (positivePhaseMeasure part k order p T vp)
    (cdNegativePhaseMeasure part k order p T (dataState part vp))

/-- CD-$k$ update using equilibrium negative phase (alternative formulation). -/
noncomputable def cdUpdateDirEquilibrium (k : ℕ) (order : List U) (T : Temperature) (p : BMParams ℝ U part)
    (vp : VisiblePattern (R := ℝ) part) : Θ U :=
  learningRule part |>.updateDir (positivePhaseMeasure part k order p T vp)
    (negativePhaseMeasure part p T)

end BMVisible

#lint only docBlame
