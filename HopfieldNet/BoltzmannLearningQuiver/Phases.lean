/-
Copyright (c) 2025 HNBM contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.BoltzmannLearningQuiver.Stat
import HopfieldNet.Quiver.NeuralNetwork.toCanonicalEnsemble
import Physlib.StatisticalMechanics.CanonicalEnsemble.Finite
import Physlib.Thermodynamics.Temperature.Basic

/-!
# Positive and negative BM learning phases

Negative phase = canonical Boltzmann measure; positive phase = Dirac at data.
-/

namespace NeuralNetwork
namespace BoltzmannLearningQuiver
namespace ZeroOne

open scoped BigOperators Temperature CanonicalEnsemble
open MeasureTheory ProbabilityTheory CanonicalEnsemble HopfieldBoltzmann BoltzmannLearningQuiver.BM

variable {U : Type} [Fintype U] [DecidableEq U] [Nonempty U]

/-- Finiteness instance for the canonical ensemble at `p`. -/
lemma instCEparamsIsFinite (p : Params ℝ U) :
    (CEparams (NN := NN ℝ U) (spec := energySpec) p).IsFinite := by
  dsimp [CEparams, HopfieldBoltzmann.CEparams]
  infer_instance

/-- Boltzmann probability `P_{p,T}(s)`. -/
noncomputable def modelProbability (T : Temperature) (p : Params ℝ U) (s : State ℝ U) : ℝ :=
  HopfieldBoltzmann.P (NN := NN ℝ U) (spec := energySpec) p T s

/-- Boltzmann probabilities are nonnegative. -/
lemma modelProbability_nonneg (T : Temperature) (p : Params ℝ U) (s : State ℝ U) :
    0 ≤ modelProbability T p s := by
  haveI := instCEparamsIsFinite p
  simpa [modelProbability, CEparams, hopfieldCE, toCanonicalEnsemble, energy_eq_spec, energySpec,
    HopfieldEnergy.zeroOneEnergySpec] using
    probability_nonneg_finite (𝓒 := CEparams (NN := NN ℝ U) energySpec p) T s

/-- Boltzmann probabilities sum to one. -/
lemma modelProbability_sum_one (T : Temperature) (p : Params ℝ U) :
    ∑ s : State ℝ U, modelProbability T p s = 1 := by
  haveI := instCEparamsIsFinite p
  simpa [modelProbability, CEparams, hopfieldCE, toCanonicalEnsemble, energy_eq_spec, energySpec,
    HopfieldEnergy.zeroOneEnergySpec] using
    sum_probability_eq_one (𝓒 := CEparams (NN := NN ℝ U) energySpec p) T

/-- Negative phase: canonical Boltzmann measure at `(p, T)`. -/
noncomputable def negativePhaseMeasure (T : Temperature) (p : Params ℝ U) : Measure (State ℝ U) :=
  (CEparams (NN := NN ℝ U) (spec := energySpec) p).μProd T

/-- Positive phase: Dirac at clamped data. -/
noncomputable def positivePhaseAtData (s_data : State ℝ U) : Measure (State ℝ U) :=
  Measure.dirac s_data

/-- Vector statistic expectation `E_μ[stat]`. -/
noncomputable def expectationStat (μ : Measure (State ℝ U)) : Θ U :=
  WithLp.toLp 2 fun i => BM.expectation μ (statCoord i)

/-- Model statistic under Boltzmann equilibrium. -/
noncomputable def modelExpectationStat (T : Temperature) (p : Params ℝ U) : Θ U :=
  expectationStat (negativePhaseMeasure T p)

/-- Exact BM learning direction. -/
noncomputable def learningDirection (T : Temperature) (p : Params ℝ U) (s_data : State ℝ U) : Θ U :=
  stat s_data - modelExpectationStat T p

/-- Expectation under Dirac positive phase at coordinate `i`. -/
lemma expectationStat_dirac (s_data : State ℝ U) (i : I U) :
    BM.expectation (positivePhaseAtData s_data) (statCoord i) = statCoord i s_data := by
  simp [BM.expectation, positivePhaseAtData, statCoord]

/-- Vector expectation under Dirac positive phase. -/
lemma expectationStat_pos_dirac (s_data : State ℝ U) :
    expectationStat (positivePhaseAtData s_data) = stat s_data := by
  ext i
  simp [expectationStat, statCoord, expectationStat_dirac]

/-- Contrastive update from phase measures. -/
noncomputable def exactLearningDirection (T : Temperature) (p : Params ℝ U) (s_data : State ℝ U) : Θ U :=
  expectationStat (positivePhaseAtData s_data) - expectationStat (negativePhaseMeasure T p)

/-- Dirac positive phase yields `learningDirection`. -/
theorem exactLearningDirection_eq_learningDirection (T : Temperature) (p : Params ℝ U) (s_data : State ℝ U) :
    exactLearningDirection T p s_data = learningDirection T p s_data := by
  simp [exactLearningDirection, learningDirection, modelExpectationStat, expectationStat_pos_dirac]

end ZeroOne
end BoltzmannLearningQuiver
end NeuralNetwork

#lint only docBlame docBlameThm
