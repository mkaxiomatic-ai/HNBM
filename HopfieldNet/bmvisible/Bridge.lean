/-
Copyright (c) 2025 HNBM contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.bmvisible.Dynamics
import HopfieldNet.BoltzmannLearningQuiver.Stat
import HopfieldNet.BoltzmannLearningQuiver.Phases
import HopfieldNet.Quiver.NeuralNetwork.toCanonicalEnsemble
import Physlib.StatisticalMechanics.CanonicalEnsemble.Finite
import Physlib.Thermodynamics.Temperature.Basic

/-!
# Bridge: visible/hidden BM ↔ fully visible `{0,1}` stack

Statistics and canonical ensemble data agree with `BoltzmannLearningQuiver.ZeroOne` after
coercion along `toZeroOneState` / `toZeroOneParams`.
-/

namespace BMVisible

open NeuralNetwork MeasureTheory ProbabilityTheory BoltzmannLearningQuiver
open scoped Temperature CanonicalEnsemble BigOperators
open HopfieldBoltzmann CanonicalEnsemble HopfieldEnergy

variable {U : Type} [Fintype U] [DecidableEq U] [Nonempty U]
variable (part : VisibleHiddenPartition U)

/-- Sufficient statistic on visible/hidden states. -/
noncomputable def bmStat (s : BMState ℝ U part) : ZeroOne.Θ U :=
  ZeroOne.stat (toZeroOneState part s)

/-- Parameter embedding on visible/hidden params. -/
noncomputable def bmThetaFromParams (p : BMParams ℝ U part) : ZeroOne.Θ U :=
  ZeroOne.thetaFromParams (toZeroOneParams part p)

/-- Temperature-scaled parameter vector. -/
noncomputable def bmScaledTheta (T : Temperature) (p : BMParams ℝ U part) : ZeroOne.Θ U :=
  ZeroOne.scaledTheta T (toZeroOneParams part p)

/-- Finiteness instance for the canonical ensemble at `p`. -/
lemma instCEparamsIsFinite (p : BMParams ℝ U part) :
    (CEparams (NN := NN ℝ U part) (spec := energySpec part) p).IsFinite := by
  dsimp [CEparams, HopfieldBoltzmann.CEparams]
  infer_instance

/-- Boltzmann probability `P_{p,T}(s)`. -/
noncomputable def modelProbability (T : Temperature) (p : BMParams ℝ U part)
    (s : BMState ℝ U part) : ℝ :=
  HopfieldBoltzmann.P (NN := NN ℝ U part) (spec := energySpec part) p T s

/-- Canonical ensemble energy equals `hamiltonian`. -/
lemma CEparams_energy_eq_hamiltonian (p : BMParams ℝ U part) (s : BMState ℝ U part) :
    (CEparams (NN := NN ℝ U part) (spec := energySpec part) p).energy s = hamiltonian part p s := by
  have _ : IsHamiltonian (NN := NN ℝ U part) := IsHamiltonian_of_EnergySpec' (energySpec part)
  simp [CEparams, hopfieldCE, toCanonicalEnsemble, energy_eq_spec, energySpec]

/-- Boltzmann probabilities are nonnegative. -/
lemma modelProbability_nonneg (T : Temperature) (p : BMParams ℝ U part) (s : BMState ℝ U part) :
    0 ≤ modelProbability part T p s := by
  haveI := instCEparamsIsFinite part p
  simpa [modelProbability, CEparams, hopfieldCE, toCanonicalEnsemble, energy_eq_spec, energySpec,
    HopfieldEnergy.zeroOneEnergySpec] using
    probability_nonneg_finite (𝓒 := CEparams (NN := NN ℝ U part) (energySpec part) p) T s

/-- Boltzmann probabilities sum to one. -/
lemma modelProbability_sum_one (T : Temperature) (p : BMParams ℝ U part) :
    ∑ s : BMState ℝ U part, modelProbability part T p s = 1 := by
  haveI := instCEparamsIsFinite part p
  simpa [modelProbability, CEparams, hopfieldCE, toCanonicalEnsemble, energy_eq_spec, energySpec,
    HopfieldEnergy.zeroOneEnergySpec] using
    sum_probability_eq_one (𝓒 := CEparams (NN := NN ℝ U part) (energySpec part) p) T

/-- Coerced statistic vector. -/
lemma bmStat_eq_stat_toZeroOne (s : BMState ℝ U part) :
    bmStat part s = ZeroOne.stat (toZeroOneState part s) := rfl

/-- Coerced parameter embedding. -/
lemma bmThetaFromParams_eq (p : BMParams ℝ U part) :
    bmThetaFromParams part p = ZeroOne.thetaFromParams (toZeroOneParams part p) := rfl

end BMVisible

#lint only docBlame
