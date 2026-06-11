/-
Copyright (c) 2025 HNBM contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.BoltzmannLearningQuiver.Phases
import HopfieldNet.BoltzmannLearningQuiver.Energy
import HopfieldNet.Quiver.NeuralNetwork.toCanonicalEnsemble
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.StatisticalMechanics.CanonicalEnsemble.Finite

/-!
# Bridge: `VectorGibbs` ↔ quiver canonical ensemble

`VectorGibbs.weight stat (scaledTheta T p) s` agrees with Boltzmann factor `exp(-β H_p(s))`.
-/

namespace NeuralNetwork
namespace BoltzmannLearningQuiver
namespace SymmetricBinary

open scoped BigOperators Temperature CanonicalEnsemble
open CanonicalEnsemble Finset VectorGibbs InnerProductSpace Matrix TwoState HopfieldEnergy HopfieldBoltzmann
  BoltzmannLearningQuiver.BM

variable {U : Type} [Fintype U] [DecidableEq U] [Nonempty U]

/-- Temperature-aware model statistic at `scaledTheta T p`. -/
noncomputable def vectorGibbsExpectationStat (T : Temperature) (p : Params ℝ U) : Θ U :=
  VectorGibbs.expectation (X := State ℝ U) (Θ := Θ U) stat (scaledTheta T p)

/-- Explicit Boltzmann sum expectation of `stat`. -/
noncomputable def boltzmannExpectationStat (T : Temperature) (p : Params ℝ U) : Θ U :=
  ∑ s : State ℝ U, modelProbability T p s • stat s

/-- Hamiltonian equals negative inner product with `thetaFromParams p`. -/
lemma hamiltonian_eq_neg_inner (p : Params ℝ U) (s : State ℝ U) :
    hamiltonian p s = - inner ℝ (stat s) (thetaFromParams p) := by
  rw [← vectorGibbsEnergy_eq_hamiltonian, vectorGibbsEnergy_eq_neg_inner]

/-- Inner product with `scaledTheta T p` equals `β H_p(s)`. -/
lemma inner_stat_scaledTheta (T : Temperature) (p : Params ℝ U) (s : State ℝ U) :
    inner ℝ (stat s) (scaledTheta T p) = (T.β : ℝ) * hamiltonian p s := by
  simp [scaledTheta, inner_smul_right, hamiltonian_eq_neg_inner]

/-- `VectorGibbs` weight equals the Boltzmann factor. -/
theorem vectorGibbs_weight_eq_boltzmannFactor (T : Temperature) (p : Params ℝ U) (s : State ℝ U) :
    VectorGibbs.weight (X := State ℝ U) (Θ := Θ U) stat (scaledTheta T p) s =
      Real.exp (-(T.β : ℝ) * hamiltonian p s) := by
  simp [VectorGibbs.weight, VectorGibbs.energy, inner_stat_scaledTheta, neg_mul]

/-- Canonical ensemble energy equals `hamiltonian`. -/
lemma CEparams_energy_eq_hamiltonian (p : Params ℝ U) (s : State ℝ U) :
    (CEparams (NN := NN ℝ U) (spec := energySpec) p).energy s = hamiltonian p s := by
  have _ : IsHamiltonian (NN := NN ℝ U) := IsHamiltonian_of_EnergySpec' energySpec
  simp [CEparams, hopfieldCE, toCanonicalEnsemble, energy_eq_spec, energySpec,
    HopfieldEnergy.symmetricBinaryEnergySpec]

/-- Partition function equals sum of Boltzmann factors. -/
lemma boltzmannPartitionFunction_eq_sum (T : Temperature) (p : Params ℝ U) :
    (CEparams (NN := NN ℝ U) (spec := energySpec) p).mathematicalPartitionFunction T =
      ∑ s : State ℝ U, Real.exp (-(T.β : ℝ) * hamiltonian p s) := by
  haveI := instCEparamsIsFinite p
  rw [mathematicalPartitionFunction_of_fintype (𝓒 := CEparams (NN := NN ℝ U) energySpec p) T]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [CEparams_energy_eq_hamiltonian, neg_mul]

/-- `VectorGibbs.Z` equals the Boltzmann partition function. -/
theorem vectorGibbs_Z_eq_boltzmannPartitionFunction (T : Temperature) (p : Params ℝ U) :
    VectorGibbs.Z (X := State ℝ U) (Θ := Θ U) stat (scaledTheta T p) =
      (CEparams (NN := NN ℝ U) (spec := energySpec) p).mathematicalPartitionFunction T := by
  simp [VectorGibbs.Z, boltzmannPartitionFunction_eq_sum, vectorGibbs_weight_eq_boltzmannFactor,
    neg_mul]

/-- `modelProbability` equals Boltzmann factor divided by `Z`. -/
theorem modelProbability_eq_boltzmannFactor_div_Z (T : Temperature) (p : Params ℝ U) (s : State ℝ U) :
    modelProbability T p s =
      Real.exp (-(T.β : ℝ) * hamiltonian p s) /
        (CEparams (NN := NN ℝ U) (spec := energySpec) p).mathematicalPartitionFunction T := by
  simp [modelProbability, P, CEparams, CanonicalEnsemble.probability, hopfieldCE,
    toCanonicalEnsemble, energy_eq_spec, energySpec, HopfieldEnergy.symmetricBinaryEnergySpec]

/-- Unnormalized `VectorGibbs` weight equals `modelProbability` times `Z`. -/
theorem vectorGibbs_weight_eq_modelProbability_mul_Z (T : Temperature) (p : Params ℝ U) (s : State ℝ U) :
    VectorGibbs.weight (X := State ℝ U) (Θ := Θ U) stat (scaledTheta T p) s =
      modelProbability T p s *
        (CEparams (NN := NN ℝ U) (spec := energySpec) p).mathematicalPartitionFunction T := by
  haveI := instCEparamsIsFinite p
  have hZpos :=
    mathematicalPartitionFunction_pos_finite (𝓒 := CEparams (NN := NN ℝ U) energySpec p) T
  rw [vectorGibbs_weight_eq_boltzmannFactor, modelProbability_eq_boltzmannFactor_div_Z]
  field_simp [hZpos.ne']

/-- `VectorGibbs.num` equals `Z • boltzmannExpectationStat`. -/
lemma num_eq_Z_smul_boltzmannExpectationStat (T : Temperature) (p : Params ℝ U) :
    VectorGibbs.num (X := State ℝ U) (Θ := Θ U) stat (scaledTheta T p) =
      (CEparams (NN := NN ℝ U) (spec := energySpec) p).mathematicalPartitionFunction T •
        boltzmannExpectationStat T p := by
  set Z := (CEparams (NN := NN ℝ U) (spec := energySpec) p).mathematicalPartitionFunction T
  have hsum :
      Z • ∑ s, modelProbability T p s • stat s =
        ∑ s, Z • (modelProbability T p s • stat s) :=
    Finset.smul_sum (r := Z) (f := fun s => modelProbability T p s • stat s)
  rw [VectorGibbs.num]
  rw [show Z • boltzmannExpectationStat T p = Z • ∑ s, modelProbability T p s • stat s from rfl, hsum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [vectorGibbs_weight_eq_modelProbability_mul_Z T p s]
  rw [mul_comm (modelProbability T p s) Z, mul_smul Z (modelProbability T p s) (stat s)]

/-- `VectorGibbs` expectation equals the explicit Boltzmann sum. -/
theorem vectorGibbsExpectationStat_eq_boltzmannExpectationStat (T : Temperature) (p : Params ℝ U) :
    vectorGibbsExpectationStat T p = boltzmannExpectationStat T p := by
  have hZ := vectorGibbs_Z_eq_boltzmannPartitionFunction T p
  haveI := instCEparamsIsFinite p
  have hZne :=
    (mathematicalPartitionFunction_pos_finite (𝓒 := CEparams (NN := NN ℝ U) energySpec p) T).ne'
  set Z := (CEparams (NN := NN ℝ U) (spec := energySpec) p).mathematicalPartitionFunction T
  calc
    vectorGibbsExpectationStat T p
        = (VectorGibbs.Z stat (scaledTheta T p))⁻¹ • VectorGibbs.num stat (scaledTheta T p) := by
      simp [vectorGibbsExpectationStat, VectorGibbs.expectation]
    _ = Z⁻¹ • (Z • boltzmannExpectationStat T p) := by rw [hZ, num_eq_Z_smul_boltzmannExpectationStat]
    _ = boltzmannExpectationStat T p := inv_smul_smul₀ hZne _

/-- Quiver negative-phase statistic equals the explicit Boltzmann sum. -/
theorem modelExpectationStat_eq_boltzmannExpectationStat (T : Temperature) (p : Params ℝ U) :
    modelExpectationStat T p = boltzmannExpectationStat T p := by
  ext i
  simp [modelExpectationStat, expectationStat, WithLp.ofLp_toLp, boltzmannExpectationStat,
    BM.expectation, negativePhaseMeasure, statCoord]
  haveI := instCEparamsIsFinite p
  rw [MeasureTheory.integral_fintype]
  · congr 1; ext s
    rw [μProd_of_fintype (𝓒 := CEparams (NN := NN ℝ U) energySpec p) T s]
    simp [modelProbability, P, CEparams, CanonicalEnsemble.probability, hopfieldCE,
      toCanonicalEnsemble, energy_eq_spec, energySpec, HopfieldEnergy.symmetricBinaryEnergySpec]
  · exact MeasureTheory.Integrable.of_finite

/-- `VectorGibbs` expectation equals `modelExpectationStat`. -/
theorem vectorGibbsExpectationStat_eq_modelExpectationStat (T : Temperature) (p : Params ℝ U) :
    vectorGibbsExpectationStat T p = modelExpectationStat T p := by
  rw [vectorGibbsExpectationStat_eq_boltzmannExpectationStat,
    modelExpectationStat_eq_boltzmannExpectationStat]

end SymmetricBinary
end BoltzmannLearningQuiver
end NeuralNetwork

#lint only docBlame docBlameThm
