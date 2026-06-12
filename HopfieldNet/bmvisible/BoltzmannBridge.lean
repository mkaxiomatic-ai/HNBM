/-
Copyright (c) 2025 HNBM contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.bmvisible.Bridge
import HopfieldNet.bmvisible.Energy
import HopfieldNet.bmvisible.Phases
import HopfieldNet.Quiver.NeuralNetwork.toCanonicalEnsemble
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.StatisticalMechanics.CanonicalEnsemble.Finite

/-!
# Bridge: `VectorGibbs` ↔ visible/hidden canonical ensemble
-/

namespace BMVisible

open NeuralNetwork MeasureTheory ProbabilityTheory BoltzmannLearningQuiver ZeroOne VectorGibbs
open scoped BigOperators Temperature CanonicalEnsemble
open CanonicalEnsemble Finset InnerProductSpace Matrix TwoState HopfieldEnergy HopfieldBoltzmann BM

variable {U : Type} [Fintype U] [DecidableEq U] [Nonempty U]
variable (part : VisibleHiddenPartition U)

/-- `VectorGibbs` expectation of `bmStat` at scaled parameters. -/
noncomputable def vectorGibbsExpectationStat (T : Temperature) (p : BMParams ℝ U part) : Θ U :=
  VectorGibbs.expectation (X := BMState ℝ U part) (Θ := Θ U) (stat := bmStat part)
    (bmScaledTheta part T p)

/-- Explicit Boltzmann expectation `∑_s P(s) • stat(s)`. -/
noncomputable def boltzmannExpectationStat (T : Temperature) (p : BMParams ℝ U part) : Θ U :=
  ∑ s : BMState ℝ U part, modelProbability part T p s • bmStat part s

theorem vectorGibbs_weight_eq_boltzmannFactor (T : Temperature) (p : BMParams ℝ U part)
    (s : BMState ℝ U part) :
    VectorGibbs.weight (X := BMState ℝ U part) (Θ := Θ U) (stat := bmStat part)
      (bmScaledTheta part T p) s =
      Real.exp (-(T.β : ℝ) * hamiltonian part p s) := by
  simp [VectorGibbs.weight, VectorGibbs.energy, inner_stat_scaledTheta, neg_mul]

lemma boltzmannPartitionFunction_eq_sum (T : Temperature) (p : BMParams ℝ U part) :
    (CEparams (NN := NN ℝ U part) (spec := energySpec part) p).mathematicalPartitionFunction T =
      ∑ s : BMState ℝ U part, Real.exp (-(T.β : ℝ) * hamiltonian part p s) := by
  haveI := instCEparamsIsFinite part p
  rw [mathematicalPartitionFunction_of_fintype (𝓒 := CEparams (NN := NN ℝ U part) (spec := energySpec part) p) T]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [CEparams_energy_eq_hamiltonian, neg_mul]

theorem vectorGibbs_Z_eq_boltzmannPartitionFunction (T : Temperature) (p : BMParams ℝ U part) :
    VectorGibbs.Z (X := BMState ℝ U part) (Θ := Θ U) (stat := bmStat part) (bmScaledTheta part T p) =
      (CEparams (NN := NN ℝ U part) (spec := energySpec part) p).mathematicalPartitionFunction T := by
  simp [VectorGibbs.Z, boltzmannPartitionFunction_eq_sum, vectorGibbs_weight_eq_boltzmannFactor,
    neg_mul]

theorem modelProbability_eq_boltzmannFactor_div_Z (T : Temperature) (p : BMParams ℝ U part)
    (s : BMState ℝ U part) :
    modelProbability part T p s =
      Real.exp (-(T.β : ℝ) * hamiltonian part p s) /
        (CEparams (NN := NN ℝ U part) (spec := energySpec part) p).mathematicalPartitionFunction T := by
  simp [modelProbability, P, CEparams, CanonicalEnsemble.probability, hopfieldCE,
    toCanonicalEnsemble, energy_eq_spec, energySpec, HopfieldEnergy.zeroOneEnergySpec]

theorem vectorGibbs_weight_eq_modelProbability_mul_Z (T : Temperature) (p : BMParams ℝ U part)
    (s : BMState ℝ U part) :
    VectorGibbs.weight (X := BMState ℝ U part) (Θ := Θ U) (stat := bmStat part)
      (bmScaledTheta part T p) s =
      modelProbability part T p s *
        (CEparams (NN := NN ℝ U part) (spec := energySpec part) p).mathematicalPartitionFunction T := by
  haveI := instCEparamsIsFinite part p
  have hZpos :=
    mathematicalPartitionFunction_pos_finite (𝓒 := CEparams (NN := NN ℝ U part) (spec := energySpec part) p) T
  rw [vectorGibbs_weight_eq_boltzmannFactor, modelProbability_eq_boltzmannFactor_div_Z]
  field_simp [hZpos.ne']

lemma num_eq_Z_smul_boltzmannExpectationStat (T : Temperature) (p : BMParams ℝ U part) :
    VectorGibbs.num (X := BMState ℝ U part) (Θ := Θ U) (stat := bmStat part)
      (bmScaledTheta part T p) =
      (CEparams (NN := NN ℝ U part) (spec := energySpec part) p).mathematicalPartitionFunction T •
        boltzmannExpectationStat part T p := by
  set Z := (CEparams (NN := NN ℝ U part) (spec := energySpec part) p).mathematicalPartitionFunction T
  have hsum :
      Z • ∑ s, modelProbability part T p s • bmStat part s =
        ∑ s, Z • (modelProbability part T p s • bmStat part s) :=
    Finset.smul_sum (r := Z) (f := fun s => modelProbability part T p s • bmStat part s)
  rw [VectorGibbs.num]
  rw [show Z • boltzmannExpectationStat part T p = Z • ∑ s, modelProbability part T p s • bmStat part s from rfl, hsum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [vectorGibbs_weight_eq_modelProbability_mul_Z part T p s]
  rw [mul_comm (modelProbability part T p s) Z, mul_smul Z (modelProbability part T p s) (bmStat part s)]

theorem vectorGibbsExpectationStat_eq_boltzmannExpectationStat (T : Temperature) (p : BMParams ℝ U part) :
    vectorGibbsExpectationStat part T p = boltzmannExpectationStat part T p := by
  have hZ := vectorGibbs_Z_eq_boltzmannPartitionFunction part T p
  haveI := instCEparamsIsFinite part p
  have hZne :=
    (mathematicalPartitionFunction_pos_finite (𝓒 := CEparams (NN := NN ℝ U part) (spec := energySpec part) p) T).ne'
  set Z := (CEparams (NN := NN ℝ U part) (spec := energySpec part) p).mathematicalPartitionFunction T
  calc
    vectorGibbsExpectationStat part T p
        = (VectorGibbs.Z (bmStat part) (bmScaledTheta part T p))⁻¹ •
            VectorGibbs.num (bmStat part) (bmScaledTheta part T p) := by
      simp [vectorGibbsExpectationStat, VectorGibbs.expectation]
    _ = Z⁻¹ • (Z • boltzmannExpectationStat part T p) := by rw [hZ, num_eq_Z_smul_boltzmannExpectationStat]
    _ = boltzmannExpectationStat part T p := inv_smul_smul₀ hZne _

theorem modelExpectationStat_eq_boltzmannExpectationStat (T : Temperature) (p : BMParams ℝ U part) :
    modelExpectationStat part T p = boltzmannExpectationStat part T p := by
  ext i
  simp only [modelExpectationStat, expectationStat, boltzmannExpectationStat, WithLp.ofLp_toLp,
    BM.expectation, negativePhaseMeasure, bmStatCoord]
  haveI := instCEparamsIsFinite part p
  have hZne :=
    (mathematicalPartitionFunction_pos_finite (𝓒 := CEparams (NN := NN ℝ U part) (spec := energySpec part) p) T).ne'
  rw [MeasureTheory.integral_fintype]
  · rw [show (∑ s, modelProbability part T p s • bmStat part s).ofLp i =
        ∑ s, modelProbability part T p s * (bmStat part s).ofLp i from by
      simp [WithLp.ofLp_sum, smul_eq_mul]]
    refine Finset.sum_congr rfl fun s _ => ?_
    have hcoord : statCoord i (toZeroOneState part s) = (bmStat part s).ofLp i := by
      simp [bmStatCoord, bmStat, statCoord, stat, WithLp.ofLp_toLp]
    rw [μProd_of_fintype (𝓒 := CEparams (NN := NN ℝ U part) (spec := energySpec part) p) T s, hcoord]
    simp only [modelProbability, P, CEparams, CanonicalEnsemble.probability, hopfieldCE,
      toCanonicalEnsemble, energy_eq_spec, energySpec]
    ring
  · exact MeasureTheory.Integrable.of_finite

theorem vectorGibbsExpectationStat_eq_modelExpectationStat (T : Temperature) (p : BMParams ℝ U part) :
    vectorGibbsExpectationStat part T p = modelExpectationStat part T p := by
  rw [vectorGibbsExpectationStat_eq_boltzmannExpectationStat,
    modelExpectationStat_eq_boltzmannExpectationStat]

end BMVisible

#lint only docBlame
