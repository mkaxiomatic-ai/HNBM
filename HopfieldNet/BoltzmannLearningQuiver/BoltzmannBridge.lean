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
## Bridge: VectorGibbs expectations ↔ Quiver canonical ensemble at temperature `T`

### Convention summary

| Object | Weight / density on state `s` |
|--------|-------------------------------|
| `VectorGibbs.weight stat θ s` | `exp (-⟪stat s, θ⟫)` |
| `HopfieldBoltzmann.P p T s` | `exp (-β(T) · hamiltonian p s) / Z` |

We proved `hamiltonian p s = -⟪stat s, thetaFromParams p⟫` (`Energy.lean`).

So the **same Boltzmann measure** appears in `VectorGibbs` with the **scaled parameter**

`scaledTheta T p := -(β(T) : ℝ) • thetaFromParams p`,

because
`-⟪stat s, scaledTheta T p⟫ = β(T) · hamiltonian p s`.

The current `Phases.modelExpectationStat` ignores `T`; the temperature-correct statistic is
`vectorGibbsExpectationStat T p` below.
-/

namespace NeuralNetwork

namespace BoltzmannLearningQuiver

namespace SymmetricBinary

open scoped BigOperators Temperature CanonicalEnsemble
open CanonicalEnsemble Finset
open ThreeD.BoltzmannLearning VectorGibbs
open InnerProductSpace Matrix TwoState HopfieldEnergy HopfieldBoltzmann

variable {U : Type} [Fintype U] [DecidableEq U] [Nonempty U]

/-- Parameter vector at inverse temperature `β(T)`: makes `VectorGibbs` weights match `exp (-β H)`. -/
noncomputable def scaledTheta (T : Temperature) (p : Params ℝ U) : Θ U :=
  (-(T.β : ℝ)) • thetaFromParams p

/-- Temperature-aware model statistic (negative phase at `(p, T)`). -/
noncomputable def vectorGibbsExpectationStat (T : Temperature) (p : Params ℝ U) : Θ U :=
  expectation (X := State ℝ U) (Θ := Θ U) stat (scaledTheta T p)

/-- Expectation `E_{s ∼ P(·|p,T)}[stat s]` from the Quiver Boltzmann probabilities. -/
noncomputable def boltzmannExpectationStat (T : Temperature) (p : Params ℝ U) : Θ U :=
  ∑ s : State ℝ U, modelProbability T p s • stat s

lemma hamiltonian_eq_neg_inner (p : Params ℝ U) (s : State ℝ U) :
    hamiltonian p s = - inner ℝ (stat s) (thetaFromParams p) := by
  rw [← vectorGibbsEnergy_eq_hamiltonian, vectorGibbsEnergy_eq_neg_inner]

lemma inner_stat_scaledTheta (T : Temperature) (p : Params ℝ U) (s : State ℝ U) :
    inner ℝ (stat s) (scaledTheta T p) = (T.β : ℝ) * hamiltonian p s := by
  simp [scaledTheta, inner_smul_right, hamiltonian_eq_neg_inner]

/-- `VectorGibbs` unnormalized weight at `scaledTheta T p` equals the canonical Boltzmann factor. -/
theorem vectorGibbs_weight_eq_boltzmannFactor (T : Temperature) (p : Params ℝ U) (s : State ℝ U) :
    VectorGibbs.weight (X := State ℝ U) (Θ := Θ U) stat (scaledTheta T p) s =
      Real.exp (-(T.β : ℝ) * hamiltonian p s) := by
  simp [VectorGibbs.weight, VectorGibbs.energy, inner_stat_scaledTheta, neg_mul]

private lemma instIsFinite (p : Params ℝ U) :
    (CEparams (NN := NN ℝ U) (spec := energySpec) p).IsFinite := by
  dsimp [CEparams, HopfieldBoltzmann.CEparams]
  infer_instance

lemma CEparams_energy_eq_hamiltonian (p : Params ℝ U) (s : State ℝ U) :
    (CEparams (NN := NN ℝ U) (spec := energySpec) p).energy s = hamiltonian p s := by
  have _ : IsHamiltonian (NN := NN ℝ U) := IsHamiltonian_of_EnergySpec' energySpec
  simp only [CEparams, hopfieldCE, toCanonicalEnsemble, energy_eq_spec, energySpec,
    HopfieldEnergy.symmetricBinaryEnergySpec]

lemma boltzmannPartitionFunction_eq_sum (T : Temperature) (p : Params ℝ U) :
    (CEparams (NN := NN ℝ U) (spec := energySpec) p).mathematicalPartitionFunction T =
      ∑ s : State ℝ U, Real.exp (-(T.β : ℝ) * hamiltonian p s) := by
  haveI := instIsFinite p
  rw [mathematicalPartitionFunction_of_fintype (𝓒 := CEparams (NN := NN ℝ U) energySpec p) T]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [CEparams_energy_eq_hamiltonian p s, neg_mul]

theorem vectorGibbs_Z_eq_boltzmannPartitionFunction (T : Temperature) (p : Params ℝ U) :
    VectorGibbs.Z (X := State ℝ U) (Θ := Θ U) stat (scaledTheta T p) =
      (CEparams (NN := NN ℝ U) (spec := energySpec) p).mathematicalPartitionFunction T := by
  simp [VectorGibbs.Z, boltzmannPartitionFunction_eq_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [vectorGibbs_weight_eq_boltzmannFactor]
  simp only [neg_mul]

theorem modelProbability_eq_boltzmannFactor_div_Z (T : Temperature) (p : Params ℝ U) (s : State ℝ U) :
    modelProbability T p s =
      Real.exp (-(T.β : ℝ) * hamiltonian p s) /
        (CEparams (NN := NN ℝ U) (spec := energySpec) p).mathematicalPartitionFunction T := by
  simp only [modelProbability, P, CEparams, CanonicalEnsemble.probability, hopfieldCE,
    toCanonicalEnsemble, energy_eq_spec, energySpec, HopfieldEnergy.symmetricBinaryEnergySpec]

theorem vectorGibbs_weight_eq_modelProbability_mul_Z (T : Temperature) (p : Params ℝ U) (s : State ℝ U) :
    VectorGibbs.weight (X := State ℝ U) (Θ := Θ U) stat (scaledTheta T p) s =
      modelProbability T p s *
        (CEparams (NN := NN ℝ U) (spec := energySpec) p).mathematicalPartitionFunction T := by
  haveI := instIsFinite p
  have hZpos :=
    mathematicalPartitionFunction_pos_finite (𝓒 := CEparams (NN := NN ℝ U) energySpec p) T
  rw [vectorGibbs_weight_eq_boltzmannFactor, modelProbability_eq_boltzmannFactor_div_Z]
  field_simp [hZpos.ne']

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
  have hdef : Z • boltzmannExpectationStat T p = Z • ∑ s, modelProbability T p s • stat s := rfl
  rw [hdef, hsum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [vectorGibbs_weight_eq_modelProbability_mul_Z T p s]
  rw [mul_comm (modelProbability T p s) Z, mul_smul Z (modelProbability T p s) (stat s)]

/-- **Main bridge:** temperature-aware `VectorGibbs` expectation equals the Boltzmann expectation. -/
theorem vectorGibbsExpectationStat_eq_boltzmannExpectationStat (T : Temperature) (p : Params ℝ U) :
    vectorGibbsExpectationStat T p = boltzmannExpectationStat T p := by
  have hZ := vectorGibbs_Z_eq_boltzmannPartitionFunction T p
  haveI := instIsFinite p
  have hZpos :=
    mathematicalPartitionFunction_pos_finite (𝓒 := CEparams (NN := NN ℝ U) energySpec p) T
  set Z := (CEparams (NN := NN ℝ U) (spec := energySpec) p).mathematicalPartitionFunction T
  have hZne : Z ≠ 0 := hZpos.ne'
  have hnum := num_eq_Z_smul_boltzmannExpectationStat T p
  calc
    vectorGibbsExpectationStat T p
        = (VectorGibbs.Z stat (scaledTheta T p))⁻¹ • VectorGibbs.num stat (scaledTheta T p) := by
      simp [vectorGibbsExpectationStat, VectorGibbs.expectation]
    _ = Z⁻¹ • (Z • boltzmannExpectationStat T p) := by
      rw [hZ, hnum]
    _ = boltzmannExpectationStat T p := inv_smul_smul₀ hZne (boltzmannExpectationStat T p)

/-- At `T`, the corrected negative-phase statistic; use this instead of `Phases.modelExpectationStat`. -/
theorem corrected_modelExpectationStat_eq_boltzmannExpectationStat (T : Temperature) (p : Params ℝ U) :
    vectorGibbsExpectationStat T p = boltzmannExpectationStat T p :=
  vectorGibbsExpectationStat_eq_boltzmannExpectationStat T p

end SymmetricBinary

end BoltzmannLearningQuiver

end NeuralNetwork
