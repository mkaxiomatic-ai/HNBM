/-
Copyright (c) 2025 HNBM contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.bmvisible.Clamp
import HopfieldNet.BoltzmannLearningQuiver.ZeroOne
import HopfieldNet.Quiver.BM.BoltzmannMachine
import HopfieldNet.Quiver.NeuralNetwork.toCanonicalEnsemble
import Physlib.Thermodynamics.Temperature.Basic

/-!
# Gibbs dynamics on visible/hidden Boltzmann machines

**Negative phase / §5 free running:** update all neurons (same as `TwoState.ZeroOne`).

**Positive phase (learning):** hold visible units fixed; apply Gibbs updates only on
`U_hid` (`hiddenGibbsSweep`).
-/

namespace BMVisible

open NeuralNetwork TwoState MeasureTheory ProbabilityTheory BoltzmannLearningQuiver ZeroOne
open scoped Temperature BigOperators

variable {U : Type} [Fintype U] [DecidableEq U] [Nonempty U]
variable (part : VisibleHiddenPartition U)

noncomputable instance twoStateInst : TwoStateNeuralNetwork (NN ℝ U part) := instTwoState part

instance : MeasurableSpace (BMState ℝ U part) := ⊤

/-- States on `NN part` coincide with those on `ZeroOne` (same activations). -/
noncomputable def stateEquivZeroOne :
    BMState ℝ U part ≃ NeuralNetwork.State (ZeroOne ℝ U) where
  toFun := toZeroOneState part
  invFun := ofZeroOneState part
  left_inv s := by ext u; simp [toZeroOneState, ofZeroOneState]
  right_inv s := by ext u; simp [toZeroOneState, ofZeroOneState]

noncomputable instance fintypeBMState : Fintype (BMState ℝ U part) :=
  Fintype.ofEquiv _ (stateEquivZeroOne part).symm

noncomputable instance decidableEqBMState : DecidableEq (BMState ℝ U part) :=
  Classical.decEq _

/-- `{0,1}` activations on `NN part` (same as `ZeroOne`). -/
instance twoStateExclusiveInst : TwoStateExclusive (NN ℝ U part) where
  pact_iff a := by
    simp [NN, ZeroOneVisibleHidden, ZeroOne, SymmetricBinary]
    exact (zeroOneExclusive (U := U)).pact_iff a

/-- `{0,1}` energy on visible/hidden BM (identical formula to `HopfieldEnergy.zeroOneHamiltonian`). -/
noncomputable def hamiltonian (p : BMParams ℝ U part) (s : BMState ℝ U part) : ℝ :=
  HopfieldEnergy.zeroOneHamiltonian (R := ℝ) (U := U)
    (p := toZeroOneParams part p) (s := toZeroOneState part s)

/-- Same energy formula as the fully visible `{0,1}` network. -/
lemma hamiltonian_eq_zeroOne (p : BMParams ℝ U part) (s : BMState ℝ U part) :
    hamiltonian part p s =
      HopfieldEnergy.zeroOneHamiltonian (p := toZeroOneParams part p) (s := toZeroOneState part s) := rfl

/-- Energy specification for Gibbs kernels on `NN part`. -/
noncomputable def energySpec : EnergySpec' (NN ℝ U part) where
  E := hamiltonian part
  localField := fun p s u => s.net p u - (p.θ u).get fin0
  localField_spec := by intros; rfl
  flip_energy_relation := by
    intro f p s u
    have h_rel := HopfieldEnergy.zeroOneHamiltonian_flip_relation
      (p := toZeroOneParams part p) (s := toZeroOneState part s) u
    have h_scale := scale_zeroOneVisibleHidden part f
    have hE :
        hamiltonian part p (updPos s u) - hamiltonian part p (updNeg s u) =
          HopfieldEnergy.zeroOneHamiltonian (toZeroOneParams part p) (updPos (toZeroOneState part s) u) -
            HopfieldEnergy.zeroOneHamiltonian (toZeroOneParams part p) (updNeg (toZeroOneState part s) u) := by
      rw [hamiltonian_eq_zeroOne, hamiltonian_eq_zeroOne, toZeroOneState_updPos, toZeroOneState_updNeg]
    rw [hE, h_rel, map_neg, h_scale, map_sub]
    rw [toZeroOneState_net part p s u]
    simp [toZeroOneParams]
    rfl

/-- Nonempty state space (all-zero configuration embedded from `ZeroOne`). -/
noncomputable instance instNonemptyBMState : Nonempty (BMState ℝ U part) :=
  ⟨ofZeroOneState part ZeroOne.defaultState⟩

/-- One-site Gibbs update (any unit). -/
noncomputable abbrev gibbsUpdate (p : BMParams ℝ U part) (T : Temperature) (s : BMState ℝ U part)
    (u : U) : PMF (BMState ℝ U part) :=
  TwoState.gibbsUpdate (R := ℝ) (U := U) (ζ := ℝ) (NN := NN ℝ U part) (RingHom.id ℝ) p T s u

/-- Gibbs sweep along `order` (typically `part.hiddenList`). -/
noncomputable abbrev gibbsSweep (order : List U) (p : BMParams ℝ U part) (T : Temperature)
    (s0 : BMState ℝ U part) : PMF (BMState ℝ U part) :=
  TwoState.gibbsSweep (R := ℝ) (U := U) (ζ := ℝ) (NN := NN ℝ U part) order p T (RingHom.id ℝ) s0

/-- Positive-phase sweep: update hidden units only, then re-merge the visible pattern. -/
noncomputable def hiddenGibbsSweep (order : List U) (p : BMParams ℝ U part) (T : Temperature)
    (vp : VisiblePattern (R := ℝ) part) (s0 : BMState ℝ U part) : PMF (BMState ℝ U part) :=
  gibbsSweep part order p T s0 |>.map fun s => visiblePatternMergeInto part vp s

/-- One CD step for the positive phase from a visible pattern. -/
noncomputable def positiveCdStep (order : List U) (p : BMParams ℝ U part) (T : Temperature)
    (vp : VisiblePattern (R := ℝ) part) (μ : PMF (BMState ℝ U part)) : PMF (BMState ℝ U part) :=
  μ.bind fun s => hiddenGibbsSweep part order p T vp s

/-- CD-$k$ distribution starting from the visible pattern (hidden units at $0$). -/
noncomputable def positiveCdPMF (k : ℕ) (order : List U) (p : BMParams ℝ U part) (T : Temperature)
    (vp : VisiblePattern (R := ℝ) part) : PMF (BMState ℝ U part) :=
  Nat.rec (PMF.pure (visiblePatternToState part vp))
    (fun _ μ => positiveCdStep part order p T vp μ) k

/-- Negative phase: full-network Boltzmann measure (same energy as `ZeroOne`). -/
noncomputable abbrev negativePhaseMeasure (p : BMParams ℝ U part) (T : Temperature) :
    Measure (BMState ℝ U part) :=
  (HopfieldBoltzmann.CEparams (NN := NN ℝ U part) (spec := energySpec part) p).μProd T

end BMVisible

#lint only docBlame
