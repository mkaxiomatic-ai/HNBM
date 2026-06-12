/-
Copyright (c) 2025 HNBM contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.bmvisible.Bridge
import HopfieldNet.BoltzmannLearningQuiver.Energy
import HopfieldNet.BoltzmannLearningQuiver.BoltzmannBridge
import HopfieldNet.BoltzmannLearningQuiver.VectorGibbs
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Hamiltonian as vector Gibbs energy on visible/hidden BM states
-/

namespace BMVisible

open scoped BigOperators
open NeuralNetwork MeasureTheory ProbabilityTheory BoltzmannLearningQuiver ZeroOne
open VectorGibbs InnerProductSpace Matrix TwoState HopfieldEnergy Finset

variable {U : Type} [Fintype U] [DecidableEq U] [Nonempty U]
variable (part : VisibleHiddenPartition U)

/-- Abstract `VectorGibbs` energy at `bmThetaFromParams p`. -/
noncomputable def vectorGibbsEnergy (p : BMParams ℝ U part) (s : BMState ℝ U part) : ℝ :=
  VectorGibbs.energy (X := BMState ℝ U part) (Θ := Θ U) (stat := bmStat part) (bmThetaFromParams part p) s

lemma vectorGibbsEnergy_eq_neg_inner (p : BMParams ℝ U part) (s : BMState ℝ U part) :
    vectorGibbsEnergy part p s = - inner ℝ (bmStat part s) (bmThetaFromParams part p) := by
  simp [vectorGibbsEnergy, VectorGibbs.energy]

theorem vectorGibbsEnergy_eq_hamiltonian (p : BMParams ℝ U part) (s : BMState ℝ U part) :
    vectorGibbsEnergy part p s = hamiltonian part p s := by
  rw [hamiltonian_eq_zeroOne]
  dsimp [vectorGibbsEnergy, bmStat, bmThetaFromParams]
  exact ZeroOne.vectorGibbsEnergy_eq_hamiltonian (toZeroOneParams part p) (toZeroOneState part s)

lemma hamiltonian_eq_neg_inner (p : BMParams ℝ U part) (s : BMState ℝ U part) :
    hamiltonian part p s = - inner ℝ (bmStat part s) (bmThetaFromParams part p) := by
  rw [← vectorGibbsEnergy_eq_hamiltonian, vectorGibbsEnergy_eq_neg_inner]

lemma inner_stat_scaledTheta (T : Temperature) (p : BMParams ℝ U part) (s : BMState ℝ U part) :
    inner ℝ (bmStat part s) (bmScaledTheta part T p) = (T.β : ℝ) * hamiltonian part p s := by
  rw [hamiltonian_eq_zeroOne, bmStat_eq_stat_toZeroOne, bmScaledTheta]
  exact ZeroOne.inner_stat_scaledTheta T (toZeroOneParams part p) (toZeroOneState part s)

end BMVisible

#lint only docBlame
