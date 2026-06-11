/-
Copyright (c) 2025 HNBM contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.BoltzmannLearningQuiver.Stat
import HopfieldNet.BoltzmannLearningQuiver.VectorGibbs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Hamiltonian as vector Gibbs energy

`hamiltonian p s = vectorGibbsEnergy p s = -⟪stat s, thetaFromParams p⟫`.
-/

namespace NeuralNetwork
namespace BoltzmannLearningQuiver
namespace SymmetricBinary

open scoped BigOperators
open VectorGibbs InnerProductSpace Matrix TwoState HopfieldEnergy Finset

variable {U : Type} [Fintype U] [DecidableEq U] [Nonempty U]

/-- Coordinate-wise sufficient-statistic coefficients. -/
noncomputable def statCoeffs (s : State ℝ U) : I U → ℝ
  | Sum.inl (i, j) => (1 / 2 : ℝ) * s.act i * s.act j
  | Sum.inr i => -s.act i

/-- Coordinate-wise parameter coefficients. -/
noncomputable def thetaCoeffs (p : Params ℝ U) : I U → ℝ
  | Sum.inl (i, j) => p.w i j
  | Sum.inr i => (p.θ i).get fin0

/-- Simp lemma for weight coordinates of `statCoeffs`. -/
@[simp] lemma statCoeffs_inl (s : State ℝ U) (i j : U) :
    statCoeffs s (Sum.inl (i, j)) = (1 / 2 : ℝ) * s.act i * s.act j := rfl

/-- Simp lemma for bias coordinates of `statCoeffs`. -/
@[simp] lemma statCoeffs_inr (s : State ℝ U) (i : U) :
    statCoeffs s (Sum.inr i) = -s.act i := rfl

/-- Simp lemma for weight coordinates of `thetaCoeffs`. -/
@[simp] lemma thetaCoeffs_inl (p : Params ℝ U) (i j : U) :
    thetaCoeffs p (Sum.inl (i, j)) = p.w i j := rfl

/-- Simp lemma for bias coordinates of `thetaCoeffs`. -/
@[simp] lemma thetaCoeffs_inr (p : Params ℝ U) (i : U) :
    thetaCoeffs p (Sum.inr i) = (p.θ i).get fin0 := rfl

/-- `WithLp.ofLp (stat s)` agrees with `statCoeffs`. -/
lemma stat_ofLp_coeff (s : State ℝ U) (i : I U) :
    WithLp.ofLp (stat s) i = statCoeffs s i := by
  cases i <;> simp [stat, statCoeffs, WithLp.ofLp_toLp]

/-- `WithLp.ofLp (thetaFromParams p)` agrees with `thetaCoeffs`. -/
lemma theta_ofLp_coeff (p : Params ℝ U) (i : I U) :
    WithLp.ofLp (thetaFromParams p) i = thetaCoeffs p i := by
  cases i <;> simp [thetaFromParams, thetaCoeffs, WithLp.ofLp_toLp]

/-- Inner product expanded to the Hopfield matrix form. -/
lemma inner_stat_theta (p : Params ℝ U) (s : State ℝ U) :
    inner ℝ (stat s) (thetaFromParams p) =
      (1 / 2 : ℝ) * ∑ i, s.act i * (p.w.mulVec s.act i) - ∑ i, (p.θ i).get fin0 * s.act i := by
  classical
  have hW :
      (∑ ij : U × U, (1 / 2 : ℝ) * s.act ij.1 * s.act ij.2 * p.w ij.1 ij.2) =
        (1 / 2 : ℝ) * ∑ i, s.act i * (p.w.mulVec s.act i) := by
    have hfactor :
        ∑ ij : U × U, (1 / 2 : ℝ) * s.act ij.1 * s.act ij.2 * p.w ij.1 ij.2 =
          (1 / 2 : ℝ) * ∑ ij : U × U, s.act ij.1 * s.act ij.2 * p.w ij.1 ij.2 := by
      convert Eq.symm (Finset.mul_sum (s := (Finset.univ : Finset (U × U))) (f := fun ij =>
        s.act ij.1 * s.act ij.2 * p.w ij.1 ij.2) (a := (1 / 2 : ℝ))) using 1
      congr 1
      ext ⟨i, j⟩
      ring
    rw [hfactor]
    congr 1
    rw [Fintype.sum_prod_type' (f := fun i j => s.act i * s.act j * p.w i j)]
    refine Finset.sum_congr rfl fun i _ => ?_
    convert Eq.symm (Finset.mul_sum (s := (Finset.univ : Finset U)) (f := fun j =>
      s.act j * p.w i j) (a := s.act i)) using 1
    · refine Finset.sum_congr rfl fun j _ => by ring
    · simp [Matrix.mulVec, dotProduct, mul_assoc, mul_comm, mul_left_comm]
  have hθ : (∑ i : U, (-s.act i) * (p.θ i).get fin0) = -∑ i, s.act i * (p.θ i).get fin0 := by
    simp [Finset.sum_neg_distrib, mul_comm]
  have hinl :
      (∑ x : U × U, statCoeffs s (Sum.inl x) * thetaCoeffs p (Sum.inl x)) =
        ∑ ij : U × U, (1 / 2 : ℝ) * s.act ij.1 * s.act ij.2 * p.w ij.1 ij.2 := by
    refine Finset.sum_congr rfl fun ⟨i, j⟩ _ => ?_
    simp [statCoeffs_inl, thetaCoeffs_inl, mul_assoc, mul_comm, mul_left_comm]
  rw [PiLp.inner_apply, Fintype.sum_sum_type]
  simp only [stat_ofLp_coeff, theta_ofLp_coeff, Real.inner_apply, statCoeffs_inr, thetaCoeffs_inr]
  rw [hinl, hW, hθ, sub_eq_add_neg, mul_comm]
  simp [mul_comm]

/-- Gibbs / Hopfield energy on quiver states (same as `HopfieldEnergy.hamiltonian`). -/
noncomputable def energy (p : Params ℝ U) (s : State ℝ U) : ℝ :=
  hamiltonian p s

/-- `hamiltonian` and `energy` are definitionally equal. -/
theorem hamiltonian_eq_energy (p : Params ℝ U) (s : State ℝ U) :
    hamiltonian p s = energy p s :=
  rfl

/-- Abstract `VectorGibbs` energy at `thetaFromParams p`. -/
noncomputable def vectorGibbsEnergy (p : Params ℝ U) (s : State ℝ U) : ℝ :=
  VectorGibbs.energy (X := State ℝ U) (Θ := Θ U) stat (thetaFromParams p) s

/-- `vectorGibbsEnergy` equals the negative inner product. -/
lemma vectorGibbsEnergy_eq_neg_inner (p : Params ℝ U) (s : State ℝ U) :
    vectorGibbsEnergy p s = - inner ℝ (stat s) (thetaFromParams p) := by
  simp [vectorGibbsEnergy, VectorGibbs.energy]

/-- `vectorGibbsEnergy p s = hamiltonian p s`. -/
theorem vectorGibbsEnergy_eq_hamiltonian (p : Params ℝ U) (s : State ℝ U) :
    vectorGibbsEnergy p s = hamiltonian p s := by
  rw [vectorGibbsEnergy_eq_neg_inner, inner_stat_theta]
  simp [hamiltonian, HopfieldEnergy.hamiltonian]
  ring

/-- Symmetry of the Hamiltonian / vector Gibbs energy identification. -/
theorem hamiltonian_eq_vectorGibbsEnergy (p : Params ℝ U) (s : State ℝ U) :
    hamiltonian p s = vectorGibbsEnergy p s :=
  (vectorGibbsEnergy_eq_hamiltonian p s).symm

/-- `energy` agrees with the abstract vector Gibbs energy. -/
theorem energy_eq_vectorGibbsEnergy (p : Params ℝ U) (s : State ℝ U) :
    energy p s = vectorGibbsEnergy p s := by
  rw [← hamiltonian_eq_energy, vectorGibbsEnergy_eq_hamiltonian]

end SymmetricBinary
end BoltzmannLearningQuiver
end NeuralNetwork

#lint only docBlame docBlameThm
