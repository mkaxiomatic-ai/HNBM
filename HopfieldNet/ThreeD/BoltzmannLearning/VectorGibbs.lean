import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
## Vector-parameter finite Gibbs identity (BM learning, multi-parameter core)

This file upgrades `FiniteGibbs` from a single scalar parameter `t : ℝ` to a parameter vector
`θ : Θ` (a real Hilbert space). The key result is the rigorous “log-partition gradient =
expectation of sufficient statistics” identity in the finite case.

This is the canonical core theorem that justifies BM learning rules once `stat` is instantiated
with the model’s sufficient statistics (weights/bias features).
-/

namespace NeuralNetwork

namespace ThreeD

namespace BoltzmannLearning

namespace VectorGibbs

open scoped BigOperators
open Finset
open InnerProductSpace

variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
variable {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]

/-- Linear energy `E_θ(x) = -⟪stat x, θ⟫`. This convention matches the exp-family weight
`w_θ(x) = exp (E_θ(x)) = exp(-⟪stat x, θ⟫)`. -/
noncomputable def energy (stat : X → Θ) (θ : Θ) (x : X) : ℝ :=
  - inner ℝ (stat x) θ

/-- Unnormalized Gibbs weight `w_θ(x) = exp(E_θ(x))`. -/
noncomputable def weight (stat : X → Θ) (θ : Θ) (x : X) : ℝ :=
  Real.exp (energy (X := X) (Θ := Θ) stat θ x)

/-- Partition function `Z(θ) = ∑_x w_θ(x)` (finite state space). -/
noncomputable def Z (stat : X → Θ) (θ : Θ) : ℝ :=
  ∑ x ∈ (univ : Finset X), weight (X := X) (Θ := Θ) stat θ x

omit [DecidableEq X] [CompleteSpace Θ] in
lemma Z_pos (stat : X → Θ) (θ : Θ) : 0 < Z (X := X) (Θ := Θ) stat θ := by
  classical
  refine Finset.sum_pos ?_ (Finset.univ_nonempty)
  intro x hx
  simp [weight, energy, Real.exp_pos]

omit [DecidableEq X] [CompleteSpace Θ] in
lemma Z_ne_zero (stat : X → Θ) (θ : Θ) : Z (X := X) (Θ := Θ) stat θ ≠ 0 :=
  ne_of_gt (Z_pos (X := X) (Θ := Θ) stat θ)

/-- Vector numerator `∑_x w_θ(x) • stat(x)` whose normalization gives the Gibbs expectation. -/
noncomputable def num (stat : X → Θ) (θ : Θ) : Θ :=
  ∑ x ∈ (univ : Finset X), (weight (X := X) (Θ := Θ) stat θ x) • stat x

/-- Gibbs expectation of the sufficient statistic `stat` under the normalized weights. -/
noncomputable def expectation (stat : X → Θ) (θ : Θ) : Θ :=
  (Z (X := X) (Θ := Θ) stat θ)⁻¹ • num (X := X) (Θ := Θ) stat θ

omit [Fintype X] [DecidableEq X] [Nonempty X] in
lemma hasFDerivAt_weight (stat : X → Θ) (x : X) (θ : Θ) :
    HasFDerivAt (fun θ' : Θ => weight (X := X) (Θ := Θ) stat θ' x)
      (weight (X := X) (Θ := Θ) stat θ x • (-(toDual ℝ Θ (stat x)))) θ := by
  have hlin : HasFDerivAt (fun θ' : Θ => inner ℝ (stat x) θ') (toDual ℝ Θ (stat x)) θ := by
    simpa [InnerProductSpace.toDual_apply_apply] using (toDual ℝ Θ (stat x)).hasFDerivAt (x := θ)
  have hE : HasFDerivAt (fun θ' : Θ => energy (X := X) (Θ := Θ) stat θ' x)
      (-(toDual ℝ Θ (stat x))) θ := by
    simpa [energy] using hlin.neg
  have hexp : HasDerivAt (fun t : ℝ => Real.exp t) (Real.exp (energy (X := X) (Θ := Θ) stat θ x))
      (energy (X := X) (Θ := Θ) stat θ x) :=
    Real.hasDerivAt_exp (energy (X := X) (Θ := Θ) stat θ x)
  simpa [weight] using (hexp.comp_hasFDerivAt θ hE)

omit [DecidableEq X] [Nonempty X] in
lemma hasFDerivAt_Z (stat : X → Θ) (θ : Θ) :
    HasFDerivAt (fun θ' : Θ => Z (X := X) (Θ := Θ) stat θ')
      (∑ x ∈ (univ : Finset X),
        (weight (X := X) (Θ := Θ) stat θ x) • (-(toDual ℝ Θ (stat x)))) θ := by
  classical
  simpa [Z] using (HasFDerivAt.fun_sum (u := (univ : Finset X))
    (A := fun x θ' => weight (X := X) (Θ := Θ) stat θ' x)
    (A' := fun x => (weight (X := X) (Θ := Θ) stat θ x) • (-(toDual ℝ Θ (stat x))))
    (x := θ) (fun x hx => hasFDerivAt_weight (X := X) (Θ := Θ) stat x θ))

omit [DecidableEq X] in
/-- The core identity: `∇ (log (Z stat)) θ = - expectation stat θ`. -/
theorem hasGradientAt_logZ (stat : X → Θ) (θ : Θ) :
    HasGradientAt (fun θ' : Θ => Real.log (Z (X := X) (Θ := Θ) stat θ'))
      (-(expectation (X := X) (Θ := Θ) stat θ)) θ := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hZ := hasFDerivAt_Z (X := X) (Θ := Θ) stat θ
  have hlog :
      HasFDerivAt (fun θ' : Θ => Real.log (Z (X := X) (Θ := Θ) stat θ'))
        ((Z (X := X) (Θ := Θ) stat θ)⁻¹ •
          (∑ x ∈ (univ : Finset X),
            (weight (X := X) (Θ := Θ) stat θ x) • (-(toDual ℝ Θ (stat x))))) θ :=
    (hZ.log (Z_ne_zero (X := X) (Θ := Θ) stat θ))
  have hD :
      (toDual ℝ Θ (-(expectation (X := X) (Θ := Θ) stat θ)))
        =
      ((Z (X := X) (Θ := Θ) stat θ)⁻¹ •
        (∑ x ∈ (univ : Finset X),
          (weight (X := X) (Θ := Θ) stat θ x) • (-(toDual ℝ Θ (stat x))))) := by
    ext h
    classical
    simp [expectation, num, Z, weight, energy, InnerProductSpace.toDual_apply_apply]
  rw [hD]
  exact hlog

end VectorGibbs

end BoltzmannLearning

end ThreeD

end NeuralNetwork
