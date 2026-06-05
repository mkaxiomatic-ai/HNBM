import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-!
## Finite Gibbs / exponential-family core identity (BM learning, nontrivial theorem)

This file proves the foundational analytic identity that underlies Boltzmann Machine learning:

For a finite state space `X` and statistic `φ : X → ℝ`, define

- weights: \(w_t(x) = \exp(-t \, φ(x))\)
- partition function: \(Z(t) = \sum_x w_t(x)\)
- Gibbs expectation: \(E_t[φ] = (\sum_x φ(x) w_t(x)) / Z(t)\)

Then:

\[
\frac{d}{dt} \log Z(t) = - E_t[φ].
\]

This is the “log-partition gradient = expectation” principle in the simplest 1-parameter case.
We keep it as a clean lemma that can later be lifted to multi-parameter energies and to the
positive-phase/negative-phase learning rule.
-/

namespace NeuralNetwork

namespace ThreeD

namespace BoltzmannLearning

namespace FiniteGibbs

set_option linter.unusedSectionVars false

open scoped BigOperators
open Finset

variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]

/-- Unnormalized weight \(w_t(x)\). -/
noncomputable def weight (φ : X → ℝ) (t : ℝ) (x : X) : ℝ :=
  Real.exp (-t * φ x)

/-- Partition function \(Z(t) = \sum_x w_t(x)\). -/
noncomputable def Z (φ : X → ℝ) (t : ℝ) : ℝ :=
  ∑ x : X, weight (X := X) φ t x

lemma Z_pos (φ : X → ℝ) (t : ℝ) : 0 < Z (X := X) φ t := by
  classical
  have : 0 < (univ : Finset X).sum (fun x => weight (X := X) φ t x) := by
    refine Finset.sum_pos ?_ (Finset.univ_nonempty)
    intro x hx
    simp [weight, Real.exp_pos]
  simpa [Z] using this

lemma Z_ne_zero (φ : X → ℝ) (t : ℝ) : Z (X := X) φ t ≠ 0 :=
  (ne_of_gt (Z_pos (X := X) φ t))

/-- Gibbs expectation \(E_t[φ]\) under the normalized weights \(w_t / Z(t)\). -/
noncomputable def expectation (φ : X → ℝ) (t : ℝ) : ℝ :=
  (∑ x : X, (φ x) * weight (X := X) φ t x) / Z (X := X) φ t

lemma hasDerivAt_Z (φ : X → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Z (X := X) φ s)
      ((univ : Finset X).sum (fun x => (-φ x) * weight (X := X) φ t x)) t := by
  classical
  have hterm :
      ∀ x ∈ (univ : Finset X),
        HasDerivAt (fun s : ℝ => weight (X := X) φ s x) ((-φ x) * weight (X := X) φ t x) t := by
    intro x _hx
    have hmul : HasDerivAt (fun s : ℝ => s * φ x) (φ x) t := by
      simpa [id, one_mul] using (hasDerivAt_id t).mul_const (φ x)
    have hneg : HasDerivAt (fun s : ℝ => -(s * φ x)) (-(φ x)) t := hmul.neg
    have hexp : HasDerivAt (fun u : ℝ => Real.exp u) (Real.exp (-(t * φ x))) (-(t * φ x)) :=
      Real.hasDerivAt_exp (-(t * φ x))
    have hcomp : HasDerivAt (fun s : ℝ => Real.exp (-(s * φ x)))
        (Real.exp (-(t * φ x)) * (-(φ x))) t :=
      by
        simpa [Function.comp] using (hexp.comp t hneg)
    simpa [weight, mul_assoc, mul_left_comm, mul_comm] using hcomp
  have hsum :
      HasDerivAt (fun s : ℝ => (univ : Finset X).sum (fun x => weight (X := X) φ s x))
        ((univ : Finset X).sum (fun x => (-φ x) * weight (X := X) φ t x)) t := by
    simpa using (HasDerivAt.fun_sum (u := (univ : Finset X))
      (A := fun x s => weight (X := X) φ s x)
      (A' := fun x => (-φ x) * weight (X := X) φ t x)
      (x := t) hterm)
  simpa [Z] using hsum

/-- Core identity: \( (d/dt)\, \log Z(t) = -E_t[φ] \). -/
theorem hasDerivAt_logZ (φ : X → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.log (Z (X := X) φ s)) (-(expectation (X := X) φ t)) t := by
  have hZ : HasDerivAt (fun s : ℝ => Z (X := X) φ s)
      ((univ : Finset X).sum (fun x => (-φ x) * weight (X := X) φ t x)) t :=
    hasDerivAt_Z (X := X) φ t
  have hZne : Z (X := X) φ t ≠ 0 := Z_ne_zero (X := X) φ t
  have hlog :
      HasDerivAt (fun s : ℝ => Real.log (Z (X := X) φ s))
        (((univ : Finset X).sum (fun x => (-φ x) * weight (X := X) φ t x)) / Z (X := X) φ t) t :=
    (hZ.log hZne)
  simpa [expectation, Z, neg_div] using hlog

end FiniteGibbs

end BoltzmannLearning

end ThreeD

end NeuralNetwork
