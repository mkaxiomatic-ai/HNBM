/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Physlib.StatisticalMechanics.CanonicalEnsemble.Finite
import HopfieldNet.Quiver.NeuralNetwork.TwoState

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.style.longLine false

open MeasureTheory

-- NOTE: `NeuralNetwork.State` in this project is defined with `U ζ : Type` (universe 0),
-- so we keep `U` and `ζ` in `Type` throughout this file to avoid universe mismatches.
variable {U ζ : Type}

/-!
# Hamiltonian neural networks and the canonical ensemble

This file defines the `IsHamiltonian` typeclass, which provides the formal lift
between the constructive, algorithmic definition of a `NeuralNetwork`
and the physical, probabilistic framework of a `CanonicalEnsemble`.
-/

/-- For any finite-state neural network we use the trivial (⊤) measurable space. -/
instance (NN : NeuralNetwork ℝ U ζ) [Fintype NN.State] : MeasurableSpace NN.State := ⊤

@[simp] lemma measurable_of_fintype_state
    (NN : NeuralNetwork ℝ U ζ) [Fintype NN.State] (f : NN.State → ℝ) :
    Measurable f := by
  unfold Measurable; intro s _; simp

/--
A typeclass asserting that a `NeuralNetwork`'s dynamics are governed by an energy function.
This is the formal statement that the network is a physical system with a well-defined
Hamiltonian, and that its deterministic dynamics are a form of energy minimization.

- `NN`: The concrete `NeuralNetwork` structure.
-/
class IsHamiltonian (NN : NeuralNetwork ℝ U ζ) [MeasurableSpace NN.State] [DecidableEq U] where
  /-- The energy function (Hamiltonian) of a given state of the network. -/
  energy : Params NN → NN.State → ℝ
  /-- A proof that the energy function is measurable (trivial for discrete (⊤) state spaces). -/
  energy_measurable : ∀ p, Measurable (energy p)
  /-- The core axiom: The energy is a Lyapunov function for the network's asynchronous
  Glauber dynamics. Any single update step does not increase the energy. -/
  energy_is_lyapunov :
    ∀ (p : Params NN) (s : NN.State) (u : U),
      energy p ((NeuralNetwork.State.Up p s u)) ≤ energy p s

/--
A formal constructor that lifts any `NeuralNetwork` proven to be `IsHamiltonian`
into the `CanonicalEnsemble` framework.

This function allows us to apply statistical
mechanics (free energy, entropy, etc.) to a structurally-defined neural network.
-/
@[simps!]
noncomputable def toCanonicalEnsemble [DecidableEq U]
    (NN : NeuralNetwork ℝ U ζ) [Fintype NN.State] [IsHamiltonian NN]
    (p : Params NN) :
    CanonicalEnsemble NN.State where
  energy := IsHamiltonian.energy p
  dof := 0 -- For discrete spin systems, there are no continuous degrees of freedom.
  phaseSpaceunit := 1 -- For counting measures, the unit is 1.
  energy_measurable := IsHamiltonian.energy_measurable p
  μ := Measure.count -- The natural base measure for a discrete state space.
  μ_sigmaFinite := by infer_instance

/-
This instance is a theorem stating that any `NeuralNetwork`
for which we can provide an `EnergySpec` is guaranteed to be an `IsHamiltonian` system.

If we define an `EnergySpec` for a network, Lean's typeclass system will now know that it is also `IsHamiltonian`.
-/

/-! ## Generic Hamiltonian bridge

We generalize the previous `IsHamiltonian_of_EnergySpecSymmetricBinary` to any
two–state neural network for which the activation predicate `pact` is *exactly*
the two distinguished states `ζ_pos` and `ζ_neg`.  This is captured by the
`TwoStateExclusive` predicate below.  For such networks, an `EnergySpec'`
immediately yields an `IsHamiltonian` instance, reusing the generic
`energy_is_lyapunov_at_site''` lemma (no binary–specialized reproofs). -/

namespace TwoState

/-- Exclusivity predicate: the allowed activations are precisely `ζ_pos` or `ζ_neg`. -/
class TwoStateExclusive
    {U ζ} (NN : NeuralNetwork ℝ U ζ)
    [TwoStateNeuralNetwork NN] : Prop where
  (pact_iff : ∀ a, NN.pact a ↔
      a = TwoStateNeuralNetwork.ζ_pos (NN := NN) ∨
      a = TwoStateNeuralNetwork.ζ_neg (NN := NN))

attribute [simp] TwoStateExclusive.pact_iff

/-!
### Consolidation with the `R`-generic exclusivity predicate

The file `NeuralNetwork/NeuralNetwork/TwoState.lean` also defines an `R`-generic predicate
`TwoStateExclusiveR`. For `R = ℝ` these notions coincide; we provide instances both ways so
`TwoStateExclusive` can be used interchangeably with `TwoStateExclusiveR`.
-/

instance
    {U ζ} (NN : NeuralNetwork ℝ U ζ) [TwoStateNeuralNetwork NN] [TwoStateExclusive NN] :
    TwoStateExclusiveR (NN := NN) where
  pact_iff := by
    intro a
    simp

instance
    {U ζ} (NN : NeuralNetwork ℝ U ζ) [TwoStateNeuralNetwork NN] [TwoStateExclusiveR (NN := NN)] :
    TwoStateExclusive NN where
  pact_iff := by
    intro a
    simp

/-- Instance: `SymmetricBinary` activations are exactly `{1,-1}`. -/
instance (U) [Fintype U] [DecidableEq U] [Nonempty U] :
  TwoStateExclusive (TwoState.SymmetricBinary ℝ U) where
  pact_iff a := by
    -- pact definition: a = 1 ∨ a = -1
    simp [TwoState.SymmetricBinary]
    rfl

/-- Instance: `ZeroOne` activations are exactly `{0,1}`. -/
instance zeroOneExclusive (U) [Fintype U] [DecidableEq U] [Nonempty U] :
  TwoStateExclusive (TwoState.ZeroOne ℝ U) where
  pact_iff a := by
    -- pact definition: a = 0 ∨ a = 1
    simp [TwoState.ZeroOne, TwoState.SymmetricBinary]
    apply Iff.intro
    · intro a_1
      cases a_1 with
      | inl h =>
        subst h
        apply Or.inr
        rfl
      | inr h_1 =>
        subst h_1
        apply Or.inl
        rfl
    · intro a_1
      cases a_1 with
      | inl h =>
        subst h
        apply Or.inr
        rfl
      | inr h_1 =>
        subst h_1
        apply Or.inl
        rfl

/-- Instance: `SymmetricSignum` activations (two-point type) are exactly the two constructors. -/
instance signumExclusive (U) [Fintype U] [DecidableEq U] [Nonempty U] :
  TwoStateExclusive (TwoState.SymmetricSignum ℝ U) where
  pact_iff a := by
    -- pact is `True`; every `a` is either `pos` or `neg` by exhaustive cases.
    cases a <;> simp [TwoState.SymmetricSignum]
    all_goals rfl

end TwoState

open TwoState

variable {U ζ : Type} [Fintype U] [DecidableEq U]
variable {NN : NeuralNetwork ℝ U ζ} [TwoStateNeuralNetwork NN]

/-- Generic bridge: any exclusive two–state NN with an `EnergySpec'` is Hamiltonian. -/
def IsHamiltonian_of_EnergySpec'
    (spec : TwoState.EnergySpec' (NN := NN))
    [Fintype NN.State]
    [TwoStateExclusive (NN := NN)] :
    IsHamiltonian (U := U) (ζ := ζ) NN where
  energy := spec.E
  energy_measurable := by
    intro p
    -- finite state space ⇒ every function measurable
    have : Measurable (spec.E p) :=
      measurable_of_fintype_state (NN := NN) (f:=spec.E p)
    simp
  energy_is_lyapunov := by
    intro p s u
    have hcur :=
      (TwoStateExclusive.pact_iff (NN := NN) (a:=s.act u)).1 (s.hp u)
    exact TwoState.EnergySpec'.energy_is_lyapunov_at_site''
            (NN := NN) spec p s u hcur

/--
Backward compatibility: the old SymmetricBinary-specific instance is now
substantiated by the generic one.  (Kept for clarity; can be removed safely.)
-/
@[deprecated IsHamiltonian_of_EnergySpec' (since := "2025-08-24")]
noncomputable def IsHamiltonian_of_EnergySpecSymmetricBinary
    {U : Type} [Fintype U] [DecidableEq U] [Nonempty U]
    [Fintype (TwoState.SymmetricBinary ℝ U).State]
    (spec : TwoState.EnergySpec' (NN := TwoState.SymmetricBinary ℝ U)) :
    IsHamiltonian (TwoState.SymmetricBinary ℝ U) :=
  (IsHamiltonian_of_EnergySpec' (NN := TwoState.SymmetricBinary ℝ U) (spec:=spec))

open CanonicalEnsemble
open scoped BigOperators

variable {U : Type} [DecidableEq U]

/-- Abbreviation: the canonical ensemble associated to a Hamiltonian neural network. -/
noncomputable abbrev hopfieldCE
    (NN : NeuralNetwork ℝ U ζ) [Fintype NN.State] [IsHamiltonian (U := U) (ζ := ζ) NN]
    (p : Params NN) :
    CanonicalEnsemble NN.State :=
  toCanonicalEnsemble (U := U) (ζ := ζ) NN p

/-- The induced finite–ensemble structure (counting measure, dof = 0, unit = 1). -/
instance
    (NN : NeuralNetwork ℝ U ζ) [Fintype NN.State] [IsHamiltonian (U := U) (ζ := ζ) NN]
    (p : Params NN) :
    CanonicalEnsemble.IsFinite (hopfieldCE (U := U) (ζ := ζ) NN p) where
  μ_eq_count := rfl
  dof_eq_zero := rfl
  phase_space_unit_eq_one := rfl

@[simp]
lemma hopfieldCE_dof
    (NN : NeuralNetwork ℝ U ζ) [Fintype NN.State] [IsHamiltonian (U := U) (ζ := ζ) NN]
    (p : Params NN) :
    (hopfieldCE (U := U) (ζ := ζ) NN p).dof = 0 := rfl

@[simp]
lemma hopfieldCE_phaseSpaceunit
    (NN : NeuralNetwork ℝ U ζ) [Fintype NN.State] [IsHamiltonian (U := U) (ζ := ζ) NN]
    (p : Params NN) :
    (hopfieldCE (U := U) (ζ := ζ) NN p).phaseSpaceunit = 1 := rfl

/-- Uniform probability for a constant-energy Hamiltonian (sanity test of the bridge). -/
lemma hopfieldCE_probability_const_energy
    (NN : NeuralNetwork ℝ U ζ) [Fintype NN.State] [IsHamiltonian (U := U) (ζ := ζ) NN]
    (p : Params NN) (c : ℝ)
    (hE : ∀ s, IsHamiltonian.energy (U := U) (ζ := ζ) (NN := NN) p s = c)
    (T : Temperature) (s : NN.State) :
    (hopfieldCE (U := U) (ζ := ζ) NN p).probability T s
      = (1 : ℝ) / (Fintype.card NN.State) := by
  set 𝓒 := hopfieldCE (U := U) (ζ := ζ) NN p
  have hZ :=
    (mathematicalPartitionFunction_of_fintype (𝓒:=𝓒) T)
  have hZconst :
      𝓒.mathematicalPartitionFunction T
        = (Fintype.card NN.State : ℝ) * Real.exp (-(T.β : ℝ) * c) := by
    have hsum :
        (∑ s : NN.State, Real.exp (-(T.β : ℝ) * 𝓒.energy s))
          = (∑ _ : NN.State, Real.exp (-(T.β : ℝ) * c)) := by
      refine Finset.sum_congr rfl ?_
      intro s _; simp [𝓒, toCanonicalEnsemble, hE]
    have hsumConst :
        (∑ _ : NN.State, Real.exp (-(T.β : ℝ) * c))
          = (Fintype.card NN.State : ℕ) • Real.exp (-(T.β : ℝ) * c) := by
      simp [Finset.sum_const, Finset.card_univ]
    have hnsmul :
        ((Fintype.card NN.State : ℕ) • Real.exp (-(T.β : ℝ) * c))
          = (Fintype.card NN.State : ℝ) * Real.exp (-(T.β : ℝ) * c) := by
      simp
    simp [hZ]
    simp_all only [toCanonicalEnsemble_energy, neg_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, 𝓒]
  unfold CanonicalEnsemble.probability
  have hexp_ne : Real.exp (-(T.β : ℝ) * c) ≠ 0 := (Real.exp_pos _).ne'
  simp_rw [𝓒, toCanonicalEnsemble, hE]
  erw [hZconst]
  simp [div_eq_mul_inv, mul_comm, mul_left_comm]

/-- Corollary: mean energy = constant `c` under the induced canonical ensemble,
    for a constant-energy network. -/
lemma hopfieldCE_meanEnergy_const
    (NN : NeuralNetwork ℝ U ζ) [Fintype NN.State] [Nonempty NN.State]
    [IsHamiltonian (U := U) (ζ := ζ) NN]
    (p : Params NN) (c : ℝ)
    (hE : ∀ s, IsHamiltonian.energy (U := U) (ζ := ζ) (NN := NN) p s = c)
    (T : Temperature) :
    (hopfieldCE (U := U) (ζ := ζ) NN p).meanEnergy T = c := by
  set 𝓒 := hopfieldCE (U := U) (ζ := ζ) NN p
  have hZeq :
      𝓒.mathematicalPartitionFunction T
        = (Fintype.card NN.State : ℝ) * Real.exp (-(T.β : ℝ) * c) := by
    have hZform := (mathematicalPartitionFunction_of_fintype (𝓒:=𝓒) T)
    have :
        (∑ s : NN.State, Real.exp (-(T.β : ℝ) * 𝓒.energy s))
          = (Fintype.card NN.State : ℝ) * Real.exp (-(T.β : ℝ) * c) := by
      have hconst :
          (∑ _ : NN.State, Real.exp (-(T.β : ℝ) * c))
            = (Fintype.card NN.State : ℕ) • Real.exp (-(T.β : ℝ) * c) := by
        simp [Finset.sum_const, Finset.card_univ]
      simp [𝓒, toCanonicalEnsemble, hE, nsmul_eq_mul,
            mul_comm]
    simpa [hZform]
  have hNum' :
      (∑ s : NN.State,
          IsHamiltonian.energy (U := U) (ζ := ζ) (NN := NN) p s *
            Real.exp (-(T.β : ℝ) *
              IsHamiltonian.energy (U := U) (ζ := ζ) (NN := NN) p s))
        = c * 𝓒.mathematicalPartitionFunction T := by
    have hNumEq :
        (∑ s : NN.State,
            IsHamiltonian.energy (U := U) (ζ := ζ) (NN := NN) p s *
              Real.exp (-(T.β : ℝ) *
                IsHamiltonian.energy (U := U) (ζ := ζ) (NN := NN) p s))
          = c * ((Fintype.card NN.State : ℝ) *
                Real.exp (-(T.β : ℝ) * c)) := by
      have hconst :
          (∑ _ : NN.State,
              c * Real.exp (-(T.β : ℝ) * c))
            = (Fintype.card NN.State : ℕ) • (c * Real.exp (-(T.β : ℝ) * c)) := by
        simp [Finset.sum_const, Finset.card_univ]
      simp [hE, nsmul_eq_mul, mul_comm, mul_left_comm]
    simpa [hZeq, mul_comm, mul_left_comm, mul_assoc] using hNumEq
  unfold CanonicalEnsemble.meanEnergy
  have hZne : 𝓒.mathematicalPartitionFunction T ≠ 0 := by
    have hcard : 0 < (Fintype.card NN.State : ℝ) := by
      have : 0 < Fintype.card NN.State := Fintype.card_pos_iff.mpr inferInstance
      exact_mod_cast this
    have hpos :
        0 < (Fintype.card NN.State : ℝ) * Real.exp (-(T.β : ℝ) * c) :=
      mul_pos hcard (Real.exp_pos _)
    simp [hZeq]
  simp_all only [neg_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ne_eq, mul_eq_zero, Nat.cast_eq_zero,
    Fintype.card_ne_zero, Real.exp_ne_zero, or_self, not_false_eq_true, toCanonicalEnsemble_energy, integral_const,
    probReal_univ, smul_eq_mul, one_mul, 𝓒]

-- Inheritance showcase: canonical–ensemble facts usable for Hopfield networks.
section CanonicalEnsembleInheritanceExamples
variable {U ζ : Type} [Fintype U] [DecidableEq U]
variable (NN : NeuralNetwork ℝ U ζ) [Fintype NN.State] [Nonempty NN.State]
variable [IsHamiltonian (U := U) (ζ := ζ) NN]
variable (p : Params NN) (T : Temperature)
variable (s : NN.State)

-- Basic objects
#check (hopfieldCE (U := U) (ζ := ζ) NN p).partitionFunction
#check (hopfieldCE (U := U) (ζ := ζ) NN p).mathematicalPartitionFunction

-- Positivity (finite specialization)
#check (mathematicalPartitionFunction_pos_finite
          (𝓒:=hopfieldCE (U := U) (ζ := ζ) NN p) (T:=T))
#check (partitionFunction_pos_finite
          (𝓒:=hopfieldCE (U := U) (ζ := ζ) NN p) (T:=T))

-- Probability normalization & basic bounds
#check (sum_probability_eq_one
          (𝓒:=hopfieldCE (U := U) (ζ := ζ) NN p) (T:=T))
#check (probability_nonneg_finite
          (𝓒:=hopfieldCE (U := U) (ζ := ζ) NN p) (T:=T) (i:=s))

-- Entropy identifications in finite case
#check (shannonEntropy_eq_differentialEntropy
          (𝓒:=hopfieldCE (U := U) (ζ := ζ) NN p) (T:=T))
#check (thermodynamicEntropy_eq_shannonEntropy
          (𝓒:=hopfieldCE (U := U) (ζ := ζ) NN p) (T:=T))

-- Additivity for two independent Hopfield ensembles (same phaseSpaceunit = 1)
variable (NN₁ NN₂ : NeuralNetwork ℝ U ζ)
variable [Fintype NN₁.State] [Nonempty NN₁.State] [IsHamiltonian (U := U) (ζ := ζ) NN₁]
variable [Fintype NN₂.State] [Nonempty NN₂.State] [IsHamiltonian (U := U) (ζ := ζ) NN₂]
variable (p₁ : Params NN₁) (p₂ : Params NN₂)

#check partitionFunction_add
  (𝓒:=hopfieldCE (U := U) (ζ := ζ) NN₁ p₁)
  (𝓒1:=hopfieldCE (U := U) (ζ := ζ) NN₂ p₂)
  (T:=T) (by simp)
#check helmholtzFreeEnergy_add
  (𝓒:=hopfieldCE (U := U) (ζ := ζ) NN₁ p₁)
  (𝓒1:=hopfieldCE (U := U) (ζ := ζ) NN₂ p₂)
  (T:=T) (by simp)
#check meanEnergy_add
  (𝓒:=hopfieldCE (U := U) (ζ := ζ) NN₁ p₁)
  (𝓒1:=hopfieldCE (U := U) (ζ := ζ) NN₂ p₂)

-- n independent copies (scaling laws)
#check partitionFunction_nsmul
  (𝓒:=hopfieldCE (U := U) (ζ := ζ) NN p) (n:=3) (T:=T)
#check helmholtzFreeEnergy_nsmul
  (𝓒:=hopfieldCE (U := U) (ζ := ζ) NN p) (n:=3) (T:=T)
#check meanEnergy_nsmul
  (𝓒:=hopfieldCE (U := U) (ζ := ζ) NN p) (n:=3) (T:=T)

end CanonicalEnsembleInheritanceExamples
