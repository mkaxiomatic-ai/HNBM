/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.QUBO.Minimizers
import HopfieldNet.Quiver.BM.Ergodicity

/-!
# The Gibbs chain of a 0/1 QUBO concentrates on the feasible set

`QUBO.Net` puts an arbitrary 0/1 QUBO `‖Âx̂ − b̂‖²` on the repository's `{0,1}` Boltzmann
network, and `QUBO.Minimizers` identifies the minimisers of that network's energy with the
zero-penalty (feasible) assignments, with an energy gap of at least `1/2`. This module draws
the probabilistic consequence.

## What is proved

* `stationary_eq_πBoltzVec` — Step 1. `HopfieldNet.Quiver.BM.Ergodicity`'s
  `RSrow_stationary_unique_eq_πBoltzVec`, instantiated at
  `NN := TwoState.ZeroOne ℝ (Fin P.nvars)`, `spec := zeroOneEnergySpec`, `p := netParams P`:
  the random-scan Gibbs chain of the QUBO has a unique stationary distribution and it is the
  Boltzmann law of the QUBO's energy. No hypothesis on `P` beyond `Nonempty (Fin P.nvars)` —
  not even `P.Wf`, since irreducibility of the chain is a fact about the *network*, and every
  `netParams P` is one.
* `πBoltzVec_apply` — that stationary vector, evaluated: it is `exp(−E/T)/Z` at the real
  temperature `kB · T`.
* `infeasible_ratio_tendsto_zero`, `infeasible_fraction_tendsto_zero`,
  `feasible_fraction_tendsto_one` — Step 2, for the un-normalised weights
  `exp(−E(s)/T)` at a real temperature parameter `T`: as `T → 0⁺`, the Boltzmann mass of the
  infeasible states relative to the feasible ones, and relative to the whole state space,
  tends to `0`, and the feasible fraction tends to `1`.
* `πBoltzVec_infeasible_mass`, `πBoltzVec_infeasible_tendsto_zero` and
  `stationary_infeasible_tendsto_zero` — the same statement transported to the *stationary
  distribution of the chain itself*: the probability that the chain's unique equilibrium law
  assigns to the infeasible states tends to `0` as the physical temperature tends to `0` from
  above.

The last item is the statement the paper wants: at equilibrium and low temperature the annealed
Boltzmann machine puts all of its mass on the solutions.

## Which dynamics this is about

The **random-scan single-site Gibbs chain**: pick a neuron uniformly, resample it from its
conditional Boltzmann law. That is the memoryless reading of the update, the one
`QUBO.Sweep.stateOfBits_stepAt` connects to the executable sweep. It is *not* `bmmStep`'s
momentum recurrence `u ← u + (Wx − θ)` of eqs (3) and (6): an undamped accumulator is not the
`Up` of any network, has no stationary law here, and nothing below applies to it.

Nor is anything below a statement about a *cooling schedule*. The limits are limits of the
equilibrium law at temperature `T` as `T → 0⁺`; they say nothing about how slowly `T` must be
lowered for a chain run at a moving temperature to track that equilibrium.
-/

namespace QUBO
namespace Problem

open TwoState HopfieldEnergy Finset Filter Topology

attribute [local instance] Classical.propDecidable

/-- Every `{0,1}` network has at least one state: switch every neuron off. -/
instance zeroOneStateNonempty (U : Type) [Fintype U] [DecidableEq U] [Nonempty U] :
    Nonempty (TwoState.ZeroOne ℝ U).State :=
  ⟨{ act := fun _ => 0, hp := fun _ => Or.inl rfl }⟩

variable (P : Problem) [Nonempty (Fin P.nvars)]

/-- The state space the QUBO's Gibbs chain moves on. -/
abbrev QState := (TwoState.ZeroOne ℝ (Fin P.nvars)).State

/-! ## Step 1: the stationary law of the random-scan Gibbs chain -/

/-- **The random-scan Gibbs chain of a 0/1 QUBO has the Boltzmann law of its objective as its
unique stationary distribution.**

This is `RSrow_stationary_unique_eq_πBoltzVec` at `NN := TwoState.ZeroOne ℝ (Fin P.nvars)`,
`spec := zeroOneEnergySpec`, `p := netParams P`. `RSrow` is the row-stochastic transition matrix
of the random-scan single-site Gibbs kernel at temperature `T`;
`RSrow_exists_unique_stationary_distribution` (irreducibility plus Perron–Frobenius) gives it a
unique stationary distribution on the simplex, and the theorem says that distribution is
`πBoltzVec`, the Boltzmann law of `zeroOneHamiltonian (netParams P)`.

Note what is *not* required: no `P.Wf`. Well-formedness is what makes the energy equal the
paper's objective; the ergodic theory only needs the network. -/
theorem stationary_eq_πBoltzVec (T : Temperature) :
    (Classical.choose
      (RSrow_exists_unique_stationary_distribution
        (NN := TwoState.ZeroOne ℝ (Fin P.nvars)) (spec := zeroOneEnergySpec)
        (p := netParams P) (T := T)).exists)
      = πBoltzVec (NN := TwoState.ZeroOne ℝ (Fin P.nvars)) (spec := zeroOneEnergySpec)
          (p := netParams P) (T := T) :=
  RSrow_stationary_unique_eq_πBoltzVec ..

/-- The Boltzmann law is stationary for the chain, on the nose. -/
theorem πBoltzVec_isStationary (T : Temperature) :
    IsStationary
      (RSrow (NN := TwoState.ZeroOne ℝ (Fin P.nvars)) zeroOneEnergySpec (netParams P) T)
      (πBoltzVec (NN := TwoState.ZeroOne ℝ (Fin P.nvars)) (spec := zeroOneEnergySpec)
        (p := netParams P) (T := T)) :=
  πBoltzVec_is_stationary_RSrow ..

/-! ## Boltzmann weights at a real temperature -/

/-- The un-normalised Boltzmann weight `exp(−E(s)/T)` of a state. -/
noncomputable def boltzWeight (T : ℝ) (s : QState P) : ℝ :=
  Real.exp (-(zeroOneHamiltonian (netParams P) s) / T)

theorem boltzWeight_pos (T : ℝ) (s : QState P) : 0 < boltzWeight P T s := Real.exp_pos _

/-- The feasible states: those whose reduced penalty vanishes. By `energy_eq_min_iff` these are
exactly the energy minimisers. -/
noncomputable def feasibleStates : Finset (QState P) :=
  Finset.univ.filter fun s => penaltyR P (bitsOfState P s) = 0

/-- The infeasible states — the complement. -/
noncomputable def infeasibleStates : Finset (QState P) :=
  Finset.univ.filter fun s => ¬ penaltyR P (bitsOfState P s) = 0

/-- The Boltzmann mass of the feasible states. -/
noncomputable def feasibleMass (T : ℝ) : ℝ := ∑ s ∈ feasibleStates P, boltzWeight P T s

/-- The Boltzmann mass of the infeasible states. -/
noncomputable def infeasibleMass (T : ℝ) : ℝ := ∑ s ∈ infeasibleStates P, boltzWeight P T s

/-- The partition sum `Z(T) = Σ_s exp(−E(s)/T)`. -/
noncomputable def partitionSum (T : ℝ) : ℝ := ∑ s, boltzWeight P T s

/-- Feasible and infeasible exhaust the state space. -/
theorem partitionSum_eq (T : ℝ) :
    partitionSum P T = feasibleMass P T + infeasibleMass P T :=
  (Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun s => penaltyR P (bitsOfState P s) = 0) _).symm

theorem infeasibleMass_nonneg (T : ℝ) : 0 ≤ infeasibleMass P T :=
  Finset.sum_nonneg fun s _ => (boltzWeight_pos P T s).le

/-- Every feasible state carries the same weight, so the feasible mass is a count times it. -/
theorem feasibleMass_eq (hW : P.Wf) (T : ℝ) :
    feasibleMass P T
      = (feasibleStates P).card * Real.exp (-(minEnergy P) / T) := by
  unfold feasibleMass
  rw [Finset.sum_congr rfl (fun s hs => ?_), Finset.sum_const, nsmul_eq_mul]
  show boltzWeight P T s = Real.exp (-(minEnergy P) / T)
  unfold boltzWeight
  rw [(energy_eq_min_iff P hW s).mpr (by simpa [feasibleStates] using hs)]

/-- With at least one feasible state, the feasible mass is positive. -/
theorem feasibleMass_pos (hfeas : (feasibleStates P).Nonempty) (T : ℝ) :
    0 < feasibleMass P T :=
  Finset.sum_pos (fun s _ => boltzWeight_pos P T s) hfeas

/-- **Every infeasible state is suppressed by `exp(−1/(2T))` relative to a feasible one.**

`boltzmann_ratio_le` state by state, summed. -/
theorem infeasibleMass_le (hW : P.Wf) {T : ℝ} (hT : 0 < T) {s' : QState P}
    (hs' : zeroOneHamiltonian (netParams P) s' = minEnergy P) :
    infeasibleMass P T
      ≤ (infeasibleStates P).card *
          (Real.exp (-(1 / 2) / T) * Real.exp (-(minEnergy P) / T)) := by
  have hbound : ∀ s ∈ infeasibleStates P,
      boltzWeight P T s ≤ Real.exp (-(1 / 2) / T) * Real.exp (-(minEnergy P) / T) := by
    intro s hs
    have hpen : ¬ penaltyR P (bitsOfState P s) = 0 := by simpa [infeasibleStates] using hs
    have hne : zeroOneHamiltonian (netParams P) s ≠ minEnergy P := fun h =>
      hpen ((energy_eq_min_iff P hW s).mp h)
    have := boltzmann_ratio_le P hW hT s s' hne hs'
    rwa [hs'] at this
  calc infeasibleMass P T
      ≤ (infeasibleStates P).card •
          (Real.exp (-(1 / 2) / T) * Real.exp (-(minEnergy P) / T)) :=
        Finset.sum_le_card_nsmul _ _ _ hbound
    _ = (infeasibleStates P).card *
          (Real.exp (-(1 / 2) / T) * Real.exp (-(minEnergy P) / T)) := nsmul_eq_mul _ _

/-! ## Step 2: concentration on the feasible set as `T → 0⁺` -/

/-- **The relative Boltzmann mass of the infeasible states is at most
`|infeasible| · exp(−1/(2T))`.** -/
theorem infeasible_ratio_le (hW : P.Wf) {s' : QState P}
    (hs' : zeroOneHamiltonian (netParams P) s' = minEnergy P) {T : ℝ} (hT : 0 < T) :
    infeasibleMass P T / feasibleMass P T
      ≤ (infeasibleStates P).card * Real.exp (-(1 / 2) / T) := by
  have hmem : s' ∈ feasibleStates P := by
    simp only [feasibleStates, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (energy_eq_min_iff P hW s').mp hs'
  have hne : (feasibleStates P).Nonempty := ⟨s', hmem⟩
  have hpos := feasibleMass_pos P hne T
  have hcard : (1 : ℝ) ≤ (feasibleStates P).card := by
    exact_mod_cast Finset.card_pos.mpr hne
  rw [div_le_iff₀ hpos, feasibleMass_eq P hW T]
  have hle := infeasibleMass_le P hW hT hs'
  have hq : (0 : ℝ) ≤ (infeasibleStates P).card * Real.exp (-(1 / 2) / T) :=
    mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le
  have hexp : (0 : ℝ) < Real.exp (-(minEnergy P) / T) := Real.exp_pos _
  have h0 : (0 : ℝ)
      ≤ (infeasibleStates P).card * Real.exp (-(1 / 2) / T) * Real.exp (-(minEnergy P) / T) :=
    mul_nonneg hq hexp.le
  have h1 : (0 : ℝ) ≤ ((feasibleStates P).card : ℝ) - 1 := by linarith
  nlinarith [hle, h0, h1]

/-- **The infeasible fraction of the total Boltzmann mass is at most
`|infeasible| · exp(−1/(2T))`.** -/
theorem infeasible_fraction_le (hW : P.Wf) {s' : QState P}
    (hs' : zeroOneHamiltonian (netParams P) s' = minEnergy P) {T : ℝ} (hT : 0 < T) :
    infeasibleMass P T / partitionSum P T
      ≤ (infeasibleStates P).card * Real.exp (-(1 / 2) / T) := by
  have hmem : s' ∈ feasibleStates P := by
    simp only [feasibleStates, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (energy_eq_min_iff P hW s').mp hs'
  have hfpos := feasibleMass_pos P ⟨s', hmem⟩ T
  have hZ : feasibleMass P T ≤ partitionSum P T := by
    rw [partitionSum_eq]; linarith [infeasibleMass_nonneg P T]
  refine le_trans (div_le_div_of_nonneg_left (infeasibleMass_nonneg P T) hfpos hZ) ?_
  exact infeasible_ratio_le P hW hs' hT

/-- The suppression factor, scaled by a constant, still tends to zero. -/
private theorem tendsto_card_suppression (c : ℝ) :
    Tendsto (fun T : ℝ => c * Real.exp (-(1 / 2) / T)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  simpa using tendsto_suppression.const_mul c

/-- **The Boltzmann mass of the infeasible states, relative to the feasible ones, tends to zero
as the temperature falls.** -/
theorem infeasible_ratio_tendsto_zero (hW : P.Wf)
    (hfeas : ∃ s : QState P, zeroOneHamiltonian (netParams P) s = minEnergy P) :
    Tendsto (fun T : ℝ => infeasibleMass P T / feasibleMass P T)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  obtain ⟨s', hs'⟩ := hfeas
  refine squeeze_zero' ?_ ?_ (tendsto_card_suppression ((infeasibleStates P).card : ℝ))
  · filter_upwards [self_mem_nhdsWithin] with T hT
    exact div_nonneg (infeasibleMass_nonneg P T) (feasibleMass_pos P ⟨s', by
      simp only [feasibleStates, Finset.mem_filter, Finset.mem_univ, true_and]
      exact (energy_eq_min_iff P hW s').mp hs'⟩ T).le
  · filter_upwards [self_mem_nhdsWithin] with T hT
    exact infeasible_ratio_le P hW hs' hT

/-- **The Boltzmann probability of the infeasible states tends to zero as the temperature
falls** — the normalised form, with `Z(T)` the partition sum over the whole (finite) state
space. -/
theorem infeasible_fraction_tendsto_zero (hW : P.Wf)
    (hfeas : ∃ s : QState P, zeroOneHamiltonian (netParams P) s = minEnergy P) :
    Tendsto (fun T : ℝ => infeasibleMass P T / partitionSum P T)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  obtain ⟨s', hs'⟩ := hfeas
  have hmem : s' ∈ feasibleStates P := by
    simp only [feasibleStates, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (energy_eq_min_iff P hW s').mp hs'
  refine squeeze_zero' ?_ ?_ (tendsto_card_suppression ((infeasibleStates P).card : ℝ))
  · filter_upwards [self_mem_nhdsWithin] with T hT
    have : 0 < partitionSum P T := by
      rw [partitionSum_eq]
      linarith [feasibleMass_pos P ⟨s', hmem⟩ T, infeasibleMass_nonneg P T]
    exact div_nonneg (infeasibleMass_nonneg P T) this.le
  · filter_upwards [self_mem_nhdsWithin] with T hT
    exact infeasible_fraction_le P hW hs' hT

/-- **…equivalently, the feasible states carry all the mass in the limit.** -/
theorem feasible_fraction_tendsto_one (hW : P.Wf)
    (hfeas : ∃ s : QState P, zeroOneHamiltonian (netParams P) s = minEnergy P) :
    Tendsto (fun T : ℝ => feasibleMass P T / partitionSum P T)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  obtain ⟨s', hs'⟩ := hfeas
  have hmem : s' ∈ feasibleStates P := by
    simp only [feasibleStates, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (energy_eq_min_iff P hW s').mp hs'
  have hlim := infeasible_fraction_tendsto_zero P hW ⟨s', hs'⟩
  have h1 : Tendsto (fun T : ℝ => 1 - infeasibleMass P T / partitionSum P T)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 - 0)) := tendsto_const_nhds.sub hlim
  rw [sub_zero] at h1
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with T hT
  have hZ : partitionSum P T ≠ 0 := by
    have : 0 < partitionSum P T := by
      rw [partitionSum_eq]
      linarith [feasibleMass_pos P ⟨s', hmem⟩ T, infeasibleMass_nonneg P T]
    exact this.ne'
  have hsplit : feasibleMass P T = partitionSum P T - infeasibleMass P T := by
    rw [partitionSum_eq]; ring
  rw [hsplit, sub_div, div_self hZ]

/-! ## The stationary distribution itself -/

open Constants in
/-- **The stationary distribution of the chain, evaluated.**

`πBoltzVec` at temperature `T` is the normalised Boltzmann weight at the real temperature
`kB · T`. This is what turns the limits above into limits about the chain. -/
theorem πBoltzVec_apply (T : Temperature) (s : QState P) :
    (πBoltzVec (NN := TwoState.ZeroOne ℝ (Fin P.nvars)) (spec := zeroOneEnergySpec)
        (p := netParams P) (T := T)).val s
      = boltzWeight P (kB * T.toReal) s / partitionSum P (kB * T.toReal) := by
  have hβ : ∀ t : QState P,
      Real.exp (-(T.β : ℝ) * (HopfieldBoltzmann.CEparams
          (NN := TwoState.ZeroOne ℝ (Fin P.nvars)) (spec := zeroOneEnergySpec)
          (netParams P)).energy t)
        = boltzWeight P (kB * T.toReal) t := by
    intro t
    show Real.exp (-(T.β : ℝ) * zeroOneHamiltonian (netParams P) t) = _
    unfold boltzWeight
    rw [Temperature.β_toReal]
    ring_nf
  show ((HopfieldBoltzmann.CEparams (NN := TwoState.ZeroOne ℝ (Fin P.nvars))
      (spec := zeroOneEnergySpec) (netParams P)).μProd T {s}).toReal = _
  rw [show (((HopfieldBoltzmann.CEparams (NN := TwoState.ZeroOne ℝ (Fin P.nvars))
        (spec := zeroOneEnergySpec) (netParams P)).μProd T) {s}).toReal
      = ((HopfieldBoltzmann.CEparams (NN := TwoState.ZeroOne ℝ (Fin P.nvars))
        (spec := zeroOneEnergySpec) (netParams P)).μProd T).real {s} from rfl,
    CanonicalEnsemble.μProd_of_fintype, CanonicalEnsemble.probability,
    CanonicalEnsemble.mathematicalPartitionFunction_of_fintype]
  unfold partitionSum
  rw [hβ s]
  exact congrArg _ (Finset.sum_congr rfl fun t _ => hβ t)

open Constants in
/-- The equilibrium probability of the infeasible set. -/
theorem πBoltzVec_infeasible_mass (T : Temperature) :
    ∑ s ∈ infeasibleStates P,
        (πBoltzVec (NN := TwoState.ZeroOne ℝ (Fin P.nvars)) (spec := zeroOneEnergySpec)
          (p := netParams P) (T := T)).val s
      = infeasibleMass P (kB * T.toReal) / partitionSum P (kB * T.toReal) := by
  rw [Finset.sum_congr rfl fun s _ => πBoltzVec_apply P T s, ← Finset.sum_div]
  rfl

/-- Scaling by `kB` and dropping to `ℝ` sends the punctured neighbourhood of absolute zero to the
punctured neighbourhood of `0` in `ℝ`. -/
private theorem tendsto_kB_toReal :
    Tendsto (fun T : Temperature => Constants.kB * T.toReal)
      (nhdsWithin 0 {T : Temperature | 0 < T.toReal})
      (nhdsWithin 0 (Set.Ioi (0 : ℝ))) := by
  have hind : Topology.IsInducing (fun T : Temperature => (T.val : NNReal)) := ⟨rfl⟩
  have hcont : Continuous (fun T : Temperature => Constants.kB * T.toReal) :=
    continuous_const.mul (NNReal.continuous_coe.comp hind.continuous)
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have h0 : Constants.kB * (0 : Temperature).toReal = 0 := by
      simp [Temperature.toReal, show (0 : Temperature).val = (0 : NNReal) from rfl]
    have hle : nhdsWithin (0 : Temperature) {T : Temperature | 0 < T.toReal}
        ≤ nhds (0 : Temperature) := nhdsWithin_le_nhds
    have h := (hcont.tendsto (0 : Temperature)).mono_left hle
    rwa [h0] at h
  · filter_upwards [self_mem_nhdsWithin] with T hT
    exact mul_pos Constants.kB_pos hT

/-- **The equilibrium law of the random-scan Gibbs chain concentrates on the feasible set.**

The probability the chain's unique stationary distribution gives to the infeasible states tends
to zero as the temperature tends to absolute zero from above. Combined with
`stationary_eq_πBoltzVec`, this is the statement that the annealed Boltzmann machine's
equilibrium measure puts all of its mass on the solutions of the QUBO. -/
theorem πBoltzVec_infeasible_tendsto_zero (hW : P.Wf)
    (hfeas : ∃ s : QState P, zeroOneHamiltonian (netParams P) s = minEnergy P) :
    Tendsto (fun T : Temperature =>
        ∑ s ∈ infeasibleStates P,
          (πBoltzVec (NN := TwoState.ZeroOne ℝ (Fin P.nvars)) (spec := zeroOneEnergySpec)
            (p := netParams P) (T := T)).val s)
      (nhdsWithin 0 {T : Temperature | 0 < T.toReal}) (nhds 0) := by
  have h := (infeasible_fraction_tendsto_zero P hW hfeas).comp tendsto_kB_toReal
  refine h.congr fun T => ?_
  exact (πBoltzVec_infeasible_mass P T).symm

/-- **The same statement, phrased on the chain's stationary distribution itself.**

`Classical.choose … .exists` is the unique stationary distribution of the random-scan Gibbs
chain's transition matrix `RSrow` at temperature `T`, the one produced by
`RSrow_exists_unique_stationary_distribution`. The mass it gives to the infeasible states tends
to zero as `T → 0⁺`. This is the composite of Step 1 and Step 2. -/
theorem stationary_infeasible_tendsto_zero (hW : P.Wf)
    (hfeas : ∃ s : QState P, zeroOneHamiltonian (netParams P) s = minEnergy P) :
    Tendsto (fun T : Temperature =>
        ∑ s ∈ infeasibleStates P,
          (Classical.choose
            (RSrow_exists_unique_stationary_distribution
              (NN := TwoState.ZeroOne ℝ (Fin P.nvars)) (spec := zeroOneEnergySpec)
              (p := netParams P) (T := T)).exists).val s)
      (nhdsWithin 0 {T : Temperature | 0 < T.toReal}) (nhds 0) := by
  refine (πBoltzVec_infeasible_tendsto_zero P hW hfeas).congr fun T => ?_
  rw [stationary_eq_πBoltzVec P T]

end Problem
end QUBO
