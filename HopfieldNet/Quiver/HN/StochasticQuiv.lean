/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import HopfieldNet.Quiver.NeuralNetwork.Stochastic
import HopfieldNet.Quiver.HN.StochasticAuxQuiv

/-!
# Stochastic Hopfield networks

Gibbs and Metropolis–Hastings updates, simulated annealing, and supporting probability lemmas.
-/

open Finset Matrix NeuralNetwork State

variable {R U : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [DecidableEq U] [Fintype U] [Nonempty U] (wθ : Params (HopfieldNetwork R U)) (s : (HopfieldNetwork R U).State)
  [Coe R ℝ] (T : ℝ)

instance : Coe ℝ ℝ := ⟨id⟩

/-- The total normalization constant for Gibbs sampling is positive. -/
lemma gibbs_total_positive (local_field : ℝ) (T : ℝ) :
    let probs : Bool → ENNReal := fun b =>
      let new_act_val := if b then 1 else -1
      ENNReal.ofReal (Real.exp (local_field * new_act_val / T))
    probs true + probs false ≠ 0 := by
  intro probs h
  exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne' (add_eq_zero.mp h).1

/-- The total normalization constant for Gibbs sampling is not infinity. -/
lemma gibbs_total_not_top (local_field : ℝ) (T : ℝ) :
    let probs : Bool → ENNReal := fun b =>
      let new_act_val := if b then 1 else -1
      ENNReal.ofReal (Real.exp (local_field * new_act_val / T))
    probs true + probs false ≠ ⊤ := by
  intro probs
  simp only [mul_ite, mul_one, mul_neg, ↓reduceIte, Bool.false_eq_true, ne_eq, ENNReal.add_eq_top,
    ENNReal.ofReal_ne_top, or_self, not_false_eq_true, probs]

/-- Normalized binary Boltzmann probabilities over `Bool` sum to `1`. -/
lemma pmf_binary_norm_sum_one (local_field : ℝ) (T : ℝ) :
    let probs : Bool → ENNReal := fun b =>
      let new_act_val := if b then 1 else -1
      ENNReal.ofReal (Real.exp (local_field * new_act_val / T))
    let total := probs true + probs false
    let norm_probs := fun b => probs b / total
    ∑ b : Bool, norm_probs b = 1 := by
  intro probs total norm_probs
  rw [Fintype.sum_bool, ENNReal.div_add_div_same,
    ENNReal.div_self (gibbs_total_positive local_field T) (gibbs_total_not_top local_field T)]

/-- For Gibbs updates, normalized probabilities over `Bool` sum to `1`. -/
lemma gibbs_probs_sum_one (v : U) :
    let local_field := s.net wθ v
    let probs : Bool → ENNReal := fun b =>
      let new_act_val := if b then 1 else -1
      ENNReal.ofReal (Real.exp (local_field * new_act_val / T))
    let total := probs true + probs false
    let norm_probs := fun b => probs b / total
    ∑ b : Bool, norm_probs b = 1 := by
  intro local_field probs total norm_probs
  rw [Fintype.sum_bool, ENNReal.div_add_div_same,
    ENNReal.div_self (gibbs_total_positive (↑local_field) T) (gibbs_total_not_top (↑local_field) T)]

lemma gibbs_Z_total_ne_zero (local_field : ℝ) (T : ℝ) :
    let Z := ENNReal.ofReal (Real.exp (local_field / T)) +
      ENNReal.ofReal (Real.exp (-local_field / T))
    Z ≠ 0 := by
  intro Z h
  exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne' (add_eq_zero.mp h).1

lemma gibbs_Z_total_ne_top (local_field : ℝ) (T : ℝ) :
    let Z := ENNReal.ofReal (Real.exp (local_field / T)) +
      ENNReal.ofReal (Real.exp (-local_field / T))
    Z ≠ ⊤ := by
  intro Z
  simp [Z, ENNReal.add_eq_top, ENNReal.ofReal_ne_top]

/-- Normalized Gibbs probabilities in partition-function form sum to `1`. -/
lemma gibbs_Z_norm_probs_sum_one (local_field : ℝ) (T : ℝ) :
    let Z := ENNReal.ofReal (Real.exp (local_field / T)) +
      ENNReal.ofReal (Real.exp (-local_field / T))
    let norm_probs := fun b =>
      if b then
        ENNReal.ofReal (Real.exp (local_field / T)) / Z
      else
        ENNReal.ofReal (Real.exp (-local_field / T)) / Z
    ∑ b : Bool, norm_probs b = 1 := by
  intro Z norm_probs
  simp only [norm_probs, Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte]
  rw [ENNReal.div_add_div_same]
  exact ENNReal.div_self (gibbs_Z_total_ne_zero local_field T) (gibbs_Z_total_ne_top local_field T)

/-- Performs a Gibbs update on a single neuron `u` of the state `s`.
The update probability depends on the energy change associated with flipping the neuron's state,
parameterized by the temperature `T`. -/
noncomputable def NN.State.gibbsUpdateNeuron [Coe R ℝ] (T : ℝ) (u : U) : PMF ((HopfieldNetwork R U).State) :=
  let h_u := s.net wθ u
  let ΔE := 2 * h_u * s.act u
  let p_flip := ENNReal.ofReal (Real.exp (-(↑ΔE) / T)) / (1 + ENNReal.ofReal (Real.exp (-(↑ΔE) / T)))
  let p_flip_le_one : p_flip ≤ 1 := by
    simp only [p_flip]
    let a := ENNReal.ofReal (Real.exp (-(↑ΔE) / T))
    rw [ENNReal.div_le_iff (by simp [add_eq_zero, one_ne_zero, ENNReal.ofReal_eq_zero])
      (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.ofReal_ne_top⟩)]
    simp only [one_mul]
    exact le_add_self
  PMF.bind (PMF.bernoulli p_flip.toNNReal (by
    exact ENNReal.toNNReal_mono (by simp [ENNReal.one_ne_top]) p_flip_le_one
  )) fun should_flip =>
    PMF.pure <| if should_flip then s.Up wθ u else s

/-- Update a single neuron according to the Gibbs sampling rule. -/
noncomputable def NN.State.gibbsUpdateSingleNeuron (u : U) : PMF ((HopfieldNetwork R U).State) :=
  let local_field := s.net wθ u
  let probs : Bool → ENNReal := fun b =>
    let new_act_val := if b then 1 else -1
    ENNReal.ofReal (Real.exp (local_field * new_act_val / T))
  let total : ENNReal := probs true + probs false
  let norm_probs : Bool → ENNReal := fun b => probs b / total
  PMF.map (fun b =>
      if b then
        NN.State.updateNeuron s u 1 hopfield_pact_one
      else
        NN.State.updateNeuron s u (-1) hopfield_pact_neg_one)
    (PMF.ofFintype norm_probs (gibbs_probs_sum_one wθ s T u))

/-- Given a Hopfield Network's parameters, temperature, and current state, performs a single step
of Gibbs sampling by:
1. Uniformly selecting a random neuron
2. Updating that neuron's state according to the Gibbs distribution -/
noncomputable def NN.State.gibbsSamplingStep : PMF ((HopfieldNetwork R U).State) :=
  let neuron_pmf : PMF U :=
    PMF.ofFintype (fun _ => (1 : ENNReal) / (Fintype.card U : ENNReal)) uniform_neuron_selection_prob_valid
  PMF.bind neuron_pmf fun u => NN.State.gibbsUpdateSingleNeuron wθ s T u

/-- Perform a stochastic update on a Pattern representation. -/
noncomputable def patternStochasticUpdate
    {n : ℕ} [Nonempty (Fin n)] (weights : Fin n → Fin n → ℝ) (h_diag_zero : ∀ i : Fin n, weights i i = 0)
    (h_sym : ∀ i j : Fin n, weights i j = weights j i) (T : ℝ)
    (pattern : NeuralNetwork.State (HopfieldNetwork ℝ (Fin n))) (i : Fin n) :
    PMF (NeuralNetwork.State (HopfieldNetwork ℝ (Fin n))) :=
  let wθ : Params (HopfieldNetwork ℝ (Fin n)) := {
    h_arrows := fun _ _ _ => trivial
    w := weights,
    hw := fun u v h => by
      if h_eq : u = v then
        rw [h_eq]
        exact h_diag_zero v
      else
        exfalso
        have hu : u ≠ v := h_eq
        exact h ⟨PLift.up hu, trivial⟩
    hw' := IsSymm.ext_iff.mpr fun i j ↦ h_sym j i
    σ := fun u => Vector.mk (Array.replicate ((HopfieldNetwork ℝ (Fin n)).κ1 u) (0 : ℝ)) rfl,
    θ := fun u => Vector.mk (Array.replicate ((HopfieldNetwork ℝ (Fin n)).κ2 u) (0 : ℝ)) rfl }
  NN.State.gibbsUpdateSingleNeuron wθ pattern T i

/-- Performs multiple steps of Gibbs sampling in a Hopfield network. -/
noncomputable def NN.State.gibbsSamplingSteps (steps : ℕ) : PMF ((HopfieldNetwork R U).State) :=
  match steps with
  | 0 => PMF.pure s
  | steps + 1 => PMF.bind (gibbsSamplingSteps steps) fun s' =>
      NN.State.gibbsSamplingStep wθ s' T

/-- Temperature schedule for simulated annealing that decreases exponentially with each step. -/
noncomputable def temperatureSchedule (initial_temp : ℝ) (cooling_rate : ℝ) (step : ℕ) : ℝ :=
  initial_temp * Real.exp (-cooling_rate * step)

/-- Recursively applies Gibbs sampling steps with decreasing temperature. -/
noncomputable def applyAnnealingSteps (temp_schedule : ℕ → ℝ) (steps : ℕ)
    (step : ℕ) (state : (HopfieldNetwork R U).State) : PMF ((HopfieldNetwork R U).State) :=
  if h : step ≥ steps then
    PMF.pure state
  else
    PMF.bind (NN.State.gibbsSamplingStep wθ state (temp_schedule step))
      (applyAnnealingSteps temp_schedule steps (step + 1))
termination_by steps - step
decreasing_by
  rw [Nat.sub_succ]
  simp only [Nat.pred_eq_sub_one, tsub_lt_self_iff, tsub_pos_iff_lt, Nat.lt_one_iff, pos_of_gt]
  exact ⟨not_le.mp h, trivial⟩

/-- Simulated annealing for a Hopfield network. -/
noncomputable def NN.State.simulatedAnnealing
    (initial_temp : ℝ) (cooling_rate : ℝ) (steps : ℕ)
    (initial_state : (HopfieldNetwork R U).State) : PMF ((HopfieldNetwork R U).State) :=
  let temp_schedule := temperatureSchedule initial_temp cooling_rate
  applyAnnealingSteps wθ temp_schedule steps 0 initial_state

/-- Metropolis-Hastings acceptance probability between two states. -/
noncomputable def NN.State.acceptanceProbability
    (current : (HopfieldNetwork R U).State) (proposed : (HopfieldNetwork R U).State) : ℝ :=
  let energy_diff := proposed.E wθ - current.E wθ
  if energy_diff ≤ 0 then 1.0 else Real.exp (-energy_diff / T)

/-- The partition function for a Hopfield network. -/
noncomputable def NN.State.partitionFunction : ℝ :=
  ∑ s : (HopfieldNetwork R U).State, Real.exp (-s.E wθ / T)

/-- Metropolis-Hastings single step for Hopfield networks. -/
noncomputable def NN.State.metropolisHastingsStep : PMF ((HopfieldNetwork R U).State) :=
  let neuron_pmf : PMF U :=
    PMF.ofFintype (fun _ => (1 : ENNReal) / (Fintype.card U : ENNReal)) uniform_neuron_selection_prob_valid
  let propose : U → PMF ((HopfieldNetwork R U).State) := fun u =>
    let flipped_state :=
      if s.act u = 1 then
        NN.State.updateNeuron s u (-1) hopfield_pact_neg_one
      else
        NN.State.updateNeuron s u 1 hopfield_pact_one
    let p := NN.State.acceptanceProbability wθ T s flipped_state
    PMF.bind (NN.State.metropolisDecision p) fun accept =>
      if accept then PMF.pure flipped_state else PMF.pure s
  PMF.bind neuron_pmf propose

/-- Multiple steps of Metropolis-Hastings algorithm for Hopfield networks. -/
noncomputable def NN.State.metropolisHastingsSteps (steps : ℕ) : PMF ((HopfieldNetwork R U).State) :=
  match steps with
  | 0 => PMF.pure s
  | steps + 1 => PMF.bind (metropolisHastingsSteps steps) fun s' =>
      NN.State.metropolisHastingsStep wθ s' T

/-- The Boltzmann (Gibbs) distribution over neural network states. -/
noncomputable def boltzmannDistribution : (HopfieldNetwork R U).State → ℝ :=
  fun s => Real.exp (-s.E wθ / T) / NN.State.partitionFunction wθ T

/-- The transition probability matrix for Gibbs sampling. -/
noncomputable def gibbsTransitionProb (s s' : (HopfieldNetwork R U).State) : ℝ :=
  ENNReal.toReal ((NN.State.gibbsSamplingStep wθ s) T s')

/-- The transition probability matrix for Metropolis-Hastings. -/
noncomputable def metropolisTransitionProb (s s' : (HopfieldNetwork R U).State) : ℝ :=
  ENNReal.toReal ((NN.State.metropolisHastingsStep wθ s) T s')

/-- Total variation distance between probability distributions. -/
noncomputable def total_variation_distance
    (μ ν : (HopfieldNetwork R U).State → ℝ) : ℝ :=
  (1 / 2) * ∑ s : (HopfieldNetwork R U).State, |μ s - ν s|

/-- Maps boolean values to states in Gibbs sampling. -/
def gibbs_bool_to_state_map (s : (HopfieldNetwork R U).State) (v : U) : Bool → (HopfieldNetwork R U).State :=
  fun b =>
    if b then
      NN.State.updateNeuron s v 1 hopfield_pact_one
    else
      NN.State.updateNeuron s v (-1) hopfield_pact_neg_one

lemma pmf_map_pos_implies_preimage {α β : Type} [Fintype α] [DecidableEq β]
    {p : α → ENNReal} (h_pmf : ∑ a, p a = 1) (f : α → β) (y : β) :
    (PMF.map f (PMF.ofFintype p h_pmf)) y > 0 →
      ∃ x : α, p x > 0 ∧ f x = y := by
  intro h_pos
  rw [PMF.map_apply] at h_pos
  simp only [PMF.ofFintype_apply, tsum_eq_filter_sum] at h_pos
  obtain ⟨x, hx_eq, hx_pos⟩ :=
    (filter_sum_pos_iff_exists_pos (p := p) (f := f) (y := y)).1 h_pos
  exact ⟨x, hx_pos, hx_eq⟩

lemma gibbsUpdate_exists_bool (v : U) (s_next : (HopfieldNetwork R U).State) :
    (NN.State.gibbsUpdateSingleNeuron wθ s T v) s_next > 0 →
      ∃ b : Bool, s_next = gibbs_bool_to_state_map s v b := by
  intro h_prob_pos
  unfold NN.State.gibbsUpdateSingleNeuron at h_prob_pos
  obtain ⟨b, hb_pos, hb_eq⟩ := pmf_map_pos_implies_preimage (gibbs_probs_sum_one wθ s T v)
    (gibbs_bool_to_state_map s v) s_next h_prob_pos
  exact ⟨b, hb_eq.symm⟩

@[simp] lemma gibbsUpdate_possible_states (v : U) (s_next : (HopfieldNetwork R U).State) :
    (NN.State.gibbsUpdateSingleNeuron wθ s T v) s_next > 0 →
      s_next = NN.State.updateNeuron s v 1 hopfield_pact_one ∨
        s_next = NN.State.updateNeuron s v (-1) hopfield_pact_neg_one := by
  intro h_prob_pos
  obtain ⟨b, hb⟩ := gibbsUpdate_exists_bool wθ s T v s_next h_prob_pos
  cases b with
  | true => left; simpa [gibbs_bool_to_state_map] using hb
  | false => right; simpa [gibbs_bool_to_state_map] using hb

@[simp] lemma gibbsUpdate_preserves_other_neurons (v w : U) (h_neq : w ≠ v) :
    ∀ s_next, (NN.State.gibbsUpdateSingleNeuron wθ s T v) s_next > 0 →
      s_next.act w = s.act w := by
  intro s_next h_prob_pos
  rcases gibbsUpdate_possible_states wθ s T v s_next h_prob_pos with h | h
  · rw [h]; exact updateNeuron_preserves s v w 1 hopfield_pact_one h_neq
  · rw [h]; exact updateNeuron_preserves s v w (-1) hopfield_pact_neg_one h_neq

/-- The normalization factor in Gibbs sampling is the sum of Boltzmann factors. -/
lemma gibbs_normalization_factor (local_field : ℝ) (T : ℝ) :
    let probs : Bool → ENNReal := fun b =>
      let new_act_val := if b then 1 else -1
      ENNReal.ofReal (Real.exp (local_field * new_act_val / T))
    let total := probs true + probs false
    total = ENNReal.ofReal (Real.exp (local_field / T)) + ENNReal.ofReal (Real.exp (-local_field / T)) := by
  intro probs total
  simp only [probs, total, ↓reduceIte, mul_one, Bool.false_eq_true, mul_neg]

lemma gibbs_prob_true (local_field : ℝ) (T : ℝ) :
    let probs : Bool → ENNReal := fun b =>
      let new_act_val := if b then 1 else -1
      ENNReal.ofReal (Real.exp (local_field * new_act_val / T))
    let total := probs true + probs false
    let norm_probs := fun b => probs b / total
    norm_probs true = ENNReal.ofReal (Real.exp (local_field / T)) /
      (ENNReal.ofReal (Real.exp (local_field / T)) + ENNReal.ofReal (Real.exp (-local_field / T))) := by
  intro probs total norm_probs
  simp only [norm_probs, probs, total, ↓reduceIte, mul_one, Bool.false_eq_true, mul_neg]

lemma gibbs_prob_false (local_field : ℝ) (T : ℝ) :
    let probs : Bool → ENNReal := fun b =>
      let new_act_val := if b then 1 else -1
      ENNReal.ofReal (Real.exp (local_field * new_act_val / T))
    let total := probs true + probs false
    let norm_probs := fun b => probs b / total
    norm_probs false = ENNReal.ofReal (Real.exp (-local_field / T)) /
      (ENNReal.ofReal (Real.exp (local_field / T)) + ENNReal.ofReal (Real.exp (-local_field / T))) := by
  intro probs total norm_probs
  simp only [norm_probs, probs, total, ↓reduceIte, mul_one, Bool.false_eq_true, mul_neg]

@[simp] lemma ENNReal_exp_ratio_to_sigmoid (x : ℝ) :
    ENNReal.ofReal (Real.exp x) /
        (ENNReal.ofReal (Real.exp x) + ENNReal.ofReal (Real.exp (-x))) =
      ENNReal.ofReal (1 / (1 + Real.exp (-2 * x))) := by
  trans ENNReal.ofReal (Real.exp x / (Real.exp x + Real.exp (-x)))
  · rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_add (Real.exp_pos x).le (Real.exp_pos (-x)).le]
  · exact congrArg ENNReal.ofReal (exp_ratio_to_sigmoid x)

lemma gibbs_prob_positive (local_field : ℝ) (T : ℝ) :
    let probs : Bool → ENNReal := fun b =>
      let new_act_val := if b then 1 else -1
      ENNReal.ofReal (Real.exp (local_field * new_act_val / T))
    let total := probs true + probs false
    ENNReal.ofReal (Real.exp (local_field / T)) / total =
      ENNReal.ofReal (1 / (1 + Real.exp (-2 * local_field / T))) := by
  intro probs total
  simp only [total, probs, ↓reduceIte, mul_one, Bool.false_eq_true, mul_neg]
  convert ENNReal_exp_ratio_to_sigmoid (local_field * (1 / T)) using 1
  · congr 1 <;> field_simp
  · rw [show -2 * (local_field * (1 / T)) = -2 * local_field / T by field_simp]

lemma gibbs_prob_negative (local_field : ℝ) (T : ℝ) :
    let probs : Bool → ENNReal := fun b =>
      let new_act_val := if b then 1 else -1
      ENNReal.ofReal (Real.exp (local_field * new_act_val / T))
    let total := probs true + probs false
    ENNReal.ofReal (Real.exp (-local_field / T)) / total =
      ENNReal.ofReal (1 / (1 + Real.exp (2 * local_field / T))) := by
  intro probs total
  simp only [total, probs, ↓reduceIte, mul_one, Bool.false_eq_true, mul_neg]
  rw [add_comm]
  convert ENNReal_exp_ratio_to_sigmoid (-local_field / T) using 1
  · rw [show -(-local_field / T) = local_field / T by ring]
  · rw [show -2 * (-local_field / T) = 2 * local_field / T by ring]

lemma gibbs_prob_positive_case (u : U) :
    let local_field := s.net wθ u
    let Z := ENNReal.ofReal (Real.exp (local_field / T)) + ENNReal.ofReal (Real.exp (-local_field / T))
    let norm_probs := fun b =>
      if b then
        ENNReal.ofReal (Real.exp (local_field / T)) / Z
      else
        ENNReal.ofReal (Real.exp (-local_field / T)) / Z
    (PMF.map (gibbs_bool_to_state_map s u)
      (PMF.ofFintype norm_probs (gibbs_Z_norm_probs_sum_one local_field T)))
        (NN.State.updateNeuron s u 1 hopfield_pact_one) = norm_probs true := by
  intro local_field Z norm_probs
  exact pmf_map_update_one s u norm_probs (gibbs_Z_norm_probs_sum_one local_field T)

lemma gibbs_prob_negative_case (u : U) :
    let local_field := s.net wθ u
    let Z := ENNReal.ofReal (Real.exp (local_field / T)) + ENNReal.ofReal (Real.exp (-local_field / T))
    let norm_probs := fun b =>
      if b then
        ENNReal.ofReal (Real.exp (local_field / T)) / Z
      else
        ENNReal.ofReal (Real.exp (-local_field / T)) / Z
    (PMF.map (gibbs_bool_to_state_map s u)
      (PMF.ofFintype norm_probs (gibbs_Z_norm_probs_sum_one local_field T)))
        (NN.State.updateNeuron s u (-1) hopfield_pact_neg_one) = norm_probs false := by
  intro local_field Z norm_probs
  exact pmf_map_update_neg_one s u norm_probs (gibbs_Z_norm_probs_sum_one local_field T)

lemma gibbsUpdate_pmf_structure (u : U) :
    let local_field := s.net wθ u
    let probs : Bool → ENNReal := fun b =>
      let new_act_val := if b then 1 else -1
      ENNReal.ofReal (Real.exp (local_field * new_act_val / T))
    let total := probs true + probs false
    let norm_probs := fun b => probs b / total
    ∀ b : Bool,
      (PMF.map (gibbs_bool_to_state_map s u) (PMF.ofFintype norm_probs (gibbs_probs_sum_one wθ s T u)))
          (gibbs_bool_to_state_map s u b) = norm_probs b := by
  intro local_field probs total norm_probs b_bool
  exact pmf_map_binary_state s u b_bool norm_probs (gibbs_probs_sum_one wθ s T u)

lemma gibbsUpdate_prob_positive (u : U) :
    let local_field := s.net wθ u
    let Z := ENNReal.ofReal (Real.exp (local_field / T)) + ENNReal.ofReal (Real.exp (-local_field / T))
    (NN.State.gibbsUpdateSingleNeuron wθ s T u) (NN.State.updateNeuron s u 1 hopfield_pact_one) =
      ENNReal.ofReal (Real.exp (local_field / T)) / Z := by
  intro local_field Z
  unfold NN.State.gibbsUpdateSingleNeuron
  rw [pmf_map_update_one s u _ (gibbs_probs_sum_one wθ s T u)]
  simp [local_field, Z, ↓reduceIte, mul_one, Bool.false_eq_true, mul_neg]

lemma gibbsUpdate_prob_negative (u : U) :
    let local_field := s.net wθ u
    let Z := ENNReal.ofReal (Real.exp (local_field / T)) + ENNReal.ofReal (Real.exp (-local_field / T))
    (NN.State.gibbsUpdateSingleNeuron wθ s T u) (NN.State.updateNeuron s u (-1) hopfield_pact_neg_one) =
      ENNReal.ofReal (Real.exp (-local_field / T)) / Z := by
  intro local_field Z
  unfold NN.State.gibbsUpdateSingleNeuron
  rw [pmf_map_update_neg_one s u _ (gibbs_probs_sum_one wθ s T u)]
  simp [local_field, Z, ↓reduceIte, mul_one, Bool.false_eq_true, mul_neg]

@[simp] lemma gibbs_update_single_neuron_prob (u : U) (new_val : R)
    (hval : (HopfieldNetwork R U).pact new_val) :
    let local_field := s.net wθ u
    let Z := ENNReal.ofReal (Real.exp (local_field / T)) + ENNReal.ofReal (Real.exp (-local_field / T))
    (NN.State.gibbsUpdateSingleNeuron wθ s T u) (NN.State.updateNeuron s u new_val hval) =
      if new_val = 1 then
        ENNReal.ofReal (Real.exp (local_field / T)) / Z
      else
        ENNReal.ofReal (Real.exp (-local_field / T)) / Z := by
  intro local_field Z
  by_cases h_val : new_val = 1
  · rw [if_pos h_val, gibbs_bool_to_state_map_positive s u new_val hval h_val]
    exact gibbsUpdate_prob_positive wθ s T u
  · rw [if_neg h_val, gibbs_bool_to_state_map_negative s u new_val hval (hopfield_value_dichotomy new_val hval h_val)]
    exact gibbsUpdate_prob_negative wθ s T u

lemma gibbs_update_zero_other_sites (s s' : (HopfieldNetwork R U).State)
    (u v : U) (_h : ∀ w : U, w ≠ u → s.act w = s'.act w) (h_diff : s.act u ≠ s'.act u) :
    v ≠ u → (NN.State.gibbsUpdateSingleNeuron wθ s T v) s' = 0 := by
  intro hv
  rw [PMF.apply_eq_zero_iff]
  intro hmem
  rcases gibbsUpdate_possible_states wθ s T v s' ((PMF.apply_pos_iff _ s').mpr hmem) with h1 | h2
  · rw [h1] at h_diff
    exact h_diff ((updateNeuron_preserves s v u 1 hopfield_pact_one (Ne.symm hv)).symm)
  · rw [h2] at h_diff
    exact h_diff ((updateNeuron_preserves s v u (-1) hopfield_pact_neg_one (Ne.symm hv)).symm)

lemma gibbs_transition_sum_simplification (s s' : (HopfieldNetwork R U).State)
    (u : U) (h : ∀ v : U, v ≠ u → s.act v = s'.act v) (h_diff : s.act u ≠ s'.act u) :
    let neuron_pmf : PMF U :=
      PMF.ofFintype (fun _ => (1 : ENNReal) / (Fintype.card U : ENNReal)) uniform_neuron_selection_prob_valid
    let update_prob (v : U) : ENNReal := (NN.State.gibbsUpdateSingleNeuron wθ s T v) s'
    ∑ v ∈ Finset.univ, neuron_pmf v * update_prob v = neuron_pmf u * update_prob u := by
  intro neuron_pmf update_prob
  refine Finset.sum_eq_single u (fun v _ hv => ?_) fun h => ?_
  · rw [show update_prob v = 0 from gibbs_update_zero_other_sites wθ T s s' u v h h_diff hv, mul_zero]
  · exact absurd (mem_univ u) h

@[simp] lemma gibbs_update_preserves_other_sites (v u : U) (hvu : v ≠ u) :
    ∀ s_next, (NN.State.gibbsUpdateSingleNeuron wθ s T v) s_next > 0 → s_next.act u = s.act u := by
  intro s_next h_pos
  rcases gibbsUpdate_possible_states wθ s T v s_next h_pos with h | h
  · rw [h]; exact updateNeuron_preserves s v u 1 hopfield_pact_one (Ne.symm hvu)
  · rw [h]; exact updateNeuron_preserves s v u (-1) hopfield_pact_neg_one (Ne.symm hvu)

@[simp] lemma uniform_neuron_prob {U : Type} [Fintype U] [Nonempty U] (u : U) :
    (1 : ENNReal) / (Fintype.card U : ENNReal) =
      PMF.ofFintype (fun _ : U => (1 : ENNReal) / (Fintype.card U : ENNReal))
        uniform_neuron_selection_prob_valid u := by
  simp [one_div, PMF.ofFintype_apply]
