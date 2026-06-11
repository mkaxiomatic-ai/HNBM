/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import HopfieldNet.Quiver.HN.StochasticQuiv
import Mathlib.Analysis.Normed.Field.Instances
import Mathlib.Data.ENNReal.Basic

set_option maxHeartbeats 1000000

open Finset Matrix NeuralNetwork State

variable {R U : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [Fintype U]
  [Nonempty U] [DecidableEq U] (wθ : Params (HopfieldNetwork R U)) [Coe R ℝ] (T : ℝ)

/-- In a tsum over all neurons, only the neuron where s and s' differ contributes --/
lemma gibbs_single_site_tsum  (s s' : (HopfieldNetwork R U).State)
  (u : U) (h_diff_at_u : s.act u ≠ s'.act u)
  (h_same_elsewhere : ∀ v : U, v ≠ u → s.act v = s'.act v) :
  ∑' (a : U),
    (PMF.ofFintype (fun _ => 1 / ↑(Fintype.card U)) ( uniform_neuron_selection_prob_valid)) a
    * (NN.State.gibbsUpdateSingleNeuron wθ s T a) s' =
  1 / ↑(Fintype.card U) * (NN.State.gibbsUpdateSingleNeuron wθ s T u)
    (NN.State.updateNeuron s u (s'.act u) (s'.hp u)) := by
  have h_upd := single_site_difference_as_update s s' u h_diff_at_u h_same_elsewhere
  rw [tsum_fintype, Finset.sum_eq_single u]
  · simp only [uniform_neuron_selection_prob]; congr 1; exact congrArg _ h_upd
  · intro a _ ha
    exact mul_eq_zero_of_right _ (gibbs_update_zero_other_sites wθ T s s' u a h_same_elsewhere h_diff_at_u ha)
  · intro h; exact absurd (mem_univ u) h

/-- Main lemma for Gibbs transition probability with single site update :
  For a state transition involving change at exactly one site u, the Gibbs transition
  probability is the product of the probability of selecting u and the probability
  of updating u to the new value --/
lemma gibbs_single_site_transition_prob (s s' : (HopfieldNetwork R U).State)
  (u : U) (h_diff_at_u : s.act u ≠ s'.act u)
  (h_same_elsewhere : ∀ v : U, v ≠ u → s.act v = s'.act v) :
  gibbsTransitionProb wθ T s s' =
  ENNReal.toReal (((1 : ENNReal) / (Fintype.card U : ENNReal)) *
  (NN.State.gibbsUpdateSingleNeuron wθ s T u) (NN.State.updateNeuron s u (s'.act u) (s'.hp u))) := by
  dsimp [gibbsTransitionProb]
  simp only [NN.State.gibbsSamplingStep, PMF.bind_apply]
  rw [gibbs_single_site_tsum wθ T s s' u h_diff_at_u h_same_elsewhere]

omit [Coe R ℝ] in
lemma gibbs_transition_sum_single_site
  (wθ : Params (HopfieldNetwork R U)) (T : ℝ) (s s' : (HopfieldNetwork R U).State) [Coe R ℝ]
  (u : U) (h_same_elsewhere : ∀ v : U, v ≠ u → s.act v = s'.act v)
  (h_diff : s.act u ≠ s'.act u) :
  ∑' (a : U), ((1 : ENNReal) / (Fintype.card U : ENNReal)) * -- Use ENNReal probability
    (NN.State.gibbsUpdateSingleNeuron wθ s T a) s' =
  ((1 : ENNReal) / (Fintype.card U : ENNReal)) * (NN.State.gibbsUpdateSingleNeuron wθ s T u) s' := by
  have h := gibbs_single_site_tsum wθ T s s' u h_diff h_same_elsewhere
  rw [← single_site_difference_as_update s s' u h_diff h_same_elsewhere] at h
  exact h

lemma gibbs_update_single_neuron_formula (s : (HopfieldNetwork R U).State)
  (u : U) (val : R) (hval : (HopfieldNetwork R U).pact val) :
  let local_field := s.net wθ u
  let Z := ENNReal.ofReal (Real.exp (local_field / T)) + ENNReal.ofReal (Real.exp (-local_field / T))
  (NN.State.gibbsUpdateSingleNeuron wθ s T u) (NN.State.updateNeuron s u val hval) =
    if val = 1 then ENNReal.ofReal (Real.exp (local_field / T)) / Z
    else ENNReal.ofReal (Real.exp (-local_field / T)) / Z :=
  gibbs_update_single_neuron_prob wθ s T u val hval

omit [Coe R ℝ] in
lemma gibbs_single_site_transition_explicit
  (s s' : (HopfieldNetwork R U).State) [Coe R ℝ]
  (u : U) (h_same_elsewhere : ∀ v : U, v ≠ u → s.act v = s'.act v)
  (_ : θ' (wθ.θ u) = 0) (_ : T > 0) (h_neq : s ≠ s') :
  gibbsTransitionProb wθ T s s' =
    (1 / (Fintype.card U : ℝ)) * ENNReal.toReal (
      let local_field := s.net wθ u
      let Z := ENNReal.ofReal (Real.exp (local_field / T)) + ENNReal.ofReal (Real.exp (-local_field / T))
      if s'.act u = 1 then
        ENNReal.ofReal (Real.exp (local_field / T)) / Z
      else
        ENNReal.ofReal (Real.exp (-local_field / T)) / Z
    ) :=
by
  have h_diff : s.act u ≠ s'.act u := by
    intro contra
    exact h_neq (NeuralNetwork.ext fun v => if hv : v = u then by rw [hv]; exact contra else h_same_elsewhere v hv)
  rw [gibbs_single_site_transition_prob wθ T s s' u h_diff h_same_elsewhere]
  rw [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_one]
  congr 1
  exact congrArg ENNReal.toReal (gibbs_update_single_neuron_formula wθ T s u (s'.act u) (s'.hp u))

/-- Multi-site transitions have zero probability --/
lemma gibbsUpdateSingleNeuron_support
  (s s' : (HopfieldNetwork R U).State) (u : U) :
  s' ∈ (NN.State.gibbsUpdateSingleNeuron wθ s T u).support →
  s' = NN.State.updateNeuron s u 1 (Or.inl rfl) ∨
  s' = NN.State.updateNeuron s u (-1) (Or.inr rfl) := by
  intro h
  rw [PMF.mem_support_iff] at h
  exact gibbsUpdate_possible_states wθ s T u s' ((PMF.apply_pos_iff _ s').mpr h)

omit [Coe R ℝ] in
lemma gibbsUpdateSingleNeuron_prob_zero_if_not_update [Coe R ℝ] (T : ℝ)
  (s s' : (HopfieldNetwork R U).State) (u : U) :
  ¬(s' = NN.State.updateNeuron s u 1 (Or.inl rfl) ∨
    s' = NN.State.updateNeuron s u (-1) (Or.inr rfl)) →
  (NN.State.gibbsUpdateSingleNeuron wθ s T u) s' = 0 := by
  intro h
  rw [PMF.apply_eq_zero_iff]
  exact fun h' => h (gibbsUpdateSingleNeuron_support wθ T s s' u h')

lemma gibbsSamplingStep_prob_zero_if_multi_site (s s' : (HopfieldNetwork R U).State) :
  (¬∃ u : U, ∀ v : U, v ≠ u → s.act v = s'.act v) →
  (NN.State.gibbsSamplingStep wθ s T) s' = 0 := by
  intro h
  unfold NN.State.gibbsSamplingStep
  simp only [PMF.bind_apply] -- Use the definition of PMF.bind
  rw [ENNReal.tsum_eq_zero]
  intro u
  refine mul_eq_zero_of_right _ ?_
  apply gibbsUpdateSingleNeuron_prob_zero_if_not_update
  intro h'
  apply h
  rcases h' with h1 | h2
  · exact ⟨u, fun v hv => by rw [h1]; exact (updateNeuron_preserves s u v 1 (Or.inl rfl) hv).symm⟩
  · exact ⟨u, fun v hv => by rw [h2]; exact (updateNeuron_preserves s u v (-1) (Or.inr rfl) hv).symm⟩

-- Main lemma
lemma gibbs_multi_site_transition (s s' : (HopfieldNetwork R U).State) :
  (¬∃ u : U, ∀ v : U, v ≠ u → s.act v = s'.act v) →
  gibbsTransitionProb wθ T s s' = 0 := by
  intro h
  unfold gibbsTransitionProb
  exact congrArg ENNReal.toReal (gibbsSamplingStep_prob_zero_if_multi_site wθ T s s' h)
