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
  [Nonempty U]

lemma mul_div_cancel_of_ne_zero {α : Type*} [Field α] (a b : α) (h : b ≠ 0) : a * b / b = a := by
  rw [div_eq_mul_inv, propext (mul_inv_eq_iff_eq_mul₀ h)]

lemma sum_univ_eq_tsum_uniform  :
  Summable (fun (_ : U) => (1 : ℝ) / ↑(Fintype.card U)) ∧
  ∑' (_ : U), (1 : ℝ) / ↑(Fintype.card U) = Finset.sum Finset.univ (fun (_ : U) => (1 : ℝ) / ↑(Fintype.card U)) :=
by
  refine ⟨Summable.of_finite, ?_⟩
  simp [one_div, ne_eq, Nat.cast_eq_zero, Fintype.card_ne_zero, nsmul_eq_mul, mul_inv_cancel₀,
    sum_const, card_univ]

variable [DecidableEq U] (wθ : Params (HopfieldNetwork R U))

/-- When states differ only at site u, the energy terms that involve pairs of sites other than u are equal --/
lemma energy_terms_without_u_equal (s s' : (HopfieldNetwork R U).State)
  (u : U) (h : ∀ v : U, v ≠ u → s.act v = s'.act v) :
  ∑ v1 ∈ univ.erase u, ∑ v2 ∈ {v2 | v2 ≠ v1 ∧ v2 ≠ u}, wθ.w v1 v2 * s'.act v1 * s'.act v2 =
  ∑ v1 ∈ univ.erase u, ∑ v2 ∈ {v2 | v2 ≠ v1 ∧ v2 ≠ u}, wθ.w v1 v2 * s.act v1 * s.act v2 := by
  refine sum_congr rfl fun v1 hv1 => sum_congr rfl fun v2 hv2 => ?_
  simp only [mem_erase, mem_univ, mem_filter, true_and] at hv1 hv2
  rw [← h v1 hv1.1, ← h v2 hv2.2]

/-- The energy difference for terms involving site u when states differ only at u --/
lemma energy_terms_with_u_diff (s s' : (HopfieldNetwork R U).State)
  (u : U) (h : ∀ v : U, v ≠ u → s.act v = s'.act v) :
  ∑ v2 ∈ Finset.filter (fun v2 => v2 ≠ u) univ, wθ.w u v2 * s'.act u * s'.act v2 -
  ∑ v2 ∈ Finset.filter (fun v2 => v2 ≠ u) univ, wθ.w u v2 * s.act u * s.act v2 =
  (s'.act u - s.act u) * (∑ v2 ∈ Finset.filter (fun v2 => v2 ≠ u) univ, wθ.w u v2 * s.act v2) := by
  have hterm (v2 : U) (hv2 : v2 ∈ Finset.filter (fun v2 => v2 ≠ u) univ) :
      wθ.w u v2 * s'.act u * s'.act v2 - wθ.w u v2 * s.act u * s.act v2 =
      (s'.act u - s.act u) * (wθ.w u v2 * s.act v2) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv2; rw [(h v2 hv2).symm]; ring
  rw [← Finset.sum_sub_distrib, sum_congr rfl hterm, Finset.mul_sum]

lemma weight_energy_diff_term_v1_eq_u (s s' : (HopfieldNetwork R U).State)
  (u : U) (h : ∀ v : U, v ≠ u → s.act v = s'.act v) :
  ∑ v2 ∈ filter (fun v2 => v2 ≠ u) univ, (wθ.w u v2 * s'.act u * s'.act v2 - wθ.w u v2 * s.act u * s.act v2) =
  (s'.act u - s.act u) * ∑ v2 ∈ filter (fun v2 => v2 ≠ u) univ, wθ.w u v2 * s.act v2 := by
  have hterm (v2 : U) (hv2 : v2 ∈ filter (fun v2 => v2 ≠ u) univ) :
      wθ.w u v2 * s'.act u * s'.act v2 - wθ.w u v2 * s.act u * s.act v2 =
      (s'.act u - s.act u) * (wθ.w u v2 * s.act v2) := by
    simp only [mem_filter, mem_univ, true_and] at hv2; rw [h v2 hv2]; ring
  rw [sum_congr rfl hterm, mul_sum]

lemma weight_energy_diff_term_v1_ne_u (s s' : (HopfieldNetwork R U).State)
  (u : U) (h : ∀ v : U, v ≠ u → s.act v = s'.act v) :
  ∑ v1 ∈ filter (fun v1 => v1 ≠ u) univ, ∑ v2 ∈ filter (fun v2 => v2 ≠ v1) univ,
    (wθ.w v1 v2 * s'.act v1 * s'.act v2 - wθ.w v1 v2 * s.act v1 * s.act v2) =
  (s'.act u - s.act u) * ∑ v1 ∈ filter (fun v1 => v1 ≠ u) univ, wθ.w v1 u * s.act v1 := by
  simp_rw [filter_ne']
  have hterm : ∀ v1 ∈ univ.erase u,
      ∑ v2 ∈ univ.erase v1, (wθ.w v1 v2 * s'.act v1 * s'.act v2 - wθ.w v1 v2 * s.act v1 * s.act v2) =
      wθ.w v1 u * s.act v1 * (s'.act u - s.act u) := by
    intro v1 hv1
    simp only [mem_erase, mem_univ] at hv1
    rw [h v1 hv1.1, sum_eq_sum_diff_singleton_add (mem_erase.mpr ⟨hv1.1.symm, mem_univ u⟩),
      sdiff_singleton_eq_erase]
    have hz : ∑ v2 ∈ (univ.erase v1).erase u,
        (wθ.w v1 v2 * s'.act v1 * s'.act v2 - wθ.w v1 v2 * s'.act v1 * s.act v2) = 0 := by
      refine sum_eq_zero fun v2 hv2 => ?_
      simp only [mem_erase] at hv2; rw [h v2 hv2.1]; ring
    rw [hz, zero_add]; ring
  have hcomm (v : U) (_ : v ∈ univ.erase u) :
      wθ.w v u * s.act v * (s'.act u - s.act u) =
      (s'.act u - s.act u) * (wθ.w v u * s.act v) := by ring
  rw [sum_congr rfl hterm, sum_congr rfl hcomm, ← mul_sum]

lemma weight_sum_symmetry (s : (HopfieldNetwork R U).State)
  (u : U) (h_symm : ∀ v1 v2 : U, wθ.w v1 v2 = wθ.w v2 v1) :
  ∑ v1 ∈ filter (fun v1 => v1 ≠ u) univ, wθ.w v1 u * s.act v1 =
  ∑ v2 ∈ filter (fun v2 => v2 ≠ u) univ, wθ.w u v2 * s.act v2 := by
  simp_rw [filter_ne']
  refine sum_congr rfl fun v hv => by simp only [mem_erase] at hv; rw [h_symm v u]

lemma weight_energy_sum_split (s s' : (HopfieldNetwork R U).State)
  (u : U) (h : ∀ v : U, v ≠ u → s.act v = s'.act v) (h_symm : ∀ v1 v2 : U, wθ.w v1 v2 = wθ.w v2 v1) :
  ∑ v1 ∈ univ, ∑ v2 ∈ filter (fun v2 => v2 ≠ v1) univ, wθ.w v1 v2 * s'.act v1 * s'.act v2 -
  ∑ v1 ∈ univ, ∑ v2 ∈ filter (fun v2 => v2 ≠ v1) univ, wθ.w v1 v2 * s.act v1 * s.act v2 =
  (s'.act u - s.act u) * (∑ v2 ∈ filter (fun v2 => v2 ≠ u) univ, wθ.w u v2 * s.act v2) * 2 := by
  simp_rw [← sum_sub_distrib, sum_eq_sum_diff_singleton_add (mem_univ u), sdiff_singleton_eq_erase,
    filter_ne']
  have h_term_u : ∑ v2 ∈ univ.erase u,
      (wθ.w u v2 * s'.act u * s'.act v2 - wθ.w u v2 * s.act u * s.act v2) =
      (s'.act u - s.act u) * ∑ v2 ∈ univ.erase u, wθ.w u v2 * s.act v2 := by
    rw [← filter_ne']; exact weight_energy_diff_term_v1_eq_u wθ s s' u h
  have h_sum_not_u : ∑ v1 ∈ univ.erase u, ∑ v2 ∈ univ.erase v1,
      (wθ.w v1 v2 * s'.act v1 * s'.act v2 - wθ.w v1 v2 * s.act v1 * s.act v2) =
      (s'.act u - s.act u) * ∑ v1 ∈ univ.erase u, wθ.w v1 u * s.act v1 := by
    rw [Eq.symm (filter_erase_equiv u)]
    simp_rw [fun v1 => Eq.symm (filter_ne' (s := univ) v1)]
    exact weight_energy_diff_term_v1_ne_u wθ s s' u h
  rw [h_sum_not_u, h_term_u, sum_congr rfl fun v _ => by rw [h_symm v u], ← two_mul]; ring

/-- For a Hopfield network with states differing at a single site, the activation
    at that site is related to the weighted sum of other activations --/
lemma local_field_relation (wθ : Params (HopfieldNetwork R U)) (s : (HopfieldNetwork R U).State) (u : U) :
  s.net wθ u = ∑ v2 ∈ {v2 | v2 ≠ u}, wθ.w u v2 * s.act v2 := by
  simp only [NeuralNetwork.State.net, HopfieldNetwork, HNfnet, NeuralNetwork.State.out, HNfout]

/-- When states differ at a single site, the energy difference in the weight component
    is proportional to the local field and activation difference --/
lemma weight_energy_single_site_diff
  (wθ : Params (HopfieldNetwork R U)) (s s' : (HopfieldNetwork R U).State)
  (u : U) (h : ∀ v : U, v ≠ u → s.act v = s'.act v) :
  s'.Ew wθ - s.Ew wθ = (s.act u - s'.act u) * s.net wθ u := by
  unfold NeuralNetwork.State.Ew NeuralNetwork.State.Wact
  rw [← mul_sub, weight_energy_sum_split wθ s s' u h fun v1 v2 => weight_symmetry wθ v1 v2,
    local_field_relation wθ s u]
  norm_num; ring

/-- When states differ at a single site, the energy difference in the bias component
    is proportional to the activation difference --/
lemma bias_energy_single_site_diff
  (wθ : Params (HopfieldNetwork R U)) (s s' : (HopfieldNetwork R U).State)
  (u : U) (h : ∀ v : U, v ≠ u → s.act v = s'.act v) :
  s'.Eθ wθ - s.Eθ wθ = θ' (wθ.θ u) * (s'.act u - s.act u) := by
  unfold NeuralNetwork.State.Eθ
  rw [← Finset.sum_sub_distrib, sum_eq_add_sum_diff_singleton_of_mem (mem_univ u), sdiff_singleton_eq_erase]
  rw [show ∑ v ∈ univ.erase u, (θ' (wθ.θ v) * s'.act v - θ' (wθ.θ v) * s.act v) = 0 from
    sum_eq_zero fun v hv => by simp only [Finset.mem_erase, Finset.mem_univ] at hv; rw [h v hv.1]; ring,
    add_zero]
  ring

/-- Energy difference for single-site updates with specified bias term.
    This is a general formulation that allows different bias configurations. --/
lemma energy_single_site_diff_with_bias
  (wθ : Params (HopfieldNetwork R U)) (s s' : (HopfieldNetwork R U).State)
  (u : U) (h : ∀ v : U, v ≠ u → s.act v = s'.act v)
  (h_bias : θ' (wθ.θ u) = 1/2 * s.net wθ u) :
  s'.E wθ - s.E wθ = -1/2 * (s'.act u - s.act u) * s.net wθ u := by
    rw [energy_decomposition, energy_decomposition, add_sub_add_comm,
      weight_energy_single_site_diff wθ s s' u h, bias_energy_single_site_diff wθ s s' u h, h_bias]
    ring_nf

lemma energy_single_site_diff
  (wθ : Params (HopfieldNetwork R U)) (s s' : (HopfieldNetwork R U).State)
  (u : U) (h : ∀ v : U, v ≠ u → s.act v = s'.act v)
  (h_bias : θ' (wθ.θ u) = 0) : -- Added hypothesis for standard Hopfield case
  s'.E wθ - s.E wθ = -(s'.act u - s.act u) * s.net wθ u := by
  -- Decompose energy into weight and bias components
  rw [energy_decomposition, energy_decomposition, add_sub_add_comm,
    weight_energy_single_site_diff wθ s s' u h, bias_energy_single_site_diff wθ s s' u h, h_bias]
  ring_nf

lemma single_site_update_eq (s s' : (HopfieldNetwork R U).State) (u : U)
  (h_same_elsewhere : ∀ v : U, v ≠ u → s.act v = s'.act v)
  (h_diff : s.act u ≠ s'.act u) :
  s' = NN.State.updateNeuron s u (s'.act u) (s'.hp u) :=
  single_site_difference_as_update s s' u h_diff h_same_elsewhere

@[simp]
lemma ENNReal.natCast_eq_ofReal (n : ℕ) : (n : ENNReal) = ENNReal.ofReal n := by
  induction n with
  | zero => simp [ENNReal.ofReal]
  | succ n ih =>
    rw [Nat.cast_succ, Nat.cast_succ, ENNReal.ofReal_add, ih, ENNReal.ofReal_one]
    exacts [Nat.cast_nonneg n, by norm_num]
