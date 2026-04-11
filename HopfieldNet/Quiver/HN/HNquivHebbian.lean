/-
Copyright (c) 2025 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import HopfieldNet.Quiver.HN.Core

set_option linter.unusedVariables false
set_option maxHeartbeats 500000

open Mathlib Finset

open Finset Matrix NeuralNetwork State Fintype

variable {R U : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [DecidableEq U] [Fintype U]
 [Nonempty U]

/--
Defines the Hebbian learning rule for a Hopfield Network.

Given a set of patterns `ps`, this function returns the network parameters
using the Hebbian learning rule, which adjusts weights based on pattern correlations.
-/
def Hebbian {m : ℕ} (ps : Fin m → (HopfieldNetwork R U).State) : Params (HopfieldNetwork R U) where
  /- The weight matrix, calculated as the sum of the outer products of the patterns minus
      a scaled identity matrix. -/
  w := ∑ k, outerProduct (ps k) (ps k) - (m : R) • (1 : Matrix U U R)
  /- The threshold function, which is set to a constant value of 0 for all units. -/
  θ u := ⟨#[0], rfl⟩
  /- The state function, which is set to an empty vector. -/
  σ _ := Vector.emptyWithCapacity 0
  h_arrows := by
    intros u v f
    trivial
  /- A proof that the weight matrix is symmetric and satisfies the Hebbian learning rule. -/
  hw u v huv := by
    simp only [sub_apply, smul_apply, smul_eq_mul]
    rw [Finset.sum_apply, Finset.sum_apply]
    have : ∀ k i, (ps k).act i * (ps k).act i = 1 := by
      intros k i ; rw [mul_self_eq_one_iff.mpr]; exact act_one_or_neg_one i
    have huv' : u = v :=
      HopfieldNetwork.eq_of_not_pwMat (R := R) (U := U) u v huv
    subst huv'
    conv => enter [1, 1, 2];
    simp only [this, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, one_apply_eq,
      sub_self]
  hw' := by
    simp only [Matrix.IsSymm,transpose_sub, transpose_smul, transpose_one, sub_left_inj]
    rw [isSymm_sum]
    intro k
    refine IsSymm.ext_iff.mpr (fun i j => CommMonoid.mul_comm ((ps k).act j) ((ps k).act i))


lemma patterns_pairwise_orthogonal {m : ℕ}  (ps : Fin m → (HopfieldNetwork R U).State)
  (horth : ∀ {i j : Fin m} (_ : i ≠ j), dotProduct (ps i).act (ps j).act = 0) :
  ∀ (j : Fin m), ((Hebbian ps).w).mulVec (ps j).act = (card U - m) * (ps j).act := by
  intros k
  ext t
  rw [Hebbian, mulVec, dotProduct]
  simp only [sub_apply, smul_apply, smul_eq_mul, Pi.natCast_def, Pi.mul_apply, Pi.sub_apply]
  rw [Finset.sum_apply]
  simp only [Finset.sum_apply]
  unfold dotProduct at horth
  have : ∀ i j, (dotProduct (ps i).act (ps j).act) = if i ≠ j then 0 else card U := fun i j ↦ by
    by_cases h : i ≠ j
    · specialize horth h
      simp_all only [ne_eq, not_false_eq_true, reduceIte, Nat.cast_zero]
      assumption
    · simp only [Decidable.not_not] at h
      nth_rw 1 [h]
      simp only [ite_not, Nat.cast_ite, Nat.cast_zero]
      refine eq_ite_iff.mpr ?_; left
      refine ⟨by assumption, ?_⟩
      · have hact1 : ∀ i, ((ps j).act i) * ((ps j).act i) = 1 := fun i ↦ mul_self_eq_one_iff.mpr (act_one_or_neg_one i)
        calc _ = ∑ i, (ps j).act i * (ps j).act i := rfl
             _ = ∑ i, 1 * 1 := by simp_rw [hact1]; rw [mul_one]
             _ = card U := by simp only [sum_const, card_univ, nsmul_eq_mul, mul_one]
  simp only [dotProduct, ite_not, Nat.cast_ite, Nat.cast_zero] at this
  conv => enter [1,2]; ext l; rw [sub_mul]; rw [sum_mul]; conv => enter [1,2]; ext i; rw [mul_assoc]
  rw [Finset.sum_sub_distrib]; nth_rw 1 [sum_comm]
  calc _= ∑ y : Fin m, (ps y).act t * ∑ x , ((ps y).act x * (ps k).act x)
          - ∑ x , ↑m * (1 : Matrix U U R) t x * (ps k).act x := ?_
       _= ∑ y : Fin m, (ps y).act t *  (if y ≠ k then 0 else card U) -
            ∑ x , ↑m * (1 : Matrix U U R) t x * (ps k).act x := ?_
       _ = (card U - ↑m) * (ps k).act t  := ?_
  · simp only [sub_left_inj]; rw [Finset.sum_congr rfl]
    exact fun x _ ↦ (mul_sum univ (fun i ↦ (ps x).act i * (ps k).act i) ((ps x).act t)).symm
  · simp only [sub_left_inj]; rw [Finset.sum_congr rfl]; intros i _
    simp_all only [reduceIte, implies_true, mem_univ, mul_ite, mul_zero, ite_not, Nat.cast_ite, Nat.cast_zero]
  · simp only [ite_not, Nat.cast_ite, Nat.cast_zero, mul_ite, mul_zero, Finset.sum_ite_eq', mem_univ, reduceIte]
    conv => enter [1,2,2]; ext k; rw [mul_assoc]
    rw [← mul_sum, mul_comm]
    simp only [one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, mem_univ, reduceIte]
    exact (sub_mul (card U : R) m ((ps k).act t)).symm

lemma stateisStablecondition {m : ℕ} (ps : Fin m → (HopfieldNetwork R U).State)
  (s : (HopfieldNetwork R U).State) c (hc : 0 < c)
  (hw : ∀ u, ((Hebbian ps).w).mulVec s.act u = c * s.act u) : s.isStable (Hebbian ps) := by
  intros u
  unfold Up net out
  simp only [reduceIte, Fin.isValue]
  rw [HNfnet_eq]
  simp_rw [mulVec, dotProduct] at hw u
  refine ite_eq_iff.mpr ?_
  cases' s.act_one_or_neg_one u with h1 h2
  · left; rw [h1]; constructor
    · rw [hw, le_iff_lt_or_eq]; left; rwa [h1, mul_one]
    · rfl
  · right; rw [h2]; constructor
    · change ¬ 0 ≤ _
      rw [le_iff_lt_or_eq]
      simp only [not_or, not_lt]
      constructor
      · rw [le_iff_lt_or_eq]; left;
        simpa only [hw, h2, mul_neg, mul_one, Left.neg_neg_iff]
      · simp_all only [mul_neg, mul_one, zero_eq_neg]
        exact ne_of_gt hc
    · rfl
  exact (Hebbian ps).hw u u fun a => by simp at a

lemma hebbian_stable_orthogonal {m : ℕ} (hm : m < card U) (ps : Fin m → (HopfieldNetwork R U).State)
    (j : Fin m) (horth : ∀ {i j : Fin m} (_ : i ≠ j), dotProduct (ps i).act (ps j).act = 0):
  isStable (Hebbian ps) (ps j) := by
  unfold isStable
  have hmn0 : 0 < (card U - m : R) := by simpa only [sub_pos, Nat.cast_lt]
  apply stateisStablecondition ps (ps j) (card U - m) hmn0
  · have := patterns_pairwise_orthogonal ps horth j
    intros u; rw [funext_iff] at this; exact (this) u

lemma dotProduct_act_self (s : (HopfieldNetwork R U).State) : dotProduct s.act s.act = card U := by
  have hsq : ∀ u : U, s.act u * s.act u = (1 : R) := fun u ↦ by
    simpa using (mul_self_eq_one_iff.mpr (s.act_one_or_neg_one u))
  simp [dotProduct, hsq, sum_const, card_univ, nsmul_eq_mul]

/-- Disturbance term for non-orthogonal patterns. -/
def disturbanceTerm {m : ℕ}  (ps : Fin m → (HopfieldNetwork R U).State) (j : Fin m) : U → R :=
  fun u ↦ ∑ i : Fin m, if i ≠ j then (ps i).act u * dotProduct (ps i).act (ps j).act else 0

/-- Full perturbed Hopfield update -/
def perturbedHopfieldUpdate {m : ℕ} (ps : Fin m → (HopfieldNetwork R U).State) (j : Fin m) : U → R :=
  fun u ↦ (card U - m : R) * (ps j).act u + disturbanceTerm ps j u

set_option maxHeartbeats 2000000 in
theorem outerProduct_sum_mulVec_apply {m : ℕ} (ps : Fin m → (HopfieldNetwork R U).State) (t : U) (pj : U → R) :
    ((∑ i, outerProduct (ps i) (ps i)) *ᵥ pj) t = ∑ i, (ps i).act t * (ps i).act ⬝ᵥ pj := by
  --rw [mulVec, Finset.sum_apply]
  simp [mulVec, dotProduct]
  calc  _ = ∑ x : U, ∑ i : Fin m, ((ps i).act t * (ps i).act x) * pj x := ?_
        _ = ∑ i : Fin m, ∑ x : U, ((ps i).act t * (ps i).act x) * pj x := Finset.sum_comm
        _ = ∑ i : Fin m, (ps i).act t * ∑ x : U, (ps i).act x * pj x := ?_
        _ = ∑ i : Fin m, (ps i).act t * dotProduct (ps i).act pj := by simp [dotProduct]
  · refine Finset.sum_congr rfl (fun x _ ↦ ?_)
    unfold outerProduct
    have:= (Finset.sum_mul (s := (Finset.univ : Finset (Fin m)))
      (f := fun i : Fin m ↦ (ps i).act t * (ps i).act x) (a := pj x))
    rw [← this]
    simp only [mul_eq_mul_right_iff]
    left
    rw [Finset.sum_apply];rw [Finset.sum_apply]
  · refine Finset.sum_congr rfl (fun i _ ↦ ?_)
    simpa [dotProduct, mul_assoc] using (mul_sum (s := (Finset.univ : Finset U))
      (f := fun x : U ↦ (ps i).act x * pj x) (a := (ps i).act t)).symm

theorem hebbian_mulVec_apply {m : ℕ} (ps : Fin m → (HopfieldNetwork R U).State) (t : U) (pj : U → R) :
      ((Hebbian ps).w).mulVec pj t = ∑ i, (ps i).act t * (ps i).act ⬝ᵥ pj - ↑m * pj t := by
  unfold Hebbian
  have hsub : ((∑ i : Fin m, outerProduct (ps i) (ps i) - (m : R) • (1 : Matrix U U R)).mulVec pj) =
    (∑ i : Fin m, outerProduct (ps i) (ps i)).mulVec pj - ((m : R) • (1 : Matrix U U R)).mulVec pj := by
    simpa [Matrix.mulVec] using
      (sub_mulVec (A := (∑ i : Fin m, outerProduct (ps i) (ps i))) (B := (m : R) • (1 : Matrix U U R)) (x := pj))
  have hsmul : ((m : R) • (1 : Matrix U U R)).mulVec pj = (m : R) • ((1 : Matrix U U R).mulVec pj) := by
    simpa [Matrix.mulVec] using
        (smul_mulVec (b := (m : R)) (M := (1 : Matrix U U R)) (v := pj))
  have h_diag : (((m : R) • (1 : Matrix U U R)).mulVec pj) t = (m : R) * pj t := by
    simp [hsmul, Pi.smul_apply, smul_eq_mul]
  have hsub_t := congrArg (fun v ↦ v t) hsub
  simpa [Pi.sub_apply, outerProduct_sum_mulVec_apply (ps := ps) (t := t) (pj := pj), h_diag] using hsub_t

/-- `patterns_pairwise_non_orthogonal` is the standard
“signal + crosstalk” decomposition for the Hebbian weight matrix built from a
family of (not necessarily orthogonal) patterns `ps`.
In particular, when the patterns are pairwise orthogonal, the disturbance term vanishes and
the field reduces to the pure signal term.
-/
lemma patterns_pairwise_non_orthogonal {m : ℕ} (ps : Fin m → (HopfieldNetwork R U).State) (j : Fin m) :
  ((Hebbian ps).w).mulVec (ps j).act = (card U - m : R) • (ps j).act + disturbanceTerm ps j := by
  ext t
  let pj : U → R := (ps j).act
  have h_field : ((Hebbian ps).w).mulVec pj t =
    (∑ i : Fin m, (ps i).act t * dotProduct (ps i).act pj) - (m : R) * pj t := by
      rw [hebbian_mulVec_apply ps t pj]
  set f : Fin m → R := fun i ↦ (ps i).act t * dotProduct (ps i).act pj
  have h_self : dotProduct pj pj = card U := by simpa [pj] using (dotProduct_act_self (s := ps j))
  have h_filter : (∑ i ∈ (Finset.univ.erase j), f i) = ∑ i : Fin m, if i ≠ j then f i else 0 := by
    simpa [filter_erase_equiv] using
      (Finset.sum_filter (s := (Finset.univ : Finset (Fin m))) (p := fun i ↦ i ≠ j) (f := f))
  have h_sig_int : (∑ i : Fin m, f i) - (m : R) * pj t =
     ((card U - m : R) * pj t) + (∑ i : Fin m, if i ≠ j then f i else 0) := by
    calc _= (f j + ∑ i ∈ (Finset.univ.erase j), f i) - (m : R) * pj t := by simp
         _ = (pj t * (card U : R) + ∑ i ∈ (Finset.univ.erase j), f i) - (m : R) * pj t := by simp [f, h_self, pj]
         _ = ((card U - m : R) * pj t) + ∑ i ∈ (Finset.univ.erase j), f i := by ring_nf
         _ = ((card U - m : R) * pj t) + (∑ i : Fin m, if i ≠ j then f i else 0) := by simp [h_filter]
  simp [h_field, h_sig_int, f, pj, disturbanceTerm, Pi.add_apply, Pi.smul_apply, smul_eq_mul, sub_eq_add_neg]
