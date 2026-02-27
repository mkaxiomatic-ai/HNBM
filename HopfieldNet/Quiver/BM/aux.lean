import HopfieldNet.Quiver.NeuralNetwork.TwoState
import HopfieldNet.TSAux
import HopfieldNet.Quiver.NeuralNetwork.toCanonicalEnsemble
import MCMC.DetailedBalanceGen
import Mathlib.Probability.Kernel.Composition.Prod
import PhysLean.StatisticalMechanics.CanonicalEnsemble.Finite

/-! Concrete Hopfield Energy and Fintype Instances
-/

namespace Matrix

open scoped Classical Finset Set BigOperators

variable {ι R} [DecidableEq ι] [CommRing R]

/-- Decomposition of an updated vector as original plus a single–site bump. -/
lemma update_decomp (x : ι → R) (i : ι) (v : R) :
  Function.update x i v =
    fun j => x j + (if j = i then v - x i else 0) := by
  funext j; by_cases hji : j = i
  · subst hji; simp
  · simp [hji]

/-- Auxiliary single–site perturbation (Kronecker bump). -/
def singleBump (i : ι) (δ : R) : ι → R := fun j => if j = i then δ else 0

lemma update_eq_add_bump (x : ι → R) (i : ι) (v : R) :
    Function.update x i v = (fun j => x j + singleBump i (v - x i) j) := by
  simp [singleBump, update_decomp]

variable [Fintype ι]

/-- Column-sum split: separate the i-th term from the rest (unordered finite type). -/
lemma sum_split_at (f : ι → R) (i : ι) :
  (∑ j, f j) = f i + ∑ j ∈ (Finset.univ.erase i), f j := by
  simpa using
    (Finset.sum_eq_add_sum_erase (s := (Finset.univ : Finset ι)) (f := f) (a := i) (by simp))

/-- Quadratic form xᵀ M x written via `mulVec`. -/
def quadraticForm (M : Matrix ι ι R) (x : ι → R) : R := ∑ j, x j * (M.mulVec x) j

/-- Effect of a single-site bump on `mulVec` (only the `i`-th column contributes). -/
lemma mulVec_update_single
  (M : Matrix ι ι R) (x : ι → R) (i : ι) (v : R) :
  ∀ j, (M.mulVec (Function.update x i v)) j
    = (M.mulVec x) j + M j i * (v - x i) := by
  intro j
  unfold Matrix.mulVec dotProduct
  calc
    (∑ k, M j k * Function.update x i v k)
        =
        M j i * Function.update x i v i
          + ∑ k ∈ Finset.univ.erase i, M j k * Function.update x i v k := by
          simpa using
            (sum_split_at (f := fun k => M j k * Function.update x i v k) i)
    _ = M j i * v + ∑ k ∈ Finset.univ.erase i, M j k * x k := by
          -- split into the i-term and the off-i terms
          congr 1
          · simp
          · refine Finset.sum_congr rfl ?_
            intro k hk
            simp [Function.update_of_ne (Finset.mem_erase.mp hk).1]
    _ = (M j i * x i + ∑ k ∈ Finset.univ.erase i, M j k * x k) + M j i * (v - x i) := by
          ring
    _ = (∑ k, M j k * x k) + M j i * (v - x i) := by
          -- rewrite the bracket via the split sum identity
          simpa [add_assoc] using
            congrArg (fun t => t + M j i * (v - x i))
              ((sum_split_at (f := fun k => M j k * x k) i).symm)

/- Raw single–site quadratic form update (no diagonal assumption).
Produces a δ-linear part plus a δ² * M i i remainder term.
  Q(update x i v) - Q x
    = (v - x i) * ((∑ j, x j * M j i) + (M.mulVec x) i)
      + (v - x i)^2 * M i i
-/
lemma quadraticForm_update_point
    (M : Matrix ι ι R) (x : ι → R) (i : ι) (v : R) (j : ι) :
  let δ : R := v - x i
  (Function.update x i v) j * (M.mulVec (Function.update x i v)) j
      - x j * (M.mulVec x) j
    =
    δ * (x j * M j i + (if j = i then (M.mulVec x) i else 0))
      + (δ * δ) * (if j = i then M j i else 0) := by
  intro δ
  have hMv :
      (M.mulVec (Function.update x i v)) j =
        (M.mulVec x) j + M j i * (v - x i) := by
    simpa using
      (mulVec_update_single (M:=M) (x:=x) (i:=i) (v:=v) j : _)
  by_cases hji : j = i
  · have hUpd_i : (Function.update x i v) i = v := by simp
    have hMv_i :
        (M.mulVec (Function.update x i v)) i =
          (M.mulVec x) i + M i i * (v - x i) := by
      simpa [hji] using hMv
    have hOnSite :
        (v * (((M.mulVec x) i) + M i i * (v - x i)) - (x i) * ((M.mulVec x) i))
          =
        (v - x i) * ((x i) * M i i + (M.mulVec x) i)
          + (v - x i) * (v - x i) * M i i := by
      ring
    subst hji
    simp_all only [Function.update_self, ↓reduceIte, δ]
  · have hUpd_off : (Function.update x i v) j = x j := by
      simp [Function.update, hji]
    have hIf1 : (if j = i then (M.mulVec x) i else 0) = 0 := by
      simp [hji]
    have hIf2 : (if j = i then M j i else 0) = 0 := by
      simp [hji]
    have hOffSite :
        (x j) * (((M.mulVec x) j) + M j i * (v - x i))
          - (x j) * ((M.mulVec x) j)
          =
        (v - x i) * ((x j) * M j i) := by
      ring
    simpa [hMv, hUpd_off, hIf1, hIf2, δ] using hOffSite

/-- Core raw single–site quadratic form update
Produces a δ-linear part plus a δ² * M i i remainder term. -/
lemma quadraticForm_update_sum
    (M : Matrix ι ι R) (x : ι → R) (i : ι) (v : R) :
  quadraticForm M (Function.update x i v) - quadraticForm M x
    =
    (v - x i) * ( (∑ j, x j * M j i) + (M.mulVec x) i )
      + (v - x i) * (v - x i) * M i i := by
  set δ : R := v - x i
  have hPoint :=
    quadraticForm_update_point (M:=M) (x:=x) (i:=i) (v:=v)
  have hDiff :
      quadraticForm M (Function.update x i v) - quadraticForm M x
        =
      ∑ j,
        ((Function.update x i v) j * (M.mulVec (Function.update x i v)) j
          - x j * (M.mulVec x) j) := by
    unfold quadraticForm
    simp [Finset.sum_sub_distrib]
  have hExpand :
      (∑ j,
        ((Function.update x i v) j * (M.mulVec (Function.update x i v)) j
          - x j * (M.mulVec x) j))
        =
      ∑ j, (δ * (x j * M j i + if j = i then (M.mulVec x) i else 0)
              + (δ * δ) * (if j = i then M j i else 0)) := by
    refine Finset.sum_congr rfl ?_
    intro j _
    simp [hPoint, δ]
  have hSplit :
      (∑ j, (δ * (x j * M j i + if j = i then (M.mulVec x) i else 0)
              + (δ * δ) * (if j = i then M j i else 0)))
        =
      (∑ j, δ * (x j * M j i + if j = i then (M.mulVec x) i else 0))
        +
      (∑ j, (δ * δ) * (if j = i then M j i else 0)) := by
    simp [Finset.sum_add_distrib]
  have hSum_if1 :
      (∑ j : ι, (if j = i then (M.mulVec x) i else 0))
        = (M.mulVec x) i := by
    have hfilter : (Finset.univ.filter (fun j : ι => j = i)) = {i} := by
      ext j; by_cases hji : j = i <;> simp [hji]
    calc
      (∑ j : ι, (if j = i then (M.mulVec x) i else 0))
          = ∑ j ∈ Finset.univ.filter (fun j => j = i), (M.mulVec x) i := by
              simp_all only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
                Finset.sum_const, Finset.card_singleton, one_smul, δ]
      _ = (M.mulVec x) i := by
              simp [hfilter]
  have hSum_if2 :
      (∑ j : ι, (if j = i then M j i else 0)) = M i i := by
    have hfilter : (Finset.univ.filter (fun j : ι => j = i)) = {i} := by
      ext j; by_cases hji : j = i <;> simp [hji]
    calc
      (∑ j : ι, (if j = i then M j i else 0))
          = ∑ j ∈ Finset.univ.filter (fun j => j = i), M j i := by
              simp_all only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
                Finset.sum_singleton, δ]
      _ = M i i := by
              simp [hfilter]
  have hPart1 :
      (∑ j, δ * (x j * M j i + if j = i then (M.mulVec x) i else 0))
        =
      δ * ((∑ j, x j * M j i) + (M.mulVec x) i) := by
    have :
        (∑ j, δ * (x j * M j i + if j = i then (M.mulVec x) i else 0))
          = δ * ∑ j, (x j * M j i + if j = i then (M.mulVec x) i else 0) := by
          simp [Finset.mul_sum]
    simp [this, Finset.sum_add_distrib, hSum_if1, add_comm, add_left_comm, add_assoc]
  have hPart2 :
      (∑ j, (δ * δ) * (if j = i then M j i else 0))
        = (δ * δ) * M i i := by
    have :
        (∑ j, (δ * δ) * (if j = i then M j i else 0))
          = (δ * δ) * ∑ j, (if j = i then M j i else 0) := by
          simp
    simp [this, hSum_if2]
  calc
    quadraticForm M (Function.update x i v) - quadraticForm M x
        = _ := hDiff
    _ = _ := hExpand
    _ = _ := hSplit
    _ = δ * ((∑ j, x j * M j i) + (M.mulVec x) i)
          + (δ * δ) * M i i := by
          simp_all only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, δ]
    _ = (v - x i) * ( (∑ j, x j * M j i) + (M.mulVec x) i )
        + (v - x i) * (v - x i) * M i i := by
          simp [δ, mul_comm, mul_assoc]

/-- Raw single–site quadratic form update (no diagonal assumption). -/
lemma quadraticForm_update_raw
    (M : Matrix ι ι R) (x : ι → R) (i : ι) (v : R) :
  quadraticForm M (Function.update x i v) - quadraticForm M x
    =
    (v - x i) * ( (∑ j, x j * M j i) + (M.mulVec x) i )
      + (v - x i) * (v - x i) * M i i :=
  quadraticForm_update_sum (M:=M) (x:=x) (i:=i) (v:=v)

/-- Version with only the i-th diagonal entry zero. -/
lemma quadraticForm_update_single_index
    {M : Matrix ι ι R} (i : ι) (hii : M i i = 0)
    (x : ι → R) (v : R) :
  quadraticForm M (Function.update x i v) - quadraticForm M x
    =
  (v - x i) *
    ( (M.mulVec x) i
      + ∑ j ∈ (Finset.univ.erase i), x j * M j i ) := by
  have hRaw := quadraticForm_update_raw (M:=M) (x:=x) (i:=i) (v:=v)
  have hDiag0 : (v - x i) * (v - x i) * M i i = 0 := by simp [hii]
  have h1 :
      quadraticForm M (Function.update x i v) - quadraticForm M x
        =
      (v - x i) * ((∑ j, x j * M j i) + (M.mulVec x) i) := by
    simpa [hDiag0, add_comm, add_left_comm, add_assoc] using hRaw
  have hSplit :
      (∑ j, x j * M j i)
        = x i * M i i + ∑ j ∈ (Finset.univ.erase i), x j * M j i := by
    have := sum_split_at (f:=fun j => x j * M j i) i
    simp [add_comm, add_left_comm, add_assoc]
  have hErase :
      (∑ j, x j * M j i)
        = ∑ j ∈ (Finset.univ.erase i), x j * M j i := by
    simp_rw [hSplit, hii]; ring_nf
  simp_rw [h1, hErase, add_comm]

/-- Stronger version assuming all diagonal entries vanish -/
lemma quadraticForm_update_single
    {M : Matrix ι ι R} (hDiag : ∀ j, M j j = 0)
    (x : ι → R) (i : ι) (v : R) :
  quadraticForm M (Function.update x i v) - quadraticForm M x
    =
  (v - x i) *
    ( (M.mulVec x) i
      + ∑ j ∈ (Finset.univ.erase i), x j * M j i ) :=
  quadraticForm_update_single_index (M:=M) (x:=x) (i:=i) (v:=v) (hii:=hDiag i)

/--
Optimized symmetric / zero–diagonal update for the quadratic form.
This is the version used in the Hopfield flip energy relation.
-/
lemma quadratic_form_update_diag_zero
    {M : Matrix ι ι R} (hSymm : M.IsSymm) (hDiag : ∀ j, M j j = 0)
    (x : ι → R) (i : ι) (v : R) :
  quadraticForm M (Function.update x i v) - quadraticForm M x
    = (v - x i) * 2 * (M.mulVec x) i := by
  have hBase := quadraticForm_update_single (R:=R) (M:=M) hDiag x i v
  have hSwap :
      ∑ j ∈ (Finset.univ.erase i), x j * M j i
        = ∑ j ∈ (Finset.univ.erase i), M i j * x j := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    simp [Matrix.IsSymm.apply hSymm, mul_comm]
  have hMulVec :
      (M.mulVec x) i = ∑ j ∈ (Finset.univ.erase i), M i j * x j := by
    unfold Matrix.mulVec dotProduct
    have : (Finset.univ : Finset ι) = {i} ∪ Finset.univ.erase i := by
      ext j; by_cases hj : j = i <;> simp [hj]
    rw [this, Finset.sum_union]; simp [Finset.disjoint_singleton_left, hDiag]
    simp
  simp_rw [hBase, hSwap, hMulVec]; simp [two_mul, add_comm, add_left_comm, add_assoc, mul_add,
    mul_comm, mul_assoc]

end Matrix

open Finset Matrix NeuralNetwork State TwoState

variable {R U σ : Type}
variable [Field R] [LinearOrder R] [IsStrictOrderedRing R]
namespace TwoState

variable {R U σ : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [DecidableEq U]
variable {NN : NeuralNetwork R U σ} [TwoStateNeuralNetwork NN]

@[simp]
lemma updPos_act_at_u (s : NN.State) (u : U) :
    (updPos (s := s) (u := u)).act u = TwoStateNeuralNetwork.ζ_pos (NN := NN) := by
  simp [updPos]

lemma updPos_act_noteq (s : NN.State) (u v : U) (h : v ≠ u) :
    (updPos (s := s) (u := u)).act v = s.act v := by
  simp [updPos, Function.update_of_ne h]

@[simp]
lemma updNeg_act_at_u (s : NN.State) (u : U) :
    (updNeg (s := s) (u := u)).act u = TwoStateNeuralNetwork.ζ_neg (NN := NN) := by
  simp [updNeg]

lemma updNeg_act_noteq (s : NN.State) (u v : U) (h : v ≠ u) :
    (updNeg (s := s) (u := u)).act v = s.act v := by
  simp [updNeg, Function.update_of_ne h]

-- /-- Strict positivity of `logisticProb`. -/
-- lemma logisticProb_pos' (x : ℝ) : 0 < logisticProb x := by
--   unfold logisticProb
--   have hden : 0 < 1 + Real.exp (-x) :=
--     add_pos_of_pos_of_nonneg zero_lt_one (le_of_lt (Real.exp_pos _))
--   simpa using (one_div_pos.mpr hden)

/-- Symmetry: logisticProb (-x) = 1 - logisticProb x. -/
lemma logisticProb_neg (x : ℝ) : logisticProb (-x) = 1 - logisticProb x := by
  unfold logisticProb
  have h1 : 1 / (1 + Real.exp x) = Real.exp (-x) / (1 + Real.exp (-x)) := by
    have hden : (1 + Real.exp x) ≠ 0 :=
      (add_pos_of_pos_of_nonneg zero_lt_one (le_of_lt (Real.exp_pos _))).ne'
    calc
      1 / (1 + Real.exp x)
          = (1 * Real.exp (-x)) / ((1 + Real.exp x) * Real.exp (-x)) := by
              field_simp [hden]
      _ = Real.exp (-x) / (Real.exp (-x) + 1) := by
              simp [mul_add, add_comm, add_left_comm, add_assoc, Real.exp_neg, mul_comm]
              ring_nf; rw [mul_eq_mul_left_iff]; simp
      _ = Real.exp (-x) / (1 + Real.exp (-x)) := by simp [add_comm]
  have h2 : Real.exp (-x) / (1 + Real.exp (-x)) = 1 - 1 / (1 + Real.exp (-x)) := by
    have hden : (1 + Real.exp (-x)) ≠ 0 :=
      (add_pos_of_pos_of_nonneg zero_lt_one (le_of_lt (Real.exp_pos _))).ne'
    field_simp [hden]
    ring
  simp_all only [one_div, neg_neg]

end TwoState

-- /-!
-- # Concrete Energy Specification for Hopfield Networks (SymmetricBinary)

-- This section defines the standard Hopfield energy function and proves it satisfies
-- the `EnergySpec'` requirements for the `SymmetricBinary` architecture.
-- We leverage `Matrix.quadraticForm` for an elegant definition and proof.
-- -/

namespace HopfieldEnergy

open Finset Matrix NeuralNetwork TwoState
open scoped Classical

variable {R U : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable [Fintype U] [DecidableEq U] [Nonempty U]

/--
The standard Hopfield energy function (Hamiltonian) for SymmetricBinary networks.
E(s) = -1/2 * sᵀ W s + θᵀ s
-/
noncomputable def hamiltonian
    (p : Params (SymmetricBinary R U)) (s : (SymmetricBinary R U).State) : R :=
  let quad : R := ∑ i : U, s.act i * (p.w.mulVec s.act i)
  let θ_vec := fun i : U => (p.θ i).get fin0
  (- (1/2 : R) * quad) + ∑ i : U, θ_vec i * s.act i

/-- Proof of the fundamental Flip Energy Relation for the SymmetricBinary network.
ΔE = E(s⁺) - E(s⁻) = -2 * Lᵤ. -/
lemma hamiltonian_flip_relation (p : Params (SymmetricBinary R U)) (s : (SymmetricBinary R U).State) (u : U) :
    let sPos := updPos (s := s) (u := u)
    let sNeg := updNeg (s := s) (u := u)
    let L := s.net p u - (p.θ u).get fin0
    (hamiltonian p sPos - hamiltonian p sNeg) = - (2 : R) * L := by
  intro sPos sNeg L
  unfold hamiltonian
  let θ_vec := fun i => (p.θ i).get fin0
  have h_quad_diff :
    (- (1/2 : R) * Matrix.quadraticForm p.w sPos.act) - (- (1/2 : R) * Matrix.quadraticForm p.w sNeg.act) =
    - (2 : R) * (p.w.mulVec s.act u) := by
    rw [← mul_sub]
    have h_sPos_from_sNeg : sPos.act = Function.update sNeg.act u 1 := by
      ext i
      by_cases hi : i = u
      · subst hi
        simp_rw [sPos, sNeg, updPos, updNeg, Function.update]
        simp_all only [↓reduceDIte]
        rfl
      · simp [sPos, sNeg, updPos, updNeg, Function.update, hi]
    rw [h_sPos_from_sNeg]
    rw [Matrix.quadratic_form_update_diag_zero (p.hw'.1) (p.hw'.2)]
    have h_sNeg_u : sNeg.act u = -1 := updNeg_act_at_u s u
    rw [h_sNeg_u]
    simp only [sub_neg_eq_add, one_add_one_eq_two]
    ring_nf
    have h_W_sNeg_eq_W_s : p.w.mulVec sNeg.act u = p.w.mulVec s.act u := by
      unfold Matrix.mulVec dotProduct
      apply Finset.sum_congr rfl
      intro j _
      by_cases h_eq : j = u
      · simp [h_eq, p.hw'.2 u]
      · rw [updNeg_act_noteq s u j h_eq]
    rw [h_W_sNeg_eq_W_s]
  have h_linear_diff :
      dotProduct θ_vec sPos.act - dotProduct θ_vec sNeg.act
        = (2 : R) * θ_vec u := by
    rw [← dotProduct_sub]
    have h_diff_vec :
        sPos.act - sNeg.act = Pi.single u (2 : R) := by
      ext v
      by_cases hv : v = u
      · subst hv
        simp [sPos, sNeg, updPos, updNeg,
              TwoState.SymmetricBinary, instTwoStateSymmetricBinary,
              Pi.single, sub_eq_add_neg, one_add_one_eq_two]
      · simp [sPos, sNeg, updPos, updNeg, Pi.single, hv, sub_eq_add_neg]
    rw [h_diff_vec, dotProduct_single]
    simp [mul_comm]
  erw [add_sub_add_comm, h_quad_diff, h_linear_diff]
  have h_net_eq_W_s : s.net p u = p.w.mulVec s.act u := by
    classical
    unfold State.net SymmetricBinary fnet Matrix.mulVec dotProduct
    refine Finset.sum_congr rfl ?_
    intro v _
    by_cases hvu : v = u
    ·
      subst hvu
      simp only [ne_eq, not_true_eq_false, ↓reduceIte, zero_eq_mul]
      exact Or.inl (p.hw'.2 v)
    · simp only [ne_eq, ite_not]
      aesop

  rw [← h_net_eq_W_s]
  ring

/-- The concrete Energy Specification for the SymmetricBinary Hopfield Network. -/
noncomputable def symmetricBinaryEnergySpec : EnergySpec' (SymmetricBinary R U) where
  E := hamiltonian
  localField := fun p s u => s.net p u - (p.θ u).get fin0
  localField_spec := by intros; rfl
  flip_energy_relation := by
    intro f p s u
    have h_rel := hamiltonian_flip_relation p s u
    have h_scale : scale (NN:=SymmetricBinary R U) f = f 2 := scale_binary f
    simp_rw [h_rel, map_mul, map_neg]
    rw [h_scale]

end HopfieldEnergy

/-!
# Fintype Instance for Real-valued Binary States

The bridge to `CanonicalEnsemble` requires `[Fintype NN.State]`. For `SymmetricBinary ℝ U`,
we must formally establish that the subtype restricted to {-1, 1} activations is finite.
-/

namespace SymmetricBinaryFintype
variable {U : Type} [Fintype U] [DecidableEq U] [Nonempty U]

/-- Helper type representing the finite set {-1, 1} in ℝ. -/
def BinarySetReal := {x : ℝ // x = 1 ∨ x = -1}

/-- Decidable equality inherited from `ℝ` (classical). -/
noncomputable instance : DecidableEq BinarySetReal := by
  classical
  infer_instance

noncomputable instance : Fintype BinarySetReal :=
  Fintype.ofList
    [⟨1, Or.inl rfl⟩, ⟨-1, Or.inr rfl⟩]
    (by
      intro x
      rcases x.property with h | h
      · simp_rw [← h]; exact List.mem_cons_self
      · simp_rw [← h]; exact List.mem_of_getLast? rfl)

/-- Equivalence between the State space of SymmetricBinary ℝ U and (U → BinarySetReal). -/
noncomputable def stateEquivBinarySet :
    (TwoState.SymmetricBinary ℝ U).State ≃ (U → BinarySetReal) where
  toFun s := fun u => ⟨s.act u, s.hp u⟩
  invFun f := {
    act := fun u => (f u).val,
    hp := fun u => (f u).property
  }
  left_inv s := by ext u; simp
  right_inv f := by ext u; simp

-- The required Fintype instance.
noncomputable instance : Fintype (TwoState.SymmetricBinary ℝ U).State :=
  Fintype.ofEquiv (U → BinarySetReal) stateEquivBinarySet.symm

end SymmetricBinaryFintype

#min_imports
