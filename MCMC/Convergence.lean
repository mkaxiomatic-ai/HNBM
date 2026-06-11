/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import MCMC.TotalVariation
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Convergence of finite Markov chains

Limit matrices, spectral gaps from Dobrushin contraction, and convergence of distributions.
-/

open Matrix Finset Filter Topology
open scoped BigOperators

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The limit matrix Π: every row equals the stationary distribution π. -/
def LimitMatrix (π : stdSimplex ℝ n) : Matrix n n ℝ :=
  fun _ j => π.val j

omit [DecidableEq n] in
lemma LimitMatrix_is_stochastic (π : stdSimplex ℝ n) : IsStochastic (LimitMatrix π) := by
  constructor
  · intro i j; exact π.property.1 j
  · intro i; simp [LimitMatrix, π.property.2]

omit [DecidableEq n] in
/-- `P * Π = Π` and `Π * P = Π`: the limit matrix is absorbing. -/
theorem LimitMatrix_absorbing (P : Matrix n n ℝ) (π : stdSimplex ℝ n)
    (h_stoch : IsStochastic P) (h_stat : IsStationary P π) :
    P * LimitMatrix π = LimitMatrix π ∧ LimitMatrix π * P = LimitMatrix π := by
  constructor
  · ext i j
    simp only [LimitMatrix, mul_apply]
    calc
      ∑ k, P i k * π.val j = (∑ k, P i k) * π.val j := (Finset.sum_mul _ _ _).symm
      _ = π.val j := by rw [h_stoch.2 i, one_mul]
  · ext i j
    simp only [LimitMatrix, mul_apply]
    have h_stat_j := congrArg (fun v => v j) h_stat
    simp [mulVec, transpose_apply] at h_stat_j
    simpa [mul_comm] using h_stat_j

/-!
## Spectral gap and matrix convergence
-/

/-- Entrywise exponential convergence to the rank-1 limit matrix at block rate `r^(k / k0)`. -/
def HasSpectralGap (P : Matrix n n ℝ) : Prop :=
  ∃ (π : stdSimplex ℝ n) (r : ℝ) (k0 : ℕ),
    IsStationary P π ∧ 0 < k0 ∧ 0 ≤ r ∧ r < 1 ∧
      ∀ i j k, |(P^k) i j - (LimitMatrix π) i j| ≤ r^(k / k0)

lemma IsPrimitive.irreducible [Nonempty n] {P : Matrix n n ℝ}
    (_ : IsStochastic P) (h_prim : IsPrimitive P) :
    Matrix.IsIrreducible P :=
  IsPrimitive.isIrreducible h_prim

lemma pow_stationary_mulVec [Nonempty n] (P : Matrix n n ℝ) (k : ℕ)
    (_ : IsStochastic P) (π : stdSimplex ℝ n) (h_stat : IsStationary P π) :
    (P^k)ᵀ *ᵥ π.val = π.val := by
  induction' k with k ih
  · simp
  · have ih' : (Pᵀ ^ k) *ᵥ π.val = π.val := by simpa [Matrix.transpose_pow] using ih
    calc (P ^ (k + 1))ᵀ *ᵥ π.val
        = (Pᵀ * (Pᵀ ^ k)) *ᵥ π.val := by simp [pow_succ, Matrix.transpose_mul, Matrix.transpose_pow]
      _ = Pᵀ *ᵥ ((Pᵀ ^ k) *ᵥ π.val) := by simp [mulVec_mulVec]
      _ = Pᵀ *ᵥ π.val := by simp [ih']
      _ = π.val := by simpa [IsStationary] using h_stat

private def delta (i : n) : n → ℝ :=
  fun t => if t = i then 1 else 0

private lemma delta_sum_one (i : n) : ∑ t, delta i t = 1 := by
  classical
  simp [delta]

omit [Fintype n] in
private lemma delta_nonneg (i : n) : ∀ t, 0 ≤ delta i t := by
  intro t
  classical
  by_cases h : t = i <;> simp [delta, h]

/-- Total variation distance between two probability vectors is at most `1`. -/
private lemma tvDist_probabilities_le_one {p q : n → ℝ}
    (hp0 : ∀ t, 0 ≤ p t) (hq0 : ∀ t, 0 ≤ q t) (hp1 : ∑ t, p t = 1) (hq1 : ∑ t, q t = 1) :
    Matrix.tvDist p q ≤ 1 := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hnum : (∑ t, |p t - q t|) ≤ 2 := by
    have hle t : |p t - q t| ≤ |p t| + |q t| := by
      simpa [sub_eq_add_neg] using abs_add_le (p t) (-q t)
    calc (∑ t, |p t - q t|)
        ≤ ∑ t, (|p t| + |q t|) := sum_le_sum fun t _ => hle t
      _ = (∑ t, |p t|) + (∑ t, |q t|) := sum_add_distrib
      _ = 2 := by
        have habs_p : (∑ t, |p t|) = 1 := by simp [abs_of_nonneg (hp0 _), hp1]
        have habs_q : (∑ t, |q t|) = 1 := by simp [abs_of_nonneg (hq0 _), hq1]
        simp [habs_p, habs_q]; norm_num
  have : (∑ t, |p t - q t|) / 2 ≤ 1 := (div_le_iff₀ h2).2 (by simpa [one_mul] using hnum)
  simpa [Matrix.tvDist] using this

private lemma dobrushinCoeff_le_one [Nonempty n] (P : Matrix n n ℝ) (hP : IsStochastic P) :
    Matrix.dobrushinCoeff P ≤ 1 := by
  let f : (n × n) → ℝ := fun p => Matrix.tvDist (Matrix.rowDist P p.1) (Matrix.rowDist P p.2)
  have hforall : ∀ d ∈ Set.range f, d ≤ 1 := by
    rintro d ⟨⟨i₁, i₂⟩, rfl⟩
    exact tvDist_probabilities_le_one
      (fun t => by simpa [Matrix.rowDist] using hP.1 i₁ t)
      (fun t => by simpa [Matrix.rowDist] using hP.1 i₂ t)
      (by simpa [Matrix.rowDist] using hP.2 i₁)
      (by simpa [Matrix.rowDist] using hP.2 i₂)
  have hnonempty : (Set.range f).Nonempty := by
    let i0 := Classical.arbitrary n
    exact ⟨f ⟨i0, i0⟩, ⟨⟨i0, i0⟩, rfl⟩⟩
  have hset_eq :
      { d | ∃ i i' : n, d = Matrix.tvDist (Matrix.rowDist P i) (Matrix.rowDist P i') } =
        Set.range f := by
    ext d; constructor
    · rintro ⟨i, i', rfl⟩; exact ⟨⟨i, i'⟩, rfl⟩
    · rintro ⟨⟨i, i'⟩, rfl⟩; exact ⟨i, i', rfl⟩
  simpa [Matrix.dobrushinCoeff, hset_eq] using csSup_le hnonempty hforall

private def distributionPushforward (Q : Matrix n n ℝ) (p : n → ℝ) : n → ℝ :=
  fun j => ∑ t, p t * Q t j

/-- Primitivity yields a spectral gap via Dobrushin contraction on a positive power. -/
lemma IsPrimitive.has_spectral_gap [Nonempty n] {P : Matrix n n ℝ}
    (h_stoch : IsStochastic P) (h_prim : IsPrimitive P) : HasSpectralGap P := by
  obtain ⟨π, hπ_stat, _⟩ :=
    exists_unique_stationary_distribution_of_irreducible h_stoch
      (IsPrimitive.irreducible h_stoch h_prim)
  obtain ⟨k0, hk0_pos, hδ_lt⟩ :=
    Matrix.dobrushinCoeff_lt_one_of_primitive (P := P) h_stoch h_prim
  set r := Matrix.dobrushinCoeff (P ^ k0)
  have hr0 : 0 ≤ r := Matrix.dobrushinCoeff_nonneg (P := P ^ k0)
  refine ⟨π, r, k0, hπ_stat, hk0_pos, hr0, hδ_lt, ?_⟩
  intro i j k
  set q := k / k0
  set s := k % k0
  have hk_decomp : k = q * k0 + s := (Nat.div_add_mod' k k0).symm
  have h_entry_le_tv :
      |(P ^ k) i j - (LimitMatrix π) i j| ≤
        Matrix.tvDist (Matrix.rowDist (P ^ k) i) π.val := by
    simpa [Matrix.rowDist, LimitMatrix] using
      Matrix.entry_abs_le_tvDist_of_rows (P := P ^ k) (i := i) (x := π.val) (j := j)
        (hsum := by simp [Matrix.rowDist, π.property.2, (isStochastic_pow h_stoch k).2 i])
  have h_contract (Q : Matrix n n ℝ) (p qv : n → ℝ)
      (hp1 : ∑ t, p t = 1) (hq1 : ∑ t, qv t = 1) :
      Matrix.tvDist (distributionPushforward Q p) (distributionPushforward Q qv) ≤
        Matrix.dobrushinCoeff Q * Matrix.tvDist p qv := by
    simpa [distributionPushforward] using
      Matrix.tvDist_contract (P := Q) (p := p) (q := qv) (hp1 := hp1) (hq1 := hq1)
  have T_fix (m : ℕ) : distributionPushforward (P ^ m) π.val = π.val := by
    funext j
    have := congrArg (fun v => v j) (pow_stationary_mulVec (P := P) m h_stoch π hπ_stat)
    simpa [distributionPushforward, mulVec, transpose_apply, Finset.mul_sum, mul_comm,
      mul_left_comm, mul_assoc] using this
  have h_tv_blocks :
      ∀ i, Matrix.tvDist (Matrix.rowDist (P ^ (q * k0)) i) π.val ≤ r ^ q := by
    refine Nat.rec (motive := fun q' => ∀ i0, Matrix.tvDist (Matrix.rowDist (P ^ (q' * k0)) i0) π.val ≤ r ^ q')
      ?base ?step q
    · intro i0
      have h_row : Matrix.rowDist (P ^ (0 * k0)) i0 = delta i0 := by
        ext t
        simp [Matrix.rowDist, pow_zero, delta, Matrix.one_apply, eq_comm]
      rw [h_row, pow_zero]
      exact tvDist_probabilities_le_one (delta_nonneg i0) π.property.1 (delta_sum_one i0) π.property.2
    · intro q ih i0
      have hp1 : ∑ t, Matrix.rowDist (P ^ (q * k0)) i0 t = 1 := by
        simpa [Matrix.rowDist] using (isStochastic_pow h_stoch (q * k0)).2 i0
      have hleft :
          distributionPushforward (P ^ k0) (Matrix.rowDist (P ^ (q * k0)) i0) =
            Matrix.rowDist (P ^ ((q + 1) * k0)) i0 := by
        funext j
        have hmul : (q + 1) * k0 = q * k0 + k0 := by
          simpa [Nat.succ_eq_add_one] using Nat.succ_mul q k0
        simp [distributionPushforward, Matrix.rowDist, Matrix.mul_apply, pow_add, hmul]
      calc
        Matrix.tvDist (Matrix.rowDist (P ^ ((q + 1) * k0)) i0) π.val
            ≤ r * Matrix.tvDist (Matrix.rowDist (P ^ (q * k0)) i0) π.val := by
              simpa [hleft, T_fix k0] using
                h_contract (P ^ k0) (Matrix.rowDist (P ^ (q * k0)) i0) π.val hp1 π.property.2
        _ ≤ r * r ^ q := mul_le_mul_of_nonneg_left (ih i0) hr0
        _ = r ^ (q + 1) := by simp [pow_succ, mul_comm]
  have hpq : Matrix.tvDist (Matrix.rowDist (P ^ k) i) π.val ≤ r ^ q := by
    have hsplit : P ^ k = P ^ (q * k0) * P ^ s := by simp [hk_decomp, pow_add]
    have hp1 : ∑ t, Matrix.rowDist (P ^ (q * k0)) i t = 1 := by
      simpa [Matrix.rowDist] using (isStochastic_pow h_stoch (q * k0)).2 i
    calc
      Matrix.tvDist (Matrix.rowDist (P ^ k) i) π.val
          ≤ Matrix.dobrushinCoeff (P ^ s) * Matrix.tvDist (Matrix.rowDist (P ^ (q * k0)) i) π.val := by
            simpa [distributionPushforward, Matrix.rowDist, hsplit, Matrix.mul_apply, T_fix s] using
              h_contract (P ^ s) (Matrix.rowDist (P ^ (q * k0)) i) π.val hp1 π.property.2
      _ ≤ Matrix.tvDist (Matrix.rowDist (P ^ (q * k0)) i) π.val := by
            simpa [one_mul] using mul_le_mul_of_nonneg_right
              (dobrushinCoeff_le_one (P := P ^ s) (isStochastic_pow h_stoch s))
              (Matrix.tvDist_nonneg _ _)
      _ ≤ r ^ q := h_tv_blocks i
  have : |(P ^ k) i j - (LimitMatrix π) i j| ≤ r ^ q := le_trans h_entry_le_tv hpq
  simpa [LimitMatrix, show q = k / k0 from rfl] using this

/-- A spectral gap implies convergence to the stationary limit matrix. -/
theorem converges_of_spectral_gap [Nonempty n] {P : Matrix n n ℝ} (_ : IsStochastic P)
    (h_gap : HasSpectralGap P) (_ : Matrix.IsIrreducible P) :
    ∃ (π : stdSimplex ℝ n), IsStationary P π ∧
      Tendsto (fun k : ℕ => P ^ k) atTop (𝓝 (LimitMatrix π)) := by
  rcases h_gap with ⟨π, r, k0, h_stat, hk0pos, hr0, hr1, h_bound⟩
  refine ⟨π, h_stat, ?_⟩
  set L := LimitMatrix π
  have h_pow_tendsto_zero : Tendsto (fun k : ℕ => r ^ (k / k0)) atTop (𝓝 0) := by
    have h_abs_lt_one : |r| < 1 := abs_lt.mpr ⟨by linarith [hr0, hr1], hr1⟩
    have h_rpow : Tendsto (fun n : ℕ => r ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_abs_lt_one h_abs_lt_one
    have h_div : Tendsto (fun k : ℕ => k / k0) atTop atTop :=
      tendsto_atTop_atTop.mpr fun b =>
        ⟨b * k0, fun n hn => (Nat.le_div_iff_mul_le hk0pos).mpr hn⟩
    simpa using h_rpow.comp h_div
  refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => ?_
  have h_abs_bound : ∀ k, |(P ^ k) i j - L i j| ≤ r ^ (k / k0) := fun k =>
    by simpa [L, LimitMatrix] using h_bound i j k
  have h_abs_tend :
      Tendsto (fun k : ℕ => |(P ^ k) i j - L i j|) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_pow_tendsto_zero
      (fun _ => abs_nonneg _) h_abs_bound
  have h_diff_tend :
      Tendsto (fun k : ℕ => (P ^ k) i j - L i j) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le (by simpa using h_abs_tend.neg) h_abs_tend
      (fun _ => neg_abs_le _) (fun _ => le_abs_self _)
  have h_add_const :
      Tendsto (fun k => L i j + ((P ^ k) i j - L i j)) atTop (𝓝 (L i j + 0)) :=
    tendsto_const_nhds.add h_diff_tend
  simpa using h_add_const

/-- If `P` satisfies `IsMCMC`, then `P^k` converges to the limit matrix built from `π`. -/
theorem convergence_to_stationarity [Nonempty n]
    (P : Matrix n n ℝ) (π : stdSimplex ℝ n) (hMCMC : IsMCMC P π) :
    Tendsto (fun k => P ^ k) atTop (𝓝 (LimitMatrix π)) := by
  obtain ⟨π', h_stat', h_conv⟩ := converges_of_spectral_gap hMCMC.stochastic
    (IsPrimitive.has_spectral_gap hMCMC.stochastic hMCMC.primitive) hMCMC.irreducible
  convert h_conv
  exact (exists_unique_stationary_distribution_of_irreducible
    hMCMC.stochastic hMCMC.irreducible).unique hMCMC.stationary h_stat'

/-!
## Convergence of distributions
-/

/-- Distribution of the chain at time `k`, starting from `μ₀`. -/
def distributionAtTime (P : Matrix n n ℝ) (μ₀ : stdSimplex ℝ n) (k : ℕ) : n → ℝ :=
  (P ^ k)ᵀ *ᵥ μ₀.val

/-- The distribution at time `k` converges to `π`, regardless of the initial distribution. -/
lemma distribution_converges_to_stationarity [Nonempty n]
    (P : Matrix n n ℝ) (π : stdSimplex ℝ n) (hMCMC : IsMCMC P π) (μ₀ : stdSimplex ℝ n) :
    Tendsto (distributionAtTime P μ₀) atTop (𝓝 π.val) := by
  have h_conv := convergence_to_stationarity P π hMCMC
  rw [tendsto_pi_nhds]
  intro i
  simpa [distributionAtTime, Matrix.mulVec, Matrix.transpose_apply, LimitMatrix, ← Finset.mul_sum,
    μ₀.prop.2] using
    tendsto_finsetSum Finset.univ fun j _ =>
      (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp h_conv j) i).mul_const (μ₀.val j)

/-- Expectation of `f` under the distribution `π`. -/
def Expectation (π : stdSimplex ℝ n) (f : n → ℝ) : ℝ :=
  ∑ i, π.val i * f i

/-- Ergodic theorem (LLN): time averages of expectations converge to `E_π[f]`. -/
theorem ergodic_theorem_lln [Nonempty n] (P : Matrix n n ℝ) (π : stdSimplex ℝ n) (hMCMC : IsMCMC P π)
    (f : n → ℝ) (μ₀ : stdSimplex ℝ n) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ k ∈ Finset.range N, ∑ i, distributionAtTime P μ₀ k i * f i)
      atTop (𝓝 (Expectation π f)) := by
  have h_seq :
      Tendsto (fun k => ∑ i, distributionAtTime P μ₀ k i * f i) atTop (𝓝 (Expectation π f)) :=
    tendsto_finsetSum Finset.univ fun i _ =>
      ((tendsto_pi_nhds.mp (distribution_converges_to_stationarity P π hMCMC μ₀)) i).mul_const (f i)
  simpa using h_seq.cesaro
