/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.CNS.Problem
import HopfieldNet.Quiver.NeuralNetwork.TwoState
import HopfieldNet.Quiver.BM.BoltzmannMachine

/-!
# The reduced Sudoku QUBO as an HNBM network

`CNS.Spec` exhibits the *unreduced* `n³`-variable QUBO as a `TwoState.ZeroOne` instance. That is
the wrong object: the solver runs on the **reduced** instance built by `Problem.ofGrid`, whose
dimension is the Table I quantity. This module puts that instance — the one the dynamics
actually iterate — on the repository's network, so that theorems about `ZeroOne` are theorems
about the running search.

## Structure of the development

Reasoning directly about `Problem.ofReduced` is reasoning about four nested `Id.run do` loops
accumulating into arrays with `set!`. That work is real but it is *bookkeeping*, and threading it
through every algebraic step would make the algebra unreadable. So the module is split:

* `Problem.Valid` records the structural invariants `ofReduced` establishes — each surviving
  variable keeps its four original constraint rows, `θ̂` is the folded threshold, `constDoubled`
  is `‖b̂‖²`. Everything downstream is proved *from `Valid`*, as ordinary algebra.
* `Problem.ofGrid_valid` (`CNS.NetValid`) discharges `Valid` for the problems the pipeline
  actually builds. That is where the loop bookkeeping lives, isolated.

The payoff is that the energy bridge below is a computation about finite sums, not about arrays.

## Why `ℝ` and not a computable carrier

`ZeroOne` needs `[Field R] [LinearOrder R]`, so `ℚ` would give a computable `Params`. It would
also be useless: `fnet` is a `Finset.sum` over all neurons, so evaluating one site costs
`P.nvars` rational multiplications where the executable path costs four `Int` additions, and the
Gibbs, detailed-balance and ergodicity development in `HopfieldNet.Quiver.BM` is stated for
`NeuralNetwork ℝ U σ` throughout. Taking `ℝ` here keeps that theory directly applicable; the
executable path is connected to it by a refinement theorem (`CNS.Refine`), which is what makes
the object that runs the object that is proved about.
-/

namespace CNS
namespace Problem

open Finset

/-! ## Incidence of the reduced constraint matrix -/

/-- `Â_{ru} = 1` when surviving variable `u` occurs in constraint row `r`.

Column deletion does not touch the rows, so `u` keeps exactly the four rows of the original
variable it came from — that is `Valid.rowsOf_eq`. -/
def inRow (P : Problem) (u r : Nat) : Bool := (P.rowsOf.getD u #[]).contains r

/-- The structural invariants `Problem.ofReduced` establishes.

Stated as a predicate so that the algebra below is independent of the imperative construction;
`CNS.NetValid` proves the pipeline's problems satisfy it. -/
structure Valid (P : Problem) : Prop where
  /-- The reduced index table is in range. -/
  varOf_lt : ∀ u < P.nvars, P.varOf.getD u 0 < numVars
  /-- A surviving variable keeps the four constraint rows it had before reduction. -/
  rowsOf_eq : ∀ u < P.nvars, P.rowsOf.getD u #[] = rowsOfVar (P.varOf.getD u 0)
  /-- `θ̂_u = 2 − Σ_{r ∋ u} b̂_r`, the folded threshold of §IV.

  Written as a sum over *all* rows against the incidence indicator rather than as a fold over
  `rowsOf u`. The two agree (`sum_indicator_weighted`); stating it this way keeps the array
  bookkeeping inside `CNS.NetValid` and out of the algebra below. -/
  theta_eq : ∀ u < P.nvars,
    P.theta.getD u 0
      = 2 - ∑ r ∈ Finset.range numRows,
          (if (P.rowsOf.getD u #[]).contains r then P.bhat.getD r 0 else 0)
  /-- `constDoubled = ‖b̂‖²`. -/
  const_eq : P.constDoubled = ∑ r ∈ Finset.range numRows, P.bhat.getD r 0 ^ 2
  /-- Distinct surviving indices name distinct original variables. -/
  varOf_inj : ∀ u < P.nvars, ∀ v < P.nvars, P.varOf.getD u 0 = P.varOf.getD v 0 → u = v

/-! ## The four rows of a variable are distinct

`diag(ÂᵀÂ) = 4` is the fact that lets the diagonal be folded into `θ̂`. It holds because the
four rows of `rowsOfVar` live in four disjoint index bands. -/

/-- `boxOf` of a cell index is a legal block number. -/
private theorem boxOf_cellIdx_lt {i j : Nat} (hi : i < n) (hj : j < n) :
    boxOf (cellIdx i j) < n := by
  simp only [boxOf, rowOf, colOf, cellIdx, blk, n] at *
  omega

/-- `rowsOfVar` in the form the band argument needs: four rows, one per constraint family. -/
private theorem rowsOfVar_eq (v : Nat) (hv : v < numVars) :
    ∃ i j k b, i < n ∧ j < n ∧ k < n ∧ b < n ∧
      rowsOfVar v = #[rowCell i j, rowCol j k, rowRow i k, rowBox b k] := by
  have hi : v / (n * n) < n := by simp only [numVars, n] at *; omega
  have hj : v % (n * n) / n < n := by simp only [n] at *; omega
  have hk : v % n < n := by simp only [n] at *; omega
  exact ⟨_, _, _, _, hi, hj, hk, boxOf_cellIdx_lt hi hj, rfl⟩

/-- **The four constraint rows of a variable are pairwise distinct and in range.**

This is what makes `diag(ÂᵀÂ) = 4`, and hence what licenses folding the diagonal into `θ̂`.
The four families occupy the disjoint index bands `[0,n²)`, `[n²,2n²)`, `[2n²,3n²)`,
`[3n²,4n²)`, so no two of them can collide. -/
theorem rowsOfVar_nodup (v : Nat) (hv : v < numVars) :
    (rowsOfVar v).toList.Nodup ∧ ∀ r ∈ rowsOfVar v, r < numRows := by
  obtain ⟨i, j, k, b, hi, hj, hk, hb, hrv⟩ := rowsOfVar_eq v hv
  rw [hrv]
  constructor
  · show List.Nodup [rowCell i j, rowCol j k, rowRow i k, rowBox b k]
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil, not_or,
      not_false_eq_true, and_true, rowCell, rowCol, rowRow, rowBox, cellIdx]
    simp only [n] at *
    omega
  · intro r hr
    simp only [rowCell, rowCol, rowRow, rowBox, cellIdx] at hr
    simp at hr
    simp only [numRows, rowCell, rowCol, rowRow, rowBox, cellIdx, n] at *
    rcases hr with h | h | h | h <;> omega

/-- Every variable lies in exactly four constraint rows. -/
theorem rowsOfVar_size (v : Nat) : (rowsOfVar v).size = 4 := by
  simp [rowsOfVar]

/-! ## Counting occurrences

The degree fact `Σ_r Â_{ru} = 4` is an instance of "summing the indicator of a duplicate-free
array over a range that contains it gives its size". -/

/-- Summing the membership indicator of a duplicate-free array over a containing range returns
its size. -/
theorem sum_indicator_contains {N : Nat} (a : Array Nat)
    (hnd : a.toList.Nodup) (hlt : ∀ r ∈ a, r < N) :
    ∑ r ∈ Finset.range N, (if a.contains r then (1 : ℝ) else 0) = (a.size : ℝ) := by
  have hfilter : (Finset.range N).filter (fun r => a.contains r = true) = a.toList.toFinset := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_range, List.mem_toFinset, Array.contains_iff_mem,
      Array.mem_toList_iff]
    exact ⟨fun h => h.2, fun h => ⟨hlt r h, h⟩⟩
  rw [← Finset.sum_filter, hfilter, Finset.sum_const, nsmul_eq_mul, mul_one,
    List.toFinset_card_of_nodup hnd, Array.length_toList]

/-! ## The network

`Â`, `W = −(ÂᵀÂ − 4I)` and `θ̂`, as real-valued functions of the reduced index. These are the
mathematical objects; `netVec` in `Problem.lean` is the `O(nvars)` integer routine that computes
the same net input, and `CNS.Refine` connects them. -/

/-- `Â_{ru}`: whether surviving variable `u` occurs in constraint row `r`. -/
noncomputable def Ahat (P : Problem) (r : Nat) (u : Fin P.nvars) : ℝ :=
  if P.inRow u.val r then 1 else 0

/-- `Â` is a `{0,1}` matrix, so it is idempotent entrywise. -/
theorem Ahat_sq (P : Problem) (r : Nat) (u : Fin P.nvars) :
    Ahat P r u * Ahat P r u = Ahat P r u := by
  unfold Ahat; split <;> ring

/-- **Every surviving variable still lies in exactly four rows.**

Deleting columns of `Â` leaves the rows alone, so the degree is the unreduced one. This is what
keeps `diag(ÂᵀÂ) = 4` after reduction, and hence what makes the `x² = x` diagonal fold produce
the *same* `W` as before. -/
theorem sum_Ahat (P : Problem) (hV : P.Valid) (u : Fin P.nvars) :
    ∑ r ∈ Finset.range numRows, Ahat P r u = 4 := by
  have hlt := hV.varOf_lt u.val u.isLt
  have hrows := hV.rowsOf_eq u.val u.isLt
  obtain ⟨hnd, hbound⟩ := rowsOfVar_nodup _ hlt
  have h : ∀ r, P.inRow u.val r = (rowsOfVar (P.varOf.getD u.val 0)).contains r := by
    intro r; unfold inRow; rw [hrows]
  simp only [Ahat, h]
  rw [sum_indicator_contains _ (by rwa [← hrows] at hnd ⊢) (by intro r hr; exact hbound r hr)]
  rw [rowsOfVar_size]
  norm_num

/-- `(ÂᵀÂ)_{uv}`: the number of constraint rows containing both `u` and `v`. -/
noncomputable def gramR (P : Problem) (u v : Fin P.nvars) : ℝ :=
  ∑ r ∈ Finset.range numRows, Ahat P r u * Ahat P r v

/-- The Gram matrix is symmetric — `mul_comm` under the sum. -/
theorem gramR_comm (P : Problem) (u v : Fin P.nvars) : gramR P u v = gramR P v u :=
  Finset.sum_congr rfl fun r _ => mul_comm _ _

/-- **The diagonal of `ÂᵀÂ` is the degree, `4`.**

This is the fact the whole encoding turns on: because it is constant, `x² = x` lets it be folded
into `θ̂`, leaving `W` with a zero diagonal — exactly what `ZeroOne`'s `pm` demands. -/
theorem gramR_diag (P : Problem) (hV : P.Valid) (u : Fin P.nvars) : gramR P u u = 4 := by
  unfold gramR
  rw [Finset.sum_congr rfl (fun r _ => Ahat_sq P r u)]
  exact sum_Ahat P hV u

/-- The coupling matrix `W = −(ÂᵀÂ − 4I)`, written as an incidence sum so that symmetry is
`mul_comm` and the zero diagonal is definitional. -/
noncomputable def Wr (P : Problem) : Matrix (Fin P.nvars) (Fin P.nvars) ℝ := fun u v =>
  if u = v then 0 else -(gramR P u v)

/-- `W` is symmetric. -/
theorem Wr_isSymm (P : Problem) : (Wr P).IsSymm := by
  ext u v
  simp only [Matrix.transpose_apply, Wr]
  by_cases h : u = v
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h), gramR_comm]

/-- `W` has zero diagonal — the other half of `pm`, and what folding `diag(ÂᵀÂ)` into `θ̂`
buys. -/
theorem Wr_diag (P : Problem) (u : Fin P.nvars) : Wr P u u = 0 := by simp [Wr]

/-- The reduced threshold `θ̂_u`, transported from `Problem.theta`. -/
noncomputable def thetaR (P : Problem) (u : Fin P.nvars) : ℝ := (P.theta.getD u.val 0 : ℝ)

/-- **The reduced Sudoku QUBO as parameters of the repository's `{0,1}` network.**

The only substantive obligation is `pm`, discharged by `Wr_isSymm` and `Wr_diag`; `pw` is `True`
for this network, and the off-arrow condition reduces to the zero diagonal because `ZeroOne`'s
arrows are exactly the pairs `u ≠ v`. -/
noncomputable def netParams (P : Problem) [Nonempty (Fin P.nvars)] :
    Params (TwoState.ZeroOne ℝ (Fin P.nvars)) where
  h_arrows := fun _ _ _ => trivial
  w := Wr P
  σ := fun _ => ⟨#[0], rfl⟩
  θ := fun u => ⟨#[thetaR P u], rfl⟩
  hw := by
    intro u v huv
    have : u = v := by by_contra hne; exact huv ⟨⟨hne⟩, trivial⟩
    subst this
    exact Wr_diag P u
  hw' := ⟨Wr_isSymm P, Wr_diag P⟩

/-! ## The energy bridge

HNBM's `{0,1}` Boltzmann Hamiltonian is `E(a) = −½aᵀWa + θᵀa`, which is the canonical form (4)
of the paper. The theorem below is that instantiating it at `netParams` returns the paper's own
objective: `E = (‖Âx̂ − b̂‖² − ‖b̂‖²)/2`, i.e. `E = p(x̂) − ½‖b̂‖²`.

This is the link that makes every `ZeroOne` theorem a theorem about Sudoku. Composed with
`CNS.Sound.penalty_zero_iff_families`, the minimisers of the HNBM energy are exactly the solved
grids — not a proxy for them. -/

/-- A bit as a `{0,1}`-valued real. -/
def bit (b : Bool) : ℝ := if b then 1 else 0

@[simp] theorem bit_sq (b : Bool) : bit b * bit b = bit b := by unfold bit; split <;> ring

/-- The row sum `ρ_r = Σ_{u ∈ r} x̂_u`. -/
noncomputable def rowSumR (P : Problem) (x : Fin P.nvars → Bool) (r : Nat) : ℝ :=
  ∑ u : Fin P.nvars, Ahat P r u * bit (x u)

/-- The reduced right-hand side `b̂_r`. -/
noncomputable def bhatR (P : Problem) (r : Nat) : ℝ := (P.bhat.getD r 0 : ℝ)

/-- The reduced objective `‖Âx̂ − b̂‖²`, i.e. twice the paper's `p(x̂)`. -/
noncomputable def penaltyR (P : Problem) (x : Fin P.nvars → Bool) : ℝ :=
  ∑ r ∈ Finset.range numRows, (rowSumR P x r - bhatR P r) ^ 2

/-- The additive constant `‖b̂‖²`. -/
noncomputable def constR (P : Problem) : ℝ := ∑ r ∈ Finset.range numRows, bhatR P r ^ 2

/-- A bit vector as a state of the network. -/
def stateOfBits (P : Problem) [Nonempty (Fin P.nvars)] (x : Fin P.nvars → Bool) :
    (TwoState.ZeroOne ℝ (Fin P.nvars)).State where
  act := fun u => bit (x u)
  hp := by
    intro u
    show bit (x u) = 0 ∨ bit (x u) = 1
    unfold bit; split
    · right; rfl
    · left; rfl

/-- `θ̂` against the incidence indicator, in the form the algebra wants. -/
theorem thetaR_eq (P : Problem) (hV : P.Valid) (u : Fin P.nvars) :
    thetaR P u = 2 - ∑ r ∈ Finset.range numRows, Ahat P r u * bhatR P r := by
  have h := hV.theta_eq u.val u.isLt
  unfold thetaR
  rw [h]
  push_cast
  congr 1
  rw [Finset.sum_congr rfl (fun r _ => ?_)]
  unfold Ahat inRow bhatR
  split <;> simp

/-- `‖b̂‖²` matches the stored constant. -/
theorem constR_eq (P : Problem) (hV : P.Valid) : constR P = (P.constDoubled : ℝ) := by
  unfold constR bhatR
  rw [hV.const_eq]
  push_cast
  rfl

/-- `W` split into its full incidence part and the diagonal correction it removes. -/
theorem Wr_split (P : Problem) (u v : Fin P.nvars) :
    Wr P u v = -(gramR P u v) + (if u = v then gramR P u v else 0) := by
  unfold Wr; split <;> simp

/-- **The `ÂᵀÂ` double sum is the sum of squared row sums.**

`Σ_u Σ_v (ÂᵀÂ)_{uv} x_u x_v = Σ_r ρ_r²`: exchanging the order of summation turns the Gram form
into a sum over rows of a perfect square. This is the step that makes the objective a sum of
per-constraint residuals. -/
private theorem gram_double_sum (P : Problem) (x : Fin P.nvars → Bool) :
    ∑ i, ∑ j, gramR P i j * (bit (x i) * bit (x j))
      = ∑ r ∈ Finset.range numRows, rowSumR P x r ^ 2 := by
  have hinner : ∀ i j, gramR P i j * (bit (x i) * bit (x j))
      = ∑ r ∈ Finset.range numRows, (Ahat P r i * bit (x i)) * (Ahat P r j * bit (x j)) := by
    intro i j
    unfold gramR
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun r _ => by ring
  calc ∑ i, ∑ j, gramR P i j * (bit (x i) * bit (x j))
      = ∑ i, ∑ r ∈ Finset.range numRows, ∑ j,
          (Ahat P r i * bit (x i)) * (Ahat P r j * bit (x j)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_congr rfl fun j _ => hinner i j, Finset.sum_comm]
    _ = ∑ r ∈ Finset.range numRows, ∑ i, ∑ j,
          (Ahat P r i * bit (x i)) * (Ahat P r j * bit (x j)) := Finset.sum_comm
    _ = ∑ r ∈ Finset.range numRows, rowSumR P x r ^ 2 := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [sq]
        unfold rowSumR
        rw [Finset.sum_mul_sum]

/-- The quadratic form of the Hamiltonian, in terms of the row sums. -/
private theorem quad_eq (P : Problem) [Nonempty (Fin P.nvars)] (hV : P.Valid)
    (x : Fin P.nvars → Bool) :
    ∑ i, (stateOfBits P x).act i * ((netParams P).w.mulVec (stateOfBits P x).act i)
      = -(∑ r ∈ Finset.range numRows, rowSumR P x r ^ 2) + 4 * ∑ u, bit (x u) := by
  have hact : ∀ i, (stateOfBits P x).act i = bit (x i) := fun _ => rfl
  have hw : ∀ i j, (netParams P).w i j = Wr P i j := fun _ _ => rfl
  -- the Hamiltonian's quadratic form as a plain double sum
  have hLHS : ∑ i, (stateOfBits P x).act i * ((netParams P).w.mulVec (stateOfBits P x).act i)
      = ∑ i, ∑ j, Wr P i j * (bit (x i) * bit (x j)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mulVec_apply_eq_sum, hact, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [hact, hw]; ring
  -- split off the diagonal
  have hsplit : ∑ i, ∑ j, Wr P i j * (bit (x i) * bit (x j))
      = (∑ i, ∑ j, -(gramR P i j * (bit (x i) * bit (x j))))
        + ∑ i, ∑ j, (if i = j then gramR P i j else 0) * (bit (x i) * bit (x j)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by rw [Wr_split P i j]; ring
  -- the off-diagonal part is minus the squared row sums
  have hoff : (∑ i, ∑ j, -(gramR P i j * (bit (x i) * bit (x j))))
      = -(∑ r ∈ Finset.range numRows, rowSumR P x r ^ 2) := by
    rw [← gram_double_sum P x, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_neg_distrib _
  -- the diagonal correction is the degree times the number of active neurons
  have hdiag : ∑ i, ∑ j, (if i = j then gramR P i j else 0) * (bit (x i) * bit (x j))
      = 4 * ∑ u, bit (x u) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_congr rfl (fun j _ => by
      rw [ite_mul, zero_mul] : ∀ j ∈ Finset.univ,
        (if i = j then gramR P i j else 0) * (bit (x i) * bit (x j))
          = if i = j then gramR P i j * (bit (x i) * bit (x j)) else 0)]
    rw [Finset.sum_ite_eq Finset.univ i (fun j => gramR P i j * (bit (x i) * bit (x j)))]
    simp only [Finset.mem_univ, if_true]
    rw [gramR_diag P hV i, bit_sq]
  rw [hLHS, hsplit, hoff, hdiag]

/-- **The HNBM energy of the reduced network is the paper's objective.**

`E(x̂) = ½‖Âx̂ − b̂‖² − ½‖b̂‖²`. The left side is `HopfieldNet.Quiver.BM`'s `{0,1}` Boltzmann
Hamiltonian at `netParams`; the right side is `p(x̂)` of (11)–(13), less the constant that (4)
drops. Every statement HNBM proves about minimising `zeroOneHamiltonian` — Lyapunov descent,
Gibbs stationarity, the zero-temperature limit — therefore lands on the Sudoku objective. -/
theorem zeroOneHamiltonian_eq (P : Problem) [Nonempty (Fin P.nvars)] (hV : P.Valid)
    (x : Fin P.nvars → Bool) :
    HopfieldEnergy.zeroOneHamiltonian (netParams P) (stateOfBits P x) = (penaltyR P x - constR P) / 2 := by
  have hact : ∀ i, (stateOfBits P x).act i = bit (x i) := fun _ => rfl
  have hθ : ∀ i, ((netParams P).θ i).get TwoState.fin0 = thetaR P i := fun _ => rfl
  -- the three aggregates the identity is stated in
  set Q := ∑ r ∈ Finset.range numRows, rowSumR P x r ^ 2 with hQ
  set C := ∑ r ∈ Finset.range numRows, bhatR P r * rowSumR P x r with hC
  set B := ∑ u, bit (x u) with hB
  -- linear term: `θ̂ᵀx̂ = 2·|x̂| − b̂ᵀÂx̂`
  have hlin : ∑ i, thetaR P i * bit (x i) = 2 * B - C := by
    rw [Finset.sum_congr rfl fun i _ => by rw [thetaR_eq P hV i, sub_mul],
      Finset.sum_sub_distrib]
    congr 1
    · rw [hB, Finset.mul_sum]
    · rw [Finset.sum_congr rfl fun i _ => Finset.sum_mul _ _ _, Finset.sum_comm, hC]
      refine Finset.sum_congr rfl fun r _ => ?_
      unfold rowSumR
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
  -- the objective expanded against the same aggregates
  have hpen : penaltyR P x = Q - 2 * C + constR P := by
    unfold penaltyR constR
    rw [Finset.sum_congr rfl fun r _ => by
      rw [sub_sq, show rowSumR P x r ^ 2 - 2 * rowSumR P x r * bhatR P r + bhatR P r ^ 2
          = rowSumR P x r ^ 2 - 2 * (bhatR P r * rowSumR P x r) + bhatR P r ^ 2 by ring]]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hQ, hC]
  unfold HopfieldEnergy.zeroOneHamiltonian
  -- rewrite the quadratic form *before* unfolding the activations, so its pattern still matches
  rw [quad_eq P hV x]
  simp only [hact, hθ]
  rw [hlin, hpen]
  ring

end Problem
end CNS
