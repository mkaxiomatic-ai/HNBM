/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.QUBO.Instances.Queens.Examples
import HopfieldNet.QUBO.Converge
import HopfieldNet.QUBO.Gibbs

/-!
# The queens network: descent, and concentration on the completions

`QUBO.Converge` and `QUBO.Gibbs` are stated for an arbitrary `Wf` problem, so the `n`-queens
QUBO inherits both without a word of queens-specific argument. This module cashes that in, and
supplies the one thing the generic theory cannot: the identification of the *feasible set* with
the set of genuine completions of the board.

## What is proved

* `energy_stateOf` — a completion, encoded, is a state of minimum energy.
* `isQueens_decode_of_minEnergy` — **conversely**, every minimum-energy state decodes to a board
  the checker accepts. Together with the above this pins the energy minimisers of the queens
  network to exactly the completions, in both directions.
* `classic8_exists_stable` — `QUBO.Converge`'s descent result at the 8-queens network: from any
  starting state, finitely many sweeps reach a state no single-site update moves.
* `classic8_feasible_fraction_tendsto_one`, `classic8_πBoltzVec_infeasible_tendsto_zero`,
  `classic8_stationary_infeasible_tendsto_zero` — `QUBO.Gibbs` at the same network: as the
  temperature falls to absolute zero, the equilibrium law of the random-scan Gibbs chain puts
  all of its mass on the solutions of the puzzle.

## What this does and does not say

It is a statement about the **equilibrium law at temperature `T`**, in the limit `T → 0⁺`. It is
*not* a statement about a cooling schedule, and in particular it is not a guarantee that a run of
`QUBO.Queens.anneal` finds a completion — measured over 40 seeds, a single annealed run settles
on the empty `8 × 8` board `0/40` times (see `QUBO.Queens.fireProps`). What the limit does say is
that the failure is a property of the *schedule*, not of the encoding: the measure the chain is
trying to sample from does concentrate on the 92 solutions, so a slow enough schedule at
equilibrium would find one. The swarm of eq. (7) is the library's practical answer instead.

The dynamics here is the random-scan single-site Gibbs chain, not `bmmStep`'s momentum
recurrence; see the module docstring of `QUBO.Gibbs`.
-/

namespace QUBO
namespace Problem

open TwoState HopfieldEnergy Finset Filter Topology

attribute [local instance] Classical.propDecidable

variable (P : Problem)

/-- **The executable objective and the abstract one vanish together.**

`QUBO.Refine.rowSumR_eq` matches the two row sums; this lifts that to the objective, which is
what lets an instance's `penaltyDoubled` soundness theorem feed the network theory. The two
row-level halves are `QUBO.Queens.penalty_zero_row` and `penalty_zero_of_rowSums`, which are
already stated for an arbitrary `Problem`. -/
theorem penaltyR_bitsOf_eq_zero_iff (hW : P.Wf) (x : Array Bool) :
    penaltyR P (bitsOf P x) = 0 ↔ P.penaltyDoubled x = 0 := by
  rw [penaltyR_eq_zero_iff]
  constructor
  · intro h
    refine Queens.penalty_zero_of_rowSums P fun r hr => ?_
    have h1 := h r (Finset.mem_range.mpr hr)
    rw [rowSumR_eq P hW x hr] at h1
    simp only [bhatR] at h1
    exact_mod_cast h1
  · intro h r hr
    have hr' := Finset.mem_range.mp hr
    rw [rowSumR_eq P hW x hr', Queens.penalty_zero_row P h hr']
    rfl

variable [Nonempty (Fin P.nvars)]

/-- **`stateOfBits` and `bitsOfState` are inverse in the other direction too.**

`QUBO.Minimizers` proves `stateOfBits (bitsOfState s) = s`; this is the companion, and is what
turns a bit vector with zero penalty into a state of minimum energy. -/
theorem bitsOfState_stateOfBits (x : Fin P.nvars → Bool) :
    bitsOfState P (stateOfBits P x) = x := by
  funext u
  have h : (stateOfBits P x).act u = bit (x u) := rfl
  unfold bitsOfState
  rw [h]
  by_cases hx : x u = true
  · rw [hx]; simp [bit]
  · rw [Bool.not_eq_true] at hx; rw [hx]; simp [bit]

end Problem

namespace Queens

open QUBO.Problem TwoState HopfieldEnergy Finset Filter Topology

attribute [local instance] Classical.propDecidable

variable (I : Instance) [Nonempty (Fin (problem I).nvars)]

/-! ## The minimisers of the queens network are exactly the completions -/

/-- A board, encoded, as a state of the network. -/
noncomputable def stateOf (q : Array Nat) : QState (problem I) :=
  stateOfBits (problem I) (bitsOf (problem I) (I.encode q))

/-- The bits of a state, back as an executable array. -/
noncomputable def arrOfState (s : QState (problem I)) : Array Bool :=
  (Array.range (problem I).nvars).map fun u =>
    if h : u < (problem I).nvars then bitsOfState (problem I) s ⟨u, h⟩ else false

theorem bitsOf_arrOfState (s : QState (problem I)) :
    bitsOf (problem I) (arrOfState I s) = bitsOfState (problem I) s := by
  funext u
  show (arrOfState I s).getD u.val false = _
  rw [arrOfState, map_range_getD _ _ _ u.isLt, dif_pos u.isLt]

/-- **A completion, encoded, is a state of minimum energy.** -/
theorem energy_stateOf (hG : I.givensOk = true) {q : Array Nat} (hq : I.isQueens q = true) :
    zeroOneHamiltonian (netParams (problem I)) (stateOf I q) = minEnergy (problem I) := by
  rw [energy_eq_min_iff (problem I) (problem_wf I), stateOf,
    bitsOfState_stateOfBits (problem I)]
  exact (penaltyR_bitsOf_eq_zero_iff (problem I) (problem_wf I) _).mpr
    (encode_penalty_zero I hG hq)

/-- **Conversely, every minimum-energy state decodes to a genuine completion.**

This is the direction the generic theory cannot supply: `QUBO.Minimizers` knows the minimisers
are the zero-penalty assignments, and `decode_isQueens` turns a zero-penalty assignment into a
board the checker accepts. -/
theorem isQueens_decode_of_minEnergy (hG : I.givensOk = true) {s : QState (problem I)}
    (hs : zeroOneHamiltonian (netParams (problem I)) s = minEnergy (problem I)) :
    I.isQueens (I.decode (arrOfState I s)) = true := by
  refine decode_isQueens I hG ?_
  refine (penaltyR_bitsOf_eq_zero_iff (problem I) (problem_wf I) _).mp ?_
  rw [bitsOf_arrOfState]
  exact (energy_eq_min_iff (problem I) (problem_wf I) s).mp hs

/-- **The queens network has a state of minimum energy iff the board can be completed.** -/
theorem exists_minEnergy_iff (hG : I.givensOk = true) :
    (∃ s : QState (problem I),
        zeroOneHamiltonian (netParams (problem I)) s = minEnergy (problem I))
      ↔ ∃ q, I.isQueens q = true :=
  ⟨fun ⟨_, hs⟩ => ⟨_, isQueens_decode_of_minEnergy I hG hs⟩,
   fun ⟨q, hq⟩ => ⟨stateOf I q, energy_stateOf I hG hq⟩⟩

/-! ## The 8-queens network

`classic8` carries the `Nonempty (Fin _)` instance from `QUBO.Queens.Examples`, and `sol8` is a
completion of it, so both hypotheses of the generic theory are discharged. -/

/-- The hypothesis `QUBO.Gibbs` asks for: some state attains the minimum energy. -/
theorem classic8_exists_minEnergy :
    ∃ s : QState (problem classic8),
      zeroOneHamiltonian (netParams (problem classic8)) s = minEnergy (problem classic8) :=
  (exists_minEnergy_iff classic8 classic8_ok).mpr ⟨sol8, sol8_isQueens⟩

/-- **Descent terminates on the 8-queens network.** From any state, finitely many sweeps reach a
state that no single-site update changes. `QUBO.Converge.exists_stable`, instantiated. -/
theorem classic8_exists_stable (s : QState (problem classic8)) :
    ∃ k, ∀ u, ((sweep (problem classic8))^[k] s).Up (netParams (problem classic8)) u
      = (sweep (problem classic8))^[k] s :=
  exists_stable (problem classic8) (problem_wf classic8) s

/-- **The Boltzmann mass of the 8-queens solutions tends to the whole mass as `T → 0⁺`.** -/
theorem classic8_feasible_fraction_tendsto_one :
    Tendsto (fun T : ℝ =>
        feasibleMass (problem classic8) T / partitionSum (problem classic8) T)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) :=
  feasible_fraction_tendsto_one (problem classic8) (problem_wf classic8)
    classic8_exists_minEnergy

/-- **The equilibrium law of the 8-queens Gibbs chain concentrates on the solutions.**

The mass the Boltzmann law gives to the non-solutions tends to `0` as the temperature tends to
absolute zero from above. -/
theorem classic8_πBoltzVec_infeasible_tendsto_zero :
    Tendsto (fun T : Temperature =>
        ∑ s ∈ infeasibleStates (problem classic8),
          (πBoltzVec (NN := TwoState.ZeroOne ℝ (Fin (problem classic8).nvars))
            (spec := zeroOneEnergySpec) (p := netParams (problem classic8)) (T := T)).val s)
      (nhdsWithin 0 {T : Temperature | 0 < T.toReal}) (nhds 0) :=
  πBoltzVec_infeasible_tendsto_zero (problem classic8) (problem_wf classic8)
    classic8_exists_minEnergy

/-- **The same, on the chain's own unique stationary distribution.**

This is the statement the paper wants, at a concrete NP-complete instance: the unique equilibrium
law of the random-scan Gibbs chain of the 8-queens QUBO gives vanishing mass to everything that
is not a solution of the puzzle. By `isQueens_decode_of_minEnergy` the surviving states really do
decode to placements the checker accepts. -/
theorem classic8_stationary_infeasible_tendsto_zero :
    Tendsto (fun T : Temperature =>
        ∑ s ∈ infeasibleStates (problem classic8),
          (Classical.choose
            (RSrow_exists_unique_stationary_distribution
              (NN := TwoState.ZeroOne ℝ (Fin (problem classic8).nvars))
              (spec := zeroOneEnergySpec) (p := netParams (problem classic8))
              (T := T)).exists).val s)
      (nhdsWithin 0 {T : Temperature | 0 < T.toReal}) (nhds 0) :=
  stationary_infeasible_tendsto_zero (problem classic8) (problem_wf classic8)
    classic8_exists_minEnergy

/-! ## A blocked board

The same theory applies verbatim, and says something different: `blocked6` has no completion, so
by `exists_minEnergy_iff` its network has **no** state of minimum energy in the sense of
`minEnergy = −‖b̂‖²/2` — the bound is never attained. The Gibbs limits above are exactly the
statements whose hypothesis fails here, which is why they need `hfeas` and not merely `Wf`. -/

instance : Nonempty (Fin (problem blocked6).nvars) := ⟨⟨0, by decide +kernel⟩⟩

/-- **The blocked 6×6 network never attains the energy lower bound.** -/
theorem blocked6_no_minEnergy :
    ¬ ∃ s : QState (problem blocked6),
        zeroOneHamiltonian (netParams (problem blocked6)) s = minEnergy (problem blocked6) :=
  fun h => blocked6_no_queens ((exists_minEnergy_iff blocked6 blocked6_ok).mp h)

/-! ## Axioms -/

#print axioms isQueens_decode_of_minEnergy
#print axioms exists_minEnergy_iff
#print axioms classic8_exists_stable
#print axioms classic8_stationary_infeasible_tendsto_zero
#print axioms blocked6_no_minEnergy

end Queens
end QUBO
