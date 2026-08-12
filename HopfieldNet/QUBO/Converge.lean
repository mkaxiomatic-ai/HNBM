import HopfieldNet.QUBO.Sweep

namespace QUBO
namespace Problem

open Finset

variable (P : Problem) [Nonempty (Fin P.nvars)]

theorem descent (s : (TwoState.ZeroOne ℝ (Fin P.nvars)).State) (u : Fin P.nvars) :
    HopfieldEnergy.zeroOneHamiltonian (netParams P) (s.Up (netParams P) u)
      ≤ HopfieldEnergy.zeroOneHamiltonian (netParams P) s := by
  exact TwoState.EnergySpec'.energy_is_lyapunov_at_site'' _ HopfieldEnergy.zeroOneEnergySpec
    (netParams P) s u (by rcases s.hp u with h | h; exacts [Or.inr h, Or.inl h])

/-! ## The energy takes values in `½ℤ` -/

omit [Nonempty (Fin P.nvars)] in
/-- The objective takes values in `ℕ`. -/
theorem exists_nat_penaltyR (x : Fin P.nvars → Bool) : ∃ n : ℕ, penaltyR P x = (n : ℝ) := by
  obtain ⟨m, hm⟩ := exists_int_penaltyR P x
  have h0 : (0 : ℝ) ≤ (m : ℝ) := hm ▸ penaltyR_nonneg P x
  have : (0 : ℤ) ≤ m := by exact_mod_cast h0
  exact ⟨m.toNat, by rw [hm]; exact_mod_cast (Int.toNat_of_nonneg this).symm⟩

/-- **The level of a state**: the integer value of the objective at its bits.

Every energy the dynamics can visit is `(penIndex − ‖b̂‖²)/2`, so `penIndex` is a `ℕ`-valued
proxy for the energy: it decreases exactly when the energy does, and it cannot decrease
forever. -/
noncomputable def penIndex (s : (TwoState.ZeroOne ℝ (Fin P.nvars)).State) : ℕ :=
  ⌊penaltyR P (bitsOfState P s)⌋₊

theorem penaltyR_eq_penIndex (s : (TwoState.ZeroOne ℝ (Fin P.nvars)).State) :
    penaltyR P (bitsOfState P s) = (penIndex P s : ℝ) := by
  obtain ⟨n, hn⟩ := exists_nat_penaltyR P (bitsOfState P s)
  rw [penIndex, hn, Nat.floor_natCast]

/-- The energy in terms of the level: `E = (penIndex − ‖b̂‖²)/2`. -/
theorem energy_eq_penIndex (hW : P.Wf) (s : (TwoState.ZeroOne ℝ (Fin P.nvars)).State) :
    HopfieldEnergy.zeroOneHamiltonian (netParams P) s = ((penIndex P s : ℝ) - constR P) / 2 := by
  rw [← penaltyR_eq_penIndex, ← stateOfBits_bitsOfState P s, zeroOneHamiltonian_eq P hW]
  simp only [stateOfBits_bitsOfState]

/-- The level is `2·(E − E_min)`: the honest form of the "number of half-units above the
minimum". -/
theorem penIndex_eq_two_mul (hW : P.Wf) (s : (TwoState.ZeroOne ℝ (Fin P.nvars)).State) :
    (penIndex P s : ℝ)
      = 2 * (HopfieldEnergy.zeroOneHamiltonian (netParams P) s - minEnergy P) := by
  rw [energy_eq_penIndex P hW s, minEnergy]; ring

/-- Energy comparison is level comparison. -/
theorem energy_lt_iff_penIndex_lt (hW : P.Wf)
    (s t : (TwoState.ZeroOne ℝ (Fin P.nvars)).State) :
    HopfieldEnergy.zeroOneHamiltonian (netParams P) s
        < HopfieldEnergy.zeroOneHamiltonian (netParams P) t ↔ penIndex P s < penIndex P t := by
  rw [energy_eq_penIndex P hW s, energy_eq_penIndex P hW t]
  constructor
  · intro h
    have : (penIndex P s : ℝ) < (penIndex P t : ℝ) := by linarith
    exact_mod_cast this
  · intro h
    have : (penIndex P s : ℝ) < (penIndex P t : ℝ) := by exact_mod_cast h
    linarith

/-- Energy equality is level equality. -/
theorem energy_eq_iff_penIndex_eq (hW : P.Wf)
    (s t : (TwoState.ZeroOne ℝ (Fin P.nvars)).State) :
    HopfieldEnergy.zeroOneHamiltonian (netParams P) s
        = HopfieldEnergy.zeroOneHamiltonian (netParams P) t ↔ penIndex P s = penIndex P t := by
  rw [energy_eq_penIndex P hW s, energy_eq_penIndex P hW t]
  constructor
  · intro h
    have : (penIndex P s : ℝ) = (penIndex P t : ℝ) := by linarith
    exact_mod_cast this
  · intro h; rw [h]

/-! ## Quantised descent -/

/-- **A site update never raises the level.** -/
theorem descent_penIndex (hW : P.Wf) (s : (TwoState.ZeroOne ℝ (Fin P.nvars)).State)
    (u : Fin P.nvars) : penIndex P (s.Up (netParams P) u) ≤ penIndex P s := by
  rcases eq_or_lt_of_le (descent P s u) with h | h
  · exact ((energy_eq_iff_penIndex_eq P hW _ _).mp h).le
  · exact ((energy_lt_iff_penIndex_lt P hW _ _).mp h).le

/-- **Quantised descent.** A single memoryless site update either leaves the energy exactly
where it was, or lowers it by at least `1/2`.

There is no third possibility: by `exists_int_penaltyR` the energy lives in the lattice
`(ℤ − ‖b̂‖²)/2`, so a strict decrease is a decrease by a whole half-unit. This is what turns
the Lyapunov inequality of `descent` — which on its own permits an infinite strictly decreasing
sequence — into a termination argument. -/
theorem descent_quantised (hW : P.Wf) (s : (TwoState.ZeroOne ℝ (Fin P.nvars)).State)
    (u : Fin P.nvars) :
    HopfieldEnergy.zeroOneHamiltonian (netParams P) (s.Up (netParams P) u)
        = HopfieldEnergy.zeroOneHamiltonian (netParams P) s
      ∨ HopfieldEnergy.zeroOneHamiltonian (netParams P) (s.Up (netParams P) u) + 1 / 2
        ≤ HopfieldEnergy.zeroOneHamiltonian (netParams P) s := by
  rcases eq_or_lt_of_le (descent_penIndex P hW s u) with h | h
  · exact Or.inl ((energy_eq_iff_penIndex_eq P hW _ _).mpr h)
  · refine Or.inr ?_
    have hcast : (penIndex P (s.Up (netParams P) u) : ℝ) + 1 ≤ (penIndex P s : ℝ) := by
      exact_mod_cast h
    rw [energy_eq_penIndex P hW, energy_eq_penIndex P hW]
    linarith

/-! ## Termination along an arbitrary sequence of sites -/

/-- `seqStates` unrolled by one step. -/
theorem seqStates_succ (s : (TwoState.ZeroOne ℝ (Fin P.nvars)).State) (useq : ℕ → Fin P.nvars)
    (n : ℕ) :
    s.seqStates (netParams P) useq (n + 1)
      = (s.seqStates (netParams P) useq n).Up (netParams P) (useq n) := rfl

/-- The level is antitone along any run of single-site updates. -/
theorem penIndex_seqStates_antitone (hW : P.Wf) (s : (TwoState.ZeroOne ℝ (Fin P.nvars)).State)
    (useq : ℕ → Fin P.nvars) :
    Antitone (fun n => penIndex P (s.seqStates (netParams P) useq n)) :=
  antitone_nat_of_succ_le fun n => by
    rw [seqStates_succ]; exact descent_penIndex P hW _ _

/-- **(a) The energy of a run is eventually constant.**

For *any* sequence of sites — not just a fair or cyclic one — the energy stops changing after
finitely many updates. -/
theorem energy_seqStates_eventually_const (hW : P.Wf)
    (s : (TwoState.ZeroOne ℝ (Fin P.nvars)).State) (useq : ℕ → Fin P.nvars) :
    ∃ N, ∀ n, N ≤ n →
      HopfieldEnergy.zeroOneHamiltonian (netParams P) (s.seqStates (netParams P) useq n)
        = HopfieldEnergy.zeroOneHamiltonian (netParams P) (s.seqStates (netParams P) useq N) := by
  let g : ℕ → ℕ := fun n => penIndex P (s.seqStates (netParams P) useq n)
  obtain ⟨N, hN⟩ : ∃ N, g N = sInf (Set.range g) :=
    (Nat.sInf_mem (⟨g 0, 0, rfl⟩ : (Set.range g).Nonempty)).imp fun _ h => h
  refine ⟨N, fun n hn => ?_⟩
  refine (energy_eq_iff_penIndex_eq P hW _ _).mpr ?_
  have h1 : g n ≤ g N := penIndex_seqStates_antitone P hW s useq hn
  have h2 : sInf (Set.range g) ≤ g n := Nat.sInf_le ⟨n, rfl⟩
  show g n = g N
  omega

/-- **(c) A quantitative bound.** Along any run, the number of strictly improving steps taken in
the first `N` updates, plus the level still remaining, is at most the level one started at. -/
theorem card_improvements_add_penIndex_le (hW : P.Wf)
    (s : (TwoState.ZeroOne ℝ (Fin P.nvars)).State) (useq : ℕ → Fin P.nvars) (N : ℕ) :
    ((Finset.range N).filter fun n =>
        HopfieldEnergy.zeroOneHamiltonian (netParams P) (s.seqStates (netParams P) useq (n + 1))
          < HopfieldEnergy.zeroOneHamiltonian
              (netParams P) (s.seqStates (netParams P) useq n)).card
      + penIndex P (s.seqStates (netParams P) useq N) ≤ penIndex P s := by
  induction N with
  | zero =>
    simp only [Finset.range_zero, Finset.filter_empty, Finset.card_empty, zero_add]
    exact le_rfl
  | succ N ih =>
    have hstep := seqStates_succ P s useq N
    rw [Finset.range_add_one, Finset.filter_insert]
    by_cases h : HopfieldEnergy.zeroOneHamiltonian (netParams P)
        (s.seqStates (netParams P) useq (N + 1))
        < HopfieldEnergy.zeroOneHamiltonian (netParams P) (s.seqStates (netParams P) useq N)
    · rw [if_pos h, Finset.card_insert_of_notMem (by simp)]
      have hlt : penIndex P (s.seqStates (netParams P) useq (N + 1))
          < penIndex P (s.seqStates (netParams P) useq N) :=
        (energy_lt_iff_penIndex_lt P hW _ _).mp h
      omega
    · rw [if_neg h]
      have hle : penIndex P (s.seqStates (netParams P) useq (N + 1))
          ≤ penIndex P (s.seqStates (netParams P) useq N) := by
        rw [hstep]; exact descent_penIndex P hW _ _
      omega

/-- **(c), in energy units.** At most `2·(E(s) − E_min)` of the first `N` updates can strictly
improve the energy — each such update costs a full half-unit, and there are only
`2·(E(s) − E_min)` half-units to spend. -/
theorem card_improvements_le (hW : P.Wf) (s : (TwoState.ZeroOne ℝ (Fin P.nvars)).State)
    (useq : ℕ → Fin P.nvars) (N : ℕ) :
    ((((Finset.range N).filter fun n =>
        HopfieldEnergy.zeroOneHamiltonian (netParams P) (s.seqStates (netParams P) useq (n + 1))
          < HopfieldEnergy.zeroOneHamiltonian
              (netParams P) (s.seqStates (netParams P) useq n)).card : ℕ) : ℝ)
      ≤ 2 * (HopfieldEnergy.zeroOneHamiltonian (netParams P) s - minEnergy P) := by
  rw [← penIndex_eq_two_mul P hW]
  have := card_improvements_add_penIndex_le P hW s useq N
  exact_mod_cast le_trans (Nat.le_add_right _ _) this

/-! ## Reaching a fixed point

Energy alone cannot prove that the *state* stops moving: an update at a site whose local field
is exactly `0` sets the neuron to `1` at no energy cost. The second component of the measure
below counts exactly those moves. `Up` breaks the tie towards `1`, so a zero-cost move can only
turn a `0` into a `1`, and there are at most `nvars` of those between energy drops. -/

/-- The activation after an update, unfolded. -/
theorem up_act (s : (TwoState.ZeroOne ℝ (Fin P.nvars)).State) (u v : Fin P.nvars) :
    (s.Up (netParams P) u).act v
      = if v = u then
          (if ((netParams P).θ u).get TwoState.fin0 ≤ s.net (netParams P) u then (1 : ℝ) else 0)
        else s.act v := rfl

/-- An update that does not move site `u` does not move the state at all. -/
theorem up_eq_self_of_act_eq (s : (TwoState.ZeroOne ℝ (Fin P.nvars)).State) (u : Fin P.nvars)
    (h : (s.Up (netParams P) u).act u = s.act u) : s.Up (netParams P) u = s := by
  refine NeuralNetwork.ext fun v => ?_
  rw [up_act]
  by_cases hv : v = u
  · subst hv; rw [if_pos rfl]; rw [up_act, if_pos rfl] at h; exact h
  · rw [if_neg hv]

/-- **A downward flip strictly lowers the energy.** If the local field at `u` is negative and
the neuron is on, switching it off gains `−L > 0`. -/
theorem energy_lt_of_flip_down (s : (TwoState.ZeroOne ℝ (Fin P.nvars)).State) (u : Fin P.nvars)
    (hold : s.act u = 1)
    (hlt : ¬ ((netParams P).θ u).get TwoState.fin0 ≤ s.net (netParams P) u) :
    HopfieldEnergy.zeroOneHamiltonian (netParams P) (s.Up (netParams P) u)
      < HopfieldEnergy.zeroOneHamiltonian (netParams P) s := by
  have hupNeg : s.Up (netParams P) u = TwoState.updNeg s u := by
    refine NeuralNetwork.ext fun v => ?_
    rw [up_act]
    show _ = Function.update s.act u (0 : ℝ) v
    rw [Function.update_apply]
    by_cases hv : v = u
    · subst hv; rw [if_pos rfl, if_pos rfl, if_neg hlt]
    · rw [if_neg hv, if_neg hv]
  have hupPos : TwoState.updPos s u = s := TwoState.updPos_eq_self_of_act_pos s u hold
  have hflip : HopfieldEnergy.zeroOneHamiltonian (netParams P) (TwoState.updPos s u)
      - HopfieldEnergy.zeroOneHamiltonian (netParams P) (TwoState.updNeg s u)
      = -(s.net (netParams P) u - ((netParams P).θ u).get TwoState.fin0) :=
    HopfieldEnergy.zeroOneHamiltonian_flip_relation (netParams P) s u
  rw [hupPos] at hflip
  rw [hupNeg]
  have hnet : s.net (netParams P) u < ((netParams P).θ u).get TwoState.fin0 := not_le.mp hlt
  linarith

/-! ### Counting the neurons that are on -/

/-- The number of active neurons. -/
noncomputable def onesCount (s : (TwoState.ZeroOne ℝ (Fin P.nvars)).State) : ℕ :=
  (Finset.univ.filter fun u => bitsOfState P s u = true).card

theorem onesCount_le (s : (TwoState.ZeroOne ℝ (Fin P.nvars)).State) :
    onesCount P s ≤ P.nvars :=
  le_trans (Finset.card_filter_le _ _) (by simp)

/-- **An upward flip strictly increases the number of active neurons.** -/
theorem onesCount_lt_of_flip_up (s : (TwoState.ZeroOne ℝ (Fin P.nvars)).State) (u : Fin P.nvars)
    (hold : s.act u = 0) (hnew : (s.Up (netParams P) u).act u = 1) :
    onesCount P s < onesCount P (s.Up (netParams P) u) := by
  have hoff : ∀ v, v ≠ u → (s.Up (netParams P) u).act v = s.act v := fun v hv => by
    rw [up_act, if_neg hv]
  have hsub : (Finset.univ.filter fun v => bitsOfState P s v = true)
      ⊆ Finset.univ.filter fun v => bitsOfState P (s.Up (netParams P) u) v = true := by
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    by_cases hvu : v = u
    · subst hvu; simp only [bitsOfState, hold, decide_eq_true_eq] at hv; exact absurd hv zero_ne_one
    · simpa only [bitsOfState, hoff v hvu] using hv
  refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).mpr ⟨u, ?_, ?_⟩)
  · simp [bitsOfState, hnew]
  · simp [bitsOfState, hold]

/-! ### The descent measure -/

/-- The termination measure: the level, with the number of *inactive* neurons as tie-break.

Lexicographic order encoded in `ℕ`: an energy drop is worth a whole `nvars + 1`, and the
tie-break can only contribute `nvars`. -/
noncomputable def descentMeasure (s : (TwoState.ZeroOne ℝ (Fin P.nvars)).State) : ℕ :=
  penIndex P s * (P.nvars + 1) + (P.nvars - onesCount P s)

omit [Nonempty (Fin P.nvars)] in
private theorem lex_lt {p' p q' q n : ℕ} (hq' : q' ≤ n) (h : p' < p) :
    p' * (n + 1) + q' < p * (n + 1) + q := by
  have h1 : (p' + 1) * (n + 1) ≤ p * (n + 1) := Nat.mul_le_mul_right _ h
  have h2 : (p' + 1) * (n + 1) = p' * (n + 1) + (n + 1) := by ring
  omega

/-- **The key dichotomy: an update either changes nothing, or strictly lowers the measure.** -/
theorem up_eq_self_or_measure_lt (hW : P.Wf) (s : (TwoState.ZeroOne ℝ (Fin P.nvars)).State)
    (u : Fin P.nvars) :
    s.Up (netParams P) u = s
      ∨ descentMeasure P (s.Up (netParams P) u) < descentMeasure P s := by
  by_cases hup : s.Up (netParams P) u = s
  · exact Or.inl hup
  refine Or.inr ?_
  have hne : (s.Up (netParams P) u).act u ≠ s.act u := fun h => hup (up_eq_self_of_act_eq P s u h)
  by_cases hle : ((netParams P).θ u).get TwoState.fin0 ≤ s.net (netParams P) u
  · -- the neuron switches on: the level cannot rise, and the count of active neurons rises
    have hnew : (s.Up (netParams P) u).act u = 1 := by rw [up_act, if_pos rfl, if_pos hle]
    have hold : s.act u = 0 := by
      rcases s.hp u with h | h
      · exact h
      · exact absurd (hnew.trans h.symm) hne
    have hones := onesCount_lt_of_flip_up P s u hold hnew
    rcases lt_or_eq_of_le (descent_penIndex P hW s u) with h | h
    · exact lex_lt (Nat.sub_le _ _) h
    · unfold descentMeasure
      rw [h]
      have h1 := onesCount_le P s
      have h2 := onesCount_le P (s.Up (netParams P) u)
      omega
  · -- the neuron switches off: the energy strictly drops, so the level does
    have hnew : (s.Up (netParams P) u).act u = 0 := by rw [up_act, if_pos rfl, if_neg hle]
    have hold : s.act u = 1 := by
      rcases s.hp u with h | h
      · exact absurd (hnew.trans h.symm) hne
      · exact h
    have hE := energy_lt_of_flip_down P s u hold hle
    exact lex_lt (Nat.sub_le _ _) ((energy_lt_iff_penIndex_lt P hW _ _).mp hE)

/-! ### The sweep -/

/-- One full sweep: update every site once, in index order. -/
noncomputable def sweep (s : (TwoState.ZeroOne ℝ (Fin P.nvars)).State) :
    (TwoState.ZeroOne ℝ (Fin P.nvars)).State :=
  (List.finRange P.nvars).foldl (fun s u => s.Up (netParams P) u) s

/-- A scan of updates cannot raise the measure. -/
theorem measure_foldl_le (hW : P.Wf) :
    ∀ (us : List (Fin P.nvars)) (s : (TwoState.ZeroOne ℝ (Fin P.nvars)).State),
      descentMeasure P (us.foldl (fun s u => s.Up (netParams P) u) s) ≤ descentMeasure P s := by
  intro us
  induction us with
  | nil => intro s; exact le_rfl
  | cons u t ih =>
    intro s
    refine le_trans (ih _) ?_
    rcases up_eq_self_or_measure_lt P hW s u with h | h
    · exact le_of_eq (congrArg _ h)
    · exact h.le

/-- A scan that does not move the measure did not move the state — at any of its sites. -/
theorem foldl_fixed_of_measure_eq (hW : P.Wf) :
    ∀ (us : List (Fin P.nvars)) (s : (TwoState.ZeroOne ℝ (Fin P.nvars)).State),
      descentMeasure P (us.foldl (fun s u => s.Up (netParams P) u) s) = descentMeasure P s →
        us.foldl (fun s u => s.Up (netParams P) u) s = s ∧ ∀ u ∈ us, s.Up (netParams P) u = s := by
  intro us
  induction us with
  | nil => intro s _; exact ⟨rfl, by simp⟩
  | cons u t ih =>
    intro s h
    rw [List.foldl_cons] at h ⊢
    have hstep : s.Up (netParams P) u = s := by
      rcases up_eq_self_or_measure_lt P hW s u with hfix | hlt
      · exact hfix
      · exact absurd h (Nat.ne_of_lt (lt_of_le_of_lt (measure_foldl_le P hW t _) hlt))
    rw [hstep] at h ⊢
    obtain ⟨h1, h2⟩ := ih s h
    exact ⟨h1, by
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact hstep
      · exact h2 v hv⟩

/-- A sweep either leaves every site fixed, or strictly lowers the measure. -/
theorem sweep_stable_or_measure_lt (hW : P.Wf)
    (s : (TwoState.ZeroOne ℝ (Fin P.nvars)).State) :
    (∀ u, s.Up (netParams P) u = s) ∨ descentMeasure P (sweep P s) < descentMeasure P s := by
  rcases lt_or_eq_of_le (measure_foldl_le P hW (List.finRange P.nvars) s) with h | h
  · exact Or.inr h
  · exact Or.inl fun u =>
      (foldl_fixed_of_measure_eq P hW (List.finRange P.nvars) s h).2 u (List.mem_finRange u)

private theorem exists_stable_aux (hW : P.Wf) :
    ∀ (n : ℕ) (s : (TwoState.ZeroOne ℝ (Fin P.nvars)).State), descentMeasure P s ≤ n →
      ∃ k, ∀ u, ((sweep P)^[k] s).Up (netParams P) u = (sweep P)^[k] s := by
  intro n
  induction n with
  | zero =>
    intro s hs
    rcases sweep_stable_or_measure_lt P hW s with h | h
    · exact ⟨0, h⟩
    · omega
  | succ n ih =>
    intro s hs
    rcases sweep_stable_or_measure_lt P hW s with h | h
    · exact ⟨0, h⟩
    · obtain ⟨k, hk⟩ := ih (sweep P s) (by omega)
      exact ⟨k + 1, by rw [Function.iterate_succ_apply]; exact hk⟩

/-- **(b) The sweep reaches a fixed point in finitely many rounds.**

After at most `descentMeasure` sweeps the state is *stable*: no single-site update changes it,
so no further sweep — and indeed no update sequence whatsoever — changes it again. -/
theorem exists_stable (hW : P.Wf) (s : (TwoState.ZeroOne ℝ (Fin P.nvars)).State) :
    ∃ k, ∀ u, ((sweep P)^[k] s).Up (netParams P) u = (sweep P)^[k] s :=
  exists_stable_aux P hW (descentMeasure P s) s le_rfl

end Problem
end QUBO
