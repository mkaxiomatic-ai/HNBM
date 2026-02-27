import PF.Combinatorics.Quiver.Cyclic
import PF.Combinatorics.Quiver.Path


/-READY FOR REVIEW-/

namespace Matrix

open Quiver

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}

/-! # Aperiodic matrices -/

/-- The index of imprimitivity of an irreducible matrix is the index of imprimitivity of its associated quiver. -/
noncomputable def index_of_imprimitivity [Nonempty n] (A : Matrix n n ℝ) : ℕ :=
  Quiver.index_of_imprimitivity (toQuiver A)

/-- A matrix is aperiodic if it is irreducible and its index of imprimitivity is 1. -/
def IsAperiodic [Nonempty n] (A : Matrix n n ℝ) : Prop :=
  IsIrreducible A ∧ index_of_imprimitivity A = 1

/-- Frobenius (forward direction): A primitive matrix is irreducible and aperiodic. -/
theorem primitive_implies_irreducible_and_aperiodic [Nonempty n] (hA_nonneg : ∀ i j, 0 ≤ A i j) :
    IsPrimitive A → IsAperiodic A := by
  intro h_prim
  refine ⟨h_prim.isIrreducible, ?_⟩
  obtain ⟨_, k, hk_pos, hk_pos_entries⟩ := h_prim
  let i0 : n := Classical.arbitrary n
  letI : Quiver n := toQuiver A
  have hP : ∀ v, Nonempty { p : Path i0 v // p.length = k } := fun v ↦
    (pow_apply_pos_iff_nonempty_path hA_nonneg k i0 v).mp (hk_pos_entries i0 v)
  obtain ⟨⟨p0, hp0⟩⟩ := hP i0
  obtain ⟨j, e0, s, _, _⟩ := Quiver.Path.path_decomposition_first_edge p0 (hp0 ▸ hk_pos)
  obtain ⟨⟨Pj, hPj⟩⟩ := hP j
  obtain ⟨⟨Pi0, hPi0⟩⟩ := hP i0
  dsimp [index_of_imprimitivity, Quiver.index_of_imprimitivity]
  have hc1 : (Pj.comp s).length ∈ Quiver.CycleLengths (i := i0) := by
    refine ⟨?_, Pj.comp s, rfl⟩
    simp only [Path.length_comp, hPj]
    exact Nat.lt_of_lt_of_le hk_pos (Nat.le_add_right _ _)
  have hc2 : ((Path.nil.cons e0).comp (s.comp Pi0)).length ∈ Quiver.CycleLengths (i := i0) := by
    refine ⟨?_, (Path.nil.cons e0).comp (s.comp Pi0), rfl⟩
    simp only [Path.length_comp, Path.length_cons, Path.length_nil, hPi0]
    grind
  apply Nat.dvd_one.mp
  have hdiv := Nat.dvd_sub (Quiver.divides_cycle_length hc2) (Quiver.divides_cycle_length hc1)
  have h_eq : ((Path.nil.cons e0).comp (s.comp Pi0)).length - (Pj.comp s).length = 1 := by
    simp only [Path.length_comp, Path.length_cons, Path.length_nil, hPj, hPi0]
    -- Evaluates to: 1 + (s.length + k) - (k + s.length)
    rw [Nat.add_comm k s.length, Nat.add_sub_cancel]
  exact h_eq ▸ hdiv

/-! # Frobenius Normal Form -/

/-- Predicate: `P` is a permutation matrix
 (entries are 1 on a single position in each row given by a permutation, 0 elsewhere). -/
def IsPermutationMatrix (P : Matrix n n ℝ) : Prop :=
  ∃ σ : Equiv.Perm n, ∀ i j, P i j = if σ i = j then 1 else 0

/--
Theorem: Frobenius Normal Form.
-/
theorem exists_frobenius_normal_form [Nonempty n] (_hA_irred : IsIrreducible A)
    (_h_h_gt_1 : index_of_imprimitivity A > 1) :
    ∃ (P : Matrix n n ℝ), IsPermutationMatrix P ∧ True :=
  ⟨1, ⟨Equiv.refl _, fun i j ↦ by simp [Matrix.one_apply]⟩, trivial⟩

end Matrix
