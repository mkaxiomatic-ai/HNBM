import HopfieldNet.Quiver.HN.HNquivHebbian
import Mathlib.Analysis.Normed.Field.Lemmas

set_option linter.unusedVariables false
set_option maxHeartbeats 500000

open Mathlib Finset

variable {R U : Type} [Zero R]

/-!
### Non-orthogonal Hebbian learning

This section exercises the **non-orthogonal** Hebbian decomposition in `HopfieldNet/HN/Core.lean`:
for patterns `pᵢ ∈ {±1}^U`, the Hebbian field on pattern `pⱼ` splits as

- **signal**: \((|U| - m) pⱼ\)
- **interference**: `disturbance ps j`

No orthogonality assumption is used.
-/

section HopfieldNonOrthogonal

open Matrix Fintype

-- Two genuinely non-orthogonal patterns in `{±1}^(Fin 4)` over `ℚ`.
def pat0 : (HopfieldNetwork ℚ (Fin 4)).State :=
  { act := fun _ => (1 : ℚ)
    hp := by
      intro u
      unfold HopfieldNetwork
      simp }

def pat1 : (HopfieldNetwork ℚ (Fin 4)).State :=
  { act := fun i =>
      if (i : Fin 4) = 0 then (-1 : ℚ) else (1 : ℚ)
    hp := by
      intro u
      unfold HopfieldNetwork
      by_cases h : (u : Fin 4) = 0
      · -- at `u = 0`, activation is `-1`
        right
        simp [h]
      · -- otherwise, activation is `1`
        left
        simp [h] }

-- Package patterns as a `Fin 2 → State` family.
def ps_nonorth : Fin 2 → (HopfieldNetwork ℚ (Fin 4)).State := ![pat0, pat1]

-- The overlap is non-zero (here it is `2`).
#eval dotProduct pat0.act pat1.act

-- A concrete interference value (non-zero).
#eval disturbanceTerm (ps := ps_nonorth) (j := (1 : Fin 2)) (0 : Fin 4)

-- The exact non-orthogonal decomposition lemma.
theorem test_nonorthogonal_decomposition :
    ((Hebbian (ps := ps_nonorth)).w).mulVec (ps_nonorth (1 : Fin 2)).act =
      (card (Fin 4) - (2 : ℕ) : ℚ) • (ps_nonorth (1 : Fin 2)).act + disturbanceTerm ps_nonorth (1 : Fin 2) := by
  simpa using (patterns_pairwise_non_orthogonal (ps := ps_nonorth) (j := (1 : Fin 2)))

#eval (Hebbian (ps := ps_nonorth)).w.mulVec (ps_nonorth (1 : Fin 2)).act

end HopfieldNonOrthogonal
