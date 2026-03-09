/-
Copyright (c) 2024 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import Mathlib.Combinatorics.Quiver.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Data.List.Pairwise

open Finset Mathlib

universe uR uU uζ v

structure NeuralNetwork (R : Type uR) (U : Type uU) (ζ : Type uζ) [Zero R]
    extends Quiver.{v, uU} U where
  (Ui Uo Uh : Set U)
  (hUi : Ui ≠ ∅)
  (hUo : Uo ≠ ∅)
  (hU : Set.univ = (Ui ∪ Uo ∪ Uh))
  (hhio : Uh ∩ (Ui ∪ Uo) = ∅)
  (κ1 κ2 : U → ℕ)
  (fnet : ∀ u : U, (U → R) → (U → R) → Vector R (κ1 u) → R)
  (fact : ∀ u : U, ζ → R → Vector R (κ2 u) → ζ)
  (fout : ∀ _ : U, ζ → R)
  (m : ζ → R)
  (pact : ζ → Prop)
  (pw : ∀ (u v : U), (u ⟶ v) → Prop)
  (pwMat : Matrix U U Prop := fun u v => ∃ f : (u ⟶ v), pw u v f)
  (pm : Matrix U U R → Prop)
  (hpact : ∀ (w : Matrix U U R) (_ : ∀ (u v : U), ¬pwMat u v → w u v = 0)
    (_ : ∀ u v (f : Hom u v), pw u v f) (_ : pm w) (σ : (u : U) → Vector R (κ1 u))
    (θ : (u : U) → Vector R (κ2 u)) (act : U → ζ),
    (∀ u : U, pact (act u)) → (∀ u : U, pact (fact u v (fnet u (w u)
    (fun v ↦ fout v (act v)) (σ u)) (θ u))))


variable {R U ζ : Type} [Zero R]

/--
`Params` is a structure that holds the external parameters for a given
neural network `NN`, along with a proof that the network's internal
parameters (its arrows) satisfy the required predicate `NN.pw`.
-/
structure Params (NN : NeuralNetwork R U ζ) where
  /-- A proof that all arrows in the neural network satisfy its parameter predicate `pw`. -/
  (h_arrows : ∀ u v (f : NN.Hom u v), NN.pw u v f)
  (w : Matrix U U R)
  /-- External parameters for the `fnet` function (e.g., biases). -/
  (σ : ∀ u : U, Vector R (NN.κ1 u))
  /-- External parameters for the `fact` function (e.g., activation function parameters). -/
  (θ : ∀ u : U, Vector R (NN.κ2 u))
  /-- The equivalent of `hw`: If there is no valid arrow between u and v, the weight must be 0. -/
  (hw : ∀ u v, ¬ NN.pwMat u v → w u v = 0)
  -- /-- 4. Matrix Validity (hw'):
  --     The matrix `w` must satisfy the global parameter predicate `pm`. -/
  (hw' : NN.pm w)

namespace NeuralNetwork

structure State (NN : NeuralNetwork R U ζ) where
  act : U → ζ
  hp : ∀ u : U, NN.pact (act u)

/-- Extensionality lemma for neural network states -/
@[ext]
lemma ext {R U ζ : Type} [Zero R] {NN : NeuralNetwork R U ζ}
    {s₁ s₂ : NN.State} : (∀ u, s₁.act u = s₂.act u) → s₁ = s₂ := by
  intro h
  cases s₁
  cases s₂
  simp only [NeuralNetwork.State.mk.injEq]
  apply funext
  exact h

namespace State

variable {NN : NeuralNetwork R U ζ} (wσθ : Params NN) (s : NN.State)

def out (u : U) : R := NN.fout u (s.act u)
def net (u : U) : R := NN.fnet u (wσθ.w u) (fun v => s.out v) (wσθ.σ u)
def onlyUi : Prop := ∃ ζ0 : ζ, ∀ u : U, u ∉ NN.Ui → s.act u = ζ0

variable [DecidableEq U]

def Up (u : U) : NeuralNetwork.State NN :=
  { act := fun v => if v = u then NN.fact u (s.act u) (s.net wσθ u) (wσθ.θ u)
              else s.act v, hp := by
      intro v
      split
      · apply NN.hpact
        intros u' v' hu'v'
        exact wσθ.hw u' v' hu'v'
        exact wσθ.h_arrows
        exact wσθ.hw'
        exact fun u ↦ s.hp u
      · apply s.hp}

def workPhase (extu : NN.State) (_ : extu.onlyUi) (uOrder : List U) : NN.State :=
  uOrder.foldl (fun s_iter u_iter => s_iter.Up wσθ u_iter) extu

def seqStates (useq : ℕ → U) : ℕ → NeuralNetwork.State NN
  | 0 => s
  | n + 1 => (seqStates useq n).Up wσθ (useq n)

def isStable : Prop :=  ∀ (u : U), (s.Up wσθ u).act u = s.act u

end State
end NeuralNetwork
