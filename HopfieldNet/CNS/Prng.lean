/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# A deterministic, seedable PRNG

Neither HNBM nor Lean core ships a generator suitable here, and Li & Wang do not say which one
they used, so bit-level agreement with their MATLAB runs is out of reach in any case. What *is*
reachable — and what matters for a reproducible artifact — is that **our** runs be exactly
replayable from a seed, on any machine.

`splitmix64` is used: tiny, fast, no state-initialisation pitfalls, and it passes BigCrush. All
arithmetic is `UInt64`, so it wraps exactly as specified with no dependence on platform word
size.
-/

namespace CNS

/-- A `splitmix64` generator state. -/
structure Rng where
  /-- The 64-bit internal state. -/
  s : UInt64
  deriving Inhabited, Repr

namespace Rng

/-- Seed the generator. -/
@[inline] def seed (s : UInt64) : Rng := ⟨s⟩

/-- Draw a 64-bit word and advance the state. -/
@[inline] def next (g : Rng) : UInt64 × Rng :=
  let s := g.s + 0x9E3779B97F4A7C15
  let z := s
  let z := (z ^^^ (z >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (z ^^^ (z >>> 31), ⟨s⟩)

/-- A uniform `Float` in `[0,1)`, built from the top 53 bits so every output is exactly
representable. -/
@[inline] def nextFloat (g : Rng) : Float × Rng :=
  let (w, g') := g.next
  (Float.ofNat (w >>> 11).toNat * (1.0 / 9007199254740992.0), g')

/-- A uniform `Nat` in `[0, m)`; returns `0` when `m = 0`. -/
@[inline] def nextBelow (g : Rng) (m : Nat) : Nat × Rng :=
  let (w, g') := g.next
  (if m == 0 then 0 else w.toNat % m, g')

/-- A uniform `Bool`. -/
@[inline] def nextBool (g : Rng) : Bool × Rng :=
  let (w, g') := g.next
  ((w >>> 63) == 1, g')

/-- A uniform random bit vector of the given length. -/
def bits (g : Rng) (len : Nat) : Array Bool × Rng := Id.run do
  let mut out : Array Bool := Array.replicate len false
  let mut gg := g
  for i in [0:len] do
    let (b, g') := gg.nextBool
    gg := g'
    out := out.set! i b
  return (out, gg)

end Rng
end CNS
