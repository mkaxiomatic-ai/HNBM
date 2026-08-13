/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.QUBO.Instances.Queens.Bench

/-!
# The figures of the paper, pinned

`papers/lpar-queens/cns-queens.tex` draws chessboards: three blocked instances with the two
completions that refute one of them, two completable instances with their solutions, and the rows of
`Â` through one square of the `4 × 4` board. Every one of those pictures is a claim about this
development, and a picture cannot be type-checked.

So each is restated here as a `#guard`, which **fails during elaboration** if it stops holding. The
coordinates below are transcribed from the `\qcgivens` and `\qcplace` arguments in the figure source,
which are written in the same order as the Lean array literals precisely so that the transcription is
mechanical: `\qcgivens{0/0,1/6}` against `#[(0,0),(1,6)]`, and `\qcplace{2,0,3,1}` against
`#[2,0,3,1]`.

If a figure is edited and this file still compiles, the figure agrees with the code. If it stops
compiling, one of the two is wrong.
-/

namespace QUBO
namespace Queens
namespace Figures

open QUBO.Queens.Bench

/-- Whether the two givens of a figure attack each other, stated over `ℤ` with real subtraction, as
`Queens.Attack` is. Used to check that `fig:blocked`(a) draws its dashed segment and (b) does not. -/
def attacks (i a k b : Int) : Bool := (a == b) || (i - a == k - b) || (i + a == k + b)

/-- An instance matches what a figure draws: the board size and the givens, in the drawn order. -/
def drawn (I : Instance) (n : Nat) (g : Array (Nat × Nat)) : Bool :=
  I.size == n && I.givens == g

/-! ## `fig:inc` --- the rows of `Â` through one square

The left panel draws four capsules through the square `(1,2)` of the `4 × 4` board, labelled
`r₁, r₆, r₉, r₁₅`; the right panel draws three through the corner `(0,0)`, labelled `r₀, r₄, r₁₀`,
and a dotted ring on the anti-diagonal that generates no row.

The board of `fig:inc` has the size the caption states, `n = 26` and `m = 18`: -/

#guard
  let I : Instance := ⟨4, #[]⟩
  I.nvars == 26 && I.nrows == 18

/-! **The left panel.** The square `(1,2)` lies in exactly the four rows drawn, with exactly the
indices printed on them, and those indices are the ones the layout assigns to the four families the
capsules are coloured for: board row `1`, column `2`, and one row from each diagonal block. -/

#guard
  let I : Instance := ⟨4, #[]⟩
  (I.rowsOf (I.cellVar 1 2)).qsort (· < ·) == #[1, 6, 9, 15]
    && I.rowRow 1 == 1 && I.colRow 2 == 6 && I.diagRow 1 == 9 && I.antiRow 2 == 15

/-! **The right panel.** The corner `(0,0)` lies in exactly three rows, with the indices printed. -/

#guard
  let I : Instance := ⟨4, #[]⟩
  (I.rowsOf (I.cellVar 0 0)).qsort (· < ·) == #[0, 4, 10]
    && I.rowRow 0 == 0 && I.colRow 0 == 4 && I.diagRow 2 == 10

/-! Each capsule is drawn through exactly the squares of its row, which is what makes the picture a
picture of `Â` rather than a decoration. Left panel, then right. -/

#guard
  let I : Instance := ⟨4, #[]⟩
  let cellsOf (r : Nat) : List (Nat × Nat) :=
    (List.range 4).flatMap fun a => (List.range 4).filterMap fun b =>
      if (I.rowsOf (I.cellVar a b)).contains r then some (a, b) else none
  (cellsOf 1  == [(1,0), (1,1), (1,2), (1,3)])          -- the horizontal capsule
    && (cellsOf 6  == [(0,2), (1,2), (2,2), (3,2)])     -- the vertical capsule
    && (cellsOf 9  == [(0,1), (1,2), (2,3)])            -- the short diagonal capsule
    && (cellsOf 15 == [(0,3), (1,2), (2,1), (3,0)])     -- the long anti-diagonal capsule
    && (cellsOf 0  == [(0,0), (0,1), (0,2), (0,3)])
    && (cellsOf 4  == [(0,0), (1,0), (2,0), (3,0)])
    && (cellsOf 10 == [(0,0), (1,1), (2,2), (3,3)])

/-! The degrees the caption states: `4` at an interior square, `3` at each of the four corners, `1` at
a slack. These are the degrees of an *empty* board; a square carrying a given meets one row more, and
the guard below pins that case, which the paper's eq. (6) in §3.3 enumerates. -/

#guard
  let I : Instance := ⟨4, #[]⟩
  (I.rowsOf (I.cellVar 1 2)).size == 4
    && (I.rowsOf (I.cellVar 0 0)).size == 3
    && (I.rowsOf (I.cellVar 0 3)).size == 3
    && (I.rowsOf (I.cellVar 3 0)).size == 3
    && (I.rowsOf (I.cellVar 3 3)).size == 3
    && (I.rowsOf (I.slackVar 0)).size == 1

/-! **Degrees once there are givens**, which is what eq. (6) of §3.3 enumerates and what the empty
board above cannot exhibit. A square carrying a given lies in its given row too, so an interior given
has degree `5` and a corner given `4`; since `Problem.theta` stores `2θ = -deg`, the stored value `-5`
means `θ = -5/2`. All four degrees `{1,3,4,5}` occur on `Comp8`, whose givens include an interior
square and a corner. Pinned across the whole corpus, so that no instance can quietly acquire a degree
the paper does not list. -/

#guard
  let I := completion8                              -- ⟨8, #[(0,0), (1,4), (2,7)]⟩
  (I.rowsOf (I.cellVar 1 4)).size == 5              -- interior given
    && (I.rowsOf (I.cellVar 2 7)).size == 5          -- interior given, on an edge but not a corner
    && (I.rowsOf (I.cellVar 0 0)).size == 4          -- corner given: 3 + its given row
    && (I.rowsOf (I.cellVar 3 3)).size == 4          -- plain interior
    && (I.rowsOf (I.cellVar 7 7)).size == 3          -- plain corner
    && (I.rowsOf (I.slackVar 0)).size == 1
    && (problem I).theta.getD (I.cellVar 1 4) 0 == -5   -- 2θ = -deg, so θ = -5/2
    && (problem I).theta.getD (I.cellVar 0 0) 0 == -4
    && ((List.range (problem I).nvars).map fun u =>
          (problem I).theta.getD u 0).eraseDups.mergeSort (· ≤ ·) == [-5, -4, -3, -1]

#guard
  (corpus ++ blockedCorpus).all fun r =>
    ((List.range r.I.nvars).map fun u => (r.I.rowsOf u).size).all fun d =>
      d == 1 || d == 3 || d == 4 || d == 5

/-! The anti-diagonal through `(0,0)` really is the lone square, so the dotted ring is drawn on a set
that exists and a row that does not: no row of `Â` contains `(0,0)` and nothing else. -/

#guard
  let I : Instance := ⟨4, #[]⟩
  (I.rowsOf (I.cellVar 0 0)).all fun r =>
    ((List.range 4).flatMap fun a => (List.range 4).filterMap fun b =>
      if (I.rowsOf (I.cellVar a b)).contains r then some (a, b) else none).length > 1

/-! ## The additive index formulas of §3.3

The paper displays the membership test as an equation, with `e` running over the whole block of
`2(2N-3)` diagonal constraints. Checked here exactly as printed, at `N = 8`, together with the two
facts that make the two families the families they are named after: constant `i - j` on the first
`2N-3`, constant `i + j` on the rest, each with at least two squares. -/

#guard
  let N := 8
  let I : Instance := ⟨N, #[]⟩
  let D := I.ndiags
  (List.range N).all fun i => (List.range N).all fun j =>
    (List.range (2 * D)).all fun e =>
      I.onSlack i j e == (if e < D then i + N == e + 2 + j else i + j + D == e + 1)

#guard
  let N := 8
  let I : Instance := ⟨N, #[]⟩
  let D := I.ndiags
  let cellsOn (e : Nat) : List (Int × Nat) :=
    (List.range N).flatMap fun i => (List.range N).filterMap fun j =>
      if I.onSlack i j e then some ((i : Int) - j, i + j) else none
  ((List.range D).all fun e =>
      let cs := cellsOn e
      cs.length ≥ 2 && cs.all fun c => c.1 == (cs.getD 0 (0, 0)).1)      -- `i - j` constant
    && ((List.range D).all fun d =>
      let cs := cellsOn (D + d)
      cs.length ≥ 2 && cs.all fun c => c.2 == (cs.getD 0 (0, 0)).2)     -- `i + j` constant

/-! ## `fig:blocked` --- three blocked instances, and the two boards that refute one of them

**(a) `Attack`.** An `8 × 8` board with the two givens drawn, and the caption's reason: they share a
diagonal, which is why the dashed segment is drawn and why no enumeration is needed. -/

#guard
  drawn attacking 8 #[(0, 0), (1, 1)]
    && Baseline.count attacking == 0
    && attacks 0 0 1 1

/-! **(b) `Blk7`.** The givens are drawn with no attack indicator, and the caption says they share no
row, no column and no diagonal. Both halves of that are checked: the pair is legal, and the board is
dead anyway. -/

#guard
  drawn blocked7 7 #[(0, 0), (1, 6)]
    && Baseline.count blocked7 == 0
    && !(attacks 0 0 1 6)
    -- and the two givens really are on distinct rows, read off the instance rather than assumed
    && ((blocked7.givens.getD 0 (0, 0)).1 != (blocked7.givens.getD 1 (0, 0)).1)

/-! **(c) `Blk4`.** A single corner queen at `N = 4`. -/

#guard
  drawn blocked4 4 #[(0, 0)] && Baseline.count blocked4 == 0

/-! **(d) and (e).** The caption says these are *the only two* completions of the empty `4 × 4`
board, and that neither places a queen at `(0,0)` --- which is the whole argument for (c). Both
claims are checked, and the drawn placements themselves. -/

#guard
  let I : Instance := ⟨4, #[]⟩
  let sols := (List.range (4 ^ 4)).filterMap fun code =>
    let q := (List.range 4).map fun i => (code / 4 ^ i) % 4
    if I.isQueens q.toArray then some q else none
  sols == [[2, 0, 3, 1], [1, 3, 0, 2]]        -- exactly the two boards drawn, in the order drawn
    && sols.all (fun q => q.getD 0 4 != 0)    -- neither uses the corner
    && Baseline.count I == 2

/-! A corner queen is fatal at `N = 4` and `N = 6` and harmless from `N = 7`, as the caption of
`fig:blocked` and §4.5 both state, with the counts §4.5 prints. -/

#guard
  ((List.range 7).map fun k => Baseline.count ⟨k + 4, #[(0, 0)]⟩) == [0, 2, 0, 4, 4, 28, 64]

/-! `Blk8` is the seventh blocked instance, the one `tab:blocked` marks as *not* refuted by proof. It is
not drawn in `fig:blocked`, and the reason given is the number of open tuples. -/

#guard
  drawn blocked8 8 #[(0, 0), (1, 2)]
    && blocked8.size - blocked8.ngivens == 6      -- six rows left open, hence the 8^6 of `tab:blocked`
    && Baseline.count blocked8 == 0

/-! ## `fig:comp` --- two completable instances and their completions

**(a), (b) `Comp6`.** The instance drawn, its unique completion drawn beside it, and the caption's
claim that the completion is unique. -/

#guard
  drawn small6 6 #[(0, 1)]
    && small6.isQueens #[1, 3, 5, 0, 2, 4]
    && Baseline.count small6 == 1
    && Baseline.solve small6 == some #[1, 3, 5, 0, 2, 4]

/-! **(c), (d) `Comp8`.** The same, and the caption's extra claim: the board drawn in (d) is also the
lexicographically first of the `92` solutions of the empty `8 × 8` board, pinned by the three
givens. -/

#guard
  drawn completion8 8 #[(0, 0), (1, 4), (2, 7)]
    && completion8.isQueens #[0, 4, 7, 5, 2, 6, 1, 3]
    && Baseline.count completion8 == 1
    && Baseline.solve completion8 == some #[0, 4, 7, 5, 2, 6, 1, 3]
    && Baseline.solve (empty 8) == some #[0, 4, 7, 5, 2, 6, 1, 3]
    && Baseline.count (empty 8) == 92

/-! The given queens drawn dark in `fig:comp` sit on squares the completion occupies, which is why
overdrawing them does not change the board: every given agrees with the solution. -/

#guard
  (completion8.givens.all fun p => (#[0, 4, 7, 5, 2, 6, 1, 3] : Array Nat).getD p.1 8 == p.2)
    && (small6.givens.all fun p => (#[1, 3, 5, 0, 2, 4] : Array Nat).getD p.1 6 == p.2)

/-! ## The size formulas of §3.1

`n = N² + 4N - 6` and `m = 6N - 6 + |G|`, which the paper says are confirmed on every row of both
tables. Checked here on both corpora at once, rather than read off the printed tables. -/

#guard
  (corpus ++ blockedCorpus).all fun r =>
    r.I.nvars == r.I.size ^ 2 + 4 * r.I.size - 6
      && r.I.nrows == 6 * r.I.size - 6 + r.I.ngivens

/-! **Where those formulas stop.** §3.1 now says they presume `N ≥ 2`. They do: at `N = 1` the board
carries one variable and two constraints while `N² + 4N - 6` and `6N - 6` both truncate to `0` in `ℕ`.
At `N = 0` the two happen to agree, both being `0`. -/

#guard
  let I1 : Instance := ⟨1, #[]⟩
  let I0 : Instance := ⟨0, #[]⟩
  I1.nvars == 1 && I1.nrows == 2                          -- what the development gives
    && 1 ^ 2 + 4 * 1 - 6 == 0 && 6 * 1 - 6 == 0           -- what the formulas give: not equal
    && I0.nvars == 0 && I0.nrows == 0                     -- and they agree at N = 0
    && 0 ^ 2 + 4 * 0 - 6 == 0 && 6 * 0 - 6 == 0

/-! The corpus is the size the abstract claims: eleven completable boards, seven blocked. -/

#guard corpus.size == 11 && blockedCorpus.size == 7

/-! And every row of the completable corpus really is completable, every row of the blocked corpus
really not. This is the property that makes the two tables two tables. -/

#guard
  corpus.all (fun r => Baseline.count r.I > 0)
    && blockedCorpus.all (fun r => Baseline.count r.I == 0)

/-! ## The counterexample of §4.4

The paper states that the second half of its minimizer theorem does not reverse: a state whose board
decodes to a completion need not attain the minimum, because `decode` reads only the square variables
and not the slacks. The witness it gives is the encoded completion `(1,3,0,2)` of the empty `4 × 4`
board with one slack bit flipped. Pinned here, because a false claim in that sentence would make the
paper assert a theorem the development does not have --- and, as the flip shows, one that is false. -/

#guard
  let I : Instance := ⟨4, #[]⟩
  let q : Array Nat := #[1, 3, 0, 2]
  let x := I.encode q
  let x' := x.set! (I.slackVar 0) (!x.getD (I.slackVar 0) false)
  I.isQueens q                                   -- `q` is a completion
    && (problem I).penaltyDoubled x == 0         -- so its encoding is a minimizer
    && I.decode x' == q                          -- the flipped state decodes to the same board
    && I.isQueens (I.decode x')                  -- which is still a completion
    && (problem I).penaltyDoubled x' != 0        -- yet the flipped state is not a minimizer

/-! ## The parameter table of §5.2

Every number the paper prints for Algorithm 2. The swarm constants are `SearchConfig` defaults, which
`runOne` and `runOneD` do not override, so they are checked on the defaults; the annealing constants
come from `benchModel`. `runOne` overrides `N`, `M`, `maxOuter`, `oneHotInit` and `groups` only, and
`runOneD` additionally sets `divThreshold := 0.9`. -/

#guard
  let c : SearchConfig := {}
  c.c0 == 0.5 && c.c1 == 2.0 && c.c2 == 0.25 && c.Pm == 0.05
    && c.divThreshold == 0.4          -- the BMm value; DHNm overrides it to 0.9
    && c.mutatePbest == false         -- step 23 mutates the seeds, never the personal bests

#guard
  benchModel.innerIters == 40 && benchModel.levels == 64
    && benchModel.T0 == 3.0 && benchModel.eta == 0.9

end Figures
end Queens
end QUBO
