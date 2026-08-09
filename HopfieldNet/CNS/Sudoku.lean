/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Sudoku: cells, units, and the binary variable indexing of Li & Wang

This module fixes the combinatorial vocabulary shared by the whole `CNS` development. It is
deliberately **Mathlib-free**: everything here is executable Lean core, so the data and
execution layers rebuild in seconds.

The variable indexing follows the paper exactly. Li & Wang vectorise the decision tensor as

  `x̄ = vec(X^{T₂}) = [x₁₁₁, x₁₁₂, …, x₉₉₉] ∈ {0,1}^{n³}`

and Algorithm 1 addresses it as `s_{i×n²+j×n+k}`. With `n = 9` and zero-based `i j k` that is
`varIdx i j k = 81*i + 9*j + k`, which is what `varIdx` below implements.

Reference: H. Li and J. Wang, "Collaborative Neurodynamic Algorithms for Solving Sudoku
Puzzles", ICIST 2022, pp. 8-17.
-/

namespace CNS

/-- Side length of the puzzle. The paper's `n`; `n = 9` throughout. -/
def n : Nat := 9

/-- Side length of a block, the paper's `√n`. -/
def blk : Nat := 3

/-- Number of cells, `n²`. -/
def numCells : Nat := n * n

/-- Number of binary decision variables, `n³`. -/
def numVars : Nat := n * n * n

/-- Number of penalty rows: one per constraint in each of the four families of (11a)-(11d),
so `4n²`. -/
def numRows : Nat := 4 * n * n

/-- Linear index of the binary variable `x_{ijk}` (zero-based `i`, `j`, `k`).

This is the paper's `i×n² + j×n + k`. -/
@[inline] def varIdx (i j k : Nat) : Nat := i * (n * n) + j * n + k

/-- Linear index of the cell in row `i`, column `j`. -/
@[inline] def cellIdx (i j : Nat) : Nat := i * n + j

/-- Row of a cell index. -/
@[inline] def rowOf (c : Nat) : Nat := c / n

/-- Column of a cell index. -/
@[inline] def colOf (c : Nat) : Nat := c % n

/-- Block index (0-8, row-major over blocks) of a cell index. -/
@[inline] def boxOf (c : Nat) : Nat := (rowOf c / blk) * blk + (colOf c / blk)

/-- The `n` cell indices of row `r`. -/
def rowCells (r : Nat) : Array Nat := (Array.range n).map (fun c => cellIdx r c)

/-- The `n` cell indices of column `c`. -/
def colCells (c : Nat) : Array Nat := (Array.range n).map (fun r => cellIdx r c)

/-- The `n` cell indices of block `b`. -/
def boxCells (b : Nat) : Array Nat :=
  let br := (b / blk) * blk
  let bc := (b % blk) * blk
  (Array.range n).map (fun t => cellIdx (br + t / blk) (bc + t % blk))

/-- All `3n` units (rows, then columns, then blocks). These are exactly the constraint
families (10b), (10c), (10d). -/
def units : Array (Array Nat) :=
  (Array.range n).map rowCells ++ (Array.range n).map colCells ++ (Array.range n).map boxCells

/-- The cells sharing a row, column, or block with `c`, excluding `c` itself.

Defined as a filter over all cells rather than by unioning the three units: it is the same set,
it is automatically duplicate-free, and `Array.mem_filter` characterises it in one step, which
`CNS.ReduceSound` needs. The three-unit union costs `O(3n)` against `O(n²)` here, but `peers`
is not on the hot path -- the search never calls it. -/
def peers (c : Nat) : Array Nat :=
  (Array.range numCells).filter fun p =>
    p != c && (rowOf p == rowOf c || colOf p == colOf c || boxOf p == boxOf c)

/-- A Sudoku grid: `numCells` entries, `none` for an empty cell and `some k` for the digit
`k+1` (so stored digits are zero-based, matching `varIdx`). -/
structure Grid where
  /-- The `n²` cells in row-major order. -/
  cells : Array (Option Nat)
  deriving Repr, Inhabited, BEq

namespace Grid

/-- Read a grid from an 81-character string: `'1'`-`'9'` are givens, any other character
(conventionally `'.'` or `'0'`) is an empty cell. Returns `none` on a length mismatch. -/
def ofString (s : String) : Option Grid :=
  let cs := s.toList
  if cs.length != numCells then none
  else some ⟨(cs.map fun ch =>
    if '1' ≤ ch && ch ≤ '9' then some (ch.toNat - '1'.toNat) else none).toArray⟩

/-- Render a grid as an 81-character string, `'.'` for empty cells. -/
def toString (g : Grid) : String :=
  g.cells.foldl (fun acc o =>
    acc.push (match o with
      | some k => Char.ofNat (k + '1'.toNat)
      | none   => '.')) ""

instance : ToString Grid := ⟨toString⟩

/-- The digit at cell `c`, if assigned. -/
@[inline] def get (g : Grid) (c : Nat) : Option Nat := g.cells.getD c none

/-- Number of given (non-empty) cells. -/
def numGivens (g : Grid) : Nat := g.cells.foldl (fun acc o => if o.isSome then acc + 1 else acc) 0

/-- Every cell is assigned. -/
def isComplete (g : Grid) : Bool := g.cells.all Option.isSome

/-- Every unit contains every digit **exactly once**.

This is constraints (10b), (10c) and (10d) verbatim -- the paper writes `Σ = 1`, not `Σ ≤ 1`.
On a complete grid with in-range digits the two are equivalent by pigeonhole, but stating the
equality directly is both closer to the paper and what lets `CNS.ReduceSound` conclude that a
digit missing from a unit *must* go in one of that unit's remaining cells. -/
def isConsistent (g : Grid) : Bool :=
  units.all fun u =>
    (Array.range n).all fun k =>
      (u.toList.foldl (fun acc c => if g.get c == some k then acc + 1 else acc) 0) == 1

/-- The grid has the right number of cells.

Needed explicitly: `isComplete` and `isConsistent` are both `all`-quantified and so are
*vacuously true* on a short array. Without this, the empty grid passes `isSolution`. -/
def hasSize (g : Grid) : Bool := g.cells.size == numCells

/-- Every assigned digit is a legal digit `0 ≤ k < n`.

Also needed explicitly: `isConsistent` counts occurrences of `0 … n-1` only, so a grid whose
every cell holds `42` has all nine counts equal to zero and passes it. -/
def digitsInRange (g : Grid) : Bool :=
  g.cells.all fun o => match o with | some k => decide (k < n) | none => true

/-- A complete, consistent grid: every row, column, and block is a permutation of `1..n`.
This is the specification the paper's constraints (10a)-(10d) encode.

All four conjuncts are load-bearing. Dropping `hasSize` admits the empty grid; dropping
`digitsInRange` admits a grid of `42`s. Both were verified to slip through an earlier version
of this definition. -/
def isSolution (g : Grid) : Bool :=
  g.hasSize && g.digitsInRange && g.isComplete && g.isConsistent

/-- `g'` extends `g`: every given of `g` is preserved. Together with `isSolution g'` this is
the paper's constraint (10e). -/
def extends' (g g' : Grid) : Bool :=
  (Array.range numCells).all fun c =>
    match g.get c with
    | none   => true
    | some k => g'.get c == some k

/-- Pretty-print as a 9x9 board. -/
def pretty (g : Grid) : String :=
  String.intercalate "\n" <|
    (List.range n).map fun i =>
      String.intercalate " " <|
        (List.range n).map fun j =>
          match g.get (cellIdx i j) with
          | some k => Nat.repr (k + 1)
          | none   => "."

end Grid
end CNS
