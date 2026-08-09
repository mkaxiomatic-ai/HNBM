/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.CNS.Sudoku

/-!
# The ten benchmark instances

Li & Wang evaluate on ten puzzles taken from

  I. Sabuncu, "Work-In-Progress: Solving Sudoku Puzzles Using Hybrid Ant Colony Optimization
  Algorithm", INISCom 2015, pp. 181-184 (open access, DOI 10.4108/icst.iniscom.2015.258984),

which they label Sabuncu1-Sabuncu10. The grids are *not* printed in the ICIST paper: Table I
reports only post-reduction dimensions, and Figs 4-8 show boards for just five of the ten.
The givens below are taken from the Sabuncu appendix; solutions are computed.

`paperTable1` records Li & Wang's Table I (number of binary variables remaining after
Algorithm 1). `HopfieldNet.CNS.Reduce` is expected to reproduce it exactly.

Note: Sabuncu3 is not a proper Sudoku -- it admits 27 distinct solutions. Every other
instance has a unique solution.
-/

namespace CNS
namespace Instances

/-- A benchmark entry: the puzzle, a known solution, and Li & Wang's Table I figure. -/
structure Entry where
  /-- Instance name as used by Li & Wang. -/
  name : String
  /-- The 81-character givens string, `'.'` for an empty cell. -/
  givens : String
  /-- A known complete solution (Sabuncu3 has 27; this is one of them). -/
  solution : String
  /-- Number of variables remaining after Algorithm 1, as printed in Table I. -/
  table1 : Nat
  deriving Repr, Inhabited

/-- The ten Sabuncu instances used by Li & Wang. -/
def all : Array Entry := #[
  { name := "Sabuncu1"
    givens := "1276..48584.1.5..7.9574.3.2269...5.....85.64..5..7.2.1314....2...6237.......6.85."
    solution := "127693485843125967695748312269314578731852649458976231314589726586237194972461853"
    table1 := 0 },
  { name := "Sabuncu2"
    givens := "75.98....6...5...8......42....395....23....81...8...5...4...3......79.....8....12"
    solution := "752984136641253798389761425816395247523647981497812653164528379235179864978436512"
    table1 := 0 },
  { name := "Sabuncu3"
    givens := "842.........5.17........38.95......2....5.......9...461....74....8.6......4....38"
    solution := "842379651396581724715624389953746812461258973287913546129837465538462197674195238"
    table1 := 171 },
  { name := "Sabuncu4"
    givens := "5.96......3.8.792....3..8......16.8..5.....1........321.4.3......67.9...........3"
    solution := "589624371431857926267391845743216589652983714918475632194538267326749158875162493"
    table1 := 95 },
  { name := "Sabuncu5"
    givens := "..4.86...9.347.1...825...67.9.8..3.2.5.....4.2.6..1.5.34...927...5.348.6...71.5.."
    solution := "574186923963472185182593467497865312851327649236941758348659271715234896629718534"
    table1 := 0 },
  { name := "Sabuncu6"
    givens := "..53.....8......2..7..1.5..4....53...1..7...6..32...8..6.5....9..4....3......97.."
    solution := "145327698839654127672918543496185372218473956753296481367542819984761235521839764"
    table1 := 209 },
  { name := "Sabuncu7"
    givens := "....68....2.7..5......4..2.8..4....33...89.7.461.......76...9..........8.....16.."
    solution := "745268391928713564613945827897426153352189476461537289176854932534692718289371645"
    table1 := 168 },
  { name := "Sabuncu8"
    givens := "2...937..5.8.......67.......9...4.25......9.7....8.........54.....3.1.5..7.8...6."
    solution := "214593786538627194967418532796134825381256947452789613823965471649371258175842369"
    table1 := 0 },
  { name := "Sabuncu9"
    givens := "6...4..1..1......3..2..8.4..2......4..73826..5......2..9.5..1..4......7..5..9...2"
    solution := "635249817814756293972138546326915784147382659589467321293574168461823975758691432"
    table1 := 163 },
  { name := "Sabuncu10"
    givens := ".3..462..8..31.74..2...8...41....6......71852582.3..743.15.492...5.67.3..4829.5.7"
    solution := "139746285856312749724958361417825693963471852582639174371584926295167438648293517"
    table1 := 0 }
]

/-- The five instances Li & Wang report in Table II (those that Algorithm 1 does not
already solve outright). -/
def tableII : Array Entry := all.filter (fun e => e.table1 != 0)

/-- Look up an instance by name. -/
def find? (nm : String) : Option Entry := all.find? (fun e => e.name == nm)

end Instances
end CNS
