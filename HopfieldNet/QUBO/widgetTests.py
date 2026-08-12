#!/usr/bin/env python3
"""Regression tests for the infoview widget JavaScript.

    python3 HopfieldNet/QUBO/widgetTests.py

`quboPlayer.js` and `Instances/Queens/queensBoard.js` are loaded unbuilt by the Lean infoview and
are never seen by a compiler, so nothing in the Lean build catches a syntax error or a wrong
coordinate in them.  This script runs them under **JavaScriptCore**, which ships with macOS at
/System/Library/Frameworks/JavaScriptCore.framework/Versions/A/Helpers/jsc, so no npm, node or
network access is needed.

How it works.  Neither file can be imported directly: they are ES modules importing `react` and
`@leanprover/infoview`, and both declare `const h` at top level.  So each is stripped of its
imports, wrapped in a closure that re-exports the functions under test, and run against a stubbed
`React` whose `createElement` returns a plain `{type, props, children}` record.  A small `expand`
invokes function components the way React would, so `Board` and `Chequer` genuinely execute rather
than sitting unevaluated as element types -- which matters, because the bug that prompted these
tests was `kind = "board"` falling through to the Sudoku renderer.

What is *not* covered: the RPC wire.  `rs.call` is stubbed, so the browser half of
`#queensBoard` is exercised here and the Lean half is exercised by `#eval`ing
`QUBO.Queens.Interactive.runSolve`, but the `$/lean/rpc/call` round trip between them is only
tested by opening the file in an editor and clicking.
"""

import pathlib
import re
import subprocess
import sys

HERE = pathlib.Path(__file__).resolve().parent
JSC = ('/System/Library/Frameworks/JavaScriptCore.framework/Versions/A/'
       'Helpers/jsc')
PLAYER = HERE / 'quboPlayer.js'
BOARD = HERE / 'Instances' / 'Queens' / 'queensBoard.js'


def wrap(path, var, entry, exports):
    """Strip ES module syntax and wrap in a closure re-exporting `exports`."""
    src = pathlib.Path(path).read_text()
    src = re.sub(r'^import .*$', '', src, flags=re.M)
    src, n = re.subn(r'export default function \(props\) \{',
                     f'var {entry} = function (props) {{', src)
    if n != 1:
        raise SystemExit(f'{path}: expected one default export, found {n}')
    fields = ', '.join(f'{e}: {e}' for e in exports)
    return f'var {var} = (function () {{\n{src}\nreturn {{ {fields} }};\n}})();\n'


STUBS = r'''
function el(type, props) {
  var kids = Array.prototype.slice.call(arguments, 2), flat = [];
  (function push(x) {
    if (x === null || x === undefined || x === false) return;
    if (Array.isArray(x)) x.forEach(push); else flat.push(x);
  })(kids);
  return { type: type, props: props || {}, children: flat };
}
var React = {
  createElement: el,
  useState: function (init) { return [init, function () {}]; },
  useMemo: function (f) { return f(); },
  useEffect: function () {},
  useContext: function () {
    return { call: function () {
      return { then: function () { return { catch: function () {} }; } }; } };
  },
};
var RpcContext = {};
function mapRpcError() { return { message: 'stub' }; }

var PASS = 0, FAIL = 0;
function ok(name, cond, extra) {
  if (cond) { PASS++; return; }
  FAIL++;
  print('  FAIL  ' + name + (extra !== undefined ? '   ' + extra : ''));
}
function eq(name, got, want) {
  var a = JSON.stringify(got), b = JSON.stringify(want);
  ok(name, a === b, 'got ' + a + ' want ' + b);
}
/** Every descendant of the given tag name. */
function collect(node, type, out) {
  out = out || [];
  if (!node || typeof node !== 'object') return out;
  if (node.type === type) out.push(node);
  (node.children || []).forEach(function (c) { collect(c, type, out); });
  return out;
}
/** Invoke function components, as React would, so Board and Chequer run. */
function expand(node) {
  if (!node || typeof node !== 'object') return node;
  var n = node, guard = 0;
  while (n && typeof n.type === 'function' && guard++ < 20) {
    var props = n.props || {};
    if (n.children && n.children.length) {
      props = Object.assign({}, props, { children: n.children });
    }
    n = n.type(props);
  }
  if (!n || typeof n !== 'object') return n;
  return { type: n.type, props: n.props || {}, children: (n.children || []).map(expand) };
}
/** All text content, for checking captions. */
function texts(node) {
  var acc = [];
  (function walk(x) {
    if (typeof x === 'string') { acc.push(x); return; }
    if (!x || typeof x !== 'object') return;
    (x.children || []).forEach(walk);
  })(node);
  return acc.join(' ');
}
'''

TESTS = r'''
print('--- decoding a frame string ---');
eq('the 6-queens solution', frameCols('135024', 6), [1, 3, 5, 0, 2, 4]);
eq('the 8-queens solution', frameCols('04752613', 8), [0, 4, 7, 5, 2, 6, 1, 3]);
eq('a dot is an empty row', frameCols('.1.', 3), [null, 1, null]);
eq('columns are base 36', frameCols('a', 11)[0], 10);
eq('an out-of-range column is dropped', frameCols('5', 3), [null, null, null]);
eq('a short frame is padded', frameCols('1', 3), [1, null, null]);

print('--- the three pairwise clauses of isQueens ---');
eq('a solution has no attacks', attacks([0, 4, 7, 5, 2, 6, 1, 3], 8), []);
eq('and so does the 6x6 one', attacks([1, 3, 5, 0, 2, 4], 6), []);
eq('shared column', attacks([2, 2], 2), [[0, 1]]);
eq('shared diagonal, adjacent', attacks([0, 1], 2), [[0, 1]]);
eq('shared anti-diagonal, adjacent', attacks([1, 0], 2), [[0, 1]]);
eq('shared diagonal, distance 3', attacks([0, null, null, 3], 4), [[0, 3]]);
eq('shared anti-diagonal, distance 3', attacks([3, null, null, 0], 4), [[0, 3]]);
eq('empty rows are skipped', attacks([0, null, 1], 3), []);
eq('each pair reported once, i < k', attacks([0, 0, 0], 3), [[0, 1], [0, 2], [1, 2]]);
// Regression: the guard was `=== null`, so a short array made `undefined === undefined`
// true and reported every pair of missing rows as attacking.
eq('blocked7 givens do not attack', attacks([0, 6], 7), []);
eq('a missing tail is not a row of queens', attacks([0], 5), []);

print('--- the queen piece ---');
var piece = QueenPiece('p0', 0, 0, 40, true);
ok('is a group', piece.type === 'g');
eq('crown, collar, body, plinth and five balls', piece.children.length, 9);
eq('the crown is a polygon', piece.children[0].type, 'polygon');
eq('the body is a path', piece.children[2].type, 'path');
eq('five crown balls', collect(piece, 'circle').length, 5);
ok('a given queen is black', piece.children[0].props.fill === '#26221e');
ok('a placed queen is white',
   QueenPiece('x', 0, 0, 40, false).children[0].props.fill === '#fbfaf7');
ok('the piece does not swallow clicks', piece.props.pointerEvents === 'none');
ok('no NaN in the coordinates', JSON.stringify(piece).indexOf('NaN') < 0);

print('--- the interactive board ---');
var givenOf = new Map(); givenOf.set(0, 0);
var b = Board({ n: 8, cols: [0, 4, 7, 5, 2, 6, 1, 3], givenOf: givenOf,
                onCell: function () {}, interactive: true });
ok('is an svg', b.type === 'svg');
eq('64 squares, a border, 8 pieces of 2 rects, 64 click targets',
   collect(b, 'rect').length, 64 + 1 + 16 + 64);
eq('eight pieces', collect(b, 'g').length, 8);
eq('a solution draws no attack lines', collect(b, 'line').length, 0);
eq('the given queen is black', collect(b, 'g')[0].children[0].props.fill, '#26221e');
eq('the rest are white', collect(b, 'g')[1].children[0].props.fill, '#fbfaf7');
var b2 = Board({ n: 2, cols: [0, 1], givenOf: new Map(),
                 onCell: function () {}, interactive: false });
eq('a static board has no click targets', collect(b2, 'rect').length, 4 + 1 + 2 + 4);
eq('one attack line', collect(b2, 'line').length, 1);
eq('a wash under each attacked queen',
   collect(b2, 'rect').filter(function (r) { return r.props.fill === '#c0392b'; }).length, 2);
var b3 = Board({ n: 4, cols: [0, null, null, null], givenOf: new Map(),
                 onCell: function () {}, interactive: false });
eq('empty rows draw no piece', collect(b3, 'g').length, 1);
ok('no NaN', JSON.stringify(b3).indexOf('NaN') < 0);

print('--- the interactive widget, rendered ---');
var app = expand(App({ size: 8, givens: [[0, 0], [1, 4]] }));
ok('renders', app.type === 'div');
var caption = texts(app);
ok('the caption gives the board size', caption.indexOf('8×8') >= 0, caption.slice(0, 120));
ok('and the number of givens', caption.indexOf('2 given') >= 0);
ok('and how many queens are placed', caption.indexOf('2/8 queens') >= 0);
ok('the seed control shows the bench seed', caption.indexOf('20260806') >= 0);
ok('the solver and edit buttons are present', collect(app, 'button').length >= 6,
   collect(app, 'button').length);
ok('one board is drawn', collect(app, 'svg').length === 1);
eq('with the two given queens on it', collect(app, 'g').length, 2);
ok('a 1x1 board renders', expand(App({ size: 1, givens: [] })).type === 'div');
ok('a 12x12 board renders', expand(App({ size: 12, givens: [] })).type === 'div');
ok('an off-board given does not crash', expand(App({ size: 4, givens: [[9, 9]] })).type === 'div');

print('--- the player, which the gallery uses ---');
eq('queenCols agrees with frameCols', queenCols('135024', 6), [1, 3, 5, 0, 2, 4]);
eq('no attacks in a solution', boardAttacks('04752613', 8), []);
eq('a shared diagonal is found', boardAttacks('01', 2), [[0, 1]]);
eq('an empty row counts as a conflict', Array.from(boardConflicts('0.', 2)).sort(), [1]);
var ch = Chequer({ frame: '04752613', nverts: 8, givens: [[0, 0]] });
ok('is an svg', ch.type === 'svg');
eq('64 squares, a border and 8 pieces of 2 rects', collect(ch, 'rect').length, 64 + 1 + 16);
eq('eight pieces', collect(ch, 'g').length, 8);
eq('rank and file labels', collect(ch, 'text').length, 16);
ok('the squares use the chessboard palette',
   collect(ch, 'rect')[0].props.fill === '#f0d9b5'
     || collect(ch, 'rect')[0].props.fill === '#b58863');
ok('no NaN', JSON.stringify(ch).indexOf('NaN') < 0);

// Regression: `kind = "board"` must reach Chequer.  Before the widget module was rebuilt it
// fell through this dispatch chain to the Sudoku renderer, and the board came out as a grid.
var props = { title: 't', kind: 'board', frames: ['04752613', '04752613'], givens: '',
              phase: [1, 1], pen: [3, 0], outer: [0, 1], solved: true, note: 'n',
              nverts: 8, edges: [[0, 0]], ncolours: 8, mrows: 0, mcols: 0, cells: [] };
var pl = expand(Player(props));
ok('the player renders', pl.type === 'div');
var pcap = texts(pl);
ok('the caption counts queens, not filled cells',
   pcap.indexOf('/8 queens') >= 0 && pcap.indexOf('/81 filled') < 0, pcap.slice(0, 160));
eq('a chessboard, not a Sudoku grid', collect(pl, 'g').length, 8);
var clash = JSON.parse(JSON.stringify(props));
clash.frames = ['01234567', '01234567'];
ok('a clashing frame reports rows in conflict',
   texts(expand(Player(clash))).indexOf('rows in conflict') >= 0);

print('');
print(PASS + ' passed, ' + FAIL + ' failed');
if (FAIL > 0) throw new Error(FAIL + ' failures');
'''


def main():
    if not pathlib.Path(JSC).exists():
        raise SystemExit('JavaScriptCore not found; these tests need macOS jsc')
    harness = (
        STUBS
        + wrap(BOARD, 'QB', 'App', ['frameCols', 'attacks', 'QueenPiece', 'Board', 'App'])
        + wrap(PLAYER, 'PL', 'Player',
               ['queenCols', 'boardAttacks', 'boardConflicts', 'Chequer', 'Player'])
        + 'var frameCols = QB.frameCols, attacks = QB.attacks, QueenPiece = QB.QueenPiece,'
          '    Board = QB.Board, App = QB.App;\n'
        + 'var queenCols = PL.queenCols, boardAttacks = PL.boardAttacks,'
          '    boardConflicts = PL.boardConflicts, Chequer = PL.Chequer, Player = PL.Player;\n'
        + TESTS
    )
    out = HERE / '.widgetTests.generated.js'
    out.write_text(harness)
    try:
        r = subprocess.run([JSC, str(out)], capture_output=True, text=True)
        sys.stdout.write(r.stdout)
        if r.stderr.strip():
            sys.stderr.write(r.stderr)
        return r.returncode
    finally:
        out.unlink(missing_ok=True)


if __name__ == '__main__':
    sys.exit(main())
