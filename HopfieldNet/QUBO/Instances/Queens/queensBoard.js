/* Interactive n-Queens Completion board.

Unlike `quboPlayer.js`, which replays frames computed during elaboration, this component is
*live*: you click squares to build a partial placement, press a solver, and the Lean language
server runs the real thing and hands back the frames. The call goes through the core
`@[server_rpc_method]` mechanism (`$/lean/rpc/call`), so the function that runs is
`QUBO.Queens.Interactive.queensSolve` in this repository — the same `QUBO.search`,
`QUBO.Queens.anneal` and `QUBO.Queens.Baseline.solve` the theorems are about, not a
reimplementation.

Three consequences worth knowing while reading the code:

  - the file must be open in the editor for the RPC to resolve, so this is a development-time
    artifact, not a web page;
  - RPC bodies run in the Lean interpreter, so a solve takes about as long as the corresponding
    `#eval`. The button is disabled while a call is in flight rather than pretending otherwise;
  - the board you draw is a *partial placement*, i.e. the `givens` of a `Queens.Instance`. One
    queen per row is enforced on click, because that is what the encoding's row constraints say.

A frame is the same encoding the other renderers use: one character per board row, '.' where that
row holds no queen, otherwise the queen's column in base 36.
*/

import * as React from 'react'
import { RpcContext, mapRpcError } from '@leanprover/infoview'

const h = React.createElement
/* Board palette. Fixed rather than theme-derived: a chessboard is a recognisable object, and these
   two mid-tones read correctly against both the light and the dark infoview. */
const SQ_LIGHT = '#f0d9b5'
const SQ_DARK = '#b58863'
const SQ_EDGE = '#8a6242'
const ATTACK = '#c0392b'

/** A chess queen drawn from primitives in a 0..1 box, so it scales to any square size.
    Deliberately not the '♛' glyph: that needs a font the infoview may not have, and when the font
    is missing nothing is drawn at all. `dark` selects a black or a white piece. */
function QueenPiece(key, x0, y0, C, dark) {
  const P = (u, v) => [x0 + u * C, y0 + v * C]
  const pt = (u, v) => P(u, v).join(',')
  const body = dark ? '#26221e' : '#fbfaf7'
  const edge = dark ? '#0d0b0a' : '#4a423a'
  const sw = Math.max(0.7, C * 0.045)
  const crown = [
    [0.14, 0.255], [0.265, 0.45], [0.32, 0.185], [0.41, 0.45],
    [0.50, 0.155], [0.59, 0.45], [0.68, 0.185], [0.735, 0.45], [0.86, 0.255],
    [0.80, 0.555], [0.20, 0.555],
  ].map(([u, v]) => pt(u, v)).join(' ')
  const els = [
    h('polygon', { key: key + 'c', points: crown, fill: body, stroke: edge, strokeWidth: sw,
      strokeLinejoin: 'round' }),
    h('rect', { key: key + 'k', x: P(0.175, 0)[0], y: P(0, 0.555)[1],
      width: C * 0.65, height: C * 0.085, rx: C * 0.03,
      fill: body, stroke: edge, strokeWidth: sw }),
    h('path', {
      key: key + 'b',
      d: `M ${pt(0.255, 0.64)} C ${pt(0.255, 0.78)} ${pt(0.205, 0.83)} ${pt(0.165, 0.875)}`
        + ` L ${pt(0.835, 0.875)} C ${pt(0.795, 0.83)} ${pt(0.745, 0.78)} ${pt(0.745, 0.64)} Z`,
      fill: body, stroke: edge, strokeWidth: sw, strokeLinejoin: 'round',
    }),
    h('rect', { key: key + 'p', x: P(0.125, 0)[0], y: P(0, 0.875)[1],
      width: C * 0.75, height: C * 0.075, rx: C * 0.028,
      fill: body, stroke: edge, strokeWidth: sw }),
  ]
  ;[[0.14, 0.235], [0.32, 0.165], [0.50, 0.135], [0.68, 0.165], [0.86, 0.235]]
    .forEach(([u, v], i) => els.push(h('circle', {
      key: key + 'q' + i, cx: P(u, v)[0], cy: P(u, v)[1], r: C * 0.072,
      fill: body, stroke: edge, strokeWidth: sw,
    })))
  return h('g', { key: key, pointerEvents: 'none' }, els)
}

/* ------------------------------------------------------------------ geometry */

/** Column of the queen in each board row of a frame string, or null. */
function frameCols(frame, n) {
  const out = []
  for (let i = 0; i < n; i++) {
    const ch = frame[i]
    if (ch === undefined || ch === '.') { out.push(null); continue }
    const c = parseInt(ch, 36)
    out.push(Number.isNaN(c) || c >= n ? null : c)
  }
  return out
}

/** Attacking pairs [i,k], i<k, among a column-per-row array. */
function attacks(cols, n) {
  const pairs = []
  for (let i = 0; i < n; i++) {
    for (let k = i + 1; k < n; k++) {
      const a = cols[i], b = cols[k]
      if (a === null || b === null) continue
      if (a === b || i - a === k - b || i + a === k + b) pairs.push([i, k])
    }
  }
  return pairs
}

/* -------------------------------------------------------------------- board */

function Board({ n, cols, givenOf, onCell, interactive }) {
  const C = Math.max(16, Math.min(40, Math.floor(320 / n)))
  const S = C * n
  const pairs = attacks(cols, n)
  const bad = new Set()
  for (const [i, k] of pairs) { bad.add(i); bad.add(k) }
  const els = []

  for (let i = 0; i < n; i++) {
    for (let j = 0; j < n; j++) {
      els.push(h('rect', {
        key: 's' + i + '_' + j, x: j * C, y: i * C, width: C, height: C,
        fill: (i + j) % 2 === 0 ? SQ_LIGHT : SQ_DARK,
      }))
    }
  }
  // wash under attacked queens
  for (const i of bad) {
    if (cols[i] === null) continue
    els.push(h('rect', {
      key: 'w' + i, x: cols[i] * C, y: i * C, width: C, height: C,
      fill: ATTACK, opacity: 0.28,
    }))
  }
  // attack lines
  pairs.forEach(([i, k], e) => els.push(h('line', {
    key: 'a' + e,
    x1: cols[i] * C + C / 2, y1: i * C + C / 2,
    x2: cols[k] * C + C / 2, y2: k * C + C / 2,
    stroke: ATTACK, strokeWidth: Math.max(1.5, C * 0.07), strokeDasharray: '5 3',
    opacity: 0.95,
  })))
  els.push(h('rect', {
    key: 'bd', x: 0, y: 0, width: S, height: S,
    fill: 'none', stroke: SQ_EDGE, strokeWidth: 2,
  }))
  // pieces: a given queen is black, one you or the solver placed is white
  for (let i = 0; i < n; i++) {
    const c = cols[i]
    if (c === null) continue
    els.push(QueenPiece('p' + i, c * C, i * C, C, givenOf.get(i) === c))
  }
  // click targets last, so they sit on top
  if (interactive) {
    for (let i = 0; i < n; i++) {
      for (let j = 0; j < n; j++) {
        els.push(h('rect', {
          key: 'c' + i + '_' + j, x: j * C, y: i * C, width: C, height: C,
          fill: 'transparent', style: { cursor: 'pointer' },
          onClick: () => onCell(i, j),
        }))
      }
    }
  }
  return h('svg', {
    width: S + 2, height: S + 2, viewBox: `-1 -1 ${S + 2} ${S + 2}`,
    style: { display: 'block' },
  }, els)
}

/* ------------------------------------------------------------------ the app */

export default function (props) {
  const rs = React.useContext(RpcContext)

  const [n, setN] = React.useState(props.size || 8)
  const [givens, setGivens] = React.useState(props.givens || [])
  const [frames, setFrames] = React.useState([])
  const [pens, setPens] = React.useState([])
  const [idx, setIdx] = React.useState(0)
  const [playing, setPlaying] = React.useState(false)
  const [busy, setBusy] = React.useState(false)
  const [status, setStatus] = React.useState('Click squares to place queens, then pick a solver.')
  const [solved, setSolved] = React.useState(false)
  const [count, setCount] = React.useState(-1)
  /* The bench's base seed, so what you see here lines up with the paper's table. The control is
     exposed rather than hidden because the solvers are stochastic and their failures are part of
     what this widget is for: `swarm` succeeds on ~6/10 seeds on the 3-given 8x8, and a single
     `anneal` succeeds on 0/20 seeds on the empty 8x8. A fixed lucky seed would misrepresent that. */
  const [seed, setSeed] = React.useState(20260806)

  const givenOf = React.useMemo(() => {
    const m = new Map()
    for (const [r, c] of givens) m.set(r, c)
    return m
  }, [givens])

  // what is on the board right now: a run's frame if we have one, else just the givens
  const cols = React.useMemo(() => {
    if (frames.length > 0) return frameCols(frames[Math.min(idx, frames.length - 1)], n)
    const out = []
    for (let i = 0; i < n; i++) out.push(givenOf.has(i) ? givenOf.get(i) : null)
    return out
  }, [frames, idx, n, givenOf])

  // playback
  React.useEffect(() => {
    if (!playing || frames.length === 0) return
    if (idx + 1 >= frames.length) { setPlaying(false); return }
    const t = setTimeout(() => setIdx(idx + 1), 90)
    return () => clearTimeout(t)
  }, [playing, idx, frames])

  const editMode = frames.length === 0

  function onCell(i, j) {
    // any edit drops the run and returns to editing
    setFrames([]); setPens([]); setIdx(0); setPlaying(false); setSolved(false); setCount(-1)
    const cur = givenOf.get(i)
    if (cur === j) setGivens(givens.filter(([r]) => r !== i))
    else setGivens(givens.filter(([r]) => r !== i).concat([[i, j]]))
    setStatus('Edited. Pick a solver.')
  }

  function resize(d) {
    const m = Math.max(1, Math.min(12, n + d))
    setN(m)
    setGivens(givens.filter(([r, c]) => r < m && c < m))
    setFrames([]); setPens([]); setIdx(0); setPlaying(false); setSolved(false); setCount(-1)
    setStatus(`Board is now ${m}×${m}.`)
  }

  function clear() {
    setGivens([]); setFrames([]); setPens([]); setIdx(0)
    setPlaying(false); setSolved(false); setCount(-1)
    setStatus('Cleared.')
  }

  function run(mode) {
    setBusy(true); setPlaying(false); setIdx(0)
    setStatus(mode === 'backtrack' ? 'Backtracking…' : 'Running in Lean…')
    rs.call('queensSolve', { size: n, givens, mode, seed })
      .then((r) => {
        setBusy(false)
        setFrames(r.frames || [])
        setPens(r.pens || [])
        setSolved(!!r.solved)
        setCount(typeof r.count === 'number' ? r.count : -1)
        setStatus(r.note || '')
        if ((r.frames || []).length > 1) setPlaying(true)
      })
      .catch((e) => { setBusy(false); setStatus(mapRpcError(e).message) })
  }

  const nQueens = cols.filter((c) => c !== null).length
  const nAtt = attacks(cols, n).length
  const pen = pens.length > 0 ? pens[Math.min(idx, pens.length - 1)] : null

  const caption = [
    `${n}×${n}`,
    `${givens.length} given`,
    `${nQueens}/${n} queens`,
    nAtt > 0 ? `${nAtt} attacking pair${nAtt === 1 ? '' : 's'}` : null,
    pen !== null ? `‖Ax−b‖² = ${pen}` : null,
    frames.length > 1 ? `frame ${Math.min(idx, frames.length - 1) + 1}/${frames.length}` : null,
    count >= 0 ? `${count} completion${count === 1 ? '' : 's'}` : null,
  ].filter(Boolean).join(' · ')

  const btn = (label, onClick, disabled, title) =>
    h('button', { key: label, onClick, disabled: disabled || busy, title }, label)

  return h('div', { className: 'cns-widget' },
    h('p', { className: 'cns-title' }, 'n-Queens Completion — live'),
    h('p', { className: 'cns-caption' }, caption),
    h(Board, { n, cols, givenOf, onCell, interactive: editMode }),
    h('div', { className: 'cns-row' },
      btn('−', () => resize(-1), n <= 1, 'smaller board'),
      btn('+', () => resize(1), n >= 12, 'larger board'),
      btn('clear', clear, false, 'remove all queens'),
    ),
    h('div', { className: 'cns-row' },
      btn('anneal', () => run('anneal'), false,
        'one annealed Boltzmann machine, eq. (6), one frame per sweep'),
      btn('swarm', () => run('swarm'), false,
        'the collaborative search, eq. (7), one frame per outer iteration'),
      btn('backtrack', () => run('backtrack'), false,
        'the certified classical baseline — deterministic, ignores the seed'),
    ),
    h('div', { className: 'cns-row' },
      h('span', { className: 'cns-note' }, 'seed'),
      btn('◀', () => setSeed(seed - 1), false, 'previous seed'),
      h('span', { className: 'cns-note' }, String(seed)),
      btn('▶', () => setSeed(seed + 1), false, 'next seed'),
    ),
    frames.length > 1
      ? h('div', { className: 'cns-row' },
          h('button', { onClick: () => { if (idx + 1 >= frames.length) setIdx(0); setPlaying(!playing) } },
            playing ? '⏸' : (idx + 1 >= frames.length ? '↻' : '▶')),
          h('input', {
            type: 'range', min: 0, max: frames.length - 1, value: Math.min(idx, frames.length - 1),
            onChange: (ev) => { setPlaying(false); setIdx(Number(ev.target.value)) },
            style: { flex: 1 },
          }),
          h('button', { onClick: () => { setFrames([]); setPens([]); setIdx(0); setSolved(false) } },
            'edit'),
        )
      : null,
    h('p', { className: 'cns-note' },
      busy ? 'Waiting for Lean…' : status),
    frames.length > 0
      ? h('p', { className: 'cns-note' },
          solved
            ? 'The decoded board was checked by `Instance.isQueens`; `decode_isQueens` says that check cannot fail when the penalty is zero.'
            : 'No zero found. If the placement is genuinely blocked, `exists_zero_iff_queens` is what makes that a fact about the board rather than a failure of the solver.')
      : null,
  )
}
