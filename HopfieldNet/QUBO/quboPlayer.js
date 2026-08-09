/* Generic QUBO player: a timeline over frames, with a renderer chosen by `kind`.
   Sudoku frames are 81-character boards; graph frames are one character per vertex.
   Forked from CNS/sudokuPlayer.js.

Animation player for the CNS Sudoku pipeline (Li & Wang, ICIST 2022).

Loaded unbuilt by the Lean infoview, so this is plain ES2020 with
`React.createElement` rather than JSX.

Colour roles, from the validated reference palette:
  Algorithm 1 (constraint reduction)  categorical slot 1, blue
  Algorithm 2 (neurodynamic search)   categorical slot 2, orange  -- also the p(x) trace
  givens                              primary ink, bold
  conflicting cell                    dashed ring, NO hue

The conflict marker deliberately carries no colour. Status red beside slot-2
orange measures OKLab dE 10.8 in light mode and 6.8 in dark -- under the 15
normal-vision floor both times -- so the distinction rides on a shape channel
plus the printed count instead.
*/
import * as React from 'react'

const h = React.createElement

const DARK = `
  color-scheme: dark;
  --surface-1: #1a1a19;
  --text-primary: #ffffff;
  --text-secondary: #c3c2b7;
  --text-muted: #898781;
  --gridline: #2c2c2a;
  --baseline: #383835;
  --border: rgba(255,255,255,0.10);
  --alg1: #3987e5;
  --alg2: #d95926;
  --good: #0ca30c;
`

const STYLE = `
.cns-viz {
  color-scheme: light;
  --surface-1: #fcfcfb;
  --text-primary: #0b0b0b;
  --text-secondary: #52514e;
  --text-muted: #898781;
  --gridline: #e1e0d9;
  --baseline: #c3c2b7;
  --border: rgba(11,11,11,0.10);
  --alg1: #2a78d6;
  --alg2: #eb6834;
  --good: #0ca30c;
  font-family: system-ui, -apple-system, "Segoe UI", sans-serif;
  font-size: 12px;
  background: var(--surface-1);
  color: var(--text-primary);
  border: 1px solid var(--border);
  border-radius: 8px;
  padding: 12px 14px;
  width: max-content;
  user-select: none;
}
@media (prefers-color-scheme: dark) {
  :root:where(:not([data-theme="light"])) .cns-viz { ${DARK} }
}
:root[data-theme="dark"] .cns-viz,
body.vscode-dark .cns-viz,
body.vscode-high-contrast .cns-viz { ${DARK} }

.cns-viz .cns-title { font-weight: 600; font-size: 13px; }
.cns-viz .cns-cap {
  color: var(--text-secondary);
  font-variant-numeric: tabular-nums;
  margin: 2px 0 8px;
}
.cns-viz .cns-row { display: flex; align-items: center; gap: 8px; margin-top: 8px; }
.cns-viz button {
  font: inherit;
  color: var(--text-primary);
  background: transparent;
  border: 1px solid var(--border);
  border-radius: 5px;
  padding: 2px 8px;
  cursor: pointer;
  min-width: 30px;
}
.cns-viz button:hover { background: color-mix(in srgb, var(--text-primary) 8%, transparent); }
.cns-viz button[data-on="1"] { border-color: var(--alg2); color: var(--alg2); }
.cns-viz input[type=range] { flex: 1; accent-color: var(--alg2); min-width: 150px; }
.cns-viz .cns-legend {
  display: flex; gap: 12px; margin-top: 10px;
  color: var(--text-secondary); font-size: 11px;
}
.cns-viz .cns-key { display: inline-flex; align-items: center; gap: 5px; }
.cns-viz .cns-sw { width: 9px; height: 9px; border-radius: 2px; }
`

const N = 9
const NC = 81

/** Row, column and block units, as arrays of cell indices. */
const UNITS = (() => {
  const u = []
  for (let r = 0; r < N; r++) u.push(Array.from({ length: N }, (_, c) => r * N + c))
  for (let c = 0; c < N; c++) u.push(Array.from({ length: N }, (_, r) => r * N + c))
  for (let b = 0; b < N; b++) {
    const br = Math.floor(b / 3) * 3, bc = (b % 3) * 3
    u.push(Array.from({ length: N }, (_, k) => (br + Math.floor(k / 3)) * N + bc + (k % 3)))
  }
  return u
})()

const isDigit = (ch) => ch >= '1' && ch <= '9'

/** Cells sharing a unit with an equal digit. */
function conflictCells(s) {
  const bad = new Set()
  for (const u of UNITS) {
    const seen = new Map()
    for (const c of u) {
      const d = s[c]
      if (!isDigit(d)) continue
      if (!seen.has(d)) seen.set(d, [])
      seen.get(d).push(c)
    }
    for (const cs of seen.values()) if (cs.length > 1) for (const c of cs) bad.add(c)
  }
  return bad
}

const CELL = 30
const BOARD = CELL * N

function Board({ frame, givens, phase, conflicts }) {
  const kids = []

  // cell backgrounds for conflicts: a wash, so the dashed ring has something to sit on
  for (const c of conflicts) {
    kids.push(h('rect', {
      key: 'w' + c,
      x: (c % N) * CELL, y: Math.floor(c / N) * CELL, width: CELL, height: CELL,
      fill: 'currentColor', opacity: 0.06,
    }))
  }

  // hairline grid
  for (let i = 1; i < N; i++) {
    if (i % 3 === 0) continue
    kids.push(h('line', {
      key: 'gv' + i, x1: i * CELL, y1: 0, x2: i * CELL, y2: BOARD,
      stroke: 'var(--gridline)', strokeWidth: 1,
    }))
    kids.push(h('line', {
      key: 'gh' + i, x1: 0, y1: i * CELL, x2: BOARD, y2: i * CELL,
      stroke: 'var(--gridline)', strokeWidth: 1,
    }))
  }
  // block rules
  for (let i = 0; i <= N; i += 3) {
    kids.push(h('line', {
      key: 'bv' + i, x1: i * CELL, y1: 0, x2: i * CELL, y2: BOARD,
      stroke: 'var(--baseline)', strokeWidth: 2,
    }))
    kids.push(h('line', {
      key: 'bh' + i, x1: 0, y1: i * CELL, x2: BOARD, y2: i * CELL,
      stroke: 'var(--baseline)', strokeWidth: 2,
    }))
  }

  // digits
  for (let c = 0; c < NC; c++) {
    const d = frame[c]
    if (!isDigit(d)) continue
    const given = isDigit(givens[c])
    kids.push(h('text', {
      key: 't' + c,
      x: (c % N) * CELL + CELL / 2,
      y: Math.floor(c / N) * CELL + CELL / 2,
      textAnchor: 'middle', dominantBaseline: 'central',
      fontSize: 15,
      fontWeight: given ? 700 : 400,
      fill: given ? 'var(--text-primary)' : (phase === 0 ? 'var(--alg1)' : 'var(--alg2)'),
    }, d))
  }

  // conflict rings -- shape channel, no hue
  for (const c of conflicts) {
    kids.push(h('rect', {
      key: 'r' + c,
      x: (c % N) * CELL + 2.5, y: Math.floor(c / N) * CELL + 2.5,
      width: CELL - 5, height: CELL - 5,
      fill: 'none', stroke: 'var(--text-secondary)', strokeWidth: 1.5,
      strokeDasharray: '3 2', rx: 3,
    }))
  }

  return h('svg', {
    width: BOARD + 2, height: BOARD + 2, viewBox: `-1 -1 ${BOARD + 2} ${BOARD + 2}`,
    style: { display: 'block' },
  }, kids)
}

/** Step-line trace of the incumbent penalty over the search segment. */
function Trace({ pen, from, cur, onSeek }) {
  const W = BOARD, H = 34, PAD = 3
  const idx = []
  for (let i = from; i < pen.length; i++) if (pen[i] >= 0) idx.push(i)
  if (idx.length < 2) return null

  const hi = Math.max(...idx.map(i => pen[i]))
  const lo = 0
  const xOf = (k) => (idx.length === 1 ? 0 : (k / (idx.length - 1)) * (W - 2 * PAD) + PAD)
  const yOf = (v) => H - PAD - (hi === lo ? 0 : (v - lo) / (hi - lo)) * (H - 2 * PAD)

  let d = ''
  idx.forEach((i, k) => {
    const x = xOf(k), y = yOf(pen[i])
    d += k === 0 ? `M ${x} ${y}` : ` H ${x} V ${y}`
  })

  const at = idx.indexOf(cur)
  const marker = at >= 0
    ? h('circle', { cx: xOf(at), cy: yOf(pen[cur]), r: 3.5, fill: 'var(--alg2)' })
    : null

  const seek = (ev) => {
    const r = ev.currentTarget.getBoundingClientRect()
    const t = (ev.clientX - r.left - PAD) / (W - 2 * PAD)
    const k = Math.round(Math.min(1, Math.max(0, t)) * (idx.length - 1))
    onSeek(idx[k])
  }

  return h('div', { style: { marginTop: '8px' } },
    h('div', {
      style: { color: 'var(--text-secondary)', fontSize: '11px', marginBottom: '2px' },
    }, '‖Ax − b‖² of the incumbent'),
    h('svg', {
      width: W, height: H, viewBox: `0 0 ${W} ${H}`,
      style: { display: 'block', cursor: 'pointer' },
      onClick: seek,
    },
      h('line', {
        x1: 0, y1: yOf(0), x2: W, y2: yOf(0),
        stroke: 'var(--baseline)', strokeWidth: 1,
      }),
      h('path', {
        d, fill: 'none', stroke: 'var(--alg2)', strokeWidth: 2,
        strokeLinejoin: 'round', strokeLinecap: 'round',
      }),
      marker,
    ),
  )
}


/* ---------------------------------------------------------------- graph view

A frame is one character per vertex: '.' for uncoloured, otherwise a colour index
in base 36. Vertices are laid out on a circle, which needs no layout pass and keeps
every edge visible on the small canvas the infoview gives us. */

const PALETTE = [
  '#e06c75', '#61afef', '#98c379', '#e5c07b',
  '#c678dd', '#56b6c2', '#d19a66', '#abb2bf',
]

const colourOf = (ch) => {
  if (ch === '.' || ch === undefined) return null
  const k = parseInt(ch, 36)
  return Number.isNaN(k) ? null : PALETTE[k % PALETTE.length]
}

const GR = 150

function Graph({ frame, nverts, edges, ncolours }) {
  const pts = []
  for (let v = 0; v < nverts; v++) {
    const a = (2 * Math.PI * v) / Math.max(1, nverts) - Math.PI / 2
    pts.push([GR + (GR - 26) * Math.cos(a), GR + (GR - 26) * Math.sin(a)])
  }
  const bad = new Set()
  edges.forEach(([u, v], e) => {
    const cu = frame[u], cv = frame[v]
    if (cu !== '.' && cu !== undefined && cu === cv) bad.add(e)
  })
  const els = []
  edges.forEach(([u, v], e) => {
    if (!pts[u] || !pts[v]) return
    els.push(h('line', {
      key: 'e' + e,
      x1: pts[u][0], y1: pts[u][1], x2: pts[v][0], y2: pts[v][1],
      stroke: bad.has(e) ? 'var(--bad)' : 'var(--text-muted)',
      strokeWidth: bad.has(e) ? 2.5 : 1,
      opacity: bad.has(e) ? 1 : 0.45,
    }))
  })
  for (let v = 0; v < nverts; v++) {
    const c = colourOf(frame[v])
    els.push(h('circle', {
      key: 'v' + v, cx: pts[v][0], cy: pts[v][1], r: 11,
      fill: c || 'var(--bg)',
      stroke: c ? 'var(--text-primary)' : 'var(--text-muted)',
      strokeWidth: 1.2,
      strokeDasharray: c ? null : '2 2',
    }))
    els.push(h('text', {
      key: 't' + v, x: pts[v][0], y: pts[v][1] + 4,
      textAnchor: 'middle', fontSize: '10px',
      fill: c ? '#1b1b1b' : 'var(--text-muted)',
    }, String(v)))
  }
  return h('svg', {
    width: 2 * GR, height: 2 * GR,
    viewBox: `0 0 ${2 * GR} ${2 * GR}`,
    style: { display: 'block' },
  }, els)
}

/** Monochromatic edges, as a set, for the legend and the caption. */
function graphConflicts(frame, edges) {
  const bad = new Set()
  edges.forEach(([u, v], e) => {
    const cu = frame[u]
    if (cu !== '.' && cu !== undefined && cu === frame[v]) bad.add(e)
  })
  return bad
}

export default function (props) {
  const { title, frames, givens, phase, pen, outer, solved, note } = props
  const kind = props.kind || 'sudoku'
  const nverts = props.nverts || 0
  const edges = props.edges || []
  const ncolours = props.ncolours || 0
  const n = frames.length
  const [i, setI] = React.useState(0)
  const [playing, setPlaying] = React.useState(false)
  const [speed, setSpeed] = React.useState(1)

  React.useEffect(() => {
    if (!playing) return
    const id = setInterval(() => {
      setI((k) => {
        if (k + 1 >= n) { setPlaying(false); return k }
        return k + 1
      })
    }, 220 / speed)
    return () => clearInterval(id)
  }, [playing, speed, n])

  const frame = frames[i] || ''
  const ph = phase[i] || 0
  const conflicts = React.useMemo(
    () => (kind === 'graph' ? graphConflicts(frame, edges) : conflictCells(frame)),
    [frame, kind, edges])
  const searchStart = React.useMemo(() => {
    const k = phase.indexOf(1)
    return k < 0 ? n : k
  }, [phase, n])

  const filled = React.useMemo(() => {
    let f = 0
    for (let c = 0; c < NC; c++) if (isDigit(frame[c])) f++
    return f
  }, [frame])

  const restart = () => { setI(0); setPlaying(true) }
  const toggle = () => {
    if (i + 1 >= n) restart()
    else setPlaying((p) => !p)
  }

  const caption = [
    `frame ${i + 1}/${n}`,
    ph === 0 ? `Algorithm 1, ${i} deduction${i === 1 ? '' : 's'}`
             : `Algorithm 2, outer ${outer[i]}`,
    `${filled}/81 filled`,
    ph === 1 && pen[i] >= 0 ? `‖Ax−b‖² = ${pen[i]}` : null,
    conflicts.size > 0 ? `${conflicts.size} cells in conflict` : null,
  ].filter(Boolean).join(' · ')

  const key = (color, label, opts) => h('span', { className: 'cns-key', key: label },
    h('span', {
      className: 'cns-sw',
      style: opts && opts.ring
        ? { border: '1.5px dashed var(--text-secondary)', borderRadius: '2px' }
        : { background: color },
    }),
    label,
  )

  return h('div', { className: 'cns-viz' },
    h('style', null, STYLE),
    h('div', { className: 'cns-title' },
      title,
      solved
        ? h('span', { style: { color: 'var(--good)', marginLeft: '8px', fontWeight: 600 } },
            '✓ verified')
        : null,
    ),
    h('div', { className: 'cns-cap' }, caption),
    kind === 'graph'
      ? h(Graph, { frame, nverts, edges, ncolours })
      : h(Board, { frame, givens, phase: ph, conflicts }),
    h('div', { className: 'cns-row' },
      h('button', { onClick: toggle, title: 'play / pause' },
        playing ? '⏸' : (i + 1 >= n ? '↻' : '▶')),
      h('input', {
        type: 'range', min: 0, max: Math.max(0, n - 1), value: i,
        onChange: (ev) => { setPlaying(false); setI(Number(ev.target.value)) },
      }),
      [1, 2, 4].map((s) => h('button', {
        key: s, 'data-on': speed === s ? '1' : '0', onClick: () => setSpeed(s),
      }, s + '×')),
    ),
    searchStart < n
      ? h('div', {
          style: {
            display: 'flex', height: '4px', marginTop: '6px', borderRadius: '2px',
            overflow: 'hidden', gap: '2px',
          },
          title: 'reduction / search segments',
        },
          h('div', { style: { flex: searchStart, background: 'var(--alg1)', opacity: 0.55 } }),
          h('div', { style: { flex: n - searchStart, background: 'var(--alg2)', opacity: 0.55 } }),
        )
      : null,
    h(Trace, { pen, from: searchStart, cur: i, onSeek: (k) => { setPlaying(false); setI(k) } }),
    h('div', { className: 'cns-legend' },
      kind === 'graph' ? null : key('var(--text-primary)', 'given'),
      key('var(--alg1)', 'Algorithm 1'),
      key('var(--alg2)', 'Algorithm 2'),
      conflicts.size > 0
        ? key(null, kind === 'graph' ? 'monochromatic edge' : 'conflict', { ring: true })
        : null,
    ),
    note ? h('div', {
      style: { color: 'var(--text-muted)', fontSize: '11px', marginTop: '8px', maxWidth: BOARD + 'px' },
    }, note) : null,
  )
}
