// fig-unfriendly.jsx
// Three figures for "An Example Where Greedy Struggles":
//   FigUnfriendlyCast          — score matrix
//   FigUnfriendlyGreedyGantt   — Greedy timeline
//   FigUnfriendlyOptimalGantt  — Optimal timeline
//
// Same 5-paper run: Bad, Good, Bad, Good, Bad  (d = 2 lockout steps)
// Greedy avg = 0.006  |  Optimal avg = 0.40

// ─── Data ────────────────────────────────────────────────────────────────────

const UF_REVIEWERS = [
  { id: 'exp', avatarKey: 'ben',  name: 'Expert',     desc: 'scores 1 on Good',  color: FIG.ben,  soft: FIG.benSoft  },
  { id: 'b1',  avatarKey: 'grad', name: 'Beginner 1', desc: 'scores 0 always',   color: FIG.grad, soft: FIG.gradSoft },
  { id: 'b2',  avatarKey: 'four', name: 'Beginner 2', desc: 'scores 0 always',   color: FIG.four, soft: FIG.fourSoft },
];
const UF_REV = Object.fromEntries(UF_REVIEWERS.map(r => [r.id, r]));

const UF_PAPERS = [
  { id: 'good', label: 'Good', prob: 0.1, color: FIG.opt, soft: FIG.optSoft, deep: FIG.optDeep },
  { id: 'bad',  label: 'Bad',  prob: 0.9, color: FIG.ml,  soft: FIG.mlSoft,  deep: FIG.mlDeep  },
];
const UF_PT = Object.fromEntries(UF_PAPERS.map(p => [p.id, p]));

const UF_SCORES = {
  good: { exp: 1,    b1: 0, b2: 0 },
  bad:  { exp: 0.01, b1: 0, b2: 0 },
};

// Both sequences share the same arrival order: Bad, Good, Bad, Good, Bad.
const UF_GREEDY_SEQ = [
  { t: 1, type: 'bad',  rev: 'exp', score: 0.01 },   // Expert is free; Greedy assigns
  { t: 2, type: 'good', rev: 'b1',  score: 0    },   // Expert busy — missed Good paper
  { t: 3, type: 'bad',  rev: 'exp', score: 0.01 },   // Expert free again; Greedy assigns
  { t: 4, type: 'good', rev: 'b1',  score: 0    },   // Expert busy — missed again
  { t: 5, type: 'bad',  rev: 'exp', score: 0.01 },   // Expert free; Greedy assigns
];

const UF_OPTIMAL_SEQ = [
  { t: 1, type: 'bad',  rev: 'b1',  score: 0 },      // Expert idle; Beginner absorbs
  { t: 2, type: 'good', rev: 'exp', score: 1 },      // Expert free → scores 1
  { t: 3, type: 'bad',  rev: 'b1',  score: 0 },      // Expert busy; Beginner absorbs
  { t: 4, type: 'good', rev: 'exp', score: 1 },      // Expert free → scores 1
  { t: 5, type: 'bad',  rev: 'b1',  score: 0 },      // Expert busy; Beginner absorbs
];

// ─── Helpers ─────────────────────────────────────────────────────────────────

// Local format: strip trailing zeros but keep 2 dp for decimals; show '1' for 1.
function ufFmt(v) {
  if (v === 0)  return '0';
  if (v === 1)  return '1';
  return fmt(v);   // fmt from shared.jsx / fig-cast.jsx
}

function ufCellStyle(h, extra) {
  return {
    height: h,
    display: 'flex', flexDirection: 'column', justifyContent: 'center',
    boxSizing: 'border-box',
    borderBottom: `1px solid ${FIG.rule}`,
    ...extra,
  };
}

// Paper glyph that looks up from UF_PT (types 'good' / 'bad').
function UfPaperGlyph({ type, size = 16 }) {
  const pt = UF_PT[type];
  return (
    <svg viewBox="0 0 20 24" width={size * 0.85} height={size}>
      <path d="M2 1 H14 L18 5 V22 Q18 23 17 23 H3 Q2 23 2 22 Z"
            fill={FIG.paper} stroke={pt.deep} strokeWidth="1"/>
      <path d="M14 1 V5 H18" fill="none" stroke={pt.deep} strokeWidth="1"/>
      <line x1="5" y1="10" x2="14" y2="10" stroke={pt.deep} strokeWidth="0.9"/>
      <line x1="5" y1="13" x2="14" y2="13" stroke={pt.deep} strokeWidth="0.9"/>
      <line x1="5" y1="16" x2="11" y2="16" stroke={pt.deep} strokeWidth="0.9"/>
    </svg>
  );
}

// ─── Cast table ──────────────────────────────────────────────────────────────

function FigUnfriendlyCast() {
  const cellH = 64;
  const labelW = 160;
  const colW   = 168;

  return (
    <div style={{
      width: 880, padding: '32px 40px 32px',
      background: FIG.paper, fontFamily: FIG.sans, color: FIG.ink,
      display: 'flex', justifyContent: 'center',
    }}>
      <div style={{
        display: 'inline-grid',
        gridTemplateColumns: `${labelW}px repeat(3, ${colW}px)`,
        borderTop:  `1px solid ${FIG.rule}`,
        borderLeft: `1px solid ${FIG.rule}`,
      }}>

        {/* ── header row ─────────────────────────────────────────────── */}
        <div style={ufCellStyle(cellH * 0.65, {
          background: FIG.paper,
          borderRight: `1px solid ${FIG.rule}`,
        })} />

        {UF_REVIEWERS.map(r => (
          <div key={r.id} style={ufCellStyle(cellH * 0.65, {
            background: FIG.paper,
            borderRight: `1px solid ${FIG.rule}`,
            flexDirection: 'column',
            alignItems: 'center', justifyContent: 'center',
            gap: 4, padding: '6px 12px',
          })}>
            <Avatar who={r.avatarKey} size={26} />
            <span style={{
              fontFamily: FIG.serif, fontSize: 13, fontWeight: 600, color: r.color,
            }}>{r.name}</span>
          </div>
        ))}

        {/* ── data rows ──────────────────────────────────────────────── */}
        {UF_PAPERS.map(pt => (
          <React.Fragment key={pt.id}>
            {/* row label */}
            <div style={ufCellStyle(cellH, {
              background: pt.soft,
              borderRight: `1px solid ${FIG.rule}`,
              borderTop:   `1px solid ${FIG.rule}`,
              padding: '0 16px',
            })}>
              <div style={{ display: 'flex', alignItems: 'center', gap: 8 }}>
                <span style={{ width: 8, height: 8, borderRadius: 999, background: pt.color }} />
                <span style={{
                  fontFamily: FIG.serif, fontSize: 14, fontWeight: 600, color: pt.deep,
                }}>{pt.label}</span>
              </div>
              <div style={{
                fontSize: 10.5, color: pt.deep, opacity: 0.8, marginTop: 2,
                fontFamily: FIG.mono,
              }}>p = {pt.prob}</div>
            </div>

            {/* score cells */}
            {UF_REVIEWERS.map(r => {
              const v = UF_SCORES[pt.id][r.id];
              return (
                <div key={r.id} style={ufCellStyle(cellH, {
                  borderRight:  `1px solid ${FIG.rule}`,
                  borderTop:    `1px solid ${FIG.rule}`,
                  background:   heatTint(v, pt.color),   // heatTint from fig-cast.jsx
                  alignItems:   'center',
                  justifyContent: 'center',
                })}>
                  <Num
                    value={ufFmt(v)}
                    size={22} weight={500}
                    color={v < 0 ? FIG.bad : FIG.ink}
                  />
                </div>
              );
            })}
          </React.Fragment>
        ))}

      </div>
    </div>
  );
}

// ─── Gantt ────────────────────────────────────────────────────────────────────

function UnfriendlyGantt({ seq, policyLabel, avg, d = 2 }) {
  const W      = 880;
  const cols   = seq.length;
  const labelW = 150;
  const gridW  = W - labelW;
  const cellW  = gridW / cols;
  const rowH   = 64;

  // Build per-reviewer occupancy (assigned + busy tail).
  const cells = UF_REVIEWERS.map(r => {
    const row = Array(cols).fill(null);
    seq.forEach((s, i) => {
      if (s.rev === r.id) {
        row[i] = { kind: 'assigned', s };
        for (let k = 1; k < d; k++) {
          if (i + k < cols) row[i + k] = { kind: 'busy', s };
        }
      }
    });
    return { r, row };
  });

  return (
    <div style={{
      width: W, padding: '32px 36px 30px',
      background: FIG.paper, fontFamily: FIG.sans, color: FIG.ink,
    }}>

      {/* ── time axis ──────────────────────────────────────────────── */}
      <div style={{ display: 'flex', marginLeft: labelW, marginBottom: 6 }}>
        {seq.map((s, i) => (
          <div key={i} style={{
            width: cellW, textAlign: 'center',
            fontFamily: FIG.mono, fontSize: 10.5,
            color: FIG.inkFaint, letterSpacing: 1,
          }}>t = {s.t}</div>
        ))}
      </div>

      {/* ── arrival strip ──────────────────────────────────────────── */}
      <div style={{
        display: 'flex', marginLeft: labelW, marginBottom: 14,
        border: `1px solid ${FIG.rule}`, borderRadius: 8, overflow: 'hidden',
      }}>
        {seq.map((s, i) => {
          const pt = UF_PT[s.type];
          return (
            <div key={i} style={{
              width: cellW, height: 40,
              background: pt.soft,
              borderRight: i < cols - 1 ? `1px solid ${FIG.rule}` : 'none',
              display: 'flex', alignItems: 'center', justifyContent: 'center', gap: 6,
            }}>
              <UfPaperGlyph type={s.type} size={14} />
              <span style={{
                fontFamily: FIG.serif, fontSize: 12.5, fontWeight: 600, color: pt.deep,
              }}>{pt.label}</span>
            </div>
          );
        })}
      </div>

      {/* ── reviewer rows ──────────────────────────────────────────── */}
      {cells.map(({ r, row }) => (
        <div key={r.id} style={{
          display: 'flex', alignItems: 'stretch', marginBottom: 4,
        }}>
          {/* label */}
          <div style={{
            width: labelW, paddingRight: 14, flexShrink: 0,
            display: 'flex', alignItems: 'center', gap: 10,
          }}>
            <Avatar who={r.avatarKey} size={32} />
            <div>
              <div style={{
                fontFamily: FIG.serif, fontSize: 13, fontWeight: 600,
                color: r.color, lineHeight: 1.1,
              }}>{r.name}</div>
              <div style={{ fontSize: 10, color: FIG.inkFaint, marginTop: 1 }}>
                {r.desc}
              </div>
            </div>
          </div>

          {/* timeline cells */}
          <div style={{ display: 'flex', flex: 1 }}>
            {row.map((c, i) => {
              if (!c) {
                return (
                  <div key={i} style={{
                    width: cellW, height: rowH,
                    borderRight: i < cols - 1 ? `1px dashed ${FIG.ruleSoft}` : 'none',
                    background: 'transparent',
                  }} />
                );
              }

              const pt = UF_PT[c.s.type];

              if (c.kind === 'assigned') {
                return (
                  <div key={i} style={{
                    width: cellW, height: rowH,
                    background: pt.soft,
                    border: `1.5px solid ${pt.color}`,
                    borderTopLeftRadius:    8,
                    borderBottomLeftRadius: 8,
                    borderTopRightRadius:    0,
                    borderBottomRightRadius: 0,
                    display: 'flex', alignItems: 'center',
                    justifyContent: 'center',
                    flexDirection: 'column', gap: 2,
                  }}>
                    <span style={{
                      fontFamily: FIG.sans, fontSize: 9.5, color: pt.deep,
                      letterSpacing: 0.6, textTransform: 'uppercase', fontWeight: 600,
                    }}>review</span>
                    <Num
                      value={ufFmt(c.s.score)}
                      size={22} weight={500}
                      color={c.s.score < 0.2 ? FIG.bad : FIG.ink}
                    />
                  </div>
                );
              }

              // busy continuation
              const isLast = i === cols - 1;
              const nextIsBusy = !isLast && (row[i + 1]?.kind === 'busy' || row[i + 1]?.kind === 'assigned');
              return (
                <div key={i} style={{
                  width: cellW, height: rowH,
                  background: `repeating-linear-gradient(135deg, ${pt.soft} 0 8px, ${FIG.paper} 8px 14px)`,
                  borderTop:    `1.5px solid ${pt.color}`,
                  borderBottom: `1.5px solid ${pt.color}`,
                  borderRight:  (!nextIsBusy) ? `1.5px solid ${pt.color}` : 'none',
                  borderLeft:   'none',
                  borderTopRightRadius:    8,
                  borderBottomRightRadius: 8,
                  display: 'flex', alignItems: 'center', justifyContent: 'center',
                }}>
                  <span style={{
                    fontFamily: FIG.sans, fontSize: 10,
                    color: pt.deep, opacity: 0.7, letterSpacing: 0.6,
                  }}>busy</span>
                </div>
              );
            })}
          </div>
        </div>
      ))}

      {/* ── footer ─────────────────────────────────────────────────── */}
      <div style={{
        marginTop: 18, paddingTop: 14,
        borderTop: `1px solid ${FIG.rule}`,
        display: 'flex', alignItems: 'baseline',
        justifyContent: 'space-between',
      }}>
        <span style={{
          fontFamily: FIG.sans, fontSize: 10.5, letterSpacing: 1.2,
          textTransform: 'uppercase', color: FIG.inkFaint, fontWeight: 600,
        }}>{policyLabel}</span>
        <div style={{ display: 'flex', alignItems: 'baseline', gap: 10 }}>
          <span style={{ fontFamily: FIG.sans, fontSize: 12, color: FIG.inkSoft }}>
            average score
          </span>
          <Num
            value={avg < 0.01 ? avg.toFixed(3) : avg.toFixed(2)}
            size={28} weight={600}
          />
        </div>
      </div>
    </div>
  );
}

function FigUnfriendlyGreedyGantt() {
  return <UnfriendlyGantt seq={UF_GREEDY_SEQ} policyLabel="Greedy" avg={0.006} />;
}
function FigUnfriendlyOptimalGantt() {
  return <UnfriendlyGantt seq={UF_OPTIMAL_SEQ} policyLabel="Optimal (Lag / Whittle)" avg={0.40} />;
}

Object.assign(window, {
  FigUnfriendlyCast,
  FigUnfriendlyGreedyGantt,
  FigUnfriendlyOptimalGantt,
});
