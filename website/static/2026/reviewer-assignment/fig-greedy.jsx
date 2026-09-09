// Figures 2 (greedy timeline) and 5 (whittle timeline) share layout.
// Two variants per policy: linear sequence (A) and gantt (B).

// ---------- Variant A — linear arrival sequence ----------

function TimelineLinear({ seq, policyLabel, avg }) {
  const W = 880;
  const cellW = 132;
  const gap = 12;

  return (
    <div style={{
      width: W, padding: '32px 36px 30px', background: FIG.paper,
      fontFamily: FIG.sans, color: FIG.ink,
    }}>
      {/* time axis */}
      <div style={{
        display: 'flex', gap, alignItems: 'flex-end',
        marginBottom: 8, paddingLeft: 78,
      }}>
        {seq.map(s => (
          <div key={s.t} style={{
            width: cellW, textAlign: 'center',
            fontFamily: FIG.mono, fontSize: 10.5, color: FIG.inkFaint, letterSpacing: 1,
          }}>
            t = {s.t}
          </div>
        ))}
      </div>

      {/* arrivals row */}
      <Row label="arrival" labelFont={FIG.sans}>
        {seq.map(s => {
          const pt = PT_BY_ID[s.type];
          return (
            <div key={s.t} style={{
              width: cellW, height: 56,
              background: pt.soft, borderRadius: 8,
              display: 'flex', flexDirection: 'column',
              alignItems: 'center', justifyContent: 'center',
              border: `1px solid ${pt.color}33`,
            }}>
              <PaperGlyph type={s.type} />
              <span style={{ marginTop: 4, fontFamily: FIG.serif, fontSize: 13, fontWeight: 600, color: pt.deep }}>
                {pt.label}
              </span>
            </div>
          );
        })}
      </Row>

      {/* assignments row */}
      <Row label="assigned" mt={10}>
        {seq.map(s => {
          const r = REV_BY_ID[s.rev];
          return (
            <div key={s.t} style={{
              width: cellW, height: 72,
              background: FIG.paper,
              border: `1px solid ${FIG.rule}`, borderRadius: 8,
              display: 'flex', flexDirection: 'column',
              alignItems: 'center', justifyContent: 'center',
              gap: 4,
            }}>
              <Avatar who={s.rev} size={32} />
              <span style={{ fontFamily: FIG.sans, fontSize: 11, fontWeight: 600, color: r.color }}>
                {r.name}
              </span>
            </div>
          );
        })}
      </Row>

      {/* score row */}
      <Row label="score" mt={6}>
        {seq.map(s => {
          const bad = s.score < 0.2;
          const ok  = s.score >= 0.6;
          const col = bad ? FIG.bad : (ok ? FIG.good : FIG.ink);
          return (
            <div key={s.t} style={{
              width: cellW, height: 44,
              display: 'flex', alignItems: 'center', justifyContent: 'center',
            }}>
              <Num value={fmt(s.score)} size={26} weight={500} color={col} />
            </div>
          );
        })}
      </Row>

      {/* avg score */}
      <div style={{
        marginTop: 18, paddingTop: 14, borderTop: `1px solid ${FIG.rule}`,
        display: 'flex', alignItems: 'baseline', justifyContent: 'space-between',
      }}>
        <div>
          <span style={{
            fontFamily: FIG.sans, fontSize: 10.5, letterSpacing: 1.2,
            textTransform: 'uppercase', color: FIG.inkFaint, fontWeight: 600,
          }}>{policyLabel}</span>
        </div>
        <div style={{ display: 'flex', alignItems: 'baseline', gap: 10 }}>
          <span style={{ fontFamily: FIG.sans, fontSize: 12, color: FIG.inkSoft }}>average score</span>
          <Num value={avg.toFixed(2)} size={28} weight={600} />
        </div>
      </div>
    </div>
  );
}

function Row({ label, labelFont = FIG.sans, mt = 0, children }) {
  return (
    <div style={{
      display: 'flex', gap: 12, alignItems: 'center', marginTop: mt,
    }}>
      <div style={{
        width: 66, textAlign: 'right', flexShrink: 0,
        fontFamily: labelFont, fontSize: 11, color: FIG.inkSoft,
        fontStyle: labelFont === FIG.serif ? 'italic' : 'normal',
      }}>
        {label}
      </div>
      {children}
    </div>
  );
}

function PaperGlyph({ type, size = 16 }) {
  const pt = PT_BY_ID[type];
  // a stylized doc icon with a corner fold
  return (
    <svg viewBox="0 0 20 24" width={size * 0.85} height={size}>
      <path d="M2 1 H14 L18 5 V22 Q18 23 17 23 H3 Q2 23 2 22 Z" fill={FIG.paper} stroke={pt.deep} strokeWidth="1"/>
      <path d="M14 1 V5 H18" fill="none" stroke={pt.deep} strokeWidth="1"/>
      <line x1="5" y1="10" x2="14" y2="10" stroke={pt.deep} strokeWidth="0.9"/>
      <line x1="5" y1="13" x2="14" y2="13" stroke={pt.deep} strokeWidth="0.9"/>
      <line x1="5" y1="16" x2="11" y2="16" stroke={pt.deep} strokeWidth="0.9"/>
    </svg>
  );
}

// ---------- Variant B — Gantt (reviewers × time) ----------

function TimelineGantt({ seq, policyLabel, avg, d = 2 }) {
  const W = 880;
  const cols = seq.length;
  const labelW = 150;
  const gridW = W - labelW;
  const cellW = gridW / cols;
  const rowH = 64;

  // Build per-reviewer occupancy: at each time t, is rev busy?
  // assignment at time t means rev is "in" cell t (review begins) and busy for next d-1 more steps lightly.
  const cells = REVIEWERS.map(r => {
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
      width: W, padding: '32px 36px 30px', background: FIG.paper,
      fontFamily: FIG.sans, color: FIG.ink,
    }}>
      {/* time axis */}
      <div style={{ display: 'flex', marginLeft: labelW, marginBottom: 6 }}>
        {seq.map((s, i) => (
          <div key={i} style={{
            width: cellW, textAlign: 'center',
            fontFamily: FIG.mono, fontSize: 10.5, color: FIG.inkFaint, letterSpacing: 1,
          }}>t = {s.t}</div>
        ))}
      </div>

      {/* arrival strip */}
      <div style={{
        display: 'flex', marginLeft: labelW, marginBottom: 14,
        border: `1px solid ${FIG.rule}`, borderRadius: 8, overflow: 'hidden',
      }}>
        {seq.map((s, i) => {
          const pt = PT_BY_ID[s.type];
          return (
            <div key={i} style={{
              width: cellW, height: 40,
              background: pt.soft,
              borderRight: i < cols - 1 ? `1px solid ${FIG.rule}` : 'none',
              display: 'flex', alignItems: 'center', justifyContent: 'center', gap: 6,
            }}>
              <PaperGlyph type={s.type} size={14} />
              <span style={{ fontFamily: FIG.serif, fontSize: 12.5, fontWeight: 600, color: pt.deep }}>
                {pt.label}
              </span>
            </div>
          );
        })}
      </div>

      {/* reviewer rows */}
      <div style={{ position: 'relative' }}>
        {cells.map(({ r, row }, ri) => (
          <div key={r.id} style={{ display: 'flex', alignItems: 'stretch', marginBottom: 4 }}>
            <div style={{
              width: labelW, paddingRight: 14,
              display: 'flex', alignItems: 'center', gap: 10,
              flexShrink: 0,
            }}>
              <Avatar who={r.id} size={32} />
              <div>
                <div style={{ fontFamily: FIG.serif, fontSize: 13, fontWeight: 600, color: r.color, lineHeight: 1.1 }}>
                  {r.name}
                </div>
                <div style={{ fontSize: 10, color: FIG.inkFaint, marginTop: 1 }}>{r.desc}</div>
              </div>
            </div>
            <div style={{ display: 'flex', flex: 1 }}>
              {row.map((c, i) => {
                if (!c) {
                  return (
                    <div key={i} style={{
                      width: cellW, height: rowH,
                      borderRight: i < cols - 1 ? `1px dashed ${FIG.ruleSoft}` : 'none',
                      background: 'transparent',
                    }}/>
                  );
                }
                const pt = PT_BY_ID[c.s.type];
                if (c.kind === 'assigned') {
                  return (
                    <div key={i} style={{
                      width: cellW, height: rowH,
                      background: pt.soft,
                      border: `1.5px solid ${pt.color}`,
                      borderRight: i < cols - 1 ? `1.5px solid ${pt.color}` : `1.5px solid ${pt.color}`,
                      display: 'flex', alignItems: 'center', justifyContent: 'center',
                      flexDirection: 'column', gap: 2,
                      borderTopRightRadius: 0, borderBottomRightRadius: 0,
                      borderTopLeftRadius: 8, borderBottomLeftRadius: 8,
                    }}>
                      <span style={{ fontFamily: FIG.sans, fontSize: 9.5, color: pt.deep, letterSpacing: 0.6, textTransform: 'uppercase', fontWeight: 600 }}>
                        review
                      </span>
                      <Num value={fmt(c.s.score)} size={22} weight={500} color={c.s.score < 0.2 ? FIG.bad : FIG.ink} />
                    </div>
                  );
                }
                // busy continuation
                return (
                  <div key={i} style={{
                    width: cellW, height: rowH,
                    background: `repeating-linear-gradient(135deg, ${pt.soft} 0 8px, ${FIG.paper} 8px 14px)`,
                    borderTop: `1.5px solid ${pt.color}`,
                    borderBottom: `1.5px solid ${pt.color}`,
                    borderRight: i === cols - 1 || row[i + 1]?.kind !== 'busy' && row[i + 1]?.kind !== 'assigned'
                      ? `1.5px solid ${pt.color}` : 'none',
                    borderTopRightRadius: 8, borderBottomRightRadius: 8,
                    display: 'flex', alignItems: 'center', justifyContent: 'center',
                  }}>
                    <span style={{ fontFamily: FIG.sans, fontSize: 10, color: pt.deep, opacity: 0.7, letterSpacing: 0.6 }}>
                      busy
                    </span>
                  </div>
                );
              })}
            </div>
          </div>
        ))}
      </div>

      {/* avg score */}
      <div style={{
        marginTop: 18, paddingTop: 14, borderTop: `1px solid ${FIG.rule}`,
        display: 'flex', alignItems: 'baseline', justifyContent: 'space-between',
      }}>
        <div>
          <span style={{
            fontFamily: FIG.sans, fontSize: 10.5, letterSpacing: 1.2,
            textTransform: 'uppercase', color: FIG.inkFaint, fontWeight: 600,
          }}>{policyLabel}</span>
        </div>
        <div style={{ display: 'flex', alignItems: 'baseline', gap: 10 }}>
          <span style={{ fontFamily: FIG.sans, fontSize: 12, color: FIG.inkSoft }}>average score</span>
          <Num value={avg.toFixed(2)} size={28} weight={600} />
        </div>
      </div>
    </div>
  );
}

// Greedy-specific wrappers
function FigGreedyLinear()  { return <TimelineLinear seq={GREEDY_SEQ}  policyLabel="Greedy"  avg={0.54}/>; }
function FigGreedyGantt()   { return <TimelineGantt  seq={GREEDY_SEQ}  policyLabel="Greedy"  avg={0.54}/>; }

Object.assign(window, {
  TimelineLinear, TimelineGantt, PaperGlyph, Row,
  FigGreedyLinear, FigGreedyGantt,
});
