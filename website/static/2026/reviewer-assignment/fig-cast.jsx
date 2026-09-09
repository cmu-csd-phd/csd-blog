// Figure 1 — The cast & similarity matrix.

// ---------- Variant A — Reviewer cards above a heatmap matrix ----------

function FigCastMatrix() {
  const W = 880;
  return (
    <div style={{
      width: W, padding: '32px 40px 32px',
      background: FIG.paper, fontFamily: FIG.sans, color: FIG.ink,
      display: 'flex', justifyContent: 'center',
    }}>
      <ScoreMatrix scores={SCORES} showProb />
    </div>
  );
}

function ScoreMatrix({ scores, showProb = false, showWtp = false, values = null, highlight = null }) {
  const data = values || scores;
  const cellH = 64;
  const labelW = 200;
  const colW = 168;
  return (
    <div style={{
      display: 'inline-grid',
      gridTemplateColumns: `${labelW}px repeat(3, ${colW}px)`,
      borderTop: `1px solid ${FIG.rule}`,
      borderLeft: `1px solid ${FIG.rule}`,
    }}>
      {/* corner */}
      <div style={cellStyle(cellH * 0.6, { background: FIG.paper, borderRight: `1px solid ${FIG.rule}` })}/>
      {REVIEWERS.map(r => (
        <div key={r.id} style={cellStyle(cellH * 0.6, {
          background: FIG.paper, borderRight: `1px solid ${FIG.rule}`,
          alignItems: 'center', justifyContent: 'center', gap: 8,
          flexDirection: 'row', display: 'flex', padding: '0 12px',
        })}>
          <Avatar who={r.id} size={26} />
          <span style={{ fontFamily: FIG.serif, fontSize: 13.5, fontWeight: 600, color: r.color }}>
            {r.name}
          </span>
        </div>
      ))}

      {/* rows */}
      {PAPER_TYPES.map(pt => (
        <React.Fragment key={pt.id}>
          <div style={cellStyle(cellH, {
            background: pt.soft,
            borderRight: `1px solid ${FIG.rule}`,
            borderTop: `1px solid ${FIG.rule}`,
            padding: '0 16px',
          })}>
            <div style={{ display: 'flex', alignItems: 'center', gap: 8 }}>
              <span style={{ width: 8, height: 8, borderRadius: 999, background: pt.color }}/>
              <span style={{ fontFamily: FIG.serif, fontSize: 14, fontWeight: 600, color: pt.deep }}>{pt.label}</span>
            </div>
            {showProb && (
              <div style={{ fontSize: 10.5, color: pt.deep, opacity: 0.8, marginTop: 2, fontFamily: FIG.mono }}>
                p = {pt.prob}
              </div>
            )}
          </div>
          {REVIEWERS.map(r => {
            const v = data[pt.id][r.id];
            const isHi = highlight && highlight.some(([t, rv]) => t === pt.id && rv === r.id);
            return (
              <div key={r.id} style={cellStyle(cellH, {
                borderRight: `1px solid ${FIG.rule}`,
                borderTop: `1px solid ${FIG.rule}`,
                background: heatTint(v, pt.color),
                alignItems: 'center', justifyContent: 'center',
                position: 'relative',
                outline: isHi ? `2px solid ${FIG.ink}` : 'none',
                outlineOffset: -2,
              })}>
                <Num value={fmt(v)} size={22} weight={500} color={v < 0 ? FIG.bad : FIG.ink} />
              </div>
            );
          })}
        </React.Fragment>
      ))}
    </div>
  );
}

function cellStyle(h, extra) {
  return {
    height: h,
    display: 'flex', flexDirection: 'column', justifyContent: 'center',
    boxSizing: 'border-box',
    borderBottom: `1px solid ${FIG.rule}`,
    ...extra,
  };
}

// Light tint proportional to value, anchored on the paper-type color.
function heatTint(v, color) {
  const c = clamp((v - 0) / 1, 0, 1);
  // Background is paper, blended toward `color` by alpha = c * 0.45
  const alpha = Math.max(0, c) * 0.45;
  return `color-mix(in oklab, ${color} ${Math.round(alpha * 100)}%, ${FIG.paper})`;
}
function clamp(x, a, b) { return Math.min(b, Math.max(a, x)); }
function fmt(v) {
  if (v === 0) return '0';
  const s = (Math.abs(v) < 1 ? v.toFixed(2) : v.toFixed(2)).replace(/^0\./, '.').replace(/^-0\./, '−.');
  return s;
}

// ---------- Variant B — Bipartite graph (paper types ↔ reviewers) ----------

function FigCastBipartite() {
  const W = 880, H = 380;
  const leftX = 170, rightX = 700;
  const ptY = { ml: 110, opt: 260 };
  const revY = { ben: 80, grad: 190, four: 300 };

  // Edge weight → stroke width and opacity
  const edges = [];
  PAPER_TYPES.forEach(pt => {
    REVIEWERS.forEach(r => {
      edges.push({ pt: pt.id, r: r.id, w: SCORES[pt.id][r.id] });
    });
  });

  return (
    <div style={{
      width: W, padding: '32px 36px 28px', background: FIG.paper,
      fontFamily: FIG.sans, color: FIG.ink,
    }}>
      <svg viewBox={`0 0 ${W - 72} ${H}`} width={W - 72} height={H}>
        {/* edges */}
        {edges.map(e => {
          const x1 = leftX, y1 = ptY[e.pt];
          const x2 = rightX, y2 = revY[e.r];
          const sw = 1 + e.w * 12;
          const col = PT_BY_ID[e.pt].color;
          return (
            <g key={`${e.pt}-${e.r}`}>
              <path
                d={`M${x1} ${y1} C ${(x1+x2)/2} ${y1}, ${(x1+x2)/2} ${y2}, ${x2} ${y2}`}
                stroke={col} strokeWidth={sw} fill="none"
                opacity={0.35 + e.w * 0.5}
                strokeLinecap="round"
              />
              {/* score label */}
              <g transform={`translate(${(x1+x2)/2}, ${(y1+y2)/2})`}>
                <rect x={-22} y={-11} width={44} height={22} rx={11} fill={FIG.paper} stroke={col} strokeOpacity={0.4}/>
                <text x={0} y={5} textAnchor="middle" fontFamily={FIG.serif} fontSize={13} fontWeight={500} fill={FIG.ink} style={{ fontVariantNumeric: 'tabular-nums' }}>
                  {fmt(e.w)}
                </text>
              </g>
            </g>
          );
        })}

        {/* Paper type nodes (left) */}
        {PAPER_TYPES.map(pt => (
          <g key={pt.id} transform={`translate(${leftX}, ${ptY[pt.id]})`}>
            <circle r={36} fill={pt.soft} stroke={pt.color} strokeWidth={1.5}/>
            <text textAnchor="middle" y={-2} fontFamily={FIG.serif} fontSize={14} fontWeight={600} fill={pt.deep}>
              {pt.label}
            </text>
            <text textAnchor="middle" y={14} fontFamily={FIG.mono} fontSize={10.5} fill={pt.deep} opacity={0.85}>
              p={pt.prob}
            </text>
          </g>
        ))}

        {/* Reviewer nodes (right) — clipart */}
        {REVIEWERS.map(r => (
          <g key={r.id} transform={`translate(${rightX}, ${revY[r.id]})`}>
            <foreignObject x={-32} y={-32} width={64} height={64}>
              <Avatar who={r.id} size={64} />
            </foreignObject>
            <text x={44} y={4} fontFamily={FIG.serif} fontSize={14} fontWeight={600} fill={r.color}>
              {r.name}
            </text>
            <text x={44} y={20} fontFamily={FIG.sans} fontSize={11} fill={FIG.inkSoft}>
              {r.desc}
            </text>
          </g>
        ))}

        {/* axis labels */}
        <text x={leftX} y={20} textAnchor="middle" fontFamily={FIG.sans} fontSize={10.5}
              fill={FIG.inkFaint} letterSpacing={1.2} style={{ textTransform: 'uppercase' }}>
          paper type
        </text>
        <text x={rightX} y={20} textAnchor="middle" fontFamily={FIG.sans} fontSize={10.5}
              fill={FIG.inkFaint} letterSpacing={1.2} style={{ textTransform: 'uppercase' }}>
          reviewer
        </text>
      </svg>
    </div>
  );
}

Object.assign(window, { FigCastMatrix, FigCastBipartite, ScoreMatrix, fmt, heatTint });
