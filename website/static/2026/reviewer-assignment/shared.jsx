// Shared tokens, character clipart, and small primitives used across figures.

const FIG = {
  // Paper backgrounds & ink
  paper: '#fbfaf6',
  paperAlt: '#f5f1ea',
  ink: '#2a2520',
  inkSoft: '#6b6358',
  inkFaint: '#9a9285',
  rule: '#d8d2c5',
  ruleSoft: '#e7e1d4',

  // Paper types
  ml: '#d99478',          // muted terracotta
  mlSoft: '#f2dccf',
  mlDeep: '#a86247',
  opt: '#7aa6b8',         // muted teal-blue
  optSoft: '#d4e2e8',
  optDeep: '#4a7384',

  // Reviewers
  ben: '#7a5d82',         // muted plum
  benSoft: '#e3d6e6',
  grad: '#6b8a6f',        // muted forest
  gradSoft: '#d6e3d8',
  four: '#b09b78',        // warm taupe
  fourSoft: '#e8e0cf',

  // Highlights
  good: '#3e7a52',
  bad: '#a4513b',
  neutral: '#7a7468',

  // Type stacks
  serif: '"Source Serif 4", Georgia, serif',
  sans: 'Inter, system-ui, sans-serif',
  mono: '"JetBrains Mono", ui-monospace, monospace',
};

// ------------------------------------------------------------------
// Character clipart — flat, simple, distinguishable.
// Each is a small SVG bust: tinted background disc + silhouette + a hint.
// ------------------------------------------------------------------

function Avatar({ who, size = 64, ring = true }) {
  const data = {
    ben: {
      bg: FIG.benSoft, fg: FIG.ben,
      hair: '#3a2f2c',
      // long dark hair past the shoulders = Fei-fei ExpertLi
      extras: (
        <g>
          {/* long hair behind the head: drapes down past shoulders */}
          <path d="M16 30 Q14 44 16 56 L20 56 Q19 48 21 42 Q22 38 24 36 Q24 30 26 26 Q32 16 38 26 Q40 30 40 36 Q42 38 43 42 Q45 48 44 56 L48 56 Q50 44 48 30 Q46 16 32 14 Q18 16 16 30 Z"
                fill="#3a2f2c"/>
          {/* fringe / front hair */}
          <path d="M20 28 Q26 18 32 20 Q38 18 44 28 Q44 24 32 18 Q20 24 20 28 Z"
                fill="#3a2f2c"/>
          {/* subtle ear hint via shadow */}
        </g>
      ),
    },
    grad: {
      bg: FIG.gradSoft, fg: FIG.grad,
      // short dark hair, focused
      extras: (
        <g>
          <path d="M19 25 Q32 12 45 25 L45 30 Q32 22 19 30 Z" fill="#3a3530" />
          {/* small mustache hint */}
          <path d="M28 39 Q32 41 36 39" stroke="#3a3530" strokeWidth="1.4" fill="none" strokeLinecap="round" />
        </g>
      ),
    },
    four: {
      bg: FIG.fourSoft, fg: FIG.four,
      // wavy hair + small/young (Beginner)
      extras: (
        <g>
          <path d="M18 26 Q22 18 26 24 Q30 16 34 24 Q38 16 42 24 Q46 18 46 26 L46 28 Q32 22 18 28 Z" fill="#6b5840" />
        </g>
      ),
    },
  }[who];

  return (
    <svg viewBox="0 0 64 64" width={size} height={size} style={{ display: 'block' }}>
      <circle cx="32" cy="32" r="30" fill={data.bg} />
      {/* shoulders */}
      <path d="M8 60 Q8 46 22 44 L42 44 Q56 46 56 60 Z" fill={data.fg} />
      {/* head */}
      <circle cx="32" cy="30" r="13" fill="#f1e3d4" />
      {/* features */}
      {data.extras}
    </svg>
  );
}

const REVIEWERS = [
  { id: 'ben',  name: 'ExpertLi',  short: 'Fei',  color: FIG.ben,  soft: FIG.benSoft,  desc: 'veteran generalist' },
  { id: 'grad', name: 'Stepinski', short: 'Adam', color: FIG.grad, soft: FIG.gradSoft, desc: 'optimization specialist' },
  { id: 'four', name: 'Beginner',  short: 'Bay',  color: FIG.four, soft: FIG.fourSoft, desc: 'novice reviewer' },
];
const REV_BY_ID = Object.fromEntries(REVIEWERS.map(r => [r.id, r]));

const PAPER_TYPES = [
  { id: 'ml',  label: 'LLM',           short: 'LLM',  color: FIG.ml,  soft: FIG.mlSoft,  deep: FIG.mlDeep,  prob: 0.8 },
  { id: 'opt', label: 'Optimization', short: 'Opt', color: FIG.opt, soft: FIG.optSoft, deep: FIG.optDeep, prob: 0.2 },
];
const PT_BY_ID = Object.fromEntries(PAPER_TYPES.map(p => [p.id, p]));

// Similarity scores s_{v,r}
const SCORES = {
  ml:  { ben: 0.9, grad: 0.1, four: 0.05 },
  opt: { ben: 0.7, grad: 0.6, four: 0.05 },
};

// Willingness-to-pay values from the post
const WTP = {
  ml:  { ben: 0.9,  grad: -0.05, four: 0.05 },
  opt: { ben: 0.46, grad: 0.6,   four: 0.05 },
};

// Sequences from the post.
const GREEDY_SEQ = [
  { t: 1, type: 'opt', rev: 'ben',  score: 0.7  },
  { t: 2, type: 'ml',  rev: 'grad', score: 0.1  },
  { t: 3, type: 'ml',  rev: 'ben', score: 0.9 },
  { t: 4, type: 'ml',  rev: 'grad',  score: 0.1  },
  { t: 5, type: 'opt', rev: 'ben', score: 0.7  },
];
const WHITTLE_SEQ = [
  { t: 1, type: 'opt', rev: 'grad', score: 0.6  },
  { t: 2, type: 'ml',  rev: 'ben',  score: 0.9  },
  { t: 3, type: 'ml',  rev: 'four', score: 0.05 },
  { t: 4, type: 'ml',  rev: 'ben',  score: 0.9  },
  { t: 5, type: 'opt', rev: 'grad', score: 0.6  },
];

// ------------------------------------------------------------------
// Small primitives
// ------------------------------------------------------------------

// A pill that represents a paper-type label.
function TypePill({ type, size = 'md' }) {
  const pt = PT_BY_ID[type];
  const pad = size === 'sm' ? '2px 8px' : size === 'lg' ? '5px 14px' : '3px 10px';
  const font = size === 'sm' ? 11 : size === 'lg' ? 14 : 12;
  return (
    <span style={{
      display: 'inline-flex', alignItems: 'center', gap: 6,
      padding: pad, borderRadius: 999,
      background: pt.soft, color: pt.deep,
      fontFamily: FIG.sans, fontSize: font, fontWeight: 600, letterSpacing: 0.2,
    }}>
      <span style={{ width: 7, height: 7, borderRadius: 999, background: pt.color }}/>
      {pt.label}
    </span>
  );
}

// A compact reviewer chip with mini avatar and name.
function RevChip({ id, size = 'md', faded = false }) {
  const r = REV_BY_ID[id];
  const a = size === 'sm' ? 18 : size === 'lg' ? 28 : 22;
  const font = size === 'sm' ? 11 : size === 'lg' ? 14 : 12;
  return (
    <span style={{
      display: 'inline-flex', alignItems: 'center', gap: 6,
      opacity: faded ? 0.35 : 1,
    }}>
      <Avatar who={id} size={a} />
      <span style={{
        fontFamily: FIG.sans, fontSize: font, fontWeight: 600, color: r.color, letterSpacing: 0.1,
      }}>{r.name}</span>
    </span>
  );
}

// A number rendered in a serif numeric face.
function Num({ value, size = 16, weight = 500, color = FIG.ink, sign = false }) {
  const n = sign && value > 0 ? `+${value}` : `${value}`;
  return (
    <span style={{
      fontFamily: FIG.serif, fontVariantNumeric: 'tabular-nums lining-nums',
      fontSize: size, fontWeight: weight, color, letterSpacing: 0.2,
    }}>{n}</span>
  );
}

// A figure title block, used inside artboards.
function FigTitle({ eyebrow, title, sub }) {
  return (
    <div style={{ marginBottom: 14 }}>
      {eyebrow && (
        <div style={{
          fontFamily: FIG.sans, fontSize: 10.5, letterSpacing: 1.2,
          textTransform: 'uppercase', color: FIG.inkFaint, fontWeight: 600,
        }}>{eyebrow}</div>
      )}
      {title && (
        <div style={{
          fontFamily: FIG.serif, fontSize: 20, fontWeight: 500, color: FIG.ink,
          marginTop: 4, lineHeight: 1.2,
        }}>{title}</div>
      )}
      {sub && (
        <div style={{
          fontFamily: FIG.sans, fontSize: 12, color: FIG.inkSoft,
          marginTop: 4, lineHeight: 1.4, maxWidth: 520,
        }}>{sub}</div>
      )}
    </div>
  );
}

Object.assign(window, {
  FIG, Avatar, REVIEWERS, REV_BY_ID, PAPER_TYPES, PT_BY_ID,
  SCORES, WTP, GREEDY_SEQ, WHITTLE_SEQ,
  TypePill, RevChip, Num, FigTitle,
});
