// Figure 5 — Whittle timeline (mirror of greedy, separate file so each can be
// tweaked independently if needed).

function FigWhittleLinear() { return <TimelineLinear seq={WHITTLE_SEQ} policyLabel="Whittle (willingness-to-pay)" avg={0.61}/>; }
function FigWhittleGantt()  { return <TimelineGantt  seq={WHITTLE_SEQ} policyLabel="Whittle (willingness-to-pay)" avg={0.61}/>; }

Object.assign(window, { FigWhittleLinear, FigWhittleGantt });
