import "./style.css";
import { type Event, State, levelColor, nextOf, stateAt } from "./replay";

interface Trace {
  name: string;
  title: string;
  kind: "sudoku" | "queens" | "pigeons";
  vars: number;
  clauses: number;
  result: "sat" | "unsat";
  labels: Record<string, string>;
  events: Event[];
  givens?: number[];
  n?: number;
  pigeons?: number;
  holes?: number;
}

const TRACES = [
  ["queens-8", "8 queens"],
  ["queens-16", "16 queens"],
  ["pigeons-6-5", "6 pigeons, 5 holes (unsatisfiable)"],
  ["sudoku-hard", "Sudoku, 25 clues"],
  ["sudoku-easy", "Sudoku, 36 clues"],
];
const SPEEDS = [1, 3, 8, 25, 80, 300]; // events per second

const $ = <T extends HTMLElement>(id: string) => document.getElementById(id) as T;
let trace: Trace;
let pos = 0;
let state = new State();
let playing = false;
let last = 0;
let carry = 0;

function label(lit: number): string {
  const name = trace.labels[String(Math.abs(lit))] ?? `x${Math.abs(lit)}`;
  return lit > 0 ? name : `¬${name}`;
}

function clauseHTML(c: number[] | null): string {
  if (!c) return "<span class=muted>none yet</span>";
  return c
    .map((l) => {
      const v = state.value(l);
      const a = state.assigned.get(Math.abs(l));
      const style = a ? `style="border-color:${levelColor(a.level)}"` : "";
      return `<span class="lit ${v === true ? "t" : v === false ? "f" : ""}" ${style}>${label(l)}</span>`;
    })
    .join('<span class="or">∨</span>');
}

// ---------------------------------------------------------------- boards

function sudoku(): string {
  const g = trace.givens!;
  let html = '<div class="sudoku">';
  for (let r = 0; r < 9; r++)
    for (let c = 0; c < 9; c++) {
      let digit = 0;
      let level = -1;
      let decision = false;
      const candidates: number[] = [];
      for (let d = 0; d < 9; d++) {
        const v = 81 * r + 9 * c + d + 1;
        const a = state.assigned.get(v);
        if (a?.value) {
          digit = d + 1;
          level = a.level;
          decision = a.decision;
        } else if (!a) candidates.push(d + 1);
      }
      const given = g[9 * r + c] !== 0;
      const cls = ["cell", c % 3 === 2 && c < 8 ? "br" : "", r % 3 === 2 && r < 8 ? "bb" : "", given ? "given" : "", decision ? "decision" : ""].join(" ");
      const style = digit && !given ? `style="color:${levelColor(level)}"` : "";
      const inner = digit ? String(digit) : `<span class="cands">${[1, 2, 3, 4, 5, 6, 7, 8, 9].map((d) => (candidates.includes(d) ? d : "&nbsp;")).join("")}</span>`;
      html += `<div class="${cls}" ${style}>${inner}</div>`;
    }
  return html + "</div>";
}

function queens(): string {
  const n = trace.n!;
  let html = `<div class="chess" style="grid-template-columns:repeat(${n},1fr)">`;
  for (let r = 0; r < n; r++)
    for (let c = 0; c < n; c++) {
      const a = state.assigned.get(n * r + c + 1);
      const dark = (r + c) % 2 === 1 ? "dark" : "";
      if (a?.value) html += `<div class="sq ${dark} ${a.decision ? "decision" : ""}" style="color:${levelColor(a.level)}">♛</div>`;
      else if (a) html += `<div class="sq ${dark} ruled" style="color:${levelColor(a.level)}">×</div>`;
      else html += `<div class="sq ${dark}"></div>`;
    }
  return html + "</div>";
}

function pigeons(): string {
  const p = trace.pigeons!, h = trace.holes!;
  let html = `<div class="pigeons" style="grid-template-columns:auto repeat(${h},1fr)"><div></div>`;
  for (let j = 0; j < h; j++) html += `<div class="hd">hole ${j + 1}</div>`;
  for (let i = 0; i < p; i++) {
    html += `<div class="hd">pigeon ${i + 1}</div>`;
    for (let j = 0; j < h; j++) {
      const a = state.assigned.get(h * i + j + 1);
      if (a?.value) html += `<div class="pc ${a.decision ? "decision" : ""}" style="color:${levelColor(a.level)}">🐦</div>`;
      else if (a) html += `<div class="pc ruled" style="color:${levelColor(a.level)}">×</div>`;
      else html += `<div class="pc"></div>`;
    }
  }
  return html + "</div>";
}

// ---------------------------------------------------------------- panels

function chart() {
  const cv = $<HTMLCanvasElement>("chart");
  const ctx = cv.getContext("2d")!;
  const w = cv.width, h = cv.height;
  ctx.clearRect(0, 0, w, h);
  const all = stateAt(trace.events, trace.events.length).levels;
  const max = Math.max(1, ...all);
  const css = getComputedStyle(document.documentElement);
  ctx.strokeStyle = css.getPropertyValue("--line");
  ctx.beginPath();
  all.forEach((l, i) => {
    const x = (i / Math.max(1, all.length - 1)) * w, y = h - 6 - (l / max) * (h - 12);
    if (i) ctx.lineTo(x, y);
    else ctx.moveTo(x, y);
  });
  ctx.stroke();
  ctx.strokeStyle = css.getPropertyValue("--accent");
  ctx.lineWidth = 1.5;
  ctx.beginPath();
  state.levels.forEach((l, i) => {
    const x = (i / Math.max(1, all.length - 1)) * w, y = h - 6 - (l / max) * (h - 12);
    if (i) ctx.lineTo(x, y);
    else ctx.moveTo(x, y);
  });
  ctx.stroke();
  ctx.lineWidth = 1;
}

function render() {
  const s = state;
  $("board").innerHTML = trace.kind === "sudoku" ? sudoku() : trace.kind === "queens" ? queens() : pigeons();
  const ev = trace.events[pos - 1];
  const done = pos >= trace.events.length;
  $("caption").textContent = done
    ? trace.result === "sat"
      ? "Solved: every variable assigned, no clause false."
      : "Refuted: a conflict at level 0 — the formula is unsatisfiable."
    : ev
      ? ev.e === "decide"
        ? `Decision at level ${ev.level}: try ${label(ev.l)}.`
        : ev.e === "a"
          ? ev.why
            ? `${label(ev.l)} is forced (level ${ev.d}): every other literal of its clause is false.`
            : ev.d === 0
              ? `${label(ev.l)} holds at level 0.`
              : `${label(ev.l)} assigned by decision.`
          : ev.e === "conflict"
            ? "Conflict: a clause has all its literals false."
            : ev.e === "learn"
              ? `Learnt a clause of ${ev.c.length} literals (LBD ${ev.lbd}); back to level ${ev.back}.`
              : ev.e === "back"
                ? `Backjump to level ${ev.to}.`
                : "Restart."
      : `${trace.vars} variables, ${trace.clauses} clauses. Press Play.`;
  const counters: [string, string][] = [
    ["event", `${pos.toLocaleString()} / ${trace.events.length.toLocaleString()}`],
    ["assigned", `${s.assigned.size} / ${trace.vars}`],
    ["level", String(s.level())],
    ["decisions", String(s.decisionCount)],
    ["conflicts", String(s.conflicts)],
    ["restarts", String(s.restarts)],
  ];
  $("counters").innerHTML = counters.map(([k, v]) => `<dt>${k}</dt><dd>${v}</dd>`).join("");
  const byLevel = new Map<number, number>();
  for (const a of s.assigned.values()) byLevel.set(a.level, (byLevel.get(a.level) ?? 0) + 1);
  $("stack").innerHTML =
    `<li><span class="sw" style="background:${levelColor(0)}"></span>level 0: ${byLevel.get(0) ?? 0} forced</li>` +
    s.decisions
      .slice(1)
      .map((d, i) => `<li><span class="sw" style="background:${levelColor(i + 1)}"></span>level ${i + 1}: <b>${label(d)}</b>, ${Math.max(0, (byLevel.get(i + 1) ?? 1) - 1)} implied</li>`)
      .join("");
  $("conflict").innerHTML = clauseHTML(s.conflict);
  $("learnt-count").textContent = `(${s.learnts.length})`;
  $("learnts").innerHTML = s.learnts
    .slice(-8)
    .reverse()
    .map((l) => `<li><span class="meta">LBD ${l.lbd}, back to ${l.back}</span>${clauseHTML(l.clause)}</li>`)
    .join("");
  $<HTMLInputElement>("scrub").value = String(pos);
  chart();
}

function seek(n: number) {
  pos = Math.max(0, Math.min(n, trace.events.length));
  state = stateAt(trace.events, pos);
  render();
}

function step(k = 1) {
  for (let i = 0; i < k && pos < trace.events.length; i++) state.apply(trace.events[pos++]);
  if (pos >= trace.events.length) setPlaying(false);
  render();
}

function setPlaying(p: boolean) {
  playing = p;
  $("play").textContent = p ? "Pause" : "Play";
  if (p) {
    if (pos >= trace.events.length) seek(0);
    last = performance.now();
    requestAnimationFrame(tick);
  }
}

function tick(now: number) {
  if (!playing) return;
  carry += ((now - last) / 1000) * SPEEDS[Number($<HTMLInputElement>("speed").value)];
  last = now;
  const k = Math.floor(carry);
  carry -= k;
  if (k > 0) step(k);
  if (playing) requestAnimationFrame(tick);
}

async function load(name: string) {
  setPlaying(false);
  trace = await fetch(`traces/${name}.json`).then((r) => r.json());
  $<HTMLInputElement>("scrub").max = String(trace.events.length);
  seek(0);
}

$<HTMLSelectElement>("trace").innerHTML = TRACES.map(([v, t]) => `<option value="${v}">${t}</option>`).join("");
$<HTMLSelectElement>("trace").addEventListener("change", (e) => void load((e.target as HTMLSelectElement).value));
$("play").addEventListener("click", () => setPlaying(!playing));
$("step").addEventListener("click", () => {
  setPlaying(false);
  step();
});
$("next-conflict").addEventListener("click", () => {
  setPlaying(false);
  seek(nextOf(trace.events, pos, "learn"));
});
$<HTMLInputElement>("scrub").addEventListener("input", (e) => {
  setPlaying(false);
  seek(Number((e.target as HTMLInputElement).value));
});
void load(TRACES[0][0]);
