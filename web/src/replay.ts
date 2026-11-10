// Replays a solver trace: the state of the search after any number of events.

export type Event =
  | { e: "a"; l: number; d: number; why?: number[] }
  | { e: "decide"; l: number; level: number }
  | { e: "back"; to: number }
  | { e: "conflict"; c: number[] }
  | { e: "learn"; c: number[]; lbd: number; back: number }
  | { e: "restart" };

export interface Assignment {
  value: boolean;
  level: number;
  decision: boolean;
  why?: number[];
  order: number; // position on the trail
}

export interface Learnt {
  clause: number[];
  lbd: number;
  back: number;
  at: number; // event index
}

export class State {
  /** variable -> its assignment */
  assigned = new Map<number, Assignment>();
  /** decision literal of each level (index 0 is unused) */
  decisions: number[] = [0];
  learnts: Learnt[] = [];
  conflict: number[] | null = null;
  conflicts = 0;
  decisionCount = 0;
  restarts = 0;
  /** decision level after each event, for the level chart */
  levels: number[] = [];
  index = 0;
  private trailLength = 0;

  level(): number {
    return this.decisions.length - 1;
  }

  apply(ev: Event) {
    switch (ev.e) {
      case "decide":
        this.decisionCount++;
        this.decisions.push(ev.l);
        break;
      case "a":
        this.assigned.set(Math.abs(ev.l), { value: ev.l > 0, level: ev.d, decision: !ev.why && ev.d > 0, why: ev.why, order: this.trailLength++ });
        this.conflict = null;
        break;
      case "back":
        for (const [v, a] of this.assigned) if (a.level > ev.to) this.assigned.delete(v);
        this.decisions.length = ev.to + 1;
        this.trailLength = this.assigned.size;
        break;
      case "conflict":
        this.conflict = ev.c;
        this.conflicts++;
        break;
      case "learn":
        this.learnts.push({ clause: ev.c, lbd: ev.lbd, back: ev.back, at: this.index });
        break;
      case "restart":
        this.restarts++;
        break;
    }
    this.levels.push(this.level());
    this.index++;
  }

  /** The value of a DIMACS literal: true, false, or undefined when unassigned. */
  value(lit: number): boolean | undefined {
    const a = this.assigned.get(Math.abs(lit));
    if (!a) return undefined;
    return lit > 0 ? a.value : !a.value;
  }
}

/** State after the first n events. */
export function stateAt(events: Event[], n: number): State {
  const s = new State();
  for (let i = 0; i < Math.min(n, events.length); i++) s.apply(events[i]);
  return s;
}

/** Index just past the next event of a given kind after position i (or the end). */
export function nextOf(events: Event[], i: number, kind: Event["e"]): number {
  for (let k = i; k < events.length; k++) if (events[k].e === kind) return k + 1;
  return events.length;
}

/** Hue for a decision level: level 0 is grey (forced), then around the colour wheel. */
export function levelColor(level: number): string {
  if (level === 0) return "hsl(220 10% 55%)";
  return `hsl(${(level * 47) % 360} 70% 45%)`;
}
