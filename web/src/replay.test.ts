import { describe, expect, it } from "vitest";
import { type Event, levelColor, nextOf, stateAt } from "./replay";

// x1 forced at level 0; decide -2; 3 implied; conflict; learn (2) and jump back to 0.
const events: Event[] = [
  { e: "a", l: 1, d: 0 },
  { e: "decide", l: -2, level: 1 },
  { e: "a", l: -2, d: 1 },
  { e: "a", l: 3, d: 1, why: [3, 2] },
  { e: "conflict", c: [-3, 2, -1] },
  { e: "back", to: 0 },
  { e: "learn", c: [2], lbd: 1, back: 0 },
  { e: "a", l: 2, d: 0 },
  { e: "restart" },
];

describe("replay", () => {
  it("tracks assignments, levels and decisions", () => {
    const s = stateAt(events, 4);
    expect(s.level()).toBe(1);
    expect(s.value(1)).toBe(true);
    expect(s.value(-2)).toBe(true);
    expect(s.value(3)).toBe(true);
    expect(s.assigned.get(2)!.decision).toBe(true);
    expect(s.assigned.get(3)!.why).toEqual([3, 2]);
    expect(s.decisionCount).toBe(1);
  });
  it("backjumps, learns and continues", () => {
    const s = stateAt(events, events.length);
    expect(s.level()).toBe(0);
    expect(s.value(3)).toBeUndefined();
    expect(s.value(2)).toBe(true);
    expect(s.conflicts).toBe(1);
    expect(s.learnts).toEqual([{ clause: [2], lbd: 1, back: 0, at: 6 }]);
    expect(s.restarts).toBe(1);
    expect(s.levels).toEqual([0, 1, 1, 1, 1, 0, 0, 0, 0]);
  });
  it("keeps the conflict until the next assignment", () => {
    expect(stateAt(events, 5).conflict).toEqual([-3, 2, -1]);
    expect(stateAt(events, 8).conflict).toBeNull();
  });
  it("finds the next event of a kind", () => {
    expect(nextOf(events, 0, "conflict")).toBe(5);
    expect(nextOf(events, 5, "conflict")).toBe(events.length);
  });
  it("colours level 0 grey and others distinctly", () => {
    expect(levelColor(0)).toContain("10%");
    expect(levelColor(1)).not.toBe(levelColor(2));
  });
});
