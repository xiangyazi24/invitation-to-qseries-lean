# Task 49: Ch20 — etaPolyPart / discriminant properties

## Goal

In `Chapter20.lean` (current state has etaPolyPart and
discriminantPolyPart):

Add these:

```lean
theorem etaPolyPart_one (q : R) :
    etaPolyPart q 1 = 1 - q := by
  simp [etaPolyPart, qPochhammer]; ring

theorem discriminantPolyPart_zero (q : R) :
    discriminantPolyPart q 0 = q := by
  simp [discriminantPolyPart, etaPolyPart]

theorem discriminantPolyPart_one (q : R) :
    discriminantPolyPart q 1 = q * (1 - q) ^ 24 := by
  simp [discriminantPolyPart, etaPolyPart, qPochhammer]; ring
```

Touch only `Chapter20.lean`. No axiom/sorry/native_decide. lake build clean.

## Deliverable

Modified file + reply.
