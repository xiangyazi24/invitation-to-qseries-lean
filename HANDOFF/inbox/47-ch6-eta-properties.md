# Task 47: Ch6 — dedekindEta truncation properties

## Goal

In `Chapter06.lean` (current state has dedekindEtaTrunc + zero + succ):

Add these:

```lean
theorem dedekindEtaTrunc_one (q : R) : dedekindEtaTrunc q 1 = 1 - q := by
  simp [dedekindEtaTrunc, qPochhammer]; ring

theorem dedekindEtaTrunc_two (q : R) :
    dedekindEtaTrunc q 2 = (1 - q) * (1 - q ^ 2) := by
  simp [dedekindEtaTrunc, qPochhammer]; ring

theorem dedekindEtaTrunc_three (q : R) :
    dedekindEtaTrunc q 3 = (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) := by
  simp [dedekindEtaTrunc, qPochhammer]; ring
```

Touch only `Chapter06.lean`. No axiom/sorry/native_decide. lake build clean.

## Deliverable

Modified file + reply.
