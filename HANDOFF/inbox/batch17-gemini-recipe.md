# Batch 17 — Gemini Tasks 152–156

## Build constraint
NEVER run full `lake build`. Always use per-chapter: `lake build QseriesFormalization.ChapterXX`

## Task 152: Ch06 — dedekindEtaTrunc N=25-28

File: `QseriesFormalization/Chapter06.lean`

Add `dedekindEtaTrunc_twentyfive` through `dedekindEtaTrunc_twentyeight`. Follow the exact pattern of existing N=21-24:

```lean
theorem dedekindEtaTrunc_twentyfive (q : R) :
    dedekindEtaTrunc q 25 = dedekindEtaTrunc q 24 * (1 - q ^ 25) := by
  simp [dedekindEtaTrunc]
```

Build: `lake build QseriesFormalization.Chapter06`

## Task 153: Ch04 — quintupleProductLHSTrunc N=4

File: `QseriesFormalization/Chapter04.lean`

Add N=4 following the pattern of N=3:

```lean
theorem quintupleProductLHSTrunc_four (q z : R) :
    quintupleProductLHSTrunc q z 4 =
      quintupleProductLHSTrunc q z 3 *
      (1 - q ^ 8) * (1 - z * q ^ 7) * (1 - z⁻¹ * q ^ 7) * (1 - z ^ 2 * q ^ 12) * (1 - z⁻¹ ^ 2 * q ^ 16) := by
  simp [quintupleProductLHSTrunc]
```

**Check:** The factor pattern for N=k uses `q^{2k}, z*q^{2k-1}, z⁻¹*q^{2k-1}, z²*q^{4k-4}, z⁻²*q^{4k}`. Double-check the exponents by looking at the definition. If `simp` alone doesn't work, add `ring` or `norm_num`.

Build: `lake build QseriesFormalization.Chapter04`

## Task 154: Ch16 — MBI N=13-14

File: `QseriesFormalization/Chapter16.lean`

Add numerator and denominator for N=13 and N=14.

Numerator pattern (uses `simp [mbiRHSNumeratorTrunc]`):
```lean
theorem mbiRHSNumeratorTrunc_thirteen (q : R) :
    mbiRHSNumeratorTrunc q 13 =
      (1 - q ^ 5) ^ 5 * (1 - q ^ 10) ^ 5 * ... * (1 - q ^ 65) ^ 5 := by
  simp [mbiRHSNumeratorTrunc]
```

Denominator pattern (chain from previous):
```lean
theorem mbiRHSDenominatorTrunc_thirteen (q : R) :
    mbiRHSDenominatorTrunc q 13 =
      (1 - q) ^ 6 * (1 - q ^ 2) ^ 6 * ... * (1 - q ^ 13) ^ 6 := by
  change mbiRHSDenominatorTrunc q 12 * (1 - q ^ (12 + 1)) ^ 6 = _
  rw [mbiRHSDenominatorTrunc_twelve]
```

Build: `lake build QseriesFormalization.Chapter16`

## Task 155: Ch20 — etaPolyPart/discriminantPolyPart N=13-14

File: `QseriesFormalization/Chapter20.lean`

Add eta N=13-14 and corresponding discriminant:
```lean
theorem etaPolyPart_thirteen (q : R) :
    etaPolyPart q 13 = (1 - q) * (1 - q^2) * ... * (1 - q^13) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_thirteen (q : R) :
    discriminantPolyPart q 13 = q * ((1 - q) * ... * (1 - q^13))^24 := by
  rw [discriminantPolyPart, etaPolyPart_thirteen]
```

Build: `lake build QseriesFormalization.Chapter20`

## Task 156: Ch05 — four-particle states

File: `QseriesFormalization/Chapter05.lean`

Check if three-particle state theorems exist. If so, add four-particle state theorems following the same pattern. The charge and energy functions should extend naturally. Look at the existing patterns and add the next level.

Build: `lake build QseriesFormalization.Chapter05`

---

Write your reply to `HANDOFF/outbox/gemini-batch-152-156-reply.md`.
