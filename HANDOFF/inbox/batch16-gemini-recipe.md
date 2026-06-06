# Q-series Lean 4 Tasks — Batch 16 Gemini (5 tasks)

Build: `lake build QseriesFormalization.ChapterXX` (NOT full `lake build` — Chapter01 takes 20+ min)
Constraints: No sorry, no axiom, no native_decide. lake build must pass.

## Task 147: Ch06 — dedekindEtaTrunc N=21-24

In `QseriesFormalization/Chapter06.lean`, add after `dedekindEtaTrunc_twenty`:

```lean
theorem dedekindEtaTrunc_twentyone (q : R) :
    dedekindEtaTrunc q 21 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
      (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) *
      (1 - q ^ 16) * (1 - q ^ 17) * (1 - q ^ 18) * (1 - q ^ 19) * (1 - q ^ 20) * (1 - q ^ 21) := by
  simp [dedekindEtaTrunc, qPochhammer]

theorem dedekindEtaTrunc_twentytwo (q : R) :
    dedekindEtaTrunc q 22 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
      (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) *
      (1 - q ^ 16) * (1 - q ^ 17) * (1 - q ^ 18) * (1 - q ^ 19) * (1 - q ^ 20) *
      (1 - q ^ 21) * (1 - q ^ 22) := by
  simp [dedekindEtaTrunc, qPochhammer]

theorem dedekindEtaTrunc_twentythree (q : R) :
    dedekindEtaTrunc q 23 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
      (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) *
      (1 - q ^ 16) * (1 - q ^ 17) * (1 - q ^ 18) * (1 - q ^ 19) * (1 - q ^ 20) *
      (1 - q ^ 21) * (1 - q ^ 22) * (1 - q ^ 23) := by
  simp [dedekindEtaTrunc, qPochhammer]

theorem dedekindEtaTrunc_twentyfour (q : R) :
    dedekindEtaTrunc q 24 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
      (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) *
      (1 - q ^ 16) * (1 - q ^ 17) * (1 - q ^ 18) * (1 - q ^ 19) * (1 - q ^ 20) *
      (1 - q ^ 21) * (1 - q ^ 22) * (1 - q ^ 23) * (1 - q ^ 24) := by
  simp [dedekindEtaTrunc, qPochhammer]
```

Verify: `lake build QseriesFormalization.Chapter06`

## Task 148: Ch18 — tCoreNumeratorTrunc N=9, tCoreDenominatorTrunc N=9

In `QseriesFormalization/Chapter18.lean`, add after existing N=8 theorems:

```lean
theorem tCoreNumeratorTrunc_nine (t : Nat) (q : R) :
    tCoreNumeratorTrunc t q 9 =
      (1 - q^t)^t * (1 - q^(2*t))^t * (1 - q^(3*t))^t *
      (1 - q^(4*t))^t * (1 - q^(5*t))^t * (1 - q^(6*t))^t *
      (1 - q^(7*t))^t * (1 - q^(8*t))^t * (1 - q^(9*t))^t := by
  simp [tCoreNumeratorTrunc, Nat.mul_comm]

theorem tCoreDenominatorTrunc_nine (q : R) :
    tCoreDenominatorTrunc q 9 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) := by
  simp [tCoreDenominatorTrunc, qPochhammer]
```

Verify: `lake build QseriesFormalization.Chapter18`

## Task 149: Ch20 — etaPolyPart/discriminantPolyPart N=11-12

In `QseriesFormalization/Chapter20.lean`, add after the N=10 theorems:

```lean
theorem etaPolyPart_eleven (q : R) :
    etaPolyPart q 11 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) * (1 - q^11) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_eleven (q : R) :
    discriminantPolyPart q 11 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) * (1 - q^11))^24 := by
  rw [discriminantPolyPart, etaPolyPart_eleven]

theorem etaPolyPart_twelve (q : R) :
    etaPolyPart q 12 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) * (1 - q^11) * (1 - q^12) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_twelve (q : R) :
    discriminantPolyPart q 12 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) * (1 - q^11) * (1 - q^12))^24 := by
  rw [discriminantPolyPart, etaPolyPart_twelve]
```

Verify: `lake build QseriesFormalization.Chapter20`

## Task 150: Ch14 — crankGenNumerator N=7-8, crankGenDenominator N=5

In `QseriesFormalization/Chapter14.lean`, add before `end Field`:

```lean
theorem crankGenNumeratorTrunc_seven (q : R) :
    crankGenNumeratorTrunc q 7 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) := by
  simp [crankGenNumeratorTrunc, qPochhammer]

theorem crankGenNumeratorTrunc_eight (q : R) :
    crankGenNumeratorTrunc q 8 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) := by
  simp [crankGenNumeratorTrunc, qPochhammer]

theorem crankGenDenominatorTrunc_five (z q : R) :
    crankGenDenominatorTrunc z q 5 =
      ((1 - z * q) * (1 - z * q ^ 2) * (1 - z * q ^ 3) * (1 - z * q ^ 4) * (1 - z * q ^ 5)) *
      ((1 - z⁻¹ * q) * (1 - z⁻¹ * q ^ 2) * (1 - z⁻¹ * q ^ 3) * (1 - z⁻¹ * q ^ 4) * (1 - z⁻¹ * q ^ 5)) := by
  simp [crankGenDenominatorTrunc, qPoch]
  ring
```

Verify: `lake build QseriesFormalization.Chapter14`

## Task 151: Ch04 — quintupleProductLHSTrunc N=3

In `QseriesFormalization/Chapter04.lean`, add after `quintupleProductLHSTrunc_two`:

```lean
/-- Quintuple product LHS at N=3. -/
theorem quintupleProductLHSTrunc_three (q z : R) :
    quintupleProductLHSTrunc q z 3 =
      (1 - q ^ 2) * (1 - z * q) * (1 - z⁻¹ * q) * (1 - z ^ 2) * (1 - z⁻¹ ^ 2 * q ^ 4) *
      (1 - q ^ 4) * (1 - z * q ^ 3) * (1 - z⁻¹ * q ^ 3) * (1 - z ^ 2 * q ^ 4) * (1 - z⁻¹ ^ 2 * q ^ 8) *
      (1 - q ^ 6) * (1 - z * q ^ 5) * (1 - z⁻¹ * q ^ 5) * (1 - z ^ 2 * q ^ 8) * (1 - z⁻¹ ^ 2 * q ^ 12) := by
  simp [quintupleProductLHSTrunc]
```

Verify: `lake build QseriesFormalization.Chapter04`

## Instructions

- Do all 5 tasks in order.
- After each edit, run `lake build QseriesFormalization.ChapterXX` to verify the SPECIFIC module.
- Do NOT run full `lake build`.
- When done, write summary to `HANDOFF/outbox/gemini-batch-147-151-reply.md`.
