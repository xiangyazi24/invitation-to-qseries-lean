# Q-series Lean 4 Tasks — Batch 8 (5 tasks)

Build: `lake build`
Constraints: No sorry, no axiom, no native_decide. lake build must pass.

## Task 107: Ch11 — R_trunc N=4

In `QseriesFormalization/Chapter11.lean`, add after `R_trunc_three`:

```lean
theorem R_trunc_four (q : ℂ) :
    R_trunc q 4 = 1 / (1 + q ^ 4 / (1 + q ^ 3 / (1 + q ^ 2 / (1 + q)))) := by
  simp [R_trunc]
  field_simp
```

## Task 108: Ch11 — α_pow_eight and β_pow_seven (Fibonacci pattern)

In `QseriesFormalization/Chapter11.lean`, add after `β_pow_six`:

```lean
theorem α_pow_eight : α ^ 8 = 21 * α + 13 := by
  have h7 := α_pow_seven
  have hsq := α_sq
  nlinarith [sq_nonneg α]

theorem β_pow_seven : β ^ 7 = 13 * β + 8 := by
  have := β_sq
  have := β_cubed
  have := β_pow_six
  nlinarith [sq_nonneg β]
```

## Task 109: Ch04 — eulerPentagonalSeriesTrunc N=3

In `QseriesFormalization/Chapter04.lean`, add after `eulerPentagonalSeriesTrunc_two`. Check the definition of `eulerPentagonalSeriesTrunc` and compute at N=3.

The pentagonal series terms use generalized pentagonal numbers: 0, 1, 2, 5, 7, 12, 15, ...
At N=3 the series includes terms for k = -1, 0, 1 (bilateral) or k = 0, 1, 2 (one-sided) depending on definition.

Look at the existing `eulerPentagonalSeriesTrunc_two` to understand the pattern and extend it.

```lean
theorem eulerPentagonalSeriesTrunc_three (q : R) :
    eulerPentagonalSeriesTrunc q 3 = 1 - q - q ^ 2 + q ^ 5 + q ^ 7 - q ^ 12 := by
  simp [eulerPentagonalSeriesTrunc, triangular, bilateralSum]
  ring
```

Adjust the RHS based on what the definition actually produces at N=3.

## Task 110: Ch06 — dedekindEtaTrunc N=11 and N=12

In `QseriesFormalization/Chapter06.lean`, add after `dedekindEtaTrunc_ten`:

```lean
theorem dedekindEtaTrunc_eleven (q : R) :
    dedekindEtaTrunc q 11 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) * (1 - q ^ 11) := by
  simp [dedekindEtaTrunc, qPochhammer]

theorem dedekindEtaTrunc_twelve (q : R) :
    dedekindEtaTrunc q 12 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
      (1 - q ^ 11) * (1 - q ^ 12) := by
  simp [dedekindEtaTrunc, qPochhammer]
```

## Task 111: Ch18 — tCoreDenominatorTrunc N=2 and tCoreRatioTrunc sanity

In `QseriesFormalization/Chapter18.lean`, add after `tCoreDenominatorTrunc_one`:

```lean
theorem tCoreDenominatorTrunc_two (q : R) :
    tCoreDenominatorTrunc q 2 = (1 - q) * (1 - q ^ 2) := by
  simp [tCoreDenominatorTrunc, qPochhammer]

theorem tCoreDenominatorTrunc_three (q : R) :
    tCoreDenominatorTrunc q 3 = (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) := by
  simp [tCoreDenominatorTrunc, qPochhammer]

theorem tCoreRatioTrunc_zero (t : Nat) (q : R) :
    tCoreRatioTrunc t q 0 = 1 := by
  simp [tCoreRatioTrunc, tCoreNumeratorTrunc, tCoreDenominatorTrunc]
```

## Instructions

- Do all 5 tasks in order.
- After each edit, run `lake build QseriesFormalization.ChapterXX` to verify.
- If a proof doesn't work, try alternatives (unfold, ring, field_simp, norm_num, nlinarith).
- When done, write summary to `HANDOFF/outbox/gemini-batch-107-111-reply.md`.
