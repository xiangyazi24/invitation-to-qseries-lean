# Q-series Lean 4 Tasks — Batch 10 (5 tasks)

Build: `lake build`
Constraints: No sorry, no axiom, no native_decide. lake build must pass.

## Task 117: Ch11 — G_trunc N=3 and H_trunc N=3

In `QseriesFormalization/Chapter11.lean`, add after `H_trunc_two`:

```lean
theorem G_trunc_three (q : ℂ) :
    G_trunc q 3 = G_trunc q 2 * (1 / ((1 - q ^ 11) * (1 - q ^ 14))) := by
  simp [G_trunc]

theorem H_trunc_three (q : ℂ) :
    H_trunc q 3 = H_trunc q 2 * (1 / ((1 - q ^ 12) * (1 - q ^ 13))) := by
  simp [H_trunc]
```

Check the G_trunc/H_trunc definitions — at N=3 they should add factors (1-q^{5*3-4})(1-q^{5*3-1}) = (1-q^11)(1-q^14) for G, and (1-q^{5*3-3})(1-q^{5*3-2}) = (1-q^12)(1-q^13) for H. Adjust the form to match the actual definition (product vs ratio).

## Task 118: Ch11 — α_pow_nine and α_pow_ten (Fibonacci)

```lean
theorem α_pow_nine : α ^ 9 = 34 * α + 21 := by
  calc
    α ^ 9 = α ^ 8 + α ^ 7 := by simpa using α_recurrence 7
    _ = 34 * α + 21 := by nlinarith [α_pow_eight, α_pow_seven]

theorem α_pow_ten : α ^ 10 = 55 * α + 34 := by
  calc
    α ^ 10 = α ^ 9 + α ^ 8 := by simpa using α_recurrence 8
    _ = 55 * α + 34 := by nlinarith [α_pow_nine, α_pow_eight]
```

## Task 119: Ch08 — D_partialSum N=6

```lean
theorem D_partialSum_six (q : R) (a : Nat) :
    D_partialSum q a 6 =
      1 + q ^ (1 + a) / (1 - q) +
      q ^ (4 + 2 * a) / ((1 - q) * (1 - q ^ 2)) +
      q ^ (9 + 3 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3)) +
      q ^ (16 + 4 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4)) +
      q ^ (25 + 5 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5)) +
      q ^ (36 + 6 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6)) := by
  simp [D_partialSum, natSum, qPochhammer, Nat.mul_comm]

theorem D_trunc_six (q : R) (a : Nat) :
    D_trunc q a 6 = D_partialSum q a 6 := rfl
```

## Task 120: Ch18 — tCoreNumeratorTrunc N=4 and N=5

```lean
theorem tCoreNumeratorTrunc_four (t : Nat) (q : R) :
    tCoreNumeratorTrunc t q 4 =
      (1 - q^t)^t * (1 - q^(2*t))^t * (1 - q^(3*t))^t * (1 - q^(4*t))^t := by
  simp [tCoreNumeratorTrunc, Nat.mul_comm]

theorem tCoreNumeratorTrunc_five (t : Nat) (q : R) :
    tCoreNumeratorTrunc t q 5 =
      (1 - q^t)^t * (1 - q^(2*t))^t * (1 - q^(3*t))^t * (1 - q^(4*t))^t * (1 - q^(5*t))^t := by
  simp [tCoreNumeratorTrunc, Nat.mul_comm]
```

## Task 121: Ch06 — dedekindEtaTrunc N=13 through N=15

```lean
theorem dedekindEtaTrunc_thirteen (q : R) :
    dedekindEtaTrunc q 13 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
      (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) := by
  simp [dedekindEtaTrunc, qPochhammer]

theorem dedekindEtaTrunc_fourteen (q : R) :
    dedekindEtaTrunc q 14 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
      (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) := by
  simp [dedekindEtaTrunc, qPochhammer]

theorem dedekindEtaTrunc_fifteen (q : R) :
    dedekindEtaTrunc q 15 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
      (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) := by
  simp [dedekindEtaTrunc, qPochhammer]
```

## Instructions

- Do all 5 tasks in order.
- After each edit, run `lake build QseriesFormalization.ChapterXX` to verify the SPECIFIC module (not full `lake build` — Chapter01 takes too long).
- If a proof doesn't work, try alternatives (unfold, ring, field_simp, norm_num, nlinarith).
- When done, write summary to `HANDOFF/outbox/gemini-batch-117-121-reply.md`.
