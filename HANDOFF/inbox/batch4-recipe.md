# Q-series Lean 4 Tasks — Batch 4 (5 tasks)

Build: `lake build`
Constraints: No sorry, no axiom, no native_decide. lake build must pass.

## Task 87: Ch7 — RHS N=4 (both a=0 and a=1)

In `QseriesFormalization/Chapter07.lean`, add RHS N=4.

For a=0, N=4: new factors at n=3 are (1 - q^(5*4-1-0)) * (1 - q^(5*4-4+0)) = (1 - q^19) * (1 - q^16).
For a=1, N=4: new factors at n=3 are (1 - q^(5*4-1-1)) * (1 - q^(5*4-4+1)) = (1 - q^18) * (1 - q^17).

```lean
/-- RHS truncation at `N = 4` for parameter `a = 0`. -/
theorem rogersRamanujanRHSTrunc_four_a0 (q : R)
    (h1 : (1 - q) ≠ 0) (h4 : (1 - q ^ 4) ≠ 0)
    (h6 : (1 - q ^ 6) ≠ 0) (h9 : (1 - q ^ 9) ≠ 0)
    (h11 : (1 - q ^ 11) ≠ 0) (h14 : (1 - q ^ 14) ≠ 0)
    (h16 : (1 - q ^ 16) ≠ 0) (h19 : (1 - q ^ 19) ≠ 0) :
    rogersRamanujanRHSTrunc q 0 4 =
      1 / ((1 - q ^ 19) * (1 - q ^ 16) * (1 - q ^ 14) * (1 - q ^ 11) *
           (1 - q ^ 9) * (1 - q ^ 6) * (1 - q ^ 4) * (1 - q)) := by
  simp [rogersRamanujanRHSTrunc]
  field_simp [h1, h4, h6, h9, h11, h14, h16, h19]

/-- RHS truncation at `N = 4` for parameter `a = 1`. -/
theorem rogersRamanujanRHSTrunc_four_a1 (q : R)
    (h2 : (1 - q ^ 2) ≠ 0) (h3 : (1 - q ^ 3) ≠ 0)
    (h7 : (1 - q ^ 7) ≠ 0) (h8 : (1 - q ^ 8) ≠ 0)
    (h12 : (1 - q ^ 12) ≠ 0) (h13 : (1 - q ^ 13) ≠ 0)
    (h17 : (1 - q ^ 17) ≠ 0) (h18 : (1 - q ^ 18) ≠ 0) :
    rogersRamanujanRHSTrunc q 1 4 =
      1 / ((1 - q ^ 18) * (1 - q ^ 17) * (1 - q ^ 13) * (1 - q ^ 12) *
           (1 - q ^ 8) * (1 - q ^ 7) * (1 - q ^ 3) * (1 - q ^ 2)) := by
  simp [rogersRamanujanRHSTrunc]
  field_simp [h2, h3, h7, h8, h12, h13, h17, h18]
```

## Task 88: Ch16 — MBI LHS and RHS at N=4

In `QseriesFormalization/Chapter16.lean`, extend both sides to N=4:

```lean
theorem mbiRHSNumeratorTrunc_four (q : R) :
    mbiRHSNumeratorTrunc q 4 =
      (1 - q ^ 5) ^ 5 * (1 - q ^ 10) ^ 5 * (1 - q ^ 15) ^ 5 * (1 - q ^ 20) ^ 5 := by
  simp [mbiRHSNumeratorTrunc]

theorem mbiRHSDenominatorTrunc_four (q : R) :
    mbiRHSDenominatorTrunc q 4 =
      (1 - q) ^ 6 * (1 - q ^ 2) ^ 6 * (1 - q ^ 3) ^ 6 * (1 - q ^ 4) ^ 6 := by
  change mbiRHSDenominatorTrunc q 3 * (1 - q ^ (3 + 1)) ^ 6 =
    (1 - q) ^ 6 * (1 - q ^ 2) ^ 6 * (1 - q ^ 3) ^ 6 * (1 - q ^ 4) ^ 6
  rw [mbiRHSDenominatorTrunc_three]
```

## Task 89: Ch11 — α and β higher powers

In `QseriesFormalization/Chapter11.lean`, add after `α_pow_five`:

```lean
theorem α_pow_six : α ^ 6 = 8 * α + 5 := by
  have h5 := α_pow_five
  have hsq := α_sq
  nlinarith [sq_nonneg α]

theorem β_pow_four : β ^ 4 = 3 * β + 2 := by
  have := β_sq
  nlinarith [sq_nonneg β]

theorem β_pow_five : β ^ 5 = 5 * β + 3 := by
  have := β_sq
  have := β_cubed
  nlinarith [sq_nonneg β]
```

Use nlinarith or ring_nf with the recurrence. Adjust if needed.

## Task 90: Ch3 — qPochhammer higher N values

In `QseriesFormalization/Chapter03.lean` (or Basic.lean if qPochhammer is there), add explicit evaluations:

Look at what `qPochhammer` evaluations are available. Add:

```lean
theorem qPochhammer_three (q : R) :
    qPochhammer q 3 = (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) := by
  simp [qPochhammer]

theorem qPochhammer_four (q : R) :
    qPochhammer q 4 = (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) := by
  simp [qPochhammer]
```

Check if these already exist in Basic.lean. If so, add N=5 and N=6 instead.

## Task 91: Ch10 — mock theta truncation N=3

In `QseriesFormalization/Chapter10.lean`, extend the mock theta stub. Check the current definitions and add the next N level.

Look at the existing definitions (f_mock_trunc or similar), compute at N=3, and prove it equals the expected closed form.

## Instructions

- Do all 5 tasks in order.
- After each edit, run `lake build QseriesFormalization.ChapterXX` to verify.
- If a proof doesn't work, try alternatives.
- When done, write summary to `HANDOFF/outbox/gemini-batch-87-91-reply.md`.
