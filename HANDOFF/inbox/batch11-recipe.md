# Q-series Lean 4 Tasks — Batch 11 (5 tasks)

Build: `lake build QseriesFormalization.ChapterXX` (NOT full `lake build` — Chapter01 takes 20+ min)
Constraints: No sorry, no axiom, no native_decide. lake build must pass.

## Task 122: Ch07 — rogersRamanujanLHSTrunc N=7

In `QseriesFormalization/Chapter07.lean`, add after `rogersRamanujanLHSTrunc_six`:

```lean
/-- LHS truncation at `N = 7` for parameter `a`. -/
theorem rogersRamanujanLHSTrunc_seven (q : R) (a : Nat) :
    rogersRamanujanLHSTrunc q a 7 =
      1 + q ^ (1 + a) / (1 - q) +
      q ^ (4 + 2 * a) / ((1 - q) * (1 - q ^ 2)) +
      q ^ (9 + 3 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3)) +
      q ^ (16 + 4 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4)) +
      q ^ (25 + 5 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5)) +
      q ^ (36 + 6 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6)) +
      q ^ (49 + 7 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7)) := by
  simp [rogersRamanujanLHSTrunc, natSum, qPochhammer, Nat.mul_comm]
```

## Task 123: Ch11 — R_trunc N=5

```lean
theorem R_trunc_five (q : ℂ) :
    R_trunc q 5 = 1 / (1 + q ^ 5 / (1 + q ^ 4 / (1 + q ^ 3 / (1 + q ^ 2 / (1 + q))))) := by
  simp [R_trunc]
  field_simp
```

## Task 124: Ch16 — mbiRHS N=7

```lean
theorem mbiRHSNumeratorTrunc_seven (q : R) :
    mbiRHSNumeratorTrunc q 7 =
      (1 - q ^ 5) ^ 5 * (1 - q ^ 10) ^ 5 * (1 - q ^ 15) ^ 5 *
      (1 - q ^ 20) ^ 5 * (1 - q ^ 25) ^ 5 * (1 - q ^ 30) ^ 5 * (1 - q ^ 35) ^ 5 := by
  simp [mbiRHSNumeratorTrunc]

theorem mbiRHSDenominatorTrunc_seven (q : R) :
    mbiRHSDenominatorTrunc q 7 =
      (1 - q) ^ 6 * (1 - q ^ 2) ^ 6 * (1 - q ^ 3) ^ 6 *
      (1 - q ^ 4) ^ 6 * (1 - q ^ 5) ^ 6 * (1 - q ^ 6) ^ 6 * (1 - q ^ 7) ^ 6 := by
  change mbiRHSDenominatorTrunc q 6 * (1 - q ^ (6 + 1)) ^ 6 = _
  rw [mbiRHSDenominatorTrunc_six]
  ring
```

## Task 125: Ch10 — ramanujanMockF_trunc N=6

```lean
theorem ramanujanMockF_trunc_six (q : R) :
    ramanujanMockF_trunc q 6 =
      1 + q / (1 + q)^2 + q^4 / ((1 + q)^2 * (1 + q^2)^2) +
      q^9 / ((1 + q) * (1 + q^2) * (1 + q^3))^2 +
      q^16 / ((1 + q) * (1 + q^2) * (1 + q^3) * (1 + q^4))^2 +
      q^25 / ((1 + q) * (1 + q^2) * (1 + q^3) * (1 + q^4) * (1 + q^5))^2 +
      q^36 / ((1 + q) * (1 + q^2) * (1 + q^3) * (1 + q^4) * (1 + q^5) * (1 + q^6))^2 := by
  simp [ramanujanMockF_trunc, natSum, qPoch]
  ring_nf
```

## Task 126: Ch13 — deepIdentityLHSTrunc N=6

```lean
theorem deepIdentityLHSTrunc_six (q : R) :
    deepIdentityLHSTrunc q 6 =
      1 + q / (1 - q) ^ 2 +
      q ^ 4 / ((1 - q) * (1 - q ^ 2)) ^ 2 +
      q ^ 9 / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3)) ^ 2 +
      q ^ 16 / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4)) ^ 2 +
      q ^ 25 / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5)) ^ 2 +
      q ^ 36 / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6)) ^ 2 := by
  simp [deepIdentityLHSTrunc, natSum, qPochhammer, Nat.mul_comm]
```

## Instructions

- Do all 5 tasks in order.
- After each edit, run `lake build QseriesFormalization.ChapterXX` to verify the SPECIFIC module.
- Do NOT run full `lake build` — Chapter01 takes 20+ minutes and is not needed.
- When done, write summary to `HANDOFF/outbox/gemini-batch-122-126-reply.md`.
