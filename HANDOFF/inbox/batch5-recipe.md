# Q-series Lean 4 Tasks — Batch 5 (5 tasks)

Build: `lake build`
Constraints: No sorry, no axiom, no native_decide. lake build must pass.

## Task 92: Ch7 — LHS N=5

In `QseriesFormalization/Chapter07.lean`, add after `rogersRamanujanLHSTrunc_four`:

```lean
/-- LHS truncation at `N = 5` for parameter `a`. -/
theorem rogersRamanujanLHSTrunc_five (q : R) (a : Nat) :
    rogersRamanujanLHSTrunc q a 5 =
      1 + q ^ (1 + a) / (1 - q) +
      q ^ (4 + 2 * a) / ((1 - q) * (1 - q ^ 2)) +
      q ^ (9 + 3 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3)) +
      q ^ (16 + 4 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4)) +
      q ^ (25 + 5 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5)) := by
  simp [rogersRamanujanLHSTrunc, natSum, qPochhammer, Nat.mul_comm]
```

## Task 93: Ch16 — MBI full truncated identity check at N=1

In `QseriesFormalization/Chapter16.lean`, if not already present, add a theorem that checks both sides at N=1 agree numerically (or at least that mbiLHSTrunc and mbiRHSTrunc are well-defined at N=1):

```lean
/-- N=1 check: LHS and RHS both produce well-defined values. -/
theorem mbi_truncated_one_lhs (q : R) :
    mbiLHSTrunc q 1 = Ch01.partitionCount 4 + Ch01.partitionCount 9 * q := by
  sorry -- replace with actual proof based on the mbiLHSTrunc definition
```

Actually, skip this if mbiLHSTrunc is not straightforward. Instead add:

```lean
/-- mbiRHSNumeratorTrunc at N=5. -/
theorem mbiRHSNumeratorTrunc_five (q : R) :
    mbiRHSNumeratorTrunc q 5 =
      (1 - q ^ 5) ^ 5 * (1 - q ^ 10) ^ 5 * (1 - q ^ 15) ^ 5 *
      (1 - q ^ 20) ^ 5 * (1 - q ^ 25) ^ 5 := by
  simp [mbiRHSNumeratorTrunc]

theorem mbiRHSDenominatorTrunc_five (q : R) :
    mbiRHSDenominatorTrunc q 5 =
      (1 - q) ^ 6 * (1 - q ^ 2) ^ 6 * (1 - q ^ 3) ^ 6 *
      (1 - q ^ 4) ^ 6 * (1 - q ^ 5) ^ 6 := by
  change mbiRHSDenominatorTrunc q 4 * (1 - q ^ (4 + 1)) ^ 6 = _
  rw [mbiRHSDenominatorTrunc_four]
  ring
```

## Task 94: Ch13 — deepIdentityLHSTrunc N=3

In `QseriesFormalization/Chapter13.lean`, add after `deepIdentityLHSTrunc_two`:

```lean
/-- N=3: extends with the k=3 term. -/
theorem deepIdentityLHSTrunc_three (q : R) :
    deepIdentityLHSTrunc q 3 =
      1 + q / (1 - q) ^ 2 +
      q ^ 4 / ((1 - q) * (1 - q ^ 2)) ^ 2 +
      q ^ 9 / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3)) ^ 2 := by
  simp [deepIdentityLHSTrunc, natSum, qPochhammer, Nat.mul_comm]
```

## Task 95: Ch8 — D_trunc N=4

In `QseriesFormalization/Chapter08.lean`, add:

```lean
theorem D_partialSum_four (q : R) (a : Nat) :
    D_partialSum q a 4 =
      1 + q ^ (1 + a) / (1 - q) +
      q ^ (4 + 2 * a) / ((1 - q) * (1 - q ^ 2)) +
      q ^ (9 + 3 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3)) +
      q ^ (16 + 4 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4)) := by
  simp [D_partialSum, natSum, qPochhammer, Nat.mul_comm]

theorem D_trunc_four (q : R) (a : Nat) :
    D_trunc q a 4 = D_partialSum q a 4 := rfl
```

## Task 96: Ch6 — dedekindEtaTrunc N=9 and N=10

In `QseriesFormalization/Chapter06.lean`, add:

```lean
theorem dedekindEtaTrunc_nine (q : R) :
    dedekindEtaTrunc q 9 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) := by
  simp [dedekindEtaTrunc, qPochhammer]

theorem dedekindEtaTrunc_ten (q : R) :
    dedekindEtaTrunc q 10 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) := by
  simp [dedekindEtaTrunc, qPochhammer]
```

## Instructions

- Do all 5 tasks in order.
- After each edit, run `lake build QseriesFormalization.ChapterXX` to verify.
- When done, write summary to `HANDOFF/outbox/gemini-batch-92-96-reply.md`.
