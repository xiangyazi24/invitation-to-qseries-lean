# Q-series Lean 4 Tasks — Batch 7 (5 tasks)

Build: `lake build`
Constraints: No sorry, no axiom, no native_decide. lake build must pass.

## Task 102: Basic — qPochhammer N=5 and N=6

In `QseriesFormalization/Basic.lean`, add after `qPochhammer_four`:

```lean
theorem qPochhammer_five (q : R) :
    qPochhammer q 5 = (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) := by
  simp [qPochhammer]

theorem qPochhammer_six (q : R) :
    qPochhammer q 6 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) := by
  simp [qPochhammer]
```

## Task 103: Ch17 — More Ramanujan congruence checks

In `QseriesFormalization/Chapter17.lean`, add more divisibility checks. We know p(14) = 135 and 135 = 27*5 so 5 | p(14). Also p(12) = 77 and 77 = 7*11, so 7 | p(12) is FALSE (77/7=11, wait 77=7*11 yes). Actually p(12) = 77. 7 | 77? 77 = 7*11. Yes!

Check: we need partitionCount_twelve and beyond. Since Ch01 only goes to partitionCount_eleven, we need to add partitionCount_twelve first.

Actually, skip the ones needing new partition values. Instead add:

```lean
/-- p(14) ≡ 0 (mod 5): p(14) = 135 = 27·5. -/
theorem partition_fourteen_dvd_five : 5 ∣ partitionCount 14 := by
  native_decide
```

Wait, no native_decide! Instead check if we can compute partitionCount 14 from the definition.

**Alternative approach**: Add a simpler theorem. p(5*2+4) = p(14). We need partitionCount 14 computed.

Actually, let's just add more congruence checks for values we already have:
- p(4) = 5, so 5 | p(4) ✓ (already have)
- p(9) = 30, so 5 | p(9) ✓ (already have)
- p(5) = 7, so 7 | p(5) ✓ (already have)
- p(6) = 11, so 11 | p(6) ✓ (already have)

Add compound checks:

```lean
/-- p(9) ≡ 0 (mod 10): p(9) = 30. -/
theorem partition_nine_dvd_ten : 10 ∣ partitionCount 9 := by
  simp [Ch01.partitionCount_nine]

/-- p(9) ≡ 0 (mod 15): p(9) = 30. -/
theorem partition_nine_dvd_fifteen : 15 ∣ partitionCount 9 := by
  simp [Ch01.partitionCount_nine]

/-- p(10) ≡ 0 (mod 7): p(10) = 42 = 6·7. -/
theorem partition_ten_dvd_seven : 7 ∣ partitionCount 10 := by
  simp [Ch01.partitionCount_ten]
```

## Task 104: Ch04 — quintupleProductLHSTrunc N=2

In `QseriesFormalization/Chapter04.lean`, add after `quintupleProductLHSTrunc_one`:

```lean
/-- Quintuple product LHS at N=2. -/
theorem quintupleProductLHSTrunc_two (q z : R) :
    quintupleProductLHSTrunc q z 2 =
      (1 - q ^ 2) * (1 - z * q) * (1 - z⁻¹ * q) * (1 - z ^ 2) * (1 - z⁻¹ ^ 2 * q ^ 4) *
      (1 - q ^ 4) * (1 - z * q ^ 3) * (1 - z⁻¹ * q ^ 3) * (1 - z ^ 2 * q ^ 2) * (1 - z⁻¹ ^ 2 * q ^ 6) := by
  simp [quintupleProductLHSTrunc]
```

Check the definition of quintupleProductLHSTrunc to get the exact factors. Adjust the RHS to match.

## Task 105: Ch13 — deepIdentityLHSTrunc N=4

In `QseriesFormalization/Chapter13.lean`, add after `deepIdentityLHSTrunc_three`:

```lean
/-- N=4: extends with the k=4 term. -/
theorem deepIdentityLHSTrunc_four (q : R) :
    deepIdentityLHSTrunc q 4 =
      1 + q / (1 - q) ^ 2 +
      q ^ 4 / ((1 - q) * (1 - q ^ 2)) ^ 2 +
      q ^ 9 / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3)) ^ 2 +
      q ^ 16 / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4)) ^ 2 := by
  simp [deepIdentityLHSTrunc, natSum, qPochhammer, Nat.mul_comm]
```

## Task 106: Ch08 — D_partialSum N=5

In `QseriesFormalization/Chapter08.lean`, add after `D_trunc_four`:

```lean
/-- N=5 closed form for D_partialSum. -/
theorem D_partialSum_five (q : R) (a : Nat) :
    D_partialSum q a 5 =
      1 + q ^ (1 + a) / (1 - q) +
      q ^ (4 + 2 * a) / ((1 - q) * (1 - q ^ 2)) +
      q ^ (9 + 3 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3)) +
      q ^ (16 + 4 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4)) +
      q ^ (25 + 5 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5)) := by
  simp [D_partialSum, natSum, qPochhammer, Nat.mul_comm]

/-- N=5 closed form for D_trunc. -/
theorem D_trunc_five (q : R) (a : Nat) :
    D_trunc q a 5 = D_partialSum q a 5 := rfl
```

## Instructions

- Do all 5 tasks in order.
- After each edit, run `lake build QseriesFormalization.ChapterXX` to verify.
- If a proof doesn't work, try alternatives (unfold, ring, field_simp, norm_num, nlinarith).
- When done, write summary to `HANDOFF/outbox/gemini-batch-102-106-reply.md`.
