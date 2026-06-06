# Q-series Lean 4 Tasks — Batch 14 Gemini (5 tasks)

Build: `lake build QseriesFormalization.ChapterXX` (NOT full `lake build` — Chapter01 takes 20+ min)
Constraints: No sorry, no axiom, no native_decide. lake build must pass.

## Task 137: Ch18 — tCoreNumeratorTrunc N=8

In `QseriesFormalization/Chapter18.lean`, add after `tCoreNumeratorTrunc_seven`:

```lean
theorem tCoreNumeratorTrunc_eight (t : Nat) (q : R) :
    tCoreNumeratorTrunc t q 8 =
      (1 - q^t)^t * (1 - q^(2*t))^t * (1 - q^(3*t))^t *
      (1 - q^(4*t))^t * (1 - q^(5*t))^t * (1 - q^(6*t))^t *
      (1 - q^(7*t))^t * (1 - q^(8*t))^t := by
  simp [tCoreNumeratorTrunc, Nat.mul_comm]
```

Verify: `lake build QseriesFormalization.Chapter18`

## Task 138: Ch20 — etaPolyPart/discriminantPolyPart N=9

In `QseriesFormalization/Chapter20.lean`, add after `discriminantPolyPart_eight`:

```lean
theorem etaPolyPart_nine (q : R) :
    etaPolyPart q 9 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_nine (q : R) :
    discriminantPolyPart q 9 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9))^24 := by
  rw [discriminantPolyPart, etaPolyPart_nine]
```

Verify: `lake build QseriesFormalization.Chapter20`

## Task 139: Ch17 — More partition congruences

In `QseriesFormalization/Chapter17.lean`, add at the end (before `end Ch17`):

```lean
/-- p(7) ≡ 0 (mod 3): p(7) = 15 = 5·3. -/
theorem partition_seven_dvd_three : 3 ∣ partitionCount 7 := by
  simp [Ch01.partitionCount_seven]

/-- p(8) ≡ 0 (mod 11): p(8) = 22 = 2·11. -/
theorem partition_eight_dvd_eleven : 11 ∣ partitionCount 8 := by
  simp [Ch01.partitionCount_eight]

/-- p(10) ≡ 0 (mod 2): p(10) = 42. -/
theorem partition_ten_dvd_two : 2 ∣ partitionCount 10 := by
  simp [Ch01.partitionCount_ten]

/-- p(10) ≡ 0 (mod 3): p(10) = 42 = 14·3. -/
theorem partition_ten_dvd_three : 3 ∣ partitionCount 10 := by
  simp [Ch01.partitionCount_ten]

/-- p(10) ≡ 0 (mod 14): p(10) = 42 = 3·14. -/
theorem partition_ten_dvd_fourteen : 14 ∣ partitionCount 10 := by
  simp [Ch01.partitionCount_ten]

/-- p(10) ≡ 0 (mod 21): p(10) = 42 = 2·21. -/
theorem partition_ten_dvd_twentyone : 21 ∣ partitionCount 10 := by
  simp [Ch01.partitionCount_ten]
```

Verify: `lake build QseriesFormalization.Chapter17`

## Task 140: Ch12 — R_trunc more levels

In `QseriesFormalization/Chapter12.lean`, add before `end Ch12`:

```lean
/-- R_trunc at N=2 matches the nested continued fraction. -/
theorem R_trunc_two_eq (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 2 =
      1 / (1 + q ^ 2 / (1 + q)) :=
  QseriesFormalization.PartIII.Ch11.R_trunc_two q

/-- R_trunc at N=3. -/
theorem R_trunc_three_eq (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 3 =
      1 / (1 + q ^ 3 / (1 + q ^ 2 / (1 + q))) :=
  QseriesFormalization.PartIII.Ch11.R_trunc_three q
```

Verify: `lake build QseriesFormalization.Chapter12`

## Task 141: Ch04 — eulerPentagonalProductTrunc N=6

In `QseriesFormalization/Chapter04.lean`, look for the last `eulerPentagonalProductTrunc` theorem and add the next level. The pattern is:

```lean
-- Find the definition of eulerPentagonalProductTrunc and add N=6
-- The proof pattern is: simp [eulerPentagonalProductTrunc, qPochhammer]
```

If `eulerPentagonalProductTrunc_five` already exists, add `_six`. If the definition uses a different name, grep for it and follow the pattern. Verify: `lake build QseriesFormalization.Chapter04`

## Instructions

- Do all 5 tasks in order.
- After each edit, run `lake build QseriesFormalization.ChapterXX` to verify the SPECIFIC module.
- Do NOT run full `lake build`.
- When done, write summary to `HANDOFF/outbox/gemini-batch-137-141-reply.md`.
