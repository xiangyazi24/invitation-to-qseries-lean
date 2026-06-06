# Q-series Lean 4 Tasks — Batch 2 (5 tasks)

Build: `lake build`
Constraints: No sorry, no axiom, no native_decide. lake build must pass.

## Task 77: Ch11 — R_trunc N=2 and N=3

In `QseriesFormalization/Chapter11.lean`, add after `R_trunc_one`:

```lean
theorem R_trunc_two (q : ℂ) : R_trunc q 2 = 1 / (1 + q / (1 + q ^ 2)) := by
  simp [R_trunc, R_trunc_one]
  ring_nf

theorem R_trunc_three (q : ℂ) :
    R_trunc q 3 = 1 / (1 + q / (1 + q ^ 2 / (1 + q ^ 3))) := by
  simp [R_trunc]
  ring_nf
```

Note: `R_trunc` is defined recursively as `1 / (1 + q^(n+1) * R_trunc q n)`. So:
- R_trunc 2 = 1 / (1 + q^2 * R_trunc 1) = 1 / (1 + q^2 * (1/(1+q))) = 1 / (1 + q^2/(1+q))
- R_trunc 3 = 1 / (1 + q^3 * R_trunc 2)

If `ring_nf` alone doesn't close it, try `simp [R_trunc]; ring` or unfold step by step.

## Task 78: Ch7 — LHS N=4

In `QseriesFormalization/Chapter07.lean`, add after `rogersRamanujanLHSTrunc_three`:

```lean
/-- LHS truncation at `N = 4` for parameter `a`. -/
theorem rogersRamanujanLHSTrunc_four (q : R) (a : Nat) :
    rogersRamanujanLHSTrunc q a 4 =
      1 + q ^ (1 + a) / (1 - q) +
      q ^ (4 + 2 * a) / ((1 - q) * (1 - q ^ 2)) +
      q ^ (9 + 3 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3)) +
      q ^ (16 + 4 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4)) := by
  simp [rogersRamanujanLHSTrunc, natSum, qPochhammer, Nat.mul_comm]
```

The exponent pattern is n^2 + a*n: 0, 1+a, 4+2a, 9+3a, 16+4a.

## Task 79: Ch8 — D_trunc N=2

In `QseriesFormalization/Chapter08.lean`, add after `D_trunc_one`:

```lean
/-- N=2 closed form for D_partialSum. -/
theorem D_partialSum_two (q : R) (a : Nat) :
    D_partialSum q a 2 =
      1 + q ^ (1 + a) / (1 - q) +
      q ^ (4 + 2 * a) / ((1 - q) * (1 - q ^ 2)) := by
  simp [D_partialSum, natSum, qPochhammer, Nat.mul_comm]

/-- N=2 closed form for D_trunc. -/
theorem D_trunc_two (q : R) (a : Nat) :
    D_trunc q a 2 =
      1 + q ^ (1 + a) / (1 - q) +
      q ^ (4 + 2 * a) / ((1 - q) * (1 - q ^ 2)) := by
  exact D_partialSum_two q a
```

The n=2 term has exponent n*n + a*n = 4 + 2a, denominator qPochhammer q 2 = (1-q)(1-q^2).

## Task 80: Ch17 — more Ramanujan congruence checks

In `QseriesFormalization/Chapter17.lean`, add more concrete checks using existing partitionCount values:

```lean
/-- p(5*1+4) = p(9) = 30 ≡ 0 (mod 5). Already exists as n_one, add n=2 check. -/
-- p(5*2+4) = p(14) requires partitionCount 14 which doesn't exist yet.
-- Use p(7*1+5) = p(12) ... but we don't have partitionCount 12.
-- So use what we DO have: p(11) = 56 for 7n+5 at n=... no, 7*0+5=5, 7*1+5=12.
-- Available: partitionCount 0..11.
-- p(5*0+4) = p(4) = 5 (done)
-- p(5*1+4) = p(9) = 30 (done)
-- p(7*0+5) = p(5) = 7 (done)
-- p(11*0+6) = p(6) = 11 (done)
-- New: p(11) = 56 = 11*... no, 56/11 = 5.09, not divisible.
-- p(5*0+0) ... let's do a different angle.

/-- Alternate: p(5) = 7 ≡ 2 (mod 5), showing non-congruence for generic n. -/
theorem partition_five_mod_five :
    partitionCount 5 % 5 = 2 := by
  simp [Ch01.partitionCount_five]

/-- p(10) = 42 ≡ 2 (mod 5). -/
theorem partition_ten_mod_five :
    partitionCount 10 % 5 = 2 := by
  simp [Ch01.partitionCount_ten]

/-- p(11) = 56 ≡ 1 (mod 5). -/
theorem partition_eleven_mod_five :
    partitionCount 11 % 5 = 1 := by
  simp [Ch01.partitionCount_eleven]

/-- p(7) = 15 ≡ 1 (mod 7). -/
theorem partition_seven_mod_seven :
    partitionCount 7 % 7 = 1 := by
  simp [Ch01.partitionCount_seven]
```

Adjust exact values if `simp` doesn't close — try `native_decide`... wait, no native_decide. Try `norm_num` or `decide` after `simp`.

Actually, skip this task if partitionCount evaluates are opaque. Replace with:

```lean
/-- p(4) ≡ 0 (mod 5) — restated via Nat.dvd for alternative API. -/
theorem partition_four_dvd_five : 5 ∣ partitionCount 4 := by
  rw [Ch01.partitionCount_four]

/-- p(9) ≡ 0 (mod 5). -/
theorem partition_nine_dvd_five : 5 ∣ partitionCount 9 := by
  rw [Ch01.partitionCount_nine]

/-- p(5) ≡ 0 (mod 7). -/
theorem partition_five_dvd_seven : 7 ∣ partitionCount 5 := by
  rw [Ch01.partitionCount_five]

/-- p(6) ≡ 0 (mod 11). -/
theorem partition_six_dvd_eleven : 11 ∣ partitionCount 6 := by
  rw [Ch01.partitionCount_six]
```

Use whichever form (`%` or `∣`) compiles. The key facts: p(4)=5, p(9)=30, p(5)=7, p(6)=11.

## Task 81: Ch4 — quintuple product N=1

In `QseriesFormalization/Chapter04.lean`, add after `quintupleProduct_truncated_zero`:

```lean
/-- Quintuple product LHS at N=1: one triple of factors. -/
theorem quintupleProductLHSTrunc_one (q z : R) :
    quintupleProductLHSTrunc q z 1 =
      (1 - q ^ 2) * (1 + z * q) * (1 + z⁻¹ * q) *
      (1 - z ^ 2 * q ^ 4) * (1 - z⁻¹ ^ 2 * q ^ 4) := by
  simp [quintupleProductLHSTrunc, qPochhammer]
  ring
```

Check the definition of `quintupleProductLHSTrunc` for the exact unfolding. If the factors don't match, adjust to what the definition actually produces at N=1. The key is getting `lake build` to pass.

## Instructions

- Do all 5 tasks in order.
- After each edit, run `lake build` (or at minimum `lake build QseriesFormalization.ChapterXX`) to verify.
- If a proof doesn't work with the suggested tactic, try alternatives: `unfold` + `simp`, `ring`, `field_simp`, `norm_num`, etc.
- No sorry, no axiom, no native_decide.
- When done, write summary to `HANDOFF/outbox/gemini-batch-77-81-reply.md`.
