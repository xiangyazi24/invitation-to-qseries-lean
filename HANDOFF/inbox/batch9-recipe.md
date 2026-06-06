# Q-series Lean 4 Tasks — Batch 9 (5 tasks)

Build: `lake build`
Constraints: No sorry, no axiom, no native_decide. lake build must pass.

## Task 112: Ch07 — rogersRamanujanLHSTrunc N=6

In `QseriesFormalization/Chapter07.lean`, add after `rogersRamanujanLHSTrunc_five`:

```lean
/-- LHS truncation at `N = 6` for parameter `a`. -/
theorem rogersRamanujanLHSTrunc_six (q : R) (a : Nat) :
    rogersRamanujanLHSTrunc q a 6 =
      1 + q ^ (1 + a) / (1 - q) +
      q ^ (4 + 2 * a) / ((1 - q) * (1 - q ^ 2)) +
      q ^ (9 + 3 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3)) +
      q ^ (16 + 4 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4)) +
      q ^ (25 + 5 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5)) +
      q ^ (36 + 6 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6)) := by
  simp [rogersRamanujanLHSTrunc, natSum, qPochhammer, Nat.mul_comm]
```

## Task 113: Ch10 — ramanujanMockF_trunc N=5

In `QseriesFormalization/Chapter10.lean`, add after `ramanujanMockF_trunc_four`:

```lean
/-- N=5: the first six terms of Ramanujan's mock theta `f(q)`. -/
theorem ramanujanMockF_trunc_five (q : R) :
    ramanujanMockF_trunc q 5 =
      1 + q / (1 + q)^2 + q^4 / ((1 + q)^2 * (1 + q^2)^2) +
      q^9 / ((1 + q) * (1 + q^2) * (1 + q^3))^2 +
      q^16 / ((1 + q) * (1 + q^2) * (1 + q^3) * (1 + q^4))^2 +
      q^25 / ((1 + q) * (1 + q^2) * (1 + q^3) * (1 + q^4) * (1 + q^5))^2 := by
  simp [ramanujanMockF_trunc, natSum, qPoch]
  ring_nf
```

## Task 114: Ch13 — deepIdentityLHSTrunc N=5

In `QseriesFormalization/Chapter13.lean`, add after `deepIdentityLHSTrunc_four`:

```lean
/-- N=5: extends with the k=5 term. -/
theorem deepIdentityLHSTrunc_five (q : R) :
    deepIdentityLHSTrunc q 5 =
      1 + q / (1 - q) ^ 2 +
      q ^ 4 / ((1 - q) * (1 - q ^ 2)) ^ 2 +
      q ^ 9 / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3)) ^ 2 +
      q ^ 16 / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4)) ^ 2 +
      q ^ 25 / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5)) ^ 2 := by
  simp [deepIdentityLHSTrunc, natSum, qPochhammer, Nat.mul_comm]
```

## Task 115: Ch20 — discriminantPolyPart N=4

In `QseriesFormalization/Chapter20.lean`, add after `discriminantPolyPart_three`. First add the helper:

```lean
/-- Sanity: η_poly q 4 = (1 - q)(1 - q^2)(1 - q^3)(1 - q^4). -/
theorem etaPolyPart_four (q : R) :
    etaPolyPart q 4 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) := by
  simp [etaPolyPart, qPochhammer]

/-- Sanity: Δ_poly q 4 = q((1 - q)(1 - q^2)(1 - q^3)(1 - q^4))^24. -/
theorem discriminantPolyPart_four (q : R) :
    discriminantPolyPart q 4 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4))^24 := by
  rw [discriminantPolyPart, etaPolyPart_four]
```

## Task 116: Ch16 — mbiRHSNumeratorTrunc N=6

In `QseriesFormalization/Chapter16.lean`, add after `mbiRHSNumeratorTrunc_five`:

```lean
theorem mbiRHSNumeratorTrunc_six (q : R) :
    mbiRHSNumeratorTrunc q 6 =
      (1 - q ^ 5) ^ 5 * (1 - q ^ 10) ^ 5 * (1 - q ^ 15) ^ 5 *
      (1 - q ^ 20) ^ 5 * (1 - q ^ 25) ^ 5 * (1 - q ^ 30) ^ 5 := by
  simp [mbiRHSNumeratorTrunc]

theorem mbiRHSDenominatorTrunc_six (q : R) :
    mbiRHSDenominatorTrunc q 6 =
      (1 - q) ^ 6 * (1 - q ^ 2) ^ 6 * (1 - q ^ 3) ^ 6 *
      (1 - q ^ 4) ^ 6 * (1 - q ^ 5) ^ 6 * (1 - q ^ 6) ^ 6 := by
  change mbiRHSDenominatorTrunc q 5 * (1 - q ^ (5 + 1)) ^ 6 = _
  rw [mbiRHSDenominatorTrunc_five]
  ring
```

## Instructions

- Do all 5 tasks in order.
- After each edit, run `lake build QseriesFormalization.ChapterXX` to verify.
- If a proof doesn't work, try alternatives (unfold, ring, field_simp, norm_num, nlinarith).
- When done, write summary to `HANDOFF/outbox/gemini-batch-112-116-reply.md`.
