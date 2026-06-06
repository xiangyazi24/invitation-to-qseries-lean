# Q-series Lean 4 Tasks — Batch 6 (5 tasks)

Build: `lake build`
Constraints: No sorry, no axiom, no native_decide. lake build must pass.

## Task 97: Ch10 — ramanujanMockF_trunc N=4

In `QseriesFormalization/Chapter10.lean`, add after `ramanujanMockF_trunc_three`:

```lean
/-- N=4: the first five terms of Ramanujan's mock theta `f(q)`. -/
theorem ramanujanMockF_trunc_four (q : R) :
    ramanujanMockF_trunc q 4 =
      1 + q / (1 + q)^2 + q^4 / ((1 + q)^2 * (1 + q^2)^2) +
      q^9 / ((1 + q) * (1 + q^2) * (1 + q^3))^2 +
      q^16 / ((1 + q) * (1 + q^2) * (1 + q^3) * (1 + q^4))^2 := by
  simp [ramanujanMockF_trunc, natSum, qPoch]
  ring_nf
```

## Task 98: Ch18 — tCoreNumeratorTrunc N=2 and N=3

In `QseriesFormalization/Chapter18.lean`, add after `tCoreNumeratorTrunc_one`:

```lean
theorem tCoreNumeratorTrunc_two (t : Nat) (q : R) :
    tCoreNumeratorTrunc t q 2 = (1 - q^t)^t * (1 - q^(2*t))^t := by
  simp [tCoreNumeratorTrunc]

theorem tCoreNumeratorTrunc_three (t : Nat) (q : R) :
    tCoreNumeratorTrunc t q 3 =
      (1 - q^t)^t * (1 - q^(2*t))^t * (1 - q^(3*t))^t := by
  simp [tCoreNumeratorTrunc]
```

## Task 99: Ch20 — discriminantPolyPart N=3

In `QseriesFormalization/Chapter20.lean`, add after `discriminantPolyPart_two`:

```lean
/-- Sanity: Δ_poly q 3 = q((1 - q)(1 - q^2)(1 - q^3))^24. -/
theorem discriminantPolyPart_three (q : R) :
    discriminantPolyPart q 3 = q * ((1 - q) * (1 - q^2) * (1 - q^3))^24 := by
  rw [discriminantPolyPart]
  congr 1
  simp [etaPolyPart, qPochhammer]
```

## Task 100: Ch09 — BaileyBeta_trivial at n=2

In `QseriesFormalization/Chapter09.lean`, add after `BaileyBeta_trivial_succ`:

```lean
/-- Trivial Bailey pair α = δ_0: the n = 2 beta value. -/
theorem BaileyBeta_trivial_two (a q : R) :
    BaileyBeta a q (fun k => if k = 0 then 1 else 0) 2 =
      1 / ((1 - q) * (1 - q ^ 2) * (1 - a * q) * (1 - a * q ^ 2)) := by
  simp [BaileyBeta, natSum, BaileyTerm, qPochhammer, qPoch]
  ring
```

Note: If `ring` alone doesn't close, try `field_simp` then `ring`. Check the actual BaileyTerm definition and adjust the expected RHS.

## Task 101: Ch11 — α_pow_seven and β_pow_six

In `QseriesFormalization/Chapter11.lean`, add after `β_pow_five`:

```lean
theorem α_pow_seven : α ^ 7 = 13 * α + 8 := by
  have h6 := α_pow_six
  have hsq := α_sq
  nlinarith [sq_nonneg α]

theorem β_pow_six : β ^ 6 = 8 * β + 5 := by
  have := β_sq
  have := β_cubed
  have := β_pow_five
  nlinarith [sq_nonneg β]
```

## Instructions

- Do all 5 tasks in order.
- After each edit, run `lake build QseriesFormalization.ChapterXX` to verify.
- If a proof doesn't work, try alternatives (unfold, ring, field_simp, norm_num, nlinarith).
- When done, write summary to `HANDOFF/outbox/gemini-batch-97-101-reply.md`.
