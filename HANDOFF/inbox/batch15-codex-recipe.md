# Q-series Lean 4 Tasks — Batch 15 Codex (5 tasks)

Build: `lake build QseriesFormalization.ChapterXX` (NOT full `lake build` — Chapter01 takes 20+ min)
Constraints: No sorry, no axiom, no native_decide. lake build must pass.

## Task C15-1: Ch11 — G_trunc/H_trunc N=6 and R_trunc N=6

In `QseriesFormalization/Chapter11.lean`, add before `end Ch11`:

For G/H N=6, the simp/field_simp approach will timeout. Use the one-step unfold pattern:

```lean
theorem G_trunc_six (q : ℂ) :
    G_trunc q 6 = G_trunc q 5 / ((1 - q ^ 26) * (1 - q ^ 29)) := by
  show G_trunc q 5 / ((1 - q ^ (5 * (5 + 1) - 4)) * (1 - q ^ (5 * (5 + 1) - 1))) =
       G_trunc q 5 / ((1 - q ^ 26) * (1 - q ^ 29))
  norm_num

theorem H_trunc_six (q : ℂ) :
    H_trunc q 6 = H_trunc q 5 / ((1 - q ^ 27) * (1 - q ^ 28)) := by
  show H_trunc q 5 / ((1 - q ^ (5 * (5 + 1) - 3)) * (1 - q ^ (5 * (5 + 1) - 2))) =
       H_trunc q 5 / ((1 - q ^ 27) * (1 - q ^ 28))
  norm_num

theorem R_trunc_six (q : ℂ) :
    R_trunc q 6 =
      1 / (1 + q ^ 6 / (1 + q ^ 5 / (1 + q ^ 4 / (1 + q ^ 3 / (1 + q ^ 2 / (1 + q)))))) := by
  simp [R_trunc]
  field_simp
```

Verify: `lake build QseriesFormalization.Chapter11`

## Task C15-2: Ch09 — BaileyBeta_trivial_seven

In `QseriesFormalization/Chapter09.lean`, add after `BaileyBeta_trivial_six`:

```lean
/-- Trivial Bailey pair α = δ_0: the n = 7 beta value. -/
theorem BaileyBeta_trivial_seven (a q : R) :
    BaileyBeta a q (fun k => if k = 0 then 1 else 0) 7 =
      1 / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) *
           (1 - a * q) * (1 - a * q ^ 2) * (1 - a * q ^ 3) * (1 - a * q ^ 4) * (1 - a * q ^ 5) * (1 - a * q ^ 6) * (1 - a * q ^ 7)) := by
  simp [BaileyBeta, natSum, BaileyTerm, qPochhammer, qPoch]
  ring
```

Verify: `lake build QseriesFormalization.Chapter09`

## Task C15-3: Ch16 — MBI N=9

In `QseriesFormalization/Chapter16.lean`, find the last `mbiNumeratorTrunc` and `mbiDenominatorTrunc` theorems and add N=9:

```lean
theorem mbiNumeratorTrunc_nine (q : R) :
    mbiNumeratorTrunc q 9 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) := by
  simp [mbiNumeratorTrunc, qPochhammer]

theorem mbiDenominatorTrunc_nine (z q : R) :
    mbiDenominatorTrunc z q 9 =
      (1 - z * q) * (1 - z * q ^ 2) * (1 - z * q ^ 3) * (1 - z * q ^ 4) * (1 - z * q ^ 5) *
      (1 - z * q ^ 6) * (1 - z * q ^ 7) * (1 - z * q ^ 8) * (1 - z * q ^ 9) *
      (1 - z⁻¹ * q) * (1 - z⁻¹ * q ^ 2) * (1 - z⁻¹ * q ^ 3) * (1 - z⁻¹ * q ^ 4) * (1 - z⁻¹ * q ^ 5) *
      (1 - z⁻¹ * q ^ 6) * (1 - z⁻¹ * q ^ 7) * (1 - z⁻¹ * q ^ 8) * (1 - z⁻¹ * q ^ 9) := by
  simp [mbiDenominatorTrunc, qPoch]
  ring
```

Verify: `lake build QseriesFormalization.Chapter16`

## Task C15-4: Ch18 — tCoreDenominatorTrunc N=8

In `QseriesFormalization/Chapter18.lean`, find `tCoreDenominatorTrunc_seven` and add:

```lean
theorem tCoreDenominatorTrunc_eight (q : R) :
    tCoreDenominatorTrunc q 8 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) := by
  simp [tCoreDenominatorTrunc, qPochhammer]
```

Verify: `lake build QseriesFormalization.Chapter18`

## Task C15-5: Ch20 — etaPolyPart/discriminantPolyPart N=10

In `QseriesFormalization/Chapter20.lean`, add after the N=9 theorems:

```lean
theorem etaPolyPart_ten (q : R) :
    etaPolyPart q 10 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_ten (q : R) :
    discriminantPolyPart q 10 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10))^24 := by
  rw [discriminantPolyPart, etaPolyPart_ten]
```

Verify: `lake build QseriesFormalization.Chapter20`

## Instructions

- Do all 5 tasks in order.
- After each edit, run `lake build QseriesFormalization.ChapterXX` to verify the SPECIFIC module.
- Do NOT run full `lake build`.
- When done, write summary to `HANDOFF/outbox/codex-batch-C15-reply.md`.
