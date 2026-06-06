# Q-series Lean 4 Tasks — Batch 12 (5 tasks)

Build: `lake build QseriesFormalization.ChapterXX` (NOT full `lake build` — Chapter01 takes 20+ min)
Constraints: No sorry, no axiom, no native_decide. lake build must pass.

## Task 127: Ch09 — BaileyBeta_trivial_four

In `QseriesFormalization/Chapter09.lean`, add after `BaileyBeta_trivial_three`:

```lean
/-- Trivial Bailey pair α = δ_0: the n = 4 beta value. -/
theorem BaileyBeta_trivial_four (a q : R) :
    BaileyBeta a q (fun k => if k = 0 then 1 else 0) 4 =
      1 / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) *
           (1 - a * q) * (1 - a * q ^ 2) * (1 - a * q ^ 3) * (1 - a * q ^ 4)) := by
  simp [BaileyBeta, natSum, BaileyTerm, qPochhammer, qPoch]
  ring
```

## Task 128: Ch11 — G_trunc N=4, H_trunc N=4

In `QseriesFormalization/Chapter11.lean`, add after `H_trunc_three`:

```lean
theorem G_trunc_four (q : ℂ) :
    G_trunc q 4 = G_trunc q 3 * (1 / ((1 - q ^ 16) * (1 - q ^ 19))) := by
  simp [G_trunc]
  field_simp
  ring_nf

theorem H_trunc_four (q : ℂ) :
    H_trunc q 4 = H_trunc q 3 * (1 / ((1 - q ^ 17) * (1 - q ^ 18))) := by
  simp [H_trunc]
  field_simp
  ring_nf
```

## Task 129: Ch18 — tCoreNumeratorTrunc N=6

In `QseriesFormalization/Chapter18.lean`, add after `tCoreNumeratorTrunc_five`:

```lean
theorem tCoreNumeratorTrunc_six (t : Nat) (q : R) :
    tCoreNumeratorTrunc t q 6 =
      (1 - q^t)^t * (1 - q^(2*t))^t * (1 - q^(3*t))^t *
      (1 - q^(4*t))^t * (1 - q^(5*t))^t * (1 - q^(6*t))^t := by
  simp [tCoreNumeratorTrunc, Nat.mul_comm]
```

## Task 130: Ch20 — etaPolyPart N=5, discriminantPolyPart N=5

In `QseriesFormalization/Chapter20.lean`, add after `discriminantPolyPart_four`:

```lean
theorem etaPolyPart_five (q : R) :
    etaPolyPart q 5 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_five (q : R) :
    discriminantPolyPart q 5 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5))^24 := by
  rw [discriminantPolyPart, etaPolyPart_five]
```

## Task 131: Ch17 — p(14) mod 7

In `QseriesFormalization/Chapter17.lean`, add at the end (before `end Ch17`):

```lean
/-- p(5*2+4) = p(14) = 135 ≡ 0 (mod 5): 135 = 27·5. -/
theorem partition_5n_plus_4_mod_5_n_two :
    partitionCount (5 * 2 + 4) % 5 = 0 := by
  simp [Ch01.partitionCount_fourteen]
```

(This requires `partitionCount_fourteen` to exist in Ch01. If it doesn't, use `native_decide` — oh wait, can't. Skip this task if `partitionCount_fourteen` is unavailable, and instead add:)

```lean
/-- p(7) ≡ 0 (mod 5): p(7) = 15 = 3·5. -/
theorem partition_seven_dvd_five : 5 ∣ partitionCount 7 := by
  simp [Ch01.partitionCount_seven]

/-- p(8) ≡ 0 (mod 2): p(8) = 22 = 11·2. -/
theorem partition_eight_dvd_two : 2 ∣ partitionCount 8 := by
  simp [Ch01.partitionCount_eight]
```

## Instructions

- Do all 5 tasks in order.
- After each edit, run `lake build QseriesFormalization.ChapterXX` to verify the SPECIFIC module.
- Do NOT run full `lake build` — Chapter01 takes 20+ minutes and is not needed.
- When done, write summary to `HANDOFF/outbox/gemini-batch-127-131-reply.md`.
