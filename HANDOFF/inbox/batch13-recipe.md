# Q-series Lean 4 Tasks — Batch 13 (5 tasks)

Build: `lake build QseriesFormalization.ChapterXX` (NOT full `lake build` — Chapter01 takes 20+ min)
Constraints: No sorry, no axiom, no native_decide. lake build must pass.

## Task 132: Ch06 — dedekindEtaTrunc N=16,17,18

In `QseriesFormalization/Chapter06.lean`, add after `dedekindEtaTrunc_fifteen`:

```lean
theorem dedekindEtaTrunc_sixteen (q : R) :
    dedekindEtaTrunc q 16 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
      (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) * (1 - q ^ 16) := by
  simp [dedekindEtaTrunc, qPochhammer]

theorem dedekindEtaTrunc_seventeen (q : R) :
    dedekindEtaTrunc q 17 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
      (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) *
      (1 - q ^ 16) * (1 - q ^ 17) := by
  simp [dedekindEtaTrunc, qPochhammer]

theorem dedekindEtaTrunc_eighteen (q : R) :
    dedekindEtaTrunc q 18 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
      (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) *
      (1 - q ^ 16) * (1 - q ^ 17) * (1 - q ^ 18) := by
  simp [dedekindEtaTrunc, qPochhammer]
```

## Task 133: Ch18 — tCoreDenominatorTrunc N=4,5,6 and tCoreRatioTrunc N=1

In `QseriesFormalization/Chapter18.lean`, add after `tCoreRatioTrunc_zero`:

```lean
theorem tCoreDenominatorTrunc_four (q : R) :
    tCoreDenominatorTrunc q 4 = (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) := by
  simp [tCoreDenominatorTrunc, qPochhammer]

theorem tCoreDenominatorTrunc_five (q : R) :
    tCoreDenominatorTrunc q 5 = (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) := by
  simp [tCoreDenominatorTrunc, qPochhammer]

theorem tCoreDenominatorTrunc_six (q : R) :
    tCoreDenominatorTrunc q 6 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) := by
  simp [tCoreDenominatorTrunc, qPochhammer]

theorem tCoreRatioTrunc_one (t : Nat) (q : R) :
    tCoreRatioTrunc t q 1 = (1 - q^t)^t / (1 - q) := by
  simp [tCoreRatioTrunc, tCoreNumeratorTrunc, tCoreDenominatorTrunc, qPochhammer]
```

## Task 134: Ch20 — etaPolyPart N=6,7 and discriminantPolyPart N=6

In `QseriesFormalization/Chapter20.lean`, add after `discriminantPolyPart_five`:

```lean
theorem etaPolyPart_six (q : R) :
    etaPolyPart q 6 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) * (1 - q^6) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_six (q : R) :
    discriminantPolyPart q 6 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) * (1 - q^6))^24 := by
  rw [discriminantPolyPart, etaPolyPart_six]

theorem etaPolyPart_seven (q : R) :
    etaPolyPart q 7 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) * (1 - q^6) * (1 - q^7) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_seven (q : R) :
    discriminantPolyPart q 7 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) * (1 - q^6) * (1 - q^7))^24 := by
  rw [discriminantPolyPart, etaPolyPart_seven]
```

## Task 135: Ch05 — charge and energy additivity for disjoint states

In `QseriesFormalization/Chapter05.lean`, add before `end Ch05`:

```lean
/-- Charge of a state with both added and removed levels equals the difference. -/
theorem charge_pair (a r : Nat) :
    charge ⟨{a}, {r}⟩ = 0 := by
  simp [charge]

/-- Energy of a balanced pair: one added level k₁ and one removed level k₂. -/
theorem energy_pair (k₁ k₂ : Nat) :
    energy ⟨{k₁}, {k₂}⟩ = k₁ + 1 + (k₂ + 1) := by
  simp [energy]

/-- Energy of two added levels (disjoint). -/
theorem energy_add_two (a b : Nat) (hab : a ≠ b) :
    energy ⟨{a, b}, ∅⟩ = a + 1 + (b + 1) := by
  simp [energy, Finset.sum_pair hab]

/-- Charge of two added levels is 2. -/
theorem charge_add_two (a b : Nat) (hab : a ≠ b) :
    charge ⟨{a, b}, ∅⟩ = 2 := by
  simp [charge, Finset.card_pair hab]
```

## Task 136: Ch04 — eulerPentagonalProductTrunc N=4,5

In `QseriesFormalization/Chapter04.lean`, add after `eulerPentagonalProductTrunc_three`:

```lean
theorem eulerPentagonalProductTrunc_four (q : R) :
    eulerPentagonalProductTrunc q 4 = (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) := by
  simp [eulerPentagonalProductTrunc, qPochhammer]

theorem eulerPentagonalProductTrunc_five (q : R) :
    eulerPentagonalProductTrunc q 5 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) := by
  simp [eulerPentagonalProductTrunc, qPochhammer]
```

## Instructions

- Do all 5 tasks in order.
- After each edit, run `lake build QseriesFormalization.ChapterXX` to verify the SPECIFIC module.
- Do NOT run full `lake build` — Chapter01 takes 20+ minutes and is not needed.
- If a proof doesn't work, try alternatives (unfold, ring, field_simp, norm_num, nlinarith, omega).
- When done, write summary to `HANDOFF/outbox/batch13-recipe-reply.md`.
