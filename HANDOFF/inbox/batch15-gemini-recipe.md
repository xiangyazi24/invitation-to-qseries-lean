# Q-series Lean 4 Tasks — Batch 15 Gemini (5 tasks)

Build: `lake build QseriesFormalization.ChapterXX` (NOT full `lake build` — Chapter01 takes 20+ min)
Constraints: No sorry, no axiom, no native_decide. lake build must pass.

## Task 142: Ch14 — Crank denominator N=3, numerator N=4/5

In `QseriesFormalization/Chapter14.lean`, add after `crankGenNumeratorTrunc_three`:

```lean
theorem crankGenDenominatorTrunc_three (z q : R) :
    crankGenDenominatorTrunc z q 3 =
      ((1 - z * q) * (1 - z * q ^ 2) * (1 - z * q ^ 3)) *
      ((1 - z⁻¹ * q) * (1 - z⁻¹ * q ^ 2) * (1 - z⁻¹ * q ^ 3)) := by
  simp [crankGenDenominatorTrunc, qPoch]
  ring

theorem crankGenNumeratorTrunc_four (q : R) :
    crankGenNumeratorTrunc q 4 = (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) := by
  simp [crankGenNumeratorTrunc, qPochhammer]

theorem crankGenNumeratorTrunc_five (q : R) :
    crankGenNumeratorTrunc q 5 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) := by
  simp [crankGenNumeratorTrunc, qPochhammer]
```

Verify: `lake build QseriesFormalization.Chapter14`

## Task 143: Ch15 — More R_trunc nesting levels

In `QseriesFormalization/Chapter15.lean`, add before `end Field`:

```lean
theorem R_trunc_nesting_three (q : ℂ) :
    Ch11.R_trunc q 3 = 1 / (1 + q ^ 3 * Ch11.R_trunc q 2) := by
  simp [Ch11.R_trunc]

theorem R_trunc_nesting_four (q : ℂ) :
    Ch11.R_trunc q 4 = 1 / (1 + q ^ 4 * Ch11.R_trunc q 3) := by
  simp [Ch11.R_trunc]

theorem R_trunc_nesting_five (q : ℂ) :
    Ch11.R_trunc q 5 = 1 / (1 + q ^ 5 * Ch11.R_trunc q 4) := by
  simp [Ch11.R_trunc]
```

Verify: `lake build QseriesFormalization.Chapter15`

## Task 144: Ch05 — Three-particle states

In `QseriesFormalization/Chapter05.lean`, add before `end Ch05`:

```lean
/-- Three particles added at levels 0, 1, 2: charge = 3, energy = 6. -/
theorem charge_three_particles :
    charge ⟨{0, 1, 2}, ∅⟩ = 3 := by
  simp [charge]

theorem energy_three_particles :
    energy ⟨{0, 1, 2}, ∅⟩ = 6 := by
  simp [energy]

/-- A balanced two-pair state: add 0,1 and remove 0,1. Charge = 0, energy = 6. -/
theorem charge_balanced_two (hab : (0 : Nat) ≠ 1) :
    charge ⟨{0, 1}, {0, 1}⟩ = 0 := by
  simp [charge, Finset.card_pair hab]

theorem energy_balanced_two (hab : (0 : Nat) ≠ 1) :
    energy ⟨{0, 1}, {0, 1}⟩ = 6 := by
  simp [energy, Finset.sum_pair hab]
```

Verify: `lake build QseriesFormalization.Chapter05`

## Task 145: Ch19 — More partition mod checks

In `QseriesFormalization/Chapter19.lean`, add before `end Ch19`:

```lean
/-- p(0) = 1, so p(0) mod 5 = 1. -/
theorem p0_mod_5 : partitionCount 0 % 5 = 1 := by
  simp [Ch01.partitionCount_zero]

/-- p(1) = 1, so p(1) mod 5 = 1. -/
theorem p1_mod_5 : partitionCount 1 % 5 = 1 := by
  simp [Ch01.partitionCount_one]

/-- p(2) = 2, so p(2) mod 5 = 2. -/
theorem p2_mod_5 : partitionCount 2 % 5 = 2 := by
  simp [Ch01.partitionCount_two]

/-- p(3) = 3, so p(3) mod 5 = 3. -/
theorem p3_mod_5 : partitionCount 3 % 5 = 3 := by
  simp [Ch01.partitionCount_three]

/-- p(7) = 15 ≡ 0 (mod 5). -/
theorem p7_dvd_5 : 5 ∣ partitionCount 7 := by
  simp [Ch01.partitionCount_seven]
```

Verify: `lake build QseriesFormalization.Chapter19`

## Task 146: Ch12 — R_trunc_four/five_eq

In `QseriesFormalization/Chapter12.lean`, add before `end Ch12`:

```lean
/-- R_trunc at N=4. -/
theorem R_trunc_four_eq (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 4 =
      1 / (1 + q ^ 4 / (1 + q ^ 3 / (1 + q ^ 2 / (1 + q)))) :=
  QseriesFormalization.PartIII.Ch11.R_trunc_four q

/-- R_trunc at N=5. -/
theorem R_trunc_five_eq (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 5 =
      1 / (1 + q ^ 5 / (1 + q ^ 4 / (1 + q ^ 3 / (1 + q ^ 2 / (1 + q))))) :=
  QseriesFormalization.PartIII.Ch11.R_trunc_five q
```

Verify: `lake build QseriesFormalization.Chapter12`

## Instructions

- Do all 5 tasks in order.
- After each edit, run `lake build QseriesFormalization.ChapterXX` to verify the SPECIFIC module.
- Do NOT run full `lake build`.
- When done, write summary to `HANDOFF/outbox/gemini-batch-142-146-reply.md`.
