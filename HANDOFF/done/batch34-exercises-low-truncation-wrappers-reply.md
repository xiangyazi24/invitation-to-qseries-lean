# Batch 34: Exercises — low truncation wrappers - Reply

## Goal

Add wrappers for these already-proved facts in `QseriesFormalization/Exercises.lean`:

Chapter 6:
- `PartI.Ch06.dedekindEtaTrunc_three`
- `PartI.Ch06.dedekindEtaTrunc_four`

Chapter 8:
- `PartII.Ch08.D_partialSum_two`
- `PartII.Ch08.D_trunc_two`

Chapter 10:
- `PartII.Ch10.ramanujanMockF_trunc_two`

## Declarations Added

The following declarations were added to `QseriesFormalization/Exercises.lean`:

```lean
-- Section Chapter6Exercises
theorem exercise6_dedekindEtaTrunc_three (q : R) :
    PartI.Ch06.dedekindEtaTrunc q 3 = (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) :=
  PartI.Ch06.dedekindEtaTrunc_three q

theorem exercise6_dedekindEtaTrunc_four (q : R) :
    PartI.Ch06.dedekindEtaTrunc q 4 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) :=
  PartI.Ch06.dedekindEtaTrunc_four q

-- Section Chapter8Exercises
theorem exercise8_D_partialSum_two (q : R) (a : Nat) :
    PartII.Ch08.D_partialSum q a 2 =
      1 + q ^ (1 + a) / (1 - q) +
      q ^ (4 + 2 * a) / ((1 - q) * (1 - q ^ 2)) :=
  PartII.Ch08.D_partialSum_two q a

theorem exercise8_D_trunc_two (q : R) (a : Nat) :
    PartII.Ch08.D_trunc q a 2 =
      1 + q ^ (1 + a) / (1 - q) +
      q ^ (4 + 2 * a) / ((1 - q) * (1 - q ^ 2)) :=
  PartII.Ch08.D_trunc_two q a

-- Section Chapter10Exercises
theorem exercise10_ramanujanMockF_trunc_two (q : R) :
    PartII.Ch10.ramanujanMockF_trunc q 2 =
      1 + q / (1 + q) ^ 2 + q ^ 4 / ((1 + q) ^ 2 * (1 + q ^ 2) ^ 2) :=
  PartII.Ch10.ramanujanMockF_trunc_two q
```

## Build Result

Successfully built `QseriesFormalization.Exercises`:

```bash
lake build QseriesFormalization.Exercises
# ⚠ [7887/7906] Replayed QseriesFormalization.Chapter02
# warning: QseriesFormalization/Chapter02.lean:98:8: declaration uses 'sorry'
# Build completed successfully (7906 jobs).
```

## Forbidden-Token Check Result

Checked for `sorry`, `axiom`, and `native_decide` in `QseriesFormalization/Exercises.lean`:

```bash
rg -n "sorry|axiom|native_decide" QseriesFormalization/Exercises.lean
# (empty)
```
No forbidden tokens found.
