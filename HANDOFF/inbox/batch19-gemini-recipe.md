# Batch 19 — Tasks 162-166

## Task 162: Ch06 — dedekindEtaTrunc N=33-36

File: `QseriesFormalization/Chapter06.lean`

Add `dedekindEtaTrunc_thirtythree` through `dedekindEtaTrunc_thirtysix`.

Pattern (same as existing):
```lean
theorem dedekindEtaTrunc_thirtythree (q : R) :
    dedekindEtaTrunc q 33 = dedekindEtaTrunc q 32 * (1 - q ^ 33) := by
  simp [dedekindEtaTrunc]
```

Build: `lake build QseriesFormalization.Chapter06`

## Task 163: Ch04 — quintupleProductLHSTrunc N=5

File: `QseriesFormalization/Chapter04.lean`

Add `quintupleProductLHSTrunc_five`. Follow the recursive pattern from N=4.

Build: `lake build QseriesFormalization.Chapter04`

## Task 164: Ch16 — MBI numerator/denominator N=17-18

File: `QseriesFormalization/Chapter16.lean`

Add `mbiRHSNumeratorTrunc_seventeen/eighteen` and `mbiRHSDenominatorTrunc_seventeen/eighteen`.

Follow the same patterns as N=15-16.

Build: `lake build QseriesFormalization.Chapter16`

## Task 165: Ch05 — five-particle and six-particle states

File: `QseriesFormalization/Chapter05.lean`

Add `charge_five_particles`, `energy_five_particles`, `charge_six_particles`, `energy_six_particles`.

Follow the pattern from four-particle states.

Build: `lake build QseriesFormalization.Chapter05`

## Task 166: Ch03 — qBinomialTerm properties

File: `QseriesFormalization/Chapter03.lean`

Add any new qBinomialTerm evaluation theorems that are natural extensions. For example, evaluate qBinomialTerm at small values (n=3,k=0; n=3,k=1; n=3,k=2; n=3,k=3) if not already present.

Build: `lake build QseriesFormalization.Chapter03`

## Build constraint
NEVER run bare `lake build`. Always `lake build QseriesFormalization.ChapterXX`.
