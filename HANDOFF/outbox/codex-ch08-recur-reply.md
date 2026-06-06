Completed the Chapter 8 finite RR recurrence closure for the Rogers-Ramanujan cases.

Touched:
- `QseriesFormalization/Pending/Chapter08_FiniteRR.lean`

Closed:
- Proved the zero-extended integer-bottom Gaussian Pascal infrastructure:
  - negative/top-exceeding vanishing for `gaussianBinomIntLower`
  - one-step lower and upper q-Pascal rules
  - the two local even/odd residual identities
- Proved the DFinite carry-telescope recurrence for all `a ≤ 1`:
  - `DFinite_recurrence_of_a_le_one`
- Specialized it to the two Chan/Rogers-Ramanujan cases:
  - `DFinite_a0_recurrence`
  - `DFinite_a1_recurrence`
- Connected the recurrences to the existing uniqueness bridge:
  - `EFinite_eq_DFinite_a0`
  - `EFinite_eq_DFinite_a1`

Not closed:
- I did not assert the arbitrary-`Nat a` recurrence without hypotheses. The current `DFiniteExponent` is an integer exponent, and for `a > 1` it can be negative; the clean zero-`q`-safe carry proof closes for the intended `a = 0, 1` cases via `a ≤ 1`.

Verification:
- `lake env lean QseriesFormalization/Pending/Chapter08_FiniteRR.lean` passed.
- `rg -n "\\bsorry\\b|\\badmit\\b|^\\s*axiom\\b|sorryAx" QseriesFormalization/Pending/Chapter08_FiniteRR.lean` returned no matches.
- Appending `#print axioms` for the new public recurrence/equality theorems reports only `[propext, Classical.choice, Quot.sound]`; no `sorryAx`.
