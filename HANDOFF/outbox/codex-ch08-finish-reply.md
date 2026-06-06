Completed the largest 0-sorry closure I could make for Chapter 8 finite RR.

Touched:
- `QseriesFormalization/Pending/Chapter08_FiniteRR.lean`

Closed:
- Added the alternating Gaussian-polynomial side:
  - `DFiniteExponent`
  - `DFiniteLower`
  - `gaussianBinomIntLower`
  - `DFiniteBound`
  - `DFiniteTerm`
  - `DFinite`
- Proved `DFinite` base/sanity values for the actual Rogers-Ramanujan cases:
  - `DFinite_zero_zero`
  - `DFinite_zero_one`
  - `DFinite_one_zero`
  - `DFinite_one_one`
  - `DFinite_zero_two`
  - `DFinite_one_two`
  - `DFinite_a0_recurrence_zero`
  - `DFinite_a1_recurrence_zero`
- Proved the recurrence uniqueness bridge:
  - `second_order_recurrence_unique`
  - `EFinite_eq_of_recurrence`
- Reduced Chan Thm 8.1 to the remaining alternating-side recurrence:
  - `EFinite_eq_DFinite_of_recurrence`
  - `EFinite_eq_DFinite_a0_of_recurrence`
  - `EFinite_eq_DFinite_a1_of_recurrence`

Not closed:
- The full `DFinite` recurrence
  `DFinite q a (N+2) = DFinite q a (N+1) + q^(N+a+1) * DFinite q a N`.
  This is the hard bilateral floor-index reindexing step. No fake theorem,
  axiom, or sorry was introduced.

Verification:
- `~/.elan/bin/lake env lean QseriesFormalization/Pending/Chapter08_FiniteRR.lean`
  passed.
- `rg -n "\\bsorry\\b|\\badmit\\b|^\\s*axiom\\b|sorryAx" QseriesFormalization/Pending/Chapter08_FiniteRR.lean`
  returned no matches.
- Temporary `#print axioms` checks for the new conditional theorem bridge reported
  only `[propext, Classical.choice, Quot.sound]`; no `sorryAx`.
