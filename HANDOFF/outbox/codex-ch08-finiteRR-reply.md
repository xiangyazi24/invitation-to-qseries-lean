Completed the acceptable deliverable: the Chan 8.1 finite sum-side recurrence.

New file:
- `QseriesFormalization/Pending/Chapter08_FiniteRR.lean`

What closed:
- Defined `EFinite q a N = sum_j q^(j^2+a*j) * [N-j choose j]_q`, i.e. Chan's
  finite `E_{N+1}(a)` sum side.
- Proved initial values:
  - `EFinite_zero`
  - `EFinite_one`
- Proved Chan Eq. (8.2), zero-based:
  - `EFinite_recurrence`:
    `EFinite q a (N+2) = EFinite q a (N+1) + q^(N+a+1) * EFinite q a N`
- Proved a one-based wrapper matching the book's indexing:
  - `EFinite_chan_eq_8_2_of_two_le`:
    `EFinite q a n = EFinite q a (n-1) + q^(n+a-1) * EFinite q a (n-2)` for `2 <= n`.

Important note:
- The handoff text identifies existing `D_partialSum q a N = sum q^(j^2+a*j)/(q;q)_j`
  with Chan's finite `E_n(a)`. The PDF does not: Chan's `E_n(a)` in Section 8.1
  is the Gaussian-polynomial finite sum `sum_j q^(j^2+a*j) [n-j-1 choose j]_q`;
  the quotient by `(q;q)_j` appears only after letting the finite top index tend
  to infinity. I formalized the recurrence for the actual finite `E_n(a)`.

Not closed:
- The theta/Gaussian right side `D_n(a)` and Theorem 8.1 equality are not yet
  formalized.

Verification:
- `~/.elan/bin/lake env lean QseriesFormalization/Pending/Chapter08_FiniteRR.lean`
  passed with no warnings.
- `rg -n "\\bsorry\\b|\\badmit\\b|^\\s*axiom\\b" QseriesFormalization/Pending/Chapter08_FiniteRR.lean`
  returned no matches.
- Re-elaborated the source with `#print axioms` appended. The new public
  theorems depend only on `[propext, Classical.choice, Quot.sound]`; no
  `sorryAx`.
