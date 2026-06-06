Status: partial formal closure, no proof holes

Added:
- `QseriesFormalization/Pending/Ramanujan1Psi1.lean`
- root import in `QseriesFormalization.lean`

What is proved:
- `expand_qPochInfPS_eq_qPochAPPS`: `expand s (qPochInfPS R) = qPochAPPS R s s`.
- `ramanujan1Psi1_limit014_formal_complex` and `_rat`:
  `(X, X^4, X^5; X^5)_∞ = ∑_{k∈ℤ} (-1)^k X^((5k²-3k)/2)`.
- `ramanujan1Psi1_limit023_formal_complex` and `_rat`:
  `(X^2, X^3, X^5; X^5)_∞ = ∑_{k∈ℤ} (-1)^k X^((5k²-k)/2)`.
- Ch10 hooks:
  - `ch10_chan1015PentagonalPS_eq_expand_onePsiOneLimit014_series`
  - `ch10_expand_onePsiOneLimit014_product_eq_chan1015PentagonalPS`
  - `coeff_ch10_chan1015PentagonalPS`
  - `chan1015RHSPS_eq_onePsiOneLimit_product_form`
  - `chan1015RHSPS_eq_AP_product_form`

Validation:
- `lake build QseriesFormalization.Pending.Ramanujan1Psi1`
- `lake env lean QseriesFormalization.lean`
- `rg -n "sorry|axiom|admit|native_decide" QseriesFormalization/Pending/Ramanujan1Psi1.lean` returned no matches.

Note:
This proves the JTP-limit/formal-PS specialization currently usable by Ch10.
The full three-parameter meromorphic Ramanujan `1ψ1(a;b;q,z)` is not yet
formalized as a Laurent/meromorphic identity in this repository.
