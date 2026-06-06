Status: partial

Modified files:
- `QseriesFormalization/Chapter03.lean`

Diff summary:
- Added `section FiniteJTP`.
- Added `finiteJTPSummand`, encoding Chan's bilateral index by the finite change of variables `l = k - n`.
- Added `finiteJTPRHS`, a `natSum` over `k = 0, ..., 2n` representing the finite bilateral sum without losing negative Laurent powers.
- Proved `finite_jacobi_triple_product_zero`.
- Proved `finite_jacobi_triple_product_one`, the concrete `n = 1` finite Jacobi triple product check.

Validation:
- `lake build`
- Final line: `Build completed successfully (7908 jobs).`

Blocked subgoal:
- The full general `n` theorem is not completed. The remaining proof needs the general algebraic bridge from `qPoch (z / q^n) q (2*n)` to `qPoch z q n * qPoch (z^-1 * q) q n`, together with the corresponding finite re-indexing from `k = 0, ..., 2n` to `l = -n, ..., n` using integer powers. I avoided the proposed `l.toNat` RHS because it truncates negative `l` and therefore does not encode the Laurent terms in Chan Eq (3.15).
