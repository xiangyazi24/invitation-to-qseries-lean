Task 48 reply

Modified `QseriesFormalization/Chapter09.lean`.

Added:
- `BaileyTerm_trivial_one_zero`
- `BaileyTerm_trivial_one_one`
- `BaileyBeta_trivial_one`
- `BaileyBeta_trivial_succ`

I did not add the requested RHS with the extra factor `(1 - a * q ^ 2)`, because it is not true for the current definition:
`BaileyTerm` uses `(a*q;q)_(n+k)`, so at `n = 1` the only nonzero trivial-pair summand is `k = 0`, whose denominator is `(q;q)_1 * (aq;q)_1 = (1-q) * (1-aq)`. The `k = 1` summand has `(aq;q)_2`, but its numerator is `α_1 = 0`, so it vanishes.

Validation:
- `lake build QseriesFormalization.Chapter09` succeeded.
- `rg "sorry|axiom|native_decide" QseriesFormalization/Chapter09.lean` produced no matches.
- Full `lake build` was attempted, but it is blocked by existing errors in `Chapter02.lean` and `Chapter06.lean`, outside the requested file scope.
