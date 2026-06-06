Status: Jacobi side closed for all `N`.

I proved the non-computational Jacobi/full-shell bridge:

```lean
theorem jacobiThetaSquareCoeffExpanded_eq_fullNormShellHQuarterSum (N : ℕ) :
    jacobiThetaSquareCoeffExpanded N = fullNormShellHQuarterSum N

theorem jacobiThetaSquareCoeff_eq_fullNormShellHQuarterSum (N : ℕ) :
    jacobiThetaSquareCoeff N = fullNormShellHQuarterSum N
```

Main new scaffolding:

```lean
def jacobiShellPairs
def fullNormShell
def jacobiOrbitPoint
def jacobiOrbitDomain
def fullShellInverse
```

The proof uses a `Finset.sum_bij'` between `Fin 4 × jacobiShellPairs N` and
`fullNormShell N`.  The inverse is built from
`r = (|A+B|-1)/2`, `s = (|A-B|-1)/2`, with the sign index determined by the
signs of `A-B` and `A+B`.  The key inverse lemmas are:

```lean
theorem fullShellInverse_jacobiOrbitPoint
theorem jacobiOrbitPoint_fullShellInverse
```

Then the `Fin 4` fiber sum collapses to four equal `gaussH` terms via:

```lean
theorem jacobiOrbitPoint_gaussH
theorem jacobiOrbitDomain_sum_eq_four_jacobiShellPairs_sum
theorem fullNormShell_sum_eq_four_jacobiShellPairs_sum
```

I also replaced
`jacobiThetaSquareCoeffExpanded_eq_fullNormShellHQuarterSum_le_fifty` so it now
follows from the all-`N` theorem instead of `native_decide`.

What remains:

The pentagonal side is still only checked through `50`; the final theorem still
has the original `sorry`.  Next target is the analogous all-`N` proof of

```lean
pentagonalWronskianCoeffExpanded N = fullNormShellHQuarterSum N
```

using the existing `gaussK`/`gaussH` orbit lemmas.

Verification:

```bash
lake env lean QseriesFormalization/Pending/Chapter15_WronskianIndependent.lean
```

Result: succeeds, with only the original final `sorry` warning.
