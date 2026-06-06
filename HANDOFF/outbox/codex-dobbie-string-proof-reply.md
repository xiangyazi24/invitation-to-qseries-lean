# Dobbie Gaussian 5-string proof status

Result: not fully closed.

Committed clean milestone:

```text
742741d ch15: add Gaussian string scalar identity
```

What closed in Lean:

- Added the `A/B` scalar layer for the existing Gaussian coordinates
  `pi5 = (1,2)`, `piBar5 = (1,-2)`.
- Proved the finite 5-string `A_t` recurrence:

```lean
theorem fiveStringASum_eq_fiveStringC_mul (g : GaussianInt) (t : ℕ) :
    fiveStringASum g t = fiveStringC t * gaussA g
```

- Proved endpoint scalar recurrence and the cleared denominator form of
  Dobbie string identity (handoff identity (24), adjusted to this file's
  `π = 1 + 2i` convention):

```lean
theorem string_scalar_identity (g : GaussianInt) (t : ℕ) :
    fiveStringEndpointScalar g t = 4 * fiveStringASum g t
```

Here

```lean
fiveStringEndpointScalar g t =
  (2*A(z_0) + 3*B(z_0)) + (2*A(z_t) - 3*B(z_t))
```

for `z_j = fiveStringPoint g t j`, so this is the integer-cleared version of

```text
(A0 + 3/2 B0) + (Ah - 3/2 Bh) = 2 * Σ A_t
```

in the repository's `pi5 = 1 + 2i` orientation.

Validation:

```bash
export PATH=$HOME/.elan/bin:$PATH
lake env lean QseriesFormalization/Pending/Chapter15_WronskianIndependent.lean
```

Result: exit code `0`, with the pre-existing warning that
`pentagonalWronskianCoeff_eq_jacobiThetaSquareCoeff` still uses `sorry`.

No new `sorry`, `axiom`, `admit`, or `native_decide` was added in the committed
milestone. The file still contains earlier `native_decide` certificates and the
one original `sorry`.

Remaining blocker:

The handoff's scalar identity is now formalized, but it is not enough by itself
to close the `5 | 4*N+1` branch. The missing Lean theorem is still the global
finite-shell decomposition/reindexing:

```lean
N : ℕ
h5N : ¬ (4 * (N : ℤ) + 1) % 5 ≠ 0
⊢ pentagonalWronskianCoeff N = jacobiThetaSquareCoeff N
```

Concretely, the next required step is one of:

1. Partition `fullNormShell N` for `5 ∣ 4*N+1` into primitive strings
   `fiveStringPoint g h j`, prove interiors contribute zero on the K side,
   and use `string_scalar_identity` on each string; or
2. Prove the equivalent full-shell recurrence for both K and H sums:
   `S(5M) = -6*S(M) - 25*S(M/5)` with the correction term only when
   `5 ∣ M`, then close by strong induction on `N`.

The local ingredients already present for this next step are:

- `fiveStringPoint_interior_unitConjOrbitK_zero`
- `fiveStringPoint_left_endpoint_succ_gaussK_zero`
- `unitConjOrbitK_pi5_add_piBar5`
- `unitConjOrbitH_pi5_add_piBar5`
- `fiveString_t0_unitConjOrbit_identity`
- `string_scalar_identity`

The missing part is the all-shell coverage/no-overlap proof (or its recurrence
form), not the scalar endpoint calculation.
