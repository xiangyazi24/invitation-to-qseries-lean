## Result

I added the requested structural layer to
`QseriesFormalization/Pending/Chapter15_WronskianIndependent.lean`.

I did not close the final all-degree coefficient identity yet; the only
remaining `sorry` is still
`pentagonalWronskianCoeff_eq_jacobiThetaSquareCoeff`.

## Added H-side lemmas

The file's current `gaussEps` is the existing parity sign

```lean
def gaussEps (a : ℤ) : ℤ :=
  if a % 2 = 0 then -1 else 1
```

so I kept that definition instead of changing semantics mid-proof.

New lemmas:

- `gaussEps_neg`
- `unitOrbitH_closed`

```lean
(∑ i : Fin 4, gaussH (gaussUnitRotate i (a,b))) =
  2 * (gaussEps a - gaussEps b) * (a ^ 2 - b ^ 2)
```

- `unitOrbitH_closed_of_eps_opposite`

```lean
(∑ i : Fin 4, gaussH (gaussUnitRotate i (a,b))) =
  4 * gaussEps a * (a ^ 2 - b ^ 2)
```

- `unitConjOrbitH_closed`

```lean
unitConjOrbitH (a,b) =
  4 * (gaussEps a - gaussEps b) * (a ^ 2 - b ^ 2)
```

- `unitConjOrbitH_closed_of_eps_opposite`

```lean
unitConjOrbitH (a,b) = 8 * gaussEps a * (a ^ 2 - b ^ 2)
```

The factor is `8` for `unitConjOrbitH` because this definition includes both
the four unit rotations and the conjugate four unit rotations.  The requested
factor `4` is now present for the four-unit orbit alone.

## Added K-side local lemmas

General selected/unselected simplifiers:

- `wronskianRSWeight_of_selector`
- `wronskianRSWeight_of_not_selector`

Explicit four-rotation expansion:

- `gaussK_explicit`

Per-row selected/unselected local lemmas:

- `wronskianRSWeight_rot0_of_selector`
- `wronskianRSWeight_rot0_of_not_selector`
- `wronskianRSWeight_rot1_of_selector`
- `wronskianRSWeight_rot1_of_not_selector`
- `wronskianRSWeight_rot2_of_selector`
- `wronskianRSWeight_rot2_of_not_selector`
- `wronskianRSWeight_rot3_of_selector`
- `wronskianRSWeight_rot3_of_not_selector`

These expose the four selector rows:

```lean
(-a - 3*b) % 5
(-3*a + b) % 5
( a + 3*b) % 5
( 3*a - b) % 5
```

and reduce each selected row to its corresponding `paritySign` times the
quadratic numerator divided by `8`.

## Added selector table

```lean
def wronskianSelectorCount (a b : ℤ) : ℕ := ...

theorem wronskianSelectorCount_residue_check :
    ∀ a b : Fin 5,
      (((a : ℤ) ^ 2 + (b : ℤ) ^ 2) % 5 ≠ 0) →
      wronskianSelectorCount (a : ℤ) (b : ℤ) = 1
```

This proves the mod-5 fact that exactly one of the four `gaussK` rotations is
selected when the norm is prime to `5`.

## Verification

Ran:

```bash
lake env lean QseriesFormalization/Pending/Chapter15_WronskianIndependent.lean
```

It succeeds with the expected single warning:

```text
Chapter15_WronskianIndependent.lean:375:8: warning: declaration uses 'sorry'
```

## Remaining step

The next proof step is to combine these row lemmas with the mod-20 sign table
to turn `fiveString_t0_residue_orbit_check` into an all-integer t=0 orbit
identity without unfolding all 32 Wronskian terms at once.
