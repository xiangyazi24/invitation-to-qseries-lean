Partial 0-sorry cyclotomic infrastructure added in
`QseriesFormalization/Pending/RamanujanQuintic.lean`.

Closed:
- Added `scaleX` as the `PowerSeries.rescale` ring hom:
  ```lean
  scaleX (c : R) : R⟦X⟧ →+* R⟦X⟧
  ```
- Proved the coefficient formula and basic API:
  ```lean
  coeff_scaleX
  scaleX_X
  scaleX_X_pow
  scaleX_oneSubXPow
  scaleX_qPochFinitePS
  ```
- Proved the `expand` commutation rule:
  ```lean
  scaleX_expand :
    scaleX c (PowerSeries.expand p hp φ) =
      PowerSeries.expand p hp (scaleX (c ^ p) φ)
  ```
- Proved the primitive fifth-root algebraic factor collapse:
  ```lean
  prod_one_sub_primitive_fifth :
    ∏ j : Fin 5, (1 - μ ^ (j : ℕ) * y) = 1 - y ^ 5
  ```
- Lifted that collapse to power series and to individual Euler factors:
  ```lean
  prod_one_sub_primitive_fifth_powerSeries
  prod_scaleX_one_sub_X_pow_fifth
  prod_scaleX_oneSubXPow_fifth
  ```
  The factor theorem has the expected case split:
  if `5 ∣ m`, the product is `(1 - X^m)^5`; otherwise it is
  `1 - X^(5*m)`.
- Proved the finite q-Pochhammer product collapse:
  ```lean
  prod_scaleX_qPochFinitePS_fifth_collapse
  ```
- Added a concrete `CyclotomicField 5 ℚ` wrapper with a chosen primitive root:
  ```lean
  QuinticCyclotomicField
  quinticZeta
  quinticZeta_isPrimitiveRoot
  quinticCyclotomic_qPochFinitePS_fifth_collapse
  ```

Not closed:
- No infinite `tprod` quotient/cancellation theorem for
  `∏ j, scaleX (ζ^j) (qPochInfPS R)`.
- No Hirschhorn (8.6.1)/(8.6.2) factor identities.
- No proof of
  ```lean
  ramanujanMod5ProductCoreThetaRat *
      PowerSeries.expand 5 (by decide) (qPochInfPS ℚ) =
    (qPochInfPS ℚ)^11
  ```
- Therefore this does not close the unconditional MBI wrapper.

Validation:
```bash
lake env lean QseriesFormalization/Pending/RamanujanQuintic.lean
rg -n "\b(sorry|admit|axiom)\b|sorryAx" \
  QseriesFormalization/Pending/RamanujanQuintic.lean
```
Lean passes; grep returns no matches.

Temporary re-elaboration with `#print axioms` for the key new public theorems:
```lean
scaleX_qPochFinitePS
scaleX_expand
prod_one_sub_primitive_fifth
prod_scaleX_one_sub_X_pow_fifth
prod_scaleX_qPochFinitePS_fifth_collapse
quinticCyclotomic_qPochFinitePS_fifth_collapse
```
reports only:
```text
[propext, Classical.choice, Quot.sound]
```
No `sorryAx`.
