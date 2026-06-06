Implemented the boundary evaluations in
`QseriesFormalization/Pending/Chapter20_LiouvilleConvolution.lean`.

Main additions:

- Reindexed both boundary sums with `boundaryParam n`.
  - `eqPartBoundaryParamSumZ_eq_actual`
  - `eqBDPartBoundaryParamSumZ_eq_actual`
  - `eqPartBoundaryParamSumZ_eq_divisor`
  - `eqBDPartBoundaryParamSumZ_eq_divisor`
  - combined as `eqPartBoundaryActualZ_eq_divisor` and
    `eqBDPartBoundaryActualZ_eq_divisor`

- Evaluated the `b = d` boundary with the correct multiplicity:
  ```lean
  theorem eqBDPartBoundaryDivisorSumZ_eq_sigma (n : Nat) :
      eqBDPartBoundaryDivisorSumZ n =
        (n : Int) * sigmaPowZ 3 n - sigmaPowZ 4 n
  ```
  This is not just `sigma_4(n)`: for fixed `b | n`, there are
  `n / b - 1` positive choices of `(a,c)`. I left
  `eqBDPartSigma4ClaimThrough5Check_false` as a small executable witness that
  the bare `sigma_4` claim is false for the current definitions.

- Evaluated the `a = c` boundary using the antidiagonal Faulhaber lemma:
  ```lean
  theorem thirty_mul_eqPartBoundaryDivisorSumZ_eq_sigma (n : Nat) :
      (30 : Int) * eqPartBoundaryDivisorSumZ n =
        21 * sigmaPowZ 5 n - 30 * sigmaPowZ 4 n +
          10 * sigmaPowZ 3 n - sigmaPowZ 1 n
  ```

- Combined the two boundary evaluations:
  ```lean
  theorem thirty_mul_boundaryActualDifference_eq_lahiri (n : Nat) :
      (30 : Int) * (eqPartBoundaryActualZ n - eqBDPartBoundaryActualZ n) =
        21 * sigmaPowZ 5 n + (10 - 30 * (n : Int)) * sigmaPowZ 3 n -
          sigmaPowZ 1 n
  ```

- Final Liouville/Lahiri convolution theorem:
  ```lean
  theorem twoforty_mul_liouvilleBD3Sum_eq_lahiri (n : Nat) :
      (240 : Int) * liouvilleBD3Sum n =
        21 * sigmaPowZ 5 n + (10 - 30 * (n : Int)) * sigmaPowZ 3 n -
          sigmaPowZ 1 n
  ```

Verification:

```bash
lake env lean QseriesFormalization/Pending/Chapter20_LiouvilleConvolution.lean
```

passes.
