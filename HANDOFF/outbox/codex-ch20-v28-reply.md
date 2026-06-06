Status: `RamanujanThetaE6` is now proved.

I first verified the arithmetic target numerically in Python for `n = 1..20`;
all residuals were `0`.

Main new Liouville result:

```lean
theorem e6_sigma_convolution_identity (n : Nat) :
    (12096 : Int) * sigmaSigmaConvZ 1 5 n -
      57600 * sigmaSigmaConvZ 3 3 n =
        -1008 * (n : Int) * sigmaPowZ 5 n +
          504 * sigmaPowZ 5 n + 24 * sigmaPowZ 1 n +
            480 * sigmaPowZ 3 n
```

This is proved in
`QseriesFormalization/Pending/Chapter20_LiouvilleConvolution.lean`.

Proof structure:

- `P15 = (b^2 + b*d + d^2)^3` gives

  ```lean
  theorem twelve_mul_liouvilleBD5Sum_add_fourteen_mul_liouvilleB3D3Sum_eq_boundaryP15
      (n : Nat) :
      12 * liouvilleBD5Sum n + 14 * liouvilleB3D3Sum n =
        (∑ q ∈ eqPart n, liouvilleP15 (q.b : Int) (q.d : Int)) -
          ∑ q ∈ eqBDPart n, (q.b : Int) ^ 6
  ```

  The key step is
  `P15(b,d) - P15(b,d-b) =
    6*b^5*d + 14*b^3*d^3 + 6*b*d^5`.
  The swap symmetry turns the two asymmetric `BD5` terms into
  `12 * liouvilleBD5Sum`.

- Existing/generalized `P33 = b^2*d^2*(b+d)^2` gives

  ```lean
  theorem four_mul_liouvilleB3D3Sum_eq_boundaryP33 (n : Nat) :
      4 * liouvilleB3D3Sum n =
        ∑ q ∈ eqPart n, liouvilleP33 (q.b : Int) (q.d : Int)
  ```

- Boundary evaluation uses the combined polynomial

  ```text
  1008*P15(b,m-b) - 17928*P33(b,m-b)
  ```

  whose antidiagonal sum is

  ```text
  24*m + 480*m^3 + 504*m^5 - 1008*m^6
  ```

  The `b=d` boundary is

  ```lean
  theorem eqBDPartBoundaryPowSix_eq_sigma (n : Nat) :
      eqBDPartBoundaryActualWithZ (fun b => (b : Int) ^ 6) n =
        (n : Int) * sigmaPowZ 5 n - sigmaPowZ 6 n
  ```

  The `sigma_6` terms cancel in the final linear combination.

Connection to Eisenstein:

```lean
theorem ramanujanThetaE6ArithmeticIdentityAt_all (n : Nat) :
    ramanujanThetaE6ArithmeticIdentityAt n

theorem RamanujanThetaE6_all : RamanujanThetaE6
```

These are in `QseriesFormalization/Pending/Chapter20_Eisenstein.lean`.

Assembly now exposes:

```lean
theorem RamanujanThetaE6_from_liouville :
    Ch20Eisenstein.RamanujanThetaE6

theorem eisensteinE4_cubed_sub_eisensteinE6_squared_eq_1728_discriminantPS_all :
    Ch20Eisenstein.eisensteinE4PS ^ 3 -
        Ch20Eisenstein.eisensteinE6PS ^ 2 =
      (PowerSeries.C (1728 : ℚ)) * PartIV.Ch20.discriminantPS ℚ
```

Validation run:

- Python check: E6 residual is `0` for `n = 1..20`.
- `lake env lean QseriesFormalization/Pending/Chapter20_LiouvilleConvolution.lean`
- direct `.olean/.ilean` generation for
  `QseriesFormalization/Pending/Chapter20_LiouvilleConvolution.lean`
- `lake env lean QseriesFormalization/Pending/Chapter20_Eisenstein.lean`
- direct `.olean/.ilean` generation for
  `QseriesFormalization/Pending/Chapter20_Eisenstein.lean`
- `lake env lean QseriesFormalization/Pending/Chapter20_TauMod691Proof.lean`
- `rg -n "\bsorry\b|\badmit\b|\baxiom\b" QseriesFormalization/Pending/Chapter20_LiouvilleConvolution.lean QseriesFormalization/Pending/Chapter20_Eisenstein.lean QseriesFormalization/Pending/Chapter20_TauMod691Proof.lean`

All Lean checks passed; the `rg` command returned no matches.

Remaining for the full tau mod 691 closure: the weight-12 linear Eisenstein
identity modulo 691 is still separate from this E6 theta closure.
