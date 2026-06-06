Assembled the Lahiri -> Ramanujan E4 chain.

Files touched:

- `QseriesFormalization/Pending/Chapter20_LiouvilleConvolution.lean`
- `QseriesFormalization/Pending/Chapter20_Eisenstein.lean`

Closed arithmetic chain:

```lean
theorem twoforty_mul_sigma1Sigma3ConvZ_eq_lahiri (n : Nat) :
    (240 : Int) * sigma1Sigma3ConvZ n =
      21 * sigmaPowZ 5 n + (10 - 30 * (n : Int)) * sigmaPowZ 3 n -
        sigmaPowZ 1 n
```

This combines:

1. `sigma1Sigma3ConvZ_eq_liouvilleBD3Sum`
2. `twoforty_mul_liouvilleBD3Sum_eq_lahiri`

Imported this into `Chapter20_Eisenstein.lean` and proved the local
Eisenstein-side Lahiri theorem for all `n`:

```lean
theorem lahiriSigma1Sigma3IdentityAt_all (n : Nat) :
    lahiriSigma1Sigma3IdentityAt n
```

Then assembled the existing bridge to the E4 arithmetic theta identity:

```lean
theorem ramanujanThetaE4ArithmeticIdentityAt_all (n : Nat) :
    ramanujanThetaE4ArithmeticIdentityAt n
```

Added the coefficient bridge from the arithmetic identity to the formal PS
residual:

```lean
theorem convCoeffZ_sigmaPowZ_one_eisensteinE4CoeffZ (n : Nat) :
    convCoeffZ (sigmaPowZ 1) eisensteinE4CoeffZ n =
      sigmaPowZ 1 n + 240 * sigma1Sigma3ConvZ n

theorem ramanujanThetaE4ResidualCoeffZ_eq_zero_all (n : Nat) :
    ramanujanThetaE4ResidualCoeffZ n = 0
```

So the formal Ramanujan E4 theta equation is now proved unconditionally:

```lean
theorem RamanujanThetaE4_all : RamanujanThetaE4
```

I also added the immediate conditional final assembly using the now-closed E4
input:

```lean
theorem eisensteinE4_cubed_sub_eisensteinE6_squared_eq_1728_discriminantPS_of_RamanujanThetaE6
    (hE6 : RamanujanThetaE6) :
    eisensteinE4PS ^ 3 - eisensteinE6PS ^ 2 =
      (PowerSeries.C (1728 : ℚ)) * discriminantPS ℚ
```

Remaining blocker for the completely unconditional
`eisensteinE4_cubed_sub_eisensteinE6_squared_eq_1728_discriminantPS`:

- `RamanujanThetaE6` is still an input to the existing discriminant bridge.
  The sigma1*sigma3/Lahiri proof closes E4, but not the separate E6 theta
  equation.

For the full mod-691 tau congruence via the Chapter 20 bridge, the remaining
inputs are still:

- `eisensteinDeltaIdentity (ZMod 691)`
- `eisensteinWeight12LinearIdentity (ZMod 691)`

The first follows from the discriminant identity once the appropriate
coefficient-ring version is available; the second is the independent
weight-12 linear Eisenstein identity.

Verification:

```bash
lake env lean QseriesFormalization/Pending/Chapter20_LiouvilleConvolution.lean
lake env lean QseriesFormalization/Pending/Chapter20_Eisenstein.lean
```

Both pass. Also checked that there are no `sorry`/`admit` occurrences in the
two files.
