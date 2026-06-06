Completed the final bridge in
`QseriesFormalization/Pending/Chapter20_LiouvilleConvolution.lean`.

The bridge is now proved for all `n`:

```lean
theorem factorPairRightSplitSumZ_eq_liouvilleBD3Sum (n : Nat) :
    sigma1Sigma3FactorPairRightSplitSumZ n = liouvilleBD3Sum n

theorem sigma1Sigma3ConvZ_eq_liouvilleBD3Sum (n : Nat) :
    sigma1Sigma3ConvZ n = liouvilleBD3Sum n
```

Proof structure:

- `liouvilleBD3Sum_eq_nested` rewrites the `Q_n` sum as the bounded
  four-variable indicator sum
  `if a*b + c*d = n then b*d^3 else 0`.
- `factorPairRightSplit_product_expansion` expands the product of the two
  bounded factor-pair sums.
- `sum_factorPair_k_eq_liouville_weight` performs the key collapse over `k`:
  the only possible contributing index is `k = a*b`, and the second indicator
  forces `c*d = n-k`, equivalently `a*b+c*d=n`.
- `factorPairRightSplitSumZ_eq_liouvilleBD3Sum` swaps the finite sums and
  applies that `k`-collapse pointwise.
- `sigma1Sigma3ConvZ_eq_liouvilleBD3Sum` combines this with the existing
  divisor-sum expansion theorem
  `sigma1Sigma3ConvZ_eq_factorPairRightSplitSumZ`.

I also left the final combined Lahiri theorem available:

```lean
theorem twoforty_mul_sigma1Sigma3ConvZ_eq_lahiri (n : Nat) :
    (240 : Int) * sigma1Sigma3ConvZ n =
      21 * sigmaPowZ 5 n + (10 - 30 * (n : Int)) * sigmaPowZ 3 n -
        sigmaPowZ 1 n
```

Verification:

```bash
lake env lean QseriesFormalization/Pending/Chapter20_LiouvilleConvolution.lean
```

passes.
