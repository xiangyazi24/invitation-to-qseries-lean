Status: the convolution-to-Liouville bridge is closed in Lean, with no
`sorry`/`admit`/`axiom`.

File changed:

- `QseriesFormalization/Pending/Chapter20_LiouvilleConvolution.lean`

Main additions:

1. Expanded the four-tuple Liouville sum into bounded nested sums:

   ```lean
   theorem sum_liouvilleBox_eq_nested (n : Nat) (F : LQuad → Int) :
       (∑ q ∈ liouvilleBox n, F q) =
         ∑ a ∈ Finset.Icc 1 n, ∑ b ∈ Finset.Icc 1 n,
           ∑ c ∈ Finset.Icc 1 n, ∑ d ∈ Finset.Icc 1 n,
             F { a := a, b := b, c := c, d := d }

   theorem liouvilleBD3Sum_eq_nested (n : Nat) :
       liouvilleBD3Sum n =
         ∑ a ∈ Finset.Icc 1 n, ∑ b ∈ Finset.Icc 1 n,
           ∑ c ∈ Finset.Icc 1 n, ∑ d ∈ Finset.Icc 1 n,
             if a * b + c * d = n then (b : Int) * (d : Int) ^ 3 else 0
   ```

2. Proved the product expansion for the bounded factor-pair split:

   ```lean
   theorem factorPairRightSplit_product_expansion (n k : Nat) :
       ((∑ a ∈ Finset.Icc 1 n, ∑ b ∈ Finset.Icc 1 n,
         if a * b = k then ((b ^ 1 : Nat) : Int) else 0) *
       (∑ c ∈ Finset.Icc 1 n, ∑ d ∈ Finset.Icc 1 n,
         if c * d = n - k then ((d ^ 3 : Nat) : Int) else 0)) =
         ∑ a ∈ Finset.Icc 1 n, ∑ b ∈ Finset.Icc 1 n,
           ∑ c ∈ Finset.Icc 1 n, ∑ d ∈ Finset.Icc 1 n,
             (if a * b = k then ((b ^ 1 : Nat) : Int) else 0) *
               (if c * d = n - k then ((d ^ 3 : Nat) : Int) else 0)
   ```

3. Proved the key inner `k` collapse. This is the reindexing content:
   for fixed positive `a,b,c,d`, exactly one `k = a*b` contributes iff
   `a*b + c*d = n`.

   ```lean
   theorem sum_factorPair_k_eq_liouville_weight {n a b c d : Nat}
       (ha : a ∈ Finset.Icc 1 n) (hb : b ∈ Finset.Icc 1 n)
       (hc : c ∈ Finset.Icc 1 n) (hd : d ∈ Finset.Icc 1 n) :
       (∑ k ∈ Finset.Icc 1 (n - 1),
         (if a * b = k then ((b ^ 1 : Nat) : Int) else 0) *
           (if c * d = n - k then ((d ^ 3 : Nat) : Int) else 0)) =
         if a * b + c * d = n then (b : Int) * (d : Int) ^ 3 else 0
   ```

4. Promoted the previous finite check to the all-`n` theorem:

   ```lean
   theorem factorPairRightSplitSumZ_eq_liouvilleBD3Sum (n : Nat) :
       sigma1Sigma3FactorPairRightSplitSumZ n = liouvilleBD3Sum n

   theorem sigma1Sigma3ConvZ_eq_liouvilleBD3Sum (n : Nat) :
       sigma1Sigma3ConvZ n = liouvilleBD3Sum n
   ```

   The last theorem uses the existing
   `sigma1Sigma3ConvZ_eq_factorPairRightSplitSumZ`, so the original
   convolution is now connected to the Liouville four-tuple sum for all `n`.

5. Added the final original-convolution Lahiri theorem:

   ```lean
   theorem twoforty_mul_sigma1Sigma3ConvZ_eq_lahiri (n : Nat) :
       (240 : Int) * sigma1Sigma3ConvZ n =
         21 * sigmaPowZ 5 n + (10 - 30 * (n : Int)) * sigmaPowZ 3 n -
           sigmaPowZ 1 n
   ```

Validation:

- `lake env lean QseriesFormalization/Pending/Chapter20_LiouvilleConvolution.lean`
- `rg -n "sorry|admit|axiom" QseriesFormalization/Pending/Chapter20_LiouvilleConvolution.lean`

Both pass.
