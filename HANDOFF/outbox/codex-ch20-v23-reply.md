Status: boundary evaluation closed in Lean, no `sorry`/`admit`/`axiom`.

File changed:

- `QseriesFormalization/Pending/Chapter20_LiouvilleConvolution.lean`

Main additions:

1. Divisor quotient sums are identified with `sigmaPowZ`.

   Added:

   ```lean
   theorem divisorQuotPowSumZ_eq_sigmaPowZ (r n : Nat) :
       (∑ a ∈ Finset.Icc 1 n,
         if a ∣ n then (((n / a) ^ r : Nat) : Int) else 0) = sigmaPowZ r n
   ```

   This is the divisor involution `a ↦ n/a`, proved through the existing
   bounded factor-pair framework.

2. The fixed-`m` Faulhaber inner sum is now available over `Int`.

   Added:

   ```lean
   theorem thirty_mul_sum_liouvilleP_antidiagonal (m : Nat) :
       (30 : Int) *
         (∑ b ∈ Finset.Ico 1 m,
           liouvilleP (b : Int) ((m - b : Nat) : Int)) =
         21 * (m : Int) ^ 5 - 30 * (m : Int) ^ 4 +
           10 * (m : Int) ^ 3 - (m : Int)
   ```

   This lifts the previous rational `liouvillePQ` computation to `Int`.

3. The `eqPart` divisor boundary is evaluated.

   Added:

   ```lean
   theorem thirty_mul_eqPartBoundaryDivisorSumZ_eq_sigma (n : Nat) :
       (30 : Int) * eqPartBoundaryDivisorSumZ n =
         21 * sigmaPowZ 5 n - 30 * sigmaPowZ 4 n +
           10 * sigmaPowZ 3 n - sigmaPowZ 1 n
   ```

4. The `eqBDPart` divisor boundary is evaluated.

   Added:

   ```lean
   theorem eqBDPartBoundaryDivisorSumZ_eq_sigma (n : Nat) :
       eqBDPartBoundaryDivisorSumZ n =
         (n : Int) * sigmaPowZ 3 n - sigmaPowZ 4 n
   ```

5. The boundary difference is assembled into the Lahiri numerator.

   Added:

   ```lean
   theorem thirty_mul_boundaryDivisorDifference_eq_lahiri (n : Nat) :
       (30 : Int) * (eqPartBoundaryDivisorSumZ n - eqBDPartBoundaryDivisorSumZ n) =
         21 * sigmaPowZ 5 n + (10 - 30 * (n : Int)) * sigmaPowZ 3 n -
           sigmaPowZ 1 n
   ```

   Then connected this back to the actual telescoping boundary through the
   existing parameter bijections:

   ```lean
   theorem thirty_mul_boundaryActualDifference_eq_lahiri (n : Nat) :
       (30 : Int) * (eqPartBoundaryActualZ n - eqBDPartBoundaryActualZ n) =
         21 * sigmaPowZ 5 n + (10 - 30 * (n : Int)) * sigmaPowZ 3 n -
           sigmaPowZ 1 n
   ```

6. Final Liouville-side Lahiri theorem:

   ```lean
   theorem twoforty_mul_liouvilleBD3Sum_eq_lahiri (n : Nat) :
       (240 : Int) * liouvilleBD3Sum n =
         21 * sigmaPowZ 5 n + (10 - 30 * (n : Int)) * sigmaPowZ 3 n -
           sigmaPowZ 1 n
   ```

   This uses the previously proved
   `eight_mul_liouvilleBD3Sum_eq_boundary_actual`.

Also hardened two existing parameter-membership proofs by replacing fragile
`omega` steps with direct `Nat.add_sub_of_le` / `Nat.div_mul_cancel`
calculations.

Validation:

- `lake env lean QseriesFormalization/Pending/Chapter20_LiouvilleConvolution.lean`
- `rg -n "sorry|admit|axiom" QseriesFormalization/Pending/Chapter20_LiouvilleConvolution.lean`

Both pass. The older bridge
`sigma1Sigma3FactorPairRightSplitSumZ n = liouvilleBD3Sum n` is still only
present as the finite check `factorPairRightSplitMatchesQThrough8Check_true`;
the new work closes the boundary/Lahiri side once that bridge is promoted.
