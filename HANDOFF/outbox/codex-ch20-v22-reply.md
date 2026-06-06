Status: partial, with the main telescope and abstract boundary assembly now
formalized in Lean.

File changed:

- `QseriesFormalization/Pending/Chapter20_LiouvilleConvolution.lean`

What was added:

1. Corrected telescope route.

   The requested statement

   `sum_{gtPart} W = sum_{dGtBPart} W`

   is not true for the current `leftMove`: it sends
   `(a,b,c,d)` to `(a-c,b,c,b+d)`, so it changes the `d` entering `W`.
   The sound telescope is instead on the lower `P` term:

   - `sum_dGtB_P_lower_eq_sum_gtPart_P`
   - `sum_bGtD_P_lower_eq_sum_ltPart_P`
   - `four_mul_sum_weightW_dGtB_telescope`
   - `four_mul_sum_weightW_bGtD_telescope`

   These prove, for example,

   ```lean
   4 * (∑ q ∈ dGtBPart n, weightW q) =
     (∑ q ∈ dGtBPart n, liouvilleP (q.b : Int) (q.d : Int)) -
       ∑ q ∈ gtPart n, liouvilleP (q.b : Int) (q.d : Int)
   ```

2. Strict-region boundary cancellation.

   Added swap reindexing for the strict regions:

   - `swapQuad_mem_gtPart_iff_ltPart`
   - `swapQuad_mem_dGtBPart_iff_bGtDPart`
   - `sum_ltPart_Pdb_eq_sum_gtPart_Pbd`
   - `sum_bGtD_Pdb_eq_sum_dGtB_Pbd`

   Then combined the a/c partition and b/d partition into:

   - `two_mul_strict_bd_P_difference_eq_boundary_P_difference`
   - `four_mul_sum_strict_bd_weightW_eq_boundary_P_difference`

   This is the formal boundary term after strict telescope:

   ```lean
   4 * ((∑ q ∈ dGtBPart n, weightW q) +
     ∑ q ∈ bGtDPart n, weightW q) =
     (∑ q ∈ eqPart n, liouvilleP (q.b : Int) (q.d : Int)) -
       ∑ q ∈ eqBDPart n, liouvilleP (q.b : Int) (q.d : Int)
   ```

3. Full `Q_n` abstract boundary assembly.

   On the `b=d` boundary, `4W - P = -b^4` was formalized:

   - `four_mul_weightW_sub_liouvilleP_of_eqBD`
   - `four_mul_sum_eqBDPart_weightW_eq_boundary`
   - `four_mul_liouvilleWSum_eq_boundary`
   - `eight_mul_liouvilleBD3Sum_eq_boundary`

   The last theorem is:

   ```lean
   8 * liouvilleBD3Sum n =
     (∑ q ∈ eqPart n, liouvilleP (q.b : Int) (q.d : Int)) -
       ∑ q ∈ eqBDPart n, (q.b : Int) ^ 4
   ```

4. Inner `eqPart` boundary polynomial.

   Added a rational version of `P`, plus the Faulhaber evaluation for the
   fixed-divisor inner sum:

   - `liouvillePQ`
   - `sum_Ico_pow_one_Q`
   - `sum_Ico_pow_two_Q`
   - `sum_Ico_pow_three_Q`
   - `sum_Ico_pow_four_Q`
   - `sum_liouvillePQ_antidiagonal_expanded`
   - `thirty_mul_sum_liouvillePQ_antidiagonal`

   The key theorem is:

   ```lean
   (30 : ℚ) *
     (∑ b ∈ Finset.Ico 1 m,
       liouvillePQ (b : ℚ) ((m - b : Nat) : ℚ)) =
     21 * (m : ℚ) ^ 5 - 30 * (m : ℚ) ^ 4 +
       10 * (m : ℚ) ^ 3 - (m : ℚ)
   ```

   This matches the expected inner evaluation for `a = c`, where
   `a * (b + d) = n` and `m = n / a`.

Remaining gap:

- The divisor reindexing of `eqPart` and `eqBDPart` is not yet formalized.
  The next target should be:

  ```lean
  30 *
    ((∑ q ∈ eqPart n, liouvilleP (q.b : Int) (q.d : Int)) -
      ∑ q ∈ eqBDPart n, (q.b : Int) ^ 4)
    =
      21 * sigmaPowZ 5 n +
        (10 - 30 * (n : Int)) * sigmaPowZ 3 n -
        sigmaPowZ 1 n
  ```

  Mathematically this follows from:

  - `eqPart`: for each divisor `a | n`, let `m = n / a`; then
    `b = 1..m-1` and `d = m-b`, so
    `30 * sum_b P(b,m-b) = 21m^5 - 30m^4 + 10m^3 - m`.
  - `eqBDPart`: for each divisor `b | n`, `a+c = n/b`, giving
    `(n/b - 1)` choices and contribution
    `∑_{b|n} (n/b - 1)b^4 = n*sigma_3(n) - sigma_4(n)`.

Validation:

- `lake env lean QseriesFormalization/Pending/Chapter20_LiouvilleConvolution.lean`
- `rg -n "sorry|admit|axiom" QseriesFormalization/Pending/Chapter20_LiouvilleConvolution.lean`

Both pass; no `sorry`, `admit`, or `axiom` was added.
