import QseriesFormalization.Chapter19
import QseriesFormalization.Pending.JacobiCubeAnalyticToFormal

/-!
# Chapter 17 — Ramanujan's third congruence `∀ n, 11 ∣ p(11n + 6)`

PARTIAL: verified by `native_decide` for n ≤ 10.

**Why not a general proof yet:**

Unlike mod-5 and mod-7, the mod-11 case does NOT admit a simple per-term
residue argument.  The relevant convolution `(jts^3 * qPoch) . coeff (11n+6)`
in `ZMod 11` is a sum over 4-tuples `(a, b, c, d)` with `T_a + T_b + T_c + P_d = 11n+6`,
weighted by `(-1)^{a+b+c} (2a+1)(2b+1)(2c+1) * pentagonalSign(P_d)`.

**Counterexample to naive per-term zero**: take `a = b = 0`, `c = 3`, `d = 0`:
  - `T_0 = 0`, `T_0 = 0`, `T_3 = 6`, `P_0 = 0`.
  - Sum `= 6 ≡ 6 (mod 11)`, fitting the form `11·0 + 6`.
  - Weight `= 1·1·(-7)·1 = -7 ≡ 4 (mod 11)`, **non-zero**.

So individual contributions are non-zero; the total vanishes by cancellation.
The general proof needs either:
  (a) Chan §17.3's η-quotient identity (multi-week formalization), or
  (b) A clever bijection / sign-flipping argument on the 4-tuple space.

For now: small-n verification by `native_decide`.
-/

namespace QseriesFormalization
namespace Pending
namespace Ch17p11

open QseriesFormalization.PartIV.Ch19
open QseriesFormalization.PartI.Ch05 (pentagonalSign)

/-- **Mod-11 Ramanujan convolution vanishing**, n ≤ 20, by direct computation. -/
theorem jts_cubed_qPoch_conv_zero_mod_11_le_twenty :
    ∀ n ≤ 20,
      (∑ pq ∈ Finset.antidiagonal (11 * n + 6),
        (∑ abc ∈ Finset.antidiagonal pq.1,
          (∑ ab ∈ Finset.antidiagonal abc.1,
            ((jacobiTripleSign ab.1 : ℤ) : ZMod 11) *
            ((jacobiTripleSign ab.2 : ℤ) : ZMod 11)) *
          ((jacobiTripleSign abc.2 : ℤ) : ZMod 11)) *
        ((pentagonalSign pq.2 : ℤ) : ZMod 11)) = 0 := by native_decide

/-- Backward-compatible alias for the earlier `n ≤ 10` version. -/
theorem jts_cubed_qPoch_conv_zero_mod_11_le_ten :
    ∀ n ≤ 10,
      (∑ pq ∈ Finset.antidiagonal (11 * n + 6),
        (∑ abc ∈ Finset.antidiagonal pq.1,
          (∑ ab ∈ Finset.antidiagonal abc.1,
            ((jacobiTripleSign ab.1 : ℤ) : ZMod 11) *
            ((jacobiTripleSign ab.2 : ℤ) : ZMod 11)) *
          ((jacobiTripleSign abc.2 : ℤ) : ZMod 11)) *
        ((pentagonalSign pq.2 : ℤ) : ZMod 11)) = 0 :=
  fun n hn => jts_cubed_qPoch_conv_zero_mod_11_le_twenty n (by omega)

end Ch17p11
end Pending
end QseriesFormalization
