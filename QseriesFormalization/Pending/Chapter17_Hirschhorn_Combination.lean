import Mathlib

/-!
# Hirschhorn §3.5 mod-11 — the polynomial identity (algebraic core)

The verified certificate (see `scripts/hirschhorn_mod11_solve.py`):
over `ℤ/11`, with `a,b,c,d,e := J₀,J₁,J₃,J₆,J₁₀`,

  `P = M₃·R₃ + M₆·R₆ + M₈·R₈ + M₉·R₉ + M₁₀·R₁₀`

where `P` is the residue-6 part of `(J₀+J₁+J₃+J₆+J₁₀)⁷` (Hirschhorn eq 3.5.3),
`R_r` is the residue-`r` part of `(…)⁴` (eqs 3.5.6–3.5.10), and `M_r` are the
degree-3 multipliers.  This is Hirschhorn's "left as an exercise" (3.5.11–13);
`a = 7, b = 5, c = 7` exist, here realised by explicit multipliers `M_r`.

Since `ring` does not reduce coefficients modulo 11, we prove the identity by
the exact **integer** factorisation `(Σ M_r R_r) − P = 11·Q` (which `ring`
discharges over `ℤ`), then kill `11·Q` using `CharP R 11`.  `Q` is computed by
`scripts/hirschhorn_mod11_solve.py` / `_compute`. -/

namespace QseriesFormalization
namespace Pending
namespace HirschhornComb

set_option maxHeartbeats 4000000 in

/-- **Hirschhorn's combination identity**, over any commutative ring of
characteristic 11.  `P = Σ_r M_r · R_r`, with `a,b,c,d,e = J₀,J₁,J₃,J₆,J₁₀`. -/
theorem hirschhorn_P_eq_combination
    {R : Type*} [CommRing R] [CharP R 11] (a b c d e : R) :
    (7*a^6*d + 10*a^5*c^2 + a^4*b*d*e + 8*a^3*d^3*e + 2*a^3*b*c^2*e + 8*a^3*b^3*c
      + 10*a^2*e^5 + 2*a^2*c*d*e^3 + 3*a^2*c^2*d^2*e + 3*a^2*b^2*d*e^2 + 3*a^2*b^2*c*d^2
      + 8*a*c^3*e^3 + a*c^4*d*e + 2*a*b*d^3*e^2 + a*b*c*d^4 + 3*a*b^2*c^2*e^2
      + 2*a*b^2*c^3*d + a*b^4*c*e + 7*a*b^6 + 10*d^5*e^2 + 7*c*d^6 + 7*c^6*e + 7*b*e^6
      + b*c*d*e^4 + 3*b*c^2*d^2*e^2 + 8*b*c^3*d^3 + 10*b^2*c^5 + 8*b^3*d*e^3
      + 2*b^3*c*d^2*e + 10*b^5*d^2)
    =
    (10*b*c*e + 10*b^3 + 4*a^2*c) * (4*a^3*c + 2*a*b*c*e + 4*a*b^3 + 4*d*e^3 + c*d^2*e + 6*b^2*d^2)
    + (4*d^2*e + 10*a*b*e + 10*a^3) * (4*a^3*d + 6*a^2*c^2 + 2*a*b*d*e + 4*d^3*e + b*c^2*e + 4*b^3*c)
    + (10*c^3 + 4*a*e^2 + 10*a*c*d) * (4*a*e^3 + 2*a*c*d*e + a*b^2*d + 4*c^3*e + 4*b*d^3 + 6*b^2*c^2)
    + (10*e^3 + 10*c*d*e + 4*b^2*d) * (6*a^2*e^2 + a^2*c*d + 4*a*c^3 + 4*b*e^3 + 2*b*c*d*e + 4*b^3*d)
    + (10*d^3 + 4*b*c^2 + 10*a*b*d) * (4*a^3*e + a*b*e^2 + 2*a*b*c*d + 6*d^2*e^2 + 4*c*d^3 + 4*b*c^3) := by
  have h11 : (11 : R) = 0 := by exact_mod_cast CharP.cast_eq_zero R 11
  -- (Σ M_r R_r) − P = 11 · Q  as an exact integer-coefficient identity.
  have key :
      ((10*b*c*e + 10*b^3 + 4*a^2*c) * (4*a^3*c + 2*a*b*c*e + 4*a*b^3 + 4*d*e^3 + c*d^2*e + 6*b^2*d^2)
        + (4*d^2*e + 10*a*b*e + 10*a^3) * (4*a^3*d + 6*a^2*c^2 + 2*a*b*d*e + 4*d^3*e + b*c^2*e + 4*b^3*c)
        + (10*c^3 + 4*a*e^2 + 10*a*c*d) * (4*a*e^3 + 2*a*c*d*e + a*b^2*d + 4*c^3*e + 4*b*d^3 + 6*b^2*c^2)
        + (10*e^3 + 10*c*d*e + 4*b^2*d) * (6*a^2*e^2 + a^2*c*d + 4*a*c^3 + 4*b*e^3 + 2*b*c*d*e + 4*b^3*d)
        + (10*d^3 + 4*b*c^2 + 10*a*b*d) * (4*a^3*e + a*b*e^2 + 2*a*b*c*d + 6*d^2*e^2 + 4*c*d^3 + 4*b*c^3))
      - (7*a^6*d + 10*a^5*c^2 + a^4*b*d*e + 8*a^3*d^3*e + 2*a^3*b*c^2*e + 8*a^3*b^3*c
          + 10*a^2*e^5 + 2*a^2*c*d*e^3 + 3*a^2*c^2*d^2*e + 3*a^2*b^2*d*e^2 + 3*a^2*b^2*c*d^2
          + 8*a*c^3*e^3 + a*c^4*d*e + 2*a*b*d^3*e^2 + a*b*c*d^4 + 3*a*b^2*c^2*e^2
          + 2*a*b^2*c^3*d + a*b^4*c*e + 7*a*b^6 + 10*d^5*e^2 + 7*c*d^6 + 7*c^6*e + 7*b*e^6
          + b*c*d*e^4 + 3*b*c^2*d^2*e^2 + 8*b*c^3*d^3 + 10*b^2*c^5 + 8*b^3*d*e^3
          + 2*b^3*c*d^2*e + 10*b^5*d^2)
      = 11 * (6*d^5*e^2 + 3*c*d^6 + 3*c^6*e + 3*b*e^6 + 9*b*c*d*e^4 + 5*b*c^2*d^2*e^2
          + 8*b*c^3*d^3 + 6*b^2*c^5 + 8*b^3*d*e^3 + 12*b^3*c*d^2*e + 6*b^5*d^2 + 8*a*c^3*e^3
          + 9*a*c^4*d*e + 12*a*b*d^3*e^2 + 9*a*b*c*d^4 + 5*a*b^2*c^2*e^2 + 12*a*b^2*c^3*d
          + 9*a*b^4*c*e + 3*a*b^6 + 6*a^2*e^5 + 12*a^2*c*d*e^3 + 5*a^2*c^2*d^2*e
          + 5*a^2*b^2*d*e^2 + 5*a^2*b^2*c*d^2 + 8*a^3*d^3*e + 12*a^3*b*c^2*e + 8*a^3*b^3*c
          + 9*a^4*b*d*e + 6*a^5*c^2 + 3*a^6*d) := by
    ring
  rw [h11, zero_mul] at key
  -- key : RHS − P = 0  ⟹  P = RHS
  exact (sub_eq_zero.mp key).symm

end HirschhornComb
end Pending
end QseriesFormalization
