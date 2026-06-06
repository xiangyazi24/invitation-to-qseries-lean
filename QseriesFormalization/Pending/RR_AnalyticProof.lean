import QseriesFormalization.Chapter07_RRStep5
import QseriesFormalization.Chapter09_BaileyLemma
import QseriesFormalization.Pending.JTP_FormalPS_Pentagonal

/-!
# Rogers-Ramanujan analytic identity over `ℂ`

This file packages the Complex-valued target

`rrJInf 1 q * (q;q)_∞ = pentagonal023(q)`

for `‖q‖ < 1`.

It also exposes the Bailey-lemma interface at `x = 1`: once the JTP-derived
pair is available as an `IsBaileyPairByM`, `theorem92` applies over `ℂ` with
the nonzero denominator hypotheses discharged from `‖q‖ < 1`.
-/

namespace QseriesFormalization
namespace Pending
namespace RRAnalyticProof

open Filter Topology
open QseriesFormalization.PartII.Ch07
open QseriesFormalization.PartII.Ch09
open QseriesFormalization.Pending.JTPFormalPSPentagonal

/-- Analytic notation for `(q;q)_∞`. -/
noncomputable def qPochhammer_inf (q : ℂ) : ℂ :=
  PartI.Ch04.eulerPentagonalInfiniteProduct q

/-- Analytic pentagonal `023` series:
`∑ k : ℤ, (-1)^k q^{k(5k-1)/2}`. -/
noncomputable def pentagonal023_analytic (q : ℂ) : ℂ :=
  pentagonal023Analytic q

/-- The JTP-derived `alpha*` sequence over `ℂ`. -/
noncomputable def alpha_star (q : ℂ) : ℕ → ℂ :=
  rrAStar q

/-- The JTP-derived `beta*` sequence over `ℂ`, i.e. `δ_{n,0}`. -/
noncomputable def beta_star (q : ℂ) : ℕ → ℂ :=
  rrBStar q

@[simp] theorem alpha_star_zero (q : ℂ) : alpha_star q 0 = 1 := by
  simp [alpha_star, rrAStar_zero]

@[simp] theorem beta_star_zero (q : ℂ) : beta_star q 0 = 1 := by
  simp [beta_star, rrBStar_zero]

@[simp] theorem beta_star_succ (q : ℂ) (n : ℕ) : beta_star q (n + 1) = 0 := by
  simp [beta_star, rrBStar_succ]

/--
Bailey Theorem 9.2 specialized to the Rogers-Ramanujan seed over `ℂ`.

The only remaining input is the full finite-JTP Bailey-pair bridge
`beta_star = M(1,q) alpha_star`.
-/
theorem theorem92_alpha_star_beta_star
    (q : ℂ) (hq : ‖q‖ < 1)
    (hpair : IsBaileyPairByM (1 : ℂ) q (alpha_star q) (beta_star q)) :
    ∀ n : ℕ,
      L2 (1 : ℂ) q (beta_star q) n =
        M (1 : ℂ) q (D2 (1 : ℂ) q (alpha_star q)) n := by
  exact theorem92 (R := ℂ) (1 : ℂ) q
    (fun k => by
      simpa [one_mul] using one_sub_pow_ne_zero_of_norm_lt_one q hq k)
    (fun k => qPochhammer_ne_zero_of_norm_lt_one q hq k)
    hpair

/--
Rogers-Ramanujan analytic identity, first identity in multiplicative form.

The closed analytic proof is obtained from the existing Chapter 7 Tannery
limit theorem and the already-proved `j ↦ -j` reindexing lemma for the
`pentagonal023` series.
-/
theorem rrJInf_one_mul_qPochhammer_inf_eq_pentagonal023_analytic
    (q : ℂ) (hq : ‖q‖ < 1) :
    rrJInf 1 q * qPochhammer_inf q = pentagonal023_analytic q := by
  unfold qPochhammer_inf pentagonal023_analytic pentagonal023Analytic
  calc
    rrJInf 1 q * PartI.Ch04.eulerPentagonalInfiniteProduct q =
        ∑' j : ℤ, (-1 : ℂ) ^ j * q ^ (j * (5 * j + 1) / 2) :=
      rrJInf_one_mul_eulerPentagonal_eq q hq
    _ = ∑' j : ℤ, (-1 : ℂ) ^ j * q ^ (j * (5 * j - 1) / 2) :=
      (tsum_pentagonal023_eq_theta_sum_1 q).symm

/-- User-facing quantified form of the same theorem. -/
theorem rogers_ramanujan_identity_complex :
    ∀ q : ℂ, ‖q‖ < 1 →
      rrJInf 1 q * qPochhammer_inf q = pentagonal023_analytic q := by
  intro q hq
  exact rrJInf_one_mul_qPochhammer_inf_eq_pentagonal023_analytic q hq

end RRAnalyticProof
end Pending
end QseriesFormalization
