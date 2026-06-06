import QseriesFormalization.Chapter07_RRStep5H
import QseriesFormalization.Pending.JTP_FormalPS_Pentagonal

/-!
# Rogers-Ramanujan analytic identity over `ℂ`, H side

This file packages the Complex-valued second Rogers-Ramanujan identity

`rrJInf q q * (q;q)_∞ = pentagonal014(q)`

for `‖q‖ < 1`.
-/

namespace QseriesFormalization
namespace Pending
namespace RRAnalyticProofH

open Filter Topology
open QseriesFormalization.PartII.Ch07
open QseriesFormalization.Pending.JTPFormalPSPentagonal

/-- Analytic notation for `(q;q)_∞`. -/
noncomputable def qPochhammer_inf (q : ℂ) : ℂ :=
  PartI.Ch04.eulerPentagonalInfiniteProduct q

/-- Analytic pentagonal `014` series:
`∑ k : ℤ, (-1)^k q^{k(5k-3)/2}`. -/
noncomputable def pentagonal014_analytic (q : ℂ) : ℂ :=
  pentagonal014Analytic q

/--
Rogers-Ramanujan analytic identity, second identity in multiplicative form.

The closed analytic proof is obtained from the existing Chapter 7 H-side
Tannery limit theorem and the already-proved `j ↦ -j` reindexing lemma for the
`pentagonal014` series.
-/
theorem rrJInf_q_mul_qPochhammer_inf_eq_pentagonal014_analytic
    (q : ℂ) (hq : ‖q‖ < 1) :
    rrJInf q q * qPochhammer_inf q = pentagonal014_analytic q := by
  unfold qPochhammer_inf pentagonal014_analytic pentagonal014Analytic
  calc
    rrJInf q q * PartI.Ch04.eulerPentagonalInfiniteProduct q =
        ∑' j : ℤ, (-1 : ℂ) ^ j * q ^ (j * (5 * j + 3) / 2) :=
      rrJInf_q_mul_eulerPentagonal_eq q hq
    _ = ∑' j : ℤ, (-1 : ℂ) ^ j * q ^ (j * (5 * j - 3) / 2) :=
      (tsum_pentagonal014_eq_theta_sum_2 q).symm

/-- User-facing quantified form of the same theorem. -/
theorem rogers_ramanujan_second_identity_complex :
    ∀ q : ℂ, ‖q‖ < 1 →
      rrJInf q q * qPochhammer_inf q = pentagonal014_analytic q := by
  intro q hq
  exact rrJInf_q_mul_qPochhammer_inf_eq_pentagonal014_analytic q hq

end RRAnalyticProofH
end Pending
end QseriesFormalization
