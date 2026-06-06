import QseriesFormalization.Chapter01
import QseriesFormalization.Chapter19

/-!
# Chapter 1 — Generating function for `partitionCount`

This companion file to `Chapter01.lean` exposes the chapter-main theorem
of Chan Ch 1, namely Euler's identity

    ∑_{n ≥ 0} p(n) X^n  =  ∏_{i ≥ 1} 1/(1 - X^i)            (1.1)

in the formal-power-series sense.  Both halves of (1.1) are proved in
`Chapter19.lean` (the formal-PS Ramanujan framework); this file re-exports
them under the `QseriesFormalization.Ch01` namespace so that Ch 1's
chapter-main result is visible at the chapter where Chan states it.

The dependency direction is `Ch01 ← Ch19 ← Ch01_GenFun`, which is acyclic
because `Chapter19` already imports `Chapter01` for `partitionCount`.
-/

namespace QseriesFormalization
namespace Ch01

open PowerSeries
open scoped PowerSeries.WithPiTopology

/-- **Coefficient form of Chan (1.1)** (Euler's generating function for
partitions): the `n`-th coefficient of `partitionGenFun ℤ` is `p(n)`.

This is the heart of Ch 1, exposed in the `Ch01` namespace via the
`Chapter19` proof. -/
theorem coeff_partitionGenFun (n : Nat) :
    (PartIV.Ch19.partitionGenFun ℤ).coeff n = (partitionCount n : ℤ) :=
  PartIV.Ch19.coeff_partitionGenFun_int n

/-- **Rational version** of the coefficient identity. -/
theorem coeff_partitionGenFun_rat (n : Nat) :
    (PartIV.Ch19.partitionGenFun ℚ).coeff n = (partitionCount n : ℚ) :=
  PartIV.Ch19.coeff_partitionGenFun_rat n

/-- **Product form of Chan (1.1)** (Euler's product expansion of the
partition generating function):
`∑ p(n) X^n = ∏' i, (1 + X^(i+1) + X^(2(i+1)) + …)` in `R⟦X⟧`, with each
factor being the formal geometric series for `1/(1 - X^(i+1))`.

This holds in any commutative semiring with a Hausdorff topology
(needed for the infinite product in the formal-series Pi-topology). -/
theorem partitionGenFun_eq_euler_product
    (R : Type*) [CommSemiring R] [TopologicalSpace R] [T2Space R] :
    PartIV.Ch19.partitionGenFun R =
      ∏' i, ((1 : R⟦X⟧) + ∑' j, (PowerSeries.X (R := R)) ^ ((i + 1) * (j + 1))) :=
  PartIV.Ch19.partitionGenFun_eq_tprod R

/-- **The geometric-series form of each Euler factor**: in any commutative
ring with a Hausdorff topological structure,
`(1 + ∑' j, X^((i+1)(j+1))) · (1 - X^(i+1)) = 1`.

This is exactly the formal-PS expression of `1/(1 - X^(i+1)) = 1 + X^(i+1)
+ X^(2(i+1)) + …`, so combined with `partitionGenFun_eq_euler_product` it
yields the classical Euler identity `∑ p(n) X^n = ∏' (1 - X^(i+1))⁻¹` in
the formal-PS sense. -/
theorem euler_factor_geometric
    (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
    (i : Nat) :
    ((1 : R⟦X⟧) + ∑' j, (PowerSeries.X (R := R)) ^ ((i + 1) * (j + 1))) *
      ((1 : R⟦X⟧) - PowerSeries.X ^ (i + 1)) = 1 :=
  PartIV.Ch19.factor_geom_series_identity R i

end Ch01
end QseriesFormalization
