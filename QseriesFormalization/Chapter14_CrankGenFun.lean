import QseriesFormalization.Chapter14
import QseriesFormalization.Chapter19

/-!
# Chapter 14 - Crank generating function

This companion file gives a bounded formal-power-series layer for the
Andrews-Garvan crank identity.

Closed here:

* `crankCount m n`, the formal `M(m,n)` fiber count from the existing
  `crank : Nat.Partition n -> Int`.
* `crankGenFunEval R z`, the one-variable q-series obtained by evaluating the
  bilateral z-variable at a fixed field element `z`.
* the coefficient formula
  `coeff_n = sum_m M(m,n) z^m`, grouped over the finite crank support.
* the `z = 1` specialization: the crank series is the ordinary partition
  generating function, hence satisfies the product/inverse identity already
  proved in Chapter 19.

The full bilateral Laurent-series identity for arbitrary `z` is stated as a
Prop (`andrewsGarvanCrankIdentityStatement`) but is not proved here.
-/

open scoped BigOperators
open scoped PowerSeries.WithPiTopology

namespace QseriesFormalization
namespace PartIII
namespace Ch14

open PowerSeries

noncomputable section

/-! ## The coefficient side `M(m,n)` -/

/-- `M(m,n)`: the number of partitions of `n` whose Andrews-Garvan crank is `m`. -/
def crankCount (m : Int) (n : Nat) : Nat :=
  Fintype.card {lam : Nat.Partition n // crank lam = m}

/-- The finite set of crank values actually attained by partitions of `n`. -/
def crankSupport (n : Nat) : Finset Int :=
  (Finset.univ : Finset (Nat.Partition n)).image (fun lam => crank lam)

/-- Summing all finite crank fibers recovers the number of partitions of `n`. -/
theorem sum_crankCount_eq_partition_card (n : Nat) :
    ∑ m ∈ crankSupport n, crankCount m n = Fintype.card (Nat.Partition n) := by
  classical
  unfold crankSupport crankCount
  rw [Fintype.card,
    Finset.card_eq_sum_card_image (fun lam : Nat.Partition n => crank lam) Finset.univ]
  congr 1
  ext m
  rw [Fintype.card_subtype]

/-! ## Fixed-`z` crank q-series -/

/--
The crank q-series after evaluating the Laurent variable at a field element `z`:

`sum_n (sum_{lambda partition of n} z^(crank lambda)) X^n`.

This is the univariate formal-power-series avatar of
`sum_{n,m} M(m,n) z^m q^n`.
-/
def crankGenFunEval (R : Type*) [Field R] (z : R) : R⟦X⟧ :=
  PowerSeries.mk fun n => ∑ lam : Nat.Partition n, z ^ crank lam

theorem coeff_crankGenFunEval (R : Type*) [Field R] (z : R) (n : Nat) :
    (crankGenFunEval R z).coeff n = ∑ lam : Nat.Partition n, z ^ crank lam := by
  rw [crankGenFunEval, PowerSeries.coeff_mk]

/-- Coefficient form: the `n`-th coefficient is `sum_m M(m,n) z^m`. -/
theorem coeff_crankGenFunEval_eq_crankCount_sum
    (R : Type*) [Field R] (z : R) (n : Nat) :
    (crankGenFunEval R z).coeff n =
      ∑ m ∈ crankSupport n, (crankCount m n : R) * z ^ m := by
  classical
  rw [coeff_crankGenFunEval]
  have hmaps :
      ∀ lam ∈ (Finset.univ : Finset (Nat.Partition n)), crank lam ∈ crankSupport n := by
    intro lam hlam
    exact Finset.mem_image.mpr ⟨lam, hlam, rfl⟩
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset (Nat.Partition n)))
    (t := crankSupport n) (g := fun lam => crank lam) hmaps
    (fun lam => z ^ crank lam)]
  refine Finset.sum_congr rfl ?_
  intro m _hm
  trans ∑ i ∈ (Finset.univ : Finset (Nat.Partition n)).filter (fun i => crank i = m),
      z ^ m
  · apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    rw [hi]
  · simp [crankCount, Fintype.card_subtype, Finset.sum_const]

/-! ## The closed `z = 1` specialization -/

/-- At `z = 1`, the crank q-series counts all partitions. -/
theorem coeff_crankGenFunEval_one (R : Type*) [Field R] (n : Nat) :
    (crankGenFunEval R 1).coeff n = (Fintype.card (Nat.Partition n) : R) := by
  rw [coeff_crankGenFunEval]
  simp

/-- The `z = 1` crank q-series is the ordinary partition generating function. -/
theorem crankGenFunEval_one_eq_partitionGenFun (R : Type*) [Field R] :
    crankGenFunEval R 1 = QseriesFormalization.PartIV.Ch19.partitionGenFun R := by
  ext n
  rw [coeff_crankGenFunEval_one, QseriesFormalization.PartIV.Ch19.coeff_partitionGenFun]

/--
The `z = 1` specialization of the product side
`(q;q)_inf / ((q;q)_inf (q;q)_inf)`, written using the already-proved inverse
`partitionGenFun = (q;q)_inf^{-1}`.
-/
def crankProductRHSAtOne (R : Type*) [CommRing R] : R⟦X⟧ :=
  QseriesFormalization.PartIV.Ch19.qPochInfPS R *
    QseriesFormalization.PartIV.Ch19.partitionGenFun R *
      QseriesFormalization.PartIV.Ch19.partitionGenFun R

theorem crankProductRHSAtOne_eq_partitionGenFun (R : Type*) [CommRing R] :
    crankProductRHSAtOne R = QseriesFormalization.PartIV.Ch19.partitionGenFun R := by
  unfold crankProductRHSAtOne
  rw [QseriesFormalization.PartIV.Ch19.qPochInfPS_mul_partitionGenFun]
  simp

/-- Product identity, closed for the concrete specialization `z = 1`. -/
theorem crankGenFunEval_one_eq_productRHSAtOne (R : Type*) [Field R] :
    crankGenFunEval R 1 = crankProductRHSAtOne R := by
  rw [crankGenFunEval_one_eq_partitionGenFun, crankProductRHSAtOne_eq_partitionGenFun]

/-- Inverse form of the same `z = 1` specialization. -/
theorem crankGenFunEval_one_mul_qPochInfPS (R : Type*) [Field R] :
    crankGenFunEval R 1 * QseriesFormalization.PartIV.Ch19.qPochInfPS R = 1 := by
  rw [crankGenFunEval_one_eq_partitionGenFun,
    QseriesFormalization.PartIV.Ch19.partitionGenFun_mul_qPochInfPS]

/-! ## Product-side statement for arbitrary fixed `z` -/

/-- Formal `(a q; q)_inf = prod_{i >= 0} (1 - a X^(i+1))`. -/
def qPochInfScaled (R : Type*) [CommRing R] [TopologicalSpace R] (a : R) : R⟦X⟧ :=
  ∏' i : Nat, ((1 : R⟦X⟧) - PowerSeries.C a * PowerSeries.X ^ (i + 1))

/--
The fixed-`z` Andrews-Garvan crank identity, with denominators multiplied out:

`C(z,q) (zq;q)_inf (z^{-1}q;q)_inf = (q;q)_inf`.

This file proves this statement only at `z = 1`.
-/
def andrewsGarvanCrankIdentityStatement
    (R : Type*) [Field R] [TopologicalSpace R] (z : R) : Prop :=
  crankGenFunEval R z * (qPochInfScaled R z * qPochInfScaled R z⁻¹) =
    QseriesFormalization.PartIV.Ch19.qPochInfPS R

/-- The scaled product at `a = 1` is the existing formal `(q;q)_inf`. -/
theorem qPochInfScaled_one (R : Type*) [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [T2Space R] :
    qPochInfScaled R 1 = QseriesFormalization.PartIV.Ch19.qPochInfPS R := by
  unfold qPochInfScaled
  rw [QseriesFormalization.PartIV.Ch19.qPochInfPS_eq_tprod]
  congr
  funext i
  simp

/-- Andrews-Garvan product identity with denominators multiplied out, closed at `z = 1`. -/
theorem andrewsGarvanCrankIdentity_at_one
    (R : Type*) [Field R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] :
    andrewsGarvanCrankIdentityStatement R 1 := by
  unfold andrewsGarvanCrankIdentityStatement
  rw [inv_one, qPochInfScaled_one, crankGenFunEval_one_eq_partitionGenFun]
  rw [← mul_assoc, QseriesFormalization.PartIV.Ch19.partitionGenFun_mul_qPochInfPS, one_mul]

/-! ## Finite scalar truncation at `z = 1` -/

variable {R : Type*} [Field R]

/-- In the finite scalar truncation, the denominator at `z = 1` is `(q;q)_N^2`. -/
theorem crankGenDenominatorTrunc_at_one (q : R) (N : Nat) :
    crankGenDenominatorTrunc (1 : R) q N = qPochhammer q N * qPochhammer q N := by
  simp [crankGenDenominatorTrunc]

/-- Consequently the finite scalar quotient at `z = 1` is `1 / (q;q)_N` when defined. -/
theorem crankGenTrunc_at_one_of_qPochhammer_ne_zero (q : R) (N : Nat)
    (h : qPochhammer q N ≠ 0) :
    crankGenTrunc (1 : R) q N = (qPochhammer q N)⁻¹ := by
  unfold crankGenTrunc crankGenNumeratorTrunc
  rw [crankGenDenominatorTrunc_at_one]
  field_simp [h]

end

end Ch14
end PartIII
end QseriesFormalization
