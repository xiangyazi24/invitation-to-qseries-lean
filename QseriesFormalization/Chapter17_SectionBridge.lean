import QseriesFormalization.Chapter19_Section5
import QseriesFormalization.Chapter01_GenFun

/-!
# Chapter 17 — Section-operator bridge to general ∀n Ramanujan congruence

This file gives the precise iff-translation between the k-section of
`partitionGenFun (ZMod p)` vanishing and the general `∀ n, p ∣ p(p·n+r)`
Ramanujan congruence statement.

Combined with Pending/Chapter16_MBI.lean (whose formal-PS form, once
proved, directly gives the section vanishing for (p, r) = (5, 4)), this
provides the missing link from MBI to the general Ramanujan ∀n theorem.
-/

namespace QseriesFormalization
namespace PartIV
namespace Ch17

open PowerSeries
open QseriesFormalization.PartIV.Ch19

/-- **Routing lemma**: `section_kr p r (partitionGenFun (ZMod p)) = 0` in
`(ZMod p)⟦X⟧` is equivalent to the general `∀ n, p ∣ p(p·n + r)`
Ramanujan congruence statement.

The forward direction extracts coefficient n from the section, identifies
it with `p(p·n + r)` reduced mod p via `coeff_partitionGenFun` and
naturality `map_partitionGenFun`, and concludes 0.  The reverse builds
the section equal to zero from coefficient-wise vanishing. -/
theorem section_kr_partitionGenFun_eq_zero_iff
    (p : Nat) [Fact (Nat.Prime p)] (r : Nat) :
    section_kr (ZMod p) p r (partitionGenFun (ZMod p)) = 0 ↔
    ∀ n, ((QseriesFormalization.Ch01.partitionCount (p * n + r) : Nat) : ZMod p) = 0 := by
  -- Bridge: coeff (partitionGenFun (ZMod p)) m = partitionCount m as ZMod p.
  have h_pg : ∀ m, PowerSeries.coeff (R := ZMod p) m (partitionGenFun (ZMod p)) =
      ((QseriesFormalization.Ch01.partitionCount m : Nat) : ZMod p) := by
    intro m
    have hmap := map_partitionGenFun (Int.castRingHom (ZMod p))
    have hcoeff_map :
        PowerSeries.coeff (R := ZMod p) m
          (PowerSeries.map (Int.castRingHom (ZMod p)) (partitionGenFun ℤ)) =
        ((QseriesFormalization.Ch01.partitionCount m : Nat) : ZMod p) := by
      rw [PowerSeries.coeff_map, QseriesFormalization.Ch01.coeff_partitionGenFun]
      simp [Int.cast_natCast]
    rw [← hmap]
    exact hcoeff_map
  constructor
  · intro h n
    have hcoeff : PowerSeries.coeff (R := ZMod p) n
        (section_kr (ZMod p) p r (partitionGenFun (ZMod p))) = 0 := by
      rw [h]; simp
    rw [coeff_section_kr, h_pg] at hcoeff
    exact hcoeff
  · intro h
    ext n
    rw [coeff_section_kr, map_zero, h_pg]
    exact h n

/-- **Direct entry point**: from section vanishing of `partitionGenFun (ZMod p)`,
conclude `∀ n, p ∣ p(p·n + r)` over ℕ (not just over ZMod p).

This is a clean restatement of `section_kr_partitionGenFun_eq_zero_iff`'s
forward direction in terms of `Nat.div`-style divisibility.  -/
theorem ramanujan_congruence_from_section_vanishing
    (p : Nat) [Fact (Nat.Prime p)] (r : Nat)
    (h : section_kr (ZMod p) p r (partitionGenFun (ZMod p)) = 0) :
    ∀ n, p ∣ QseriesFormalization.Ch01.partitionCount (p * n + r) := by
  intro n
  have h_iff := (section_kr_partitionGenFun_eq_zero_iff p r).mp h n
  -- h_iff : ((partitionCount (p*n+r) : Nat) : ZMod p) = 0
  -- Use the standard fact: (m : ZMod p) = 0 ↔ p ∣ m (over Nat).
  exact (ZMod.natCast_eq_zero_iff _ p).mp h_iff

end Ch17
end PartIV
end QseriesFormalization
