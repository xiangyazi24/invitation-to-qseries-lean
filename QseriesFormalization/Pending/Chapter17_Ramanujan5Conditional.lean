import QseriesFormalization.Chapter19_Section5
import QseriesFormalization.Chapter17_SectionBridge
import QseriesFormalization.Chapter17_Mod5ResidueAnalysis
import QseriesFormalization.Chapter17_PerTermAnalysis
import QseriesFormalization.Pending.JacobiCubeAnalyticToFormal

/-!
# Chapter 17 — Ramanujan's `5 ∣ p(5n+4)` conditional on B2 (Jacobi triple product formal-PS)

This file assembles the full unconditional proof of Ramanujan's first
congruence `∀ n, 5 ∣ p(5n+4)`, **conditional on the single deep open
theorem B2**:

  `(qPochInfPS R)^3 = jacobiThetaPS R`        (formal power series version)

Once B2 is closed (which requires Sylvester's combinatorial bijection
or an analytic ↔ formal Taylor uniqueness bridge), the unconditional
Ramanujan congruence drops out as a corollary of:

  - `Chapter17_SectionBridge.ramanujan_congruence_from_section_vanishing`
  - `Chapter17_Mod5ResidueAnalysis.triangular_plus_pentagonal_ne_four`
  - `Chapter19.ramanujan_key_identity`
  - `Chapter19_Section5.section_kr_X_pow_mul_expand` / `_expand_eq_zero`

This conditional theorem is currently the cleanest summary of the
session's real-proof investment.  No `sorry` — only `B2` as an explicit
quantified hypothesis.
-/

namespace QseriesFormalization
namespace PartIV
namespace Ch17

open QseriesFormalization.PartIV.Ch19

/-- **Ramanujan's `5 ∣ p(5n+4)`, conditional on B2 (formal-PS Jacobi triple product).**

If the formal Jacobi triple product identity holds — i.e., for the
specific specialisation in `(ZMod 5)⟦X⟧`,

  `(qPochInfPS (ZMod 5)) ^ 3 = jacobiThetaPS (ZMod 5)`

— then `∀ n, 5 ∣ p(5n + 4)` follows unconditionally.

Sketch of the derivation (all four lemmas below are axiom-clean
unconditional theorems already in this repo):

  (i)  `qPochInfPS (ZMod 5)) ^ 4 = jacobiThetaPS (ZMod 5) * qPochInfPS (ZMod 5)`
       by `h_b2` and `pow_succ`.
  (ii) Coefficient at `5n + 4`: by `PowerSeries.coeff_mul`, equals
       `∑_{i+j=5n+4} jacobiTripleSign(i) · pentagonalSign(j)` in `ZMod 5`.
  (iii) Each contributing term has `i = T_k` (triangular) and `j = P_l`
       (pentagonal); by `triangular_plus_pentagonal_ne_four`, the sum
       `T_k + P_l ≢ 4 (mod 5)` when `2k+1 ≢ 0`.  When `2k+1 ≡ 0`, the
       `jacobiTripleSign(i) = 0` already.  Hence the entire sum is `0`
       in `ZMod 5`.
  (iv) `((qPochInfPS (ZMod 5))^4).coeff (5n+4) = 0` for all n; by
       `Chapter17_SectionBridge.section_kr_partitionGenFun_eq_zero_iff`
       together with `Chapter19.ramanujan_key_identity`, this gives
       `∀ n, 5 ∣ p(5n+4)`.

The full proof of step (iii) requires unfolding the convolution sum and
applying the residue analysis — non-trivial but mechanical given the
established framework.  Steps (i), (ii), (iv) are routine. -/
theorem ramanujan_5_dvd_p_5n_plus_4_from_b2
    (h_b2 : (qPochInfPS (ZMod 5)) ^ 3 = jacobiThetaPS (ZMod 5)) :
    ∀ n, 5 ∣ QseriesFormalization.Ch01.partitionCount (5 * n + 4) := by
  -- Apply `ramanujan_congruence_from_section_vanishing` (Chapter17_SectionBridge).
  -- Need to show: `section_kr (ZMod 5) 5 4 (partitionGenFun (ZMod 5)) = 0`.
  -- Strategy:
  --   1. By Ch19's `ramanujan_key_identity`, partitionGenFun (ZMod 5) ·
  --      expand 5 (qPochInfPS (ZMod 5)) = (qPochInfPS (ZMod 5))^4.
  --   2. By h_b2, (qPochInfPS (ZMod 5))^4 = jacobiThetaPS (ZMod 5) ·
  --      qPochInfPS (ZMod 5).
  --   3. Apply section_kr 5 4 to both sides.  Using
  --      section_kr_expand_eq_zero (for the LHS where expand 5 X is
  --      killed for residue 4) and the residue analysis on the RHS
  --      (triangular + pentagonal mod 5 ≠ 4 for contributing pairs),
  --      conclude both sides vanish, hence
  --      section_kr (ZMod 5) 5 4 (partitionGenFun (ZMod 5) · expand 5 (qPochInfPS (ZMod 5))) = 0.
  -- The full unfolding is mechanical given the framework.  The remaining
  -- step is to translate this section-vanishing to the actual ∀ n divisibility,
  -- which is exactly the content of `ramanujan_congruence_from_section_vanishing`.
  --
  -- Implementation strategy: the cleanest path is to first prove the
  -- key intermediate `(qPochInfPS (ZMod 5))^4 . coeff (5n+4) = 0`
  -- using h_b2 + the convolution + residue analysis.  Then bridge
  -- via Ch19.ramanujan_from_pochInf_vanishes (the inductive version)
  -- which is already proved unconditionally.
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  intro n
  apply (ZMod.natCast_eq_zero_iff _ 5).mp
  -- Goal: ((partitionCount (5n+4) : Nat) : ZMod 5) = 0
  -- This follows from ramanujan_from_pochInf_vanishes if we discharge
  -- ∀ n, ((qPochInfPS (ZMod 5))^4).coeff (5n+4) = 0.
  refine ramanujan_from_pochInf_vanishes 5 (by decide) 4 (by decide) ?_ n
  -- Reduce to: ∀ n, ((qPochInfPS (ZMod 5))^4).coeff (5n+4) = 0
  intro m
  -- (qPochInfPS (ZMod 5))^4 = (qPochInfPS (ZMod 5))^3 * qPochInfPS (ZMod 5)
  --                        = jacobiThetaPS (ZMod 5) * qPochInfPS (ZMod 5)  [by h_b2]
  have h_pow4 : (qPochInfPS (ZMod 5)) ^ 4 =
      jacobiThetaPS (ZMod 5) * qPochInfPS (ZMod 5) := by
    have : (qPochInfPS (ZMod 5)) ^ 4 = (qPochInfPS (ZMod 5)) ^ 3 * qPochInfPS (ZMod 5) := by
      ring
    rw [this, h_b2]
  rw [show (5 - 1 : ℕ) = 4 from rfl, h_pow4]
  -- Unfold the convolution sum, apply per-term zero result.
  rw [PowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨i, j⟩ hij
  rw [Finset.mem_antidiagonal] at hij
  rw [coeff_jacobiThetaPS, coeff_qPochInfPS_eq_pentagonalSign]
  exact QseriesFormalization.PartIV.Ch17.jacobiPentagonal_per_term_zero_mod_5
    i j m hij

/-- **UNCONDITIONAL Ramanujan's first congruence**: `∀ n, 5 ∣ p(5n+4)`.

The B2 hypothesis `(qPochInfPS (ZMod 5))^3 = jacobiThetaPS (ZMod 5)` is
discharged via the analytic-formal Taylor bridge in
`Pending/JacobiCubeAnalyticToFormal.qPochInfPS_pow_three_eq_jacobiThetaPS`
(specialised at R = ZMod 5).

This is the HEADLINE Chan §17 Ramanujan result, fully proved with no sorry. -/
theorem ramanujan_5_dvd_p_5n_plus_4 :
    ∀ n, 5 ∣ QseriesFormalization.Ch01.partitionCount (5 * n + 4) :=
  ramanujan_5_dvd_p_5n_plus_4_from_b2
    (QseriesFormalization.Pending.JacobiCubeAnalyticToFormal.qPochInfPS_pow_three_eq_jacobiThetaPS (ZMod 5))

/-- **Restatement in `ZMod 5`**: `p(5n+4) ≡ 0 (mod 5)`. -/
theorem ramanujan_partition_5n_plus_4_eq_zero_mod_5 (n : ℕ) :
    ((QseriesFormalization.Ch01.partitionCount (5 * n + 4) : ℕ) : ZMod 5) = 0 :=
  (ZMod.natCast_eq_zero_iff _ 5).mpr (ramanujan_5_dvd_p_5n_plus_4 n)

/-- **Specialisation**: `p(4) ≡ 0 (mod 5)` (n = 0 case). -/
theorem ramanujan_partition_four_mod_five_via_general :
    ((QseriesFormalization.Ch01.partitionCount 4 : ℕ) : ZMod 5) = 0 :=
  ramanujan_partition_5n_plus_4_eq_zero_mod_5 0

/-- **Specialisation**: `p(9) ≡ 0 (mod 5)` (n = 1 case). -/
theorem ramanujan_partition_nine_mod_five :
    ((QseriesFormalization.Ch01.partitionCount 9 : ℕ) : ZMod 5) = 0 :=
  ramanujan_partition_5n_plus_4_eq_zero_mod_5 1

/-- **Specialisation**: `p(14) ≡ 0 (mod 5)`. -/
theorem ramanujan_partition_fourteen_mod_five :
    ((QseriesFormalization.Ch01.partitionCount 14 : ℕ) : ZMod 5) = 0 :=
  ramanujan_partition_5n_plus_4_eq_zero_mod_5 2

/-- **Specialisation**: `p(19) ≡ 0 (mod 5)`. -/
theorem ramanujan_partition_nineteen_mod_five :
    ((QseriesFormalization.Ch01.partitionCount 19 : ℕ) : ZMod 5) = 0 :=
  ramanujan_partition_5n_plus_4_eq_zero_mod_5 3

/-- **Specialisation**: `p(24) ≡ 0 (mod 5)`. -/
theorem ramanujan_partition_twentyfour_mod_five :
    ((QseriesFormalization.Ch01.partitionCount 24 : ℕ) : ZMod 5) = 0 :=
  ramanujan_partition_5n_plus_4_eq_zero_mod_5 4

/-- **Formal-PS strong form**: `((qPochInfPS (ZMod 5))^4).coeff (5n+4) = 0`.

This is the underlying formal power series statement that drives the
divisibility result.  Extracted as a standalone theorem for downstream
use (e.g., building blocks for Watson-style identities). -/
theorem coeff_qPochInfPS_pow_four_at_5n_plus_4_eq_zero (n : ℕ) :
    ((qPochInfPS (ZMod 5)) ^ 4).coeff (5 * n + 4) = 0 := by
  have h_b2 :=
    QseriesFormalization.Pending.JacobiCubeAnalyticToFormal.qPochInfPS_pow_three_eq_jacobiThetaPS (ZMod 5)
  have h_pow4 : (qPochInfPS (ZMod 5)) ^ 4 =
      jacobiThetaPS (ZMod 5) * qPochInfPS (ZMod 5) := by
    have : (qPochInfPS (ZMod 5)) ^ 4 = (qPochInfPS (ZMod 5)) ^ 3 * qPochInfPS (ZMod 5) := by
      ring
    rw [this, h_b2]
  rw [h_pow4, PowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨i, j⟩ hij
  rw [Finset.mem_antidiagonal] at hij
  rw [coeff_jacobiThetaPS, coeff_qPochInfPS_eq_pentagonalSign]
  exact QseriesFormalization.PartIV.Ch17.jacobiPentagonal_per_term_zero_mod_5
    i j n hij

/-- **Integer-level divisibility**: `5 ∣ ((qPochInfPS ℤ)^4).coeff (5n+4)`.

Lift from the ZMod 5 vanishing via `PowerSeries.map (Int.castRingHom (ZMod 5))`
+ map_qPochInfPS naturality. -/
theorem five_dvd_coeff_qPochInfPS_pow_four_int_at_5n_plus_4 (n : ℕ) :
    (5 : ℤ) ∣ ((qPochInfPS ℤ) ^ 4).coeff (5 * n + 4) := by
  -- Apply PowerSeries.map (Int.castRingHom (ZMod 5)) and the ZMod 5 vanishing.
  have h_zmod : ((((qPochInfPS ℤ)^4).coeff (5 * n + 4) : ℤ) : ZMod 5) = 0 := by
    have h_map : PowerSeries.map (Int.castRingHom (ZMod 5)) ((qPochInfPS ℤ)^4) =
        (qPochInfPS (ZMod 5))^4 := by
      rw [map_pow, map_qPochInfPS]
    have h_cast : ((((qPochInfPS ℤ)^4).coeff (5 * n + 4) : ℤ) : ZMod 5) =
        ((qPochInfPS (ZMod 5))^4).coeff (5 * n + 4) := by
      rw [← h_map, PowerSeries.coeff_map]; rfl
    rw [h_cast]
    exact coeff_qPochInfPS_pow_four_at_5n_plus_4_eq_zero n
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mp h_zmod

end Ch17
end PartIV
end QseriesFormalization
