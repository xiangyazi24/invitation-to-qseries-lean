import Mathlib.RingTheory.PowerSeries.Expand
import QseriesFormalization.Pending.JTP_FormalPS_Pentagonal
import QseriesFormalization.Pending.Chapter17_ASD_Mod5_Full

/-!
# ASD eta-product formal identities

This file records the modulus-25 eta-product identities obtained from the
closed mod-5 formal Jacobi triple product identities by the substitution
`X ↦ X^5`.
-/

namespace QseriesFormalization
namespace Pending
namespace ASDEtaProducts

open PowerSeries
open scoped Topology PowerSeries PowerSeries.WithPiTopology

open JTPFormalPSPentagonal
open QseriesFormalization.PartIV.Ch19

/-! ## Expanding AP products -/

theorem continuous_expand (R : Type*) [CommRing R] [TopologicalSpace R]
    (s : ℕ) (hs : s ≠ 0) :
    Continuous (PowerSeries.expand s hs : R⟦X⟧ → R⟦X⟧) := by
  rw [continuous_iff_continuousAt]
  intro φ
  rw [ContinuousAt, PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
  intro n
  simp_rw [PowerSeries.coeff_expand s hs]
  by_cases hdiv : s ∣ n
  · simpa [hdiv] using (PowerSeries.WithPiTopology.continuous_coeff R (n / s)).tendsto φ
  · simpa [hdiv] using tendsto_const_nhds

/-- Expanding a single AP factor performs the substitution `X ↦ X^s`. -/
theorem expand_apFactorPS (R : Type*) [CommRing R]
    (s : ℕ) (hs : s ≠ 0) (r m n : ℕ) :
    PowerSeries.expand s hs (apFactorPS R r m n) =
      apFactorPS R (s * r) (s * m) n := by
  rw [apFactorPS, apFactorPS, map_sub, map_one, map_pow, PowerSeries.expand_X, ← pow_mul]
  congr 1
  ring

/-- Expanding `(X^r;X^m)_∞` gives `(X^(sr);X^(sm))_∞`. -/
theorem expand_qPochAPPS (R : Type*) [CommRing R] [TopologicalSpace R] [T2Space R]
    (s r m : ℕ) (hs : s ≠ 0) (hm : 0 < m) :
    PowerSeries.expand s hs (qPochAPPS R r m) =
      qPochAPPS R (s * r) (s * m) := by
  unfold qPochAPPS
  rw [(multipliable_apFactorPS R r m hm).map_tprod
    (PowerSeries.expand s hs) (continuous_expand R s hs)]
  exact tprod_congr fun n => expand_apFactorPS R s hs r m n

/-! ## Hirschhorn §3.6.5: the mod-25 F/G eta products -/

/-- Hirschhorn's `F(q^5) = (q^10,q^15,q^25;q^25)_∞`. -/
noncomputable def asd5FProductPS
    (R : Type*) [CommRing R] [TopologicalSpace R] : R⟦X⟧ :=
  qPochAPPS R 10 25 * qPochAPPS R 15 25 * qPochAPPS R 25 25

/-- Hirschhorn's `G(q^5) = (q^5,q^20,q^25;q^25)_∞`. -/
noncomputable def asd5GProductPS
    (R : Type*) [CommRing R] [TopologicalSpace R] : R⟦X⟧ :=
  qPochAPPS R 5 25 * qPochAPPS R 20 25 * qPochAPPS R 25 25

/--
The theta side of `F(q^5)`: the mod-5 `pentagonal023` theta series after
`X ↦ X^5`, i.e. `∑ (-1)^k X^((25k^2 - 5k)/2)`.
-/
noncomputable def asd5FSeriesPS (R : Type*) [CommRing R] : R⟦X⟧ :=
  PowerSeries.expand 5 (by decide) (pentagonal023SeriesPS R)

/--
The theta side of `G(q^5)`: the mod-5 `pentagonal014` theta series after
`X ↦ X^5`, i.e. `∑ (-1)^k X^((25k^2 - 15k)/2)`.
-/
noncomputable def asd5GSeriesPS (R : Type*) [CommRing R] : R⟦X⟧ :=
  PowerSeries.expand 5 (by decide) (pentagonal014SeriesPS R)

@[simp] theorem coeff_asd5FSeriesPS (R : Type*) [CommRing R] (n : ℕ) :
    (asd5FSeriesPS R).coeff n =
      if 5 ∣ n then pentagonal023Coeff R (n / 5) else 0 := by
  rw [asd5FSeriesPS, PowerSeries.coeff_expand]
  by_cases hdiv : 5 ∣ n <;> simp [hdiv]

@[simp] theorem coeff_asd5GSeriesPS (R : Type*) [CommRing R] (n : ℕ) :
    (asd5GSeriesPS R).coeff n =
      if 5 ∣ n then pentagonal014Coeff R (n / 5) else 0 := by
  rw [asd5GSeriesPS, PowerSeries.coeff_expand]
  by_cases hdiv : 5 ∣ n <;> simp [hdiv]

theorem expand_pentagonalProduct023PS
    (R : Type*) [CommRing R] [TopologicalSpace R] [T2Space R] :
    PowerSeries.expand 5 (by decide) (pentagonalProduct023PS R) =
      asd5FProductPS R := by
  unfold pentagonalProduct023PS asd5FProductPS
  rw [map_mul, map_mul]
  rw [expand_qPochAPPS R 5 2 5 (by decide) (by norm_num),
    expand_qPochAPPS R 5 3 5 (by decide) (by norm_num),
    expand_qPochAPPS R 5 5 5 (by decide) (by norm_num)]

theorem expand_pentagonalProduct014PS
    (R : Type*) [CommRing R] [TopologicalSpace R] [T2Space R] :
    PowerSeries.expand 5 (by decide) (pentagonalProduct014PS R) =
      asd5GProductPS R := by
  unfold pentagonalProduct014PS asd5GProductPS
  rw [map_mul, map_mul]
  rw [expand_qPochAPPS R 5 1 5 (by decide) (by norm_num),
    expand_qPochAPPS R 5 4 5 (by decide) (by norm_num),
    expand_qPochAPPS R 5 5 5 (by decide) (by norm_num)]

/-- Formal `F(q^5)` eta-product identity over `ℂ`. -/
theorem asd5FProductPS_eq_asd5FSeriesPS_complex :
    asd5FProductPS ℂ = asd5FSeriesPS ℂ := by
  rw [← expand_pentagonalProduct023PS ℂ]
  unfold asd5FSeriesPS
  rw [pentagonalProduct023PS_eq_pentagonal023SeriesPS_complex]

/-- Formal `G(q^5)` eta-product identity over `ℂ`. -/
theorem asd5GProductPS_eq_asd5GSeriesPS_complex :
    asd5GProductPS ℂ = asd5GSeriesPS ℂ := by
  rw [← expand_pentagonalProduct014PS ℂ]
  unfold asd5GSeriesPS
  rw [pentagonalProduct014PS_eq_pentagonal014SeriesPS_complex]

/-! ## Integral and mod-5 forms of the two JTP product identities -/

private theorem map_pentagonalTripleFactor014PS_int
    (R : Type*) [CommRing R] (n : ℕ) :
    PowerSeries.map (Int.castRingHom R) (pentagonalTripleFactor014PS ℤ n) =
      pentagonalTripleFactor014PS R n := by
  simp [pentagonalTripleFactor014PS, apFactorPS, PowerSeries.map_X]

private theorem map_pentagonalTripleFactor023PS_int
    (R : Type*) [CommRing R] (n : ℕ) :
    PowerSeries.map (Int.castRingHom R) (pentagonalTripleFactor023PS ℤ n) =
      pentagonalTripleFactor023PS R n := by
  simp [pentagonalTripleFactor023PS, apFactorPS, PowerSeries.map_X]

private theorem map_pentagonalProduct014PS_int
    (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] :
    PowerSeries.map (Int.castRingHom R) (pentagonalProduct014PS ℤ) =
      pentagonalProduct014PS R := by
  ext k
  rw [PowerSeries.coeff_map, coeff_pentagonalProduct014PS_eq_coeff_partial ℤ k,
    coeff_pentagonalProduct014PS_eq_coeff_partial R k]
  rw [← PowerSeries.coeff_map]
  congr 1
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro n _hn
  exact map_pentagonalTripleFactor014PS_int R n

private theorem map_pentagonalProduct023PS_int
    (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] :
    PowerSeries.map (Int.castRingHom R) (pentagonalProduct023PS ℤ) =
      pentagonalProduct023PS R := by
  ext k
  rw [PowerSeries.coeff_map, coeff_pentagonalProduct023PS_eq_coeff_partial ℤ k,
    coeff_pentagonalProduct023PS_eq_coeff_partial R k]
  rw [← PowerSeries.coeff_map]
  congr 1
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro n _hn
  exact map_pentagonalTripleFactor023PS_int R n

private theorem map_pentagonal014SeriesPS_int
    (R : Type*) [CommRing R] :
    PowerSeries.map (Int.castRingHom R) (pentagonal014SeriesPS ℤ) =
      pentagonal014SeriesPS R := by
  ext n
  rw [PowerSeries.coeff_map, coeff_pentagonal014SeriesPS, coeff_pentagonal014SeriesPS]
  unfold pentagonal014Coeff
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  by_cases hk : pentagonal014Exp k = n <;> simp [hk, negOnePowInt]

private theorem map_pentagonal023SeriesPS_int
    (R : Type*) [CommRing R] :
    PowerSeries.map (Int.castRingHom R) (pentagonal023SeriesPS ℤ) =
      pentagonal023SeriesPS R := by
  ext n
  rw [PowerSeries.coeff_map, coeff_pentagonal023SeriesPS, coeff_pentagonal023SeriesPS]
  unfold pentagonal023Coeff
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  by_cases hk : pentagonal023Exp k = n <;> simp [hk, negOnePowInt]

/-- Integral form of `(q,q^4,q^5;q^5)_∞ = ∑ (-1)^k q^((5k^2-3k)/2)`. -/
theorem pentagonalProduct014PS_eq_pentagonal014SeriesPS_int :
    pentagonalProduct014PS ℤ = pentagonal014SeriesPS ℤ := by
  ext n
  have h := congrArg (fun φ : ℂ⟦X⟧ => φ.coeff n) (by
    calc
      PowerSeries.map (Int.castRingHom ℂ) (pentagonalProduct014PS ℤ)
          = pentagonalProduct014PS ℂ := map_pentagonalProduct014PS_int ℂ
      _ = pentagonal014SeriesPS ℂ :=
          pentagonalProduct014PS_eq_pentagonal014SeriesPS_complex
      _ = PowerSeries.map (Int.castRingHom ℂ) (pentagonal014SeriesPS ℤ) :=
          (map_pentagonal014SeriesPS_int ℂ).symm)
  exact Int.cast_injective (by simpa [PowerSeries.coeff_map] using h)

/-- Integral form of `(q^2,q^3,q^5;q^5)_∞ = ∑ (-1)^k q^((5k^2-k)/2)`. -/
theorem pentagonalProduct023PS_eq_pentagonal023SeriesPS_int :
    pentagonalProduct023PS ℤ = pentagonal023SeriesPS ℤ := by
  ext n
  have h := congrArg (fun φ : ℂ⟦X⟧ => φ.coeff n) (by
    calc
      PowerSeries.map (Int.castRingHom ℂ) (pentagonalProduct023PS ℤ)
          = pentagonalProduct023PS ℂ := map_pentagonalProduct023PS_int ℂ
      _ = pentagonal023SeriesPS ℂ :=
          pentagonalProduct023PS_eq_pentagonal023SeriesPS_complex
      _ = PowerSeries.map (Int.castRingHom ℂ) (pentagonal023SeriesPS ℤ) :=
          (map_pentagonal023SeriesPS_int ℂ).symm)
  exact Int.cast_injective (by simpa [PowerSeries.coeff_map] using h)

/-- Mod-5 form of `(q,q^4,q^5;q^5)_∞ = ∑ (-1)^k q^((5k^2-3k)/2)`. -/
theorem pentagonalProduct014PS_eq_pentagonal014SeriesPS_zmod5 :
    pentagonalProduct014PS (ZMod 5) = pentagonal014SeriesPS (ZMod 5) := by
  calc
    pentagonalProduct014PS (ZMod 5)
        = PowerSeries.map (Int.castRingHom (ZMod 5)) (pentagonalProduct014PS ℤ) :=
          (map_pentagonalProduct014PS_int (ZMod 5)).symm
    _ = PowerSeries.map (Int.castRingHom (ZMod 5)) (pentagonal014SeriesPS ℤ) := by
          rw [pentagonalProduct014PS_eq_pentagonal014SeriesPS_int]
    _ = pentagonal014SeriesPS (ZMod 5) := map_pentagonal014SeriesPS_int (ZMod 5)

/-- Mod-5 form of `(q^2,q^3,q^5;q^5)_∞ = ∑ (-1)^k q^((5k^2-k)/2)`. -/
theorem pentagonalProduct023PS_eq_pentagonal023SeriesPS_zmod5 :
    pentagonalProduct023PS (ZMod 5) = pentagonal023SeriesPS (ZMod 5) := by
  calc
    pentagonalProduct023PS (ZMod 5)
        = PowerSeries.map (Int.castRingHom (ZMod 5)) (pentagonalProduct023PS ℤ) :=
          (map_pentagonalProduct023PS_int (ZMod 5)).symm
    _ = PowerSeries.map (Int.castRingHom (ZMod 5)) (pentagonal023SeriesPS ℤ) := by
          rw [pentagonalProduct023PS_eq_pentagonal023SeriesPS_int]
    _ = pentagonal023SeriesPS (ZMod 5) := map_pentagonal023SeriesPS_int (ZMod 5)

/-- Formal `F(q^5)` eta-product identity over `ZMod 5`. -/
theorem asd5FProductPS_eq_asd5FSeriesPS_zmod5 :
    asd5FProductPS (ZMod 5) = asd5FSeriesPS (ZMod 5) := by
  rw [← expand_pentagonalProduct023PS (ZMod 5)]
  unfold asd5FSeriesPS
  rw [pentagonalProduct023PS_eq_pentagonal023SeriesPS_zmod5]

/-- Formal `G(q^5)` eta-product identity over `ZMod 5`. -/
theorem asd5GProductPS_eq_asd5GSeriesPS_zmod5 :
    asd5GProductPS (ZMod 5) = asd5GSeriesPS (ZMod 5) := by
  rw [← expand_pentagonalProduct014PS (ZMod 5)]
  unfold asd5GSeriesPS
  rw [pentagonalProduct014PS_eq_pentagonal014SeriesPS_zmod5]

/-!
## Section-to-eta bridge, conditional on the remaining A-section identifications

The hard coefficient-level gap left by this file is the identification
`A 0 = F(q^5)` and `A 1 = -3qG(q^5)` in `ZMod 5`.  The following lemmas
show that once those two identifications are supplied, the section-form ASD
congruences from `Chapter17_ASD_Mod5_Full` immediately rewrite to the
eta-product form.
-/

noncomputable abbrev asd5GShiftedProductPS : (ZMod 5)⟦X⟧ :=
  -(3 : (ZMod 5)⟦X⟧) * PowerSeries.X * asd5GProductPS (ZMod 5)

open QseriesFormalization.Pending.ASDMod5
open QseriesFormalization.Pending.ASDMod5Full
open QseriesFormalization.PartIV.Ch17

private theorem even_int_pentagonal023_num (k : ℤ) :
    Even (k * (5 * k - 1)) := by
  rcases Int.even_or_odd k with hk | hk
  · exact hk.mul_right _
  · refine Even.mul_left ?_ k
    rcases hk with ⟨a, ha⟩
    rw [ha]
    exact ⟨5 * a + 2, by ring⟩

private theorem two_mul_int_pentagonal023_div_two (k : ℤ) :
    2 * (k * (5 * k - 1) / 2) = k * (5 * k - 1) := by
  exact Int.two_mul_ediv_two_of_even (even_int_pentagonal023_num k)

private theorem pentagonal023Exp_injective {a b : ℤ}
    (h : pentagonal023Exp a = pentagonal023Exp b) : a = b := by
  have hcast : ((pentagonal023Exp a : ℕ) : ℤ) =
      ((pentagonal023Exp b : ℕ) : ℤ) := by
    exact_mod_cast h
  rw [int_coe_pentagonal023Exp, int_coe_pentagonal023Exp] at hcast
  have hmul := congrArg (fun z : ℤ => 2 * z) hcast
  change 2 * (a * (5 * a - 1) / 2) =
    2 * (b * (5 * b - 1) / 2) at hmul
  rw [two_mul_int_pentagonal023_div_two,
    two_mul_int_pentagonal023_div_two] at hmul
  have hfac : (a - b) * (5 * (a + b) - 1) = 0 := by
    nlinarith
  have hsecond : 5 * (a + b) - 1 ≠ 0 := by omega
  rcases mul_eq_zero.mp hfac with hab | hbad
  · omega
  · exact (hsecond hbad).elim

private theorem pentagonal023Coeff_eq_of_exp (m : ℕ) (k : ℤ)
    (hk : pentagonal023Exp k = m) :
    pentagonal023Coeff (ZMod 5) m = negOnePowInt (ZMod 5) k := by
  unfold pentagonal023Coeff
  calc
    (∑ l ∈ Finset.Icc (-(m + 1 : ℤ)) (m + 1 : ℤ),
        if pentagonal023Exp l = m then negOnePowInt (ZMod 5) l else 0)
        = (if pentagonal023Exp k = m then negOnePowInt (ZMod 5) k else 0) := by
          apply Finset.sum_eq_single k
          · intro l _hl hlne
            by_cases hleq : pentagonal023Exp l = m
            · have hlk : l = k := pentagonal023Exp_injective (hleq.trans hk.symm)
              exact (hlne hlk).elim
            · simp [hleq]
          · intro hknot
            exact (hknot (pentagonal023Exp_mem_Icc_of_eq hk)).elim
    _ = negOnePowInt (ZMod 5) k := by rw [if_pos hk]

private theorem pentagonal023Coeff_eq_zero_of_no_exp (m : ℕ)
    (h : ∀ k : ℤ, pentagonal023Exp k ≠ m) :
    pentagonal023Coeff (ZMod 5) m = 0 := by
  unfold pentagonal023Coeff
  apply Finset.sum_eq_zero
  intro k _hk
  simp [h k]

private theorem even_nat_mul_five_mul_add_one (a : ℕ) :
    Even (a * (5 * a + 1)) := by
  rcases Nat.even_or_odd a with ha | ha
  · exact ha.mul_right _
  · refine Even.mul_left ?_ a
    rcases ha with ⟨t, ht⟩
    rw [ht]
    exact ⟨5 * t + 3, by ring⟩

private theorem even_nat_mul_five_mul_sub_one (a : ℕ) :
    Even (a * (5 * a - 1)) := by
  rcases Nat.even_or_odd a with ha | ha
  · exact ha.mul_right _
  · refine Even.mul_left ?_ a
    rcases ha with ⟨t, ht⟩
    rw [ht]
    exact ⟨5 * t + 2, by omega⟩

private theorem five_mul_pentagonal023Exp_neg_nat_formula (a : ℕ) :
    5 * (a * (5 * a + 1) / 2) = (5 * a) * (5 * a + 1) / 2 := by
  obtain ⟨q, hq⟩ := even_nat_mul_five_mul_add_one a
  have hprod : (5 * a) * (5 * a + 1) = 5 * (a * (5 * a + 1)) := by ring
  rw [hprod, hq]
  omega

private theorem five_mul_pentagonal023Exp_nat_formula (a : ℕ) :
    5 * (a * (5 * a - 1) / 2) = (5 * a - 1) * (5 * a) / 2 := by
  obtain ⟨q, hq⟩ := even_nat_mul_five_mul_sub_one a
  have hprod : (5 * a - 1) * (5 * a) = 5 * (a * (5 * a - 1)) := by ring
  rw [hprod, hq]
  omega

private theorem pentagonal023Exp_neg_nat (a : ℕ) :
    pentagonal023Exp (-(a : ℤ)) = a * (5 * a + 1) / 2 := by
  rw [← Int.natCast_inj]
  rw [int_coe_pentagonal023Exp]
  norm_num
  ring_nf

private theorem pentagonal023Exp_nat (a : ℕ) :
    pentagonal023Exp (a : ℤ) = a * (5 * a - 1) / 2 := by
  rw [← Int.natCast_inj]
  rw [int_coe_pentagonal023Exp]
  by_cases ha : a = 0
  · simp [ha]
  · have hsub : ((5 * a - 1 : ℕ) : ℤ) = 5 * (a : ℤ) - 1 := by omega
    norm_num
    rw [hsub]

private theorem triangular_index_mod5_eq_zero (j : ℕ)
    (h : (((j * (j + 1) / 2 : ℕ) : ZMod 5) = 0)) :
    j % 5 = 0 ∨ j % 5 = 4 := by
  rw [triangular_cast_eq_triangularMod5] at h
  have hj : (j : ZMod 5) = ((j % 5 : ℕ) : ZMod 5) :=
    natCast_zmod5_eq_mod j
  rw [hj] at h
  have hlt : j % 5 < 5 := Nat.mod_lt j (by decide)
  interval_cases j % 5 <;> simp [triangularMod5] at h ⊢
  all_goals exact absurd h (by decide)

private theorem neg_one_pow_zmod5_five_mul (a : ℕ) :
    (-1 : ZMod 5) ^ (5 * a) = (-1 : ZMod 5) ^ a := by
  rw [show 5 * a = a * 5 by omega, pow_mul]
  rcases Nat.even_or_odd a with ha | ha
  · rw [Even.neg_one_pow ha]
    norm_num
  · rw [Odd.neg_one_pow ha]
    norm_num

private theorem neg_one_pow_zmod5_five_mul_sub_one (a : ℕ) (ha : 0 < a) :
    (-1 : ZMod 5) ^ (5 * a - 1) = -((-1 : ZMod 5) ^ a) := by
  rcases Nat.even_or_odd a with ha_even | ha_odd
  · have ha_even' := ha_even
    rcases ha_even with ⟨t, ht⟩
    have hodd : Odd (5 * a - 1) := by
      refine ⟨5 * t - 1, ?_⟩
      omega
    rw [Even.neg_one_pow ha_even', Odd.neg_one_pow hodd]
  · have ha_odd' := ha_odd
    rcases ha_odd with ⟨t, ht⟩
    have heven : Even (5 * a - 1) := by
      refine ⟨5 * t + 2, ?_⟩
      omega
    rw [Odd.neg_one_pow ha_odd', Even.neg_one_pow heven]
    norm_num

private theorem jacobi_five_mul_sign_zero_family (a : ℕ) :
    ((((-1 : ℤ) ^ (5 * a) * (2 * (5 * a) + 1) : ℤ) : ZMod 5)) =
      negOnePowInt (ZMod 5) (-(a : ℤ)) := by
  simp [negOnePowInt]
  rw [neg_one_pow_zmod5_five_mul a]
  have hcoeff : (2 : ZMod 5) * (5 * (a : ZMod 5)) + 1 = 1 := by
    have h5 : (5 : ZMod 5) = 0 := by decide
    rw [show (5 : ZMod 5) * a = 5 * a by rfl, h5, zero_mul]
    ring
  rw [hcoeff, mul_one]

private theorem jacobi_five_mul_sign_four_family (a : ℕ) (ha : 0 < a) :
    ((((-1 : ℤ) ^ (5 * a - 1) * (2 * (5 * a - 1) + 1) : ℤ) : ZMod 5)) =
      negOnePowInt (ZMod 5) (a : ℤ) := by
  simp [negOnePowInt]
  rw [neg_one_pow_zmod5_five_mul_sub_one a ha]
  have hcoeff : (2 : ZMod 5) * (5 * (a : ZMod 5) - 1) + 1 = -1 := by
    have h5 : (5 : ZMod 5) = 0 := by decide
    rw [h5, zero_mul]
    norm_num
  rw [hcoeff]
  ring

private theorem jacobiTripleSign_five_mul_eq_pentagonal023Coeff_zmod5 (m : ℕ) :
    ((jacobiTripleSign (5 * m) : ℤ) : ZMod 5) =
      pentagonal023Coeff (ZMod 5) m := by
  by_cases htri : ∃ j ≤ 5 * m, 5 * m = j * (j + 1) / 2
  · obtain ⟨j, _hjle, hj⟩ := htri
    rw [hj, jacobiTripleSign_triangular]
    have htri_zmod : (((j * (j + 1) / 2 : ℕ) : ZMod 5) = 0) := by
      rw [← hj]
      push_cast
      change (5 : ZMod 5) * (m : ZMod 5) = 0
      have h5 : (5 : ZMod 5) = 0 := by decide
      rw [h5, zero_mul]
    rcases triangular_index_mod5_eq_zero j htri_zmod with hjmod | hjmod
    · let a := j / 5
      have hj_eq : j = 5 * a := by
        calc
          j = j % 5 + 5 * (j / 5) := (Nat.mod_add_div j 5).symm
          _ = 0 + 5 * a := by rw [hjmod]
          _ = 5 * a := by omega
      have hexp : pentagonal023Exp (-(a : ℤ)) = m := by
        rw [pentagonal023Exp_neg_nat]
        apply Eq.symm
        exact Nat.eq_of_mul_eq_mul_left (n := 5) (by decide) (by
          rw [five_mul_pentagonal023Exp_neg_nat_formula]
          have hj_formula : (5 * a) * (5 * a + 1) / 2 = j * (j + 1) / 2 := by
            rw [← hj_eq]
          rw [hj_formula]
          exact hj)
      rw [pentagonal023Coeff_eq_of_exp m (-(a : ℤ)) hexp]
      rw [hj_eq]
      exact jacobi_five_mul_sign_zero_family a
    · let a := j / 5 + 1
      have ha : 0 < a := by omega
      have hj_eq : j = 5 * a - 1 := by
        calc
          j = j % 5 + 5 * (j / 5) := (Nat.mod_add_div j 5).symm
          _ = 4 + 5 * (j / 5) := by rw [hjmod]
          _ = 5 * a - 1 := by omega
      have hexp : pentagonal023Exp (a : ℤ) = m := by
        rw [pentagonal023Exp_nat]
        apply Eq.symm
        exact Nat.eq_of_mul_eq_mul_left (n := 5) (by decide) (by
          rw [five_mul_pentagonal023Exp_nat_formula]
          have hj_formula : (5 * a - 1) * (5 * a) / 2 = j * (j + 1) / 2 := by
            rw [← hj_eq]
            have hs : 5 * a = j + 1 := by omega
            rw [hs]
          rw [hj_formula]
          exact hj)
      rw [pentagonal023Coeff_eq_of_exp m (a : ℤ) hexp]
      rw [hj_eq]
      have hcast_sub : ((5 * a - 1 : ℕ) : ZMod 5) = 5 * (a : ZMod 5) - 1 := by
        have hs : 5 * a - 1 + 1 = 5 * a := by omega
        have hs_cast : (((5 * a - 1 + 1 : ℕ) : ZMod 5) =
            ((5 * a : ℕ) : ZMod 5)) := by
          exact congrArg (fun n : ℕ => (n : ZMod 5)) hs
        push_cast at hs_cast
        linear_combination hs_cast
      push_cast
      rw [hcast_sub]
      simpa using jacobi_five_mul_sign_four_family a ha
  · push_neg at htri
    rw [jacobiTripleSign_of_not_triangular (5 * m) htri]
    simp only [Int.cast_zero]
    symm
    apply pentagonal023Coeff_eq_zero_of_no_exp
    intro k hk
    cases k with
    | ofNat a =>
        change pentagonal023Exp (a : ℤ) = m at hk
        rw [pentagonal023Exp_nat] at hk
        by_cases ha : a = 0
        · subst a
          simp at hk
          subst m
          exact htri 0 (by simp) (by simp)
        · have hj : 5 * m = (5 * a - 1) * (5 * a) / 2 := by
            rw [← five_mul_pentagonal023Exp_nat_formula, hk]
          have hsucc : 5 * a - 1 + 1 = 5 * a := by omega
          have hjle : 5 * a - 1 ≤ 5 * m := by
            rw [hj]
            rw [← hsucc]
            exact k_le_triangular (5 * a - 1)
          have hjtri : 5 * m = (5 * a - 1) * (5 * a - 1 + 1) / 2 := by
            rwa [hsucc]
          exact htri (5 * a - 1) hjle hjtri
    | negSucc n =>
        let a := n + 1
        have hk' : pentagonal023Exp (-(a : ℤ)) = m := by
          change pentagonal023Exp (Int.negSucc n) = m
          exact hk
        rw [pentagonal023Exp_neg_nat] at hk'
        have hj : 5 * m = (5 * a) * (5 * a + 1) / 2 := by
          rw [← five_mul_pentagonal023Exp_neg_nat_formula, hk']
        have hjle : 5 * a ≤ 5 * m := by
          rw [hj]
          exact k_le_triangular (5 * a)
        exact htri (5 * a) hjle hj

theorem A0_eq_asd5FSeriesPS_zmod5 :
    A 0 = asd5FSeriesPS (ZMod 5) := by
  ext n
  rw [A, coeff_section5]
  by_cases hdiv : 5 ∣ n
  · have hnmod : n % 5 = 0 := Nat.mod_eq_zero_of_dvd hdiv
    rw [if_pos hnmod]
    rw [QseriesFormalization.Pending.JacobiCubeAnalyticToFormal.qPochInfPS_pow_three_eq_jacobiThetaPS,
      coeff_jacobiThetaPS]
    rw [coeff_asd5FSeriesPS, if_pos hdiv]
    have hn : 5 * (n / 5) = n := Nat.mul_div_cancel' hdiv
    calc
      ((jacobiTripleSign n : ℤ) : ZMod 5)
          = ((jacobiTripleSign (5 * (n / 5)) : ℤ) : ZMod 5) := by rw [hn]
      _ = pentagonal023Coeff (ZMod 5) (n / 5) :=
          jacobiTripleSign_five_mul_eq_pentagonal023Coeff_zmod5 (n / 5)
  · have hnmod : n % 5 ≠ 0 := by
      intro hnmod
      exact hdiv (Nat.dvd_of_mod_eq_zero hnmod)
    rw [if_neg hnmod]
    rw [coeff_asd5FSeriesPS, if_neg hdiv]

theorem A0_eq_asd5FProductPS_zmod5 :
    A 0 = asd5FProductPS (ZMod 5) := by
  rw [A0_eq_asd5FSeriesPS_zmod5, asd5FProductPS_eq_asd5FSeriesPS_zmod5]

private theorem even_int_pentagonal014_num (k : ℤ) :
    Even (k * (5 * k - 3)) := by
  rcases Int.even_or_odd k with hk | hk
  · exact hk.mul_right _
  · refine Even.mul_left ?_ k
    rcases hk with ⟨a, ha⟩
    rw [ha]
    exact ⟨5 * a + 1, by ring⟩

private theorem two_mul_int_pentagonal014_div_two (k : ℤ) :
    2 * (k * (5 * k - 3) / 2) = k * (5 * k - 3) := by
  exact Int.two_mul_ediv_two_of_even (even_int_pentagonal014_num k)

private theorem pentagonal014Exp_injective {a b : ℤ}
    (h : pentagonal014Exp a = pentagonal014Exp b) : a = b := by
  have hcast : ((pentagonal014Exp a : ℕ) : ℤ) =
      ((pentagonal014Exp b : ℕ) : ℤ) := by
    exact_mod_cast h
  rw [int_coe_pentagonal014Exp, int_coe_pentagonal014Exp] at hcast
  have hmul := congrArg (fun z : ℤ => 2 * z) hcast
  change 2 * (a * (5 * a - 3) / 2) =
    2 * (b * (5 * b - 3) / 2) at hmul
  rw [two_mul_int_pentagonal014_div_two,
    two_mul_int_pentagonal014_div_two] at hmul
  have hfac : (a - b) * (5 * (a + b) - 3) = 0 := by
    nlinarith
  have hsecond : 5 * (a + b) - 3 ≠ 0 := by omega
  rcases mul_eq_zero.mp hfac with hab | hbad
  · omega
  · exact (hsecond hbad).elim

private theorem pentagonal014Coeff_eq_of_exp (m : ℕ) (k : ℤ)
    (hk : pentagonal014Exp k = m) :
    pentagonal014Coeff (ZMod 5) m = negOnePowInt (ZMod 5) k := by
  unfold pentagonal014Coeff
  calc
    (∑ l ∈ Finset.Icc (-(m + 1 : ℤ)) (m + 1 : ℤ),
        if pentagonal014Exp l = m then negOnePowInt (ZMod 5) l else 0)
        = (if pentagonal014Exp k = m then negOnePowInt (ZMod 5) k else 0) := by
          apply Finset.sum_eq_single k
          · intro l _hl hlne
            by_cases hleq : pentagonal014Exp l = m
            · have hlk : l = k := pentagonal014Exp_injective (hleq.trans hk.symm)
              exact (hlne hlk).elim
            · simp [hleq]
          · intro hknot
            exact (hknot (pentagonal014Exp_mem_Icc_of_eq hk)).elim
    _ = negOnePowInt (ZMod 5) k := by rw [if_pos hk]

private theorem pentagonal014Coeff_eq_zero_of_no_exp (m : ℕ)
    (h : ∀ k : ℤ, pentagonal014Exp k ≠ m) :
    pentagonal014Coeff (ZMod 5) m = 0 := by
  unfold pentagonal014Coeff
  apply Finset.sum_eq_zero
  intro k _hk
  simp [h k]

private theorem even_nat_mul_five_mul_add_three (a : ℕ) :
    Even (a * (5 * a + 3)) := by
  rcases Nat.even_or_odd a with ha | ha
  · exact ha.mul_right _
  · refine Even.mul_left ?_ a
    rcases ha with ⟨t, ht⟩
    rw [ht]
    exact ⟨5 * t + 4, by ring⟩

private theorem even_nat_mul_five_mul_sub_three (a : ℕ) :
    Even (a * (5 * a - 3)) := by
  rcases Nat.even_or_odd a with ha | ha
  · exact ha.mul_right _
  · refine Even.mul_left ?_ a
    rcases ha with ⟨t, ht⟩
    rw [ht]
    exact ⟨5 * t + 1, by omega⟩

private theorem five_mul_pentagonal014Exp_neg_nat_formula (a : ℕ) :
    5 * (a * (5 * a + 3) / 2) + 1 = (5 * a + 1) * (5 * a + 2) / 2 := by
  obtain ⟨q, hq⟩ := even_nat_mul_five_mul_add_three a
  have hprod : (5 * a + 1) * (5 * a + 2) = 5 * (a * (5 * a + 3)) + 2 := by
    ring
  rw [hprod, hq]
  omega

private theorem five_mul_pentagonal014Exp_nat_formula (a : ℕ) (ha : 0 < a) :
    5 * (a * (5 * a - 3) / 2) + 1 = (5 * a - 2) * (5 * a - 1) / 2 := by
  obtain ⟨q, hq⟩ := even_nat_mul_five_mul_sub_three a
  have hprod : (5 * a - 2) * (5 * a - 1) = 5 * (a * (5 * a - 3)) + 2 := by
    apply Nat.cast_injective (R := ℤ)
    push_cast
    have h1 : ((5 * a - 2 : ℕ) : ℤ) = 5 * (a : ℤ) - 2 := by omega
    have h2 : ((5 * a - 1 : ℕ) : ℤ) = 5 * (a : ℤ) - 1 := by omega
    have h3 : ((5 * a - 3 : ℕ) : ℤ) = 5 * (a : ℤ) - 3 := by omega
    rw [h1, h2, h3]
    ring
  rw [hprod, hq]
  omega

private theorem pentagonal014Exp_neg_nat (a : ℕ) :
    pentagonal014Exp (-(a : ℤ)) = a * (5 * a + 3) / 2 := by
  rw [← Int.natCast_inj]
  rw [int_coe_pentagonal014Exp]
  norm_num
  ring_nf

private theorem pentagonal014Exp_nat (a : ℕ) :
    pentagonal014Exp (a : ℤ) = a * (5 * a - 3) / 2 := by
  rw [← Int.natCast_inj]
  rw [int_coe_pentagonal014Exp]
  by_cases ha : a = 0
  · simp [ha]
  · have hsub : ((5 * a - 3 : ℕ) : ℤ) = 5 * (a : ℤ) - 3 := by omega
    norm_num
    rw [hsub]

private theorem triangular_index_mod5_eq_one (j : ℕ)
    (h : (((j * (j + 1) / 2 : ℕ) : ZMod 5) = 1)) :
    j % 5 = 1 ∨ j % 5 = 3 := by
  rw [triangular_cast_eq_triangularMod5] at h
  have hj : (j : ZMod 5) = ((j % 5 : ℕ) : ZMod 5) :=
    natCast_zmod5_eq_mod j
  rw [hj] at h
  have hlt : j % 5 < 5 := Nat.mod_lt j (by decide)
  interval_cases j % 5 <;> simp [triangularMod5] at h ⊢
  all_goals exact absurd h (by decide)

private theorem neg_one_pow_zmod5_five_mul_add_one (a : ℕ) :
    (-1 : ZMod 5) ^ (5 * a + 1) = -((-1 : ZMod 5) ^ a) := by
  rcases Nat.even_or_odd a with ha_even | ha_odd
  · have ha_even' := ha_even
    rcases ha_even with ⟨t, ht⟩
    have hodd : Odd (5 * a + 1) := by
      refine ⟨5 * t, ?_⟩
      omega
    rw [Even.neg_one_pow ha_even', Odd.neg_one_pow hodd]
  · have ha_odd' := ha_odd
    rcases ha_odd with ⟨t, ht⟩
    have heven : Even (5 * a + 1) := by
      refine ⟨5 * t + 3, ?_⟩
      omega
    rw [Odd.neg_one_pow ha_odd', Even.neg_one_pow heven]
    norm_num

private theorem neg_one_pow_zmod5_five_mul_sub_two (a : ℕ) (ha : 0 < a) :
    (-1 : ZMod 5) ^ (5 * a - 2) = (-1 : ZMod 5) ^ a := by
  rcases Nat.even_or_odd a with ha_even | ha_odd
  · have ha_even' := ha_even
    rcases ha_even with ⟨t, ht⟩
    have heven : Even (5 * a - 2) := by
      refine ⟨5 * t - 1, ?_⟩
      omega
    rw [Even.neg_one_pow ha_even', Even.neg_one_pow heven]
  · have ha_odd' := ha_odd
    rcases ha_odd with ⟨t, ht⟩
    have hodd : Odd (5 * a - 2) := by
      refine ⟨5 * t + 1, ?_⟩
      omega
    rw [Odd.neg_one_pow ha_odd', Odd.neg_one_pow hodd]

private theorem jacobi_five_mul_sign_one_family (a : ℕ) :
    ((((-1 : ℤ) ^ (5 * a + 1) * (2 * (5 * a + 1) + 1) : ℤ) : ZMod 5)) =
      -(3 : ZMod 5) * negOnePowInt (ZMod 5) (-(a : ℤ)) := by
  simp [negOnePowInt]
  rw [neg_one_pow_zmod5_five_mul_add_one a]
  have hcoeff : (2 : ZMod 5) * (5 * (a : ZMod 5) + 1) + 1 = 3 := by
    have h5 : (5 : ZMod 5) = 0 := by decide
    rw [h5, zero_mul]
    norm_num
  rw [hcoeff]
  ring

private theorem jacobi_five_mul_sign_three_family (a : ℕ) (ha : 0 < a) :
    ((((-1 : ℤ) ^ (5 * a - 2) * (2 * (5 * a - 2) + 1) : ℤ) : ZMod 5)) =
      -(3 : ZMod 5) * negOnePowInt (ZMod 5) (a : ℤ) := by
  simp [negOnePowInt]
  rw [neg_one_pow_zmod5_five_mul_sub_two a ha]
  have hcoeff : (2 : ZMod 5) * (5 * (a : ZMod 5) - 2) + 1 = -3 := by
    have h5 : (5 : ZMod 5) = 0 := by decide
    rw [h5, zero_mul]
    norm_num
  rw [hcoeff]
  ring

private theorem jacobiTripleSign_five_mul_add_one_eq_pentagonal014Coeff_zmod5
    (m : ℕ) :
    ((jacobiTripleSign (5 * m + 1) : ℤ) : ZMod 5) =
      -(3 : ZMod 5) * pentagonal014Coeff (ZMod 5) m := by
  by_cases htri : ∃ j ≤ 5 * m + 1, 5 * m + 1 = j * (j + 1) / 2
  · obtain ⟨j, _hjle, hj⟩ := htri
    rw [hj, jacobiTripleSign_triangular]
    have htri_zmod : (((j * (j + 1) / 2 : ℕ) : ZMod 5) = 1) := by
      rw [← hj]
      push_cast
      change (5 : ZMod 5) * (m : ZMod 5) + 1 = 1
      have h5 : (5 : ZMod 5) = 0 := by decide
      rw [h5, zero_mul, zero_add]
    rcases triangular_index_mod5_eq_one j htri_zmod with hjmod | hjmod
    · let a := j / 5
      have hj_eq : j = 5 * a + 1 := by
        calc
          j = j % 5 + 5 * (j / 5) := (Nat.mod_add_div j 5).symm
          _ = 1 + 5 * a := by rw [hjmod]
          _ = 5 * a + 1 := by omega
      have hexp : pentagonal014Exp (-(a : ℤ)) = m := by
        rw [pentagonal014Exp_neg_nat]
        apply Eq.symm
        exact Nat.eq_of_mul_eq_mul_left (n := 5) (by decide) (by
          have hformula := five_mul_pentagonal014Exp_neg_nat_formula a
          have hj_formula :
              (5 * a + 1) * (5 * a + 2) / 2 = j * (j + 1) / 2 := by
            rw [← hj_eq]
            have hs : 5 * a + 2 = j + 1 := by omega
            rw [hs]
          omega)
      rw [pentagonal014Coeff_eq_of_exp m (-(a : ℤ)) hexp]
      rw [hj_eq]
      exact jacobi_five_mul_sign_one_family a
    · let a := j / 5 + 1
      have ha : 0 < a := by omega
      have hj_eq : j = 5 * a - 2 := by
        calc
          j = j % 5 + 5 * (j / 5) := (Nat.mod_add_div j 5).symm
          _ = 3 + 5 * (j / 5) := by rw [hjmod]
          _ = 5 * a - 2 := by omega
      have hexp : pentagonal014Exp (a : ℤ) = m := by
        rw [pentagonal014Exp_nat]
        apply Eq.symm
        exact Nat.eq_of_mul_eq_mul_left (n := 5) (by decide) (by
          have hformula := five_mul_pentagonal014Exp_nat_formula a ha
          have hj_formula :
              (5 * a - 2) * (5 * a - 1) / 2 = j * (j + 1) / 2 := by
            rw [← hj_eq]
            have hs : 5 * a - 1 = j + 1 := by omega
            rw [hs]
          omega)
      rw [pentagonal014Coeff_eq_of_exp m (a : ℤ) hexp]
      rw [hj_eq]
      push_cast
      have hcast_sub_two : ((5 * a - 2 : ℕ) : ZMod 5) = 5 * (a : ZMod 5) - 2 := by
        have hs : 5 * a - 2 + 2 = 5 * a := by omega
        have hs_cast : (((5 * a - 2 + 2 : ℕ) : ZMod 5) =
            ((5 * a : ℕ) : ZMod 5)) := by
          exact congrArg (fun n : ℕ => (n : ZMod 5)) hs
        push_cast at hs_cast
        linear_combination hs_cast
      rw [hcast_sub_two]
      simpa using jacobi_five_mul_sign_three_family a ha
  · push_neg at htri
    rw [jacobiTripleSign_of_not_triangular (5 * m + 1) htri]
    simp only [Int.cast_zero]
    have hcoeff_zero : pentagonal014Coeff (ZMod 5) m = 0 := by
      apply pentagonal014Coeff_eq_zero_of_no_exp
      intro k hk
      cases k with
      | ofNat a =>
          change pentagonal014Exp (a : ℤ) = m at hk
          rw [pentagonal014Exp_nat] at hk
          by_cases ha : a = 0
          · subst a
            simp at hk
            subst m
            exact htri 1 (by simp) (by simp)
          · have ha_pos : 0 < a := by omega
            have hj : 5 * m + 1 = (5 * a - 2) * (5 * a - 1) / 2 := by
              rw [← five_mul_pentagonal014Exp_nat_formula a ha_pos, hk]
            have hsucc : 5 * a - 2 + 1 = 5 * a - 1 := by omega
            have hjle : 5 * a - 2 ≤ 5 * m + 1 := by
              rw [hj]
              rw [← hsucc]
              exact k_le_triangular (5 * a - 2)
            have hjtri :
                5 * m + 1 = (5 * a - 2) * (5 * a - 2 + 1) / 2 := by
              rwa [hsucc]
            exact htri (5 * a - 2) hjle hjtri
      | negSucc n =>
          let a := n + 1
          have hk' : pentagonal014Exp (-(a : ℤ)) = m := by
            change pentagonal014Exp (Int.negSucc n) = m
            exact hk
          rw [pentagonal014Exp_neg_nat] at hk'
          have hj : 5 * m + 1 = (5 * a + 1) * (5 * a + 2) / 2 := by
            rw [← five_mul_pentagonal014Exp_neg_nat_formula, hk']
          have hsucc : 5 * a + 1 + 1 = 5 * a + 2 := by omega
          have hjle : 5 * a + 1 ≤ 5 * m + 1 := by
            rw [hj]
            rw [← hsucc]
            exact k_le_triangular (5 * a + 1)
          have hjtri :
              5 * m + 1 = (5 * a + 1) * (5 * a + 1 + 1) / 2 := by
            rwa [hsucc]
          exact htri (5 * a + 1) hjle hjtri
    rw [hcoeff_zero]
    ring

private theorem neg_three_ps_eq_C :
    (-(3 : (ZMod 5)⟦X⟧)) = PowerSeries.C (-(3 : ZMod 5)) := by
  rw [show (3 : (ZMod 5)⟦X⟧) = PowerSeries.C (3 : ZMod 5) by
    exact (map_natCast (PowerSeries.C : ZMod 5 →+* (ZMod 5)⟦X⟧) 3).symm]
  rw [map_neg]

theorem A1_eq_asd5GShiftedSeriesPS_zmod5 :
    A 1 = -(3 : (ZMod 5)⟦X⟧) * PowerSeries.X * asd5GSeriesPS (ZMod 5) := by
  ext n
  cases n with
  | zero =>
      rw [A, coeff_section5]
      simp
  | succ n =>
      rw [A, coeff_section5]
      rw [mul_assoc, neg_three_ps_eq_C, PowerSeries.coeff_C_mul,
        PowerSeries.coeff_succ_X_mul]
      by_cases hres : (n + 1) % 5 = 1
      · rw [if_pos hres]
        rw [QseriesFormalization.Pending.JacobiCubeAnalyticToFormal.qPochInfPS_pow_three_eq_jacobiThetaPS,
          coeff_jacobiThetaPS]
        have hnmod : n % 5 = 0 := by omega
        have hdiv : 5 ∣ n := Nat.dvd_of_mod_eq_zero hnmod
        rw [coeff_asd5GSeriesPS, if_pos hdiv]
        have hn : 5 * (n / 5) = n := Nat.mul_div_cancel' hdiv
        calc
          ((jacobiTripleSign (n + 1) : ℤ) : ZMod 5)
              = ((jacobiTripleSign (5 * (n / 5) + 1) : ℤ) : ZMod 5) := by
                rw [hn]
          _ = -(3 : ZMod 5) * pentagonal014Coeff (ZMod 5) (n / 5) :=
              jacobiTripleSign_five_mul_add_one_eq_pentagonal014Coeff_zmod5 (n / 5)
      · rw [if_neg hres]
        have hnotdiv : ¬ 5 ∣ n := by omega
        rw [coeff_asd5GSeriesPS, if_neg hnotdiv, mul_zero]

theorem A1_eq_asd5GShiftedProductPS_zmod5 :
    A 1 = asd5GShiftedProductPS := by
  rw [A1_eq_asd5GShiftedSeriesPS_zmod5]
  unfold asd5GShiftedProductPS
  rw [asd5GProductPS_eq_asd5GSeriesPS_zmod5]

/-- Conditional eta-product form of the `5n` section congruence. -/
theorem partition_section_0_eq_eta_product_of_A0
    (hA0 : A 0 = asd5FProductPS (ZMod 5)) :
    section_kr (ZMod 5) 5 0 P5 =
      section_kr (ZMod 5) 5 0 ((asd5FProductPS (ZMod 5)) ^ 3) * P5 ^ 2 := by
  rw [partition_section_0_eq_over_Q5_sq]
  unfold N0
  rw [hA0]

/-- Conditional eta-product form of the `5n+1` section congruence. -/
theorem partition_section_1_eq_eta_product_of_A0_A1
    (hA0 : A 0 = asd5FProductPS (ZMod 5))
    (hA1 : A 1 = asd5GShiftedProductPS) :
    section_kr (ZMod 5) 5 1 P5 =
      section_kr (ZMod 5) 5 1
        ((3 : (ZMod 5)⟦X⟧) * (asd5FProductPS (ZMod 5)) ^ 2 *
          asd5GShiftedProductPS) * P5 ^ 2 := by
  rw [partition_section_1_eq_over_Q5_sq]
  unfold N1
  rw [hA0, hA1]

/-- Conditional eta-product form of the `5n+2` section congruence. -/
theorem partition_section_2_eq_eta_product_of_A0_A1
    (hA0 : A 0 = asd5FProductPS (ZMod 5))
    (hA1 : A 1 = asd5GShiftedProductPS) :
    section_kr (ZMod 5) 5 2 P5 =
      section_kr (ZMod 5) 5 2
        ((3 : (ZMod 5)⟦X⟧) * asd5FProductPS (ZMod 5) *
          asd5GShiftedProductPS ^ 2) * P5 ^ 2 := by
  rw [partition_section_2_eq_over_Q5_sq]
  unfold N2
  rw [hA0, hA1]

/-- Conditional eta-product form of the `5n+3` section congruence. -/
theorem partition_section_3_eq_eta_product_of_A1
    (hA1 : A 1 = asd5GShiftedProductPS) :
    section_kr (ZMod 5) 5 3 P5 =
      section_kr (ZMod 5) 5 3 (asd5GShiftedProductPS ^ 3) * P5 ^ 2 := by
  rw [partition_section_3_eq_over_Q5_sq]
  unfold N3
  rw [hA1]

/-- The clean `5n+4` ASD congruence in divided section form. -/
theorem partition_section_4_eq_zero_eta_product :
    section_kr (ZMod 5) 5 4 P5 = 0 :=
  partition_section_4_eq_zero

/-! ### UNCONDITIONAL ASD mod-5 η-quotient congruences (Hirschhorn 3.6.7)

The `A 0 = F`, `A 1 = -3qG` identifications are now theorems
(`A0_eq_asd5FProductPS_zmod5`, `A1_eq_asd5GShiftedProductPS_zmod5`), so the
conditional forms above become unconditional. -/

/-- **ASD `5n`** (unconditional): `∑ p(5n)qⁿ ≡ F(q⁵)³/(q;q)² (mod 5)`, section form. -/
theorem partition_section_0_eq_eta_product :
    section_kr (ZMod 5) 5 0 P5 =
      section_kr (ZMod 5) 5 0 ((asd5FProductPS (ZMod 5)) ^ 3) * P5 ^ 2 :=
  partition_section_0_eq_eta_product_of_A0 A0_eq_asd5FProductPS_zmod5

/-- **ASD `5n+1`** (unconditional). -/
theorem partition_section_1_eq_eta_product :
    section_kr (ZMod 5) 5 1 P5 =
      section_kr (ZMod 5) 5 1
        ((3 : (ZMod 5)⟦X⟧) * (asd5FProductPS (ZMod 5)) ^ 2 *
          asd5GShiftedProductPS) * P5 ^ 2 :=
  partition_section_1_eq_eta_product_of_A0_A1
    A0_eq_asd5FProductPS_zmod5 A1_eq_asd5GShiftedProductPS_zmod5

/-- **ASD `5n+2`** (unconditional). -/
theorem partition_section_2_eq_eta_product :
    section_kr (ZMod 5) 5 2 P5 =
      section_kr (ZMod 5) 5 2
        ((3 : (ZMod 5)⟦X⟧) * asd5FProductPS (ZMod 5) *
          asd5GShiftedProductPS ^ 2) * P5 ^ 2 :=
  partition_section_2_eq_eta_product_of_A0_A1
    A0_eq_asd5FProductPS_zmod5 A1_eq_asd5GShiftedProductPS_zmod5

/-- **ASD `5n+3`** (unconditional). -/
theorem partition_section_3_eq_eta_product :
    section_kr (ZMod 5) 5 3 P5 =
      section_kr (ZMod 5) 5 3 (asd5GShiftedProductPS ^ 3) * P5 ^ 2 :=
  partition_section_3_eq_eta_product_of_A1 A1_eq_asd5GShiftedProductPS_zmod5

end ASDEtaProducts
end Pending
end QseriesFormalization
