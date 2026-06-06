import QseriesFormalization.Chapter19

/-!
# Chapter 19 — k-sections of power series (foundation for MBI / general Ramanujan)

To prove `∀ n, 5 ∣ p(5n+4)` and the other Ramanujan congruence families
unconditionally, we need Hirschhorn-style algebra on (ZMod p)⟦X⟧ that
extracts the coefficients in a fixed residue class.  The natural tool is
the **k-section operator** at residue r:

  section_kr φ := mk (fun n => coeff φ (k·n + r))

This file defines that operator and proves its basic algebraic properties.
These are foundation lemmas for the MBI proof (Pending/Chapter16_MBI.lean)
and for discharging the formal-PS vanishing hypothesis needed by Chapter
19's `ramanujan_from_pochInf_vanishes`.

All theorems in this file are unconditional (no sorry, no axiom beyond
the core three).
-/

namespace QseriesFormalization
namespace PartIV
namespace Ch19

open PowerSeries

/-- **k-section at residue r** of a power series.

`section_kr R k r φ` is the power series whose `n`-th coefficient is the
`(k·n + r)`-th coefficient of `φ`. -/
noncomputable def section_kr (R : Type*) [CommSemiring R] (k r : ℕ)
    (φ : PowerSeries R) : PowerSeries R :=
  PowerSeries.mk (fun n => PowerSeries.coeff (R := R) (k * n + r) φ)

@[simp]
theorem coeff_section_kr (R : Type*) [CommSemiring R] (k r n : ℕ)
    (φ : PowerSeries R) :
    PowerSeries.coeff (R := R) n (section_kr R k r φ) =
      PowerSeries.coeff (R := R) (k * n + r) φ := by
  unfold section_kr
  exact PowerSeries.coeff_mk n _

/-- The k-section is additive in the input. -/
theorem section_kr_add (R : Type*) [CommSemiring R] (k r : ℕ)
    (φ ψ : PowerSeries R) :
    section_kr R k r (φ + ψ) = section_kr R k r φ + section_kr R k r ψ := by
  ext n
  rw [coeff_section_kr, map_add, map_add, coeff_section_kr, coeff_section_kr]

/-- For `0 < r < k` and `k ≠ 0`, the k-section at residue r of `expand k _`
vanishes (because `expand k _` has nonzero coefficients only at multiples
of k, while `k·n + r` for `0 < r < k` is never a multiple of k). -/
theorem section_kr_expand_eq_zero
    (R : Type*) [CommRing R] (k : ℕ) (hk : k ≠ 0) (r : ℕ)
    (hr_pos : 0 < r) (hr : r < k) (φ : PowerSeries R) :
    section_kr R k r (PowerSeries.expand k hk φ) = 0 := by
  ext n
  rw [coeff_section_kr]
  rw [PowerSeries.coeff_expand]
  rw [map_zero]
  split_ifs with h_dvd
  · -- Case k ∣ (k·n + r): impossible because 0 < r < k.
    exfalso
    obtain ⟨q, hq⟩ := h_dvd
    have hk_pos : 0 < k := Nat.pos_of_ne_zero hk
    -- Either q ≤ n or q ≥ n + 1.  Both lead to contradiction.
    by_cases hqn : q ≤ n
    · -- q ≤ n: then k * q ≤ k * n, so r = k * q - k * n ≤ 0, contradicting r > 0.
      have hkq_le : k * q ≤ k * n := Nat.mul_le_mul_left k hqn
      omega
    · -- q ≥ n + 1: then k * q ≥ k * (n + 1) = k * n + k, so r ≥ k, contradicting r < k.
      push_neg at hqn
      have hq_ge : n + 1 ≤ q := hqn
      have hkq_ge : k * (n + 1) ≤ k * q := Nat.mul_le_mul_left k hq_ge
      have : k * n + k ≤ k * q := by linarith [Nat.mul_succ k n]
      omega
  · rfl

/-- **Inverse property of k-section with X^r·expand_k**:
`section_kr R k r (X^r * expand k φ) = φ`.

This is the key fact that lets us extract the residue-r part of any
power series presented in the form `X^r * (something at multiples of k)`.

Concretely: `(X^r * expand k φ).coeff (k·n + r) = (expand k φ).coeff (k·n)
= φ.coeff n`. -/
theorem section_kr_X_pow_mul_expand
    (R : Type*) [CommRing R] (k : ℕ) (hk : k ≠ 0) (r : ℕ) (hr : r < k)
    (φ : PowerSeries R) :
    section_kr R k r ((PowerSeries.X (R := R)) ^ r *
        PowerSeries.expand k hk φ) = φ := by
  ext n
  rw [coeff_section_kr]
  rw [PowerSeries.coeff_X_pow_mul']
  -- Goal: if r ≤ k·n + r then coeff (expand k φ) (k·n + r - r) else 0 = coeff φ n.
  rw [if_pos (by omega)]
  -- Goal: coeff (expand k φ) (k·n + r - r) = coeff φ n
  -- Simplify k·n + r - r = k·n
  have hkn_simp : k * n + r - r = k * n := by omega
  rw [hkn_simp]
  rw [PowerSeries.coeff_expand]
  have hkn_div : k * n / k = n := Nat.mul_div_cancel_left n (Nat.pos_of_ne_zero hk)
  rw [if_pos ⟨n, rfl⟩, hkn_div]

/-- **The constant `5` is zero in `ZMod 5`** — used at the end of the MBI
proof: the RHS prefactor `5 ·` becomes `0 ·`, so the entire RHS vanishes
in (ZMod 5)⟦X⟧.

This is the algebraic mechanism by which Ramanujan's `5 ∣ p(5n+4)` falls
out of MBI: take MBI in (ZMod 5)⟦X⟧, both sides simplify to give
`mk (fun n => p(5n+4)) = 0` in (ZMod 5)⟦X⟧, i.e. `p(5n+4) ≡ 0 (mod 5)`
for all n. -/
theorem five_smul_eq_zero_in_ZMod_five (φ : PowerSeries (ZMod 5)) :
    (5 : ZMod 5) • φ = 0 := by
  have h5 : (5 : ZMod 5) = 0 := by decide
  rw [h5, zero_smul]

end Ch19
end PartIV
end QseriesFormalization
