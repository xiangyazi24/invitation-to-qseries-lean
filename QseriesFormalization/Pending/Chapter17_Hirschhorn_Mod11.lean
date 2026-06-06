import QseriesFormalization.Chapter19_JacobiTripleSignChar
import QseriesFormalization.Chapter17_Mod11PerTermAnalysis
import QseriesFormalization.Pending.Chapter17_Ramanujan5Conditional
import QseriesFormalization.Pending.Chapter17_Ramanujan7
import QseriesFormalization.Pending.JacobiCubeAnalyticToFormal
import QseriesFormalization.Pending.Chapter17_Hirschhorn_Combination

/-!
# Chapter 17 — Hirschhorn's elementary proof of `∀ n, 11 ∣ p(11n + 6)`

Following Hirschhorn (2014), *J. Number Theory* **139**, 205–209, and
*The Power of q* (Springer 2017) §3.5.

**Strategy** (entirely in `ZMod 11` formal power series):

1. Decompose `(qPoch ZMod 11)^3` into 11-residue parts `J_0, J_1, J_3, J_6, J_{10}`:
   By B2 (Jacobi cube identity) `(qPoch)^3 = ∑ (-1)^k (2k+1) X^{T_k}`.
   `T_k mod 11 ∈ {0, 1, 3, 6, 10}` after excluding `k ≡ 5 mod 11` (where the
   coefficient `2k+1 ≡ 0 mod 11`).
   Hence `(qPoch ZMod 11)^3 = J_0 + J_1 + J_3 + J_6 + J_10` where `J_i` keeps
   only terms with exponent `≡ i (mod 11)`.

2. Frobenius lift: `1/(qPoch ZMod 11) = (qPoch)^{21}/(qPoch)^{22}`.
   `(qPoch)^{22} = ((qPoch)^{11})^2 = (expand 11 qPoch)^2` (Frobenius).
   `(qPoch)^{21} = ((qPoch)^3)^7 = (J_0+J_1+J_3+J_6+J_{10})^7`.
   So `partitionGenFun ZMod 11 ≡ (J_0+J_1+J_3+J_6+J_{10})^7 / (expand 11 qPoch ZMod 11)^2`.

3. Extract coefficient of `X^{11n+6}` from LHS = `partitionCount (11n+6) mod 11`.
   From RHS = sum P of `J_a J_b J_c J_d J_e J_f J_g` monomials with total
   exponent ≡ 6 mod 11, divided by `(expand 11 qPoch)^2`.

4. **Key trick** (Hirschhorn): `(J_0+J_1+J_3+J_6+J_{10})^4 = ((qPoch)^3)^4 =
   (qPoch)^{12} = (qPoch)^{11} · qPoch ≡ (expand 11 qPoch) · qPoch (mod 11)`.

5. `(expand 11 qPoch) · qPoch` has non-zero coefficients only at exponents whose
   mod-11 residue is in `{pentagonal mod 11} = {0, 1, 2, 4, 5, 7}`.
   So residues `{3, 6, 8, 9, 10}` give zero coefficient.

6. Equating with LHS expansion of `(J_0+J_1+J_3+J_6+J_{10})^4`, we get 5 polynomial
   relations among `J_i`-monomials (one for each forbidden residue).

7. Hirschhorn shows the residue-6 monomial sum `P` (after the 7th-power expansion)
   is a `Z`-linear combination of these 5 relations with explicit multipliers
   `a = 7, b = 5, c = 7`.  Hence `P ≡ 0 (mod 11)`.

**This file is a SCAFFOLD with intermediate sorries**.  The structure is set
up; closing each step is concrete algebraic work but requires writing out the
30+ monomial expansion explicitly.
-/

namespace QseriesFormalization
namespace Pending
namespace Hirschhorn11

open PowerSeries
open QseriesFormalization.PartIV.Ch19

/-- The 11-residue section of a formal power series over `R`: keep only
coefficients at indices `≡ r (mod 11)`, set the rest to 0. -/
noncomputable def section11 (R : Type*) [CommRing R] (r : ℕ) (φ : R⟦X⟧) : R⟦X⟧ :=
  PowerSeries.mk (fun n => if n % 11 = r then φ.coeff n else 0)

/-- Coefficient of an 11-section. -/
@[simp] theorem coeff_section11 (R : Type*) [CommRing R] (r : ℕ) (φ : R⟦X⟧) (n : ℕ) :
    (section11 R r φ).coeff n = if n % 11 = r then φ.coeff n else 0 := by
  rw [section11, PowerSeries.coeff_mk]

/-- **Section decomposition**: any power series equals the sum of its 11 residue
sections.  `φ = Σ_{r=0}^{10} section11 r φ`.  This is the algebraic backbone of
Hirschhorn's residue bookkeeping. -/
theorem sum_section11_eq (R : Type*) [CommRing R] (φ : R⟦X⟧) :
    ∑ r ∈ Finset.range 11, section11 R r φ = φ := by
  ext n
  rw [map_sum]
  simp only [coeff_section11]
  -- Exactly one r ∈ range 11 matches n % 11; that term is φ.coeff n, rest are 0.
  rw [Finset.sum_ite_eq (Finset.range 11) (n % 11) (fun _ => φ.coeff n)]
  have : n % 11 ∈ Finset.range 11 := Finset.mem_range.mpr (Nat.mod_lt n (by decide))
  simp [this]

/-- An 11-section is supported only on indices with the given residue:
its coefficient is 0 whenever `n % 11 ≠ r`. -/
theorem coeff_section11_of_ne (R : Type*) [CommRing R] (r : ℕ) (φ : R⟦X⟧)
    (n : ℕ) (h : n % 11 ≠ r) : (section11 R r φ).coeff n = 0 := by
  rw [coeff_section11, if_neg h]

/-- **Residue addition under multiplication**: the product of an `r`-section and
an `s`-section is supported only on residue `(r + s) % 11`.

This is the formal statement that "`J_a · J_b` lives on residue `a+b`", the
combinatorial engine of Hirschhorn's §3.5 monomial bookkeeping. -/
theorem coeff_section11_mul_section11_of_ne (R : Type*) [CommRing R]
    (r s : ℕ) (φ ψ : R⟦X⟧) (n : ℕ) (h : n % 11 ≠ (r + s) % 11) :
    (section11 R r φ * section11 R s ψ).coeff n = 0 := by
  rw [PowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨i, j⟩ hij
  rw [Finset.mem_antidiagonal] at hij
  -- If i%11 = r and j%11 = s then n%11 = (i+j)%11 = (r+s)%11, contradiction.
  by_cases hi : i % 11 = r
  · by_cases hj : j % 11 = s
    · exfalso
      apply h
      have : n = i + j := hij.symm
      rw [this, Nat.add_mod, hi, hj]
    · change (section11 R r φ).coeff (i, j).1 * (section11 R s ψ).coeff (i, j).2 = 0
      rw [coeff_section11_of_ne R s ψ j hj, mul_zero]
  · change (section11 R r φ).coeff (i, j).1 * (section11 R s ψ).coeff (i, j).2 = 0
    rw [coeff_section11_of_ne R r φ i hi, zero_mul]

/-- `φ` is supported on one residue class modulo 11. -/
def IsRes {R : Type*} [CommRing R] (r : ℕ) (φ : R⟦X⟧) : Prop :=
  ∀ n, n % 11 ≠ r → φ.coeff n = 0

theorem section11_add (R : Type*) [CommRing R] (r : ℕ) (φ ψ : R⟦X⟧) :
    section11 R r (φ + ψ) = section11 R r φ + section11 R r ψ := by
  ext n
  simp only [coeff_section11, map_add]
  split <;> simp

theorem section11_zero (R : Type*) [CommRing R] (r : ℕ) :
    section11 R r (0 : R⟦X⟧) = 0 := by
  ext n
  simp [coeff_section11]

theorem section11_eq_self_of_isRes {R : Type*} [CommRing R]
    (r : ℕ) {φ : R⟦X⟧} (hφ : IsRes r φ) :
    section11 R r φ = φ := by
  ext n
  rw [coeff_section11]
  by_cases hn : n % 11 = r
  · simp [hn]
  · simp [hn, hφ n hn]

theorem section11_eq_zero_of_isRes {R : Type*} [CommRing R]
    (t r : ℕ) {φ : R⟦X⟧} (htr : t ≠ r) (hφ : IsRes r φ) :
    section11 R t φ = 0 := by
  ext n
  rw [coeff_section11]
  by_cases hn : n % 11 = t
  · have hnr : n % 11 ≠ r := by
      intro h
      exact htr (hn.symm.trans h)
    simp [hn, hφ n hnr]
  · simp [hn]

theorem isRes_section11 {R : Type*} [CommRing R] (r : ℕ) (φ : R⟦X⟧) :
    IsRes r (section11 R r φ) := by
  intro n hn
  exact coeff_section11_of_ne R r φ n hn

theorem isRes_zero {R : Type*} [CommRing R] (r : ℕ) :
    IsRes r (0 : R⟦X⟧) := by
  intro n hn
  simp

theorem isRes_add {R : Type*} [CommRing R] {r : ℕ} {φ ψ : R⟦X⟧}
    (hφ : IsRes r φ) (hψ : IsRes r ψ) :
    IsRes r (φ + ψ) := by
  intro n hn
  rw [map_add, hφ n hn, hψ n hn, zero_add]

theorem isRes_natCast_mul {R : Type*} [CommRing R] (c r : ℕ) {φ : R⟦X⟧}
    (hφ : IsRes r φ) :
    IsRes r ((c : R⟦X⟧) * φ) := by
  intro n hn
  rw [PowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨i, j⟩ hij
  rw [Finset.mem_antidiagonal] at hij
  by_cases hi : i = 0
  · subst hi
    have hj : j = n := by omega
    rw [hj, hφ n hn, mul_zero]
  · have hcoeff : ((c : R⟦X⟧).coeff i) = 0 := by
      rw [show (c : R⟦X⟧) = (PowerSeries.C : R →+* R⟦X⟧) (c : R) by
        exact (map_natCast (PowerSeries.C : R →+* R⟦X⟧) c).symm]
      rw [PowerSeries.coeff_C]
      simp [hi]
    rw [hcoeff, zero_mul]

theorem isRes_mul {R : Type*} [CommRing R] {r s : ℕ} {φ ψ : R⟦X⟧}
    (hφ : IsRes r φ) (hψ : IsRes s ψ) :
    IsRes ((r + s) % 11) (φ * ψ) := by
  intro n hn
  rw [PowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨i, j⟩ hij
  rw [Finset.mem_antidiagonal] at hij
  by_cases hi : i % 11 = r
  · by_cases hj : j % 11 = s
    · exfalso
      apply hn
      rw [← hij, Nat.add_mod, hi, hj]
    · change φ.coeff i * ψ.coeff j = 0
      rw [hψ j hj, mul_zero]
  · change φ.coeff i * ψ.coeff j = 0
    rw [hφ i hi, zero_mul]

theorem isRes_pow {R : Type*} [CommRing R] {r : ℕ} {φ : R⟦X⟧}
    (hφ : IsRes r φ) :
    ∀ m, IsRes ((m * r) % 11) (φ ^ m)
  | 0 => by
      intro n hn
      rw [pow_zero]
      by_cases hn0 : n = 0
      · subst hn0
        simp at hn
      · rw [PowerSeries.coeff_one]
        simp [hn0]
  | m + 1 => by
      have hm := isRes_pow hφ m
      simpa [Nat.succ_mul, Nat.add_mod, Nat.mod_mod, pow_succ]
        using isRes_mul hm hφ

theorem natCast_powerSeries_zmod11_eq_mod (n : ℕ) :
    (n : PowerSeries (ZMod 11)) = ((n % 11 : ℕ) : PowerSeries (ZMod 11)) := by
  rw [show (n : PowerSeries (ZMod 11)) =
      (PowerSeries.C : ZMod 11 →+* PowerSeries (ZMod 11)) (n : ZMod 11) by
        exact (map_natCast (PowerSeries.C : ZMod 11 →+* PowerSeries (ZMod 11)) n).symm]
  rw [show ((n % 11 : ℕ) : PowerSeries (ZMod 11)) =
      (PowerSeries.C : ZMod 11 →+* PowerSeries (ZMod 11)) ((n % 11 : ℕ) : ZMod 11) by
        exact (map_natCast (PowerSeries.C : ZMod 11 →+* PowerSeries (ZMod 11)) (n % 11)).symm]
  congr 1
  conv_lhs => rw [← Nat.mod_add_div n 11]
  push_cast
  have h11 : (11 : ZMod 11) = 0 := by decide
  rw [h11]
  ring

@[simp] theorem zmod11_ps_natCast_12 : (12 : PowerSeries (ZMod 11)) = 1 := by
  change ((12 : ℕ) : PowerSeries (ZMod 11)) = (1 : PowerSeries (ZMod 11))
  rw [natCast_powerSeries_zmod11_eq_mod 12]
  norm_num

@[simp] theorem zmod11_ps_natCast_21 : (21 : PowerSeries (ZMod 11)) = 10 := by
  change ((21 : ℕ) : PowerSeries (ZMod 11)) = (10 : PowerSeries (ZMod 11))
  rw [natCast_powerSeries_zmod11_eq_mod 21]
  norm_num

@[simp] theorem zmod11_ps_natCast_24 : (24 : PowerSeries (ZMod 11)) = 2 := by
  change ((24 : ℕ) : PowerSeries (ZMod 11)) = (2 : PowerSeries (ZMod 11))
  rw [natCast_powerSeries_zmod11_eq_mod 24]
  norm_num

@[simp] theorem zmod11_ps_natCast_140 : (140 : PowerSeries (ZMod 11)) = 8 := by
  change ((140 : ℕ) : PowerSeries (ZMod 11)) = (8 : PowerSeries (ZMod 11))
  rw [natCast_powerSeries_zmod11_eq_mod 140]
  norm_num

@[simp] theorem zmod11_ps_natCast_210 : (210 : PowerSeries (ZMod 11)) = 1 := by
  change ((210 : ℕ) : PowerSeries (ZMod 11)) = (1 : PowerSeries (ZMod 11))
  rw [natCast_powerSeries_zmod11_eq_mod 210]
  norm_num

@[simp] theorem zmod11_ps_natCast_420 : (420 : PowerSeries (ZMod 11)) = 2 := by
  change ((420 : ℕ) : PowerSeries (ZMod 11)) = (2 : PowerSeries (ZMod 11))
  rw [natCast_powerSeries_zmod11_eq_mod 420]
  norm_num

@[simp] theorem zmod11_ps_natCast_630 : (630 : PowerSeries (ZMod 11)) = 3 := by
  change ((630 : ℕ) : PowerSeries (ZMod 11)) = (3 : PowerSeries (ZMod 11))
  rw [natCast_powerSeries_zmod11_eq_mod 630]
  norm_num

/-- `J_i` for `i ∈ {0, 1, 3, 6, 10}`: the 11-residue components of
`(qPoch ZMod 11)^3` whose mod-11 residue gives non-zero jacobiTripleSign mod 11. -/
noncomputable def J (i : ℕ) : (ZMod 11)⟦X⟧ :=
  section11 (ZMod 11) i ((qPochInfPS (ZMod 11))^3)

theorem isRes_J (i : ℕ) : IsRes i (J i) := by
  exact isRes_section11 i ((qPochInfPS (ZMod 11))^3)

noncomputable def JMon (a b c d e : ℕ) : (ZMod 11)⟦X⟧ :=
  ((((J 0)^a * (J 1)^b) * (J 3)^c) * (J 6)^d) * (J 10)^e

def JMonRes (a b c d e : ℕ) : ℕ :=
  (((((a * 0) % 11 + (b * 1) % 11) % 11 + (c * 3) % 11) % 11 +
      (d * 6) % 11) % 11 + (e * 10) % 11) % 11

noncomputable def JTerm (coeff a b c d e : ℕ) : (ZMod 11)⟦X⟧ :=
  (coeff : (ZMod 11)⟦X⟧) * JMon a b c d e

theorem isRes_JMon (a b c d e : ℕ) :
    IsRes (JMonRes a b c d e) (JMon a b c d e) := by
  have h0 := isRes_pow (isRes_J 0) a
  have h1 := isRes_pow (isRes_J 1) b
  have h3 := isRes_pow (isRes_J 3) c
  have h6 := isRes_pow (isRes_J 6) d
  have h10 := isRes_pow (isRes_J 10) e
  simpa [JMon, JMonRes] using
    isRes_mul (isRes_mul (isRes_mul (isRes_mul h0 h1) h3) h6) h10

theorem isRes_JTerm (coeff a b c d e : ℕ) :
    IsRes (JMonRes a b c d e) (JTerm coeff a b c d e) := by
  simpa [JTerm] using isRes_natCast_mul (R := ZMod 11) coeff
    (JMonRes a b c d e) (isRes_JMon a b c d e)

@[simp] theorem section11_JTerm (target coeff a b c d e : ℕ) :
    section11 (ZMod 11) target (JTerm coeff a b c d e) =
      if target = JMonRes a b c d e then JTerm coeff a b c d e else 0 := by
  by_cases h : target = JMonRes a b c d e
  · rw [if_pos h, h]
    exact section11_eq_self_of_isRes (JMonRes a b c d e)
      (isRes_JTerm coeff a b c d e)
  · rw [if_neg h]
    exact section11_eq_zero_of_isRes target (JMonRes a b c d e) h
      (isRes_JTerm coeff a b c d e)

noncomputable def JSum : (ZMod 11)⟦X⟧ :=
  J 0 + J 1 + J 3 + J 6 + J 10

noncomputable def H11_R3 : (ZMod 11)⟦X⟧ :=
  4*(J 0)^3*(J 3) + 2*(J 0)*(J 1)*(J 3)*(J 10) + 4*(J 0)*(J 1)^3
    + 4*(J 6)*(J 10)^3 + (J 3)*(J 6)^2*(J 10) + 6*(J 1)^2*(J 6)^2

noncomputable def H11_R6 : (ZMod 11)⟦X⟧ :=
  4*(J 0)^3*(J 6) + 6*(J 0)^2*(J 3)^2 + 2*(J 0)*(J 1)*(J 6)*(J 10)
    + 4*(J 6)^3*(J 10) + (J 1)*(J 3)^2*(J 10) + 4*(J 1)^3*(J 3)

noncomputable def H11_R8 : (ZMod 11)⟦X⟧ :=
  4*(J 0)*(J 10)^3 + 2*(J 0)*(J 3)*(J 6)*(J 10) + (J 0)*(J 1)^2*(J 6)
    + 4*(J 3)^3*(J 10) + 4*(J 1)*(J 6)^3 + 6*(J 1)^2*(J 3)^2

noncomputable def H11_R9 : (ZMod 11)⟦X⟧ :=
  6*(J 0)^2*(J 10)^2 + (J 0)^2*(J 3)*(J 6) + 4*(J 0)*(J 3)^3
    + 4*(J 1)*(J 10)^3 + 2*(J 1)*(J 3)*(J 6)*(J 10) + 4*(J 1)^3*(J 6)

noncomputable def H11_R10 : (ZMod 11)⟦X⟧ :=
  4*(J 0)^3*(J 10) + (J 0)*(J 1)*(J 10)^2 + 2*(J 0)*(J 1)*(J 3)*(J 6)
    + 6*(J 6)^2*(J 10)^2 + 4*(J 3)*(J 6)^3 + 4*(J 1)*(J 3)^3

noncomputable def H11_P : (ZMod 11)⟦X⟧ :=
  7*(J 0)^6*(J 6) + 10*(J 0)^5*(J 3)^2 + (J 0)^4*(J 1)*(J 6)*(J 10)
    + 8*(J 0)^3*(J 6)^3*(J 10) + 2*(J 0)^3*(J 1)*(J 3)^2*(J 10)
    + 8*(J 0)^3*(J 1)^3*(J 3) + 10*(J 0)^2*(J 10)^5
    + 2*(J 0)^2*(J 3)*(J 6)*(J 10)^3 + 3*(J 0)^2*(J 3)^2*(J 6)^2*(J 10)
    + 3*(J 0)^2*(J 1)^2*(J 6)*(J 10)^2 + 3*(J 0)^2*(J 1)^2*(J 3)*(J 6)^2
    + 8*(J 0)*(J 3)^3*(J 10)^3 + (J 0)*(J 3)^4*(J 6)*(J 10)
    + 2*(J 0)*(J 1)*(J 6)^3*(J 10)^2 + (J 0)*(J 1)*(J 3)*(J 6)^4
    + 3*(J 0)*(J 1)^2*(J 3)^2*(J 10)^2 + 2*(J 0)*(J 1)^2*(J 3)^3*(J 6)
    + (J 0)*(J 1)^4*(J 3)*(J 10) + 7*(J 0)*(J 1)^6
    + 10*(J 6)^5*(J 10)^2 + 7*(J 3)*(J 6)^6 + 7*(J 3)^6*(J 10)
    + 7*(J 1)*(J 10)^6 + (J 1)*(J 3)*(J 6)*(J 10)^4
    + 3*(J 1)*(J 3)^2*(J 6)^2*(J 10)^2 + 8*(J 1)*(J 3)^3*(J 6)^3
    + 10*(J 1)^2*(J 3)^5 + 8*(J 1)^3*(J 6)*(J 10)^3
    + 2*(J 1)^3*(J 3)*(J 6)^2*(J 10) + 10*(J 1)^5*(J 6)^2

set_option maxHeartbeats 4000000 in
theorem JSum_pow_four_expansion :
    JSum ^ 4 =
      JTerm 1 4 0 0 0 0 + JTerm 4 3 1 0 0 0 + JTerm 4 3 0 1 0 0 + JTerm 4 3 0 0 1 0 + JTerm 4 3 0 0 0 1
      + JTerm 6 2 2 0 0 0 + JTerm 12 2 1 1 0 0 + JTerm 12 2 1 0 1 0 + JTerm 12 2 1 0 0 1 + JTerm 6 2 0 2 0 0
      + JTerm 12 2 0 1 1 0 + JTerm 12 2 0 1 0 1 + JTerm 6 2 0 0 2 0 + JTerm 12 2 0 0 1 1 + JTerm 6 2 0 0 0 2
      + JTerm 4 1 3 0 0 0 + JTerm 12 1 2 1 0 0 + JTerm 12 1 2 0 1 0 + JTerm 12 1 2 0 0 1 + JTerm 12 1 1 2 0 0
      + JTerm 24 1 1 1 1 0 + JTerm 24 1 1 1 0 1 + JTerm 12 1 1 0 2 0 + JTerm 24 1 1 0 1 1 + JTerm 12 1 1 0 0 2
      + JTerm 4 1 0 3 0 0 + JTerm 12 1 0 2 1 0 + JTerm 12 1 0 2 0 1 + JTerm 12 1 0 1 2 0 + JTerm 24 1 0 1 1 1
      + JTerm 12 1 0 1 0 2 + JTerm 4 1 0 0 3 0 + JTerm 12 1 0 0 2 1 + JTerm 12 1 0 0 1 2 + JTerm 4 1 0 0 0 3
      + JTerm 1 0 4 0 0 0 + JTerm 4 0 3 1 0 0 + JTerm 4 0 3 0 1 0 + JTerm 4 0 3 0 0 1 + JTerm 6 0 2 2 0 0
      + JTerm 12 0 2 1 1 0 + JTerm 12 0 2 1 0 1 + JTerm 6 0 2 0 2 0 + JTerm 12 0 2 0 1 1 + JTerm 6 0 2 0 0 2
      + JTerm 4 0 1 3 0 0 + JTerm 12 0 1 2 1 0 + JTerm 12 0 1 2 0 1 + JTerm 12 0 1 1 2 0 + JTerm 24 0 1 1 1 1
      + JTerm 12 0 1 1 0 2 + JTerm 4 0 1 0 3 0 + JTerm 12 0 1 0 2 1 + JTerm 12 0 1 0 1 2 + JTerm 4 0 1 0 0 3
      + JTerm 1 0 0 4 0 0 + JTerm 4 0 0 3 1 0 + JTerm 4 0 0 3 0 1 + JTerm 6 0 0 2 2 0 + JTerm 12 0 0 2 1 1
      + JTerm 6 0 0 2 0 2 + JTerm 4 0 0 1 3 0 + JTerm 12 0 0 1 2 1 + JTerm 12 0 0 1 1 2 + JTerm 4 0 0 1 0 3
      + JTerm 1 0 0 0 4 0 + JTerm 4 0 0 0 3 1 + JTerm 6 0 0 0 2 2 + JTerm 4 0 0 0 1 3 + JTerm 1 0 0 0 0 4 := by
  simp only [JSum, JTerm, JMon]
  ring_nf

set_option maxHeartbeats 4000000 in
theorem section11_JSum_pow_four_eq_R3 :
    section11 (ZMod 11) 3 (JSum ^ 4) = H11_R3 := by
  rw [JSum_pow_four_expansion]
  simp [section11_add, JMonRes]
  simp [H11_R3, JTerm, JMon]
  ring_nf

set_option maxHeartbeats 4000000 in
theorem section11_JSum_pow_four_eq_R6 :
    section11 (ZMod 11) 6 (JSum ^ 4) = H11_R6 := by
  rw [JSum_pow_four_expansion]
  simp [section11_add, JMonRes]
  simp [H11_R6, JTerm, JMon]
  ring_nf

set_option maxHeartbeats 4000000 in
theorem section11_JSum_pow_four_eq_R8 :
    section11 (ZMod 11) 8 (JSum ^ 4) = H11_R8 := by
  rw [JSum_pow_four_expansion]
  simp [section11_add, JMonRes]
  simp [H11_R8, JTerm, JMon]
  ring_nf

set_option maxHeartbeats 4000000 in
theorem section11_JSum_pow_four_eq_R9 :
    section11 (ZMod 11) 9 (JSum ^ 4) = H11_R9 := by
  rw [JSum_pow_four_expansion]
  simp [section11_add, JMonRes]
  simp [H11_R9, JTerm, JMon]
  ring_nf

set_option maxHeartbeats 4000000 in
theorem section11_JSum_pow_four_eq_R10 :
    section11 (ZMod 11) 10 (JSum ^ 4) = H11_R10 := by
  rw [JSum_pow_four_expansion]
  simp [section11_add, JMonRes]
  simp [H11_R10, JTerm, JMon]
  ring_nf

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem JSum_pow_seven_expansion :
    JSum ^ 7 =
      JTerm 1 7 0 0 0 0 + JTerm 7 6 1 0 0 0 + JTerm 7 6 0 1 0 0 + JTerm 7 6 0 0 1 0
      + JTerm 7 6 0 0 0 1 + JTerm 21 5 2 0 0 0 + JTerm 42 5 1 1 0 0 + JTerm 42 5 1 0 1 0
      + JTerm 42 5 1 0 0 1 + JTerm 21 5 0 2 0 0 + JTerm 42 5 0 1 1 0 + JTerm 42 5 0 1 0 1
      + JTerm 21 5 0 0 2 0 + JTerm 42 5 0 0 1 1 + JTerm 21 5 0 0 0 2 + JTerm 35 4 3 0 0 0
      + JTerm 105 4 2 1 0 0 + JTerm 105 4 2 0 1 0 + JTerm 105 4 2 0 0 1 + JTerm 105 4 1 2 0 0
      + JTerm 210 4 1 1 1 0 + JTerm 210 4 1 1 0 1 + JTerm 105 4 1 0 2 0 + JTerm 210 4 1 0 1 1
      + JTerm 105 4 1 0 0 2 + JTerm 35 4 0 3 0 0 + JTerm 105 4 0 2 1 0 + JTerm 105 4 0 2 0 1
      + JTerm 105 4 0 1 2 0 + JTerm 210 4 0 1 1 1 + JTerm 105 4 0 1 0 2 + JTerm 35 4 0 0 3 0
      + JTerm 105 4 0 0 2 1 + JTerm 105 4 0 0 1 2 + JTerm 35 4 0 0 0 3 + JTerm 35 3 4 0 0 0
      + JTerm 140 3 3 1 0 0 + JTerm 140 3 3 0 1 0 + JTerm 140 3 3 0 0 1 + JTerm 210 3 2 2 0 0
      + JTerm 420 3 2 1 1 0 + JTerm 420 3 2 1 0 1 + JTerm 210 3 2 0 2 0 + JTerm 420 3 2 0 1 1
      + JTerm 210 3 2 0 0 2 + JTerm 140 3 1 3 0 0 + JTerm 420 3 1 2 1 0 + JTerm 420 3 1 2 0 1
      + JTerm 420 3 1 1 2 0 + JTerm 840 3 1 1 1 1 + JTerm 420 3 1 1 0 2 + JTerm 140 3 1 0 3 0
      + JTerm 420 3 1 0 2 1 + JTerm 420 3 1 0 1 2 + JTerm 140 3 1 0 0 3 + JTerm 35 3 0 4 0 0
      + JTerm 140 3 0 3 1 0 + JTerm 140 3 0 3 0 1 + JTerm 210 3 0 2 2 0 + JTerm 420 3 0 2 1 1
      + JTerm 210 3 0 2 0 2 + JTerm 140 3 0 1 3 0 + JTerm 420 3 0 1 2 1 + JTerm 420 3 0 1 1 2
      + JTerm 140 3 0 1 0 3 + JTerm 35 3 0 0 4 0 + JTerm 140 3 0 0 3 1 + JTerm 210 3 0 0 2 2
      + JTerm 140 3 0 0 1 3 + JTerm 35 3 0 0 0 4 + JTerm 21 2 5 0 0 0 + JTerm 105 2 4 1 0 0
      + JTerm 105 2 4 0 1 0 + JTerm 105 2 4 0 0 1 + JTerm 210 2 3 2 0 0 + JTerm 420 2 3 1 1 0
      + JTerm 420 2 3 1 0 1 + JTerm 210 2 3 0 2 0 + JTerm 420 2 3 0 1 1 + JTerm 210 2 3 0 0 2
      + JTerm 210 2 2 3 0 0 + JTerm 630 2 2 2 1 0 + JTerm 630 2 2 2 0 1 + JTerm 630 2 2 1 2 0
      + JTerm 1260 2 2 1 1 1 + JTerm 630 2 2 1 0 2 + JTerm 210 2 2 0 3 0 + JTerm 630 2 2 0 2 1
      + JTerm 630 2 2 0 1 2 + JTerm 210 2 2 0 0 3 + JTerm 105 2 1 4 0 0 + JTerm 420 2 1 3 1 0
      + JTerm 420 2 1 3 0 1 + JTerm 630 2 1 2 2 0 + JTerm 1260 2 1 2 1 1 + JTerm 630 2 1 2 0 2
      + JTerm 420 2 1 1 3 0 + JTerm 1260 2 1 1 2 1 + JTerm 1260 2 1 1 1 2 + JTerm 420 2 1 1 0 3
      + JTerm 105 2 1 0 4 0 + JTerm 420 2 1 0 3 1 + JTerm 630 2 1 0 2 2 + JTerm 420 2 1 0 1 3
      + JTerm 105 2 1 0 0 4 + JTerm 21 2 0 5 0 0 + JTerm 105 2 0 4 1 0 + JTerm 105 2 0 4 0 1
      + JTerm 210 2 0 3 2 0 + JTerm 420 2 0 3 1 1 + JTerm 210 2 0 3 0 2 + JTerm 210 2 0 2 3 0
      + JTerm 630 2 0 2 2 1 + JTerm 630 2 0 2 1 2 + JTerm 210 2 0 2 0 3 + JTerm 105 2 0 1 4 0
      + JTerm 420 2 0 1 3 1 + JTerm 630 2 0 1 2 2 + JTerm 420 2 0 1 1 3 + JTerm 105 2 0 1 0 4
      + JTerm 21 2 0 0 5 0 + JTerm 105 2 0 0 4 1 + JTerm 210 2 0 0 3 2 + JTerm 210 2 0 0 2 3
      + JTerm 105 2 0 0 1 4 + JTerm 21 2 0 0 0 5 + JTerm 7 1 6 0 0 0 + JTerm 42 1 5 1 0 0
      + JTerm 42 1 5 0 1 0 + JTerm 42 1 5 0 0 1 + JTerm 105 1 4 2 0 0 + JTerm 210 1 4 1 1 0
      + JTerm 210 1 4 1 0 1 + JTerm 105 1 4 0 2 0 + JTerm 210 1 4 0 1 1 + JTerm 105 1 4 0 0 2
      + JTerm 140 1 3 3 0 0 + JTerm 420 1 3 2 1 0 + JTerm 420 1 3 2 0 1 + JTerm 420 1 3 1 2 0
      + JTerm 840 1 3 1 1 1 + JTerm 420 1 3 1 0 2 + JTerm 140 1 3 0 3 0 + JTerm 420 1 3 0 2 1
      + JTerm 420 1 3 0 1 2 + JTerm 140 1 3 0 0 3 + JTerm 105 1 2 4 0 0 + JTerm 420 1 2 3 1 0
      + JTerm 420 1 2 3 0 1 + JTerm 630 1 2 2 2 0 + JTerm 1260 1 2 2 1 1 + JTerm 630 1 2 2 0 2
      + JTerm 420 1 2 1 3 0 + JTerm 1260 1 2 1 2 1 + JTerm 1260 1 2 1 1 2 + JTerm 420 1 2 1 0 3
      + JTerm 105 1 2 0 4 0 + JTerm 420 1 2 0 3 1 + JTerm 630 1 2 0 2 2 + JTerm 420 1 2 0 1 3
      + JTerm 105 1 2 0 0 4 + JTerm 42 1 1 5 0 0 + JTerm 210 1 1 4 1 0 + JTerm 210 1 1 4 0 1
      + JTerm 420 1 1 3 2 0 + JTerm 840 1 1 3 1 1 + JTerm 420 1 1 3 0 2 + JTerm 420 1 1 2 3 0
      + JTerm 1260 1 1 2 2 1 + JTerm 1260 1 1 2 1 2 + JTerm 420 1 1 2 0 3 + JTerm 210 1 1 1 4 0
      + JTerm 840 1 1 1 3 1 + JTerm 1260 1 1 1 2 2 + JTerm 840 1 1 1 1 3 + JTerm 210 1 1 1 0 4
      + JTerm 42 1 1 0 5 0 + JTerm 210 1 1 0 4 1 + JTerm 420 1 1 0 3 2 + JTerm 420 1 1 0 2 3
      + JTerm 210 1 1 0 1 4 + JTerm 42 1 1 0 0 5 + JTerm 7 1 0 6 0 0 + JTerm 42 1 0 5 1 0
      + JTerm 42 1 0 5 0 1 + JTerm 105 1 0 4 2 0 + JTerm 210 1 0 4 1 1 + JTerm 105 1 0 4 0 2
      + JTerm 140 1 0 3 3 0 + JTerm 420 1 0 3 2 1 + JTerm 420 1 0 3 1 2 + JTerm 140 1 0 3 0 3
      + JTerm 105 1 0 2 4 0 + JTerm 420 1 0 2 3 1 + JTerm 630 1 0 2 2 2 + JTerm 420 1 0 2 1 3
      + JTerm 105 1 0 2 0 4 + JTerm 42 1 0 1 5 0 + JTerm 210 1 0 1 4 1 + JTerm 420 1 0 1 3 2
      + JTerm 420 1 0 1 2 3 + JTerm 210 1 0 1 1 4 + JTerm 42 1 0 1 0 5 + JTerm 7 1 0 0 6 0
      + JTerm 42 1 0 0 5 1 + JTerm 105 1 0 0 4 2 + JTerm 140 1 0 0 3 3 + JTerm 105 1 0 0 2 4
      + JTerm 42 1 0 0 1 5 + JTerm 7 1 0 0 0 6 + JTerm 1 0 7 0 0 0 + JTerm 7 0 6 1 0 0
      + JTerm 7 0 6 0 1 0 + JTerm 7 0 6 0 0 1 + JTerm 21 0 5 2 0 0 + JTerm 42 0 5 1 1 0
      + JTerm 42 0 5 1 0 1 + JTerm 21 0 5 0 2 0 + JTerm 42 0 5 0 1 1 + JTerm 21 0 5 0 0 2
      + JTerm 35 0 4 3 0 0 + JTerm 105 0 4 2 1 0 + JTerm 105 0 4 2 0 1 + JTerm 105 0 4 1 2 0
      + JTerm 210 0 4 1 1 1 + JTerm 105 0 4 1 0 2 + JTerm 35 0 4 0 3 0 + JTerm 105 0 4 0 2 1
      + JTerm 105 0 4 0 1 2 + JTerm 35 0 4 0 0 3 + JTerm 35 0 3 4 0 0 + JTerm 140 0 3 3 1 0
      + JTerm 140 0 3 3 0 1 + JTerm 210 0 3 2 2 0 + JTerm 420 0 3 2 1 1 + JTerm 210 0 3 2 0 2
      + JTerm 140 0 3 1 3 0 + JTerm 420 0 3 1 2 1 + JTerm 420 0 3 1 1 2 + JTerm 140 0 3 1 0 3
      + JTerm 35 0 3 0 4 0 + JTerm 140 0 3 0 3 1 + JTerm 210 0 3 0 2 2 + JTerm 140 0 3 0 1 3
      + JTerm 35 0 3 0 0 4 + JTerm 21 0 2 5 0 0 + JTerm 105 0 2 4 1 0 + JTerm 105 0 2 4 0 1
      + JTerm 210 0 2 3 2 0 + JTerm 420 0 2 3 1 1 + JTerm 210 0 2 3 0 2 + JTerm 210 0 2 2 3 0
      + JTerm 630 0 2 2 2 1 + JTerm 630 0 2 2 1 2 + JTerm 210 0 2 2 0 3 + JTerm 105 0 2 1 4 0
      + JTerm 420 0 2 1 3 1 + JTerm 630 0 2 1 2 2 + JTerm 420 0 2 1 1 3 + JTerm 105 0 2 1 0 4
      + JTerm 21 0 2 0 5 0 + JTerm 105 0 2 0 4 1 + JTerm 210 0 2 0 3 2 + JTerm 210 0 2 0 2 3
      + JTerm 105 0 2 0 1 4 + JTerm 21 0 2 0 0 5 + JTerm 7 0 1 6 0 0 + JTerm 42 0 1 5 1 0
      + JTerm 42 0 1 5 0 1 + JTerm 105 0 1 4 2 0 + JTerm 210 0 1 4 1 1 + JTerm 105 0 1 4 0 2
      + JTerm 140 0 1 3 3 0 + JTerm 420 0 1 3 2 1 + JTerm 420 0 1 3 1 2 + JTerm 140 0 1 3 0 3
      + JTerm 105 0 1 2 4 0 + JTerm 420 0 1 2 3 1 + JTerm 630 0 1 2 2 2 + JTerm 420 0 1 2 1 3
      + JTerm 105 0 1 2 0 4 + JTerm 42 0 1 1 5 0 + JTerm 210 0 1 1 4 1 + JTerm 420 0 1 1 3 2
      + JTerm 420 0 1 1 2 3 + JTerm 210 0 1 1 1 4 + JTerm 42 0 1 1 0 5 + JTerm 7 0 1 0 6 0
      + JTerm 42 0 1 0 5 1 + JTerm 105 0 1 0 4 2 + JTerm 140 0 1 0 3 3 + JTerm 105 0 1 0 2 4
      + JTerm 42 0 1 0 1 5 + JTerm 7 0 1 0 0 6 + JTerm 1 0 0 7 0 0 + JTerm 7 0 0 6 1 0
      + JTerm 7 0 0 6 0 1 + JTerm 21 0 0 5 2 0 + JTerm 42 0 0 5 1 1 + JTerm 21 0 0 5 0 2
      + JTerm 35 0 0 4 3 0 + JTerm 105 0 0 4 2 1 + JTerm 105 0 0 4 1 2 + JTerm 35 0 0 4 0 3
      + JTerm 35 0 0 3 4 0 + JTerm 140 0 0 3 3 1 + JTerm 210 0 0 3 2 2 + JTerm 140 0 0 3 1 3
      + JTerm 35 0 0 3 0 4 + JTerm 21 0 0 2 5 0 + JTerm 105 0 0 2 4 1 + JTerm 210 0 0 2 3 2
      + JTerm 210 0 0 2 2 3 + JTerm 105 0 0 2 1 4 + JTerm 21 0 0 2 0 5 + JTerm 7 0 0 1 6 0
      + JTerm 42 0 0 1 5 1 + JTerm 105 0 0 1 4 2 + JTerm 140 0 0 1 3 3 + JTerm 105 0 0 1 2 4
      + JTerm 42 0 0 1 1 5 + JTerm 7 0 0 1 0 6 + JTerm 1 0 0 0 7 0 + JTerm 7 0 0 0 6 1
      + JTerm 21 0 0 0 5 2 + JTerm 35 0 0 0 4 3 + JTerm 35 0 0 0 3 4 + JTerm 21 0 0 0 2 5
  + JTerm 7 0 0 0 1 6 + JTerm 1 0 0 0 0 7 := by
  simp only [JSum, JTerm, JMon]
  ring

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem section11_JSum_pow_seven_eq_P :
    section11 (ZMod 11) 6 (JSum ^ 7) = H11_P := by
  rw [JSum_pow_seven_expansion]
  simp [section11_add, JMonRes]
  simp [H11_P, JTerm, JMon]
  ring_nf

/-- **Decomposition of `(qPoch ZMod 11)^3`**: equals `J_0 + J_1 + J_3 + J_6 + J_{10}`.

Reason: by B2 `(qPoch)^3 = jacobiThetaPS` with `coeff = jts`.  In `ZMod 11`:
`(jts n : ZMod 11) ≠ 0` only when `n` is triangular `T_k` with `k ≢ 5 mod 11`,
and `T_k mod 11 ∈ {0, 1, 3, 6, 10}` (by direct mod-11 computation).  Coefficients
at other residues are 0 mod 11. -/
theorem qPochInfPS_cube_decompose_mod_11 :
    (qPochInfPS (ZMod 11))^3 = J 0 + J 1 + J 3 + J 6 + J 10 := by
  ext n
  -- LHS via B2: ((qPoch)^3).coeff n = (jts n : ZMod 11).
  have hB2 :
      ((qPochInfPS (ZMod 11))^3).coeff n =
        ((QseriesFormalization.PartIV.Ch19.jacobiTripleSign n : ℤ) : ZMod 11) := by
    rw [QseriesFormalization.Pending.JacobiCubeAnalyticToFormal.qPochInfPS_pow_three_eq_jacobiThetaPS]
    rw [QseriesFormalization.PartIV.Ch19.coeff_jacobiThetaPS]
  -- Reduce RHS sum to 5 conditionals on (qPoch^3).coeff n.
  have hRHS :
      (J 0 + J 1 + J 3 + J 6 + J 10 : (ZMod 11)⟦X⟧).coeff n =
        (if n % 11 = 0 then ((qPochInfPS (ZMod 11))^3).coeff n else 0) +
        (if n % 11 = 1 then ((qPochInfPS (ZMod 11))^3).coeff n else 0) +
        (if n % 11 = 3 then ((qPochInfPS (ZMod 11))^3).coeff n else 0) +
        (if n % 11 = 6 then ((qPochInfPS (ZMod 11))^3).coeff n else 0) +
        (if n % 11 = 10 then ((qPochInfPS (ZMod 11))^3).coeff n else 0) := by
    simp only [J, section11, map_add, coeff_mk]
  rw [hRHS]
  -- Bridge n%11 to (n : ZMod 11).
  have h_nmod : (n : ZMod 11) = ((n % 11 : ℕ) : ZMod 11) := by
    conv_lhs => rw [← Nat.mod_add_div n 11]
    push_cast
    have : (11 : ZMod 11) = 0 := by decide
    rw [this]; ring
  -- Off-residue zero lemma.
  have h_zero_off :
      n % 11 ≠ 0 → n % 11 ≠ 1 → n % 11 ≠ 3 → n % 11 ≠ 6 → n % 11 ≠ 10 →
        ((qPochInfPS (ZMod 11))^3).coeff n = 0 := by
    intros h0 h1 h3 h6 h10
    rw [hB2]
    by_contra h_ne
    have h_res := QseriesFormalization.PartIV.Ch17.jacobiTripleSign_nonzero_mod_11_residue n h_ne
    rw [h_nmod] at h_res
    have hlt : n % 11 < 11 := Nat.mod_lt n (by decide)
    -- Each case of h_res gives (((n%11 : ℕ) : ZMod 11) = i), forcing n%11 = i in ℕ.
    interval_cases (n % 11) <;>
      rcases h_res with hr | hr | hr | hr | hr <;>
        first
          | exact h0 rfl
          | exact h1 rfl
          | exact h3 rfl
          | exact h6 rfl
          | exact h10 rfl
          | exact absurd hr (by decide)
  -- Final case split: n%11 ∈ {0,...,10}, 11 cases.
  have hlt : n % 11 < 11 := Nat.mod_lt n (by decide)
  interval_cases (n % 11) <;> simp_all

/-- **Kind-one pentagonal residues mod 11**: for any `k`, `k(3k-1)/2 mod 11 ∈ {0,1,2,4,5,7}`. -/
theorem pentagonal_kind_one_mod_11 (k : ℕ) :
    (((k * (3 * k - 1) / 2 : ℕ) : ZMod 11) = 0) ∨
    (((k * (3 * k - 1) / 2 : ℕ) : ZMod 11) = 1) ∨
    (((k * (3 * k - 1) / 2 : ℕ) : ZMod 11) = 2) ∨
    (((k * (3 * k - 1) / 2 : ℕ) : ZMod 11) = 4) ∨
    (((k * (3 * k - 1) / 2 : ℕ) : ZMod 11) = 5) ∨
    (((k * (3 * k - 1) / 2 : ℕ) : ZMod 11) = 7) := by
  rcases Nat.eq_zero_or_pos k with hk0 | hk1
  · subst hk0; left; simp
  -- k ≥ 1: standard cast.
  -- 2 * k(3k-1)/2 = k(3k-1) since k(3k-1) is even.
  have h_even : Even (k * (3 * k - 1)) := by
    rcases Nat.even_or_odd k with hek | hok
    · exact hek.mul_right _
    · refine Even.mul_left ?_ k
      obtain ⟨m, hm⟩ := hok
      have h1 : 3 * k - 1 = 6 * m + 2 := by rw [hm]; omega
      rw [h1]; exact ⟨3 * m + 1, by ring⟩
  obtain ⟨q, hq⟩ := h_even
  have hq' : k * (3 * k - 1) = 2 * q := by rw [hq]; ring
  have h_div : k * (3 * k - 1) / 2 = q := by
    rw [hq']; exact Nat.mul_div_cancel_left q (by decide)
  rw [h_div]
  -- For k ≥ 1: ((3*k - 1 : ℕ) : ZMod 11) = 3*(k : ZMod 11) - 1.
  have h_cast_3k : ((3 * k - 1 : ℕ) : ZMod 11) = 3 * (k : ZMod 11) - 1 := by
    have heq : (3 * k - 1 : ℕ) + 1 = 3 * k := by omega
    have h1 : (((3 * k - 1 : ℕ) + 1 : ℕ) : ZMod 11) = ((3 * k : ℕ) : ZMod 11) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ZMod 11) heq
    push_cast at h1
    linear_combination h1
  have h_2q_cast : (2 : ZMod 11) * (q : ZMod 11) = (k : ZMod 11) * (3 * (k : ZMod 11) - 1) := by
    have h2 : ((2 * q : ℕ) : ZMod 11) = ((k * (3 * k - 1) : ℕ) : ZMod 11) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ZMod 11) hq'.symm
    push_cast at h2
    rw [h_cast_3k] at h2
    linear_combination h2
  have h_q_eq : (q : ZMod 11) = 6 * ((k : ZMod 11) * (3 * (k : ZMod 11) - 1)) := by
    have h_inv : (6 : ZMod 11) * 2 = 1 := by decide
    calc (q : ZMod 11)
        = 1 * (q : ZMod 11) := (one_mul _).symm
      _ = (6 * 2) * (q : ZMod 11) := by rw [h_inv]
      _ = 6 * (2 * (q : ZMod 11)) := by ring
      _ = 6 * ((k : ZMod 11) * (3 * (k : ZMod 11) - 1)) := by rw [h_2q_cast]
  rw [h_q_eq]
  obtain ⟨k', hk'⟩ : ∃ k' : ZMod 11, (k : ZMod 11) = k' := ⟨(k : ZMod 11), rfl⟩
  rw [hk']
  fin_cases k' <;> decide

/-- **Kind-two pentagonal residues mod 11**: for any `k`, `k(3k+1)/2 mod 11 ∈ {0,1,2,4,5,7}`. -/
theorem pentagonal_kind_two_mod_11 (k : ℕ) :
    (((k * (3 * k + 1) / 2 : ℕ) : ZMod 11) = 0) ∨
    (((k * (3 * k + 1) / 2 : ℕ) : ZMod 11) = 1) ∨
    (((k * (3 * k + 1) / 2 : ℕ) : ZMod 11) = 2) ∨
    (((k * (3 * k + 1) / 2 : ℕ) : ZMod 11) = 4) ∨
    (((k * (3 * k + 1) / 2 : ℕ) : ZMod 11) = 5) ∨
    (((k * (3 * k + 1) / 2 : ℕ) : ZMod 11) = 7) := by
  -- k(3k+1) is always even.
  have h_even : Even (k * (3 * k + 1)) := by
    rcases Nat.even_or_odd k with hek | hok
    · exact hek.mul_right _
    · refine Even.mul_left ?_ k
      obtain ⟨m, hm⟩ := hok
      rw [hm]
      exact ⟨3 * m + 2, by ring⟩
  obtain ⟨q, hq⟩ := h_even
  have hq' : k * (3 * k + 1) = 2 * q := by rw [hq]; ring
  have h_div : k * (3 * k + 1) / 2 = q := by
    rw [hq']; exact Nat.mul_div_cancel_left q (by decide)
  rw [h_div]
  have h_2q_cast : (2 : ZMod 11) * (q : ZMod 11) = (k : ZMod 11) * (3 * (k : ZMod 11) + 1) := by
    have h2 : ((2 * q : ℕ) : ZMod 11) = ((k * (3 * k + 1) : ℕ) : ZMod 11) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ZMod 11) hq'.symm
    push_cast at h2
    linear_combination h2
  have h_q_eq : (q : ZMod 11) = 6 * ((k : ZMod 11) * (3 * (k : ZMod 11) + 1)) := by
    have h_inv : (6 : ZMod 11) * 2 = 1 := by decide
    calc (q : ZMod 11)
        = 1 * (q : ZMod 11) := (one_mul _).symm
      _ = (6 * 2) * (q : ZMod 11) := by rw [h_inv]
      _ = 6 * (2 * (q : ZMod 11)) := by ring
      _ = 6 * ((k : ZMod 11) * (3 * (k : ZMod 11) + 1)) := by rw [h_2q_cast]
  rw [h_q_eq]
  obtain ⟨k', hk'⟩ : ∃ k' : ZMod 11, (k : ZMod 11) = k' := ⟨(k : ZMod 11), rfl⟩
  rw [hk']
  fin_cases k' <;> decide

/-- **Pentagonal residues mod 11**: `pentagonalSign n mod 11 ≠ 0` implies
`n mod 11 ∈ {0, 1, 2, 4, 5, 7}`.

Used to show `(expand 11 qPoch · qPoch) ZMod 11` has zero coefficient at
residues `{3, 6, 8, 9, 10}`. -/
theorem pentagonalSign_mod_11_residue (n : ℕ)
    (h : ((QseriesFormalization.PartI.Ch04Franklin.pentagonalSign n : ℤ) : ZMod 11) ≠ 0) :
    (n : ZMod 11) = 0 ∨ (n : ZMod 11) = 1 ∨ (n : ZMod 11) = 2 ∨
    (n : ZMod 11) = 4 ∨ (n : ZMod 11) = 5 ∨ (n : ZMod 11) = 7 := by
  -- Unfold the def: pentagonalSign n ≠ 0 forces one of two finds to succeed.
  unfold QseriesFormalization.PartI.Ch04Franklin.pentagonalSign at h
  -- Case on the outer match.
  cases h_find1 : (List.range (n + 1)).find? (fun k => decide (n = k * (3 * k - 1) / 2)) with
  | some k =>
      have hpred := (List.find?_eq_some_iff_append.mp h_find1).1
      simp only [decide_eq_true_eq] at hpred
      rw [hpred]
      exact pentagonal_kind_one_mod_11 k
  | none =>
      rw [h_find1] at h
      cases h_find2 : (List.range (n + 1)).find?
            (fun k => decide (0 < k ∧ n = k * (3 * k + 1) / 2)) with
      | some k =>
          have hpred := (List.find?_eq_some_iff_append.mp h_find2).1
          simp only [decide_eq_true_eq] at hpred
          rw [hpred.2]
          exact pentagonal_kind_two_mod_11 k
      | none =>
          rw [h_find2] at h
          simp at h

/-- **Frobenius cube-power identity**: `(qPoch ZMod 11)^{12} = (expand 11 qPoch) · qPoch`. -/
theorem qPochInfPS_pow_twelve_mod_11 :
    (qPochInfPS (ZMod 11))^12 =
      (PowerSeries.expand 11 (by decide) (qPochInfPS (ZMod 11))) * qPochInfPS (ZMod 11) := by
  -- (qPoch)^12 = (qPoch)^11 · qPoch.  Frobenius: (qPoch)^11 = expand 11 qPoch in ZMod 11.
  rw [show (qPochInfPS (ZMod 11))^12 =
      (qPochInfPS (ZMod 11))^11 * qPochInfPS (ZMod 11) from by ring]
  haveI : Fact (Nat.Prime 11) := ⟨by decide⟩
  rw [qPochInfPS_pow_eq_expand 11 (by decide)]

/-- **Coefficient zero off pentagonal residues**: for `r ∈ {3, 6, 8, 9, 10}`,
`((expand 11 qPoch * qPoch) ZMod 11).coeff (11n+r) = 0`.

Reason: convolution sum requires `(qPoch).coeff j ≠ 0` for some `j ≡ r (mod 11)`,
but `qPoch.coeff j = pentagonalSign j` is non-zero mod 11 only when `j mod 11 ∈ {0,1,2,4,5,7}`. -/
theorem coeff_expand_mul_qPoch_zero_off_pentagonal (r : ℕ)
    (hr : r = 3 ∨ r = 6 ∨ r = 8 ∨ r = 9 ∨ r = 10) (n : ℕ) :
    ((PowerSeries.expand 11 (by decide) (qPochInfPS (ZMod 11))) *
      qPochInfPS (ZMod 11)).coeff (11 * n + r) = 0 := by
  rw [PowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨i, j⟩ hij
  rw [Finset.mem_antidiagonal] at hij
  -- Coefficient of expand 11 at i is 0 unless 11 | i.
  by_cases h_div : 11 ∣ i
  · -- Then j ≡ r (mod 11), but pentagonalSign j ≡ 0 (mod 11).
    have h_j_mod : (j : ZMod 11) = (r : ZMod 11) := by
      obtain ⟨m, hm⟩ := h_div
      have h_sum : j = 11 * n + r - i := by omega
      have : ((j : ℕ) : ZMod 11) = ((11 * n + r - i : ℕ) : ZMod 11) := by
        exact_mod_cast congrArg (Nat.cast : ℕ → ZMod 11) h_sum
      -- j + i = 11n + r in ℕ, so (j : ZMod 11) + (i : ZMod 11) = (11n+r : ZMod 11) = r.
      have h_sum_z : (j : ZMod 11) + (i : ZMod 11) = (r : ZMod 11) := by
        have : ((j + i : ℕ) : ZMod 11) = ((11 * n + r : ℕ) : ZMod 11) := by
          have hadd : j + i = 11 * n + r := by omega
          exact_mod_cast congrArg (Nat.cast : ℕ → ZMod 11) hadd
        push_cast at this
        have h11 : (11 : ZMod 11) = 0 := by decide
        rw [h11] at this
        linear_combination this
      have h_i_z : (i : ZMod 11) = 0 := by
        rw [hm]; push_cast
        have h11 : (11 : ZMod 11) = 0 := by decide
        rw [h11]; ring
      rw [h_i_z, add_zero] at h_sum_z
      exact h_sum_z
    have h_qPoch_zero : (qPochInfPS (ZMod 11)).coeff j = 0 := by
      rw [coeff_qPochInfPS_eq_pentagonalSign]
      by_contra h_ne
      have h_res := pentagonalSign_mod_11_residue j h_ne
      rw [h_j_mod] at h_res
      rcases hr with hr_eq | hr_eq | hr_eq | hr_eq | hr_eq <;>
        rw [hr_eq] at h_res <;>
        rcases h_res with h | h | h | h | h | h <;>
        exact absurd h (by decide)
    change (PowerSeries.expand 11 _ (qPochInfPS (ZMod 11))).coeff i *
        (qPochInfPS (ZMod 11)).coeff j = 0
    rw [h_qPoch_zero, mul_zero]
  · -- expand 11 has coeff 0 when 11 ∤ i.
    have h_exp_zero : (PowerSeries.expand 11 (by decide) (qPochInfPS (ZMod 11))).coeff i = 0 := by
      rw [PowerSeries.coeff_expand]
      simp [h_div]
    change (PowerSeries.expand 11 _ (qPochInfPS (ZMod 11))).coeff i *
        (qPochInfPS (ZMod 11)).coeff j = 0
    rw [h_exp_zero, zero_mul]

/-- **Cube power vanishing off pentagonal residues**:
`((qPoch ZMod 11)^12).coeff (11n+r) = 0` for `r ∈ {3, 6, 8, 9, 10}`.

This is the **key Hirschhorn relation** (3.5.6)–(3.5.10) on the J_i power series:
when written as `(J_0+J_1+J_3+J_6+J_10)^4`, the coefficient at residue `r ∈ {3,6,8,9,10}`
mod 11 must vanish, yielding 5 polynomial identities. -/
theorem coeff_qPochInfPS_pow_twelve_zero_off_pentagonal (r : ℕ)
    (hr : r = 3 ∨ r = 6 ∨ r = 8 ∨ r = 9 ∨ r = 10) (n : ℕ) :
    ((qPochInfPS (ZMod 11))^12).coeff (11 * n + r) = 0 := by
  rw [qPochInfPS_pow_twelve_mod_11]
  exact coeff_expand_mul_qPoch_zero_off_pentagonal r hr n

theorem section11_qPochInfPS_pow_twelve_zero_off_pentagonal (r : ℕ)
    (hr : r = 3 ∨ r = 6 ∨ r = 8 ∨ r = 9 ∨ r = 10) :
    section11 (ZMod 11) r ((qPochInfPS (ZMod 11))^12) = 0 := by
  ext n
  rw [coeff_section11]
  by_cases hn : n % 11 = r
  · rw [if_pos hn]
    have hn_eq : n = 11 * (n / 11) + r := by
      calc
        n = n % 11 + 11 * (n / 11) := (Nat.mod_add_div n 11).symm
        _ = r + 11 * (n / 11) := by rw [hn]
        _ = 11 * (n / 11) + r := by omega
    rw [hn_eq]
    exact coeff_qPochInfPS_pow_twelve_zero_off_pentagonal r hr (n / 11)
  · rw [if_neg hn]
    simp

set_option maxHeartbeats 4000000 in
theorem JSum_eq_qPochInfPS_cube :
    JSum = (qPochInfPS (ZMod 11))^3 := by
  simpa [JSum] using qPochInfPS_cube_decompose_mod_11.symm

theorem JSum_pow_four_eq_qPochInfPS_pow_twelve :
    JSum ^ 4 = (qPochInfPS (ZMod 11))^12 := by
  rw [JSum_eq_qPochInfPS_cube]
  ring

theorem H11_R3_eq_zero : H11_R3 = 0 := by
  have h : section11 (ZMod 11) 3 (JSum ^ 4) = 0 := by
    rw [JSum_pow_four_eq_qPochInfPS_pow_twelve]
    exact section11_qPochInfPS_pow_twelve_zero_off_pentagonal 3 (by simp)
  rwa [section11_JSum_pow_four_eq_R3] at h

theorem H11_R6_eq_zero : H11_R6 = 0 := by
  have h : section11 (ZMod 11) 6 (JSum ^ 4) = 0 := by
    rw [JSum_pow_four_eq_qPochInfPS_pow_twelve]
    exact section11_qPochInfPS_pow_twelve_zero_off_pentagonal 6 (by simp)
  rwa [section11_JSum_pow_four_eq_R6] at h

theorem H11_R8_eq_zero : H11_R8 = 0 := by
  have h : section11 (ZMod 11) 8 (JSum ^ 4) = 0 := by
    rw [JSum_pow_four_eq_qPochInfPS_pow_twelve]
    exact section11_qPochInfPS_pow_twelve_zero_off_pentagonal 8 (by simp)
  rwa [section11_JSum_pow_four_eq_R8] at h

theorem H11_R9_eq_zero : H11_R9 = 0 := by
  have h : section11 (ZMod 11) 9 (JSum ^ 4) = 0 := by
    rw [JSum_pow_four_eq_qPochInfPS_pow_twelve]
    exact section11_qPochInfPS_pow_twelve_zero_off_pentagonal 9 (by simp)
  rwa [section11_JSum_pow_four_eq_R9] at h

theorem H11_R10_eq_zero : H11_R10 = 0 := by
  have h : section11 (ZMod 11) 10 (JSum ^ 4) = 0 := by
    rw [JSum_pow_four_eq_qPochInfPS_pow_twelve]
    exact section11_qPochInfPS_pow_twelve_zero_off_pentagonal 10 (by simp)
  rwa [section11_JSum_pow_four_eq_R10] at h

set_option maxHeartbeats 4000000 in
theorem H11_P_eq_zero : H11_P = 0 := by
  have hcomb :
      H11_P =
        (10*(J 1)*(J 3)*(J 10) + 10*(J 1)^3 + 4*(J 0)^2*(J 3)) * H11_R3
      + (4*(J 6)^2*(J 10) + 10*(J 0)*(J 1)*(J 10) + 10*(J 0)^3) * H11_R6
      + (10*(J 3)^3 + 4*(J 0)*(J 10)^2 + 10*(J 0)*(J 3)*(J 6)) * H11_R8
      + (10*(J 10)^3 + 10*(J 3)*(J 6)*(J 10) + 4*(J 1)^2*(J 6)) * H11_R9
      + (10*(J 6)^3 + 4*(J 1)*(J 3)^2 + 10*(J 0)*(J 1)*(J 6)) * H11_R10 := by
    simpa [H11_P, H11_R3, H11_R6, H11_R8, H11_R9, H11_R10]
      using (QseriesFormalization.Pending.HirschhornComb.hirschhorn_P_eq_combination
        (R := (ZMod 11)⟦X⟧) (J 0) (J 1) (J 3) (J 6) (J 10))
  rw [H11_R3_eq_zero, H11_R6_eq_zero, H11_R8_eq_zero, H11_R9_eq_zero,
    H11_R10_eq_zero] at hcomb
  simpa using hcomb

theorem section11_JSum_pow_seven_eq_zero :
    section11 (ZMod 11) 6 (JSum ^ 7) = 0 := by
  rw [section11_JSum_pow_seven_eq_P, H11_P_eq_zero]

/-! ### Reduction: 30-monomial claim ⇒ headline

In `ZMod 11`, by Frobenius `(qPoch)^11 = expand 11 qPoch`, so
`(qPoch)^21 = (qPoch)^11 · (qPoch)^10 = expand 11 qPoch · (qPoch)^10`.

Taking the coefficient at `11k+6`:
  `(qPoch)^21.coeff (11k+6) = Σ_{m=0}^{k} qPoch.coeff(m) · (qPoch)^10.coeff (11(k-m)+6)`
                            = `(qPoch)^10.coeff (11k+6)` (m=0 term)
                              + `Σ_{m=1}^{k} qPoch.coeff(m) · (qPoch)^10.coeff (11(k-m)+6)`.

So **if** `(qPoch)^21.coeff (11k+6) = 0` for all `k`, **then** by strong induction
on `k`, `(qPoch)^10.coeff (11k+6) = 0` for all `k`.

The Hirschhorn §3.5 30-monomial argument proves the antecedent.  We isolate
this as an explicit hypothesis: closing it remains future work, but the
reduction itself is now formalized. -/

/-- **Reduction**: from `((qPoch)^21).coeff (11k+6) = 0` (Hirschhorn 30-monomial)
to `((qPoch)^10).coeff (11k+6) = 0` (algebraic core of headline). -/
theorem coeff_qPochInfPS_pow_ten_at_11n_plus_6_eq_zero
    (h21 : ∀ k, ((qPochInfPS (ZMod 11))^21).coeff (11 * k + 6) = 0) :
    ∀ k, ((qPochInfPS (ZMod 11))^10).coeff (11 * k + 6) = 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k IH =>
    haveI : Fact (Nat.Prime 11) := ⟨by decide⟩
    -- (qPoch)^21 = expand 11 qPoch · (qPoch)^10
    have h_pow21 : (qPochInfPS (ZMod 11))^21 =
        (PowerSeries.expand 11 (by decide) (qPochInfPS (ZMod 11))) *
          (qPochInfPS (ZMod 11))^10 := by
      have : (qPochInfPS (ZMod 11))^21 =
          (qPochInfPS (ZMod 11))^11 * (qPochInfPS (ZMod 11))^10 := by ring
      rw [this, qPochInfPS_pow_eq_expand 11 (by decide)]
    have h_assumed := h21 k
    rw [h_pow21, PowerSeries.coeff_mul] at h_assumed
    -- For each (i, j) ∈ antidiagonal, the only contribution with non-zero factor:
    --   (i, j) = (0, 11k+6): factor = 1 · (qPoch)^10.coeff(11k+6) = LHS.
    --   (i, j) = (11m, 11(k-m)+6) for m ≥ 1: factor = qPoch.coeff(m) · 0 = 0  (by IH)
    --   (i, j) with 11∤i: factor = 0
    -- Define f : Sym → ZMod 11 and split the sum.
    classical
    set f : ℕ × ℕ → ZMod 11 := fun p =>
      (PowerSeries.expand 11 (by decide) (qPochInfPS (ZMod 11))).coeff p.1 *
        ((qPochInfPS (ZMod 11))^10).coeff p.2 with hf_def
    have hfk : f (0, 11 * k + 6) = ((qPochInfPS (ZMod 11))^10).coeff (11 * k + 6) := by
      simp only [hf_def]
      rw [PowerSeries.coeff_expand]
      simp [coeff_zero_qPochInfPS]
    have h_other_zero : ∀ p ∈ Finset.antidiagonal (11 * k + 6),
        p ≠ (0, 11 * k + 6) → f p = 0 := by
      rintro ⟨i, j⟩ hij h_ne
      rw [Finset.mem_antidiagonal] at hij
      simp only [hf_def]
      by_cases h_div : 11 ∣ i
      · obtain ⟨m, hm⟩ := h_div
        rcases Nat.eq_zero_or_pos m with hm0 | hmp
        · subst hm0
          simp at hm
          subst hm
          have hj : j = 11 * k + 6 := by omega
          subst hj
          exact absurd rfl h_ne
        · have hj_eq : j = 11 * (k - m) + 6 := by omega
          have hk_m_lt : k - m < k := by omega
          have hIH := IH (k - m) hk_m_lt
          rw [hj_eq, hIH, mul_zero]
      · have h_exp_zero :
            (PowerSeries.expand 11 (by decide) (qPochInfPS (ZMod 11))).coeff i = 0 := by
          rw [PowerSeries.coeff_expand]; simp [h_div]
        rw [h_exp_zero, zero_mul]
    have h_mem : (0, 11 * k + 6) ∈ Finset.antidiagonal (11 * k + 6) := by
      simp [Finset.mem_antidiagonal]
    rw [← Finset.add_sum_erase _ _ h_mem] at h_assumed
    have h_erase_zero :
        ∑ p ∈ (Finset.antidiagonal (11 * k + 6)).erase (0, 11 * k + 6), f p = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      rw [Finset.mem_erase] at hp
      exact h_other_zero p hp.2 hp.1
    rw [h_erase_zero, add_zero] at h_assumed
    -- h_assumed : f (0, 11 * k + 6) = 0 (after unfolding), i.e.,
    --             expand.coeff(0) * (qPoch)^10.coeff(11k+6) = 0.
    change f (0, 11 * k + 6) = 0 at h_assumed
    rw [hfk] at h_assumed
    exact h_assumed

/-- **22nd-power vanishing on any non-multiple of 11**: by Frobenius squared,
`(qPoch ZMod 11)^22 = (expand 11 qPoch)^2`, whose coefficients vanish off
multiples of 11.  Used as an intermediate stepping stone toward the 30-monomial
claim, and as a clean unconditional sanity check. -/
theorem coeff_qPochInfPS_pow_twentytwo_off_mult_11 (n : ℕ) (hn : ¬ 11 ∣ n) :
    ((qPochInfPS (ZMod 11))^22).coeff n = 0 := by
  haveI : Fact (Nat.Prime 11) := ⟨by decide⟩
  have h_pow22 : (qPochInfPS (ZMod 11))^22 =
      (PowerSeries.expand 11 (by decide) (qPochInfPS (ZMod 11)))^2 := by
    have : (qPochInfPS (ZMod 11))^22 = ((qPochInfPS (ZMod 11))^11)^2 := by ring
    rw [this, qPochInfPS_pow_eq_expand 11 (by decide)]
  rw [h_pow22, sq, PowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨i, j⟩ hij
  rw [Finset.mem_antidiagonal] at hij
  -- expand 11 qPoch.coeff(i) is 0 unless 11 | i; similarly for j.
  by_cases h_i_div : 11 ∣ i
  · by_cases h_j_div : 11 ∣ j
    · -- Both divisible by 11: but then 11 | i+j = n, contradicting hn.
      exfalso
      apply hn
      rw [← hij]
      exact Dvd.dvd.add h_i_div h_j_div
    · show (PowerSeries.expand 11 _ (qPochInfPS (ZMod 11))).coeff (i, j).1 *
          (PowerSeries.expand 11 _ (qPochInfPS (ZMod 11))).coeff (i, j).2 = 0
      change (PowerSeries.expand 11 _ (qPochInfPS (ZMod 11))).coeff i *
          (PowerSeries.expand 11 _ (qPochInfPS (ZMod 11))).coeff j = 0
      have h_exp_zero_j :
          (PowerSeries.expand 11 (by decide) (qPochInfPS (ZMod 11))).coeff j = 0 := by
        rw [PowerSeries.coeff_expand]; simp [h_j_div]
      rw [h_exp_zero_j, mul_zero]
  · show (PowerSeries.expand 11 _ (qPochInfPS (ZMod 11))).coeff (i, j).1 *
        (PowerSeries.expand 11 _ (qPochInfPS (ZMod 11))).coeff (i, j).2 = 0
    change (PowerSeries.expand 11 _ (qPochInfPS (ZMod 11))).coeff i *
        (PowerSeries.expand 11 _ (qPochInfPS (ZMod 11))).coeff j = 0
    have h_exp_zero_i :
        (PowerSeries.expand 11 (by decide) (qPochInfPS (ZMod 11))).coeff i = 0 := by
      rw [PowerSeries.coeff_expand]; simp [h_i_div]
    rw [h_exp_zero_i, zero_mul]

/-- **33rd-power vanishing off multiples of 11**: from `(qPoch)^33 = (expand 11 qPoch)^3`. -/
theorem coeff_qPochInfPS_pow_thirtythree_off_mult_11 (n : ℕ) (hn : ¬ 11 ∣ n) :
    ((qPochInfPS (ZMod 11))^33).coeff n = 0 := by
  haveI : Fact (Nat.Prime 11) := ⟨by decide⟩
  have h_pow33 : (qPochInfPS (ZMod 11))^33 =
      (PowerSeries.expand 11 (by decide) (qPochInfPS (ZMod 11)))^3 := by
    have : (qPochInfPS (ZMod 11))^33 = ((qPochInfPS (ZMod 11))^11)^3 := by ring
    rw [this, qPochInfPS_pow_eq_expand 11 (by decide)]
  rw [h_pow33]
  -- (expand 11 f)^3 has support only on multiples of 11.
  have h_support : ∀ m, ¬ 11 ∣ m →
      ((PowerSeries.expand 11 (by decide) (qPochInfPS (ZMod 11)))^3).coeff m = 0 := by
    intro m hm
    -- (expand f)^3 = expand f · expand f · expand f.  Each factor coefficient is 0 off multiples of 11.
    rw [show (PowerSeries.expand 11 (by decide) (qPochInfPS (ZMod 11)))^3 =
        (PowerSeries.expand 11 (by decide) (qPochInfPS (ZMod 11)))^2 *
        (PowerSeries.expand 11 (by decide) (qPochInfPS (ZMod 11))) from by ring]
    rw [PowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    rintro ⟨a, b⟩ hab
    rw [Finset.mem_antidiagonal] at hab
    by_cases h_b_div : 11 ∣ b
    · -- Then 11 ∣ a → 11 ∣ a+b = m.  But ¬11∣m, so 11 ∤ a.
      have h_a_ndiv : ¬ 11 ∣ a := by
        intro h_a
        apply hm; rw [← hab]; exact Dvd.dvd.add h_a h_b_div
      show ((PowerSeries.expand 11 _ (qPochInfPS (ZMod 11)))^2).coeff (a, b).1 *
          (PowerSeries.expand 11 _ (qPochInfPS (ZMod 11))).coeff (a, b).2 = 0
      change ((PowerSeries.expand 11 _ (qPochInfPS (ZMod 11)))^2).coeff a *
          (PowerSeries.expand 11 _ (qPochInfPS (ZMod 11))).coeff b = 0
      -- ((expand)^2).coeff(a): use the 22-power lemma indirectly.
      have h_a_zero : ((PowerSeries.expand 11 (by decide) (qPochInfPS (ZMod 11)))^2).coeff a = 0 := by
        have h_pow22 : (qPochInfPS (ZMod 11))^22 =
            (PowerSeries.expand 11 (by decide) (qPochInfPS (ZMod 11)))^2 := by
          have : (qPochInfPS (ZMod 11))^22 = ((qPochInfPS (ZMod 11))^11)^2 := by ring
          rw [this, qPochInfPS_pow_eq_expand 11 (by decide)]
        rw [← h_pow22]
        exact coeff_qPochInfPS_pow_twentytwo_off_mult_11 a h_a_ndiv
      rw [h_a_zero, zero_mul]
    · show ((PowerSeries.expand 11 _ (qPochInfPS (ZMod 11)))^2).coeff (a, b).1 *
          (PowerSeries.expand 11 _ (qPochInfPS (ZMod 11))).coeff (a, b).2 = 0
      change ((PowerSeries.expand 11 _ (qPochInfPS (ZMod 11)))^2).coeff a *
          (PowerSeries.expand 11 _ (qPochInfPS (ZMod 11))).coeff b = 0
      have h_b_zero : (PowerSeries.expand 11 (by decide) (qPochInfPS (ZMod 11))).coeff b = 0 := by
        rw [PowerSeries.coeff_expand]; simp [h_b_div]
      rw [h_b_zero, mul_zero]
  exact h_support n hn

/-- **Hirschhorn 30-monomial claim** (Hirschhorn §3.5, *The Power of q* 2017):
the 21st power of `qPoch` over `ZMod 11` has zero coefficient at every index
of form `11k+6`; equivalently `section11 6 (S^7) = 0` where `S = (qPoch)^3`.

**What is now PROVEN** (so this is no longer a black box):
* `S = J_0 + J_1 + J_3 + J_6 + J_{10}` (`qPochInfPS_cube_decompose_mod_11`).
* The 5 J-relations `section11 r (S^4) = section11 r ((qPoch)^12) = 0` for
  `r ∈ {3,6,8,9,10}` (`coeff_qPochInfPS_pow_twelve_zero_off_pentagonal`).
* **Hirschhorn's "left as an exercise" combination identity** — the core algebra
  `P = M_3 R_3 + M_6 R_6 + M_8 R_8 + M_9 R_9 + M_{10} R_{10}` over any char-11
  ring (`Chapter17_Hirschhorn_Combination.hirschhorn_P_eq_combination`), where
  `P` is the residue-6 part of `(J_0+J_1+J_3+J_6+J_{10})^7` (eq 3.5.3, 30
  monomials) and `R_r` are the residue-`r` parts of the 4th power.  The explicit
  `P`, `R_r`, `M_r` and the integer certificate `(ΣM_rR_r)−P = 11·Q` are computed
  in `scripts/hirschhorn_mod11_{compute,solve}.py`.

The residue-extraction dictionary is formalized above:
  `section11 6 (S^7) = P(J_0,…,J_{10})`  and  `section11 r (S^4) = R_r(J_0,…)`,
i.e. `section11 t` of a power of `S` equals the explicit residue-`t`
J-polynomial.  The proof then is:
`section11 6 (S^7) = P(J) = Σ M_r(J)·R_r(J) = Σ M_r(J)·0 = 0`. -/
theorem coeff_qPochInfPS_pow_twentyone_at_11n_plus_6_eq_zero :
    ∀ k, ((qPochInfPS (ZMod 11))^21).coeff (11 * k + 6) = 0 := by
  intro k
  have hmod : (11 * k + 6) % 11 = 6 := by omega
  have hsec_coeff : (JSum ^ 7).coeff (11 * k + 6) = 0 := by
    have h := congrArg (fun φ : (ZMod 11)⟦X⟧ => φ.coeff (11 * k + 6))
      section11_JSum_pow_seven_eq_zero
    change (section11 (ZMod 11) 6 (JSum ^ 7)).coeff (11 * k + 6) = 0 at h
    rw [coeff_section11] at h
    simpa [hmod] using h
  rw [show (qPochInfPS (ZMod 11))^21 = ((qPochInfPS (ZMod 11))^3)^7 by ring]
  rw [← JSum_eq_qPochInfPS_cube]
  exact hsec_coeff

/-- **Formal-PS strong form**: `((qPochInfPS (ZMod 11))^10).coeff (11n+6) = 0`.

This packages the Hirschhorn 21st-power vanishing with the Frobenius descent
`(qPoch)^21 = expand 11 qPoch · (qPoch)^10`. -/
theorem coeff_qPochInfPS_pow_ten_at_11n_plus_6_eq_zero_unconditional (n : ℕ) :
    ((qPochInfPS (ZMod 11))^10).coeff (11 * n + 6) = 0 :=
  coeff_qPochInfPS_pow_ten_at_11n_plus_6_eq_zero
    coeff_qPochInfPS_pow_twentyone_at_11n_plus_6_eq_zero n

/-- **Integer-level formal coefficient divisibility**:
`11 ∣ ((qPochInfPS ℤ)^10).coeff (11n+6)`. -/
theorem eleven_dvd_coeff_qPochInfPS_pow_ten_int_at_11n_plus_6 (n : ℕ) :
    (11 : ℤ) ∣ ((qPochInfPS ℤ)^10).coeff (11 * n + 6) := by
  have h_zmod :
      ((((qPochInfPS ℤ)^10).coeff (11 * n + 6) : ℤ) : ZMod 11) = 0 := by
    have h_map : PowerSeries.map (Int.castRingHom (ZMod 11)) ((qPochInfPS ℤ)^10) =
        (qPochInfPS (ZMod 11))^10 := by
      rw [map_pow, map_qPochInfPS]
    have h_cast : ((((qPochInfPS ℤ)^10).coeff (11 * n + 6) : ℤ) : ZMod 11) =
        ((qPochInfPS (ZMod 11))^10).coeff (11 * n + 6) := by
      rw [← h_map, PowerSeries.coeff_map]
      rfl
    rw [h_cast]
    exact coeff_qPochInfPS_pow_ten_at_11n_plus_6_eq_zero_unconditional n
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 11).mp h_zmod

/-- **HEADLINE (target)**: `∀ n, 11 ∣ p(11n+6)`. -/
theorem ramanujan_11_dvd_p_11n_plus_6 :
    ∀ n, 11 ∣ QseriesFormalization.Ch01.partitionCount (11 * n + 6) := by
  haveI : Fact (Nat.Prime 11) := ⟨by decide⟩
  intro n
  apply (ZMod.natCast_eq_zero_iff _ 11).mp
  refine ramanujan_from_pochInf_vanishes 11 (by decide) 6 (by decide) ?_ n
  intro m
  rw [show (11 - 1 : ℕ) = 10 from rfl]
  exact coeff_qPochInfPS_pow_ten_at_11n_plus_6_eq_zero_unconditional m

/-- **Restatement in `ZMod 11`**: `p(11n+6) ≡ 0 (mod 11)`. -/
theorem ramanujan_partition_11n_plus_6_eq_zero_mod_11 (n : ℕ) :
    ((QseriesFormalization.Ch01.partitionCount (11 * n + 6) : ℕ) : ZMod 11) = 0 :=
  (ZMod.natCast_eq_zero_iff _ 11).mpr (ramanujan_11_dvd_p_11n_plus_6 n)

/-- Congruence-class form of Ramanujan's mod-11 partition congruence. -/
theorem ramanujan_11_dvd_partitionCount_of_mod_eq_six
    (m : ℕ) (hm : m % 11 = 6) :
    11 ∣ QseriesFormalization.Ch01.partitionCount m := by
  have hm_decomp : m = 11 * (m / 11) + 6 := by
    have h := (Nat.mod_add_div m 11).symm
    omega
  rw [hm_decomp]
  exact ramanujan_11_dvd_p_11n_plus_6 (m / 11)

/-- `ZMod 11` form for every index in residue class `6`. -/
theorem ramanujan_partition_mod_11_eq_zero_of_mod_eq_six
    (m : ℕ) (hm : m % 11 = 6) :
    ((QseriesFormalization.Ch01.partitionCount m : ℕ) : ZMod 11) = 0 :=
  (ZMod.natCast_eq_zero_iff _ 11).mpr
    (ramanujan_11_dvd_partitionCount_of_mod_eq_six m hm)

/-- A nested arithmetic-progression corollary: `11 ∣ p(121n+72)`. -/
theorem ramanujan_11_dvd_p_121n_plus_72 (n : ℕ) :
    11 ∣ QseriesFormalization.Ch01.partitionCount (121 * n + 72) := by
  have hmod : (121 * n + 72) % 11 = 6 := by omega
  exact ramanujan_11_dvd_partitionCount_of_mod_eq_six (121 * n + 72) hmod

/-- `ZMod 11` form of the nested progression `121n+72`. -/
theorem ramanujan_partition_121n_plus_72_eq_zero_mod_11 (n : ℕ) :
    ((QseriesFormalization.Ch01.partitionCount (121 * n + 72) : ℕ) : ZMod 11) = 0 :=
  (ZMod.natCast_eq_zero_iff _ 11).mpr (ramanujan_11_dvd_p_121n_plus_72 n)

/-- Uniform nested arithmetic-progression corollary:
`11 ∣ p(121n + 11a + 6)`. -/
theorem ramanujan_11_dvd_p_121n_plus_11a_plus_6 (n a : ℕ) :
    11 ∣ QseriesFormalization.Ch01.partitionCount (121 * n + (11 * a + 6)) := by
  have hmod : (121 * n + (11 * a + 6)) % 11 = 6 := by omega
  exact ramanujan_11_dvd_partitionCount_of_mod_eq_six
    (121 * n + (11 * a + 6)) hmod

/-- `ZMod 11` form of the uniform nested progression `121n+11a+6`. -/
theorem ramanujan_partition_121n_plus_11a_plus_6_eq_zero_mod_11 (n a : ℕ) :
    ((QseriesFormalization.Ch01.partitionCount (121 * n + (11 * a + 6)) : ℕ) :
      ZMod 11) = 0 :=
  (ZMod.natCast_eq_zero_iff _ 11).mpr
    (ramanujan_11_dvd_p_121n_plus_11a_plus_6 n a)

/-- Concrete nested progression: `11 ∣ p(121n+6)`. -/
theorem ramanujan_11_dvd_p_121n_plus_6 (n : ℕ) :
    11 ∣ QseriesFormalization.Ch01.partitionCount (121 * n + 6) := by
  simpa using ramanujan_11_dvd_p_121n_plus_11a_plus_6 n 0

/-- `ZMod 11` form of the concrete nested progression `121n+6`. -/
theorem ramanujan_partition_121n_plus_6_eq_zero_mod_11 (n : ℕ) :
    ((QseriesFormalization.Ch01.partitionCount (121 * n + 6) : ℕ) : ZMod 11) = 0 :=
  (ZMod.natCast_eq_zero_iff _ 11).mpr (ramanujan_11_dvd_p_121n_plus_6 n)

/-- Concrete nested progression: `11 ∣ p(121n+17)`. -/
theorem ramanujan_11_dvd_p_121n_plus_17 (n : ℕ) :
    11 ∣ QseriesFormalization.Ch01.partitionCount (121 * n + 17) := by
  simpa [Nat.mul_one] using ramanujan_11_dvd_p_121n_plus_11a_plus_6 n 1

/-- `ZMod 11` form of the concrete nested progression `121n+17`. -/
theorem ramanujan_partition_121n_plus_17_eq_zero_mod_11 (n : ℕ) :
    ((QseriesFormalization.Ch01.partitionCount (121 * n + 17) : ℕ) : ZMod 11) = 0 :=
  (ZMod.natCast_eq_zero_iff _ 11).mpr (ramanujan_11_dvd_p_121n_plus_17 n)

/-- Concrete nested progression: `11 ∣ p(121n+116)`. -/
theorem ramanujan_11_dvd_p_121n_plus_116 (n : ℕ) :
    11 ∣ QseriesFormalization.Ch01.partitionCount (121 * n + 116) := by
  simpa using ramanujan_11_dvd_p_121n_plus_11a_plus_6 n 10

/-- Concrete nested progression: `p(121n+116) ≡ 0 (mod 11)`. -/
theorem ramanujan_partition_121n_plus_116_eq_zero_mod_11 (n : ℕ) :
    ((QseriesFormalization.Ch01.partitionCount (121 * n + 116) : ℕ) : ZMod 11) = 0 := by
  simpa using ramanujan_partition_121n_plus_11a_plus_6_eq_zero_mod_11 n 10

/-- Two-level nested arithmetic-progression corollary:
`11 ∣ p(1331n + 121a + 11b + 6)`. -/
theorem ramanujan_11_dvd_p_1331n_plus_121a_plus_11b_plus_6
    (n a b : ℕ) :
    11 ∣ QseriesFormalization.Ch01.partitionCount
      (1331 * n + 121 * a + 11 * b + 6) := by
  have hmod : (1331 * n + 121 * a + 11 * b + 6) % 11 = 6 := by omega
  exact ramanujan_11_dvd_partitionCount_of_mod_eq_six
    (1331 * n + 121 * a + 11 * b + 6) hmod

/-- `ZMod 11` form of the two-level nested progression
`1331n + 121a + 11b + 6`. -/
theorem ramanujan_partition_1331n_plus_121a_plus_11b_plus_6_eq_zero_mod_11
    (n a b : ℕ) :
    ((QseriesFormalization.Ch01.partitionCount
      (1331 * n + 121 * a + 11 * b + 6) : ℕ) : ZMod 11) = 0 :=
  (ZMod.natCast_eq_zero_iff _ 11).mpr
    (ramanujan_11_dvd_p_1331n_plus_121a_plus_11b_plus_6 n a b)

/-- Concrete two-level nested progression: `11 ∣ p(1331n+1326)`. -/
theorem ramanujan_11_dvd_p_1331n_plus_1326 (n : ℕ) :
    11 ∣ QseriesFormalization.Ch01.partitionCount (1331 * n + 1326) := by
  have hidx : 1331 * n + 1326 = 1331 * n + 121 * 10 + 11 * 10 + 6 := by omega
  rw [hidx]
  exact ramanujan_11_dvd_p_1331n_plus_121a_plus_11b_plus_6 n 10 10

/-- `ZMod 11` form of the concrete progression `1331n+1326`. -/
theorem ramanujan_partition_1331n_plus_1326_eq_zero_mod_11 (n : ℕ) :
    ((QseriesFormalization.Ch01.partitionCount (1331 * n + 1326) : ℕ) : ZMod 11) = 0 := by
  have hidx : 1331 * n + 1326 = 1331 * n + 121 * 10 + 11 * 10 + 6 := by omega
  rw [hidx]
  exact ramanujan_partition_1331n_plus_121a_plus_11b_plus_6_eq_zero_mod_11 n 10 10

/-- Congruence-class form of Ramanujan's mod-5 partition congruence. -/
theorem ramanujan_5_dvd_partitionCount_of_mod_eq_four
    (m : ℕ) (hm : m % 5 = 4) :
    5 ∣ QseriesFormalization.Ch01.partitionCount m := by
  have hm_decomp : m = 5 * (m / 5) + 4 := by
    have h := (Nat.mod_add_div m 5).symm
    omega
  rw [hm_decomp]
  exact QseriesFormalization.PartIV.Ch17.ramanujan_5_dvd_p_5n_plus_4 (m / 5)

/-- Congruence-class form of Ramanujan's mod-7 partition congruence. -/
theorem ramanujan_7_dvd_partitionCount_of_mod_eq_five
    (m : ℕ) (hm : m % 7 = 5) :
    7 ∣ QseriesFormalization.Ch01.partitionCount m := by
  have hm_decomp : m = 7 * (m / 7) + 5 := by
    have h := (Nat.mod_add_div m 7).symm
    omega
  rw [hm_decomp]
  exact QseriesFormalization.Pending.Ch17p7.ramanujan_7_dvd_p_7n_plus_5 (m / 7)

/-- `ZMod 5` form for every index in residue class `4`. -/
theorem ramanujan_partition_mod_5_eq_zero_of_mod_eq_four
    (m : ℕ) (hm : m % 5 = 4) :
    ((QseriesFormalization.Ch01.partitionCount m : ℕ) : ZMod 5) = 0 :=
  (ZMod.natCast_eq_zero_iff _ 5).mpr
    (ramanujan_5_dvd_partitionCount_of_mod_eq_four m hm)

/-- `ZMod 7` form for every index in residue class `5`. -/
theorem ramanujan_partition_mod_7_eq_zero_of_mod_eq_five
    (m : ℕ) (hm : m % 7 = 5) :
    ((QseriesFormalization.Ch01.partitionCount m : ℕ) : ZMod 7) = 0 :=
  (ZMod.natCast_eq_zero_iff _ 7).mpr
    (ramanujan_7_dvd_partitionCount_of_mod_eq_five m hm)

/-- Uniform nested arithmetic-progression corollary for the mod-5 Ramanujan
congruence: `5 ∣ p(25n + 5a + 4)`. -/
theorem ramanujan_5_dvd_p_25n_plus_5a_plus_4 (n a : ℕ) :
    5 ∣ QseriesFormalization.Ch01.partitionCount (25 * n + 5 * a + 4) := by
  have hmod : (25 * n + 5 * a + 4) % 5 = 4 := by omega
  exact ramanujan_5_dvd_partitionCount_of_mod_eq_four
    (25 * n + 5 * a + 4) hmod

/-- `ZMod 5` form of the nested progression `25n+5a+4`. -/
theorem ramanujan_partition_25n_plus_5a_plus_4_eq_zero_mod_5 (n a : ℕ) :
    ((QseriesFormalization.Ch01.partitionCount (25 * n + 5 * a + 4) : ℕ) :
      ZMod 5) = 0 :=
  (ZMod.natCast_eq_zero_iff _ 5).mpr
    (ramanujan_5_dvd_p_25n_plus_5a_plus_4 n a)

/-- Two-level nested arithmetic-progression corollary for the mod-5 Ramanujan
congruence: `5 ∣ p(125n + 25a + 5b + 4)`. -/
theorem ramanujan_5_dvd_p_125n_plus_25a_plus_5b_plus_4 (n a b : ℕ) :
    5 ∣ QseriesFormalization.Ch01.partitionCount (125 * n + 25 * a + 5 * b + 4) := by
  have hmod : (125 * n + 25 * a + 5 * b + 4) % 5 = 4 := by omega
  exact ramanujan_5_dvd_partitionCount_of_mod_eq_four
    (125 * n + 25 * a + 5 * b + 4) hmod

/-- `ZMod 5` form of the two-level nested progression
`125n+25a+5b+4`. -/
theorem ramanujan_partition_125n_plus_25a_plus_5b_plus_4_eq_zero_mod_5
    (n a b : ℕ) :
    ((QseriesFormalization.Ch01.partitionCount (125 * n + 25 * a + 5 * b + 4) : ℕ) :
      ZMod 5) = 0 :=
  (ZMod.natCast_eq_zero_iff _ 5).mpr
    (ramanujan_5_dvd_p_125n_plus_25a_plus_5b_plus_4 n a b)

/-- Concrete two-level mod-5 progression: `5 ∣ p(125n+124)`. -/
theorem ramanujan_5_dvd_p_125n_plus_124 (n : ℕ) :
    5 ∣ QseriesFormalization.Ch01.partitionCount (125 * n + 124) := by
  have hmod : (125 * n + 124) % 5 = 4 := by omega
  exact ramanujan_5_dvd_partitionCount_of_mod_eq_four (125 * n + 124) hmod

/-- `ZMod 5` form of the concrete progression `125n+124`. -/
theorem ramanujan_partition_125n_plus_124_eq_zero_mod_5 (n : ℕ) :
    ((QseriesFormalization.Ch01.partitionCount (125 * n + 124) : ℕ) : ZMod 5) = 0 := by
  have hmod : (125 * n + 124) % 5 = 4 := by omega
  exact ramanujan_partition_mod_5_eq_zero_of_mod_eq_four (125 * n + 124) hmod

/-- Uniform nested arithmetic-progression corollary for the mod-7 Ramanujan
congruence: `7 ∣ p(49n + 7a + 5)`. -/
theorem ramanujan_7_dvd_p_49n_plus_7a_plus_5 (n a : ℕ) :
    7 ∣ QseriesFormalization.Ch01.partitionCount (49 * n + 7 * a + 5) := by
  have hmod : (49 * n + 7 * a + 5) % 7 = 5 := by omega
  exact ramanujan_7_dvd_partitionCount_of_mod_eq_five
    (49 * n + 7 * a + 5) hmod

/-- `ZMod 7` form of the nested progression `49n+7a+5`. -/
theorem ramanujan_partition_49n_plus_7a_plus_5_eq_zero_mod_7 (n a : ℕ) :
    ((QseriesFormalization.Ch01.partitionCount (49 * n + 7 * a + 5) : ℕ) :
      ZMod 7) = 0 :=
  (ZMod.natCast_eq_zero_iff _ 7).mpr
    (ramanujan_7_dvd_p_49n_plus_7a_plus_5 n a)

/-- Two-level nested arithmetic-progression corollary for the mod-7 Ramanujan
congruence: `7 ∣ p(343n + 49a + 7b + 5)`. -/
theorem ramanujan_7_dvd_p_343n_plus_49a_plus_7b_plus_5 (n a b : ℕ) :
    7 ∣ QseriesFormalization.Ch01.partitionCount (343 * n + 49 * a + 7 * b + 5) := by
  have hmod : (343 * n + 49 * a + 7 * b + 5) % 7 = 5 := by omega
  exact ramanujan_7_dvd_partitionCount_of_mod_eq_five
    (343 * n + 49 * a + 7 * b + 5) hmod

/-- `ZMod 7` form of the two-level nested progression
`343n+49a+7b+5`. -/
theorem ramanujan_partition_343n_plus_49a_plus_7b_plus_5_eq_zero_mod_7
    (n a b : ℕ) :
    ((QseriesFormalization.Ch01.partitionCount (343 * n + 49 * a + 7 * b + 5) : ℕ) :
      ZMod 7) = 0 :=
  (ZMod.natCast_eq_zero_iff _ 7).mpr
    (ramanujan_7_dvd_p_343n_plus_49a_plus_7b_plus_5 n a b)

/-- Concrete two-level mod-7 progression: `7 ∣ p(343n+341)`. -/
theorem ramanujan_7_dvd_p_343n_plus_341 (n : ℕ) :
    7 ∣ QseriesFormalization.Ch01.partitionCount (343 * n + 341) := by
  have hmod : (343 * n + 341) % 7 = 5 := by omega
  exact ramanujan_7_dvd_partitionCount_of_mod_eq_five (343 * n + 341) hmod

/-- `ZMod 7` form of the concrete progression `343n+341`. -/
theorem ramanujan_partition_343n_plus_341_eq_zero_mod_7 (n : ℕ) :
    ((QseriesFormalization.Ch01.partitionCount (343 * n + 341) : ℕ) : ZMod 7) = 0 := by
  have hmod : (343 * n + 341) % 7 = 5 := by omega
  exact ramanujan_partition_mod_7_eq_zero_of_mod_eq_five (343 * n + 341) hmod

/-- Concrete one-level mod-5 progression: `5 ∣ p(25n+24)`. -/
theorem ramanujan_5_dvd_p_25n_plus_24 (n : ℕ) :
    5 ∣ QseriesFormalization.Ch01.partitionCount (25 * n + 24) := by
  have hidx : 25 * n + 24 = 25 * n + 5 * 4 + 4 := by omega
  rw [hidx]
  exact ramanujan_5_dvd_p_25n_plus_5a_plus_4 n 4

/-- `ZMod 5` form of the concrete one-level progression `25n+24`. -/
theorem ramanujan_partition_25n_plus_24_eq_zero_mod_5 (n : ℕ) :
    ((QseriesFormalization.Ch01.partitionCount (25 * n + 24) : ℕ) : ZMod 5) = 0 := by
  have hidx : 25 * n + 24 = 25 * n + 5 * 4 + 4 := by omega
  rw [hidx]
  exact ramanujan_partition_25n_plus_5a_plus_4_eq_zero_mod_5 n 4

/-- Concrete one-level mod-7 progression: `7 ∣ p(49n+47)`. -/
theorem ramanujan_7_dvd_p_49n_plus_47 (n : ℕ) :
    7 ∣ QseriesFormalization.Ch01.partitionCount (49 * n + 47) := by
  have hidx : 49 * n + 47 = 49 * n + 7 * 6 + 5 := by omega
  rw [hidx]
  exact ramanujan_7_dvd_p_49n_plus_7a_plus_5 n 6

/-- `ZMod 7` form of the concrete one-level progression `49n+47`. -/
theorem ramanujan_partition_49n_plus_47_eq_zero_mod_7 (n : ℕ) :
    ((QseriesFormalization.Ch01.partitionCount (49 * n + 47) : ℕ) : ZMod 7) = 0 := by
  have hidx : 49 * n + 47 = 49 * n + 7 * 6 + 5 := by omega
  rw [hidx]
  exact ramanujan_partition_49n_plus_7a_plus_5_eq_zero_mod_7 n 6

/-- One-level nested forms of the three classical Ramanujan partition
congruences. -/
theorem ramanujan_classical_partition_congruences_nested_one_level :
    (∀ n a, 5 ∣ QseriesFormalization.Ch01.partitionCount
      (25 * n + 5 * a + 4)) ∧
      (∀ n a, 7 ∣ QseriesFormalization.Ch01.partitionCount
        (49 * n + 7 * a + 5)) ∧
      (∀ n a, 11 ∣ QseriesFormalization.Ch01.partitionCount
        (121 * n + 11 * a + 6)) := by
  exact ⟨ramanujan_5_dvd_p_25n_plus_5a_plus_4,
    ramanujan_7_dvd_p_49n_plus_7a_plus_5,
    ramanujan_11_dvd_p_121n_plus_11a_plus_6⟩

/-- `ZMod` one-level nested forms of the three classical Ramanujan partition
congruences. -/
theorem ramanujan_classical_partition_congruences_nested_one_level_zmod :
    (∀ n a,
      ((QseriesFormalization.Ch01.partitionCount
        (25 * n + 5 * a + 4) : ℕ) : ZMod 5) = 0) ∧
      (∀ n a,
        ((QseriesFormalization.Ch01.partitionCount
          (49 * n + 7 * a + 5) : ℕ) : ZMod 7) = 0) ∧
      (∀ n a,
        ((QseriesFormalization.Ch01.partitionCount
          (121 * n + 11 * a + 6) : ℕ) : ZMod 11) = 0) := by
  exact ⟨ramanujan_partition_25n_plus_5a_plus_4_eq_zero_mod_5,
    ramanujan_partition_49n_plus_7a_plus_5_eq_zero_mod_7,
    ramanujan_partition_121n_plus_11a_plus_6_eq_zero_mod_11⟩

/-- Concrete one-level residue representatives for the three nested classical
Ramanujan partition congruences. -/
theorem ramanujan_classical_partition_congruences_one_level_concrete :
    (∀ n, 5 ∣ QseriesFormalization.Ch01.partitionCount (25 * n + 24)) ∧
      (∀ n, 7 ∣ QseriesFormalization.Ch01.partitionCount (49 * n + 47)) ∧
      (∀ n, 11 ∣ QseriesFormalization.Ch01.partitionCount (121 * n + 116)) := by
  exact ⟨ramanujan_5_dvd_p_25n_plus_24,
    ramanujan_7_dvd_p_49n_plus_47,
    ramanujan_11_dvd_p_121n_plus_116⟩

/-- `ZMod` form of the concrete one-level residue representatives. -/
theorem ramanujan_classical_partition_congruences_one_level_concrete_zmod :
    (∀ n, ((QseriesFormalization.Ch01.partitionCount (25 * n + 24) : ℕ) : ZMod 5) = 0) ∧
      (∀ n, ((QseriesFormalization.Ch01.partitionCount (49 * n + 47) : ℕ) : ZMod 7) = 0) ∧
      (∀ n, ((QseriesFormalization.Ch01.partitionCount (121 * n + 116) : ℕ) : ZMod 11) = 0) := by
  exact ⟨ramanujan_partition_25n_plus_24_eq_zero_mod_5,
    ramanujan_partition_49n_plus_47_eq_zero_mod_7,
    ramanujan_partition_121n_plus_116_eq_zero_mod_11⟩

/-- Two-level nested forms of the three classical Ramanujan partition
congruences. -/
theorem ramanujan_classical_partition_congruences_nested_two_level :
    (∀ n a b, 5 ∣ QseriesFormalization.Ch01.partitionCount
      (125 * n + 25 * a + 5 * b + 4)) ∧
      (∀ n a b, 7 ∣ QseriesFormalization.Ch01.partitionCount
        (343 * n + 49 * a + 7 * b + 5)) ∧
      (∀ n a b, 11 ∣ QseriesFormalization.Ch01.partitionCount
        (1331 * n + 121 * a + 11 * b + 6)) := by
  exact ⟨ramanujan_5_dvd_p_125n_plus_25a_plus_5b_plus_4,
    ramanujan_7_dvd_p_343n_plus_49a_plus_7b_plus_5,
    ramanujan_11_dvd_p_1331n_plus_121a_plus_11b_plus_6⟩

/-- `ZMod` two-level nested forms of the three classical Ramanujan partition
congruences. -/
theorem ramanujan_classical_partition_congruences_nested_two_level_zmod :
    (∀ n a b,
      ((QseriesFormalization.Ch01.partitionCount
        (125 * n + 25 * a + 5 * b + 4) : ℕ) : ZMod 5) = 0) ∧
      (∀ n a b,
        ((QseriesFormalization.Ch01.partitionCount
          (343 * n + 49 * a + 7 * b + 5) : ℕ) : ZMod 7) = 0) ∧
      (∀ n a b,
        ((QseriesFormalization.Ch01.partitionCount
          (1331 * n + 121 * a + 11 * b + 6) : ℕ) : ZMod 11) = 0) := by
  exact ⟨ramanujan_partition_125n_plus_25a_plus_5b_plus_4_eq_zero_mod_5,
    ramanujan_partition_343n_plus_49a_plus_7b_plus_5_eq_zero_mod_7,
    ramanujan_partition_1331n_plus_121a_plus_11b_plus_6_eq_zero_mod_11⟩

/-- Concrete deepest residue representatives for the three nested classical
Ramanujan partition congruences. -/
theorem ramanujan_classical_partition_congruences_deep_concrete :
    (∀ n, 5 ∣ QseriesFormalization.Ch01.partitionCount (125 * n + 124)) ∧
      (∀ n, 7 ∣ QseriesFormalization.Ch01.partitionCount (343 * n + 341)) ∧
      (∀ n, 11 ∣ QseriesFormalization.Ch01.partitionCount (1331 * n + 1326)) := by
  exact ⟨ramanujan_5_dvd_p_125n_plus_124,
    ramanujan_7_dvd_p_343n_plus_341,
    ramanujan_11_dvd_p_1331n_plus_1326⟩

/-- `ZMod` form of the concrete deepest residue representatives. -/
theorem ramanujan_classical_partition_congruences_deep_concrete_zmod :
    (∀ n, ((QseriesFormalization.Ch01.partitionCount (125 * n + 124) : ℕ) : ZMod 5) = 0) ∧
      (∀ n, ((QseriesFormalization.Ch01.partitionCount (343 * n + 341) : ℕ) : ZMod 7) = 0) ∧
      (∀ n, ((QseriesFormalization.Ch01.partitionCount (1331 * n + 1326) : ℕ) : ZMod 11) = 0) := by
  exact ⟨ramanujan_partition_125n_plus_124_eq_zero_mod_5,
    ramanujan_partition_343n_plus_341_eq_zero_mod_7,
    ramanujan_partition_1331n_plus_1326_eq_zero_mod_11⟩

/-- Three-level nested arithmetic-progression corollary for the mod-5
Ramanujan congruence: `5 ∣ p(625n + 125a + 25b + 5c + 4)`. -/
theorem ramanujan_5_dvd_p_625n_plus_125a_plus_25b_plus_5c_plus_4
    (n a b c : ℕ) :
    5 ∣ QseriesFormalization.Ch01.partitionCount
      (625 * n + 125 * a + 25 * b + 5 * c + 4) := by
  have hmod : (625 * n + 125 * a + 25 * b + 5 * c + 4) % 5 = 4 := by omega
  exact ramanujan_5_dvd_partitionCount_of_mod_eq_four
    (625 * n + 125 * a + 25 * b + 5 * c + 4) hmod

/-- `ZMod 5` form of the three-level nested progression
`625n+125a+25b+5c+4`. -/
theorem ramanujan_partition_625n_plus_125a_plus_25b_plus_5c_plus_4_eq_zero_mod_5
    (n a b c : ℕ) :
    ((QseriesFormalization.Ch01.partitionCount
      (625 * n + 125 * a + 25 * b + 5 * c + 4) : ℕ) : ZMod 5) = 0 :=
  (ZMod.natCast_eq_zero_iff _ 5).mpr
    (ramanujan_5_dvd_p_625n_plus_125a_plus_25b_plus_5c_plus_4 n a b c)

/-- Concrete three-level mod-5 progression: `5 ∣ p(625n+624)`. -/
theorem ramanujan_5_dvd_p_625n_plus_624 (n : ℕ) :
    5 ∣ QseriesFormalization.Ch01.partitionCount (625 * n + 624) := by
  have hmod : (625 * n + 624) % 5 = 4 := by omega
  exact ramanujan_5_dvd_partitionCount_of_mod_eq_four (625 * n + 624) hmod

/-- `ZMod 5` form of the concrete progression `625n+624`. -/
theorem ramanujan_partition_625n_plus_624_eq_zero_mod_5 (n : ℕ) :
    ((QseriesFormalization.Ch01.partitionCount (625 * n + 624) : ℕ) : ZMod 5) = 0 := by
  have hmod : (625 * n + 624) % 5 = 4 := by omega
  exact ramanujan_partition_mod_5_eq_zero_of_mod_eq_four (625 * n + 624) hmod

/-- Three-level nested arithmetic-progression corollary for the mod-7
Ramanujan congruence: `7 ∣ p(2401n + 343a + 49b + 7c + 5)`. -/
theorem ramanujan_7_dvd_p_2401n_plus_343a_plus_49b_plus_7c_plus_5
    (n a b c : ℕ) :
    7 ∣ QseriesFormalization.Ch01.partitionCount
      (2401 * n + 343 * a + 49 * b + 7 * c + 5) := by
  have hmod : (2401 * n + 343 * a + 49 * b + 7 * c + 5) % 7 = 5 := by omega
  exact ramanujan_7_dvd_partitionCount_of_mod_eq_five
    (2401 * n + 343 * a + 49 * b + 7 * c + 5) hmod

/-- `ZMod 7` form of the three-level nested progression
`2401n+343a+49b+7c+5`. -/
theorem ramanujan_partition_2401n_plus_343a_plus_49b_plus_7c_plus_5_eq_zero_mod_7
    (n a b c : ℕ) :
    ((QseriesFormalization.Ch01.partitionCount
      (2401 * n + 343 * a + 49 * b + 7 * c + 5) : ℕ) : ZMod 7) = 0 :=
  (ZMod.natCast_eq_zero_iff _ 7).mpr
    (ramanujan_7_dvd_p_2401n_plus_343a_plus_49b_plus_7c_plus_5 n a b c)

/-- Concrete three-level mod-7 progression: `7 ∣ p(2401n+2399)`. -/
theorem ramanujan_7_dvd_p_2401n_plus_2399 (n : ℕ) :
    7 ∣ QseriesFormalization.Ch01.partitionCount (2401 * n + 2399) := by
  have hmod : (2401 * n + 2399) % 7 = 5 := by omega
  exact ramanujan_7_dvd_partitionCount_of_mod_eq_five (2401 * n + 2399) hmod

/-- `ZMod 7` form of the concrete progression `2401n+2399`. -/
theorem ramanujan_partition_2401n_plus_2399_eq_zero_mod_7 (n : ℕ) :
    ((QseriesFormalization.Ch01.partitionCount (2401 * n + 2399) : ℕ) : ZMod 7) = 0 := by
  have hmod : (2401 * n + 2399) % 7 = 5 := by omega
  exact ramanujan_partition_mod_7_eq_zero_of_mod_eq_five (2401 * n + 2399) hmod

/-- Three-level nested arithmetic-progression corollary for the mod-11
Ramanujan congruence: `11 ∣ p(14641n + 1331a + 121b + 11c + 6)`. -/
theorem ramanujan_11_dvd_p_14641n_plus_1331a_plus_121b_plus_11c_plus_6
    (n a b c : ℕ) :
    11 ∣ QseriesFormalization.Ch01.partitionCount
      (14641 * n + 1331 * a + 121 * b + 11 * c + 6) := by
  have hmod : (14641 * n + 1331 * a + 121 * b + 11 * c + 6) % 11 = 6 := by omega
  exact ramanujan_11_dvd_partitionCount_of_mod_eq_six
    (14641 * n + 1331 * a + 121 * b + 11 * c + 6) hmod

/-- `ZMod 11` form of the three-level nested progression
`14641n+1331a+121b+11c+6`. -/
theorem ramanujan_partition_14641n_plus_1331a_plus_121b_plus_11c_plus_6_eq_zero_mod_11
    (n a b c : ℕ) :
    ((QseriesFormalization.Ch01.partitionCount
      (14641 * n + 1331 * a + 121 * b + 11 * c + 6) : ℕ) : ZMod 11) = 0 :=
  (ZMod.natCast_eq_zero_iff _ 11).mpr
    (ramanujan_11_dvd_p_14641n_plus_1331a_plus_121b_plus_11c_plus_6 n a b c)

/-- Concrete three-level mod-11 progression: `11 ∣ p(14641n+14636)`. -/
theorem ramanujan_11_dvd_p_14641n_plus_14636 (n : ℕ) :
    11 ∣ QseriesFormalization.Ch01.partitionCount (14641 * n + 14636) := by
  have hmod : (14641 * n + 14636) % 11 = 6 := by omega
  exact ramanujan_11_dvd_partitionCount_of_mod_eq_six (14641 * n + 14636) hmod

/-- `ZMod 11` form of the concrete progression `14641n+14636`. -/
theorem ramanujan_partition_14641n_plus_14636_eq_zero_mod_11 (n : ℕ) :
    ((QseriesFormalization.Ch01.partitionCount (14641 * n + 14636) : ℕ) : ZMod 11) = 0 := by
  have hmod : (14641 * n + 14636) % 11 = 6 := by omega
  exact ramanujan_partition_mod_11_eq_zero_of_mod_eq_six (14641 * n + 14636) hmod

/-- Three-level nested forms of the three classical Ramanujan partition
congruences. -/
theorem ramanujan_classical_partition_congruences_nested_three_level :
    (∀ n a b c, 5 ∣ QseriesFormalization.Ch01.partitionCount
      (625 * n + 125 * a + 25 * b + 5 * c + 4)) ∧
      (∀ n a b c, 7 ∣ QseriesFormalization.Ch01.partitionCount
        (2401 * n + 343 * a + 49 * b + 7 * c + 5)) ∧
      (∀ n a b c, 11 ∣ QseriesFormalization.Ch01.partitionCount
        (14641 * n + 1331 * a + 121 * b + 11 * c + 6)) := by
  exact ⟨ramanujan_5_dvd_p_625n_plus_125a_plus_25b_plus_5c_plus_4,
    ramanujan_7_dvd_p_2401n_plus_343a_plus_49b_plus_7c_plus_5,
    ramanujan_11_dvd_p_14641n_plus_1331a_plus_121b_plus_11c_plus_6⟩

/-- `ZMod` three-level nested forms of the three classical Ramanujan partition
congruences. -/
theorem ramanujan_classical_partition_congruences_nested_three_level_zmod :
    (∀ n a b c,
      ((QseriesFormalization.Ch01.partitionCount
        (625 * n + 125 * a + 25 * b + 5 * c + 4) : ℕ) : ZMod 5) = 0) ∧
      (∀ n a b c,
        ((QseriesFormalization.Ch01.partitionCount
          (2401 * n + 343 * a + 49 * b + 7 * c + 5) : ℕ) : ZMod 7) = 0) ∧
      (∀ n a b c,
        ((QseriesFormalization.Ch01.partitionCount
          (14641 * n + 1331 * a + 121 * b + 11 * c + 6) : ℕ) : ZMod 11) = 0) := by
  exact ⟨ramanujan_partition_625n_plus_125a_plus_25b_plus_5c_plus_4_eq_zero_mod_5,
    ramanujan_partition_2401n_plus_343a_plus_49b_plus_7c_plus_5_eq_zero_mod_7,
    ramanujan_partition_14641n_plus_1331a_plus_121b_plus_11c_plus_6_eq_zero_mod_11⟩

/-- Concrete three-level deepest residue representatives for the three nested
classical Ramanujan partition congruences. -/
theorem ramanujan_classical_partition_congruences_three_level_concrete :
    (∀ n, 5 ∣ QseriesFormalization.Ch01.partitionCount (625 * n + 624)) ∧
      (∀ n, 7 ∣ QseriesFormalization.Ch01.partitionCount (2401 * n + 2399)) ∧
      (∀ n, 11 ∣ QseriesFormalization.Ch01.partitionCount (14641 * n + 14636)) := by
  exact ⟨ramanujan_5_dvd_p_625n_plus_624,
    ramanujan_7_dvd_p_2401n_plus_2399,
    ramanujan_11_dvd_p_14641n_plus_14636⟩

/-- `ZMod` form of the concrete three-level deepest residue representatives. -/
theorem ramanujan_classical_partition_congruences_three_level_concrete_zmod :
    (∀ n, ((QseriesFormalization.Ch01.partitionCount (625 * n + 624) : ℕ) : ZMod 5) = 0) ∧
      (∀ n, ((QseriesFormalization.Ch01.partitionCount (2401 * n + 2399) : ℕ) : ZMod 7) = 0) ∧
      (∀ n, ((QseriesFormalization.Ch01.partitionCount (14641 * n + 14636) : ℕ) : ZMod 11) = 0) := by
  exact ⟨ramanujan_partition_625n_plus_624_eq_zero_mod_5,
    ramanujan_partition_2401n_plus_2399_eq_zero_mod_7,
    ramanujan_partition_14641n_plus_14636_eq_zero_mod_11⟩

/-- Four-level nested arithmetic-progression corollary for the mod-5
Ramanujan congruence: `5 ∣ p(3125n + 625a + 125b + 25c + 5d + 4)`. -/
theorem ramanujan_5_dvd_p_3125n_plus_625a_plus_125b_plus_25c_plus_5d_plus_4
    (n a b c d : ℕ) :
    5 ∣ QseriesFormalization.Ch01.partitionCount
      (3125 * n + 625 * a + 125 * b + 25 * c + 5 * d + 4) := by
  have hmod : (3125 * n + 625 * a + 125 * b + 25 * c + 5 * d + 4) % 5 = 4 := by
    omega
  exact ramanujan_5_dvd_partitionCount_of_mod_eq_four
    (3125 * n + 625 * a + 125 * b + 25 * c + 5 * d + 4) hmod

/-- `ZMod 5` form of the four-level nested progression
`3125n+625a+125b+25c+5d+4`. -/
theorem ramanujan_partition_3125n_plus_625a_plus_125b_plus_25c_plus_5d_plus_4_eq_zero_mod_5
    (n a b c d : ℕ) :
    ((QseriesFormalization.Ch01.partitionCount
      (3125 * n + 625 * a + 125 * b + 25 * c + 5 * d + 4) : ℕ) : ZMod 5) = 0 :=
  (ZMod.natCast_eq_zero_iff _ 5).mpr
    (ramanujan_5_dvd_p_3125n_plus_625a_plus_125b_plus_25c_plus_5d_plus_4 n a b c d)

/-- Concrete four-level mod-5 progression: `5 ∣ p(3125n+3124)`. -/
theorem ramanujan_5_dvd_p_3125n_plus_3124 (n : ℕ) :
    5 ∣ QseriesFormalization.Ch01.partitionCount (3125 * n + 3124) := by
  have hmod : (3125 * n + 3124) % 5 = 4 := by omega
  exact ramanujan_5_dvd_partitionCount_of_mod_eq_four (3125 * n + 3124) hmod

/-- `ZMod 5` form of the concrete progression `3125n+3124`. -/
theorem ramanujan_partition_3125n_plus_3124_eq_zero_mod_5 (n : ℕ) :
    ((QseriesFormalization.Ch01.partitionCount (3125 * n + 3124) : ℕ) : ZMod 5) = 0 := by
  have hmod : (3125 * n + 3124) % 5 = 4 := by omega
  exact ramanujan_partition_mod_5_eq_zero_of_mod_eq_four (3125 * n + 3124) hmod

/-- Four-level nested arithmetic-progression corollary for the mod-7
Ramanujan congruence: `7 ∣ p(16807n + 2401a + 343b + 49c + 7d + 5)`. -/
theorem ramanujan_7_dvd_p_16807n_plus_2401a_plus_343b_plus_49c_plus_7d_plus_5
    (n a b c d : ℕ) :
    7 ∣ QseriesFormalization.Ch01.partitionCount
      (16807 * n + 2401 * a + 343 * b + 49 * c + 7 * d + 5) := by
  have hmod : (16807 * n + 2401 * a + 343 * b + 49 * c + 7 * d + 5) % 7 = 5 := by
    omega
  exact ramanujan_7_dvd_partitionCount_of_mod_eq_five
    (16807 * n + 2401 * a + 343 * b + 49 * c + 7 * d + 5) hmod

/-- `ZMod 7` form of the four-level nested progression
`16807n+2401a+343b+49c+7d+5`. -/
theorem ramanujan_partition_16807n_plus_2401a_plus_343b_plus_49c_plus_7d_plus_5_eq_zero_mod_7
    (n a b c d : ℕ) :
    ((QseriesFormalization.Ch01.partitionCount
      (16807 * n + 2401 * a + 343 * b + 49 * c + 7 * d + 5) : ℕ) : ZMod 7) = 0 :=
  (ZMod.natCast_eq_zero_iff _ 7).mpr
    (ramanujan_7_dvd_p_16807n_plus_2401a_plus_343b_plus_49c_plus_7d_plus_5 n a b c d)

/-- Concrete four-level mod-7 progression: `7 ∣ p(16807n+16805)`. -/
theorem ramanujan_7_dvd_p_16807n_plus_16805 (n : ℕ) :
    7 ∣ QseriesFormalization.Ch01.partitionCount (16807 * n + 16805) := by
  have hmod : (16807 * n + 16805) % 7 = 5 := by omega
  exact ramanujan_7_dvd_partitionCount_of_mod_eq_five (16807 * n + 16805) hmod

/-- `ZMod 7` form of the concrete progression `16807n+16805`. -/
theorem ramanujan_partition_16807n_plus_16805_eq_zero_mod_7 (n : ℕ) :
    ((QseriesFormalization.Ch01.partitionCount (16807 * n + 16805) : ℕ) : ZMod 7) = 0 := by
  have hmod : (16807 * n + 16805) % 7 = 5 := by omega
  exact ramanujan_partition_mod_7_eq_zero_of_mod_eq_five (16807 * n + 16805) hmod

/-- Four-level nested arithmetic-progression corollary for the mod-11
Ramanujan congruence:
`11 ∣ p(161051n + 14641a + 1331b + 121c + 11d + 6)`. -/
theorem ramanujan_11_dvd_p_161051n_plus_14641a_plus_1331b_plus_121c_plus_11d_plus_6
    (n a b c d : ℕ) :
    11 ∣ QseriesFormalization.Ch01.partitionCount
      (161051 * n + 14641 * a + 1331 * b + 121 * c + 11 * d + 6) := by
  have hmod :
      (161051 * n + 14641 * a + 1331 * b + 121 * c + 11 * d + 6) % 11 = 6 := by
    omega
  exact ramanujan_11_dvd_partitionCount_of_mod_eq_six
    (161051 * n + 14641 * a + 1331 * b + 121 * c + 11 * d + 6) hmod

/-- `ZMod 11` form of the four-level nested progression
`161051n+14641a+1331b+121c+11d+6`. -/
theorem ramanujan_partition_161051n_plus_14641a_plus_1331b_plus_121c_plus_11d_plus_6_eq_zero_mod_11
    (n a b c d : ℕ) :
    ((QseriesFormalization.Ch01.partitionCount
      (161051 * n + 14641 * a + 1331 * b + 121 * c + 11 * d + 6) : ℕ) : ZMod 11) = 0 :=
  (ZMod.natCast_eq_zero_iff _ 11).mpr
    (ramanujan_11_dvd_p_161051n_plus_14641a_plus_1331b_plus_121c_plus_11d_plus_6 n a b c d)

/-- Concrete four-level mod-11 progression: `11 ∣ p(161051n+161046)`. -/
theorem ramanujan_11_dvd_p_161051n_plus_161046 (n : ℕ) :
    11 ∣ QseriesFormalization.Ch01.partitionCount (161051 * n + 161046) := by
  have hmod : (161051 * n + 161046) % 11 = 6 := by omega
  exact ramanujan_11_dvd_partitionCount_of_mod_eq_six (161051 * n + 161046) hmod

/-- `ZMod 11` form of the concrete progression `161051n+161046`. -/
theorem ramanujan_partition_161051n_plus_161046_eq_zero_mod_11 (n : ℕ) :
    ((QseriesFormalization.Ch01.partitionCount (161051 * n + 161046) : ℕ) : ZMod 11) = 0 := by
  have hmod : (161051 * n + 161046) % 11 = 6 := by omega
  exact ramanujan_partition_mod_11_eq_zero_of_mod_eq_six (161051 * n + 161046) hmod

/-- Four-level nested forms of the three classical Ramanujan partition
congruences. -/
theorem ramanujan_classical_partition_congruences_nested_four_level :
    (∀ n a b c d, 5 ∣ QseriesFormalization.Ch01.partitionCount
      (3125 * n + 625 * a + 125 * b + 25 * c + 5 * d + 4)) ∧
      (∀ n a b c d, 7 ∣ QseriesFormalization.Ch01.partitionCount
        (16807 * n + 2401 * a + 343 * b + 49 * c + 7 * d + 5)) ∧
      (∀ n a b c d, 11 ∣ QseriesFormalization.Ch01.partitionCount
        (161051 * n + 14641 * a + 1331 * b + 121 * c + 11 * d + 6)) := by
  exact ⟨ramanujan_5_dvd_p_3125n_plus_625a_plus_125b_plus_25c_plus_5d_plus_4,
    ramanujan_7_dvd_p_16807n_plus_2401a_plus_343b_plus_49c_plus_7d_plus_5,
    ramanujan_11_dvd_p_161051n_plus_14641a_plus_1331b_plus_121c_plus_11d_plus_6⟩

/-- `ZMod` four-level nested forms of the three classical Ramanujan partition
congruences. -/
theorem ramanujan_classical_partition_congruences_nested_four_level_zmod :
    (∀ n a b c d,
      ((QseriesFormalization.Ch01.partitionCount
        (3125 * n + 625 * a + 125 * b + 25 * c + 5 * d + 4) : ℕ) : ZMod 5) = 0) ∧
      (∀ n a b c d,
        ((QseriesFormalization.Ch01.partitionCount
          (16807 * n + 2401 * a + 343 * b + 49 * c + 7 * d + 5) : ℕ) : ZMod 7) = 0) ∧
      (∀ n a b c d,
        ((QseriesFormalization.Ch01.partitionCount
          (161051 * n + 14641 * a + 1331 * b + 121 * c + 11 * d + 6) : ℕ) :
            ZMod 11) = 0) := by
  exact ⟨ramanujan_partition_3125n_plus_625a_plus_125b_plus_25c_plus_5d_plus_4_eq_zero_mod_5,
    ramanujan_partition_16807n_plus_2401a_plus_343b_plus_49c_plus_7d_plus_5_eq_zero_mod_7,
    ramanujan_partition_161051n_plus_14641a_plus_1331b_plus_121c_plus_11d_plus_6_eq_zero_mod_11⟩

/-- Concrete four-level deepest residue representatives for the three nested
classical Ramanujan partition congruences. -/
theorem ramanujan_classical_partition_congruences_four_level_concrete :
    (∀ n, 5 ∣ QseriesFormalization.Ch01.partitionCount (3125 * n + 3124)) ∧
      (∀ n, 7 ∣ QseriesFormalization.Ch01.partitionCount (16807 * n + 16805)) ∧
      (∀ n, 11 ∣ QseriesFormalization.Ch01.partitionCount (161051 * n + 161046)) := by
  exact ⟨ramanujan_5_dvd_p_3125n_plus_3124,
    ramanujan_7_dvd_p_16807n_plus_16805,
    ramanujan_11_dvd_p_161051n_plus_161046⟩

/-- `ZMod` form of the concrete four-level deepest residue representatives. -/
theorem ramanujan_classical_partition_congruences_four_level_concrete_zmod :
    (∀ n, ((QseriesFormalization.Ch01.partitionCount (3125 * n + 3124) : ℕ) : ZMod 5) = 0) ∧
      (∀ n, ((QseriesFormalization.Ch01.partitionCount (16807 * n + 16805) : ℕ) : ZMod 7) = 0) ∧
      (∀ n, ((QseriesFormalization.Ch01.partitionCount (161051 * n + 161046) : ℕ) :
        ZMod 11) = 0) := by
  exact ⟨ramanujan_partition_3125n_plus_3124_eq_zero_mod_5,
    ramanujan_partition_16807n_plus_16805_eq_zero_mod_7,
    ramanujan_partition_161051n_plus_161046_eq_zero_mod_11⟩

/-- Stability of the mod-5 Ramanujan congruence under adding a multiple of `5`. -/
theorem ramanujan_5_dvd_partitionCount_add_five_mul_of_mod_eq_four
    (m k : ℕ) (hm : m % 5 = 4) :
    5 ∣ QseriesFormalization.Ch01.partitionCount (m + 5 * k) := by
  have hmod : (m + 5 * k) % 5 = 4 := by omega
  exact ramanujan_5_dvd_partitionCount_of_mod_eq_four (m + 5 * k) hmod

/-- `ZMod 5` form of stability under adding a multiple of `5`. -/
theorem ramanujan_partition_add_five_mul_eq_zero_mod_5_of_mod_eq_four
    (m k : ℕ) (hm : m % 5 = 4) :
    ((QseriesFormalization.Ch01.partitionCount (m + 5 * k) : ℕ) : ZMod 5) = 0 :=
  (ZMod.natCast_eq_zero_iff _ 5).mpr
    (ramanujan_5_dvd_partitionCount_add_five_mul_of_mod_eq_four m k hm)

/-- Stability of the mod-7 Ramanujan congruence under adding a multiple of `7`. -/
theorem ramanujan_7_dvd_partitionCount_add_seven_mul_of_mod_eq_five
    (m k : ℕ) (hm : m % 7 = 5) :
    7 ∣ QseriesFormalization.Ch01.partitionCount (m + 7 * k) := by
  have hmod : (m + 7 * k) % 7 = 5 := by omega
  exact ramanujan_7_dvd_partitionCount_of_mod_eq_five (m + 7 * k) hmod

/-- `ZMod 7` form of stability under adding a multiple of `7`. -/
theorem ramanujan_partition_add_seven_mul_eq_zero_mod_7_of_mod_eq_five
    (m k : ℕ) (hm : m % 7 = 5) :
    ((QseriesFormalization.Ch01.partitionCount (m + 7 * k) : ℕ) : ZMod 7) = 0 :=
  (ZMod.natCast_eq_zero_iff _ 7).mpr
    (ramanujan_7_dvd_partitionCount_add_seven_mul_of_mod_eq_five m k hm)

/-- Stability of the mod-11 Ramanujan congruence under adding a multiple of `11`. -/
theorem ramanujan_11_dvd_partitionCount_add_eleven_mul_of_mod_eq_six
    (m k : ℕ) (hm : m % 11 = 6) :
    11 ∣ QseriesFormalization.Ch01.partitionCount (m + 11 * k) := by
  have hmod : (m + 11 * k) % 11 = 6 := by omega
  exact ramanujan_11_dvd_partitionCount_of_mod_eq_six (m + 11 * k) hmod

/-- `ZMod 11` form of stability under adding a multiple of `11`. -/
theorem ramanujan_partition_add_eleven_mul_eq_zero_mod_11_of_mod_eq_six
    (m k : ℕ) (hm : m % 11 = 6) :
    ((QseriesFormalization.Ch01.partitionCount (m + 11 * k) : ℕ) : ZMod 11) = 0 :=
  (ZMod.natCast_eq_zero_iff _ 11).mpr
    (ramanujan_11_dvd_partitionCount_add_eleven_mul_of_mod_eq_six m k hm)

/-- Stability under adding a multiple of the relevant modulus, assembled for
the three classical Ramanujan congruences. -/
theorem ramanujan_classical_partition_congruences_add_modulus_multiple :
    (∀ m k, m % 5 = 4 →
      5 ∣ QseriesFormalization.Ch01.partitionCount (m + 5 * k)) ∧
      (∀ m k, m % 7 = 5 →
        7 ∣ QseriesFormalization.Ch01.partitionCount (m + 7 * k)) ∧
      (∀ m k, m % 11 = 6 →
        11 ∣ QseriesFormalization.Ch01.partitionCount (m + 11 * k)) := by
  exact ⟨ramanujan_5_dvd_partitionCount_add_five_mul_of_mod_eq_four,
    ramanujan_7_dvd_partitionCount_add_seven_mul_of_mod_eq_five,
    ramanujan_11_dvd_partitionCount_add_eleven_mul_of_mod_eq_six⟩

/-- `ZMod` stability under adding a multiple of the relevant modulus. -/
theorem ramanujan_classical_partition_congruences_add_modulus_multiple_zmod :
    (∀ m k, m % 5 = 4 →
      ((QseriesFormalization.Ch01.partitionCount (m + 5 * k) : ℕ) : ZMod 5) = 0) ∧
      (∀ m k, m % 7 = 5 →
        ((QseriesFormalization.Ch01.partitionCount (m + 7 * k) : ℕ) : ZMod 7) = 0) ∧
      (∀ m k, m % 11 = 6 →
        ((QseriesFormalization.Ch01.partitionCount (m + 11 * k) : ℕ) : ZMod 11) = 0) := by
  exact ⟨ramanujan_partition_add_five_mul_eq_zero_mod_5_of_mod_eq_four,
    ramanujan_partition_add_seven_mul_eq_zero_mod_7_of_mod_eq_five,
    ramanujan_partition_add_eleven_mul_eq_zero_mod_11_of_mod_eq_six⟩

/-- Stability of the mod-5 Ramanujan congruence under adding a multiple of `5`
on the left. -/
theorem ramanujan_5_dvd_partitionCount_five_mul_add_of_mod_eq_four
    (m k : ℕ) (hm : m % 5 = 4) :
    5 ∣ QseriesFormalization.Ch01.partitionCount (5 * k + m) := by
  have h := ramanujan_5_dvd_partitionCount_add_five_mul_of_mod_eq_four m k hm
  have harg : 5 * k + m = m + 5 * k := by omega
  simpa [harg] using h

/-- `ZMod 5` form of stability under adding a multiple of `5` on the left. -/
theorem ramanujan_partition_five_mul_add_eq_zero_mod_5_of_mod_eq_four
    (m k : ℕ) (hm : m % 5 = 4) :
    ((QseriesFormalization.Ch01.partitionCount (5 * k + m) : ℕ) : ZMod 5) = 0 :=
  (ZMod.natCast_eq_zero_iff _ 5).mpr
    (ramanujan_5_dvd_partitionCount_five_mul_add_of_mod_eq_four m k hm)

/-- Stability of the mod-7 Ramanujan congruence under adding a multiple of `7`
on the left. -/
theorem ramanujan_7_dvd_partitionCount_seven_mul_add_of_mod_eq_five
    (m k : ℕ) (hm : m % 7 = 5) :
    7 ∣ QseriesFormalization.Ch01.partitionCount (7 * k + m) := by
  have h := ramanujan_7_dvd_partitionCount_add_seven_mul_of_mod_eq_five m k hm
  have harg : 7 * k + m = m + 7 * k := by omega
  simpa [harg] using h

/-- `ZMod 7` form of stability under adding a multiple of `7` on the left. -/
theorem ramanujan_partition_seven_mul_add_eq_zero_mod_7_of_mod_eq_five
    (m k : ℕ) (hm : m % 7 = 5) :
    ((QseriesFormalization.Ch01.partitionCount (7 * k + m) : ℕ) : ZMod 7) = 0 :=
  (ZMod.natCast_eq_zero_iff _ 7).mpr
    (ramanujan_7_dvd_partitionCount_seven_mul_add_of_mod_eq_five m k hm)

/-- Stability of the mod-11 Ramanujan congruence under adding a multiple of
`11` on the left. -/
theorem ramanujan_11_dvd_partitionCount_eleven_mul_add_of_mod_eq_six
    (m k : ℕ) (hm : m % 11 = 6) :
    11 ∣ QseriesFormalization.Ch01.partitionCount (11 * k + m) := by
  have h := ramanujan_11_dvd_partitionCount_add_eleven_mul_of_mod_eq_six m k hm
  have harg : 11 * k + m = m + 11 * k := by omega
  simpa [harg] using h

/-- `ZMod 11` form of stability under adding a multiple of `11` on the left. -/
theorem ramanujan_partition_eleven_mul_add_eq_zero_mod_11_of_mod_eq_six
    (m k : ℕ) (hm : m % 11 = 6) :
    ((QseriesFormalization.Ch01.partitionCount (11 * k + m) : ℕ) : ZMod 11) = 0 :=
  (ZMod.natCast_eq_zero_iff _ 11).mpr
    (ramanujan_11_dvd_partitionCount_eleven_mul_add_of_mod_eq_six m k hm)

/-- Stability under adding a multiple of the relevant modulus on the left,
assembled for the three classical Ramanujan congruences. -/
theorem ramanujan_classical_partition_congruences_modulus_multiple_add :
    (∀ m k, m % 5 = 4 →
      5 ∣ QseriesFormalization.Ch01.partitionCount (5 * k + m)) ∧
      (∀ m k, m % 7 = 5 →
        7 ∣ QseriesFormalization.Ch01.partitionCount (7 * k + m)) ∧
      (∀ m k, m % 11 = 6 →
        11 ∣ QseriesFormalization.Ch01.partitionCount (11 * k + m)) := by
  exact ⟨ramanujan_5_dvd_partitionCount_five_mul_add_of_mod_eq_four,
    ramanujan_7_dvd_partitionCount_seven_mul_add_of_mod_eq_five,
    ramanujan_11_dvd_partitionCount_eleven_mul_add_of_mod_eq_six⟩

/-- `ZMod` stability under adding a multiple of the relevant modulus on the
left. -/
theorem ramanujan_classical_partition_congruences_modulus_multiple_add_zmod :
    (∀ m k, m % 5 = 4 →
      ((QseriesFormalization.Ch01.partitionCount (5 * k + m) : ℕ) : ZMod 5) = 0) ∧
      (∀ m k, m % 7 = 5 →
        ((QseriesFormalization.Ch01.partitionCount (7 * k + m) : ℕ) : ZMod 7) = 0) ∧
      (∀ m k, m % 11 = 6 →
        ((QseriesFormalization.Ch01.partitionCount (11 * k + m) : ℕ) : ZMod 11) = 0) := by
  exact ⟨ramanujan_partition_five_mul_add_eq_zero_mod_5_of_mod_eq_four,
    ramanujan_partition_seven_mul_add_eq_zero_mod_7_of_mod_eq_five,
    ramanujan_partition_eleven_mul_add_eq_zero_mod_11_of_mod_eq_six⟩

/-- Stability of the mod-5 Ramanujan congruence under adding two multiples of
`5`. -/
theorem ramanujan_5_dvd_partitionCount_add_two_five_mul_of_mod_eq_four
    (m k l : ℕ) (hm : m % 5 = 4) :
    5 ∣ QseriesFormalization.Ch01.partitionCount (m + 5 * k + 5 * l) := by
  have hmod : (m + 5 * k + 5 * l) % 5 = 4 := by omega
  exact ramanujan_5_dvd_partitionCount_of_mod_eq_four (m + 5 * k + 5 * l) hmod

/-- `ZMod 5` form of stability under adding two multiples of `5`. -/
theorem ramanujan_partition_add_two_five_mul_eq_zero_mod_5_of_mod_eq_four
    (m k l : ℕ) (hm : m % 5 = 4) :
    ((QseriesFormalization.Ch01.partitionCount (m + 5 * k + 5 * l) : ℕ) : ZMod 5) = 0 :=
  (ZMod.natCast_eq_zero_iff _ 5).mpr
    (ramanujan_5_dvd_partitionCount_add_two_five_mul_of_mod_eq_four m k l hm)

/-- Stability of the mod-7 Ramanujan congruence under adding two multiples of
`7`. -/
theorem ramanujan_7_dvd_partitionCount_add_two_seven_mul_of_mod_eq_five
    (m k l : ℕ) (hm : m % 7 = 5) :
    7 ∣ QseriesFormalization.Ch01.partitionCount (m + 7 * k + 7 * l) := by
  have hmod : (m + 7 * k + 7 * l) % 7 = 5 := by omega
  exact ramanujan_7_dvd_partitionCount_of_mod_eq_five (m + 7 * k + 7 * l) hmod

/-- `ZMod 7` form of stability under adding two multiples of `7`. -/
theorem ramanujan_partition_add_two_seven_mul_eq_zero_mod_7_of_mod_eq_five
    (m k l : ℕ) (hm : m % 7 = 5) :
    ((QseriesFormalization.Ch01.partitionCount (m + 7 * k + 7 * l) : ℕ) : ZMod 7) = 0 :=
  (ZMod.natCast_eq_zero_iff _ 7).mpr
    (ramanujan_7_dvd_partitionCount_add_two_seven_mul_of_mod_eq_five m k l hm)

/-- Stability of the mod-11 Ramanujan congruence under adding two multiples of
`11`. -/
theorem ramanujan_11_dvd_partitionCount_add_two_eleven_mul_of_mod_eq_six
    (m k l : ℕ) (hm : m % 11 = 6) :
    11 ∣ QseriesFormalization.Ch01.partitionCount (m + 11 * k + 11 * l) := by
  have hmod : (m + 11 * k + 11 * l) % 11 = 6 := by omega
  exact ramanujan_11_dvd_partitionCount_of_mod_eq_six (m + 11 * k + 11 * l) hmod

/-- `ZMod 11` form of stability under adding two multiples of `11`. -/
theorem ramanujan_partition_add_two_eleven_mul_eq_zero_mod_11_of_mod_eq_six
    (m k l : ℕ) (hm : m % 11 = 6) :
    ((QseriesFormalization.Ch01.partitionCount (m + 11 * k + 11 * l) : ℕ) : ZMod 11) = 0 :=
  (ZMod.natCast_eq_zero_iff _ 11).mpr
    (ramanujan_11_dvd_partitionCount_add_two_eleven_mul_of_mod_eq_six m k l hm)

/-- Stability under adding two multiples of the relevant modulus, assembled for
the three classical Ramanujan congruences. -/
theorem ramanujan_classical_partition_congruences_add_two_modulus_multiples :
    (∀ m k l, m % 5 = 4 →
      5 ∣ QseriesFormalization.Ch01.partitionCount (m + 5 * k + 5 * l)) ∧
      (∀ m k l, m % 7 = 5 →
        7 ∣ QseriesFormalization.Ch01.partitionCount (m + 7 * k + 7 * l)) ∧
      (∀ m k l, m % 11 = 6 →
        11 ∣ QseriesFormalization.Ch01.partitionCount (m + 11 * k + 11 * l)) := by
  exact ⟨ramanujan_5_dvd_partitionCount_add_two_five_mul_of_mod_eq_four,
    ramanujan_7_dvd_partitionCount_add_two_seven_mul_of_mod_eq_five,
    ramanujan_11_dvd_partitionCount_add_two_eleven_mul_of_mod_eq_six⟩

/-- `ZMod` stability under adding two multiples of the relevant modulus. -/
theorem ramanujan_classical_partition_congruences_add_two_modulus_multiples_zmod :
    (∀ m k l, m % 5 = 4 →
      ((QseriesFormalization.Ch01.partitionCount (m + 5 * k + 5 * l) : ℕ) : ZMod 5) = 0) ∧
      (∀ m k l, m % 7 = 5 →
        ((QseriesFormalization.Ch01.partitionCount (m + 7 * k + 7 * l) : ℕ) : ZMod 7) = 0) ∧
      (∀ m k l, m % 11 = 6 →
        ((QseriesFormalization.Ch01.partitionCount (m + 11 * k + 11 * l) : ℕ) :
          ZMod 11) = 0) := by
  exact ⟨ramanujan_partition_add_two_five_mul_eq_zero_mod_5_of_mod_eq_four,
    ramanujan_partition_add_two_seven_mul_eq_zero_mod_7_of_mod_eq_five,
    ramanujan_partition_add_two_eleven_mul_eq_zero_mod_11_of_mod_eq_six⟩

/-- Stability of the mod-5 Ramanujan congruence under adding three multiples of
`5`. -/
theorem ramanujan_5_dvd_partitionCount_add_three_five_mul_of_mod_eq_four
    (m k l r : ℕ) (hm : m % 5 = 4) :
    5 ∣ QseriesFormalization.Ch01.partitionCount (m + 5 * k + 5 * l + 5 * r) := by
  have hmod : (m + 5 * k + 5 * l + 5 * r) % 5 = 4 := by omega
  exact ramanujan_5_dvd_partitionCount_of_mod_eq_four
    (m + 5 * k + 5 * l + 5 * r) hmod

/-- `ZMod 5` form of stability under adding three multiples of `5`. -/
theorem ramanujan_partition_add_three_five_mul_eq_zero_mod_5_of_mod_eq_four
    (m k l r : ℕ) (hm : m % 5 = 4) :
    ((QseriesFormalization.Ch01.partitionCount (m + 5 * k + 5 * l + 5 * r) : ℕ) :
      ZMod 5) = 0 :=
  (ZMod.natCast_eq_zero_iff _ 5).mpr
    (ramanujan_5_dvd_partitionCount_add_three_five_mul_of_mod_eq_four m k l r hm)

/-- Stability of the mod-7 Ramanujan congruence under adding three multiples of
`7`. -/
theorem ramanujan_7_dvd_partitionCount_add_three_seven_mul_of_mod_eq_five
    (m k l r : ℕ) (hm : m % 7 = 5) :
    7 ∣ QseriesFormalization.Ch01.partitionCount (m + 7 * k + 7 * l + 7 * r) := by
  have hmod : (m + 7 * k + 7 * l + 7 * r) % 7 = 5 := by omega
  exact ramanujan_7_dvd_partitionCount_of_mod_eq_five
    (m + 7 * k + 7 * l + 7 * r) hmod

/-- `ZMod 7` form of stability under adding three multiples of `7`. -/
theorem ramanujan_partition_add_three_seven_mul_eq_zero_mod_7_of_mod_eq_five
    (m k l r : ℕ) (hm : m % 7 = 5) :
    ((QseriesFormalization.Ch01.partitionCount (m + 7 * k + 7 * l + 7 * r) : ℕ) :
      ZMod 7) = 0 :=
  (ZMod.natCast_eq_zero_iff _ 7).mpr
    (ramanujan_7_dvd_partitionCount_add_three_seven_mul_of_mod_eq_five m k l r hm)

/-- Stability of the mod-11 Ramanujan congruence under adding three multiples
of `11`. -/
theorem ramanujan_11_dvd_partitionCount_add_three_eleven_mul_of_mod_eq_six
    (m k l r : ℕ) (hm : m % 11 = 6) :
    11 ∣ QseriesFormalization.Ch01.partitionCount (m + 11 * k + 11 * l + 11 * r) := by
  have hmod : (m + 11 * k + 11 * l + 11 * r) % 11 = 6 := by omega
  exact ramanujan_11_dvd_partitionCount_of_mod_eq_six
    (m + 11 * k + 11 * l + 11 * r) hmod

/-- `ZMod 11` form of stability under adding three multiples of `11`. -/
theorem ramanujan_partition_add_three_eleven_mul_eq_zero_mod_11_of_mod_eq_six
    (m k l r : ℕ) (hm : m % 11 = 6) :
    ((QseriesFormalization.Ch01.partitionCount (m + 11 * k + 11 * l + 11 * r) : ℕ) :
      ZMod 11) = 0 :=
  (ZMod.natCast_eq_zero_iff _ 11).mpr
    (ramanujan_11_dvd_partitionCount_add_three_eleven_mul_of_mod_eq_six m k l r hm)

/-- Stability under adding three multiples of the relevant modulus, assembled
for the three classical Ramanujan congruences. -/
theorem ramanujan_classical_partition_congruences_add_three_modulus_multiples :
    (∀ m k l r, m % 5 = 4 →
      5 ∣ QseriesFormalization.Ch01.partitionCount (m + 5 * k + 5 * l + 5 * r)) ∧
      (∀ m k l r, m % 7 = 5 →
        7 ∣ QseriesFormalization.Ch01.partitionCount (m + 7 * k + 7 * l + 7 * r)) ∧
      (∀ m k l r, m % 11 = 6 →
        11 ∣ QseriesFormalization.Ch01.partitionCount
          (m + 11 * k + 11 * l + 11 * r)) := by
  exact ⟨ramanujan_5_dvd_partitionCount_add_three_five_mul_of_mod_eq_four,
    ramanujan_7_dvd_partitionCount_add_three_seven_mul_of_mod_eq_five,
    ramanujan_11_dvd_partitionCount_add_three_eleven_mul_of_mod_eq_six⟩

/-- `ZMod` stability under adding three multiples of the relevant modulus. -/
theorem ramanujan_classical_partition_congruences_add_three_modulus_multiples_zmod :
    (∀ m k l r, m % 5 = 4 →
      ((QseriesFormalization.Ch01.partitionCount (m + 5 * k + 5 * l + 5 * r) : ℕ) :
        ZMod 5) = 0) ∧
      (∀ m k l r, m % 7 = 5 →
        ((QseriesFormalization.Ch01.partitionCount (m + 7 * k + 7 * l + 7 * r) : ℕ) :
          ZMod 7) = 0) ∧
      (∀ m k l r, m % 11 = 6 →
        ((QseriesFormalization.Ch01.partitionCount (m + 11 * k + 11 * l + 11 * r) :
          ℕ) : ZMod 11) = 0) := by
  exact ⟨ramanujan_partition_add_three_five_mul_eq_zero_mod_5_of_mod_eq_four,
    ramanujan_partition_add_three_seven_mul_eq_zero_mod_7_of_mod_eq_five,
    ramanujan_partition_add_three_eleven_mul_eq_zero_mod_11_of_mod_eq_six⟩

/-- Stability of the mod-5 Ramanujan congruence under adding four multiples of
`5`. -/
theorem ramanujan_5_dvd_partitionCount_add_four_five_mul_of_mod_eq_four
    (m k l r s : ℕ) (hm : m % 5 = 4) :
    5 ∣ QseriesFormalization.Ch01.partitionCount
      (m + 5 * k + 5 * l + 5 * r + 5 * s) := by
  have hmod : (m + 5 * k + 5 * l + 5 * r + 5 * s) % 5 = 4 := by omega
  exact ramanujan_5_dvd_partitionCount_of_mod_eq_four
    (m + 5 * k + 5 * l + 5 * r + 5 * s) hmod

/-- `ZMod 5` form of stability under adding four multiples of `5`. -/
theorem ramanujan_partition_add_four_five_mul_eq_zero_mod_5_of_mod_eq_four
    (m k l r s : ℕ) (hm : m % 5 = 4) :
    ((QseriesFormalization.Ch01.partitionCount
      (m + 5 * k + 5 * l + 5 * r + 5 * s) : ℕ) : ZMod 5) = 0 :=
  (ZMod.natCast_eq_zero_iff _ 5).mpr
    (ramanujan_5_dvd_partitionCount_add_four_five_mul_of_mod_eq_four m k l r s hm)

/-- Stability of the mod-7 Ramanujan congruence under adding four multiples of
`7`. -/
theorem ramanujan_7_dvd_partitionCount_add_four_seven_mul_of_mod_eq_five
    (m k l r s : ℕ) (hm : m % 7 = 5) :
    7 ∣ QseriesFormalization.Ch01.partitionCount
      (m + 7 * k + 7 * l + 7 * r + 7 * s) := by
  have hmod : (m + 7 * k + 7 * l + 7 * r + 7 * s) % 7 = 5 := by omega
  exact ramanujan_7_dvd_partitionCount_of_mod_eq_five
    (m + 7 * k + 7 * l + 7 * r + 7 * s) hmod

/-- `ZMod 7` form of stability under adding four multiples of `7`. -/
theorem ramanujan_partition_add_four_seven_mul_eq_zero_mod_7_of_mod_eq_five
    (m k l r s : ℕ) (hm : m % 7 = 5) :
    ((QseriesFormalization.Ch01.partitionCount
      (m + 7 * k + 7 * l + 7 * r + 7 * s) : ℕ) : ZMod 7) = 0 :=
  (ZMod.natCast_eq_zero_iff _ 7).mpr
    (ramanujan_7_dvd_partitionCount_add_four_seven_mul_of_mod_eq_five m k l r s hm)

/-- Stability of the mod-11 Ramanujan congruence under adding four multiples
of `11`. -/
theorem ramanujan_11_dvd_partitionCount_add_four_eleven_mul_of_mod_eq_six
    (m k l r s : ℕ) (hm : m % 11 = 6) :
    11 ∣ QseriesFormalization.Ch01.partitionCount
      (m + 11 * k + 11 * l + 11 * r + 11 * s) := by
  have hmod : (m + 11 * k + 11 * l + 11 * r + 11 * s) % 11 = 6 := by omega
  exact ramanujan_11_dvd_partitionCount_of_mod_eq_six
    (m + 11 * k + 11 * l + 11 * r + 11 * s) hmod

/-- `ZMod 11` form of stability under adding four multiples of `11`. -/
theorem ramanujan_partition_add_four_eleven_mul_eq_zero_mod_11_of_mod_eq_six
    (m k l r s : ℕ) (hm : m % 11 = 6) :
    ((QseriesFormalization.Ch01.partitionCount
      (m + 11 * k + 11 * l + 11 * r + 11 * s) : ℕ) : ZMod 11) = 0 :=
  (ZMod.natCast_eq_zero_iff _ 11).mpr
    (ramanujan_11_dvd_partitionCount_add_four_eleven_mul_of_mod_eq_six m k l r s hm)

/-- Stability under adding four multiples of the relevant modulus, assembled
for the three classical Ramanujan congruences. -/
theorem ramanujan_classical_partition_congruences_add_four_modulus_multiples :
    (∀ m k l r s, m % 5 = 4 →
      5 ∣ QseriesFormalization.Ch01.partitionCount
        (m + 5 * k + 5 * l + 5 * r + 5 * s)) ∧
      (∀ m k l r s, m % 7 = 5 →
        7 ∣ QseriesFormalization.Ch01.partitionCount
          (m + 7 * k + 7 * l + 7 * r + 7 * s)) ∧
      (∀ m k l r s, m % 11 = 6 →
        11 ∣ QseriesFormalization.Ch01.partitionCount
          (m + 11 * k + 11 * l + 11 * r + 11 * s)) := by
  exact ⟨ramanujan_5_dvd_partitionCount_add_four_five_mul_of_mod_eq_four,
    ramanujan_7_dvd_partitionCount_add_four_seven_mul_of_mod_eq_five,
    ramanujan_11_dvd_partitionCount_add_four_eleven_mul_of_mod_eq_six⟩

/-- `ZMod` stability under adding four multiples of the relevant modulus. -/
theorem ramanujan_classical_partition_congruences_add_four_modulus_multiples_zmod :
    (∀ m k l r s, m % 5 = 4 →
      ((QseriesFormalization.Ch01.partitionCount
        (m + 5 * k + 5 * l + 5 * r + 5 * s) : ℕ) : ZMod 5) = 0) ∧
      (∀ m k l r s, m % 7 = 5 →
        ((QseriesFormalization.Ch01.partitionCount
          (m + 7 * k + 7 * l + 7 * r + 7 * s) : ℕ) : ZMod 7) = 0) ∧
      (∀ m k l r s, m % 11 = 6 →
        ((QseriesFormalization.Ch01.partitionCount
          (m + 11 * k + 11 * l + 11 * r + 11 * s) : ℕ) : ZMod 11) = 0) := by
  exact ⟨ramanujan_partition_add_four_five_mul_eq_zero_mod_5_of_mod_eq_four,
    ramanujan_partition_add_four_seven_mul_eq_zero_mod_7_of_mod_eq_five,
    ramanujan_partition_add_four_eleven_mul_eq_zero_mod_11_of_mod_eq_six⟩

/-- Classical Ramanujan congruences in residue-class form. -/
theorem ramanujan_classical_partition_congruences_residue :
    (∀ m, m % 5 = 4 → 5 ∣ QseriesFormalization.Ch01.partitionCount m) ∧
      (∀ m, m % 7 = 5 → 7 ∣ QseriesFormalization.Ch01.partitionCount m) ∧
      (∀ m, m % 11 = 6 → 11 ∣ QseriesFormalization.Ch01.partitionCount m) := by
  exact ⟨ramanujan_5_dvd_partitionCount_of_mod_eq_four,
    ramanujan_7_dvd_partitionCount_of_mod_eq_five,
    ramanujan_11_dvd_partitionCount_of_mod_eq_six⟩

/-- `ZMod` residue-class form of the three classical Ramanujan congruences. -/
theorem ramanujan_classical_partition_congruences_residue_zmod :
    (∀ m, m % 5 = 4 →
      ((QseriesFormalization.Ch01.partitionCount m : ℕ) : ZMod 5) = 0) ∧
      (∀ m, m % 7 = 5 →
        ((QseriesFormalization.Ch01.partitionCount m : ℕ) : ZMod 7) = 0) ∧
      (∀ m, m % 11 = 6 →
        ((QseriesFormalization.Ch01.partitionCount m : ℕ) : ZMod 11) = 0) := by
  exact ⟨ramanujan_partition_mod_5_eq_zero_of_mod_eq_four,
    ramanujan_partition_mod_7_eq_zero_of_mod_eq_five,
    ramanujan_partition_mod_11_eq_zero_of_mod_eq_six⟩

/-- ModEq form of the mod-5 Ramanujan congruence. -/
theorem ramanujan_5_dvd_partitionCount_of_modEq_four
    (m : ℕ) (hm : m ≡ 4 [MOD 5]) :
    5 ∣ QseriesFormalization.Ch01.partitionCount m := by
  have hmod : m % 5 = 4 := by
    have h : m % 5 = 4 % 5 := by simpa [Nat.ModEq] using hm
    simpa using h
  exact ramanujan_5_dvd_partitionCount_of_mod_eq_four m hmod

/-- `ZMod 5` form using `Nat.ModEq`. -/
theorem ramanujan_partition_mod_5_eq_zero_of_modEq_four
    (m : ℕ) (hm : m ≡ 4 [MOD 5]) :
    ((QseriesFormalization.Ch01.partitionCount m : ℕ) : ZMod 5) = 0 :=
  (ZMod.natCast_eq_zero_iff _ 5).mpr
    (ramanujan_5_dvd_partitionCount_of_modEq_four m hm)

/-- ModEq form of the mod-7 Ramanujan congruence. -/
theorem ramanujan_7_dvd_partitionCount_of_modEq_five
    (m : ℕ) (hm : m ≡ 5 [MOD 7]) :
    7 ∣ QseriesFormalization.Ch01.partitionCount m := by
  have hmod : m % 7 = 5 := by
    have h : m % 7 = 5 % 7 := by simpa [Nat.ModEq] using hm
    simpa using h
  exact ramanujan_7_dvd_partitionCount_of_mod_eq_five m hmod

/-- `ZMod 7` form using `Nat.ModEq`. -/
theorem ramanujan_partition_mod_7_eq_zero_of_modEq_five
    (m : ℕ) (hm : m ≡ 5 [MOD 7]) :
    ((QseriesFormalization.Ch01.partitionCount m : ℕ) : ZMod 7) = 0 :=
  (ZMod.natCast_eq_zero_iff _ 7).mpr
    (ramanujan_7_dvd_partitionCount_of_modEq_five m hm)

/-- ModEq form of the mod-11 Ramanujan congruence. -/
theorem ramanujan_11_dvd_partitionCount_of_modEq_six
    (m : ℕ) (hm : m ≡ 6 [MOD 11]) :
    11 ∣ QseriesFormalization.Ch01.partitionCount m := by
  have hmod : m % 11 = 6 := by
    have h : m % 11 = 6 % 11 := by simpa [Nat.ModEq] using hm
    simpa using h
  exact ramanujan_11_dvd_partitionCount_of_mod_eq_six m hmod

/-- `ZMod 11` form using `Nat.ModEq`. -/
theorem ramanujan_partition_mod_11_eq_zero_of_modEq_six
    (m : ℕ) (hm : m ≡ 6 [MOD 11]) :
    ((QseriesFormalization.Ch01.partitionCount m : ℕ) : ZMod 11) = 0 :=
  (ZMod.natCast_eq_zero_iff _ 11).mpr
    (ramanujan_11_dvd_partitionCount_of_modEq_six m hm)

/-- Classical Ramanujan congruences assembled in `Nat.ModEq` form. -/
theorem ramanujan_classical_partition_congruences_modEq :
    (∀ m, m ≡ 4 [MOD 5] → 5 ∣ QseriesFormalization.Ch01.partitionCount m) ∧
      (∀ m, m ≡ 5 [MOD 7] → 7 ∣ QseriesFormalization.Ch01.partitionCount m) ∧
      (∀ m, m ≡ 6 [MOD 11] → 11 ∣ QseriesFormalization.Ch01.partitionCount m) := by
  exact ⟨ramanujan_5_dvd_partitionCount_of_modEq_four,
    ramanujan_7_dvd_partitionCount_of_modEq_five,
    ramanujan_11_dvd_partitionCount_of_modEq_six⟩

/-- `ZMod` form of the three classical Ramanujan congruences using
`Nat.ModEq`. -/
theorem ramanujan_classical_partition_congruences_modEq_zmod :
    (∀ m, m ≡ 4 [MOD 5] →
      ((QseriesFormalization.Ch01.partitionCount m : ℕ) : ZMod 5) = 0) ∧
      (∀ m, m ≡ 5 [MOD 7] →
        ((QseriesFormalization.Ch01.partitionCount m : ℕ) : ZMod 7) = 0) ∧
      (∀ m, m ≡ 6 [MOD 11] →
        ((QseriesFormalization.Ch01.partitionCount m : ℕ) : ZMod 11) = 0) := by
  exact ⟨ramanujan_partition_mod_5_eq_zero_of_modEq_four,
    ramanujan_partition_mod_7_eq_zero_of_modEq_five,
    ramanujan_partition_mod_11_eq_zero_of_modEq_six⟩

/-- ModEq-periodic form of the mod-5 Ramanujan congruence. -/
theorem ramanujan_5_dvd_partitionCount_add_of_modEq_four_of_modEq_zero
    (m k : ℕ) (hm : m ≡ 4 [MOD 5]) (hk : k ≡ 0 [MOD 5]) :
    5 ∣ QseriesFormalization.Ch01.partitionCount (m + k) := by
  have hm' : m % 5 = 4 := by
    have h : m % 5 = 4 % 5 := by simpa [Nat.ModEq] using hm
    simpa using h
  have hk' : k % 5 = 0 := by
    have h : k % 5 = 0 % 5 := by simpa [Nat.ModEq] using hk
    simpa using h
  have hmk : (m + k) % 5 = 4 := by
    rw [Nat.add_mod, hm', hk']
  exact ramanujan_5_dvd_partitionCount_of_mod_eq_four (m + k) hmk

/-- ModEq-periodic form of the mod-7 Ramanujan congruence. -/
theorem ramanujan_7_dvd_partitionCount_add_of_modEq_five_of_modEq_zero
    (m k : ℕ) (hm : m ≡ 5 [MOD 7]) (hk : k ≡ 0 [MOD 7]) :
    7 ∣ QseriesFormalization.Ch01.partitionCount (m + k) := by
  have hm' : m % 7 = 5 := by
    have h : m % 7 = 5 % 7 := by simpa [Nat.ModEq] using hm
    simpa using h
  have hk' : k % 7 = 0 := by
    have h : k % 7 = 0 % 7 := by simpa [Nat.ModEq] using hk
    simpa using h
  have hmk : (m + k) % 7 = 5 := by
    rw [Nat.add_mod, hm', hk']
  exact ramanujan_7_dvd_partitionCount_of_mod_eq_five (m + k) hmk

/-- ModEq-periodic form of the mod-11 Ramanujan congruence. -/
theorem ramanujan_11_dvd_partitionCount_add_of_modEq_six_of_modEq_zero
    (m k : ℕ) (hm : m ≡ 6 [MOD 11]) (hk : k ≡ 0 [MOD 11]) :
    11 ∣ QseriesFormalization.Ch01.partitionCount (m + k) := by
  have hm' : m % 11 = 6 := by
    have h : m % 11 = 6 % 11 := by simpa [Nat.ModEq] using hm
    simpa using h
  have hk' : k % 11 = 0 := by
    have h : k % 11 = 0 % 11 := by simpa [Nat.ModEq] using hk
    simpa using h
  have hmk : (m + k) % 11 = 6 := by
    rw [Nat.add_mod, hm', hk']
  exact ramanujan_11_dvd_partitionCount_of_mod_eq_six (m + k) hmk

/-- `ZMod 5` periodic form using `Nat.ModEq`. -/
theorem ramanujan_partition_add_eq_zero_mod_5_of_modEq_four_of_modEq_zero
    (m k : ℕ) (hm : m ≡ 4 [MOD 5]) (hk : k ≡ 0 [MOD 5]) :
    ((QseriesFormalization.Ch01.partitionCount (m + k) : ℕ) : ZMod 5) = 0 :=
  (ZMod.natCast_eq_zero_iff _ 5).mpr
    (ramanujan_5_dvd_partitionCount_add_of_modEq_four_of_modEq_zero m k hm hk)

/-- `ZMod 7` periodic form using `Nat.ModEq`. -/
theorem ramanujan_partition_add_eq_zero_mod_7_of_modEq_five_of_modEq_zero
    (m k : ℕ) (hm : m ≡ 5 [MOD 7]) (hk : k ≡ 0 [MOD 7]) :
    ((QseriesFormalization.Ch01.partitionCount (m + k) : ℕ) : ZMod 7) = 0 :=
  (ZMod.natCast_eq_zero_iff _ 7).mpr
    (ramanujan_7_dvd_partitionCount_add_of_modEq_five_of_modEq_zero m k hm hk)

/-- `ZMod 11` periodic form using `Nat.ModEq`. -/
theorem ramanujan_partition_add_eq_zero_mod_11_of_modEq_six_of_modEq_zero
    (m k : ℕ) (hm : m ≡ 6 [MOD 11]) (hk : k ≡ 0 [MOD 11]) :
    ((QseriesFormalization.Ch01.partitionCount (m + k) : ℕ) : ZMod 11) = 0 :=
  (ZMod.natCast_eq_zero_iff _ 11).mpr
    (ramanujan_11_dvd_partitionCount_add_of_modEq_six_of_modEq_zero m k hm hk)

/-- Periodic `Nat.ModEq` form of the three classical Ramanujan congruences. -/
theorem ramanujan_classical_partition_congruences_add_modEq_zero :
    (∀ m k, m ≡ 4 [MOD 5] → k ≡ 0 [MOD 5] →
      5 ∣ QseriesFormalization.Ch01.partitionCount (m + k)) ∧
      (∀ m k, m ≡ 5 [MOD 7] → k ≡ 0 [MOD 7] →
        7 ∣ QseriesFormalization.Ch01.partitionCount (m + k)) ∧
      (∀ m k, m ≡ 6 [MOD 11] → k ≡ 0 [MOD 11] →
        11 ∣ QseriesFormalization.Ch01.partitionCount (m + k)) := by
  exact ⟨ramanujan_5_dvd_partitionCount_add_of_modEq_four_of_modEq_zero,
    ramanujan_7_dvd_partitionCount_add_of_modEq_five_of_modEq_zero,
    ramanujan_11_dvd_partitionCount_add_of_modEq_six_of_modEq_zero⟩

/-- `ZMod` periodic `Nat.ModEq` form of the three classical congruences. -/
theorem ramanujan_classical_partition_congruences_add_modEq_zero_zmod :
    (∀ m k, m ≡ 4 [MOD 5] → k ≡ 0 [MOD 5] →
      ((QseriesFormalization.Ch01.partitionCount (m + k) : ℕ) : ZMod 5) = 0) ∧
      (∀ m k, m ≡ 5 [MOD 7] → k ≡ 0 [MOD 7] →
        ((QseriesFormalization.Ch01.partitionCount (m + k) : ℕ) : ZMod 7) = 0) ∧
      (∀ m k, m ≡ 6 [MOD 11] → k ≡ 0 [MOD 11] →
        ((QseriesFormalization.Ch01.partitionCount (m + k) : ℕ) : ZMod 11) = 0) := by
  exact ⟨ramanujan_partition_add_eq_zero_mod_5_of_modEq_four_of_modEq_zero,
    ramanujan_partition_add_eq_zero_mod_7_of_modEq_five_of_modEq_zero,
    ramanujan_partition_add_eq_zero_mod_11_of_modEq_six_of_modEq_zero⟩

/-- **Classical Ramanujan partition congruences**, assembled in one statement:
`5 ∣ p(5n+4)`, `7 ∣ p(7n+5)`, and `11 ∣ p(11n+6)`. -/
theorem ramanujan_classical_partition_congruences :
    (∀ n, 5 ∣ QseriesFormalization.Ch01.partitionCount (5 * n + 4)) ∧
      (∀ n, 7 ∣ QseriesFormalization.Ch01.partitionCount (7 * n + 5)) ∧
      (∀ n, 11 ∣ QseriesFormalization.Ch01.partitionCount (11 * n + 6)) := by
  exact ⟨QseriesFormalization.PartIV.Ch17.ramanujan_5_dvd_p_5n_plus_4,
    QseriesFormalization.Pending.Ch17p7.ramanujan_7_dvd_p_7n_plus_5,
    ramanujan_11_dvd_p_11n_plus_6⟩

/-- `ZMod` form of the three classical Ramanujan partition congruences. -/
theorem ramanujan_classical_partition_congruences_zmod :
    (∀ n, ((QseriesFormalization.Ch01.partitionCount (5 * n + 4) : ℕ) : ZMod 5) = 0) ∧
      (∀ n, ((QseriesFormalization.Ch01.partitionCount (7 * n + 5) : ℕ) : ZMod 7) = 0) ∧
      (∀ n, ((QseriesFormalization.Ch01.partitionCount (11 * n + 6) : ℕ) : ZMod 11) = 0) := by
  exact ⟨QseriesFormalization.PartIV.Ch17.ramanujan_partition_5n_plus_4_eq_zero_mod_5,
    QseriesFormalization.Pending.Ch17p7.ramanujan_partition_7n_plus_5_eq_zero_mod_7,
    ramanujan_partition_11n_plus_6_eq_zero_mod_11⟩

end Hirschhorn11
end Pending
end QseriesFormalization
