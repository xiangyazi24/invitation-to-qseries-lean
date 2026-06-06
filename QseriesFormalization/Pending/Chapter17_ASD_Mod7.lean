import QseriesFormalization.Chapter17_Mod7PerTermAnalysis
import QseriesFormalization.Pending.JacobiCubeAnalyticToFormal

/-!
# Chapter 17 — Atkin-Swinnerton-Dyer dissection mod 7

This file records the mod-7 residue decomposition of the Jacobi cube
`(qPochInfPS (ZMod 7))^3` used in Hirschhorn §3.7.
-/

namespace QseriesFormalization
namespace Pending
namespace Hirschhorn7

open PowerSeries
open QseriesFormalization.PartIV.Ch19

/-- The 7-residue section of a formal power series over `R`: keep only
coefficients at indices congruent to `r` modulo 7. -/
noncomputable def section7 (R : Type*) [CommRing R] (r : ℕ) (φ : R⟦X⟧) : R⟦X⟧ :=
  PowerSeries.mk (fun n => if n % 7 = r then φ.coeff n else 0)

/-- Coefficient of a 7-section. -/
@[simp] theorem coeff_section7 (R : Type*) [CommRing R] (r : ℕ) (φ : R⟦X⟧) (n : ℕ) :
    (section7 R r φ).coeff n = if n % 7 = r then φ.coeff n else 0 := by
  rw [section7, PowerSeries.coeff_mk]

/-- A formal power series is supported on one residue class modulo 7. -/
def IsRes7 {R : Type*} [CommRing R] (r : ℕ) (φ : R⟦X⟧) : Prop :=
  ∀ n, n % 7 ≠ r → φ.coeff n = 0

/-- A 7-section is supported on its chosen residue class. -/
theorem isRes7_section7 {R : Type*} [CommRing R] (r : ℕ) (φ : R⟦X⟧) :
    IsRes7 r (section7 R r φ) := by
  intro n hn
  rw [coeff_section7, if_neg hn]

/-- The `r`-th residue component of `(qPochInfPS (ZMod 7))^3`. -/
noncomputable def ASD7 (r : ℕ) : (ZMod 7)⟦X⟧ :=
  section7 (ZMod 7) r ((qPochInfPS (ZMod 7))^3)

theorem isRes7_ASD7 (r : ℕ) : IsRes7 r (ASD7 r) := by
  exact isRes7_section7 r ((qPochInfPS (ZMod 7))^3)

/-- **Mod-7 ASD cube decomposition.**  In `ZMod 7`, the Jacobi cube has only
residue `0`, `1`, and `3` components.  The triangular residue `6` occurs only
when the Jacobi coefficient factor `2k+1` is `0` modulo 7, so it contributes no
section. -/
theorem qPochInfPS_cube_decompose_mod_7 :
    (qPochInfPS (ZMod 7))^3 = ASD7 0 + ASD7 1 + ASD7 3 := by
  ext n
  have hB2 :
      ((qPochInfPS (ZMod 7))^3).coeff n =
        ((QseriesFormalization.PartIV.Ch19.jacobiTripleSign n : ℤ) : ZMod 7) := by
    rw [QseriesFormalization.Pending.JacobiCubeAnalyticToFormal.qPochInfPS_pow_three_eq_jacobiThetaPS]
    rw [QseriesFormalization.PartIV.Ch19.coeff_jacobiThetaPS]
  have hRHS :
      (ASD7 0 + ASD7 1 + ASD7 3 : (ZMod 7)⟦X⟧).coeff n =
        (if n % 7 = 0 then ((qPochInfPS (ZMod 7))^3).coeff n else 0) +
        (if n % 7 = 1 then ((qPochInfPS (ZMod 7))^3).coeff n else 0) +
        (if n % 7 = 3 then ((qPochInfPS (ZMod 7))^3).coeff n else 0) := by
    simp only [ASD7, section7, map_add, coeff_mk]
  rw [hRHS]
  have h_nmod : (n : ZMod 7) = ((n % 7 : ℕ) : ZMod 7) := by
    conv_lhs => rw [← Nat.mod_add_div n 7]
    push_cast
    have : (7 : ZMod 7) = 0 := by decide
    rw [this]
    ring
  have h_zero_off :
      n % 7 ≠ 0 → n % 7 ≠ 1 → n % 7 ≠ 3 →
        ((qPochInfPS (ZMod 7))^3).coeff n = 0 := by
    intros h0 h1 h3
    rw [hB2]
    by_contra h_ne
    have h_res :=
      QseriesFormalization.PartIV.Ch17.jacobiTripleSign_nonzero_mod_7_residue n h_ne
    rw [h_nmod] at h_res
    have hlt : n % 7 < 7 := Nat.mod_lt n (by decide)
    interval_cases (n % 7) <;>
      rcases h_res with hr | hr | hr <;>
        first
        | exact h0 rfl
        | exact h1 rfl
        | exact h3 rfl
        | exact absurd hr (by decide)
  have hlt : n % 7 < 7 := Nat.mod_lt n (by decide)
  interval_cases (n % 7) <;> simp_all

#print axioms qPochInfPS_cube_decompose_mod_7

end Hirschhorn7
end Pending
end QseriesFormalization
