import QseriesFormalization.Basic
import QseriesFormalization.Chapter04
import QseriesFormalization.Chapter19
import QseriesFormalization.Pending.Chapter15_FormalDeriv
import QseriesFormalization.Pending.JacobiCubeAnalyticToFormal

/-!
# Chapter 20 — Modular discriminant Δ and the Ramanujan τ-function

⚠️  **AUX CHAPTER — full modularity of Δ(τ) OPEN**.

Per `PLAYBOOK_AUDIT.md` (2026-05-22): this file is the formal-PS landing
strip for the Ramanujan τ-function and the discriminant.  Genuine
results proved here:

  • Values: `ramanujanTau_zero .. ramanujanTau_fifty` matching OEIS A000594
  • Multiplicativity checks at coprime factor pairs up to 50
  • Prime-power Hecke recursion checks for p ∈ {2, 3, 5, 7} up to 50
  • Log-derivative recurrence for all `n ≥ 2`
  • Parity theorem: `τ(n)` is odd iff `n` is an odd square
  • Mod-691 congruence `τ(n) ≡ σ₁₁(n)` verified through `n ≤ 50`
  • Mod-p congruences: `ramanujanTau_p_mod_p` for `p ∈ {2,3,5,7}`
  • n = 0 unconditional Ramanujan trio:
    `ramanujan_partition_four_mod_five`, `_five_mod_seven`,
    `_six_mod_eleven`
  • Frobenius: `discriminantPS_pow_eq_expand`
  • Algebraic structure: `etaPS_isUnit`, `discriminantPS_not_isUnit`,
    `discriminantPS_eq_X_mul_etaPS_pow_24`,
    `discriminantPS_eq_X_mul_tprod_pow_24`

**Chan's Ch 20 main result — the modular invariance of Δ(τ) under
SL₂(ℤ) and the resulting full multiplicativity of `τ(n)` — is NOT
formalized here**, because the formal-PS approach does not see the
complex-analytic modularity directly; that requires Mathlib's
`ModularForm` infrastructure which is incomplete for the η-quotient
case.  Tracked as Tier 5 #18 in `TODO_THEOREMS.md`.
-/

namespace QseriesFormalization
namespace PartIV
namespace Ch20

def _root_.Nat.divisorSum (n : Nat) (f : Nat → Nat) : Nat :=
  ∑ d ∈ Finset.Icc 1 n, if d ∣ n then f d else 0

/-- The divisor power sum `σ₁₁(n) = ∑_{d ∣ n} d^11`, with `σ₁₁(0) = 0`. -/
def sigma11 (n : Nat) : Nat :=
  Nat.divisorSum n (fun d => d ^ 11)

section Field

variable {R : Type*} [Field R]

/-- The Dedekind eta function (formal placeholder, polynomial form
without the q^{1/24} prefactor). -/
noncomputable def etaPolyPart (q : R) (N : Nat) : R :=
  qPochhammer q N

/-- Sanity: η_poly q 0 = 1. -/
@[simp] theorem etaPolyPart_zero (q : R) : etaPolyPart q 0 = 1 := rfl

/-- Recursion for the eta-polynomial truncation:
`η_poly q (N+1) = η_poly q N · (1 − q^(N+1))`. -/
theorem etaPolyPart_succ (q : R) (N : Nat) :
    etaPolyPart q (N + 1) = etaPolyPart q N * (1 - q ^ (N + 1)) := by
  simp [etaPolyPart, qPochhammer_succ]

/-- Sanity: η_poly q 1 = 1 - q. -/
theorem etaPolyPart_one (q : R) :
    etaPolyPart q 1 = 1 - q := by
  simp [etaPolyPart, qPochhammer]

/-- Sanity: η_poly q 2 = (1 - q)(1 - q^2). -/
theorem etaPolyPart_two (q : R) :
    etaPolyPart q 2 = (1 - q) * (1 - q^2) := by
  simp [etaPolyPart, qPochhammer]

/-- The discriminant Δ(q) = q · η^24, polynomial part. -/
noncomputable def discriminantPolyPart (q : R) (N : Nat) : R :=
  q * etaPolyPart q N ^ 24

/-- Sanity: Δ_poly q 0 = q. -/
theorem discriminantPolyPart_zero (q : R) :
    discriminantPolyPart q 0 = q := by
  simp [discriminantPolyPart, etaPolyPart]

/-- Recursion for the discriminant polynomial truncation:
`Δ_poly q (N+1) = q · (η_poly q N · (1 − q^(N+1)))^24`. -/
theorem discriminantPolyPart_succ (q : R) (N : Nat) :
    discriminantPolyPart q (N + 1) =
      q * (etaPolyPart q N * (1 - q ^ (N + 1))) ^ 24 := by
  simp [discriminantPolyPart, etaPolyPart_succ]

/-- Sanity: Δ_poly q 1 = q * (1 - q)^24. -/
theorem discriminantPolyPart_one (q : R) :
    discriminantPolyPart q 1 = q * (1 - q) ^ 24 := by
  simp [discriminantPolyPart, etaPolyPart, qPochhammer]

/-- Sanity: Δ_poly q 2 = q((1 - q)(1 - q^2))^24. -/
theorem discriminantPolyPart_two (q : R) :
    discriminantPolyPart q 2 = q * ((1 - q) * (1 - q^2))^24 := by
  rw [discriminantPolyPart, etaPolyPart_two]

/-- Sanity: η_poly q 3 = (1 - q)(1 - q^2)(1 - q^3). -/
theorem etaPolyPart_three (q : R) :
    etaPolyPart q 3 = (1 - q) * (1 - q^2) * (1 - q^3) := by
  simp [etaPolyPart, qPochhammer]

/-- Sanity: Δ_poly q 3 = q((1 - q)(1 - q^2)(1 - q^3))^24. -/
theorem discriminantPolyPart_three (q : R) :
    discriminantPolyPart q 3 = q * ((1 - q) * (1 - q^2) * (1 - q^3))^24 := by
  rw [discriminantPolyPart, etaPolyPart_three]

theorem etaPolyPart_four (q : R) :
    etaPolyPart q 4 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_four (q : R) :
    discriminantPolyPart q 4 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4))^24 := by
  rw [discriminantPolyPart, etaPolyPart_four]

theorem etaPolyPart_five (q : R) :
    etaPolyPart q 5 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_five (q : R) :
    discriminantPolyPart q 5 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5))^24 := by
  rw [discriminantPolyPart, etaPolyPart_five]

theorem etaPolyPart_six (q : R) :
    etaPolyPart q 6 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) * (1 - q^6) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_six (q : R) :
    discriminantPolyPart q 6 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) * (1 - q^6))^24 := by
  rw [discriminantPolyPart, etaPolyPart_six]

theorem etaPolyPart_seven (q : R) :
    etaPolyPart q 7 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) * (1 - q^6) * (1 - q^7) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_seven (q : R) :
    discriminantPolyPart q 7 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) * (1 - q^6) * (1 - q^7))^24 := by
  rw [discriminantPolyPart, etaPolyPart_seven]

theorem etaPolyPart_eight (q : R) :
    etaPolyPart q 8 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) * (1 - q^6) * (1 - q^7) * (1 - q^8) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_eight (q : R) :
    discriminantPolyPart q 8 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) * (1 - q^6) * (1 - q^7) * (1 - q^8))^24 := by
  rw [discriminantPolyPart, etaPolyPart_eight]

theorem etaPolyPart_nine (q : R) :
    etaPolyPart q 9 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_nine (q : R) :
    discriminantPolyPart q 9 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9))^24 := by
  rw [discriminantPolyPart, etaPolyPart_nine]

theorem etaPolyPart_ten (q : R) :
    etaPolyPart q 10 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_ten (q : R) :
    discriminantPolyPart q 10 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10))^24 := by
  rw [discriminantPolyPart, etaPolyPart_ten]

theorem etaPolyPart_eleven (q : R) :
    etaPolyPart q 11 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) * (1 - q^11) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_eleven (q : R) :
    discriminantPolyPart q 11 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) * (1 - q^11))^24 := by
  rw [discriminantPolyPart, etaPolyPart_eleven]

theorem etaPolyPart_twelve (q : R) :
    etaPolyPart q 12 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) * (1 - q^11) * (1 - q^12) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_twelve (q : R) :
    discriminantPolyPart q 12 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) * (1 - q^11) * (1 - q^12))^24 := by
  rw [discriminantPolyPart, etaPolyPart_twelve]

theorem etaPolyPart_thirteen (q : R) :
    etaPolyPart q 13 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) * (1 - q^11) *
      (1 - q^12) * (1 - q^13) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_thirteen (q : R) :
    discriminantPolyPart q 13 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) * (1 - q^11) *
      (1 - q^12) * (1 - q^13))^24 := by
  rw [discriminantPolyPart, etaPolyPart_thirteen]

theorem etaPolyPart_fourteen (q : R) :
    etaPolyPart q 14 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) * (1 - q^11) *
      (1 - q^12) * (1 - q^13) * (1 - q^14) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_fourteen (q : R) :
    discriminantPolyPart q 14 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) * (1 - q^11) *
      (1 - q^12) * (1 - q^13) * (1 - q^14))^24 := by
  rw [discriminantPolyPart, etaPolyPart_fourteen]

theorem etaPolyPart_fifteen (q : R) :
    etaPolyPart q 15 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) * (1 - q^11) *
      (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_fifteen (q : R) :
    discriminantPolyPart q 15 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) * (1 - q^11) *
      (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15))^24 := by
  rw [discriminantPolyPart, etaPolyPart_fifteen]

theorem etaPolyPart_sixteen (q : R) :
    etaPolyPart q 16 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) * (1 - q^11) *
      (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) * (1 - q^16) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_sixteen (q : R) :
    discriminantPolyPart q 16 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) * (1 - q^11) *
      (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) * (1 - q^16))^24 := by
  rw [discriminantPolyPart, etaPolyPart_sixteen]

theorem etaPolyPart_seventeen (q : R) :
    etaPolyPart q 17 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) * (1 - q^11) *
      (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) * (1 - q^16) * (1 - q^17) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_seventeen (q : R) :
    discriminantPolyPart q 17 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) * (1 - q^11) *
      (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) * (1 - q^16) * (1 - q^17))^24 := by
  rw [discriminantPolyPart, etaPolyPart_seventeen]

theorem etaPolyPart_eighteen (q : R) :
    etaPolyPart q 18 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) * (1 - q^11) *
      (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) * (1 - q^16) * (1 - q^17) *
      (1 - q^18) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_eighteen (q : R) :
    discriminantPolyPart q 18 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) * (1 - q^11) *
      (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) * (1 - q^16) * (1 - q^17) *
      (1 - q^18))^24 := by
  rw [discriminantPolyPart, etaPolyPart_eighteen]

theorem etaPolyPart_nineteen (q : R) :
    etaPolyPart q 19 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) * (1 - q^11) *
      (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) * (1 - q^16) * (1 - q^17) *
      (1 - q^18) * (1 - q^19) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_nineteen (q : R) :
    discriminantPolyPart q 19 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) * (1 - q^11) *
      (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) * (1 - q^16) * (1 - q^17) *
      (1 - q^18) * (1 - q^19))^24 := by
  rw [discriminantPolyPart, etaPolyPart_nineteen]

theorem etaPolyPart_twenty (q : R) :
    etaPolyPart q 20 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) * (1 - q^11) *
      (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) * (1 - q^16) * (1 - q^17) *
      (1 - q^18) * (1 - q^19) * (1 - q^20) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_twenty (q : R) :
    discriminantPolyPart q 20 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) * (1 - q^11) *
      (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) * (1 - q^16) * (1 - q^17) *
      (1 - q^18) * (1 - q^19) * (1 - q^20))^24 := by
  rw [discriminantPolyPart, etaPolyPart_twenty]

theorem etaPolyPart_twentyone (q : R) :
    etaPolyPart q 21 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) * (1 - q^11) *
      (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) * (1 - q^16) * (1 - q^17) *
      (1 - q^18) * (1 - q^19) * (1 - q^20) * (1 - q^21) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_twentyone (q : R) :
    discriminantPolyPart q 21 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) * (1 - q^11) *
      (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) * (1 - q^16) * (1 - q^17) *
      (1 - q^18) * (1 - q^19) * (1 - q^20) * (1 - q^21))^24 := by
  rw [discriminantPolyPart, etaPolyPart_twentyone]

theorem etaPolyPart_twentytwo (q : R) :
    etaPolyPart q 22 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) * (1 - q^11) *
      (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) * (1 - q^16) * (1 - q^17) *
      (1 - q^18) * (1 - q^19) * (1 - q^20) * (1 - q^21) * (1 - q^22) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_twentytwo (q : R) :
    discriminantPolyPart q 22 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) * (1 - q^11) *
      (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) * (1 - q^16) * (1 - q^17) *
      (1 - q^18) * (1 - q^19) * (1 - q^20) * (1 - q^21) * (1 - q^22))^24 := by
  rw [discriminantPolyPart, etaPolyPart_twentytwo]

theorem etaPolyPart_twentythree (q : R) :
    etaPolyPart q 23 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) * (1 - q^11) *
      (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) * (1 - q^16) * (1 - q^17) *
      (1 - q^18) * (1 - q^19) * (1 - q^20) * (1 - q^21) * (1 - q^22) * (1 - q^23) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_twentythree (q : R) :
    discriminantPolyPart q 23 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) * (1 - q^11) *
      (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) * (1 - q^16) * (1 - q^17) *
      (1 - q^18) * (1 - q^19) * (1 - q^20) * (1 - q^21) * (1 - q^22) * (1 - q^23))^24 := by
  rw [discriminantPolyPart, etaPolyPart_twentythree]

theorem etaPolyPart_twentyfour (q : R) :
    etaPolyPart q 24 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) * (1 - q^11) *
      (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) * (1 - q^16) * (1 - q^17) *
      (1 - q^18) * (1 - q^19) * (1 - q^20) * (1 - q^21) * (1 - q^22) * (1 - q^23) *
      (1 - q^24) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_twentyfour (q : R) :
    discriminantPolyPart q 24 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) * (1 - q^11) *
      (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) * (1 - q^16) * (1 - q^17) *
      (1 - q^18) * (1 - q^19) * (1 - q^20) * (1 - q^21) * (1 - q^22) * (1 - q^23) *
      (1 - q^24))^24 := by
  rw [discriminantPolyPart, etaPolyPart_twentyfour]

theorem etaPolyPart_twentyfive (q : R) :
    etaPolyPart q 25 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) * (1 - q^11) *
      (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) * (1 - q^16) * (1 - q^17) *
      (1 - q^18) * (1 - q^19) * (1 - q^20) * (1 - q^21) * (1 - q^22) * (1 - q^23) *
      (1 - q^24) * (1 - q^25) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_twentyfive (q : R) :
    discriminantPolyPart q 25 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) * (1 - q^11) *
      (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) * (1 - q^16) * (1 - q^17) *
      (1 - q^18) * (1 - q^19) * (1 - q^20) * (1 - q^21) * (1 - q^22) * (1 - q^23) *
      (1 - q^24) * (1 - q^25))^24 := by
  rw [discriminantPolyPart, etaPolyPart_twentyfive]

theorem etaPolyPart_twentysix (q : R) :
    etaPolyPart q 26 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) * (1 - q^11) *
      (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) * (1 - q^16) * (1 - q^17) *
      (1 - q^18) * (1 - q^19) * (1 - q^20) * (1 - q^21) * (1 - q^22) * (1 - q^23) *
      (1 - q^24) * (1 - q^25) * (1 - q^26) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_twentysix (q : R) :
    discriminantPolyPart q 26 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) * (1 - q^11) *
      (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) * (1 - q^16) * (1 - q^17) *
      (1 - q^18) * (1 - q^19) * (1 - q^20) * (1 - q^21) * (1 - q^22) * (1 - q^23) *
      (1 - q^24) * (1 - q^25) * (1 - q^26))^24 := by
  rw [discriminantPolyPart, etaPolyPart_twentysix]

theorem etaPolyPart_twentyseven (q : R) :
    etaPolyPart q 27 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) * (1 - q^11) *
      (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) * (1 - q^16) * (1 - q^17) *
      (1 - q^18) * (1 - q^19) * (1 - q^20) * (1 - q^21) * (1 - q^22) * (1 - q^23) *
      (1 - q^24) * (1 - q^25) * (1 - q^26) * (1 - q^27) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_twentyseven (q : R) :
    discriminantPolyPart q 27 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) * (1 - q^11) *
      (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) * (1 - q^16) * (1 - q^17) *
      (1 - q^18) * (1 - q^19) * (1 - q^20) * (1 - q^21) * (1 - q^22) * (1 - q^23) *
      (1 - q^24) * (1 - q^25) * (1 - q^26) * (1 - q^27))^24 := by
  rw [discriminantPolyPart, etaPolyPart_twentyseven]

theorem etaPolyPart_twentyeight (q : R) :
    etaPolyPart q 28 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) * (1 - q^11) *
      (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) * (1 - q^16) * (1 - q^17) *
      (1 - q^18) * (1 - q^19) * (1 - q^20) * (1 - q^21) * (1 - q^22) * (1 - q^23) *
      (1 - q^24) * (1 - q^25) * (1 - q^26) * (1 - q^27) * (1 - q^28) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_twentyeight (q : R) :
    discriminantPolyPart q 28 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) * (1 - q^11) *
      (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) * (1 - q^16) * (1 - q^17) *
      (1 - q^18) * (1 - q^19) * (1 - q^20) * (1 - q^21) * (1 - q^22) * (1 - q^23) *
      (1 - q^24) * (1 - q^25) * (1 - q^26) * (1 - q^27) * (1 - q^28))^24 := by
  rw [discriminantPolyPart, etaPolyPart_twentyeight]

theorem etaPolyPart_twentynine (q : R) :
    etaPolyPart q 29 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) * (1 - q^11) *
      (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) * (1 - q^16) * (1 - q^17) *
      (1 - q^18) * (1 - q^19) * (1 - q^20) * (1 - q^21) * (1 - q^22) * (1 - q^23) *
      (1 - q^24) * (1 - q^25) * (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_twentynine (q : R) :
    discriminantPolyPart q 29 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) * (1 - q^11) *
      (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) * (1 - q^16) * (1 - q^17) *
      (1 - q^18) * (1 - q^19) * (1 - q^20) * (1 - q^21) * (1 - q^22) * (1 - q^23) *
      (1 - q^24) * (1 - q^25) * (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29))^24 := by
  rw [discriminantPolyPart, etaPolyPart_twentynine]

theorem etaPolyPart_thirty (q : R) :
    etaPolyPart q 30 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) * (1 - q^11) *
      (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) * (1 - q^16) * (1 - q^17) *
      (1 - q^18) * (1 - q^19) * (1 - q^20) * (1 - q^21) * (1 - q^22) * (1 - q^23) *
      (1 - q^24) * (1 - q^25) * (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) *
      (1 - q^30) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_thirty (q : R) :
    discriminantPolyPart q 30 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) * (1 - q^11) *
      (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) * (1 - q^16) * (1 - q^17) *
      (1 - q^18) * (1 - q^19) * (1 - q^20) * (1 - q^21) * (1 - q^22) * (1 - q^23) *
      (1 - q^24) * (1 - q^25) * (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) *
      (1 - q^30))^24 := by
  rw [discriminantPolyPart, etaPolyPart_thirty]

theorem etaPolyPart_thirtyone (q : R) :
    etaPolyPart q 31 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) * (1 - q^11) *
      (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) * (1 - q^16) * (1 - q^17) *
      (1 - q^18) * (1 - q^19) * (1 - q^20) * (1 - q^21) * (1 - q^22) * (1 - q^23) *
      (1 - q^24) * (1 - q^25) * (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) *
      (1 - q^30) * (1 - q^31) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_thirtyone (q : R) :
    discriminantPolyPart q 31 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) * (1 - q^11) *
      (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) * (1 - q^16) * (1 - q^17) *
      (1 - q^18) * (1 - q^19) * (1 - q^20) * (1 - q^21) * (1 - q^22) * (1 - q^23) *
      (1 - q^24) * (1 - q^25) * (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) *
      (1 - q^30) * (1 - q^31))^24 := by
  rw [discriminantPolyPart, etaPolyPart_thirtyone]

theorem etaPolyPart_thirtytwo (q : R) :
    etaPolyPart q 32 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) * (1 - q^11) *
      (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) * (1 - q^16) * (1 - q^17) *
      (1 - q^18) * (1 - q^19) * (1 - q^20) * (1 - q^21) * (1 - q^22) * (1 - q^23) *
      (1 - q^24) * (1 - q^25) * (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) *
      (1 - q^30) * (1 - q^31) * (1 - q^32) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_thirtytwo (q : R) :
    discriminantPolyPart q 32 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) * (1 - q^11) *
      (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) * (1 - q^16) * (1 - q^17) *
      (1 - q^18) * (1 - q^19) * (1 - q^20) * (1 - q^21) * (1 - q^22) * (1 - q^23) *
      (1 - q^24) * (1 - q^25) * (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) *
      (1 - q^30) * (1 - q^31) * (1 - q^32))^24 := by
  rw [discriminantPolyPart, etaPolyPart_thirtytwo]

theorem etaPolyPart_thirtythree (q : R) :
    etaPolyPart q 33 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) * (1 - q^11) *
      (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) * (1 - q^16) * (1 - q^17) *
      (1 - q^18) * (1 - q^19) * (1 - q^20) * (1 - q^21) * (1 - q^22) * (1 - q^23) *
      (1 - q^24) * (1 - q^25) * (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) *
      (1 - q^30) * (1 - q^31) * (1 - q^32) * (1 - q^33) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_thirtythree (q : R) :
    discriminantPolyPart q 33 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) * (1 - q^11) *
      (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) * (1 - q^16) * (1 - q^17) *
      (1 - q^18) * (1 - q^19) * (1 - q^20) * (1 - q^21) * (1 - q^22) * (1 - q^23) *
      (1 - q^24) * (1 - q^25) * (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) *
      (1 - q^30) * (1 - q^31) * (1 - q^32) * (1 - q^33))^24 := by
  rw [discriminantPolyPart, etaPolyPart_thirtythree]

theorem etaPolyPart_thirtyfour (q : R) :
    etaPolyPart q 34 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) * (1 - q^11) *
      (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) * (1 - q^16) * (1 - q^17) *
      (1 - q^18) * (1 - q^19) * (1 - q^20) * (1 - q^21) * (1 - q^22) * (1 - q^23) *
      (1 - q^24) * (1 - q^25) * (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) *
      (1 - q^30) * (1 - q^31) * (1 - q^32) * (1 - q^33) * (1 - q^34) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_thirtyfour (q : R) :
    discriminantPolyPart q 34 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) * (1 - q^11) *
      (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) * (1 - q^16) * (1 - q^17) *
      (1 - q^18) * (1 - q^19) * (1 - q^20) * (1 - q^21) * (1 - q^22) * (1 - q^23) *
      (1 - q^24) * (1 - q^25) * (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) *
      (1 - q^30) * (1 - q^31) * (1 - q^32) * (1 - q^33) * (1 - q^34))^24 := by
  rw [discriminantPolyPart, etaPolyPart_thirtyfour]

theorem etaPolyPart_thirtyfive (q : R) :
    etaPolyPart q 35 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) * (1 - q^11) *
      (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) * (1 - q^16) * (1 - q^17) *
      (1 - q^18) * (1 - q^19) * (1 - q^20) * (1 - q^21) * (1 - q^22) * (1 - q^23) *
      (1 - q^24) * (1 - q^25) * (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) *
      (1 - q^30) * (1 - q^31) * (1 - q^32) * (1 - q^33) * (1 - q^34) * (1 - q^35) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_thirtyfive (q : R) :
    discriminantPolyPart q 35 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) * (1 - q^11) *
      (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) * (1 - q^16) * (1 - q^17) *
      (1 - q^18) * (1 - q^19) * (1 - q^20) * (1 - q^21) * (1 - q^22) * (1 - q^23) *
      (1 - q^24) * (1 - q^25) * (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) *
      (1 - q^30) * (1 - q^31) * (1 - q^32) * (1 - q^33) * (1 - q^34) * (1 - q^35))^24 := by
  rw [discriminantPolyPart, etaPolyPart_thirtyfive]

theorem etaPolyPart_thirtysix (q : R) :
    etaPolyPart q 36 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) * (1 - q^11) *
      (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) * (1 - q^16) * (1 - q^17) *
      (1 - q^18) * (1 - q^19) * (1 - q^20) * (1 - q^21) * (1 - q^22) * (1 - q^23) *
      (1 - q^24) * (1 - q^25) * (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) *
      (1 - q^30) * (1 - q^31) * (1 - q^32) * (1 - q^33) * (1 - q^34) * (1 - q^35) *
      (1 - q^36) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_thirtysix (q : R) :
    discriminantPolyPart q 36 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) * (1 - q^11) *
      (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) * (1 - q^16) * (1 - q^17) *
      (1 - q^18) * (1 - q^19) * (1 - q^20) * (1 - q^21) * (1 - q^22) * (1 - q^23) *
      (1 - q^24) * (1 - q^25) * (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) *
      (1 - q^30) * (1 - q^31) * (1 - q^32) * (1 - q^33) * (1 - q^34) * (1 - q^35) *
      (1 - q^36))^24 := by
  rw [discriminantPolyPart, etaPolyPart_thirtysix]

theorem etaPolyPart_thirtyseven (q : R) :
    etaPolyPart q 37 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) * (1 - q^11) *
      (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) * (1 - q^16) * (1 - q^17) *
      (1 - q^18) * (1 - q^19) * (1 - q^20) * (1 - q^21) * (1 - q^22) * (1 - q^23) *
      (1 - q^24) * (1 - q^25) * (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) *
      (1 - q^30) * (1 - q^31) * (1 - q^32) * (1 - q^33) * (1 - q^34) * (1 - q^35) *
      (1 - q^36) * (1 - q^37) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_thirtyseven (q : R) :
    discriminantPolyPart q 37 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) * (1 - q^11) *
      (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) * (1 - q^16) * (1 - q^17) *
      (1 - q^18) * (1 - q^19) * (1 - q^20) * (1 - q^21) * (1 - q^22) * (1 - q^23) *
      (1 - q^24) * (1 - q^25) * (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) *
      (1 - q^30) * (1 - q^31) * (1 - q^32) * (1 - q^33) * (1 - q^34) * (1 - q^35) *
      (1 - q^36) * (1 - q^37))^24 := by
  rw [discriminantPolyPart, etaPolyPart_thirtyseven]

theorem etaPolyPart_thirtyeight (q : R) :
    etaPolyPart q 38 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) * (1 - q^11) *
      (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) * (1 - q^16) * (1 - q^17) *
      (1 - q^18) * (1 - q^19) * (1 - q^20) * (1 - q^21) * (1 - q^22) * (1 - q^23) *
      (1 - q^24) * (1 - q^25) * (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) *
      (1 - q^30) * (1 - q^31) * (1 - q^32) * (1 - q^33) * (1 - q^34) * (1 - q^35) *
      (1 - q^36) * (1 - q^37) * (1 - q^38) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_thirtyeight (q : R) :
    discriminantPolyPart q 38 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) * (1 - q^11) *
      (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) * (1 - q^16) * (1 - q^17) *
      (1 - q^18) * (1 - q^19) * (1 - q^20) * (1 - q^21) * (1 - q^22) * (1 - q^23) *
      (1 - q^24) * (1 - q^25) * (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) *
      (1 - q^30) * (1 - q^31) * (1 - q^32) * (1 - q^33) * (1 - q^34) * (1 - q^35) *
      (1 - q^36) * (1 - q^37) * (1 - q^38))^24 := by
  rw [discriminantPolyPart, etaPolyPart_thirtyeight]

theorem etaPolyPart_thirtynine (q : R) :
    etaPolyPart q 39 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) * (1 - q^11) *
      (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) * (1 - q^16) * (1 - q^17) *
      (1 - q^18) * (1 - q^19) * (1 - q^20) * (1 - q^21) * (1 - q^22) * (1 - q^23) *
      (1 - q^24) * (1 - q^25) * (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) *
      (1 - q^30) * (1 - q^31) * (1 - q^32) * (1 - q^33) * (1 - q^34) * (1 - q^35) *
      (1 - q^36) * (1 - q^37) * (1 - q^38) * (1 - q^39) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_thirtynine (q : R) :
    discriminantPolyPart q 39 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) * (1 - q^11) *
      (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) * (1 - q^16) * (1 - q^17) *
      (1 - q^18) * (1 - q^19) * (1 - q^20) * (1 - q^21) * (1 - q^22) * (1 - q^23) *
      (1 - q^24) * (1 - q^25) * (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) *
      (1 - q^30) * (1 - q^31) * (1 - q^32) * (1 - q^33) * (1 - q^34) * (1 - q^35) *
      (1 - q^36) * (1 - q^37) * (1 - q^38) * (1 - q^39))^24 := by
  rw [discriminantPolyPart, etaPolyPart_thirtynine]

theorem etaPolyPart_forty (q : R) :
    etaPolyPart q 40 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) * (1 - q^11) *
      (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) * (1 - q^16) * (1 - q^17) *
      (1 - q^18) * (1 - q^19) * (1 - q^20) * (1 - q^21) * (1 - q^22) * (1 - q^23) *
      (1 - q^24) * (1 - q^25) * (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) *
      (1 - q^30) * (1 - q^31) * (1 - q^32) * (1 - q^33) * (1 - q^34) * (1 - q^35) *
      (1 - q^36) * (1 - q^37) * (1 - q^38) * (1 - q^39) * (1 - q^40) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_forty (q : R) :
    discriminantPolyPart q 40 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) * (1 - q^11) *
      (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) * (1 - q^16) * (1 - q^17) *
      (1 - q^18) * (1 - q^19) * (1 - q^20) * (1 - q^21) * (1 - q^22) * (1 - q^23) *
      (1 - q^24) * (1 - q^25) * (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) *
      (1 - q^30) * (1 - q^31) * (1 - q^32) * (1 - q^33) * (1 - q^34) * (1 - q^35) *
      (1 - q^36) * (1 - q^37) * (1 - q^38) * (1 - q^39) * (1 - q^40))^24 := by
  rw [discriminantPolyPart, etaPolyPart_forty]

theorem etaPolyPart_fortyone (q : R) :
    etaPolyPart q 41 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) * (1 - q^11) *
      (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) * (1 - q^16) * (1 - q^17) *
      (1 - q^18) * (1 - q^19) * (1 - q^20) * (1 - q^21) * (1 - q^22) * (1 - q^23) *
      (1 - q^24) * (1 - q^25) * (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) *
      (1 - q^30) * (1 - q^31) * (1 - q^32) * (1 - q^33) * (1 - q^34) * (1 - q^35) *
      (1 - q^36) * (1 - q^37) * (1 - q^38) * (1 - q^39) * (1 - q^40) * (1 - q^41) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_fortyone (q : R) :
    discriminantPolyPart q 41 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) * (1 - q^11) *
      (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) * (1 - q^16) * (1 - q^17) *
      (1 - q^18) * (1 - q^19) * (1 - q^20) * (1 - q^21) * (1 - q^22) * (1 - q^23) *
      (1 - q^24) * (1 - q^25) * (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) *
      (1 - q^30) * (1 - q^31) * (1 - q^32) * (1 - q^33) * (1 - q^34) * (1 - q^35) *
      (1 - q^36) * (1 - q^37) * (1 - q^38) * (1 - q^39) * (1 - q^40) * (1 - q^41))^24 := by
  rw [discriminantPolyPart, etaPolyPart_fortyone]

theorem etaPolyPart_fortytwo (q : R) :
    etaPolyPart q 42 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) * (1 - q^11) *
      (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) * (1 - q^16) * (1 - q^17) *
      (1 - q^18) * (1 - q^19) * (1 - q^20) * (1 - q^21) * (1 - q^22) * (1 - q^23) *
      (1 - q^24) * (1 - q^25) * (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) *
      (1 - q^30) * (1 - q^31) * (1 - q^32) * (1 - q^33) * (1 - q^34) * (1 - q^35) *
      (1 - q^36) * (1 - q^37) * (1 - q^38) * (1 - q^39) * (1 - q^40) * (1 - q^41) *
      (1 - q^42) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_fortytwo (q : R) :
    discriminantPolyPart q 42 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) * (1 - q^11) *
      (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) * (1 - q^16) * (1 - q^17) *
      (1 - q^18) * (1 - q^19) * (1 - q^20) * (1 - q^21) * (1 - q^22) * (1 - q^23) *
      (1 - q^24) * (1 - q^25) * (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) *
      (1 - q^30) * (1 - q^31) * (1 - q^32) * (1 - q^33) * (1 - q^34) * (1 - q^35) *
      (1 - q^36) * (1 - q^37) * (1 - q^38) * (1 - q^39) * (1 - q^40) * (1 - q^41) *
      (1 - q^42))^24 := by
  rw [discriminantPolyPart, etaPolyPart_fortytwo]

theorem etaPolyPart_fortythree (q : R) :
    etaPolyPart q 43 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) * (1 - q^11) *
      (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) * (1 - q^16) * (1 - q^17) *
      (1 - q^18) * (1 - q^19) * (1 - q^20) * (1 - q^21) * (1 - q^22) * (1 - q^23) *
      (1 - q^24) * (1 - q^25) * (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) *
      (1 - q^30) * (1 - q^31) * (1 - q^32) * (1 - q^33) * (1 - q^34) * (1 - q^35) *
      (1 - q^36) * (1 - q^37) * (1 - q^38) * (1 - q^39) * (1 - q^40) * (1 - q^41) *
      (1 - q^42) * (1 - q^43) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_fortythree (q : R) :
    discriminantPolyPart q 43 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) * (1 - q^11) *
      (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) * (1 - q^16) * (1 - q^17) *
      (1 - q^18) * (1 - q^19) * (1 - q^20) * (1 - q^21) * (1 - q^22) * (1 - q^23) *
      (1 - q^24) * (1 - q^25) * (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) *
      (1 - q^30) * (1 - q^31) * (1 - q^32) * (1 - q^33) * (1 - q^34) * (1 - q^35) *
      (1 - q^36) * (1 - q^37) * (1 - q^38) * (1 - q^39) * (1 - q^40) * (1 - q^41) *
      (1 - q^42) * (1 - q^43))^24 := by
  rw [discriminantPolyPart, etaPolyPart_fortythree]

theorem etaPolyPart_fortyfour (q : R) :
    etaPolyPart q 44 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) * (1 - q^11) *
      (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) * (1 - q^16) * (1 - q^17) *
      (1 - q^18) * (1 - q^19) * (1 - q^20) * (1 - q^21) * (1 - q^22) * (1 - q^23) *
      (1 - q^24) * (1 - q^25) * (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) *
      (1 - q^30) * (1 - q^31) * (1 - q^32) * (1 - q^33) * (1 - q^34) * (1 - q^35) *
      (1 - q^36) * (1 - q^37) * (1 - q^38) * (1 - q^39) * (1 - q^40) * (1 - q^41) *
      (1 - q^42) * (1 - q^43) * (1 - q^44) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_fortyfour (q : R) :
    discriminantPolyPart q 44 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) * (1 - q^11) *
      (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) * (1 - q^16) * (1 - q^17) *
      (1 - q^18) * (1 - q^19) * (1 - q^20) * (1 - q^21) * (1 - q^22) * (1 - q^23) *
      (1 - q^24) * (1 - q^25) * (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) *
      (1 - q^30) * (1 - q^31) * (1 - q^32) * (1 - q^33) * (1 - q^34) * (1 - q^35) *
      (1 - q^36) * (1 - q^37) * (1 - q^38) * (1 - q^39) * (1 - q^40) * (1 - q^41) *
      (1 - q^42) * (1 - q^43) * (1 - q^44))^24 := by
  rw [discriminantPolyPart, etaPolyPart_fortyfour]

theorem etaPolyPart_fortyfive (q : R) :
    etaPolyPart q 45 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) * (1 - q^11) *
      (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) * (1 - q^16) * (1 - q^17) *
      (1 - q^18) * (1 - q^19) * (1 - q^20) * (1 - q^21) * (1 - q^22) * (1 - q^23) *
      (1 - q^24) * (1 - q^25) * (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) *
      (1 - q^30) * (1 - q^31) * (1 - q^32) * (1 - q^33) * (1 - q^34) * (1 - q^35) *
      (1 - q^36) * (1 - q^37) * (1 - q^38) * (1 - q^39) * (1 - q^40) * (1 - q^41) *
      (1 - q^42) * (1 - q^43) * (1 - q^44) * (1 - q^45) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_fortyfive (q : R) :
    discriminantPolyPart q 45 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) * (1 - q^11) *
      (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) * (1 - q^16) * (1 - q^17) *
      (1 - q^18) * (1 - q^19) * (1 - q^20) * (1 - q^21) * (1 - q^22) * (1 - q^23) *
      (1 - q^24) * (1 - q^25) * (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) *
      (1 - q^30) * (1 - q^31) * (1 - q^32) * (1 - q^33) * (1 - q^34) * (1 - q^35) *
      (1 - q^36) * (1 - q^37) * (1 - q^38) * (1 - q^39) * (1 - q^40) * (1 - q^41) *
      (1 - q^42) * (1 - q^43) * (1 - q^44) * (1 - q^45))^24 := by
  rw [discriminantPolyPart, etaPolyPart_fortyfive]

theorem etaPolyPart_fortysix (q : R) :
    etaPolyPart q 46 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) *
      (1 - q^11) * (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) *
      (1 - q^16) * (1 - q^17) * (1 - q^18) * (1 - q^19) * (1 - q^20) *
      (1 - q^21) * (1 - q^22) * (1 - q^23) * (1 - q^24) * (1 - q^25) *
      (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) * (1 - q^30) *
      (1 - q^31) * (1 - q^32) * (1 - q^33) * (1 - q^34) * (1 - q^35) *
      (1 - q^36) * (1 - q^37) * (1 - q^38) * (1 - q^39) * (1 - q^40) *
      (1 - q^41) * (1 - q^42) * (1 - q^43) * (1 - q^44) * (1 - q^45) *
      (1 - q^46) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_fortysix (q : R) :
    discriminantPolyPart q 46 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) *
      (1 - q^11) * (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) *
      (1 - q^16) * (1 - q^17) * (1 - q^18) * (1 - q^19) * (1 - q^20) *
      (1 - q^21) * (1 - q^22) * (1 - q^23) * (1 - q^24) * (1 - q^25) *
      (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) * (1 - q^30) *
      (1 - q^31) * (1 - q^32) * (1 - q^33) * (1 - q^34) * (1 - q^35) *
      (1 - q^36) * (1 - q^37) * (1 - q^38) * (1 - q^39) * (1 - q^40) *
      (1 - q^41) * (1 - q^42) * (1 - q^43) * (1 - q^44) * (1 - q^45) *
      (1 - q^46))^24 := by
  rw [discriminantPolyPart, etaPolyPart_fortysix]

theorem etaPolyPart_fortyseven (q : R) :
    etaPolyPart q 47 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) *
      (1 - q^11) * (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) *
      (1 - q^16) * (1 - q^17) * (1 - q^18) * (1 - q^19) * (1 - q^20) *
      (1 - q^21) * (1 - q^22) * (1 - q^23) * (1 - q^24) * (1 - q^25) *
      (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) * (1 - q^30) *
      (1 - q^31) * (1 - q^32) * (1 - q^33) * (1 - q^34) * (1 - q^35) *
      (1 - q^36) * (1 - q^37) * (1 - q^38) * (1 - q^39) * (1 - q^40) *
      (1 - q^41) * (1 - q^42) * (1 - q^43) * (1 - q^44) * (1 - q^45) *
      (1 - q^46) * (1 - q^47) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_fortyseven (q : R) :
    discriminantPolyPart q 47 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) *
      (1 - q^11) * (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) *
      (1 - q^16) * (1 - q^17) * (1 - q^18) * (1 - q^19) * (1 - q^20) *
      (1 - q^21) * (1 - q^22) * (1 - q^23) * (1 - q^24) * (1 - q^25) *
      (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) * (1 - q^30) *
      (1 - q^31) * (1 - q^32) * (1 - q^33) * (1 - q^34) * (1 - q^35) *
      (1 - q^36) * (1 - q^37) * (1 - q^38) * (1 - q^39) * (1 - q^40) *
      (1 - q^41) * (1 - q^42) * (1 - q^43) * (1 - q^44) * (1 - q^45) *
      (1 - q^46) * (1 - q^47))^24 := by
  rw [discriminantPolyPart, etaPolyPart_fortyseven]

theorem etaPolyPart_fortyeight (q : R) :
    etaPolyPart q 48 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) *
      (1 - q^11) * (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) *
      (1 - q^16) * (1 - q^17) * (1 - q^18) * (1 - q^19) * (1 - q^20) *
      (1 - q^21) * (1 - q^22) * (1 - q^23) * (1 - q^24) * (1 - q^25) *
      (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) * (1 - q^30) *
      (1 - q^31) * (1 - q^32) * (1 - q^33) * (1 - q^34) * (1 - q^35) *
      (1 - q^36) * (1 - q^37) * (1 - q^38) * (1 - q^39) * (1 - q^40) *
      (1 - q^41) * (1 - q^42) * (1 - q^43) * (1 - q^44) * (1 - q^45) *
      (1 - q^46) * (1 - q^47) * (1 - q^48) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_fortyeight (q : R) :
    discriminantPolyPart q 48 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) *
      (1 - q^11) * (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) *
      (1 - q^16) * (1 - q^17) * (1 - q^18) * (1 - q^19) * (1 - q^20) *
      (1 - q^21) * (1 - q^22) * (1 - q^23) * (1 - q^24) * (1 - q^25) *
      (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) * (1 - q^30) *
      (1 - q^31) * (1 - q^32) * (1 - q^33) * (1 - q^34) * (1 - q^35) *
      (1 - q^36) * (1 - q^37) * (1 - q^38) * (1 - q^39) * (1 - q^40) *
      (1 - q^41) * (1 - q^42) * (1 - q^43) * (1 - q^44) * (1 - q^45) *
      (1 - q^46) * (1 - q^47) * (1 - q^48))^24 := by
  rw [discriminantPolyPart, etaPolyPart_fortyeight]

theorem etaPolyPart_fortynine (q : R) :
    etaPolyPart q 49 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) *
      (1 - q^11) * (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) *
      (1 - q^16) * (1 - q^17) * (1 - q^18) * (1 - q^19) * (1 - q^20) *
      (1 - q^21) * (1 - q^22) * (1 - q^23) * (1 - q^24) * (1 - q^25) *
      (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) * (1 - q^30) *
      (1 - q^31) * (1 - q^32) * (1 - q^33) * (1 - q^34) * (1 - q^35) *
      (1 - q^36) * (1 - q^37) * (1 - q^38) * (1 - q^39) * (1 - q^40) *
      (1 - q^41) * (1 - q^42) * (1 - q^43) * (1 - q^44) * (1 - q^45) *
      (1 - q^46) * (1 - q^47) * (1 - q^48) * (1 - q^49) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_fortynine (q : R) :
    discriminantPolyPart q 49 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) *
      (1 - q^11) * (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) *
      (1 - q^16) * (1 - q^17) * (1 - q^18) * (1 - q^19) * (1 - q^20) *
      (1 - q^21) * (1 - q^22) * (1 - q^23) * (1 - q^24) * (1 - q^25) *
      (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) * (1 - q^30) *
      (1 - q^31) * (1 - q^32) * (1 - q^33) * (1 - q^34) * (1 - q^35) *
      (1 - q^36) * (1 - q^37) * (1 - q^38) * (1 - q^39) * (1 - q^40) *
      (1 - q^41) * (1 - q^42) * (1 - q^43) * (1 - q^44) * (1 - q^45) *
      (1 - q^46) * (1 - q^47) * (1 - q^48) * (1 - q^49))^24 := by
  rw [discriminantPolyPart, etaPolyPart_fortynine]

theorem etaPolyPart_fifty (q : R) :
    etaPolyPart q 50 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) *
      (1 - q^11) * (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) *
      (1 - q^16) * (1 - q^17) * (1 - q^18) * (1 - q^19) * (1 - q^20) *
      (1 - q^21) * (1 - q^22) * (1 - q^23) * (1 - q^24) * (1 - q^25) *
      (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) * (1 - q^30) *
      (1 - q^31) * (1 - q^32) * (1 - q^33) * (1 - q^34) * (1 - q^35) *
      (1 - q^36) * (1 - q^37) * (1 - q^38) * (1 - q^39) * (1 - q^40) *
      (1 - q^41) * (1 - q^42) * (1 - q^43) * (1 - q^44) * (1 - q^45) *
      (1 - q^46) * (1 - q^47) * (1 - q^48) * (1 - q^49) * (1 - q^50) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_fifty (q : R) :
    discriminantPolyPart q 50 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) *
      (1 - q^11) * (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) *
      (1 - q^16) * (1 - q^17) * (1 - q^18) * (1 - q^19) * (1 - q^20) *
      (1 - q^21) * (1 - q^22) * (1 - q^23) * (1 - q^24) * (1 - q^25) *
      (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) * (1 - q^30) *
      (1 - q^31) * (1 - q^32) * (1 - q^33) * (1 - q^34) * (1 - q^35) *
      (1 - q^36) * (1 - q^37) * (1 - q^38) * (1 - q^39) * (1 - q^40) *
      (1 - q^41) * (1 - q^42) * (1 - q^43) * (1 - q^44) * (1 - q^45) *
      (1 - q^46) * (1 - q^47) * (1 - q^48) * (1 - q^49) * (1 - q^50))^24 := by
  rw [discriminantPolyPart, etaPolyPart_fifty]

theorem etaPolyPart_fiftyone (q : R) :
    etaPolyPart q 51 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) *
      (1 - q^11) * (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) *
      (1 - q^16) * (1 - q^17) * (1 - q^18) * (1 - q^19) * (1 - q^20) *
      (1 - q^21) * (1 - q^22) * (1 - q^23) * (1 - q^24) * (1 - q^25) *
      (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) * (1 - q^30) *
      (1 - q^31) * (1 - q^32) * (1 - q^33) * (1 - q^34) * (1 - q^35) *
      (1 - q^36) * (1 - q^37) * (1 - q^38) * (1 - q^39) * (1 - q^40) *
      (1 - q^41) * (1 - q^42) * (1 - q^43) * (1 - q^44) * (1 - q^45) *
      (1 - q^46) * (1 - q^47) * (1 - q^48) * (1 - q^49) * (1 - q^50) *
      (1 - q^51) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_fiftyone (q : R) :
    discriminantPolyPart q 51 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) *
      (1 - q^11) * (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) *
      (1 - q^16) * (1 - q^17) * (1 - q^18) * (1 - q^19) * (1 - q^20) *
      (1 - q^21) * (1 - q^22) * (1 - q^23) * (1 - q^24) * (1 - q^25) *
      (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) * (1 - q^30) *
      (1 - q^31) * (1 - q^32) * (1 - q^33) * (1 - q^34) * (1 - q^35) *
      (1 - q^36) * (1 - q^37) * (1 - q^38) * (1 - q^39) * (1 - q^40) *
      (1 - q^41) * (1 - q^42) * (1 - q^43) * (1 - q^44) * (1 - q^45) *
      (1 - q^46) * (1 - q^47) * (1 - q^48) * (1 - q^49) * (1 - q^50) *
      (1 - q^51))^24 := by
  rw [discriminantPolyPart, etaPolyPart_fiftyone]

theorem etaPolyPart_fiftytwo (q : R) :
    etaPolyPart q 52 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) *
      (1 - q^11) * (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) *
      (1 - q^16) * (1 - q^17) * (1 - q^18) * (1 - q^19) * (1 - q^20) *
      (1 - q^21) * (1 - q^22) * (1 - q^23) * (1 - q^24) * (1 - q^25) *
      (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) * (1 - q^30) *
      (1 - q^31) * (1 - q^32) * (1 - q^33) * (1 - q^34) * (1 - q^35) *
      (1 - q^36) * (1 - q^37) * (1 - q^38) * (1 - q^39) * (1 - q^40) *
      (1 - q^41) * (1 - q^42) * (1 - q^43) * (1 - q^44) * (1 - q^45) *
      (1 - q^46) * (1 - q^47) * (1 - q^48) * (1 - q^49) * (1 - q^50) *
      (1 - q^51) * (1 - q^52) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_fiftytwo (q : R) :
    discriminantPolyPart q 52 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) *
      (1 - q^11) * (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) *
      (1 - q^16) * (1 - q^17) * (1 - q^18) * (1 - q^19) * (1 - q^20) *
      (1 - q^21) * (1 - q^22) * (1 - q^23) * (1 - q^24) * (1 - q^25) *
      (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) * (1 - q^30) *
      (1 - q^31) * (1 - q^32) * (1 - q^33) * (1 - q^34) * (1 - q^35) *
      (1 - q^36) * (1 - q^37) * (1 - q^38) * (1 - q^39) * (1 - q^40) *
      (1 - q^41) * (1 - q^42) * (1 - q^43) * (1 - q^44) * (1 - q^45) *
      (1 - q^46) * (1 - q^47) * (1 - q^48) * (1 - q^49) * (1 - q^50) *
      (1 - q^51) * (1 - q^52))^24 := by
  rw [discriminantPolyPart, etaPolyPart_fiftytwo]

theorem etaPolyPart_fiftythree (q : R) :
    etaPolyPart q 53 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) *
      (1 - q^11) * (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) *
      (1 - q^16) * (1 - q^17) * (1 - q^18) * (1 - q^19) * (1 - q^20) *
      (1 - q^21) * (1 - q^22) * (1 - q^23) * (1 - q^24) * (1 - q^25) *
      (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) * (1 - q^30) *
      (1 - q^31) * (1 - q^32) * (1 - q^33) * (1 - q^34) * (1 - q^35) *
      (1 - q^36) * (1 - q^37) * (1 - q^38) * (1 - q^39) * (1 - q^40) *
      (1 - q^41) * (1 - q^42) * (1 - q^43) * (1 - q^44) * (1 - q^45) *
      (1 - q^46) * (1 - q^47) * (1 - q^48) * (1 - q^49) * (1 - q^50) *
      (1 - q^51) * (1 - q^52) * (1 - q^53) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_fiftythree (q : R) :
    discriminantPolyPart q 53 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) *
      (1 - q^11) * (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) *
      (1 - q^16) * (1 - q^17) * (1 - q^18) * (1 - q^19) * (1 - q^20) *
      (1 - q^21) * (1 - q^22) * (1 - q^23) * (1 - q^24) * (1 - q^25) *
      (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) * (1 - q^30) *
      (1 - q^31) * (1 - q^32) * (1 - q^33) * (1 - q^34) * (1 - q^35) *
      (1 - q^36) * (1 - q^37) * (1 - q^38) * (1 - q^39) * (1 - q^40) *
      (1 - q^41) * (1 - q^42) * (1 - q^43) * (1 - q^44) * (1 - q^45) *
      (1 - q^46) * (1 - q^47) * (1 - q^48) * (1 - q^49) * (1 - q^50) *
      (1 - q^51) * (1 - q^52) * (1 - q^53))^24 := by
  rw [discriminantPolyPart, etaPolyPart_fiftythree]

theorem etaPolyPart_fiftyfour (q : R) :
    etaPolyPart q 54 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) *
      (1 - q^11) * (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) *
      (1 - q^16) * (1 - q^17) * (1 - q^18) * (1 - q^19) * (1 - q^20) *
      (1 - q^21) * (1 - q^22) * (1 - q^23) * (1 - q^24) * (1 - q^25) *
      (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) * (1 - q^30) *
      (1 - q^31) * (1 - q^32) * (1 - q^33) * (1 - q^34) * (1 - q^35) *
      (1 - q^36) * (1 - q^37) * (1 - q^38) * (1 - q^39) * (1 - q^40) *
      (1 - q^41) * (1 - q^42) * (1 - q^43) * (1 - q^44) * (1 - q^45) *
      (1 - q^46) * (1 - q^47) * (1 - q^48) * (1 - q^49) * (1 - q^50) *
      (1 - q^51) * (1 - q^52) * (1 - q^53) * (1 - q^54) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_fiftyfour (q : R) :
    discriminantPolyPart q 54 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) *
      (1 - q^11) * (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) *
      (1 - q^16) * (1 - q^17) * (1 - q^18) * (1 - q^19) * (1 - q^20) *
      (1 - q^21) * (1 - q^22) * (1 - q^23) * (1 - q^24) * (1 - q^25) *
      (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) * (1 - q^30) *
      (1 - q^31) * (1 - q^32) * (1 - q^33) * (1 - q^34) * (1 - q^35) *
      (1 - q^36) * (1 - q^37) * (1 - q^38) * (1 - q^39) * (1 - q^40) *
      (1 - q^41) * (1 - q^42) * (1 - q^43) * (1 - q^44) * (1 - q^45) *
      (1 - q^46) * (1 - q^47) * (1 - q^48) * (1 - q^49) * (1 - q^50) *
      (1 - q^51) * (1 - q^52) * (1 - q^53) * (1 - q^54))^24 := by
  rw [discriminantPolyPart, etaPolyPart_fiftyfour]

theorem etaPolyPart_fiftyfive (q : R) :
    etaPolyPart q 55 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) *
      (1 - q^11) * (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) *
      (1 - q^16) * (1 - q^17) * (1 - q^18) * (1 - q^19) * (1 - q^20) *
      (1 - q^21) * (1 - q^22) * (1 - q^23) * (1 - q^24) * (1 - q^25) *
      (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) * (1 - q^30) *
      (1 - q^31) * (1 - q^32) * (1 - q^33) * (1 - q^34) * (1 - q^35) *
      (1 - q^36) * (1 - q^37) * (1 - q^38) * (1 - q^39) * (1 - q^40) *
      (1 - q^41) * (1 - q^42) * (1 - q^43) * (1 - q^44) * (1 - q^45) *
      (1 - q^46) * (1 - q^47) * (1 - q^48) * (1 - q^49) * (1 - q^50) *
      (1 - q^51) * (1 - q^52) * (1 - q^53) * (1 - q^54) * (1 - q^55) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_fiftyfive (q : R) :
    discriminantPolyPart q 55 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) *
      (1 - q^11) * (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) *
      (1 - q^16) * (1 - q^17) * (1 - q^18) * (1 - q^19) * (1 - q^20) *
      (1 - q^21) * (1 - q^22) * (1 - q^23) * (1 - q^24) * (1 - q^25) *
      (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) * (1 - q^30) *
      (1 - q^31) * (1 - q^32) * (1 - q^33) * (1 - q^34) * (1 - q^35) *
      (1 - q^36) * (1 - q^37) * (1 - q^38) * (1 - q^39) * (1 - q^40) *
      (1 - q^41) * (1 - q^42) * (1 - q^43) * (1 - q^44) * (1 - q^45) *
      (1 - q^46) * (1 - q^47) * (1 - q^48) * (1 - q^49) * (1 - q^50) *
      (1 - q^51) * (1 - q^52) * (1 - q^53) * (1 - q^54) * (1 - q^55))^24 := by
  rw [discriminantPolyPart, etaPolyPart_fiftyfive]

theorem etaPolyPart_fiftysix (q : R) :
    etaPolyPart q 56 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) *
      (1 - q^11) * (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) *
      (1 - q^16) * (1 - q^17) * (1 - q^18) * (1 - q^19) * (1 - q^20) *
      (1 - q^21) * (1 - q^22) * (1 - q^23) * (1 - q^24) * (1 - q^25) *
      (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) * (1 - q^30) *
      (1 - q^31) * (1 - q^32) * (1 - q^33) * (1 - q^34) * (1 - q^35) *
      (1 - q^36) * (1 - q^37) * (1 - q^38) * (1 - q^39) * (1 - q^40) *
      (1 - q^41) * (1 - q^42) * (1 - q^43) * (1 - q^44) * (1 - q^45) *
      (1 - q^46) * (1 - q^47) * (1 - q^48) * (1 - q^49) * (1 - q^50) *
      (1 - q^51) * (1 - q^52) * (1 - q^53) * (1 - q^54) * (1 - q^55) *
      (1 - q^56) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_fiftysix (q : R) :
    discriminantPolyPart q 56 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) *
      (1 - q^11) * (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) *
      (1 - q^16) * (1 - q^17) * (1 - q^18) * (1 - q^19) * (1 - q^20) *
      (1 - q^21) * (1 - q^22) * (1 - q^23) * (1 - q^24) * (1 - q^25) *
      (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) * (1 - q^30) *
      (1 - q^31) * (1 - q^32) * (1 - q^33) * (1 - q^34) * (1 - q^35) *
      (1 - q^36) * (1 - q^37) * (1 - q^38) * (1 - q^39) * (1 - q^40) *
      (1 - q^41) * (1 - q^42) * (1 - q^43) * (1 - q^44) * (1 - q^45) *
      (1 - q^46) * (1 - q^47) * (1 - q^48) * (1 - q^49) * (1 - q^50) *
      (1 - q^51) * (1 - q^52) * (1 - q^53) * (1 - q^54) * (1 - q^55) *
      (1 - q^56))^24 := by
  rw [discriminantPolyPart, etaPolyPart_fiftysix]

theorem etaPolyPart_fiftyseven (q : R) :
    etaPolyPart q 57 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) *
      (1 - q^11) * (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) *
      (1 - q^16) * (1 - q^17) * (1 - q^18) * (1 - q^19) * (1 - q^20) *
      (1 - q^21) * (1 - q^22) * (1 - q^23) * (1 - q^24) * (1 - q^25) *
      (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) * (1 - q^30) *
      (1 - q^31) * (1 - q^32) * (1 - q^33) * (1 - q^34) * (1 - q^35) *
      (1 - q^36) * (1 - q^37) * (1 - q^38) * (1 - q^39) * (1 - q^40) *
      (1 - q^41) * (1 - q^42) * (1 - q^43) * (1 - q^44) * (1 - q^45) *
      (1 - q^46) * (1 - q^47) * (1 - q^48) * (1 - q^49) * (1 - q^50) *
      (1 - q^51) * (1 - q^52) * (1 - q^53) * (1 - q^54) * (1 - q^55) *
      (1 - q^56) * (1 - q^57) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_fiftyseven (q : R) :
    discriminantPolyPart q 57 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) *
      (1 - q^11) * (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) *
      (1 - q^16) * (1 - q^17) * (1 - q^18) * (1 - q^19) * (1 - q^20) *
      (1 - q^21) * (1 - q^22) * (1 - q^23) * (1 - q^24) * (1 - q^25) *
      (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) * (1 - q^30) *
      (1 - q^31) * (1 - q^32) * (1 - q^33) * (1 - q^34) * (1 - q^35) *
      (1 - q^36) * (1 - q^37) * (1 - q^38) * (1 - q^39) * (1 - q^40) *
      (1 - q^41) * (1 - q^42) * (1 - q^43) * (1 - q^44) * (1 - q^45) *
      (1 - q^46) * (1 - q^47) * (1 - q^48) * (1 - q^49) * (1 - q^50) *
      (1 - q^51) * (1 - q^52) * (1 - q^53) * (1 - q^54) * (1 - q^55) *
      (1 - q^56) * (1 - q^57))^24 := by
  rw [discriminantPolyPart, etaPolyPart_fiftyseven]

theorem etaPolyPart_fiftyeight (q : R) :
    etaPolyPart q 58 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) *
      (1 - q^11) * (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) *
      (1 - q^16) * (1 - q^17) * (1 - q^18) * (1 - q^19) * (1 - q^20) *
      (1 - q^21) * (1 - q^22) * (1 - q^23) * (1 - q^24) * (1 - q^25) *
      (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) * (1 - q^30) *
      (1 - q^31) * (1 - q^32) * (1 - q^33) * (1 - q^34) * (1 - q^35) *
      (1 - q^36) * (1 - q^37) * (1 - q^38) * (1 - q^39) * (1 - q^40) *
      (1 - q^41) * (1 - q^42) * (1 - q^43) * (1 - q^44) * (1 - q^45) *
      (1 - q^46) * (1 - q^47) * (1 - q^48) * (1 - q^49) * (1 - q^50) *
      (1 - q^51) * (1 - q^52) * (1 - q^53) * (1 - q^54) * (1 - q^55) *
      (1 - q^56) * (1 - q^57) * (1 - q^58) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_fiftyeight (q : R) :
    discriminantPolyPart q 58 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) *
      (1 - q^11) * (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) *
      (1 - q^16) * (1 - q^17) * (1 - q^18) * (1 - q^19) * (1 - q^20) *
      (1 - q^21) * (1 - q^22) * (1 - q^23) * (1 - q^24) * (1 - q^25) *
      (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) * (1 - q^30) *
      (1 - q^31) * (1 - q^32) * (1 - q^33) * (1 - q^34) * (1 - q^35) *
      (1 - q^36) * (1 - q^37) * (1 - q^38) * (1 - q^39) * (1 - q^40) *
      (1 - q^41) * (1 - q^42) * (1 - q^43) * (1 - q^44) * (1 - q^45) *
      (1 - q^46) * (1 - q^47) * (1 - q^48) * (1 - q^49) * (1 - q^50) *
      (1 - q^51) * (1 - q^52) * (1 - q^53) * (1 - q^54) * (1 - q^55) *
      (1 - q^56) * (1 - q^57) * (1 - q^58))^24 := by
  rw [discriminantPolyPart, etaPolyPart_fiftyeight]

theorem etaPolyPart_fiftynine (q : R) :
    etaPolyPart q 59 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) *
      (1 - q^11) * (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) *
      (1 - q^16) * (1 - q^17) * (1 - q^18) * (1 - q^19) * (1 - q^20) *
      (1 - q^21) * (1 - q^22) * (1 - q^23) * (1 - q^24) * (1 - q^25) *
      (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) * (1 - q^30) *
      (1 - q^31) * (1 - q^32) * (1 - q^33) * (1 - q^34) * (1 - q^35) *
      (1 - q^36) * (1 - q^37) * (1 - q^38) * (1 - q^39) * (1 - q^40) *
      (1 - q^41) * (1 - q^42) * (1 - q^43) * (1 - q^44) * (1 - q^45) *
      (1 - q^46) * (1 - q^47) * (1 - q^48) * (1 - q^49) * (1 - q^50) *
      (1 - q^51) * (1 - q^52) * (1 - q^53) * (1 - q^54) * (1 - q^55) *
      (1 - q^56) * (1 - q^57) * (1 - q^58) * (1 - q^59) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_fiftynine (q : R) :
    discriminantPolyPart q 59 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) *
      (1 - q^11) * (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) *
      (1 - q^16) * (1 - q^17) * (1 - q^18) * (1 - q^19) * (1 - q^20) *
      (1 - q^21) * (1 - q^22) * (1 - q^23) * (1 - q^24) * (1 - q^25) *
      (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) * (1 - q^30) *
      (1 - q^31) * (1 - q^32) * (1 - q^33) * (1 - q^34) * (1 - q^35) *
      (1 - q^36) * (1 - q^37) * (1 - q^38) * (1 - q^39) * (1 - q^40) *
      (1 - q^41) * (1 - q^42) * (1 - q^43) * (1 - q^44) * (1 - q^45) *
      (1 - q^46) * (1 - q^47) * (1 - q^48) * (1 - q^49) * (1 - q^50) *
      (1 - q^51) * (1 - q^52) * (1 - q^53) * (1 - q^54) * (1 - q^55) *
      (1 - q^56) * (1 - q^57) * (1 - q^58) * (1 - q^59))^24 := by
  rw [discriminantPolyPart, etaPolyPart_fiftynine]

theorem etaPolyPart_sixty (q : R) :
    etaPolyPart q 60 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) *
      (1 - q^11) * (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) *
      (1 - q^16) * (1 - q^17) * (1 - q^18) * (1 - q^19) * (1 - q^20) *
      (1 - q^21) * (1 - q^22) * (1 - q^23) * (1 - q^24) * (1 - q^25) *
      (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) * (1 - q^30) *
      (1 - q^31) * (1 - q^32) * (1 - q^33) * (1 - q^34) * (1 - q^35) *
      (1 - q^36) * (1 - q^37) * (1 - q^38) * (1 - q^39) * (1 - q^40) *
      (1 - q^41) * (1 - q^42) * (1 - q^43) * (1 - q^44) * (1 - q^45) *
      (1 - q^46) * (1 - q^47) * (1 - q^48) * (1 - q^49) * (1 - q^50) *
      (1 - q^51) * (1 - q^52) * (1 - q^53) * (1 - q^54) * (1 - q^55) *
      (1 - q^56) * (1 - q^57) * (1 - q^58) * (1 - q^59) * (1 - q^60) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_sixty (q : R) :
    discriminantPolyPart q 60 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) *
      (1 - q^11) * (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) *
      (1 - q^16) * (1 - q^17) * (1 - q^18) * (1 - q^19) * (1 - q^20) *
      (1 - q^21) * (1 - q^22) * (1 - q^23) * (1 - q^24) * (1 - q^25) *
      (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) * (1 - q^30) *
      (1 - q^31) * (1 - q^32) * (1 - q^33) * (1 - q^34) * (1 - q^35) *
      (1 - q^36) * (1 - q^37) * (1 - q^38) * (1 - q^39) * (1 - q^40) *
      (1 - q^41) * (1 - q^42) * (1 - q^43) * (1 - q^44) * (1 - q^45) *
      (1 - q^46) * (1 - q^47) * (1 - q^48) * (1 - q^49) * (1 - q^50) *
      (1 - q^51) * (1 - q^52) * (1 - q^53) * (1 - q^54) * (1 - q^55) *
      (1 - q^56) * (1 - q^57) * (1 - q^58) * (1 - q^59) * (1 - q^60))^24 := by
  rw [discriminantPolyPart, etaPolyPart_sixty]

theorem etaPolyPart_sixtyone (q : R) :
    etaPolyPart q 61 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) *
      (1 - q^11) * (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) *
      (1 - q^16) * (1 - q^17) * (1 - q^18) * (1 - q^19) * (1 - q^20) *
      (1 - q^21) * (1 - q^22) * (1 - q^23) * (1 - q^24) * (1 - q^25) *
      (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) * (1 - q^30) *
      (1 - q^31) * (1 - q^32) * (1 - q^33) * (1 - q^34) * (1 - q^35) *
      (1 - q^36) * (1 - q^37) * (1 - q^38) * (1 - q^39) * (1 - q^40) *
      (1 - q^41) * (1 - q^42) * (1 - q^43) * (1 - q^44) * (1 - q^45) *
      (1 - q^46) * (1 - q^47) * (1 - q^48) * (1 - q^49) * (1 - q^50) *
      (1 - q^51) * (1 - q^52) * (1 - q^53) * (1 - q^54) * (1 - q^55) *
      (1 - q^56) * (1 - q^57) * (1 - q^58) * (1 - q^59) * (1 - q^60) *
      (1 - q^61) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_sixtyone (q : R) :
    discriminantPolyPart q 61 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) *
      (1 - q^11) * (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) *
      (1 - q^16) * (1 - q^17) * (1 - q^18) * (1 - q^19) * (1 - q^20) *
      (1 - q^21) * (1 - q^22) * (1 - q^23) * (1 - q^24) * (1 - q^25) *
      (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) * (1 - q^30) *
      (1 - q^31) * (1 - q^32) * (1 - q^33) * (1 - q^34) * (1 - q^35) *
      (1 - q^36) * (1 - q^37) * (1 - q^38) * (1 - q^39) * (1 - q^40) *
      (1 - q^41) * (1 - q^42) * (1 - q^43) * (1 - q^44) * (1 - q^45) *
      (1 - q^46) * (1 - q^47) * (1 - q^48) * (1 - q^49) * (1 - q^50) *
      (1 - q^51) * (1 - q^52) * (1 - q^53) * (1 - q^54) * (1 - q^55) *
      (1 - q^56) * (1 - q^57) * (1 - q^58) * (1 - q^59) * (1 - q^60) *
      (1 - q^61))^24 := by
  rw [discriminantPolyPart, etaPolyPart_sixtyone]

theorem etaPolyPart_sixtytwo (q : R) :
    etaPolyPart q 62 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) *
      (1 - q^11) * (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) *
      (1 - q^16) * (1 - q^17) * (1 - q^18) * (1 - q^19) * (1 - q^20) *
      (1 - q^21) * (1 - q^22) * (1 - q^23) * (1 - q^24) * (1 - q^25) *
      (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) * (1 - q^30) *
      (1 - q^31) * (1 - q^32) * (1 - q^33) * (1 - q^34) * (1 - q^35) *
      (1 - q^36) * (1 - q^37) * (1 - q^38) * (1 - q^39) * (1 - q^40) *
      (1 - q^41) * (1 - q^42) * (1 - q^43) * (1 - q^44) * (1 - q^45) *
      (1 - q^46) * (1 - q^47) * (1 - q^48) * (1 - q^49) * (1 - q^50) *
      (1 - q^51) * (1 - q^52) * (1 - q^53) * (1 - q^54) * (1 - q^55) *
      (1 - q^56) * (1 - q^57) * (1 - q^58) * (1 - q^59) * (1 - q^60) *
      (1 - q^61) * (1 - q^62) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_sixtytwo (q : R) :
    discriminantPolyPart q 62 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) *
      (1 - q^11) * (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) *
      (1 - q^16) * (1 - q^17) * (1 - q^18) * (1 - q^19) * (1 - q^20) *
      (1 - q^21) * (1 - q^22) * (1 - q^23) * (1 - q^24) * (1 - q^25) *
      (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) * (1 - q^30) *
      (1 - q^31) * (1 - q^32) * (1 - q^33) * (1 - q^34) * (1 - q^35) *
      (1 - q^36) * (1 - q^37) * (1 - q^38) * (1 - q^39) * (1 - q^40) *
      (1 - q^41) * (1 - q^42) * (1 - q^43) * (1 - q^44) * (1 - q^45) *
      (1 - q^46) * (1 - q^47) * (1 - q^48) * (1 - q^49) * (1 - q^50) *
      (1 - q^51) * (1 - q^52) * (1 - q^53) * (1 - q^54) * (1 - q^55) *
      (1 - q^56) * (1 - q^57) * (1 - q^58) * (1 - q^59) * (1 - q^60) *
      (1 - q^61) * (1 - q^62))^24 := by
  rw [discriminantPolyPart, etaPolyPart_sixtytwo]

theorem etaPolyPart_sixtythree (q : R) :
    etaPolyPart q 63 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) *
      (1 - q^11) * (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) *
      (1 - q^16) * (1 - q^17) * (1 - q^18) * (1 - q^19) * (1 - q^20) *
      (1 - q^21) * (1 - q^22) * (1 - q^23) * (1 - q^24) * (1 - q^25) *
      (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) * (1 - q^30) *
      (1 - q^31) * (1 - q^32) * (1 - q^33) * (1 - q^34) * (1 - q^35) *
      (1 - q^36) * (1 - q^37) * (1 - q^38) * (1 - q^39) * (1 - q^40) *
      (1 - q^41) * (1 - q^42) * (1 - q^43) * (1 - q^44) * (1 - q^45) *
      (1 - q^46) * (1 - q^47) * (1 - q^48) * (1 - q^49) * (1 - q^50) *
      (1 - q^51) * (1 - q^52) * (1 - q^53) * (1 - q^54) * (1 - q^55) *
      (1 - q^56) * (1 - q^57) * (1 - q^58) * (1 - q^59) * (1 - q^60) *
      (1 - q^61) * (1 - q^62) * (1 - q^63) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_sixtythree (q : R) :
    discriminantPolyPart q 63 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) *
      (1 - q^11) * (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) *
      (1 - q^16) * (1 - q^17) * (1 - q^18) * (1 - q^19) * (1 - q^20) *
      (1 - q^21) * (1 - q^22) * (1 - q^23) * (1 - q^24) * (1 - q^25) *
      (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) * (1 - q^30) *
      (1 - q^31) * (1 - q^32) * (1 - q^33) * (1 - q^34) * (1 - q^35) *
      (1 - q^36) * (1 - q^37) * (1 - q^38) * (1 - q^39) * (1 - q^40) *
      (1 - q^41) * (1 - q^42) * (1 - q^43) * (1 - q^44) * (1 - q^45) *
      (1 - q^46) * (1 - q^47) * (1 - q^48) * (1 - q^49) * (1 - q^50) *
      (1 - q^51) * (1 - q^52) * (1 - q^53) * (1 - q^54) * (1 - q^55) *
      (1 - q^56) * (1 - q^57) * (1 - q^58) * (1 - q^59) * (1 - q^60) *
      (1 - q^61) * (1 - q^62) * (1 - q^63))^24 := by
  rw [discriminantPolyPart, etaPolyPart_sixtythree]

theorem etaPolyPart_sixtyfour (q : R) :
    etaPolyPart q 64 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) *
      (1 - q^11) * (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) *
      (1 - q^16) * (1 - q^17) * (1 - q^18) * (1 - q^19) * (1 - q^20) *
      (1 - q^21) * (1 - q^22) * (1 - q^23) * (1 - q^24) * (1 - q^25) *
      (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) * (1 - q^30) *
      (1 - q^31) * (1 - q^32) * (1 - q^33) * (1 - q^34) * (1 - q^35) *
      (1 - q^36) * (1 - q^37) * (1 - q^38) * (1 - q^39) * (1 - q^40) *
      (1 - q^41) * (1 - q^42) * (1 - q^43) * (1 - q^44) * (1 - q^45) *
      (1 - q^46) * (1 - q^47) * (1 - q^48) * (1 - q^49) * (1 - q^50) *
      (1 - q^51) * (1 - q^52) * (1 - q^53) * (1 - q^54) * (1 - q^55) *
      (1 - q^56) * (1 - q^57) * (1 - q^58) * (1 - q^59) * (1 - q^60) *
      (1 - q^61) * (1 - q^62) * (1 - q^63) * (1 - q^64) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_sixtyfour (q : R) :
    discriminantPolyPart q 64 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) *
      (1 - q^11) * (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) *
      (1 - q^16) * (1 - q^17) * (1 - q^18) * (1 - q^19) * (1 - q^20) *
      (1 - q^21) * (1 - q^22) * (1 - q^23) * (1 - q^24) * (1 - q^25) *
      (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) * (1 - q^30) *
      (1 - q^31) * (1 - q^32) * (1 - q^33) * (1 - q^34) * (1 - q^35) *
      (1 - q^36) * (1 - q^37) * (1 - q^38) * (1 - q^39) * (1 - q^40) *
      (1 - q^41) * (1 - q^42) * (1 - q^43) * (1 - q^44) * (1 - q^45) *
      (1 - q^46) * (1 - q^47) * (1 - q^48) * (1 - q^49) * (1 - q^50) *
      (1 - q^51) * (1 - q^52) * (1 - q^53) * (1 - q^54) * (1 - q^55) *
      (1 - q^56) * (1 - q^57) * (1 - q^58) * (1 - q^59) * (1 - q^60) *
      (1 - q^61) * (1 - q^62) * (1 - q^63) * (1 - q^64))^24 := by
  rw [discriminantPolyPart, etaPolyPart_sixtyfour]

theorem etaPolyPart_sixtyfive (q : R) :
    etaPolyPart q 65 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) *
      (1 - q^11) * (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) *
      (1 - q^16) * (1 - q^17) * (1 - q^18) * (1 - q^19) * (1 - q^20) *
      (1 - q^21) * (1 - q^22) * (1 - q^23) * (1 - q^24) * (1 - q^25) *
      (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) * (1 - q^30) *
      (1 - q^31) * (1 - q^32) * (1 - q^33) * (1 - q^34) * (1 - q^35) *
      (1 - q^36) * (1 - q^37) * (1 - q^38) * (1 - q^39) * (1 - q^40) *
      (1 - q^41) * (1 - q^42) * (1 - q^43) * (1 - q^44) * (1 - q^45) *
      (1 - q^46) * (1 - q^47) * (1 - q^48) * (1 - q^49) * (1 - q^50) *
      (1 - q^51) * (1 - q^52) * (1 - q^53) * (1 - q^54) * (1 - q^55) *
      (1 - q^56) * (1 - q^57) * (1 - q^58) * (1 - q^59) * (1 - q^60) *
      (1 - q^61) * (1 - q^62) * (1 - q^63) * (1 - q^64) * (1 - q^65) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_sixtyfive (q : R) :
    discriminantPolyPart q 65 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) *
      (1 - q^11) * (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) *
      (1 - q^16) * (1 - q^17) * (1 - q^18) * (1 - q^19) * (1 - q^20) *
      (1 - q^21) * (1 - q^22) * (1 - q^23) * (1 - q^24) * (1 - q^25) *
      (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) * (1 - q^30) *
      (1 - q^31) * (1 - q^32) * (1 - q^33) * (1 - q^34) * (1 - q^35) *
      (1 - q^36) * (1 - q^37) * (1 - q^38) * (1 - q^39) * (1 - q^40) *
      (1 - q^41) * (1 - q^42) * (1 - q^43) * (1 - q^44) * (1 - q^45) *
      (1 - q^46) * (1 - q^47) * (1 - q^48) * (1 - q^49) * (1 - q^50) *
      (1 - q^51) * (1 - q^52) * (1 - q^53) * (1 - q^54) * (1 - q^55) *
      (1 - q^56) * (1 - q^57) * (1 - q^58) * (1 - q^59) * (1 - q^60) *
      (1 - q^61) * (1 - q^62) * (1 - q^63) * (1 - q^64) * (1 - q^65))^24 := by
  rw [discriminantPolyPart, etaPolyPart_sixtyfive]

theorem etaPolyPart_sixtysix (q : R) :
    etaPolyPart q 66 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) *
      (1 - q^11) * (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) *
      (1 - q^16) * (1 - q^17) * (1 - q^18) * (1 - q^19) * (1 - q^20) *
      (1 - q^21) * (1 - q^22) * (1 - q^23) * (1 - q^24) * (1 - q^25) *
      (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) * (1 - q^30) *
      (1 - q^31) * (1 - q^32) * (1 - q^33) * (1 - q^34) * (1 - q^35) *
      (1 - q^36) * (1 - q^37) * (1 - q^38) * (1 - q^39) * (1 - q^40) *
      (1 - q^41) * (1 - q^42) * (1 - q^43) * (1 - q^44) * (1 - q^45) *
      (1 - q^46) * (1 - q^47) * (1 - q^48) * (1 - q^49) * (1 - q^50) *
      (1 - q^51) * (1 - q^52) * (1 - q^53) * (1 - q^54) * (1 - q^55) *
      (1 - q^56) * (1 - q^57) * (1 - q^58) * (1 - q^59) * (1 - q^60) *
      (1 - q^61) * (1 - q^62) * (1 - q^63) * (1 - q^64) * (1 - q^65) *
      (1 - q^66) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_sixtysix (q : R) :
    discriminantPolyPart q 66 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) *
      (1 - q^11) * (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) *
      (1 - q^16) * (1 - q^17) * (1 - q^18) * (1 - q^19) * (1 - q^20) *
      (1 - q^21) * (1 - q^22) * (1 - q^23) * (1 - q^24) * (1 - q^25) *
      (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) * (1 - q^30) *
      (1 - q^31) * (1 - q^32) * (1 - q^33) * (1 - q^34) * (1 - q^35) *
      (1 - q^36) * (1 - q^37) * (1 - q^38) * (1 - q^39) * (1 - q^40) *
      (1 - q^41) * (1 - q^42) * (1 - q^43) * (1 - q^44) * (1 - q^45) *
      (1 - q^46) * (1 - q^47) * (1 - q^48) * (1 - q^49) * (1 - q^50) *
      (1 - q^51) * (1 - q^52) * (1 - q^53) * (1 - q^54) * (1 - q^55) *
      (1 - q^56) * (1 - q^57) * (1 - q^58) * (1 - q^59) * (1 - q^60) *
      (1 - q^61) * (1 - q^62) * (1 - q^63) * (1 - q^64) * (1 - q^65) *
      (1 - q^66))^24 := by
  rw [discriminantPolyPart, etaPolyPart_sixtysix]

theorem etaPolyPart_sixtyseven (q : R) :
    etaPolyPart q 67 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) *
      (1 - q^11) * (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) *
      (1 - q^16) * (1 - q^17) * (1 - q^18) * (1 - q^19) * (1 - q^20) *
      (1 - q^21) * (1 - q^22) * (1 - q^23) * (1 - q^24) * (1 - q^25) *
      (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) * (1 - q^30) *
      (1 - q^31) * (1 - q^32) * (1 - q^33) * (1 - q^34) * (1 - q^35) *
      (1 - q^36) * (1 - q^37) * (1 - q^38) * (1 - q^39) * (1 - q^40) *
      (1 - q^41) * (1 - q^42) * (1 - q^43) * (1 - q^44) * (1 - q^45) *
      (1 - q^46) * (1 - q^47) * (1 - q^48) * (1 - q^49) * (1 - q^50) *
      (1 - q^51) * (1 - q^52) * (1 - q^53) * (1 - q^54) * (1 - q^55) *
      (1 - q^56) * (1 - q^57) * (1 - q^58) * (1 - q^59) * (1 - q^60) *
      (1 - q^61) * (1 - q^62) * (1 - q^63) * (1 - q^64) * (1 - q^65) *
      (1 - q^66) * (1 - q^67) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_sixtyseven (q : R) :
    discriminantPolyPart q 67 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) *
      (1 - q^11) * (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) *
      (1 - q^16) * (1 - q^17) * (1 - q^18) * (1 - q^19) * (1 - q^20) *
      (1 - q^21) * (1 - q^22) * (1 - q^23) * (1 - q^24) * (1 - q^25) *
      (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) * (1 - q^30) *
      (1 - q^31) * (1 - q^32) * (1 - q^33) * (1 - q^34) * (1 - q^35) *
      (1 - q^36) * (1 - q^37) * (1 - q^38) * (1 - q^39) * (1 - q^40) *
      (1 - q^41) * (1 - q^42) * (1 - q^43) * (1 - q^44) * (1 - q^45) *
      (1 - q^46) * (1 - q^47) * (1 - q^48) * (1 - q^49) * (1 - q^50) *
      (1 - q^51) * (1 - q^52) * (1 - q^53) * (1 - q^54) * (1 - q^55) *
      (1 - q^56) * (1 - q^57) * (1 - q^58) * (1 - q^59) * (1 - q^60) *
      (1 - q^61) * (1 - q^62) * (1 - q^63) * (1 - q^64) * (1 - q^65) *
      (1 - q^66) * (1 - q^67))^24 := by
  rw [discriminantPolyPart, etaPolyPart_sixtyseven]

theorem etaPolyPart_sixtyeight (q : R) :
    etaPolyPart q 68 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) *
      (1 - q^11) * (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) *
      (1 - q^16) * (1 - q^17) * (1 - q^18) * (1 - q^19) * (1 - q^20) *
      (1 - q^21) * (1 - q^22) * (1 - q^23) * (1 - q^24) * (1 - q^25) *
      (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) * (1 - q^30) *
      (1 - q^31) * (1 - q^32) * (1 - q^33) * (1 - q^34) * (1 - q^35) *
      (1 - q^36) * (1 - q^37) * (1 - q^38) * (1 - q^39) * (1 - q^40) *
      (1 - q^41) * (1 - q^42) * (1 - q^43) * (1 - q^44) * (1 - q^45) *
      (1 - q^46) * (1 - q^47) * (1 - q^48) * (1 - q^49) * (1 - q^50) *
      (1 - q^51) * (1 - q^52) * (1 - q^53) * (1 - q^54) * (1 - q^55) *
      (1 - q^56) * (1 - q^57) * (1 - q^58) * (1 - q^59) * (1 - q^60) *
      (1 - q^61) * (1 - q^62) * (1 - q^63) * (1 - q^64) * (1 - q^65) *
      (1 - q^66) * (1 - q^67) * (1 - q^68) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_sixtyeight (q : R) :
    discriminantPolyPart q 68 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) *
      (1 - q^11) * (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) *
      (1 - q^16) * (1 - q^17) * (1 - q^18) * (1 - q^19) * (1 - q^20) *
      (1 - q^21) * (1 - q^22) * (1 - q^23) * (1 - q^24) * (1 - q^25) *
      (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) * (1 - q^30) *
      (1 - q^31) * (1 - q^32) * (1 - q^33) * (1 - q^34) * (1 - q^35) *
      (1 - q^36) * (1 - q^37) * (1 - q^38) * (1 - q^39) * (1 - q^40) *
      (1 - q^41) * (1 - q^42) * (1 - q^43) * (1 - q^44) * (1 - q^45) *
      (1 - q^46) * (1 - q^47) * (1 - q^48) * (1 - q^49) * (1 - q^50) *
      (1 - q^51) * (1 - q^52) * (1 - q^53) * (1 - q^54) * (1 - q^55) *
      (1 - q^56) * (1 - q^57) * (1 - q^58) * (1 - q^59) * (1 - q^60) *
      (1 - q^61) * (1 - q^62) * (1 - q^63) * (1 - q^64) * (1 - q^65) *
      (1 - q^66) * (1 - q^67) * (1 - q^68))^24 := by
  rw [discriminantPolyPart, etaPolyPart_sixtyeight]

theorem etaPolyPart_sixtynine (q : R) :
    etaPolyPart q 69 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) *
      (1 - q^11) * (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) *
      (1 - q^16) * (1 - q^17) * (1 - q^18) * (1 - q^19) * (1 - q^20) *
      (1 - q^21) * (1 - q^22) * (1 - q^23) * (1 - q^24) * (1 - q^25) *
      (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) * (1 - q^30) *
      (1 - q^31) * (1 - q^32) * (1 - q^33) * (1 - q^34) * (1 - q^35) *
      (1 - q^36) * (1 - q^37) * (1 - q^38) * (1 - q^39) * (1 - q^40) *
      (1 - q^41) * (1 - q^42) * (1 - q^43) * (1 - q^44) * (1 - q^45) *
      (1 - q^46) * (1 - q^47) * (1 - q^48) * (1 - q^49) * (1 - q^50) *
      (1 - q^51) * (1 - q^52) * (1 - q^53) * (1 - q^54) * (1 - q^55) *
      (1 - q^56) * (1 - q^57) * (1 - q^58) * (1 - q^59) * (1 - q^60) *
      (1 - q^61) * (1 - q^62) * (1 - q^63) * (1 - q^64) * (1 - q^65) *
      (1 - q^66) * (1 - q^67) * (1 - q^68) * (1 - q^69) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_sixtynine (q : R) :
    discriminantPolyPart q 69 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) *
      (1 - q^11) * (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) *
      (1 - q^16) * (1 - q^17) * (1 - q^18) * (1 - q^19) * (1 - q^20) *
      (1 - q^21) * (1 - q^22) * (1 - q^23) * (1 - q^24) * (1 - q^25) *
      (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) * (1 - q^30) *
      (1 - q^31) * (1 - q^32) * (1 - q^33) * (1 - q^34) * (1 - q^35) *
      (1 - q^36) * (1 - q^37) * (1 - q^38) * (1 - q^39) * (1 - q^40) *
      (1 - q^41) * (1 - q^42) * (1 - q^43) * (1 - q^44) * (1 - q^45) *
      (1 - q^46) * (1 - q^47) * (1 - q^48) * (1 - q^49) * (1 - q^50) *
      (1 - q^51) * (1 - q^52) * (1 - q^53) * (1 - q^54) * (1 - q^55) *
      (1 - q^56) * (1 - q^57) * (1 - q^58) * (1 - q^59) * (1 - q^60) *
      (1 - q^61) * (1 - q^62) * (1 - q^63) * (1 - q^64) * (1 - q^65) *
      (1 - q^66) * (1 - q^67) * (1 - q^68) * (1 - q^69))^24 := by
  rw [discriminantPolyPart, etaPolyPart_sixtynine]

theorem etaPolyPart_seventy (q : R) :
    etaPolyPart q 70 = (1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) *
      (1 - q^11) * (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) *
      (1 - q^16) * (1 - q^17) * (1 - q^18) * (1 - q^19) * (1 - q^20) *
      (1 - q^21) * (1 - q^22) * (1 - q^23) * (1 - q^24) * (1 - q^25) *
      (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) * (1 - q^30) *
      (1 - q^31) * (1 - q^32) * (1 - q^33) * (1 - q^34) * (1 - q^35) *
      (1 - q^36) * (1 - q^37) * (1 - q^38) * (1 - q^39) * (1 - q^40) *
      (1 - q^41) * (1 - q^42) * (1 - q^43) * (1 - q^44) * (1 - q^45) *
      (1 - q^46) * (1 - q^47) * (1 - q^48) * (1 - q^49) * (1 - q^50) *
      (1 - q^51) * (1 - q^52) * (1 - q^53) * (1 - q^54) * (1 - q^55) *
      (1 - q^56) * (1 - q^57) * (1 - q^58) * (1 - q^59) * (1 - q^60) *
      (1 - q^61) * (1 - q^62) * (1 - q^63) * (1 - q^64) * (1 - q^65) *
      (1 - q^66) * (1 - q^67) * (1 - q^68) * (1 - q^69) * (1 - q^70) := by
  simp [etaPolyPart, qPochhammer]

theorem discriminantPolyPart_seventy (q : R) :
    discriminantPolyPart q 70 = q * ((1 - q) * (1 - q^2) * (1 - q^3) * (1 - q^4) * (1 - q^5) *
      (1 - q^6) * (1 - q^7) * (1 - q^8) * (1 - q^9) * (1 - q^10) *
      (1 - q^11) * (1 - q^12) * (1 - q^13) * (1 - q^14) * (1 - q^15) *
      (1 - q^16) * (1 - q^17) * (1 - q^18) * (1 - q^19) * (1 - q^20) *
      (1 - q^21) * (1 - q^22) * (1 - q^23) * (1 - q^24) * (1 - q^25) *
      (1 - q^26) * (1 - q^27) * (1 - q^28) * (1 - q^29) * (1 - q^30) *
      (1 - q^31) * (1 - q^32) * (1 - q^33) * (1 - q^34) * (1 - q^35) *
      (1 - q^36) * (1 - q^37) * (1 - q^38) * (1 - q^39) * (1 - q^40) *
      (1 - q^41) * (1 - q^42) * (1 - q^43) * (1 - q^44) * (1 - q^45) *
      (1 - q^46) * (1 - q^47) * (1 - q^48) * (1 - q^49) * (1 - q^50) *
      (1 - q^51) * (1 - q^52) * (1 - q^53) * (1 - q^54) * (1 - q^55) *
      (1 - q^56) * (1 - q^57) * (1 - q^58) * (1 - q^59) * (1 - q^60) *
      (1 - q^61) * (1 - q^62) * (1 - q^63) * (1 - q^64) * (1 - q^65) *
      (1 - q^66) * (1 - q^67) * (1 - q^68) * (1 - q^69) * (1 - q^70))^24 := by
  rw [discriminantPolyPart, etaPolyPart_seventy]


end Field

section Complex

open Filter Topology

/-- The truncated η polynomial part converges to Euler's infinite product `(q;q)_∞`. -/
theorem tendsto_etaPolyPart (q : ℂ) (hq : ‖q‖ < 1) :
    Tendsto (fun N : ℕ => etaPolyPart q N) atTop
      (𝓝 (PartI.Ch04.eulerPentagonalInfiniteProduct q)) := by
  exact PartI.Ch04.tendsto_eulerPentagonalProductTrunc q hq

/-- The truncated discriminant polynomial part converges to `q · (q;q)_∞^24`. -/
theorem tendsto_discriminantPolyPart (q : ℂ) (hq : ‖q‖ < 1) :
    Tendsto (fun N : ℕ => discriminantPolyPart q N) atTop
      (𝓝 (q * (PartI.Ch04.eulerPentagonalInfiniteProduct q) ^ 24)) := by
  have h_eta := tendsto_etaPolyPart q hq
  have h_pow := h_eta.pow 24
  have h_const := h_pow.const_mul q
  refine h_const.congr ?_
  intro N
  simp [discriminantPolyPart]

end Complex

/-! ### Formal power series eta and discriminant

We lift Chan's η and Δ to formal power series over a commutative ring, using
the partition generating function infrastructure from Chapter 19. -/

section FormalPS

open PowerSeries QseriesFormalization.PartIV.Ch19
open QseriesFormalization.Pending.Ch15FormalDeriv

variable (R : Type*) [CommRing R]

/-- The Dedekind eta function as a formal power series over `R` (without the
`q^{1/24}` prefactor): `η_PS = (q;q)_∞ = ∏(1 - q^n)`. -/
noncomputable def etaPS : R⟦X⟧ := qPochInfPS R

/-- The modular discriminant as a formal power series: `Δ_PS = X · η_PS^24`. -/
noncomputable def discriminantPS : R⟦X⟧ := PowerSeries.X * (etaPS R) ^ 24

/-- The coefficient sequence of `Δ_PS` is the Ramanujan τ function. -/
noncomputable def ramanujanTau (n : Nat) : R := (discriminantPS R).coeff n

/-- η_PS times the partition generating function equals 1 (formal Euler identity
on power series, since 1/(q;q)∞ generates partitions). -/
theorem etaPS_mul_partitionGenFun :
    etaPS R * partitionGenFun R = 1 := by
  unfold etaPS qPochInfPS
  rw [mul_comm]
  exact partitionGenFun_mul_qPochInfPS R

/-- The constant term of η_PS is 1. -/
@[simp] theorem coeff_zero_etaPS : (etaPS R).coeff 0 = 1 := by
  unfold etaPS; exact coeff_zero_qPochInfPS R

/-- Δ_PS has zero constant term: `τ(0) = 0`. -/
@[simp] theorem ramanujanTau_zero : ramanujanTau R 0 = 0 := by
  unfold ramanujanTau discriminantPS
  rw [PowerSeries.coeff_zero_eq_constantCoeff, map_mul, PowerSeries.constantCoeff_X,
    zero_mul]

/-- The first nontrivial coefficient: `τ(1) = 1`. -/
theorem ramanujanTau_one : ramanujanTau R 1 = 1 := by
  unfold ramanujanTau discriminantPS
  rw [PowerSeries.coeff_succ_X_mul]
  -- ((etaPS R)^24).coeff 0 = (constantCoeff)((etaPS R))^24 = 1^24 = 1
  rw [PowerSeries.coeff_zero_eq_constantCoeff, map_pow,
    ← PowerSeries.coeff_zero_eq_constantCoeff, coeff_zero_etaPS, one_pow]

/-- Helper: when `f.coeff 0 = 1`, `(f^k).coeff 1 = k · f.coeff 1`. -/
theorem coeff_one_pow_of_constantCoeff_one
    (f : R⟦X⟧) (hf : f.coeff 0 = 1) (k : Nat) :
    (f ^ k).coeff 1 = (k : R) * f.coeff 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, PowerSeries.coeff_mul]
    rw [show (Finset.antidiagonal 1 : Finset (Nat × Nat)) = {(0, 1), (1, 0)} from rfl]
    rw [Finset.sum_insert (by simp), Finset.sum_singleton]
    have h_zero : (f ^ k).coeff 0 = 1 := by
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow,
          ← PowerSeries.coeff_zero_eq_constantCoeff_apply, hf, one_pow]
    rw [h_zero, ih, hf, mul_one]
    push_cast
    ring

/-- The second coefficient: `τ(2) = -24`. -/
theorem ramanujanTau_two : ramanujanTau R 2 = -24 := by
  unfold ramanujanTau discriminantPS
  -- (X · eta^24).coeff 2 = (eta^24).coeff 1
  rw [show (2 : Nat) = 1 + 1 from rfl]
  rw [PowerSeries.coeff_succ_X_mul]
  -- (eta^24).coeff 1 = 24 · eta.coeff 1
  rw [coeff_one_pow_of_constantCoeff_one R (etaPS R) (coeff_zero_etaPS R) 24]
  rw [show (etaPS R).coeff 1 = -1 from coeff_one_qPochInfPS R]
  push_cast
  ring

/-- Helper: when `f.coeff 0 = 1`,
`(f^k).coeff 2 = k · f.coeff 2 + (k.choose 2) · (f.coeff 1)^2`. -/
theorem coeff_two_pow_of_constantCoeff_one
    (f : R⟦X⟧) (hf : f.coeff 0 = 1) (k : Nat) :
    (f ^ k).coeff 2 = (k : R) * f.coeff 2 + (k.choose 2 : R) * (f.coeff 1) ^ 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, PowerSeries.coeff_mul]
    rw [show (Finset.antidiagonal 2 : Finset (Nat × Nat)) = {(0, 2), (1, 1), (2, 0)} from rfl]
    rw [Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_singleton]
    have h_zero : (f ^ k).coeff 0 = 1 := by
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow,
          ← PowerSeries.coeff_zero_eq_constantCoeff_apply, hf, one_pow]
    have h_one : (f ^ k).coeff 1 = (k : R) * f.coeff 1 :=
      coeff_one_pow_of_constantCoeff_one R f hf k
    rw [h_zero, h_one, ih, hf]
    have h_succ_choose : ((k + 1).choose 2 : R) = (k.choose 2 : R) + k := by
      rw [Nat.choose_succ_succ k 1, Nat.choose_one_right]; push_cast; ring
    rw [h_succ_choose]
    push_cast
    ring

/-- The third coefficient: `τ(3) = 252`. -/
theorem ramanujanTau_three : ramanujanTau R 3 = 252 := by
  unfold ramanujanTau discriminantPS
  rw [show (3 : Nat) = 2 + 1 from rfl]
  rw [PowerSeries.coeff_succ_X_mul]
  -- (eta^24).coeff 2 = 24 · eta.coeff 2 + C(24,2) · (eta.coeff 1)^2
  --                  = 24 · (-1) + 276 · 1 = 252
  rw [coeff_two_pow_of_constantCoeff_one R (etaPS R) (coeff_zero_etaPS R) 24]
  rw [show (etaPS R).coeff 1 = -1 from coeff_one_qPochInfPS R]
  rw [show (etaPS R).coeff 2 = -1 from coeff_two_qPochInfPS R]
  show (24 : R) * (-1) + ((24).choose 2 : R) * (-1 : R) ^ 2 = 252
  rw [show ((24 : Nat).choose 2 : R) = 276 from by norm_num [Nat.choose]]
  ring

/-- Helper: when `f.coeff 0 = 1`,
`(f^k).coeff 3 = k·f.coeff 3 + 2·C(k,2)·f.coeff 2·f.coeff 1 + C(k,3)·(f.coeff 1)^3`. -/
theorem coeff_three_pow_of_constantCoeff_one
    (f : R⟦X⟧) (hf : f.coeff 0 = 1) (k : Nat) :
    (f ^ k).coeff 3 = (k : R) * f.coeff 3
      + 2 * (k.choose 2 : R) * f.coeff 2 * f.coeff 1
      + (k.choose 3 : R) * (f.coeff 1) ^ 3 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, PowerSeries.coeff_mul]
    rw [show (Finset.antidiagonal 3 : Finset (Nat × Nat)) = {(0, 3), (1, 2), (2, 1), (3, 0)} from rfl]
    rw [Finset.sum_insert (by simp), Finset.sum_insert (by simp),
        Finset.sum_insert (by simp), Finset.sum_singleton]
    have h_zero : (f ^ k).coeff 0 = 1 := by
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow,
          ← PowerSeries.coeff_zero_eq_constantCoeff_apply, hf, one_pow]
    have h_one : (f ^ k).coeff 1 = (k : R) * f.coeff 1 :=
      coeff_one_pow_of_constantCoeff_one R f hf k
    have h_two : (f ^ k).coeff 2 =
        (k : R) * f.coeff 2 + (k.choose 2 : R) * (f.coeff 1) ^ 2 :=
      coeff_two_pow_of_constantCoeff_one R f hf k
    rw [h_zero, h_one, h_two, ih, hf]
    -- Pascal: C(k+1,2) = C(k,2) + k, C(k+1,3) = C(k,3) + C(k,2)
    have hC2 : ((k + 1).choose 2 : R) = (k.choose 2 : R) + k := by
      rw [Nat.choose_succ_succ k 1, Nat.choose_one_right]; push_cast; ring
    have hC3 : ((k + 1).choose 3 : R) = (k.choose 3 : R) + (k.choose 2 : R) := by
      rw [Nat.choose_succ_succ]; push_cast; ring
    rw [hC2, hC3]
    push_cast
    ring

/-- Helper: when `f.coeff 0 = 1`,
`(f^k).coeff 4 = k·f.coeff 4 + 2·C(k,2)·f.coeff 3·f.coeff 1 + 3·C(k,3)·f.coeff 2·(f.coeff 1)^2
              + C(k,2)·(f.coeff 2)^2 + C(k,4)·(f.coeff 1)^4`. -/
theorem coeff_four_pow_of_constantCoeff_one
    (f : R⟦X⟧) (hf : f.coeff 0 = 1) (k : Nat) :
    (f ^ k).coeff 4 = (k : R) * f.coeff 4
      + 2 * (k.choose 2 : R) * f.coeff 3 * f.coeff 1
      + 3 * (k.choose 3 : R) * f.coeff 2 * (f.coeff 1) ^ 2
      + (k.choose 2 : R) * (f.coeff 2) ^ 2
      + (k.choose 4 : R) * (f.coeff 1) ^ 4 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, PowerSeries.coeff_mul]
    rw [show (Finset.antidiagonal 4 : Finset (Nat × Nat))
      = {(0, 4), (1, 3), (2, 2), (3, 1), (4, 0)} from rfl]
    rw [Finset.sum_insert (by simp), Finset.sum_insert (by simp),
        Finset.sum_insert (by simp), Finset.sum_insert (by simp),
        Finset.sum_singleton]
    have h_zero : (f ^ k).coeff 0 = 1 := by
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow,
          ← PowerSeries.coeff_zero_eq_constantCoeff_apply, hf, one_pow]
    have h_one : (f ^ k).coeff 1 = (k : R) * f.coeff 1 :=
      coeff_one_pow_of_constantCoeff_one R f hf k
    have h_two : (f ^ k).coeff 2 =
        (k : R) * f.coeff 2 + (k.choose 2 : R) * (f.coeff 1) ^ 2 :=
      coeff_two_pow_of_constantCoeff_one R f hf k
    have h_three : (f ^ k).coeff 3 = (k : R) * f.coeff 3
        + 2 * (k.choose 2 : R) * f.coeff 2 * f.coeff 1
        + (k.choose 3 : R) * (f.coeff 1) ^ 3 :=
      coeff_three_pow_of_constantCoeff_one R f hf k
    rw [h_zero, h_one, h_two, h_three, ih, hf]
    -- Pascal-like identities:
    have hC2 : ((k + 1).choose 2 : R) = (k.choose 2 : R) + k := by
      rw [Nat.choose_succ_succ k 1, Nat.choose_one_right]; push_cast; ring
    have hC3 : ((k + 1).choose 3 : R) = (k.choose 3 : R) + (k.choose 2 : R) := by
      rw [Nat.choose_succ_succ]; push_cast; ring
    have hC4 : ((k + 1).choose 4 : R) = (k.choose 4 : R) + (k.choose 3 : R) := by
      rw [Nat.choose_succ_succ]; push_cast; ring
    rw [hC2, hC3, hC4]
    push_cast
    ring

/-- The fourth coefficient: `τ(4) = -1472`. -/
theorem ramanujanTau_four : ramanujanTau R 4 = -1472 := by
  unfold ramanujanTau discriminantPS
  rw [show (4 : Nat) = 3 + 1 from rfl]
  rw [PowerSeries.coeff_succ_X_mul]
  -- (eta^24).coeff 3 = 24·0 + 2·C(24,2)·(-1)·(-1) + C(24,3)·(-1)
  --                 = 0 + 2·276 - 2024 = 552 - 2024 = -1472
  rw [coeff_three_pow_of_constantCoeff_one R (etaPS R) (coeff_zero_etaPS R) 24]
  rw [show (etaPS R).coeff 1 = -1 from coeff_one_qPochInfPS R]
  rw [show (etaPS R).coeff 2 = -1 from coeff_two_qPochInfPS R]
  rw [show (etaPS R).coeff 3 = 0 from coeff_three_qPochInfPS R]
  show (24 : R) * 0 + 2 * ((24 : Nat).choose 2 : R) * (-1) * (-1)
      + ((24 : Nat).choose 3 : R) * (-1 : R) ^ 3 = -1472
  rw [show ((24 : Nat).choose 2 : R) = 276 from by norm_num [Nat.choose],
      show ((24 : Nat).choose 3 : R) = 2024 from by norm_num [Nat.choose]]
  ring

/-- Helper: when `f.coeff 0 = 1`,
`(f^k).coeff 5 = k·f.coeff 5 + 2·C(k,2)·f.coeff 4·f.coeff 1 + 2·C(k,2)·f.coeff 3·f.coeff 2
              + 3·C(k,3)·f.coeff 3·(f.coeff 1)^2 + 3·C(k,3)·(f.coeff 2)^2·f.coeff 1
              + 4·C(k,4)·f.coeff 2·(f.coeff 1)^3 + C(k,5)·(f.coeff 1)^5`. -/
theorem coeff_five_pow_of_constantCoeff_one
    (f : R⟦X⟧) (hf : f.coeff 0 = 1) (k : Nat) :
    (f ^ k).coeff 5 = (k : R) * f.coeff 5
      + 2 * (k.choose 2 : R) * f.coeff 4 * f.coeff 1
      + 2 * (k.choose 2 : R) * f.coeff 3 * f.coeff 2
      + 3 * (k.choose 3 : R) * f.coeff 3 * (f.coeff 1) ^ 2
      + 3 * (k.choose 3 : R) * (f.coeff 2) ^ 2 * f.coeff 1
      + 4 * (k.choose 4 : R) * f.coeff 2 * (f.coeff 1) ^ 3
      + (k.choose 5 : R) * (f.coeff 1) ^ 5 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, PowerSeries.coeff_mul]
    rw [show (Finset.antidiagonal 5 : Finset (Nat × Nat))
      = {(0, 5), (1, 4), (2, 3), (3, 2), (4, 1), (5, 0)} from rfl]
    rw [Finset.sum_insert (by simp), Finset.sum_insert (by simp),
        Finset.sum_insert (by simp), Finset.sum_insert (by simp),
        Finset.sum_insert (by simp), Finset.sum_singleton]
    have h_zero : (f ^ k).coeff 0 = 1 := by
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow,
          ← PowerSeries.coeff_zero_eq_constantCoeff_apply, hf, one_pow]
    have h_one : (f ^ k).coeff 1 = (k : R) * f.coeff 1 :=
      coeff_one_pow_of_constantCoeff_one R f hf k
    have h_two : (f ^ k).coeff 2 =
        (k : R) * f.coeff 2 + (k.choose 2 : R) * (f.coeff 1) ^ 2 :=
      coeff_two_pow_of_constantCoeff_one R f hf k
    have h_three : (f ^ k).coeff 3 = (k : R) * f.coeff 3
        + 2 * (k.choose 2 : R) * f.coeff 2 * f.coeff 1
        + (k.choose 3 : R) * (f.coeff 1) ^ 3 :=
      coeff_three_pow_of_constantCoeff_one R f hf k
    have h_four : (f ^ k).coeff 4 = (k : R) * f.coeff 4
        + 2 * (k.choose 2 : R) * f.coeff 3 * f.coeff 1
        + 3 * (k.choose 3 : R) * f.coeff 2 * (f.coeff 1) ^ 2
        + (k.choose 2 : R) * (f.coeff 2) ^ 2
        + (k.choose 4 : R) * (f.coeff 1) ^ 4 :=
      coeff_four_pow_of_constantCoeff_one R f hf k
    rw [h_zero, h_one, h_two, h_three, h_four, ih, hf]
    have hC2 : ((k + 1).choose 2 : R) = (k.choose 2 : R) + k := by
      rw [Nat.choose_succ_succ k 1, Nat.choose_one_right]; push_cast; ring
    have hC3 : ((k + 1).choose 3 : R) = (k.choose 3 : R) + (k.choose 2 : R) := by
      rw [Nat.choose_succ_succ]; push_cast; ring
    have hC4 : ((k + 1).choose 4 : R) = (k.choose 4 : R) + (k.choose 3 : R) := by
      rw [Nat.choose_succ_succ]; push_cast; ring
    have hC5 : ((k + 1).choose 5 : R) = (k.choose 5 : R) + (k.choose 4 : R) := by
      rw [Nat.choose_succ_succ]; push_cast; ring
    rw [hC2, hC3, hC4, hC5]
    push_cast
    ring

/-- The fifth coefficient: `τ(5) = 4830`. -/
theorem ramanujanTau_five : ramanujanTau R 5 = 4830 := by
  unfold ramanujanTau discriminantPS
  rw [show (5 : Nat) = 4 + 1 from rfl]
  rw [PowerSeries.coeff_succ_X_mul]
  -- (eta^24).coeff 4 = 24·0 + 2·C(24,2)·0·(-1) + 3·C(24,3)·(-1)·1 + C(24,2)·1 + C(24,4)·1
  --                 = 0 + 0 + 3·2024·(-1) + 276 + 10626
  --                 = -6072 + 276 + 10626 = 4830
  rw [coeff_four_pow_of_constantCoeff_one R (etaPS R) (coeff_zero_etaPS R) 24]
  rw [show (etaPS R).coeff 1 = -1 from coeff_one_qPochInfPS R]
  rw [show (etaPS R).coeff 2 = -1 from coeff_two_qPochInfPS R]
  rw [show (etaPS R).coeff 3 = 0 from coeff_three_qPochInfPS R]
  rw [show (etaPS R).coeff 4 = 0 from coeff_four_qPochInfPS R]
  show (24 : R) * 0 + 2 * ((24 : Nat).choose 2 : R) * 0 * (-1)
      + 3 * ((24 : Nat).choose 3 : R) * (-1) * (-1 : R) ^ 2
      + ((24 : Nat).choose 2 : R) * (-1 : R) ^ 2
      + ((24 : Nat).choose 4 : R) * (-1 : R) ^ 4 = 4830
  rw [show ((24 : Nat).choose 2 : R) = 276 from by norm_num [Nat.choose],
      show ((24 : Nat).choose 3 : R) = 2024 from by norm_num [Nat.choose],
      show ((24 : Nat).choose 4 : R) = 10626 from by norm_num [Nat.choose]]
  ring

/-- The sixth coefficient: `τ(6) = -6048`.
**Multiplicativity check**: τ(6) = τ(2) · τ(3) = (-24) · 252 = -6048 (Ramanujan's τ is
multiplicative on coprime arguments; this is the first nontrivial check at the pair (2,3)). -/
theorem ramanujanTau_six : ramanujanTau R 6 = -6048 := by
  unfold ramanujanTau discriminantPS
  rw [show (6 : Nat) = 5 + 1 from rfl]
  rw [PowerSeries.coeff_succ_X_mul]
  -- (eta^24).coeff 5 = 24·1 + 2·C(24,2)·0·(-1) + 2·C(24,2)·0·(-1)
  --                + 3·C(24,3)·0·1 + 3·C(24,3)·1·(-1) + 4·C(24,4)·(-1)·(-1)³ + C(24,5)·(-1)^5
  --   = 24 + 0 + 0 + 0 + 3·2024·(-1) + 4·10626·1 + 42504·(-1)
  --   = 24 - 6072 + 42504 - 42504 = -6048
  rw [coeff_five_pow_of_constantCoeff_one R (etaPS R) (coeff_zero_etaPS R) 24]
  rw [show (etaPS R).coeff 1 = -1 from coeff_one_qPochInfPS R]
  rw [show (etaPS R).coeff 2 = -1 from coeff_two_qPochInfPS R]
  rw [show (etaPS R).coeff 3 = 0 from coeff_three_qPochInfPS R]
  rw [show (etaPS R).coeff 4 = 0 from coeff_four_qPochInfPS R]
  rw [show (etaPS R).coeff 5 = 1 from coeff_five_qPochInfPS R]
  show (24 : R) * 1 + 2 * ((24 : Nat).choose 2 : R) * 0 * (-1)
      + 2 * ((24 : Nat).choose 2 : R) * 0 * (-1)
      + 3 * ((24 : Nat).choose 3 : R) * 0 * (-1 : R) ^ 2
      + 3 * ((24 : Nat).choose 3 : R) * (-1 : R) ^ 2 * (-1)
      + 4 * ((24 : Nat).choose 4 : R) * (-1) * (-1 : R) ^ 3
      + ((24 : Nat).choose 5 : R) * (-1 : R) ^ 5 = -6048
  rw [show ((24 : Nat).choose 2 : R) = 276 from by norm_num [Nat.choose],
      show ((24 : Nat).choose 3 : R) = 2024 from by norm_num [Nat.choose],
      show ((24 : Nat).choose 4 : R) = 10626 from by norm_num [Nat.choose],
      show ((24 : Nat).choose 5 : R) = 42504 from by norm_num [Nat.choose]]
  ring

/-- **Ramanujan τ multiplicativity at (2, 3)**: τ(6) = τ(2) · τ(3).
This is the first nontrivial instance of the multiplicative property of the Ramanujan
τ function (Mordell 1917): for coprime m, n, τ(mn) = τ(m)·τ(n). -/
theorem ramanujanTau_mul_two_three :
    (ramanujanTau R 6 : R) = ramanujanTau R 2 * ramanujanTau R 3 := by
  rw [ramanujanTau_six, ramanujanTau_two, ramanujanTau_three]
  ring

/-- **Ramanujan τ Hecke relation at p=2, a=1**: `τ(4) = τ(2)² - 2¹¹ · τ(1)`.
This is the prime-power Hecke recursion `τ(p^{a+1}) = τ(p)·τ(p^a) - p¹¹·τ(p^{a-1})`. -/
theorem ramanujanTau_hecke_two_one :
    (ramanujanTau R 4 : R) = ramanujanTau R 2 * ramanujanTau R 2 - 2048 * ramanujanTau R 1 := by
  rw [ramanujanTau_four, ramanujanTau_two, ramanujanTau_one]
  ring



/-- η_PS is a unit in `R⟦X⟧`. -/
theorem etaPS_isUnit : IsUnit (etaPS R) := by
  rw [PowerSeries.isUnit_iff_constantCoeff,
    ← PowerSeries.coeff_zero_eq_constantCoeff, coeff_zero_etaPS]
  exact isUnit_one

-- B2 small case verifications removed (they don't help the general proof).
-- General B2 target: (qPochInfPS R)^3 = jacobiThetaPS R requires Sylvester
-- combinatorial or analytic-formal bridge.

/-! ### Unconditional Ramanujan congruence: p(4) ≡ 0 (mod 5)

Closing the n=0 case of Ramanujan p(5n+4) ≡ 0 (mod 5) using the formal-PS
framework: compute `((q;q)∞^4).coeff 4` directly via the coeff_four_pow helper
and the Euler-pentagonal coefficient values, then bridge to `partitionCount 4`
via `coeff_pochInfPow_eq_partitionCount_of_lt`. -/

/-- Compute `((qPochInfPS R)^4).coeff 4 = -5` in any commutative ring `R`.
This is a direct application of the binomial coefficient formula with the
Euler-pentagonal values `f.coeff 0..4 = 1, -1, -1, 0, 0`. -/
theorem coeff_four_qPochInf_pow_four :
    ((QseriesFormalization.PartIV.Ch19.qPochInfPS R) ^ 4).coeff 4 = -5 := by
  rw [coeff_four_pow_of_constantCoeff_one R
        (QseriesFormalization.PartIV.Ch19.qPochInfPS R)
        (QseriesFormalization.PartIV.Ch19.coeff_zero_qPochInfPS R) 4]
  rw [QseriesFormalization.PartIV.Ch19.coeff_one_qPochInfPS,
      QseriesFormalization.PartIV.Ch19.coeff_two_qPochInfPS,
      QseriesFormalization.PartIV.Ch19.coeff_three_qPochInfPS,
      QseriesFormalization.PartIV.Ch19.coeff_four_qPochInfPS]
  show (4 : R) * 0 + 2 * ((4 : Nat).choose 2 : R) * 0 * (-1)
      + 3 * ((4 : Nat).choose 3 : R) * (-1) * (-1 : R) ^ 2
      + ((4 : Nat).choose 2 : R) * (-1 : R) ^ 2
      + ((4 : Nat).choose 4 : R) * (-1 : R) ^ 4 = -5
  rw [show ((4 : Nat).choose 2 : R) = 6 from by norm_num [Nat.choose],
      show ((4 : Nat).choose 3 : R) = 4 from by norm_num [Nat.choose],
      show ((4 : Nat).choose 4 : R) = 1 from by norm_num [Nat.choose]]
  ring

/-- **Ramanujan p(4) ≡ 0 (mod 5)** — unconditional, via formal power series.

This closes the n=0 case of `p(5n+4) ≡ 0 (mod 5)` without using the (still open)
infinite-vanishing hypothesis. The proof bridges Ch19's algebraic framework
to a direct binomial computation of `((q;q)_∞^4).coeff 4 = -5 ≡ 0 (mod 5)`. -/
theorem ramanujan_partition_four_mod_five :
    ((QseriesFormalization.Ch01.partitionCount 4 : Nat) : ZMod 5) = 0 := by
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hp : (5 : Nat) ≠ 0 := by decide
  have hr : 4 < (5 : Nat) := by decide
  have h := QseriesFormalization.PartIV.Ch19.coeff_pochInfPow_eq_partitionCount_of_lt
    5 hp 4 hr
  simp only [show (5 - 1 : Nat) = 4 from rfl] at h
  rw [← h, coeff_four_qPochInf_pow_four]
  decide

/-- Compute `((qPochInfPS R)^6).coeff 5 = 0` in any commutative ring `R`.
With Euler-pentagonal `f.coeff 0..5 = 1, -1, -1, 0, 0, 1`:
6·1 + 0 + 0 + 0 - 60 + 60 - 6 = 0 (vanishes identically in `R`, not just mod 7). -/
theorem coeff_five_qPochInf_pow_six :
    ((QseriesFormalization.PartIV.Ch19.qPochInfPS R) ^ 6).coeff 5 = 0 := by
  rw [coeff_five_pow_of_constantCoeff_one R
        (QseriesFormalization.PartIV.Ch19.qPochInfPS R)
        (QseriesFormalization.PartIV.Ch19.coeff_zero_qPochInfPS R) 6]
  rw [QseriesFormalization.PartIV.Ch19.coeff_one_qPochInfPS,
      QseriesFormalization.PartIV.Ch19.coeff_two_qPochInfPS,
      QseriesFormalization.PartIV.Ch19.coeff_three_qPochInfPS,
      QseriesFormalization.PartIV.Ch19.coeff_four_qPochInfPS,
      QseriesFormalization.PartIV.Ch19.coeff_five_qPochInfPS]
  show (6 : R) * 1 + 2 * ((6 : Nat).choose 2 : R) * 0 * (-1)
      + 2 * ((6 : Nat).choose 2 : R) * 0 * (-1)
      + 3 * ((6 : Nat).choose 3 : R) * 0 * (-1 : R) ^ 2
      + 3 * ((6 : Nat).choose 3 : R) * (-1 : R) ^ 2 * (-1)
      + 4 * ((6 : Nat).choose 4 : R) * (-1) * (-1 : R) ^ 3
      + ((6 : Nat).choose 5 : R) * (-1 : R) ^ 5 = 0
  rw [show ((6 : Nat).choose 2 : R) = 15 from by norm_num [Nat.choose],
      show ((6 : Nat).choose 3 : R) = 20 from by norm_num [Nat.choose],
      show ((6 : Nat).choose 4 : R) = 15 from by norm_num [Nat.choose],
      show ((6 : Nat).choose 5 : R) = 6 from by norm_num [Nat.choose]]
  ring

/-- **Ramanujan p(5) ≡ 0 (mod 7)** — unconditional, via formal power series.
The n=0 case of `p(7n+5) ≡ 0 (mod 7)`. -/
theorem ramanujan_partition_five_mod_seven :
    ((QseriesFormalization.Ch01.partitionCount 5 : Nat) : ZMod 7) = 0 := by
  haveI : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hp : (7 : Nat) ≠ 0 := by decide
  have hr : 5 < (7 : Nat) := by decide
  have h := QseriesFormalization.PartIV.Ch19.coeff_pochInfPow_eq_partitionCount_of_lt
    7 hp 5 hr
  simp only [show (7 - 1 : Nat) = 6 from rfl] at h
  rw [← h, coeff_five_qPochInf_pow_six]

/-- Helper: `(f^k).coeff 6` for `f.coeff 0 = 1`, with all 11 shapes of 6
(6; 5+1; 4+2; 3+3; 4+1+1; 3+2+1; 2+2+2; 3+1+1+1; 2+2+1+1; 2+1+1+1+1; 1+1+1+1+1+1). -/
theorem coeff_six_pow_of_constantCoeff_one
    (f : R⟦X⟧) (hf : f.coeff 0 = 1) (k : Nat) :
    (f ^ k).coeff 6 = (k : R) * f.coeff 6
      + 2 * (k.choose 2 : R) * f.coeff 5 * f.coeff 1
      + 2 * (k.choose 2 : R) * f.coeff 4 * f.coeff 2
      + (k.choose 2 : R) * (f.coeff 3) ^ 2
      + 3 * (k.choose 3 : R) * f.coeff 4 * (f.coeff 1) ^ 2
      + 6 * (k.choose 3 : R) * f.coeff 3 * f.coeff 2 * f.coeff 1
      + (k.choose 3 : R) * (f.coeff 2) ^ 3
      + 4 * (k.choose 4 : R) * f.coeff 3 * (f.coeff 1) ^ 3
      + 6 * (k.choose 4 : R) * (f.coeff 2) ^ 2 * (f.coeff 1) ^ 2
      + 5 * (k.choose 5 : R) * f.coeff 2 * (f.coeff 1) ^ 4
      + (k.choose 6 : R) * (f.coeff 1) ^ 6 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, PowerSeries.coeff_mul]
    rw [show (Finset.antidiagonal 6 : Finset (Nat × Nat))
      = {(0, 6), (1, 5), (2, 4), (3, 3), (4, 2), (5, 1), (6, 0)} from rfl]
    rw [Finset.sum_insert (by simp), Finset.sum_insert (by simp),
        Finset.sum_insert (by simp), Finset.sum_insert (by simp),
        Finset.sum_insert (by simp), Finset.sum_insert (by simp),
        Finset.sum_singleton]
    have h_zero : (f ^ k).coeff 0 = 1 := by
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow,
          ← PowerSeries.coeff_zero_eq_constantCoeff_apply, hf, one_pow]
    have h_one : (f ^ k).coeff 1 = (k : R) * f.coeff 1 :=
      coeff_one_pow_of_constantCoeff_one R f hf k
    have h_two : (f ^ k).coeff 2 =
        (k : R) * f.coeff 2 + (k.choose 2 : R) * (f.coeff 1) ^ 2 :=
      coeff_two_pow_of_constantCoeff_one R f hf k
    have h_three : (f ^ k).coeff 3 = (k : R) * f.coeff 3
        + 2 * (k.choose 2 : R) * f.coeff 2 * f.coeff 1
        + (k.choose 3 : R) * (f.coeff 1) ^ 3 :=
      coeff_three_pow_of_constantCoeff_one R f hf k
    have h_four : (f ^ k).coeff 4 = (k : R) * f.coeff 4
        + 2 * (k.choose 2 : R) * f.coeff 3 * f.coeff 1
        + 3 * (k.choose 3 : R) * f.coeff 2 * (f.coeff 1) ^ 2
        + (k.choose 2 : R) * (f.coeff 2) ^ 2
        + (k.choose 4 : R) * (f.coeff 1) ^ 4 :=
      coeff_four_pow_of_constantCoeff_one R f hf k
    have h_five : (f ^ k).coeff 5 = (k : R) * f.coeff 5
        + 2 * (k.choose 2 : R) * f.coeff 4 * f.coeff 1
        + 2 * (k.choose 2 : R) * f.coeff 3 * f.coeff 2
        + 3 * (k.choose 3 : R) * f.coeff 3 * (f.coeff 1) ^ 2
        + 3 * (k.choose 3 : R) * (f.coeff 2) ^ 2 * f.coeff 1
        + 4 * (k.choose 4 : R) * f.coeff 2 * (f.coeff 1) ^ 3
        + (k.choose 5 : R) * (f.coeff 1) ^ 5 :=
      coeff_five_pow_of_constantCoeff_one R f hf k
    rw [h_zero, h_one, h_two, h_three, h_four, h_five, ih, hf]
    have hC2 : ((k + 1).choose 2 : R) = (k.choose 2 : R) + k := by
      rw [Nat.choose_succ_succ k 1, Nat.choose_one_right]; push_cast; ring
    have hC3 : ((k + 1).choose 3 : R) = (k.choose 3 : R) + (k.choose 2 : R) := by
      rw [Nat.choose_succ_succ]; push_cast; ring
    have hC4 : ((k + 1).choose 4 : R) = (k.choose 4 : R) + (k.choose 3 : R) := by
      rw [Nat.choose_succ_succ]; push_cast; ring
    have hC5 : ((k + 1).choose 5 : R) = (k.choose 5 : R) + (k.choose 4 : R) := by
      rw [Nat.choose_succ_succ]; push_cast; ring
    have hC6 : ((k + 1).choose 6 : R) = (k.choose 6 : R) + (k.choose 5 : R) := by
      rw [Nat.choose_succ_succ]; push_cast; ring
    rw [hC2, hC3, hC4, hC5, hC6]
    push_cast
    ring

/-- Compute `((qPochInfPS R)^10).coeff 6 = 0` in any commutative ring `R`.
With Euler-pentagonal `f.coeff 0..6 = 1, -1, -1, 0, 0, 1, 0` and k=10:
the 11-shape expansion gives `0 - 90 + 0 + 0 + 0 + 0 - 120 + 0 + 1260 - 1260 + 210 = 0`. -/
theorem coeff_six_qPochInf_pow_ten :
    ((QseriesFormalization.PartIV.Ch19.qPochInfPS R) ^ 10).coeff 6 = 0 := by
  rw [coeff_six_pow_of_constantCoeff_one R
        (QseriesFormalization.PartIV.Ch19.qPochInfPS R)
        (QseriesFormalization.PartIV.Ch19.coeff_zero_qPochInfPS R) 10]
  rw [QseriesFormalization.PartIV.Ch19.coeff_one_qPochInfPS,
      QseriesFormalization.PartIV.Ch19.coeff_two_qPochInfPS,
      QseriesFormalization.PartIV.Ch19.coeff_three_qPochInfPS,
      QseriesFormalization.PartIV.Ch19.coeff_four_qPochInfPS,
      QseriesFormalization.PartIV.Ch19.coeff_five_qPochInfPS,
      QseriesFormalization.PartIV.Ch19.coeff_six_qPochInfPS]
  show (10 : R) * 0 + 2 * ((10 : Nat).choose 2 : R) * 1 * (-1)
      + 2 * ((10 : Nat).choose 2 : R) * 0 * (-1)
      + ((10 : Nat).choose 2 : R) * (0 : R) ^ 2
      + 3 * ((10 : Nat).choose 3 : R) * 0 * (-1 : R) ^ 2
      + 6 * ((10 : Nat).choose 3 : R) * 0 * (-1) * (-1)
      + ((10 : Nat).choose 3 : R) * (-1 : R) ^ 3
      + 4 * ((10 : Nat).choose 4 : R) * 0 * (-1 : R) ^ 3
      + 6 * ((10 : Nat).choose 4 : R) * (-1 : R) ^ 2 * (-1 : R) ^ 2
      + 5 * ((10 : Nat).choose 5 : R) * (-1) * (-1 : R) ^ 4
      + ((10 : Nat).choose 6 : R) * (-1 : R) ^ 6 = 0
  rw [show ((10 : Nat).choose 2 : R) = 45 from by norm_num [Nat.choose],
      show ((10 : Nat).choose 3 : R) = 120 from by norm_num [Nat.choose],
      show ((10 : Nat).choose 4 : R) = 210 from by norm_num [Nat.choose],
      show ((10 : Nat).choose 5 : R) = 252 from by norm_num [Nat.choose],
      show ((10 : Nat).choose 6 : R) = 210 from by norm_num [Nat.choose]]
  ring

/-- The seventh coefficient: `τ(7) = -16744`. -/
theorem ramanujanTau_seven : ramanujanTau R 7 = -16744 := by
  unfold ramanujanTau discriminantPS
  rw [show (7 : Nat) = 6 + 1 from rfl]
  rw [PowerSeries.coeff_succ_X_mul]
  -- (eta^24).coeff 6 via coeff_six_pow_of_constantCoeff_one with k=24:
  --   24·0 + 2·276·1·(-1) + 0 + 0 + 0 + 0 + 2024·(-1) + 0
  --        + 6·10626·1·1 + 5·42504·(-1)·1 + 134596·1
  --   = -552 - 2024 + 63756 - 212520 + 134596 = -16744
  rw [coeff_six_pow_of_constantCoeff_one R (etaPS R) (coeff_zero_etaPS R) 24]
  rw [show (etaPS R).coeff 1 = -1 from coeff_one_qPochInfPS R]
  rw [show (etaPS R).coeff 2 = -1 from coeff_two_qPochInfPS R]
  rw [show (etaPS R).coeff 3 = 0 from coeff_three_qPochInfPS R]
  rw [show (etaPS R).coeff 4 = 0 from coeff_four_qPochInfPS R]
  rw [show (etaPS R).coeff 5 = 1 from coeff_five_qPochInfPS R]
  rw [show (etaPS R).coeff 6 = 0 from coeff_six_qPochInfPS R]
  show (24 : R) * 0 + 2 * ((24 : Nat).choose 2 : R) * 1 * (-1)
      + 2 * ((24 : Nat).choose 2 : R) * 0 * (-1)
      + ((24 : Nat).choose 2 : R) * (0 : R) ^ 2
      + 3 * ((24 : Nat).choose 3 : R) * 0 * (-1 : R) ^ 2
      + 6 * ((24 : Nat).choose 3 : R) * 0 * (-1) * (-1)
      + ((24 : Nat).choose 3 : R) * (-1 : R) ^ 3
      + 4 * ((24 : Nat).choose 4 : R) * 0 * (-1 : R) ^ 3
      + 6 * ((24 : Nat).choose 4 : R) * (-1 : R) ^ 2 * (-1 : R) ^ 2
      + 5 * ((24 : Nat).choose 5 : R) * (-1) * (-1 : R) ^ 4
      + ((24 : Nat).choose 6 : R) * (-1 : R) ^ 6 = -16744
  rw [show ((24 : Nat).choose 2 : R) = 276 from by norm_num [Nat.choose],
      show ((24 : Nat).choose 3 : R) = 2024 from by norm_num [Nat.choose],
      show ((24 : Nat).choose 4 : R) = 10626 from by norm_num [Nat.choose],
      show ((24 : Nat).choose 5 : R) = 42504 from by norm_num [Nat.choose],
      show ((24 : Nat).choose 6 : R) = 134596 from by norm_num [Nat.choose]]
  ring

/-- **Ramanujan p(6) ≡ 0 (mod 11)** — unconditional, via formal power series.
The n=0 case of `p(11n+6) ≡ 0 (mod 11)`, completing the formal-PS closure of
the trio of classical Ramanujan congruences at n=0. -/
theorem ramanujan_partition_six_mod_eleven :
    ((QseriesFormalization.Ch01.partitionCount 6 : Nat) : ZMod 11) = 0 := by
  haveI : Fact (Nat.Prime 11) := ⟨by decide⟩
  have hp : (11 : Nat) ≠ 0 := by decide
  have hr : 6 < (11 : Nat) := by decide
  have h := QseriesFormalization.PartIV.Ch19.coeff_pochInfPow_eq_partitionCount_of_lt
    11 hp 6 hr
  simp only [show (11 - 1 : Nat) = 10 from rfl] at h
  rw [← h, coeff_six_qPochInf_pow_ten]

/-- Helper: `(f^k).coeff 7` for `f.coeff 0 = 1`, with all 15 shapes of 7:
(7); (6,1); (5,2); (4,3); (5,1,1); (4,2,1); (3,3,1); (3,2,2);
(4,1,1,1); (3,2,1,1); (2,2,2,1);
(3,1,1,1,1); (2,2,1,1,1); (2,1,1,1,1,1); (1^7). -/
theorem coeff_seven_pow_of_constantCoeff_one
    (f : R⟦X⟧) (hf : f.coeff 0 = 1) (k : Nat) :
    (f ^ k).coeff 7 = (k : R) * f.coeff 7
      + 2 * (k.choose 2 : R) * f.coeff 6 * f.coeff 1
      + 2 * (k.choose 2 : R) * f.coeff 5 * f.coeff 2
      + 2 * (k.choose 2 : R) * f.coeff 4 * f.coeff 3
      + 3 * (k.choose 3 : R) * f.coeff 5 * (f.coeff 1) ^ 2
      + 6 * (k.choose 3 : R) * f.coeff 4 * f.coeff 2 * f.coeff 1
      + 3 * (k.choose 3 : R) * (f.coeff 3) ^ 2 * f.coeff 1
      + 3 * (k.choose 3 : R) * f.coeff 3 * (f.coeff 2) ^ 2
      + 4 * (k.choose 4 : R) * f.coeff 4 * (f.coeff 1) ^ 3
      + 12 * (k.choose 4 : R) * f.coeff 3 * f.coeff 2 * (f.coeff 1) ^ 2
      + 4 * (k.choose 4 : R) * (f.coeff 2) ^ 3 * f.coeff 1
      + 5 * (k.choose 5 : R) * f.coeff 3 * (f.coeff 1) ^ 4
      + 10 * (k.choose 5 : R) * (f.coeff 2) ^ 2 * (f.coeff 1) ^ 3
      + 6 * (k.choose 6 : R) * f.coeff 2 * (f.coeff 1) ^ 5
      + (k.choose 7 : R) * (f.coeff 1) ^ 7 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, PowerSeries.coeff_mul]
    rw [show (Finset.antidiagonal 7 : Finset (Nat × Nat))
      = {(0, 7), (1, 6), (2, 5), (3, 4), (4, 3), (5, 2), (6, 1), (7, 0)} from rfl]
    rw [Finset.sum_insert (by simp), Finset.sum_insert (by simp),
        Finset.sum_insert (by simp), Finset.sum_insert (by simp),
        Finset.sum_insert (by simp), Finset.sum_insert (by simp),
        Finset.sum_insert (by simp), Finset.sum_singleton]
    have h_zero : (f ^ k).coeff 0 = 1 := by
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow,
          ← PowerSeries.coeff_zero_eq_constantCoeff_apply, hf, one_pow]
    have h_one : (f ^ k).coeff 1 = (k : R) * f.coeff 1 :=
      coeff_one_pow_of_constantCoeff_one R f hf k
    have h_two : (f ^ k).coeff 2 =
        (k : R) * f.coeff 2 + (k.choose 2 : R) * (f.coeff 1) ^ 2 :=
      coeff_two_pow_of_constantCoeff_one R f hf k
    have h_three : (f ^ k).coeff 3 = (k : R) * f.coeff 3
        + 2 * (k.choose 2 : R) * f.coeff 2 * f.coeff 1
        + (k.choose 3 : R) * (f.coeff 1) ^ 3 :=
      coeff_three_pow_of_constantCoeff_one R f hf k
    have h_four : (f ^ k).coeff 4 = (k : R) * f.coeff 4
        + 2 * (k.choose 2 : R) * f.coeff 3 * f.coeff 1
        + 3 * (k.choose 3 : R) * f.coeff 2 * (f.coeff 1) ^ 2
        + (k.choose 2 : R) * (f.coeff 2) ^ 2
        + (k.choose 4 : R) * (f.coeff 1) ^ 4 :=
      coeff_four_pow_of_constantCoeff_one R f hf k
    have h_five : (f ^ k).coeff 5 = (k : R) * f.coeff 5
        + 2 * (k.choose 2 : R) * f.coeff 4 * f.coeff 1
        + 2 * (k.choose 2 : R) * f.coeff 3 * f.coeff 2
        + 3 * (k.choose 3 : R) * f.coeff 3 * (f.coeff 1) ^ 2
        + 3 * (k.choose 3 : R) * (f.coeff 2) ^ 2 * f.coeff 1
        + 4 * (k.choose 4 : R) * f.coeff 2 * (f.coeff 1) ^ 3
        + (k.choose 5 : R) * (f.coeff 1) ^ 5 :=
      coeff_five_pow_of_constantCoeff_one R f hf k
    have h_six : (f ^ k).coeff 6 = (k : R) * f.coeff 6
        + 2 * (k.choose 2 : R) * f.coeff 5 * f.coeff 1
        + 2 * (k.choose 2 : R) * f.coeff 4 * f.coeff 2
        + (k.choose 2 : R) * (f.coeff 3) ^ 2
        + 3 * (k.choose 3 : R) * f.coeff 4 * (f.coeff 1) ^ 2
        + 6 * (k.choose 3 : R) * f.coeff 3 * f.coeff 2 * f.coeff 1
        + (k.choose 3 : R) * (f.coeff 2) ^ 3
        + 4 * (k.choose 4 : R) * f.coeff 3 * (f.coeff 1) ^ 3
        + 6 * (k.choose 4 : R) * (f.coeff 2) ^ 2 * (f.coeff 1) ^ 2
        + 5 * (k.choose 5 : R) * f.coeff 2 * (f.coeff 1) ^ 4
        + (k.choose 6 : R) * (f.coeff 1) ^ 6 :=
      coeff_six_pow_of_constantCoeff_one R f hf k
    rw [h_zero, h_one, h_two, h_three, h_four, h_five, h_six, ih, hf]
    have hC2 : ((k + 1).choose 2 : R) = (k.choose 2 : R) + k := by
      rw [Nat.choose_succ_succ k 1, Nat.choose_one_right]; push_cast; ring
    have hC3 : ((k + 1).choose 3 : R) = (k.choose 3 : R) + (k.choose 2 : R) := by
      rw [Nat.choose_succ_succ]; push_cast; ring
    have hC4 : ((k + 1).choose 4 : R) = (k.choose 4 : R) + (k.choose 3 : R) := by
      rw [Nat.choose_succ_succ]; push_cast; ring
    have hC5 : ((k + 1).choose 5 : R) = (k.choose 5 : R) + (k.choose 4 : R) := by
      rw [Nat.choose_succ_succ]; push_cast; ring
    have hC6 : ((k + 1).choose 6 : R) = (k.choose 6 : R) + (k.choose 5 : R) := by
      rw [Nat.choose_succ_succ]; push_cast; ring
    have hC7 : ((k + 1).choose 7 : R) = (k.choose 7 : R) + (k.choose 6 : R) := by
      rw [Nat.choose_succ_succ]; push_cast; ring
    rw [hC2, hC3, hC4, hC5, hC6, hC7]
    push_cast
    ring

/-- The eighth coefficient: `τ(8) = 84480`. -/
theorem ramanujanTau_eight : ramanujanTau R 8 = 84480 := by
  unfold ramanujanTau discriminantPS
  rw [show (8 : Nat) = 7 + 1 from rfl]
  rw [PowerSeries.coeff_succ_X_mul]
  rw [coeff_seven_pow_of_constantCoeff_one R (etaPS R) (coeff_zero_etaPS R) 24]
  rw [show (etaPS R).coeff 1 = -1 from coeff_one_qPochInfPS R]
  rw [show (etaPS R).coeff 2 = -1 from coeff_two_qPochInfPS R]
  rw [show (etaPS R).coeff 3 = 0 from coeff_three_qPochInfPS R]
  rw [show (etaPS R).coeff 4 = 0 from coeff_four_qPochInfPS R]
  rw [show (etaPS R).coeff 5 = 1 from coeff_five_qPochInfPS R]
  rw [show (etaPS R).coeff 6 = 0 from coeff_six_qPochInfPS R]
  rw [show (etaPS R).coeff 7 = 1 from
    QseriesFormalization.PartIV.Ch19.coeff_seven_qPochInfPS R]
  show (24 : R) * 1 + 2 * ((24 : Nat).choose 2 : R) * 0 * (-1)
      + 2 * ((24 : Nat).choose 2 : R) * 1 * (-1)
      + 2 * ((24 : Nat).choose 2 : R) * 0 * 0
      + 3 * ((24 : Nat).choose 3 : R) * 1 * (-1 : R) ^ 2
      + 6 * ((24 : Nat).choose 3 : R) * 0 * (-1) * (-1)
      + 3 * ((24 : Nat).choose 3 : R) * (0 : R) ^ 2 * (-1)
      + 3 * ((24 : Nat).choose 3 : R) * 0 * (-1 : R) ^ 2
      + 4 * ((24 : Nat).choose 4 : R) * 0 * (-1 : R) ^ 3
      + 12 * ((24 : Nat).choose 4 : R) * 0 * (-1) * (-1 : R) ^ 2
      + 4 * ((24 : Nat).choose 4 : R) * (-1 : R) ^ 3 * (-1)
      + 5 * ((24 : Nat).choose 5 : R) * 0 * (-1 : R) ^ 4
      + 10 * ((24 : Nat).choose 5 : R) * (-1 : R) ^ 2 * (-1 : R) ^ 3
      + 6 * ((24 : Nat).choose 6 : R) * (-1) * (-1 : R) ^ 5
      + ((24 : Nat).choose 7 : R) * (-1 : R) ^ 7 = 84480
  rw [show ((24 : Nat).choose 2 : R) = 276 from by norm_num [Nat.choose],
      show ((24 : Nat).choose 3 : R) = 2024 from by norm_num [Nat.choose],
      show ((24 : Nat).choose 4 : R) = 10626 from by norm_num [Nat.choose],
      show ((24 : Nat).choose 5 : R) = 42504 from by norm_num [Nat.choose],
      show ((24 : Nat).choose 6 : R) = 134596 from by norm_num [Nat.choose],
      show ((24 : Nat).choose 7 : R) = 346104 from by norm_num [Nat.choose]]
  ring

/-- **Ramanujan τ Hecke relation at p=2, a=2**: `τ(8) = τ(2)·τ(4) - 2¹¹ · τ(2)`. -/
theorem ramanujanTau_hecke_two_two :
    (ramanujanTau R 8 : R) = ramanujanTau R 2 * ramanujanTau R 4 - 2048 * ramanujanTau R 2 := by
  rw [ramanujanTau_eight, ramanujanTau_two, ramanujanTau_four]
  ring

/-! ### Extended Ramanujan τ values through 50 -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

/-- Integer coefficient of `(q;q)_inf`, via Euler's pentagonal theorem. -/
def tauEtaCoeffZ (n : Nat) : Int := QseriesFormalization.PartI.Ch04Franklin.pentagonalSign n

theorem coeff_etaPS_eq_tauEtaCoeffZ (R : Type*) [CommRing R] (n : Nat) :
    (etaPS R).coeff n = (tauEtaCoeffZ n : R) := by
  unfold etaPS tauEtaCoeffZ
  exact QseriesFormalization.PartIV.Ch19.coeff_qPochInfPS_eq_pentagonalSign R n

/-- One truncated convolution step for powers of `(q;q)_inf`, keeping coefficients `0..N`. -/
def tauEtaPowStep (N : Nat) (v : Vector Int (N + 1)) : Vector Int (N + 1) :=
  Vector.ofFn fun j : Fin (N + 1) =>
    ∑ i : Fin (j.1 + 1),
      v.get ⟨i.1, by omega⟩ * tauEtaCoeffZ (j.1 - i.1)

/-- Coefficients `0..N` of `(q;q)_inf^k`, computed by repeated truncated convolution. -/
def tauEtaPowVec (N : Nat) : Nat → Vector Int (N + 1)
  | 0 => Vector.ofFn fun j : Fin (N + 1) => if j.1 = 0 then 1 else 0
  | k + 1 => tauEtaPowStep N (tauEtaPowVec N k)

/-- The integer coefficient of `X^n` in `(q;q)_inf^k`. -/
def tauEtaPowCoeffZ (k n : Nat) : Int :=
  (tauEtaPowVec n k).get ⟨n, Nat.lt_succ_self n⟩

theorem tauEtaPowVec_spec (R : Type*) [CommRing R] (N k : Nat) :
    ∀ j : Fin (N + 1), ((tauEtaPowVec N k).get j : R) = ((etaPS R) ^ k).coeff j.1 := by
  induction k with
  | zero =>
      intro j
      rw [tauEtaPowVec, Vector.get_ofFn]
      by_cases h : j.1 = 0 <;> simp [h, PowerSeries.coeff_one]
  | succ k ih =>
      intro j
      rw [tauEtaPowVec, tauEtaPowStep, Vector.get_ofFn]
      rw [pow_succ, PowerSeries.coeff_mul]
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (f := fun a b => ((etaPS R) ^ k).coeff a * (etaPS R).coeff b) j.1]
      rw [← Fin.sum_univ_eq_sum_range
        (fun i => ((etaPS R) ^ k).coeff i * (etaPS R).coeff (j.1 - i)) (j.1 + 1)]
      push_cast
      apply Finset.sum_congr rfl
      intro i _
      rw [ih ⟨i.1, by omega⟩]
      rw [coeff_etaPS_eq_tauEtaCoeffZ]

theorem coeff_etaPS_pow_eq_tauEtaPowCoeffZ (R : Type*) [CommRing R] (k n : Nat) :
    ((etaPS R) ^ k).coeff n = (tauEtaPowCoeffZ k n : R) := by
  rw [← tauEtaPowVec_spec R n k ⟨n, Nat.lt_succ_self n⟩]
  rfl

theorem ramanujanTau_succ_eq_tauEtaPowCoeffZ (R : Type*) [CommRing R] (n : Nat) :
    ramanujanTau R (n + 1) = (tauEtaPowCoeffZ 24 n : R) := by
  unfold ramanujanTau discriminantPS
  rw [PowerSeries.coeff_succ_X_mul, coeff_etaPS_pow_eq_tauEtaPowCoeffZ]

theorem ramanujanTau_succ_eq_of_tauEtaPowCoeffZ
    (R : Type*) [CommRing R] (n : Nat) (z : Int) (h : tauEtaPowCoeffZ 24 n = z) :
    ramanujanTau R (n + 1) = (z : R) := by
  rw [ramanujanTau_succ_eq_tauEtaPowCoeffZ R n, h]

def tauEtaPowVecCoeffZ (N k n : Nat) : Int :=
  if h : n < N + 1 then (tauEtaPowVec N k).get ⟨n, h⟩ else 0

theorem ramanujanTau_succ_eq_tauEtaPowVecCoeffZ
    (R : Type*) [CommRing R] {N n : Nat} (hN : n < N + 1) :
    ramanujanTau R (n + 1) = (tauEtaPowVecCoeffZ N 24 n : R) := by
  unfold tauEtaPowVecCoeffZ
  rw [dif_pos hN]
  unfold ramanujanTau discriminantPS
  rw [PowerSeries.coeff_succ_X_mul]
  rw [← tauEtaPowVec_spec R N 24 ⟨n, hN⟩]

theorem ramanujanTau_succ_eq_of_tauEtaPowVecCoeffZ
    (R : Type*) [CommRing R] (N n : Nat) (hN : n < N + 1) (z : Int)
    (h : tauEtaPowVecCoeffZ N 24 n = z) :
    ramanujanTau R (n + 1) = (z : R) := by
  rw [ramanujanTau_succ_eq_tauEtaPowVecCoeffZ (R := R) (N := N) (n := n) hN, h]

def tauEtaPowVec49_24_coeffs : List Int :=
  [1, -24, 252, -1472, 4830, -6048, -16744, 84480,
    -113643, -115920, 534612, -370944, -577738, 401856, 1217160, 987136,
    -6905934, 2727432, 10661420, -7109760, -4219488, -12830688, 18643272,
    21288960, -25499225, 13865712, -73279080, 24647168, 128406630, -29211840,
    -52843168, -196706304, 134722224, 165742416, -80873520, 167282496,
    -182213314, -255874080, -145589976, 408038400, 308120442, 101267712,
    -17125708, -786948864, -548895690, -447438528, 2687348496, 248758272,
    -1696965207, 611981400]

theorem tauEtaPowVec49_24_cert :
    (tauEtaPowVec 49 24).toList = tauEtaPowVec49_24_coeffs := by
  decide

theorem tauEtaPowVec49_24_coeff_8 : tauEtaPowVecCoeffZ 49 24 8 = -113643 := by
  have h := congrArg (fun xs : List Int => xs[8]?) tauEtaPowVec49_24_cert
  simpa [tauEtaPowVecCoeffZ, tauEtaPowVec49_24_coeffs] using h

theorem tauEtaPowVec49_24_coeff_9 : tauEtaPowVecCoeffZ 49 24 9 = -115920 := by
  have h := congrArg (fun xs : List Int => xs[9]?) tauEtaPowVec49_24_cert
  simpa [tauEtaPowVecCoeffZ, tauEtaPowVec49_24_coeffs] using h

theorem tauEtaPowVec49_24_coeff_10 : tauEtaPowVecCoeffZ 49 24 10 = 534612 := by
  have h := congrArg (fun xs : List Int => xs[10]?) tauEtaPowVec49_24_cert
  simpa [tauEtaPowVecCoeffZ, tauEtaPowVec49_24_coeffs] using h

theorem tauEtaPowVec49_24_coeff_11 : tauEtaPowVecCoeffZ 49 24 11 = -370944 := by
  have h := congrArg (fun xs : List Int => xs[11]?) tauEtaPowVec49_24_cert
  simpa [tauEtaPowVecCoeffZ, tauEtaPowVec49_24_coeffs] using h

theorem tauEtaPowVec49_24_coeff_12 : tauEtaPowVecCoeffZ 49 24 12 = -577738 := by
  have h := congrArg (fun xs : List Int => xs[12]?) tauEtaPowVec49_24_cert
  simpa [tauEtaPowVecCoeffZ, tauEtaPowVec49_24_coeffs] using h

theorem tauEtaPowVec49_24_coeff_13 : tauEtaPowVecCoeffZ 49 24 13 = 401856 := by
  have h := congrArg (fun xs : List Int => xs[13]?) tauEtaPowVec49_24_cert
  simpa [tauEtaPowVecCoeffZ, tauEtaPowVec49_24_coeffs] using h

theorem tauEtaPowVec49_24_coeff_14 : tauEtaPowVecCoeffZ 49 24 14 = 1217160 := by
  have h := congrArg (fun xs : List Int => xs[14]?) tauEtaPowVec49_24_cert
  simpa [tauEtaPowVecCoeffZ, tauEtaPowVec49_24_coeffs] using h

theorem tauEtaPowVec49_24_coeff_15 : tauEtaPowVecCoeffZ 49 24 15 = 987136 := by
  have h := congrArg (fun xs : List Int => xs[15]?) tauEtaPowVec49_24_cert
  simpa [tauEtaPowVecCoeffZ, tauEtaPowVec49_24_coeffs] using h

theorem tauEtaPowVec49_24_coeff_16 : tauEtaPowVecCoeffZ 49 24 16 = -6905934 := by
  have h := congrArg (fun xs : List Int => xs[16]?) tauEtaPowVec49_24_cert
  simpa [tauEtaPowVecCoeffZ, tauEtaPowVec49_24_coeffs] using h

theorem tauEtaPowVec49_24_coeff_17 : tauEtaPowVecCoeffZ 49 24 17 = 2727432 := by
  have h := congrArg (fun xs : List Int => xs[17]?) tauEtaPowVec49_24_cert
  simpa [tauEtaPowVecCoeffZ, tauEtaPowVec49_24_coeffs] using h

theorem tauEtaPowVec49_24_coeff_18 : tauEtaPowVecCoeffZ 49 24 18 = 10661420 := by
  have h := congrArg (fun xs : List Int => xs[18]?) tauEtaPowVec49_24_cert
  simpa [tauEtaPowVecCoeffZ, tauEtaPowVec49_24_coeffs] using h

theorem tauEtaPowVec49_24_coeff_19 : tauEtaPowVecCoeffZ 49 24 19 = -7109760 := by
  have h := congrArg (fun xs : List Int => xs[19]?) tauEtaPowVec49_24_cert
  simpa [tauEtaPowVecCoeffZ, tauEtaPowVec49_24_coeffs] using h

theorem tauEtaPowVec49_24_coeff_20 : tauEtaPowVecCoeffZ 49 24 20 = -4219488 := by
  have h := congrArg (fun xs : List Int => xs[20]?) tauEtaPowVec49_24_cert
  simpa [tauEtaPowVecCoeffZ, tauEtaPowVec49_24_coeffs] using h

theorem tauEtaPowVec49_24_coeff_21 : tauEtaPowVecCoeffZ 49 24 21 = -12830688 := by
  have h := congrArg (fun xs : List Int => xs[21]?) tauEtaPowVec49_24_cert
  simpa [tauEtaPowVecCoeffZ, tauEtaPowVec49_24_coeffs] using h

theorem tauEtaPowVec49_24_coeff_22 : tauEtaPowVecCoeffZ 49 24 22 = 18643272 := by
  have h := congrArg (fun xs : List Int => xs[22]?) tauEtaPowVec49_24_cert
  simpa [tauEtaPowVecCoeffZ, tauEtaPowVec49_24_coeffs] using h

theorem tauEtaPowVec49_24_coeff_23 : tauEtaPowVecCoeffZ 49 24 23 = 21288960 := by
  have h := congrArg (fun xs : List Int => xs[23]?) tauEtaPowVec49_24_cert
  simpa [tauEtaPowVecCoeffZ, tauEtaPowVec49_24_coeffs] using h

theorem tauEtaPowVec49_24_coeff_24 : tauEtaPowVecCoeffZ 49 24 24 = -25499225 := by
  have h := congrArg (fun xs : List Int => xs[24]?) tauEtaPowVec49_24_cert
  simpa [tauEtaPowVecCoeffZ, tauEtaPowVec49_24_coeffs] using h

theorem tauEtaPowVec49_24_coeff_25 : tauEtaPowVecCoeffZ 49 24 25 = 13865712 := by
  have h := congrArg (fun xs : List Int => xs[25]?) tauEtaPowVec49_24_cert
  simpa [tauEtaPowVecCoeffZ, tauEtaPowVec49_24_coeffs] using h

theorem tauEtaPowVec49_24_coeff_26 : tauEtaPowVecCoeffZ 49 24 26 = -73279080 := by
  have h := congrArg (fun xs : List Int => xs[26]?) tauEtaPowVec49_24_cert
  simpa [tauEtaPowVecCoeffZ, tauEtaPowVec49_24_coeffs] using h

theorem tauEtaPowVec49_24_coeff_27 : tauEtaPowVecCoeffZ 49 24 27 = 24647168 := by
  have h := congrArg (fun xs : List Int => xs[27]?) tauEtaPowVec49_24_cert
  simpa [tauEtaPowVecCoeffZ, tauEtaPowVec49_24_coeffs] using h

theorem tauEtaPowVec49_24_coeff_28 : tauEtaPowVecCoeffZ 49 24 28 = 128406630 := by
  have h := congrArg (fun xs : List Int => xs[28]?) tauEtaPowVec49_24_cert
  simpa [tauEtaPowVecCoeffZ, tauEtaPowVec49_24_coeffs] using h

theorem tauEtaPowVec49_24_coeff_29 : tauEtaPowVecCoeffZ 49 24 29 = -29211840 := by
  have h := congrArg (fun xs : List Int => xs[29]?) tauEtaPowVec49_24_cert
  simpa [tauEtaPowVecCoeffZ, tauEtaPowVec49_24_coeffs] using h

theorem tauEtaPowVec49_24_coeff_30 : tauEtaPowVecCoeffZ 49 24 30 = -52843168 := by
  have h := congrArg (fun xs : List Int => xs[30]?) tauEtaPowVec49_24_cert
  simpa [tauEtaPowVecCoeffZ, tauEtaPowVec49_24_coeffs] using h

theorem tauEtaPowVec49_24_coeff_31 : tauEtaPowVecCoeffZ 49 24 31 = -196706304 := by
  have h := congrArg (fun xs : List Int => xs[31]?) tauEtaPowVec49_24_cert
  simpa [tauEtaPowVecCoeffZ, tauEtaPowVec49_24_coeffs] using h

theorem tauEtaPowVec49_24_coeff_32 : tauEtaPowVecCoeffZ 49 24 32 = 134722224 := by
  have h := congrArg (fun xs : List Int => xs[32]?) tauEtaPowVec49_24_cert
  simpa [tauEtaPowVecCoeffZ, tauEtaPowVec49_24_coeffs] using h

theorem tauEtaPowVec49_24_coeff_33 : tauEtaPowVecCoeffZ 49 24 33 = 165742416 := by
  have h := congrArg (fun xs : List Int => xs[33]?) tauEtaPowVec49_24_cert
  simpa [tauEtaPowVecCoeffZ, tauEtaPowVec49_24_coeffs] using h

theorem tauEtaPowVec49_24_coeff_34 : tauEtaPowVecCoeffZ 49 24 34 = -80873520 := by
  have h := congrArg (fun xs : List Int => xs[34]?) tauEtaPowVec49_24_cert
  simpa [tauEtaPowVecCoeffZ, tauEtaPowVec49_24_coeffs] using h

theorem tauEtaPowVec49_24_coeff_35 : tauEtaPowVecCoeffZ 49 24 35 = 167282496 := by
  have h := congrArg (fun xs : List Int => xs[35]?) tauEtaPowVec49_24_cert
  simpa [tauEtaPowVecCoeffZ, tauEtaPowVec49_24_coeffs] using h

theorem tauEtaPowVec49_24_coeff_36 : tauEtaPowVecCoeffZ 49 24 36 = -182213314 := by
  have h := congrArg (fun xs : List Int => xs[36]?) tauEtaPowVec49_24_cert
  simpa [tauEtaPowVecCoeffZ, tauEtaPowVec49_24_coeffs] using h

theorem tauEtaPowVec49_24_coeff_37 : tauEtaPowVecCoeffZ 49 24 37 = -255874080 := by
  have h := congrArg (fun xs : List Int => xs[37]?) tauEtaPowVec49_24_cert
  simpa [tauEtaPowVecCoeffZ, tauEtaPowVec49_24_coeffs] using h

theorem tauEtaPowVec49_24_coeff_38 : tauEtaPowVecCoeffZ 49 24 38 = -145589976 := by
  have h := congrArg (fun xs : List Int => xs[38]?) tauEtaPowVec49_24_cert
  simpa [tauEtaPowVecCoeffZ, tauEtaPowVec49_24_coeffs] using h

theorem tauEtaPowVec49_24_coeff_39 : tauEtaPowVecCoeffZ 49 24 39 = 408038400 := by
  have h := congrArg (fun xs : List Int => xs[39]?) tauEtaPowVec49_24_cert
  simpa [tauEtaPowVecCoeffZ, tauEtaPowVec49_24_coeffs] using h

theorem tauEtaPowVec49_24_coeff_40 : tauEtaPowVecCoeffZ 49 24 40 = 308120442 := by
  have h := congrArg (fun xs : List Int => xs[40]?) tauEtaPowVec49_24_cert
  simpa [tauEtaPowVecCoeffZ, tauEtaPowVec49_24_coeffs] using h

theorem tauEtaPowVec49_24_coeff_41 : tauEtaPowVecCoeffZ 49 24 41 = 101267712 := by
  have h := congrArg (fun xs : List Int => xs[41]?) tauEtaPowVec49_24_cert
  simpa [tauEtaPowVecCoeffZ, tauEtaPowVec49_24_coeffs] using h

theorem tauEtaPowVec49_24_coeff_42 : tauEtaPowVecCoeffZ 49 24 42 = -17125708 := by
  have h := congrArg (fun xs : List Int => xs[42]?) tauEtaPowVec49_24_cert
  simpa [tauEtaPowVecCoeffZ, tauEtaPowVec49_24_coeffs] using h

theorem tauEtaPowVec49_24_coeff_43 : tauEtaPowVecCoeffZ 49 24 43 = -786948864 := by
  have h := congrArg (fun xs : List Int => xs[43]?) tauEtaPowVec49_24_cert
  simpa [tauEtaPowVecCoeffZ, tauEtaPowVec49_24_coeffs] using h

theorem tauEtaPowVec49_24_coeff_44 : tauEtaPowVecCoeffZ 49 24 44 = -548895690 := by
  have h := congrArg (fun xs : List Int => xs[44]?) tauEtaPowVec49_24_cert
  simpa [tauEtaPowVecCoeffZ, tauEtaPowVec49_24_coeffs] using h

theorem tauEtaPowVec49_24_coeff_45 : tauEtaPowVecCoeffZ 49 24 45 = -447438528 := by
  have h := congrArg (fun xs : List Int => xs[45]?) tauEtaPowVec49_24_cert
  simpa [tauEtaPowVecCoeffZ, tauEtaPowVec49_24_coeffs] using h

theorem tauEtaPowVec49_24_coeff_46 : tauEtaPowVecCoeffZ 49 24 46 = 2687348496 := by
  have h := congrArg (fun xs : List Int => xs[46]?) tauEtaPowVec49_24_cert
  simpa [tauEtaPowVecCoeffZ, tauEtaPowVec49_24_coeffs] using h

theorem tauEtaPowVec49_24_coeff_47 : tauEtaPowVecCoeffZ 49 24 47 = 248758272 := by
  have h := congrArg (fun xs : List Int => xs[47]?) tauEtaPowVec49_24_cert
  simpa [tauEtaPowVecCoeffZ, tauEtaPowVec49_24_coeffs] using h

theorem tauEtaPowVec49_24_coeff_48 : tauEtaPowVecCoeffZ 49 24 48 = -1696965207 := by
  have h := congrArg (fun xs : List Int => xs[48]?) tauEtaPowVec49_24_cert
  simpa [tauEtaPowVecCoeffZ, tauEtaPowVec49_24_coeffs] using h

theorem tauEtaPowVec49_24_coeff_49 : tauEtaPowVecCoeffZ 49 24 49 = 611981400 := by
  have h := congrArg (fun xs : List Int => xs[49]?) tauEtaPowVec49_24_cert
  simpa [tauEtaPowVecCoeffZ, tauEtaPowVec49_24_coeffs] using h

theorem ramanujanTau_nine (R : Type*) [CommRing R] : ramanujanTau R 9 = -113643 := by
  simpa using ramanujanTau_succ_eq_of_tauEtaPowVecCoeffZ R 49 8 (by norm_num) (-113643 : Int) tauEtaPowVec49_24_coeff_8

theorem ramanujanTau_ten (R : Type*) [CommRing R] : ramanujanTau R 10 = -115920 := by
  simpa using ramanujanTau_succ_eq_of_tauEtaPowVecCoeffZ R 49 9 (by norm_num) (-115920 : Int) tauEtaPowVec49_24_coeff_9

theorem ramanujanTau_eleven (R : Type*) [CommRing R] : ramanujanTau R 11 = 534612 := by
  simpa using ramanujanTau_succ_eq_of_tauEtaPowVecCoeffZ R 49 10 (by norm_num) (534612 : Int) tauEtaPowVec49_24_coeff_10

theorem ramanujanTau_twelve (R : Type*) [CommRing R] : ramanujanTau R 12 = -370944 := by
  simpa using ramanujanTau_succ_eq_of_tauEtaPowVecCoeffZ R 49 11 (by norm_num) (-370944 : Int) tauEtaPowVec49_24_coeff_11

theorem ramanujanTau_thirteen (R : Type*) [CommRing R] : ramanujanTau R 13 = -577738 := by
  simpa using ramanujanTau_succ_eq_of_tauEtaPowVecCoeffZ R 49 12 (by norm_num) (-577738 : Int) tauEtaPowVec49_24_coeff_12

theorem ramanujanTau_fourteen (R : Type*) [CommRing R] : ramanujanTau R 14 = 401856 := by
  simpa using ramanujanTau_succ_eq_of_tauEtaPowVecCoeffZ R 49 13 (by norm_num) (401856 : Int) tauEtaPowVec49_24_coeff_13

theorem ramanujanTau_fifteen (R : Type*) [CommRing R] : ramanujanTau R 15 = 1217160 := by
  simpa using ramanujanTau_succ_eq_of_tauEtaPowVecCoeffZ R 49 14 (by norm_num) (1217160 : Int) tauEtaPowVec49_24_coeff_14

theorem ramanujanTau_sixteen (R : Type*) [CommRing R] : ramanujanTau R 16 = 987136 := by
  simpa using ramanujanTau_succ_eq_of_tauEtaPowVecCoeffZ R 49 15 (by norm_num) (987136 : Int) tauEtaPowVec49_24_coeff_15

theorem ramanujanTau_seventeen (R : Type*) [CommRing R] : ramanujanTau R 17 = -6905934 := by
  simpa using ramanujanTau_succ_eq_of_tauEtaPowVecCoeffZ R 49 16 (by norm_num) (-6905934 : Int) tauEtaPowVec49_24_coeff_16

theorem ramanujanTau_eighteen (R : Type*) [CommRing R] : ramanujanTau R 18 = 2727432 := by
  simpa using ramanujanTau_succ_eq_of_tauEtaPowVecCoeffZ R 49 17 (by norm_num) (2727432 : Int) tauEtaPowVec49_24_coeff_17

theorem ramanujanTau_nineteen (R : Type*) [CommRing R] : ramanujanTau R 19 = 10661420 := by
  simpa using ramanujanTau_succ_eq_of_tauEtaPowVecCoeffZ R 49 18 (by norm_num) (10661420 : Int) tauEtaPowVec49_24_coeff_18

theorem ramanujanTau_twenty (R : Type*) [CommRing R] : ramanujanTau R 20 = -7109760 := by
  simpa using ramanujanTau_succ_eq_of_tauEtaPowVecCoeffZ R 49 19 (by norm_num) (-7109760 : Int) tauEtaPowVec49_24_coeff_19

theorem ramanujanTau_twentyone (R : Type*) [CommRing R] : ramanujanTau R 21 = -4219488 := by
  simpa using ramanujanTau_succ_eq_of_tauEtaPowVecCoeffZ R 49 20 (by norm_num) (-4219488 : Int) tauEtaPowVec49_24_coeff_20

theorem ramanujanTau_twentytwo (R : Type*) [CommRing R] : ramanujanTau R 22 = -12830688 := by
  simpa using ramanujanTau_succ_eq_of_tauEtaPowVecCoeffZ R 49 21 (by norm_num) (-12830688 : Int) tauEtaPowVec49_24_coeff_21

theorem ramanujanTau_twentythree (R : Type*) [CommRing R] : ramanujanTau R 23 = 18643272 := by
  simpa using ramanujanTau_succ_eq_of_tauEtaPowVecCoeffZ R 49 22 (by norm_num) (18643272 : Int) tauEtaPowVec49_24_coeff_22

theorem ramanujanTau_twentyfour (R : Type*) [CommRing R] : ramanujanTau R 24 = 21288960 := by
  simpa using ramanujanTau_succ_eq_of_tauEtaPowVecCoeffZ R 49 23 (by norm_num) (21288960 : Int) tauEtaPowVec49_24_coeff_23

theorem ramanujanTau_twentyfive (R : Type*) [CommRing R] : ramanujanTau R 25 = -25499225 := by
  simpa using ramanujanTau_succ_eq_of_tauEtaPowVecCoeffZ R 49 24 (by norm_num) (-25499225 : Int) tauEtaPowVec49_24_coeff_24

theorem ramanujanTau_twentysix (R : Type*) [CommRing R] : ramanujanTau R 26 = 13865712 := by
  simpa using ramanujanTau_succ_eq_of_tauEtaPowVecCoeffZ R 49 25 (by norm_num) (13865712 : Int) tauEtaPowVec49_24_coeff_25

theorem ramanujanTau_twentyseven (R : Type*) [CommRing R] : ramanujanTau R 27 = -73279080 := by
  simpa using ramanujanTau_succ_eq_of_tauEtaPowVecCoeffZ R 49 26 (by norm_num) (-73279080 : Int) tauEtaPowVec49_24_coeff_26

theorem ramanujanTau_twentyeight (R : Type*) [CommRing R] : ramanujanTau R 28 = 24647168 := by
  simpa using ramanujanTau_succ_eq_of_tauEtaPowVecCoeffZ R 49 27 (by norm_num) (24647168 : Int) tauEtaPowVec49_24_coeff_27

theorem ramanujanTau_twentynine (R : Type*) [CommRing R] : ramanujanTau R 29 = 128406630 := by
  simpa using ramanujanTau_succ_eq_of_tauEtaPowVecCoeffZ R 49 28 (by norm_num) (128406630 : Int) tauEtaPowVec49_24_coeff_28

theorem ramanujanTau_thirty (R : Type*) [CommRing R] : ramanujanTau R 30 = -29211840 := by
  simpa using ramanujanTau_succ_eq_of_tauEtaPowVecCoeffZ R 49 29 (by norm_num) (-29211840 : Int) tauEtaPowVec49_24_coeff_29

theorem ramanujanTau_thirtyone (R : Type*) [CommRing R] : ramanujanTau R 31 = -52843168 := by
  simpa using ramanujanTau_succ_eq_of_tauEtaPowVecCoeffZ R 49 30 (by norm_num) (-52843168 : Int) tauEtaPowVec49_24_coeff_30

theorem ramanujanTau_thirtytwo (R : Type*) [CommRing R] : ramanujanTau R 32 = -196706304 := by
  simpa using ramanujanTau_succ_eq_of_tauEtaPowVecCoeffZ R 49 31 (by norm_num) (-196706304 : Int) tauEtaPowVec49_24_coeff_31

theorem ramanujanTau_thirtythree (R : Type*) [CommRing R] : ramanujanTau R 33 = 134722224 := by
  simpa using ramanujanTau_succ_eq_of_tauEtaPowVecCoeffZ R 49 32 (by norm_num) (134722224 : Int) tauEtaPowVec49_24_coeff_32

theorem ramanujanTau_thirtyfour (R : Type*) [CommRing R] : ramanujanTau R 34 = 165742416 := by
  simpa using ramanujanTau_succ_eq_of_tauEtaPowVecCoeffZ R 49 33 (by norm_num) (165742416 : Int) tauEtaPowVec49_24_coeff_33

theorem ramanujanTau_thirtyfive (R : Type*) [CommRing R] : ramanujanTau R 35 = -80873520 := by
  simpa using ramanujanTau_succ_eq_of_tauEtaPowVecCoeffZ R 49 34 (by norm_num) (-80873520 : Int) tauEtaPowVec49_24_coeff_34

theorem ramanujanTau_thirtysix (R : Type*) [CommRing R] : ramanujanTau R 36 = 167282496 := by
  simpa using ramanujanTau_succ_eq_of_tauEtaPowVecCoeffZ R 49 35 (by norm_num) (167282496 : Int) tauEtaPowVec49_24_coeff_35

theorem ramanujanTau_thirtyseven (R : Type*) [CommRing R] : ramanujanTau R 37 = -182213314 := by
  simpa using ramanujanTau_succ_eq_of_tauEtaPowVecCoeffZ R 49 36 (by norm_num) (-182213314 : Int) tauEtaPowVec49_24_coeff_36

theorem ramanujanTau_thirtyeight (R : Type*) [CommRing R] : ramanujanTau R 38 = -255874080 := by
  simpa using ramanujanTau_succ_eq_of_tauEtaPowVecCoeffZ R 49 37 (by norm_num) (-255874080 : Int) tauEtaPowVec49_24_coeff_37

theorem ramanujanTau_thirtynine (R : Type*) [CommRing R] : ramanujanTau R 39 = -145589976 := by
  simpa using ramanujanTau_succ_eq_of_tauEtaPowVecCoeffZ R 49 38 (by norm_num) (-145589976 : Int) tauEtaPowVec49_24_coeff_38

theorem ramanujanTau_forty (R : Type*) [CommRing R] : ramanujanTau R 40 = 408038400 := by
  simpa using ramanujanTau_succ_eq_of_tauEtaPowVecCoeffZ R 49 39 (by norm_num) (408038400 : Int) tauEtaPowVec49_24_coeff_39

theorem ramanujanTau_fortyone (R : Type*) [CommRing R] : ramanujanTau R 41 = 308120442 := by
  simpa using ramanujanTau_succ_eq_of_tauEtaPowVecCoeffZ R 49 40 (by norm_num) (308120442 : Int) tauEtaPowVec49_24_coeff_40

theorem ramanujanTau_fortytwo (R : Type*) [CommRing R] : ramanujanTau R 42 = 101267712 := by
  simpa using ramanujanTau_succ_eq_of_tauEtaPowVecCoeffZ R 49 41 (by norm_num) (101267712 : Int) tauEtaPowVec49_24_coeff_41

theorem ramanujanTau_fortythree (R : Type*) [CommRing R] : ramanujanTau R 43 = -17125708 := by
  simpa using ramanujanTau_succ_eq_of_tauEtaPowVecCoeffZ R 49 42 (by norm_num) (-17125708 : Int) tauEtaPowVec49_24_coeff_42

theorem ramanujanTau_fortyfour (R : Type*) [CommRing R] : ramanujanTau R 44 = -786948864 := by
  simpa using ramanujanTau_succ_eq_of_tauEtaPowVecCoeffZ R 49 43 (by norm_num) (-786948864 : Int) tauEtaPowVec49_24_coeff_43

theorem ramanujanTau_fortyfive (R : Type*) [CommRing R] : ramanujanTau R 45 = -548895690 := by
  simpa using ramanujanTau_succ_eq_of_tauEtaPowVecCoeffZ R 49 44 (by norm_num) (-548895690 : Int) tauEtaPowVec49_24_coeff_44

theorem ramanujanTau_fortysix (R : Type*) [CommRing R] : ramanujanTau R 46 = -447438528 := by
  simpa using ramanujanTau_succ_eq_of_tauEtaPowVecCoeffZ R 49 45 (by norm_num) (-447438528 : Int) tauEtaPowVec49_24_coeff_45

theorem ramanujanTau_fortyseven (R : Type*) [CommRing R] : ramanujanTau R 47 = 2687348496 := by
  simpa using ramanujanTau_succ_eq_of_tauEtaPowVecCoeffZ R 49 46 (by norm_num) (2687348496 : Int) tauEtaPowVec49_24_coeff_46

theorem ramanujanTau_fortyeight (R : Type*) [CommRing R] : ramanujanTau R 48 = 248758272 := by
  simpa using ramanujanTau_succ_eq_of_tauEtaPowVecCoeffZ R 49 47 (by norm_num) (248758272 : Int) tauEtaPowVec49_24_coeff_47

theorem ramanujanTau_fortynine (R : Type*) [CommRing R] : ramanujanTau R 49 = -1696965207 := by
  simpa using ramanujanTau_succ_eq_of_tauEtaPowVecCoeffZ R 49 48 (by norm_num) (-1696965207 : Int) tauEtaPowVec49_24_coeff_48

theorem ramanujanTau_fifty (R : Type*) [CommRing R] : ramanujanTau R 50 = 611981400 := by
  simpa using ramanujanTau_succ_eq_of_tauEtaPowVecCoeffZ R 49 49 (by norm_num) (611981400 : Int) tauEtaPowVec49_24_coeff_49

/-! ### Hecke multiplicativity checks at coprime factor pairs up to 50 -/

theorem ramanujanTau_ten_eq : ramanujanTau ℤ 10 = ramanujanTau ℤ 2 * ramanujanTau ℤ 5 := by
  rw [ramanujanTau_ten, ramanujanTau_two, ramanujanTau_five]
  norm_num

theorem ramanujanTau_fourteen_eq : ramanujanTau ℤ 14 = ramanujanTau ℤ 2 * ramanujanTau ℤ 7 := by
  rw [ramanujanTau_fourteen, ramanujanTau_two, ramanujanTau_seven]
  norm_num

theorem ramanujanTau_fifteen_eq : ramanujanTau ℤ 15 = ramanujanTau ℤ 3 * ramanujanTau ℤ 5 := by
  rw [ramanujanTau_fifteen, ramanujanTau_three, ramanujanTau_five]
  norm_num

theorem ramanujanTau_eighteen_eq : ramanujanTau ℤ 18 = ramanujanTau ℤ 2 * ramanujanTau ℤ 9 := by
  rw [ramanujanTau_eighteen, ramanujanTau_two, ramanujanTau_nine]
  norm_num

theorem ramanujanTau_twenty_eq : ramanujanTau ℤ 20 = ramanujanTau ℤ 4 * ramanujanTau ℤ 5 := by
  rw [ramanujanTau_twenty, ramanujanTau_four, ramanujanTau_five]
  norm_num

theorem ramanujanTau_twentyone_eq : ramanujanTau ℤ 21 = ramanujanTau ℤ 3 * ramanujanTau ℤ 7 := by
  rw [ramanujanTau_twentyone, ramanujanTau_three, ramanujanTau_seven]
  norm_num

theorem ramanujanTau_twentytwo_eq : ramanujanTau ℤ 22 = ramanujanTau ℤ 2 * ramanujanTau ℤ 11 := by
  rw [ramanujanTau_twentytwo, ramanujanTau_two, ramanujanTau_eleven]
  norm_num

theorem ramanujanTau_twelve_eq : ramanujanTau ℤ 12 = ramanujanTau ℤ 3 * ramanujanTau ℤ 4 := by
  rw [ramanujanTau_twelve, ramanujanTau_three, ramanujanTau_four]
  norm_num

theorem ramanujanTau_twentyfour_eq : ramanujanTau ℤ 24 = ramanujanTau ℤ 3 * ramanujanTau ℤ 8 := by
  rw [ramanujanTau_twentyfour, ramanujanTau_three, ramanujanTau_eight]
  norm_num

theorem ramanujanTau_twentysix_eq : ramanujanTau ℤ 26 = ramanujanTau ℤ 2 * ramanujanTau ℤ 13 := by
  rw [ramanujanTau_twentysix, ramanujanTau_two, ramanujanTau_thirteen]
  norm_num

theorem ramanujanTau_twentyeight_eq : ramanujanTau ℤ 28 = ramanujanTau ℤ 4 * ramanujanTau ℤ 7 := by
  rw [ramanujanTau_twentyeight, ramanujanTau_four, ramanujanTau_seven]
  norm_num

theorem ramanujanTau_thirty_eq : ramanujanTau ℤ 30 = ramanujanTau ℤ 2 * ramanujanTau ℤ 15 := by
  rw [ramanujanTau_thirty, ramanujanTau_two, ramanujanTau_fifteen]
  norm_num

theorem ramanujanTau_thirty_eq' : ramanujanTau ℤ 30 = ramanujanTau ℤ 5 * ramanujanTau ℤ 6 := by
  rw [ramanujanTau_thirty, ramanujanTau_five, ramanujanTau_six]
  norm_num

theorem ramanujanTau_thirty_eq'' : ramanujanTau ℤ 30 = ramanujanTau ℤ 3 * ramanujanTau ℤ 10 := by
  rw [ramanujanTau_thirty, ramanujanTau_three, ramanujanTau_ten]
  norm_num

theorem ramanujanTau_thirtythree_eq : ramanujanTau ℤ 33 = ramanujanTau ℤ 3 * ramanujanTau ℤ 11 := by
  rw [ramanujanTau_thirtythree, ramanujanTau_three, ramanujanTau_eleven]
  norm_num

theorem ramanujanTau_thirtyfour_eq : ramanujanTau ℤ 34 = ramanujanTau ℤ 2 * ramanujanTau ℤ 17 := by
  rw [ramanujanTau_thirtyfour, ramanujanTau_two, ramanujanTau_seventeen]
  norm_num

theorem ramanujanTau_thirtyfive_eq : ramanujanTau ℤ 35 = ramanujanTau ℤ 5 * ramanujanTau ℤ 7 := by
  rw [ramanujanTau_thirtyfive, ramanujanTau_five, ramanujanTau_seven]
  norm_num

theorem ramanujanTau_thirtysix_eq : ramanujanTau ℤ 36 = ramanujanTau ℤ 4 * ramanujanTau ℤ 9 := by
  rw [ramanujanTau_thirtysix, ramanujanTau_four, ramanujanTau_nine]
  norm_num

theorem ramanujanTau_thirtyeight_eq : ramanujanTau ℤ 38 = ramanujanTau ℤ 2 * ramanujanTau ℤ 19 := by
  rw [ramanujanTau_thirtyeight, ramanujanTau_two, ramanujanTau_nineteen]
  norm_num

theorem ramanujanTau_thirtynine_eq : ramanujanTau ℤ 39 = ramanujanTau ℤ 3 * ramanujanTau ℤ 13 := by
  rw [ramanujanTau_thirtynine, ramanujanTau_three, ramanujanTau_thirteen]
  norm_num

theorem ramanujanTau_forty_eq : ramanujanTau ℤ 40 = ramanujanTau ℤ 5 * ramanujanTau ℤ 8 := by
  rw [ramanujanTau_forty, ramanujanTau_five, ramanujanTau_eight]
  norm_num

theorem ramanujanTau_fortytwo_eq : ramanujanTau ℤ 42 = ramanujanTau ℤ 2 * ramanujanTau ℤ 21 := by
  rw [ramanujanTau_fortytwo, ramanujanTau_two, ramanujanTau_twentyone]
  norm_num

theorem ramanujanTau_fortytwo_eq' : ramanujanTau ℤ 42 = ramanujanTau ℤ 3 * ramanujanTau ℤ 14 := by
  rw [ramanujanTau_fortytwo, ramanujanTau_three, ramanujanTau_fourteen]
  norm_num

theorem ramanujanTau_fortytwo_eq'' : ramanujanTau ℤ 42 = ramanujanTau ℤ 6 * ramanujanTau ℤ 7 := by
  rw [ramanujanTau_fortytwo, ramanujanTau_six, ramanujanTau_seven]
  norm_num

theorem ramanujanTau_fortyfour_eq : ramanujanTau ℤ 44 = ramanujanTau ℤ 4 * ramanujanTau ℤ 11 := by
  rw [ramanujanTau_fortyfour, ramanujanTau_four, ramanujanTau_eleven]
  norm_num

theorem ramanujanTau_fortyfive_eq : ramanujanTau ℤ 45 = ramanujanTau ℤ 5 * ramanujanTau ℤ 9 := by
  rw [ramanujanTau_fortyfive, ramanujanTau_five, ramanujanTau_nine]
  norm_num

theorem ramanujanTau_fortysix_eq : ramanujanTau ℤ 46 = ramanujanTau ℤ 2 * ramanujanTau ℤ 23 := by
  rw [ramanujanTau_fortysix, ramanujanTau_two, ramanujanTau_twentythree]
  norm_num

theorem ramanujanTau_fortyeight_eq : ramanujanTau ℤ 48 = ramanujanTau ℤ 3 * ramanujanTau ℤ 16 := by
  rw [ramanujanTau_fortyeight, ramanujanTau_three, ramanujanTau_sixteen]
  norm_num

theorem ramanujanTau_fifty_eq : ramanujanTau ℤ 50 = ramanujanTau ℤ 2 * ramanujanTau ℤ 25 := by
  rw [ramanujanTau_fifty, ramanujanTau_two, ramanujanTau_twentyfive]
  norm_num

theorem ramanujanTau_mul_of_coprime_mul_le_50 (a b : Nat) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (_hab : Nat.Coprime a b) (hprod : a * b ≤ 50) :
    ramanujanTau ℤ (a * b) = ramanujanTau ℤ a * ramanujanTau ℤ b := by
  have ha50 : a ≤ 50 := by
    have hle : a ≤ a * b := by
      calc
        a = a * 1 := by rw [mul_one]
        _ ≤ a * b := Nat.mul_le_mul_left a hb
    exact le_trans hle hprod
  have hb50 : b ≤ 50 := by
    have hle : b ≤ a * b := by
      calc
        b = 1 * b := by rw [one_mul]
        _ ≤ a * b := Nat.mul_le_mul_right b ha
    exact le_trans hle hprod
  interval_cases a <;> interval_cases b <;>
    simp [ramanujanTau_zero, ramanujanTau_one, ramanujanTau_two, ramanujanTau_three,
      ramanujanTau_four, ramanujanTau_five, ramanujanTau_six, ramanujanTau_seven,
      ramanujanTau_eight, ramanujanTau_nine, ramanujanTau_ten, ramanujanTau_eleven,
      ramanujanTau_twelve, ramanujanTau_thirteen, ramanujanTau_fourteen,
      ramanujanTau_fifteen, ramanujanTau_sixteen, ramanujanTau_seventeen,
      ramanujanTau_eighteen, ramanujanTau_nineteen, ramanujanTau_twenty,
      ramanujanTau_twentyone, ramanujanTau_twentytwo, ramanujanTau_twentythree,
      ramanujanTau_twentyfour, ramanujanTau_twentyfive, ramanujanTau_twentysix,
      ramanujanTau_twentyseven, ramanujanTau_twentyeight, ramanujanTau_twentynine,
      ramanujanTau_thirty, ramanujanTau_thirtyone, ramanujanTau_thirtytwo,
      ramanujanTau_thirtythree, ramanujanTau_thirtyfour, ramanujanTau_thirtyfive,
      ramanujanTau_thirtysix, ramanujanTau_thirtyseven, ramanujanTau_thirtyeight,
      ramanujanTau_thirtynine, ramanujanTau_forty, ramanujanTau_fortyone,
      ramanujanTau_fortytwo, ramanujanTau_fortythree, ramanujanTau_fortyfour,
      ramanujanTau_fortyfive, ramanujanTau_fortysix, ramanujanTau_fortyseven,
      ramanujanTau_fortyeight, ramanujanTau_fortynine, ramanujanTau_fifty] at * <;>
    norm_num at *

/-! ### Prime-power Hecke recursion checks -/

theorem ramanujanTau_hecke_two_three :
    ramanujanTau ℤ 16 = ramanujanTau ℤ 2 * ramanujanTau ℤ 8 - 2048 * ramanujanTau ℤ 4 := by
  rw [ramanujanTau_sixteen, ramanujanTau_two, ramanujanTau_eight, ramanujanTau_four]
  norm_num

theorem ramanujanTau_hecke_two_four :
    ramanujanTau ℤ 32 = ramanujanTau ℤ 2 * ramanujanTau ℤ 16 - 2048 * ramanujanTau ℤ 8 := by
  rw [ramanujanTau_thirtytwo, ramanujanTau_two, ramanujanTau_sixteen, ramanujanTau_eight]
  norm_num

theorem ramanujanTau_hecke_three_one :
    ramanujanTau ℤ 9 = ramanujanTau ℤ 3 * ramanujanTau ℤ 3 - 177147 * ramanujanTau ℤ 1 := by
  rw [ramanujanTau_nine, ramanujanTau_three, ramanujanTau_one]
  norm_num

theorem ramanujanTau_hecke_three_two :
    ramanujanTau ℤ 27 = ramanujanTau ℤ 3 * ramanujanTau ℤ 9 - 177147 * ramanujanTau ℤ 3 := by
  rw [ramanujanTau_twentyseven, ramanujanTau_three, ramanujanTau_nine]
  norm_num

theorem ramanujanTau_hecke_five_one :
    ramanujanTau ℤ 25 = ramanujanTau ℤ 5 * ramanujanTau ℤ 5 - 48828125 * ramanujanTau ℤ 1 := by
  rw [ramanujanTau_twentyfive, ramanujanTau_five, ramanujanTau_one]
  norm_num

theorem ramanujanTau_hecke_seven_one :
    ramanujanTau ℤ 49 =
      ramanujanTau ℤ 7 * ramanujanTau ℤ 7 - 1977326743 * ramanujanTau ℤ 1 := by
  rw [ramanujanTau_fortynine, ramanujanTau_seven, ramanujanTau_one]
  norm_num

theorem ramanujanTau_hecke_prime_power_le_50 (p r : Nat) (hp : Nat.Prime p) (hr : 1 ≤ r)
    (hle : p ^ (r + 1) ≤ 50) :
    ramanujanTau ℤ (p ^ (r + 1)) =
      ramanujanTau ℤ p * ramanujanTau ℤ (p ^ r) -
        (p ^ 11 : ℤ) * ramanujanTau ℤ (p ^ (r - 1)) := by
  have hp2 : 2 ≤ p := Nat.Prime.two_le hp
  have hp50 : p ≤ 50 := by
    have hpow : p ≤ p ^ (r + 1) := Nat.le_pow (a := p) (b := r + 1) (by omega)
    exact le_trans hpow hle
  have hr4 : r ≤ 4 := by
    have h2pow : 2 ^ (r + 1) ≤ p ^ (r + 1) := Nat.pow_le_pow_left hp2 (r + 1)
    have h2pow50 : 2 ^ (r + 1) ≤ 50 := le_trans h2pow hle
    by_contra hnot
    have hr5 : 5 ≤ r := by omega
    have h64 : 64 ≤ 2 ^ (r + 1) := by
      have hpow := Nat.pow_le_pow_right (n := 2) (by norm_num) (show 6 ≤ r + 1 by omega)
      norm_num at hpow
      exact hpow
    omega
  interval_cases p <;> interval_cases r <;>
    simp [ramanujanTau_zero, ramanujanTau_one, ramanujanTau_two, ramanujanTau_three,
      ramanujanTau_four, ramanujanTau_five, ramanujanTau_six, ramanujanTau_seven,
      ramanujanTau_eight, ramanujanTau_nine, ramanujanTau_ten, ramanujanTau_eleven,
      ramanujanTau_twelve, ramanujanTau_thirteen, ramanujanTau_fourteen,
      ramanujanTau_fifteen, ramanujanTau_sixteen, ramanujanTau_seventeen,
      ramanujanTau_eighteen, ramanujanTau_nineteen, ramanujanTau_twenty,
      ramanujanTau_twentyone, ramanujanTau_twentytwo, ramanujanTau_twentythree,
      ramanujanTau_twentyfour, ramanujanTau_twentyfive, ramanujanTau_twentysix,
      ramanujanTau_twentyseven, ramanujanTau_twentyeight, ramanujanTau_twentynine,
      ramanujanTau_thirty, ramanujanTau_thirtyone, ramanujanTau_thirtytwo,
      ramanujanTau_thirtythree, ramanujanTau_thirtyfour, ramanujanTau_thirtyfive,
      ramanujanTau_thirtysix, ramanujanTau_thirtyseven, ramanujanTau_thirtyeight,
      ramanujanTau_thirtynine, ramanujanTau_forty, ramanujanTau_fortyone,
      ramanujanTau_fortytwo, ramanujanTau_fortythree, ramanujanTau_fortyfour,
      ramanujanTau_fortyfive, ramanujanTau_fortysix, ramanujanTau_fortyseven,
      ramanujanTau_fortyeight, ramanujanTau_fortynine, ramanujanTau_fifty] at * <;>
    norm_num at *

/-! ### Parity and coefficient bounds through 50 -/

private theorem int_odd_iff_zmod_two_eq_one (z : ℤ) :
    Odd z ↔ ((z : ZMod 2) = 1) := by
  rw [Int.odd_iff]
  constructor
  · intro hz
    change (z : ZMod 2) = ((1 : ℤ) : ZMod 2)
    rw [ZMod.intCast_eq_intCast_iff]
    rw [Int.modEq_iff_dvd]
    omega
  · intro hz
    change (z : ZMod 2) = ((1 : ℤ) : ZMod 2) at hz
    rw [ZMod.intCast_eq_intCast_iff] at hz
    rw [Int.modEq_iff_dvd] at hz
    omega

private theorem odd_int_cast_zmod_two_eq_one (z : ℤ) (hz : Odd z) :
    ((z : ZMod 2) = 1) :=
  (int_odd_iff_zmod_two_eq_one z).mp hz

private theorem odd_jacobiTripleSign_triangular_zmod_two (r : Nat) :
    (((jacobiTripleSign (r * (r + 1) / 2) : ℤ) : ZMod 2) = 1) := by
  rw [jacobiTripleSign_triangular]
  apply odd_int_cast_zmod_two_eq_one
  have h1 : Odd ((-1 : ℤ) ^ r) := by
    induction r with
    | zero => simp
    | succ r ih =>
        rw [pow_succ]
        exact ih.mul (by simp)
  have h2 : Odd (((2 * r + 1 : Nat) : ℤ)) := by
    use r
    norm_num
  exact h1.mul h2

private theorem odd_square_eq_eight_triangular_add_one (r : Nat) :
    (2 * r + 1) ^ 2 = 8 * (r * (r + 1) / 2) + 1 := by
  have h2 := two_mul_triangular r
  change 2 * (r * (r + 1) / 2) = r * (r + 1) at h2
  nlinarith

private theorem powerSeries_pow_eight_eq_expand_eight_zmod_two (f : (ZMod 2)⟦X⟧) :
    f ^ 8 = PowerSeries.expand 8 (by norm_num) f := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  let hp2 : (2 : Nat) ≠ 0 := by norm_num
  let hp4 : (4 : Nat) ≠ 0 := by norm_num
  let hp8 : (8 : Nat) ≠ 0 := by norm_num
  have h2e : PowerSeries.expand 2 hp2 f = f ^ 2 :=
    PowerSeries.expand_eq_pow_zmod 2 hp2 f
  have h4 : f ^ 4 = PowerSeries.expand 4 hp4 f := by
    calc
      f ^ 4 = (f ^ 2) ^ 2 := by ring
      _ = (PowerSeries.expand 2 hp2 f) ^ 2 := by rw [← h2e]
      _ = PowerSeries.expand 2 hp2 (PowerSeries.expand 2 hp2 f) := by
        exact (PowerSeries.expand_eq_pow_zmod 2 hp2 (PowerSeries.expand 2 hp2 f)).symm
      _ = PowerSeries.expand 4 hp4 f := by
        have h := PowerSeries.expand_mul (p := 2) (q := 2) (hp := hp2) (hq := hp2) (φ := f)
        simpa [hp4] using h.symm
  have h4e : PowerSeries.expand 4 hp4 f = f ^ 4 := h4.symm
  calc
    f ^ 8 = (f ^ 4) ^ 2 := by ring
    _ = (PowerSeries.expand 4 hp4 f) ^ 2 := by rw [← h4e]
    _ = PowerSeries.expand 2 hp2 (PowerSeries.expand 4 hp4 f) := by
      exact (PowerSeries.expand_eq_pow_zmod 2 hp2 (PowerSeries.expand 4 hp4 f)).symm
    _ = PowerSeries.expand 8 hp8 f := by
      have h := PowerSeries.expand_mul (p := 2) (q := 4) (hp := hp2) (hq := hp4) (φ := f)
      simpa [hp8] using h.symm

private theorem discriminantPS_zmod_two_eq_X_mul_expand_eight_jacobiThetaPS :
    discriminantPS (ZMod 2) =
      PowerSeries.X * PowerSeries.expand 8 (by norm_num) (jacobiThetaPS (ZMod 2)) := by
  unfold discriminantPS etaPS
  have hB2 :=
    QseriesFormalization.Pending.JacobiCubeAnalyticToFormal.qPochInfPS_pow_three_eq_jacobiThetaPS
      (ZMod 2)
  have hpow : (qPochInfPS (ZMod 2)) ^ 24 = (jacobiThetaPS (ZMod 2)) ^ 8 := by
    calc
      (qPochInfPS (ZMod 2)) ^ 24 = ((qPochInfPS (ZMod 2)) ^ 3) ^ 8 := by ring
      _ = (jacobiThetaPS (ZMod 2)) ^ 8 := by rw [hB2]
  rw [hpow, powerSeries_pow_eight_eq_expand_eight_zmod_two]

private theorem coeff_expand_eight_jacobiThetaPS_zmod_two_eq_one (k : Nat) :
    (PowerSeries.expand 8 (by norm_num) (jacobiThetaPS (ZMod 2))).coeff k = 1 ↔
      ∃ r : Nat, k + 1 = (2 * r + 1) ^ 2 := by
  classical
  rw [PowerSeries.coeff_expand]
  constructor
  · intro hcoeff
    by_cases h8 : 8 ∣ k
    · rw [if_pos h8, coeff_jacobiThetaPS] at hcoeff
      by_cases htri : ∃ r ≤ k / 8, k / 8 = r * (r + 1) / 2
      · rcases htri with ⟨r, _hrle, hr⟩
        refine ⟨r, ?_⟩
        have hk : k = 8 * (r * (r + 1) / 2) := by
          calc
            k = 8 * (k / 8) := (Nat.mul_div_cancel' h8).symm
            _ = 8 * (r * (r + 1) / 2) := by rw [hr]
        rw [hk, ← odd_square_eq_eight_triangular_add_one]
      · push_neg at htri
        rw [jacobiTripleSign_of_not_triangular (k / 8) htri] at hcoeff
        norm_num at hcoeff
    · rw [if_neg h8] at hcoeff
      norm_num at hcoeff
  · rintro ⟨r, hr⟩
    have hk : k = 8 * (r * (r + 1) / 2) := by
      have hs := odd_square_eq_eight_triangular_add_one r
      omega
    have h8 : 8 ∣ k := by
      exact ⟨r * (r + 1) / 2, hk⟩
    have hdiv : k / 8 = r * (r + 1) / 2 := by
      rw [hk]
      exact Nat.mul_div_right _ (by norm_num)
    rw [if_pos h8, hdiv, coeff_jacobiThetaPS]
    exact odd_jacobiTripleSign_triangular_zmod_two r

theorem ramanujanTau_mod_two_eq_one_iff_odd_square (n : Nat) :
    ramanujanTau (ZMod 2) n = 1 ↔ ∃ r : Nat, n = (2 * r + 1) ^ 2 := by
  unfold ramanujanTau
  rw [discriminantPS_zmod_two_eq_X_mul_expand_eight_jacobiThetaPS]
  cases n with
  | zero =>
      have hcoeff : (PowerSeries.X * PowerSeries.expand 8 (by norm_num)
          (jacobiThetaPS (ZMod 2))).coeff 0 = 0 := by
        simp [PowerSeries.coeff_zero_eq_constantCoeff]
      rw [hcoeff]
      constructor
      · intro h
        norm_num at h
      · rintro ⟨r, hr⟩
        have hpos : 0 < (2 * r + 1) ^ 2 := by positivity
        omega
  | succ k =>
      rw [PowerSeries.coeff_succ_X_mul]
      exact coeff_expand_eight_jacobiThetaPS_zmod_two_eq_one k

private theorem map_discriminantPS_int_zmod_two :
    PowerSeries.map (Int.castRingHom (ZMod 2)) (discriminantPS ℤ) =
      discriminantPS (ZMod 2) := by
  unfold discriminantPS etaPS
  rw [map_mul, map_pow, map_qPochInfPS, PowerSeries.map_X]

private theorem ramanujanTau_int_cast_zmod_two (n : Nat) :
    (((ramanujanTau ℤ n : ℤ) : ZMod 2) = ramanujanTau (ZMod 2) n) := by
  unfold ramanujanTau
  have h := congrArg (fun f : (ZMod 2)⟦X⟧ => f.coeff n) map_discriminantPS_int_zmod_two
  change (PowerSeries.map (Int.castRingHom (ZMod 2)) (discriminantPS ℤ)).coeff n =
    (discriminantPS (ZMod 2)).coeff n at h
  rw [PowerSeries.coeff_map] at h
  exact h

theorem ramanujanTau_odd_iff_odd_square_param (n : Nat) :
    Odd (ramanujanTau ℤ n) ↔ ∃ r : Nat, n = (2 * r + 1) ^ 2 := by
  rw [int_odd_iff_zmod_two_eq_one]
  rw [ramanujanTau_int_cast_zmod_two]
  exact ramanujanTau_mod_two_eq_one_iff_odd_square n

theorem ramanujanTau_odd_iff_odd_square (n : Nat) :
    Odd (ramanujanTau ℤ n) ↔ ∃ m : Nat, Odd m ∧ n = m ^ 2 := by
  rw [ramanujanTau_odd_iff_odd_square_param]
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨2 * r + 1, ?_, hr⟩
    exact ⟨r, rfl⟩
  · rintro ⟨m, hm, hm2⟩
    rcases hm with ⟨r, rfl⟩
    exact ⟨r, hm2⟩

/-- Direct parity pattern through 50: `τ(n)` is odd exactly at `1, 9, 25, 49`. -/
theorem ramanujanTau_odd_iff_odd_square_through_fifty (n : Nat) (hn : n ≤ 50) :
    Odd (ramanujanTau ℤ n) ↔ n = 1 ∨ n = 9 ∨ n = 25 ∨ n = 49 := by
  interval_cases n <;>
    simp [ramanujanTau_zero, ramanujanTau_one, ramanujanTau_two, ramanujanTau_three,
      ramanujanTau_four, ramanujanTau_five, ramanujanTau_six, ramanujanTau_seven,
      ramanujanTau_eight, ramanujanTau_nine, ramanujanTau_ten, ramanujanTau_eleven,
      ramanujanTau_twelve, ramanujanTau_thirteen, ramanujanTau_fourteen,
      ramanujanTau_fifteen, ramanujanTau_sixteen, ramanujanTau_seventeen,
      ramanujanTau_eighteen, ramanujanTau_nineteen, ramanujanTau_twenty,
      ramanujanTau_twentyone, ramanujanTau_twentytwo, ramanujanTau_twentythree,
      ramanujanTau_twentyfour, ramanujanTau_twentyfive, ramanujanTau_twentysix,
      ramanujanTau_twentyseven, ramanujanTau_twentyeight, ramanujanTau_twentynine,
      ramanujanTau_thirty, ramanujanTau_thirtyone, ramanujanTau_thirtytwo,
      ramanujanTau_thirtythree, ramanujanTau_thirtyfour, ramanujanTau_thirtyfive,
      ramanujanTau_thirtysix, ramanujanTau_thirtyseven, ramanujanTau_thirtyeight,
      ramanujanTau_thirtynine, ramanujanTau_forty, ramanujanTau_fortyone,
      ramanujanTau_fortytwo, ramanujanTau_fortythree, ramanujanTau_fortyfour,
      ramanujanTau_fortyfive, ramanujanTau_fortysix, ramanujanTau_fortyseven,
      ramanujanTau_fortyeight, ramanujanTau_fortynine, ramanujanTau_fifty] <;>
    norm_num

/-- Crude verified coefficient bound through 50, attained at `τ(47)`. -/
theorem ramanujanTau_abs_le_through_fifty (n : Nat) (hn : n ≤ 50) :
    |ramanujanTau ℤ n| ≤ (2687348496 : ℤ) := by
  interval_cases n <;>
    simp [ramanujanTau_zero, ramanujanTau_one, ramanujanTau_two, ramanujanTau_three,
      ramanujanTau_four, ramanujanTau_five, ramanujanTau_six, ramanujanTau_seven,
      ramanujanTau_eight, ramanujanTau_nine, ramanujanTau_ten, ramanujanTau_eleven,
      ramanujanTau_twelve, ramanujanTau_thirteen, ramanujanTau_fourteen,
      ramanujanTau_fifteen, ramanujanTau_sixteen, ramanujanTau_seventeen,
      ramanujanTau_eighteen, ramanujanTau_nineteen, ramanujanTau_twenty,
      ramanujanTau_twentyone, ramanujanTau_twentytwo, ramanujanTau_twentythree,
      ramanujanTau_twentyfour, ramanujanTau_twentyfive, ramanujanTau_twentysix,
      ramanujanTau_twentyseven, ramanujanTau_twentyeight, ramanujanTau_twentynine,
      ramanujanTau_thirty, ramanujanTau_thirtyone, ramanujanTau_thirtytwo,
      ramanujanTau_thirtythree, ramanujanTau_thirtyfour, ramanujanTau_thirtyfive,
      ramanujanTau_thirtysix, ramanujanTau_thirtyseven, ramanujanTau_thirtyeight,
      ramanujanTau_thirtynine, ramanujanTau_forty, ramanujanTau_fortyone,
      ramanujanTau_fortytwo, ramanujanTau_fortythree, ramanujanTau_fortyfour,
      ramanujanTau_fortyfive, ramanujanTau_fortysix, ramanujanTau_fortyseven,
      ramanujanTau_fortyeight, ramanujanTau_fortynine, ramanujanTau_fifty]

/-- Finite Lehmer verification through 50: none of `τ(1), ..., τ(50)` vanishes. -/
theorem ramanujanTau_ne_zero_through_fifty (n : Nat) (hn0 : 1 ≤ n) (hn50 : n ≤ 50) :
    ramanujanTau ℤ n ≠ 0 := by
  interval_cases n <;>
    simp [ramanujanTau_one, ramanujanTau_two, ramanujanTau_three, ramanujanTau_four,
      ramanujanTau_five, ramanujanTau_six, ramanujanTau_seven, ramanujanTau_eight,
      ramanujanTau_nine, ramanujanTau_ten, ramanujanTau_eleven, ramanujanTau_twelve,
      ramanujanTau_thirteen, ramanujanTau_fourteen, ramanujanTau_fifteen,
      ramanujanTau_sixteen, ramanujanTau_seventeen, ramanujanTau_eighteen,
      ramanujanTau_nineteen, ramanujanTau_twenty, ramanujanTau_twentyone,
      ramanujanTau_twentytwo, ramanujanTau_twentythree, ramanujanTau_twentyfour,
      ramanujanTau_twentyfive, ramanujanTau_twentysix, ramanujanTau_twentyseven,
      ramanujanTau_twentyeight, ramanujanTau_twentynine, ramanujanTau_thirty,
      ramanujanTau_thirtyone, ramanujanTau_thirtytwo, ramanujanTau_thirtythree,
      ramanujanTau_thirtyfour, ramanujanTau_thirtyfive, ramanujanTau_thirtysix,
      ramanujanTau_thirtyseven, ramanujanTau_thirtyeight, ramanujanTau_thirtynine,
      ramanujanTau_forty, ramanujanTau_fortyone, ramanujanTau_fortytwo,
      ramanujanTau_fortythree, ramanujanTau_fortyfour, ramanujanTau_fortyfive,
      ramanujanTau_fortysix, ramanujanTau_fortyseven, ramanujanTau_fortyeight,
      ramanujanTau_fortynine, ramanujanTau_fifty]

/-! ### Ramanujan's mod-691 congruence through 50 -/

theorem ramanujanTau_congr_sigma11_mod_691_through_fifty (n : Nat) (hn : n ≤ 50) :
    (ramanujanTau ℤ n : ZMod 691) = (sigma11 n : ZMod 691) := by
  interval_cases n <;>
    simp [sigma11, Nat.divisorSum, ramanujanTau_zero, ramanujanTau_one,
      ramanujanTau_two, ramanujanTau_three, ramanujanTau_four, ramanujanTau_five,
      ramanujanTau_six, ramanujanTau_seven, ramanujanTau_eight, ramanujanTau_nine,
      ramanujanTau_ten, ramanujanTau_eleven, ramanujanTau_twelve, ramanujanTau_thirteen,
      ramanujanTau_fourteen, ramanujanTau_fifteen, ramanujanTau_sixteen,
      ramanujanTau_seventeen, ramanujanTau_eighteen, ramanujanTau_nineteen,
      ramanujanTau_twenty, ramanujanTau_twentyone, ramanujanTau_twentytwo,
      ramanujanTau_twentythree, ramanujanTau_twentyfour, ramanujanTau_twentyfive,
      ramanujanTau_twentysix, ramanujanTau_twentyseven, ramanujanTau_twentyeight,
      ramanujanTau_twentynine, ramanujanTau_thirty, ramanujanTau_thirtyone,
      ramanujanTau_thirtytwo, ramanujanTau_thirtythree, ramanujanTau_thirtyfour,
      ramanujanTau_thirtyfive, ramanujanTau_thirtysix, ramanujanTau_thirtyseven,
      ramanujanTau_thirtyeight, ramanujanTau_thirtynine, ramanujanTau_forty,
      ramanujanTau_fortyone, ramanujanTau_fortytwo, ramanujanTau_fortythree,
      ramanujanTau_fortyfour, ramanujanTau_fortyfive, ramanujanTau_fortysix,
      ramanujanTau_fortyseven, ramanujanTau_fortyeight, ramanujanTau_fortynine,
      ramanujanTau_fifty] <;>
    native_decide

/-- The mod-691 reduction of the integral weight-12 Eisenstein coefficient series
`B₁₂/24 + ∑ σ₁₁(n) X^n`.  The Bernoulli constant term vanishes modulo 691, and
our local `sigma11` convention also has `sigma11 0 = 0`. -/
noncomputable def eisensteinE12PSMod691 : (ZMod 691)⟦X⟧ :=
  PowerSeries.mk fun n => (sigma11 n : ZMod 691)

@[simp] theorem coeff_eisensteinE12PSMod691 (n : Nat) :
    eisensteinE12PSMod691.coeff n = (sigma11 n : ZMod 691) := by
  simp [eisensteinE12PSMod691]

@[simp] theorem coeff_zero_eisensteinE12PSMod691 :
    eisensteinE12PSMod691.coeff 0 = 0 := by
  simp [sigma11, Nat.divisorSum]

/-! #### Formal Eisenstein series for the mod-691 route -/

/-- The divisor power sum `sigma_r(n) = sum_{d | n} d^r`, with value `0` at `n = 0`. -/
def sigmaPower (r n : Nat) : Nat :=
  Nat.divisorSum n (fun d => d ^ r)

@[simp] theorem sigmaPower_eleven (n : Nat) :
    sigmaPower 11 n = sigma11 n := rfl

/-- The formal series `S_r = sum_{n >= 0} sigma_r(n) X^n`. -/
noncomputable def divisorSigmaPowerPS (R : Type*) [CommRing R] (r : Nat) : R⟦X⟧ :=
  PowerSeries.mk fun n => (sigmaPower r n : R)

@[simp] theorem coeff_divisorSigmaPowerPS
    (R : Type*) [CommRing R] (r n : Nat) :
    (divisorSigmaPowerPS R r).coeff n = (sigmaPower r n : R) := by
  simp [divisorSigmaPowerPS]

/-- The formal Eisenstein series `E_4 = 1 + 240 S_3`. -/
noncomputable def eisensteinE4PS (R : Type*) [CommRing R] : R⟦X⟧ :=
  1 + (240 : R⟦X⟧) * divisorSigmaPowerPS R 3

/-- The formal Eisenstein series `E_6 = 1 - 504 S_5`. -/
noncomputable def eisensteinE6PS (R : Type*) [CommRing R] : R⟦X⟧ :=
  1 - (504 : R⟦X⟧) * divisorSigmaPowerPS R 5

/-- The nonconstant part of the normalized weight-12 Eisenstein series. -/
noncomputable def eisensteinS11PS (R : Type*) [CommRing R] : R⟦X⟧ :=
  divisorSigmaPowerPS R 11

@[simp] theorem coeff_eisensteinS11PS
    (R : Type*) [CommRing R] (n : Nat) :
    (eisensteinS11PS R).coeff n = (sigma11 n : R) := by
  simp [eisensteinS11PS]

theorem eisensteinE12PSMod691_eq_eisensteinS11PS :
    eisensteinE12PSMod691 = eisensteinS11PS (ZMod 691) := by
  ext n
  simp [eisensteinE12PSMod691]

/-- The quasimodular Eisenstein series `E_2 = 1 - 24 S_1`. -/
noncomputable def eisensteinE2PS (R : Type*) [CommRing R] : R⟦X⟧ :=
  1 - (24 : R⟦X⟧) * divisorSigmaPowerPS R 1

/-- Target formal identity `E_4^3 - E_6^2 = 1728 Delta`. -/
def eisensteinDeltaIdentity (R : Type*) [CommRing R] : Prop :=
  eisensteinE4PS R ^ 3 - eisensteinE6PS R ^ 2 =
    (1728 : R⟦X⟧) * discriminantPS R

/-- Target weight-12 linear relation
`441 E_4^3 + 250 E_6^2 = 691 + 65520 S_11`. -/
def eisensteinWeight12LinearIdentity (R : Type*) [CommRing R] : Prop :=
  (441 : R⟦X⟧) * eisensteinE4PS R ^ 3 +
      (250 : R⟦X⟧) * eisensteinE6PS R ^ 2 =
    (691 : R⟦X⟧) + (65520 : R⟦X⟧) * eisensteinS11PS R

/-- Ramanujan's theta equation for `E_4`, written without division. -/
def ramanujanThetaE4Equation : Prop :=
  (3 : ℚ⟦X⟧) * thetaOp (eisensteinE4PS ℚ) =
    eisensteinE2PS ℚ * eisensteinE4PS ℚ - eisensteinE6PS ℚ

/-- Ramanujan's theta equation for `E_6`, written without division. -/
def ramanujanThetaE6Equation : Prop :=
  (2 : ℚ⟦X⟧) * thetaOp (eisensteinE6PS ℚ) =
    eisensteinE2PS ℚ * eisensteinE6PS ℚ - eisensteinE4PS ℚ ^ 2

theorem coeff_thetaOp_divisorSigmaPowerPS
    (R : Type*) [CommRing R] (r n : Nat) :
    (thetaOp (divisorSigmaPowerPS R r)).coeff n =
      (sigmaPower r n : R) * (n : R) := by
  rw [coeff_thetaOp]
  simp

theorem coeff_thetaOp_eisensteinE4PS_rat (n : Nat) :
    (thetaOp (eisensteinE4PS ℚ)).coeff n =
      (240 : ℚ) * (sigmaPower 3 n : ℚ) * (n : ℚ) := by
  rw [eisensteinE4PS, thetaOp_add, thetaOp_one]
  change (0 + thetaOp (PowerSeries.C (240 : ℚ) * divisorSigmaPowerPS ℚ 3)).coeff n =
    (240 : ℚ) * (sigmaPower 3 n : ℚ) * (n : ℚ)
  rw [thetaOp_C_mul]
  simp [coeff_thetaOp_divisorSigmaPowerPS]
  ring

theorem coeff_thetaOp_eisensteinE6PS_rat (n : Nat) :
    (thetaOp (eisensteinE6PS ℚ)).coeff n =
      -(504 : ℚ) * (sigmaPower 5 n : ℚ) * (n : ℚ) := by
  rw [eisensteinE6PS, thetaOp_sub, thetaOp_one]
  change (0 - thetaOp (PowerSeries.C (504 : ℚ) * divisorSigmaPowerPS ℚ 5)).coeff n =
    -(504 : ℚ) * (sigmaPower 5 n : ℚ) * (n : ℚ)
  rw [thetaOp_C_mul]
  simp [coeff_thetaOp_divisorSigmaPowerPS]
  ring

/-- `sigma11` computed directly in `ZMod 691`, avoiding huge natural powers in
the finite certificates below. -/
def sigma11Mod691 (n : Nat) : ZMod 691 :=
  ∑ d ∈ Finset.Icc 1 n, if d ∣ n then (d : ZMod 691) ^ 11 else 0

theorem sigma11Mod691_eq_sigma11 (n : Nat) :
    sigma11Mod691 n = (sigma11 n : ZMod 691) := by
  unfold sigma11Mod691 sigma11 Nat.divisorSum
  push_cast
  apply Finset.sum_congr rfl
  intro d _
  by_cases h : d ∣ n <;> simp [h]

/-- One truncated convolution step for `(q;q)_∞^k` directly over `ZMod 691`.
This avoids the very large integer coefficients produced by `tauEtaPowVec`. -/
def tauEtaPowStepMod691 (N : Nat) (v : Vector (ZMod 691) (N + 1)) :
    Vector (ZMod 691) (N + 1) :=
  Vector.ofFn fun j : Fin (N + 1) =>
    ∑ i : Fin (j.1 + 1),
      v.get ⟨i.1, by omega⟩ * (tauEtaCoeffZ (j.1 - i.1) : ZMod 691)

/-- Coefficients `0..N` of `(q;q)_∞^k`, reduced modulo 691. -/
def tauEtaPowVecMod691 (N : Nat) : Nat → Vector (ZMod 691) (N + 1)
  | 0 => Vector.ofFn fun j : Fin (N + 1) => if j.1 = 0 then 1 else 0
  | k + 1 => tauEtaPowStepMod691 N (tauEtaPowVecMod691 N k)

theorem tauEtaPowVecMod691_spec (N k : Nat) :
    ∀ j : Fin (N + 1),
      (tauEtaPowVecMod691 N k).get j =
        ((etaPS (ZMod 691)) ^ k).coeff j.1 := by
  induction k with
  | zero =>
      intro j
      rw [tauEtaPowVecMod691, Vector.get_ofFn]
      by_cases h : j.1 = 0 <;> simp [h, PowerSeries.coeff_one]
  | succ k ih =>
      intro j
      rw [tauEtaPowVecMod691, tauEtaPowStepMod691, Vector.get_ofFn]
      rw [pow_succ, PowerSeries.coeff_mul]
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (f := fun a b =>
          ((etaPS (ZMod 691)) ^ k).coeff a * (etaPS (ZMod 691)).coeff b) j.1]
      rw [← Fin.sum_univ_eq_sum_range
        (fun i =>
          ((etaPS (ZMod 691)) ^ k).coeff i *
            (etaPS (ZMod 691)).coeff (j.1 - i)) (j.1 + 1)]
      apply Finset.sum_congr rfl
      intro i _
      rw [ih ⟨i.1, by omega⟩]
      rw [coeff_etaPS_eq_tauEtaCoeffZ]

theorem ramanujanTau_succ_eq_tauEtaPowVecMod691 {N n : Nat} (hN : n < N + 1) :
    ramanujanTau (ZMod 691) (n + 1) =
      (tauEtaPowVecMod691 N 24).get ⟨n, hN⟩ := by
  unfold ramanujanTau discriminantPS
  rw [PowerSeries.coeff_succ_X_mul]
  rw [tauEtaPowVecMod691_spec N 24 ⟨n, hN⟩]

def ramanujanTauCoeffMod691FromVec (N n : Nat) (v : Vector (ZMod 691) (N + 1)) :
    ZMod 691 :=
  if n = 0 then 0
  else if h : n - 1 < N + 1 then v.get ⟨n - 1, h⟩
  else 0

theorem ramanujanTau_eq_tauCoeffMod691FromVec (N n : Nat) (hn : n ≤ N + 1) :
    ramanujanTau (ZMod 691) n =
      ramanujanTauCoeffMod691FromVec N n (tauEtaPowVecMod691 N 24) := by
  cases n with
  | zero =>
      simp [ramanujanTauCoeffMod691FromVec]
  | succ n =>
      have hnN : n < N + 1 := by omega
      simp [ramanujanTauCoeffMod691FromVec, hnN, ramanujanTau_succ_eq_tauEtaPowVecMod691 hnN]

theorem tauCoeffMod691_congr_sigma11_mod691_through_two_hundred :
    (let v := tauEtaPowVecMod691 199 24
     ∀ i : Fin (200 + 1),
      ramanujanTauCoeffMod691FromVec 199 i.1 v = sigma11Mod691 i.1) := by
  native_decide

/-- Finite certificate for Ramanujan's mod-691 congruence through `n = 300`.
The computation is carried out entirely in `ZMod 691`. -/
theorem tauCoeffMod691_congr_sigma11_mod691_through_three_hundred :
    (let v := tauEtaPowVecMod691 299 24
     ∀ i : Fin (300 + 1),
      ramanujanTauCoeffMod691FromVec 299 i.1 v = sigma11Mod691 i.1) := by
  native_decide

/-- Finite certificate that no `τ(n)` with `1 ≤ n ≤ 300` vanishes modulo `691`. -/
theorem tauCoeffMod691_ne_zero_through_three_hundred :
    (let v := tauEtaPowVecMod691 299 24
     ∀ i : Fin 300,
      ramanujanTauCoeffMod691FromVec 299 (i.1 + 1) v ≠ 0) := by
  native_decide

/-! ### Log-derivative recurrence -/

noncomputable def divisorGeomPS (R : Type*) [CommRing R] (d : Nat) : R⟦X⟧ :=
  PowerSeries.mk fun n => if d ∣ n ∧ 0 < n then (1 : R) else 0

@[simp] theorem coeff_divisorGeomPS (R : Type*) [CommRing R] (d n : Nat) :
    (divisorGeomPS R d).coeff n = if d ∣ n ∧ 0 < n then (1 : R) else 0 := by
  simp [divisorGeomPS]

private theorem coeff_X_pow_mul_eq_zero_of_lt (R : Type*) [CommRing R]
    (G : R⟦X⟧) {d n : Nat} (hnd : n < d) :
    (PowerSeries.X ^ d * G).coeff n = 0 := by
  rw [PowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro x hx
  rw [PowerSeries.coeff_X_pow]
  split_ifs with hx1
  · have hsum := Finset.mem_antidiagonal.mp hx
    omega
  · simp

private theorem coeff_X_pow_mul_cases (R : Type*) [CommRing R]
    (G : R⟦X⟧) (d n : Nat) :
    (PowerSeries.X ^ d * G).coeff n = if d ≤ n then G.coeff (n - d) else 0 := by
  by_cases hdn : d ≤ n
  · have h := PowerSeries.coeff_X_pow_mul G d (n - d)
    rw [if_pos hdn]
    simpa [Nat.sub_add_cancel hdn, Nat.add_comm] using h
  · rw [if_neg hdn]
    exact coeff_X_pow_mul_eq_zero_of_lt R G (Nat.lt_of_not_ge hdn)

theorem one_sub_X_pow_mul_divisorGeomPS (R : Type*) [CommRing R] {d : Nat} (hd : 0 < d) :
    ((1 : R⟦X⟧) - PowerSeries.X ^ d) * divisorGeomPS R d = PowerSeries.X ^ d := by
  ext n
  rw [sub_mul]
  simp only [map_sub]
  rw [coeff_X_pow_mul_cases R (divisorGeomPS R d) d n]
  rw [PowerSeries.coeff_X_pow]
  by_cases hn0 : n = 0
  · subst n
    have hz : ¬ 0 = d := by omega
    simp [hz]
  by_cases hdn : d ≤ n
  · rw [if_pos hdn]
    by_cases hnd : n = d
    · subst n
      simp [hd]
    · have hlt : d < n := lt_of_le_of_ne hdn (Ne.symm hnd)
      have hn_minus_pos : 0 < n - d := Nat.sub_pos_of_lt hlt
      by_cases hdiv : d ∣ n
      · have hdiv_sub : d ∣ n - d := by
          rcases hdiv with ⟨a, ha⟩
          have ha_pos : 0 < a := by
            by_contra haz
            have ha0 : a = 0 := Nat.eq_zero_of_not_pos haz
            simp [ha0] at ha
            omega
          refine ⟨a - 1, ?_⟩
          calc
            n - d = d * a - d := by rw [ha]
            _ = d * a - d * 1 := by simp
            _ = d * (a - 1) := by rw [← Nat.mul_sub_left_distrib]
        have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
        simp [hdiv, hdiv_sub, hn_minus_pos, hnpos, hnd]
      · have hdiv_sub_false : ¬ d ∣ n - d := by
          intro hs
          apply hdiv
          rcases hs with ⟨a, ha⟩
          refine ⟨a + 1, ?_⟩
          calc
            n = (n - d) + d := (Nat.sub_add_cancel hdn).symm
            _ = d * a + d := by rw [ha]
            _ = d * (a + 1) := by ring
        simp [hdiv, hdiv_sub_false, hn_minus_pos, hnd]
  · rw [if_neg hdn]
    have hx : ¬ (d ∣ n ∧ 0 < n) := by
      intro h
      exact hdn (Nat.le_of_dvd h.2 h.1)
    have hne : ¬ n = d := by omega
    simp [hx, hne]

noncomputable def qPochFinitePS (R : Type*) [CommRing R] (N : Nat) : R⟦X⟧ :=
  ∏ i ∈ Finset.range N, ((1 : R⟦X⟧) - PowerSeries.X ^ (i + 1))

noncomputable def finiteDivisorSigmaPS (R : Type*) [CommRing R] (N : Nat) : R⟦X⟧ :=
  PowerSeries.mk fun n =>
    ∑ d ∈ Finset.Icc 1 N, if d ∣ n ∧ 0 < n then ((d : Nat) : R) else 0

@[simp] theorem coeff_finiteDivisorSigmaPS (R : Type*) [CommRing R] (N n : Nat) :
    (finiteDivisorSigmaPS R N).coeff n =
      ∑ d ∈ Finset.Icc 1 N, if d ∣ n ∧ 0 < n then ((d : Nat) : R) else 0 := by
  simp [finiteDivisorSigmaPS]

theorem finiteDivisorSigmaPS_succ (R : Type*) [CommRing R] (N : Nat) :
    finiteDivisorSigmaPS R (N + 1) =
      finiteDivisorSigmaPS R N +
        PowerSeries.C (((N + 1 : Nat) : R)) * divisorGeomPS R (N + 1) := by
  ext n
  rw [coeff_finiteDivisorSigmaPS, map_add, PowerSeries.coeff_C_mul, coeff_divisorGeomPS,
    coeff_finiteDivisorSigmaPS]
  rw [Finset.sum_Icc_succ_top (show 1 ≤ N + 1 by omega)]
  by_cases h : (N + 1) ∣ n ∧ 0 < n <;> simp [h]

theorem thetaOp_X_pow (R : Type*) [CommRing R] (d : Nat) :
    thetaOp (PowerSeries.X ^ d : R⟦X⟧) = PowerSeries.C (d : R) * PowerSeries.X ^ d := by
  ext n
  rw [coeff_thetaOp, PowerSeries.coeff_C_mul]
  rw [PowerSeries.coeff_X_pow]
  split_ifs with h <;> subst_vars <;> simp

/-- In characteristic 691, the Euler theta operator has nontrivial kernel:
`θ(1 + X^691) = 0`.  This is the obstruction to proving the full mod-691
identity from the first-order log-derivative recurrence alone. -/
theorem thetaOp_one_add_X_pow_691_mod_691 :
    thetaOp ((1 : (ZMod 691)⟦X⟧) + PowerSeries.X ^ 691) = 0 := by
  rw [thetaOp_add, thetaOp_one, thetaOp_X_pow]
  have h691 : (691 : ZMod 691) = 0 := by decide
  simp [h691]

/-- Multiplication by `1 + X^691` preserves any equation of the form
`θ F = F * A` over `ZMod 691`.  Thus a log-derivative recurrence in
characteristic 691 is not a uniqueness principle without extra information at
the Frobenius-obstruction coefficients. -/
theorem thetaOp_equation_mul_one_add_X_pow_691_mod_691
    {F A : (ZMod 691)⟦X⟧} (hF : thetaOp F = F * A) :
    thetaOp (F * ((1 : (ZMod 691)⟦X⟧) + PowerSeries.X ^ 691)) =
      (F * ((1 : (ZMod 691)⟦X⟧) + PowerSeries.X ^ 691)) * A := by
  rw [thetaOp_mul, thetaOp_one_add_X_pow_691_mod_691, hF]
  simp only [mul_zero, zero_add]
  ac_rfl

theorem thetaOp_one_sub_X_pow (R : Type*) [CommRing R] (d : Nat) :
    thetaOp ((1 : R⟦X⟧) - PowerSeries.X ^ d) =
      -PowerSeries.C (d : R) * PowerSeries.X ^ d := by
  rw [thetaOp_sub, thetaOp_one, thetaOp_X_pow]
  ring

theorem qPochFinitePS_succ (R : Type*) [CommRing R] (N : Nat) :
    qPochFinitePS R (N + 1) =
      qPochFinitePS R N * ((1 : R⟦X⟧) - PowerSeries.X ^ (N + 1)) := by
  simp [qPochFinitePS, Finset.prod_range_succ]

theorem thetaOp_qPochFinitePS (R : Type*) [CommRing R] (N : Nat) :
    thetaOp (qPochFinitePS R N) =
      -qPochFinitePS R N * finiteDivisorSigmaPS R N := by
  induction N with
  | zero =>
      have hzero : finiteDivisorSigmaPS R 0 = 0 := by
        ext n
        simp [finiteDivisorSigmaPS]
      simp [qPochFinitePS, hzero]
  | succ N ih =>
      rw [qPochFinitePS_succ, finiteDivisorSigmaPS_succ]
      rw [thetaOp_mul, thetaOp_one_sub_X_pow, ih]
      have hgeom := one_sub_X_pow_mul_divisorGeomPS R (d := N + 1) (by omega)
      calc
        (qPochFinitePS R N * (-C ↑(N + 1) * X ^ (N + 1)) +
            ((1 : R⟦X⟧) - X ^ (N + 1)) * (-qPochFinitePS R N * finiteDivisorSigmaPS R N))
            = -qPochFinitePS R N * finiteDivisorSigmaPS R N * ((1 : R⟦X⟧) - X ^ (N + 1)) +
              -qPochFinitePS R N * (C ↑(N + 1) * X ^ (N + 1)) := by ring
        _ = -qPochFinitePS R N * finiteDivisorSigmaPS R N * ((1 : R⟦X⟧) - X ^ (N + 1)) +
              -qPochFinitePS R N *
                (C ↑(N + 1) * (((1 : R⟦X⟧) - X ^ (N + 1)) * divisorGeomPS R (N + 1))) := by
                rw [hgeom]
        _ = -(qPochFinitePS R N * ((1 : R⟦X⟧) - X ^ (N + 1))) *
              (finiteDivisorSigmaPS R N + C ↑(N + 1) * divisorGeomPS R (N + 1)) := by ring

noncomputable def divisorSigmaPS (R : Type*) [CommRing R] : R⟦X⟧ :=
  PowerSeries.mk fun n => ((Nat.divisorSum n id : Nat) : R)

@[simp] theorem coeff_divisorSigmaPS (R : Type*) [CommRing R] (n : Nat) :
    (divisorSigmaPS R).coeff n = ((Nat.divisorSum n id : Nat) : R) := by
  simp [divisorSigmaPS]

theorem coeff_finiteDivisorSigmaPS_eq_divisorSum
    (R : Type*) [CommRing R] {N n : Nat} (hnN : n ≤ N) :
    (finiteDivisorSigmaPS R N).coeff n = (Nat.divisorSum n id : R) := by
  rw [coeff_finiteDivisorSigmaPS, Nat.divisorSum]
  by_cases hn0 : n = 0
  · subst n
    simp
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    have hsubset : Finset.Icc 1 n ⊆ Finset.Icc 1 N := by
      intro d hd
      rw [Finset.mem_Icc] at hd ⊢
      exact ⟨hd.1, le_trans hd.2 hnN⟩
    rw [Finset.sum_subset hsubset]
    · push_cast
      apply Finset.sum_congr rfl
      intro d hd
      simp [hnpos]
    · intro d hdN hdnot
      rw [Finset.mem_Icc] at hdN
      have hdn : n < d := by
        have hnotle : ¬ d ≤ n := by
          intro hle
          exact hdnot (by rw [Finset.mem_Icc]; exact ⟨hdN.1, hle⟩)
        omega
      have hnotdiv : ¬ d ∣ n := by
        intro hdiv
        have dle : d ≤ n := Nat.le_of_dvd hnpos hdiv
        omega
      simp [hnotdiv]

theorem coeff_etaPS_eq_qPochFinitePS (k N : Nat) (hkN : k < N) :
    (etaPS ℤ).coeff k = (qPochFinitePS ℤ N).coeff k := by
  unfold etaPS qPochFinitePS
  exact QseriesFormalization.PartIV.Ch19.coeff_qPochInfPS_eq_coeff_finite_product_of_lt ℤ k N hkN

theorem coeff_qPochFinitePS_mul_finiteDivisorSigmaPS_eq_etaPS_mul_divisorSigmaPS
    (n N : Nat) (hN : n < N) :
    (qPochFinitePS ℤ N * finiteDivisorSigmaPS ℤ N).coeff n =
      (etaPS ℤ * divisorSigmaPS ℤ).coeff n := by
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have hp_sum : p.1 + p.2 = n := Finset.mem_antidiagonal.mp hp
  have hp1 : p.1 < N := by omega
  have hp2 : p.2 ≤ N := by omega
  rw [← coeff_etaPS_eq_qPochFinitePS p.1 N hp1]
  rw [coeff_finiteDivisorSigmaPS_eq_divisorSum ℤ (N := N) (n := p.2) hp2]
  rw [coeff_divisorSigmaPS]

theorem thetaOp_etaPS_eq_neg_etaPS_mul_divisorSigmaPS :
    thetaOp (etaPS ℤ) = -etaPS ℤ * divisorSigmaPS ℤ := by
  ext n
  let N := n + 1
  have hN : n < N := by omega
  have hfin := congrArg (fun f : ℤ⟦X⟧ => f.coeff n) (thetaOp_qPochFinitePS ℤ N)
  have hleft : (thetaOp (etaPS ℤ)).coeff n =
      (thetaOp (qPochFinitePS ℤ N)).coeff n := by
    rw [coeff_thetaOp, coeff_thetaOp, coeff_etaPS_eq_qPochFinitePS n N hN]
  have hprod := coeff_qPochFinitePS_mul_finiteDivisorSigmaPS_eq_etaPS_mul_divisorSigmaPS n N hN
  calc
    (thetaOp (etaPS ℤ)).coeff n
        = (thetaOp (qPochFinitePS ℤ N)).coeff n := hleft
    _ = (-qPochFinitePS ℤ N * finiteDivisorSigmaPS ℤ N).coeff n := hfin
    _ = (-(qPochFinitePS ℤ N * finiteDivisorSigmaPS ℤ N)).coeff n := by rw [neg_mul]
    _ = (-(etaPS ℤ * divisorSigmaPS ℤ)).coeff n := by
          simpa only [map_neg] using congrArg Neg.neg hprod
    _ = (-etaPS ℤ * divisorSigmaPS ℤ).coeff n := by rw [neg_mul]

theorem thetaOp_discriminantPS_eq :
    thetaOp (discriminantPS ℤ) =
      discriminantPS ℤ - (24 : ℤ⟦X⟧) * discriminantPS ℤ * divisorSigmaPS ℤ := by
  unfold discriminantPS
  rw [thetaOp_mul, thetaOp_X, thetaOp_pow, thetaOp_etaPS_eq_neg_etaPS_mul_divisorSigmaPS]
  norm_num
  ring

theorem coeff_discriminantPS_mul_divisorSigmaPS (n : Nat) (hn : 1 ≤ n) :
    (discriminantPS ℤ * divisorSigmaPS ℤ).coeff n =
      ∑ k ∈ Finset.Icc 1 (n - 1),
        (Nat.divisorSum k id : ℤ) * ramanujanTau ℤ (n - k) := by
  rw [PowerSeries.coeff_mul]
  rw [← Finset.Nat.sum_antidiagonal_swap
    (f := fun p : Nat × Nat =>
      (discriminantPS ℤ).coeff p.1 * (divisorSigmaPS ℤ).coeff p.2)]
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun k j => (discriminantPS ℤ).coeff j * (divisorSigmaPS ℤ).coeff k)]
  simp only [coeff_divisorSigmaPS, ramanujanTau]
  have hsubset : Finset.Icc 1 (n - 1) ⊆ Finset.range (n + 1) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    rw [Finset.mem_range]
    omega
  rw [← Finset.sum_subset hsubset]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_Icc] at hk
    ring
  · intro k hkrange hknot
    rw [Finset.mem_range] at hkrange
    have hk_cases : k = 0 ∨ k = n := by
      by_cases hk0 : k = 0
      · exact Or.inl hk0
      · right
        have hk1 : 1 ≤ k := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hk0)
        have hkn : ¬ k ≤ n - 1 := by
          intro hle
          exact hknot (by rw [Finset.mem_Icc]; exact ⟨hk1, hle⟩)
        omega
    rcases hk_cases with rfl | hk
    · simp [Nat.divisorSum]
    · subst k
      rw [Nat.sub_self]
      change ramanujanTau ℤ 0 * (Nat.divisorSum n id : ℤ) = 0
      rw [ramanujanTau_zero]
      ring

theorem ramanujanTau_log_derivative_recurrence (n : Nat) (hn : 2 ≤ n) :
    ((n : ℤ) - 1) * ramanujanTau ℤ n =
      -24 * ∑ k ∈ Finset.Icc 1 (n - 1),
        (Nat.divisorSum k id : ℤ) * ramanujanTau ℤ (n - k) := by
  let T : ℤ := ∑ k ∈ Finset.Icc 1 (n - 1),
        (Nat.divisorSum k id : ℤ) * ramanujanTau ℤ (n - k)
  have hcoeff := congrArg (fun f : ℤ⟦X⟧ => f.coeff n) thetaOp_discriminantPS_eq
  change (thetaOp (discriminantPS ℤ)).coeff n =
      (discriminantPS ℤ - (24 : ℤ⟦X⟧) * discriminantPS ℤ * divisorSigmaPS ℤ).coeff n at hcoeff
  rw [coeff_thetaOp] at hcoeff
  rw [map_sub] at hcoeff
  have h24coeff :
      (((24 : ℤ⟦X⟧) * discriminantPS ℤ * divisorSigmaPS ℤ).coeff n) =
        (24 : ℤ) * (discriminantPS ℤ * divisorSigmaPS ℤ).coeff n := by
    rw [mul_assoc]
    change (PowerSeries.C (24 : ℤ) * (discriminantPS ℤ * divisorSigmaPS ℤ)).coeff n =
      (24 : ℤ) * (discriminantPS ℤ * divisorSigmaPS ℤ).coeff n
    rw [PowerSeries.coeff_C_mul]
  rw [h24coeff] at hcoeff
  change ramanujanTau ℤ n * (n : ℤ) =
      ramanujanTau ℤ n - (24 : ℤ) * (discriminantPS ℤ * divisorSigmaPS ℤ).coeff n at hcoeff
  rw [coeff_discriminantPS_mul_divisorSigmaPS n (by omega)] at hcoeff
  change ramanujanTau ℤ n * (n : ℤ) = ramanujanTau ℤ n - (24 : ℤ) * T at hcoeff
  change ((n : ℤ) - 1) * ramanujanTau ℤ n = -24 * T
  calc
    ((n : ℤ) - 1) * ramanujanTau ℤ n
        = ramanujanTau ℤ n * (n : ℤ) - ramanujanTau ℤ n := by ring
    _ = -24 * T := by rw [hcoeff]; ring

/-! ### Ramanujan τ congruences at primes p ∈ {2, 3, 5, 7}

For the Ramanujan tau function, classical results show `τ(p) ≡ 0 (mod p)` for certain
small primes (and more generally `τ(p) ≡ 1 + p¹¹ (mod 691)` etc.). We verify the
prime divisibility for p = 2, 3, 5, 7 directly from the computed values. -/

/-- τ(2) ≡ 0 (mod 2). -/
theorem ramanujanTau_two_mod_two :
    (ramanujanTau ℤ 2 : ZMod 2) = 0 := by
  rw [show ramanujanTau ℤ 2 = -24 from ramanujanTau_two ℤ]
  decide

/-- τ(3) ≡ 0 (mod 3). -/
theorem ramanujanTau_three_mod_three :
    (ramanujanTau ℤ 3 : ZMod 3) = 0 := by
  rw [show ramanujanTau ℤ 3 = 252 from ramanujanTau_three ℤ]
  decide

/-- τ(5) ≡ 0 (mod 5). -/
theorem ramanujanTau_five_mod_five :
    (ramanujanTau ℤ 5 : ZMod 5) = 0 := by
  rw [show ramanujanTau ℤ 5 = 4830 from ramanujanTau_five ℤ]
  decide

/-- τ(7) ≡ 0 (mod 7). -/
theorem ramanujanTau_seven_mod_seven :
    (ramanujanTau ℤ 7 : ZMod 7) = 0 := by
  rw [show ramanujanTau ℤ 7 = -16744 from ramanujanTau_seven ℤ]
  decide

/-! ### Chan Theorem 20.1 / Ono target -/

/-- An arithmetic-progression partition congruence modulo `m`:
`p(A * n + B) = 0 (mod m)` for every `n`, with positive step `A`. -/
def PartitionAPCongruence (m A B : Nat) : Prop :=
  0 < A ∧
    ∀ n : Nat,
      ((QseriesFormalization.Ch01.partitionCount (A * n + B) : Nat) : ZMod m) = 0

/-- "Infinitely many congruences" in the unbounded-step sense.  For every lower
bound `C`, there is a partition congruence with step at least `C`. -/
def InfinitelyManyPartitionAPCongruences (m : Nat) : Prop :=
  ∀ C : Nat, ∃ A B : Nat, C ≤ A ∧ PartitionAPCongruence m A B

/-- Formal target for Chan Theorem 20.1 / Ono's theorem.  The proof in Chan uses
half-integral-weight modular forms, Hecke operators, Shimura correspondence, and
Serre density; this file records the target as a proposition, not as an
unproved theorem wrapper. -/
def onoTheorem20_1Statement : Prop :=
  ∀ m : Nat, Nat.Prime m → 5 ≤ m → InfinitelyManyPartitionAPCongruences m

/-- Δ_PS is not a unit (since `τ(0) = 0`, in a nontrivial ring). -/
theorem discriminantPS_not_isUnit [Nontrivial R] : ¬ IsUnit (discriminantPS R) := by
  intro h
  have hc := PowerSeries.isUnit_iff_constantCoeff.mp h
  rw [← PowerSeries.coeff_zero_eq_constantCoeff] at hc
  have := ramanujanTau_zero R
  unfold ramanujanTau at this
  rw [this] at hc
  exact not_isUnit_zero hc

/-- **Structural identity**: `Δ_PS · J^24 = X` in `R⟦X⟧`.

By definition `discriminantPS R = X · (qPochInfPS R)^24`. Since
`qPochInfPS R · partitionGenFun R = 1`, we get `(qPochInfPS R)^24 · (partitionGenFun R)^24 = 1`,
and multiplying by `X` gives the claim. -/
theorem discriminantPS_mul_partitionGenFun_pow_24 :
    discriminantPS R * (QseriesFormalization.PartIV.Ch19.partitionGenFun R) ^ 24 =
      PowerSeries.X := by
  have hqJ : QseriesFormalization.PartIV.Ch19.qPochInfPS R *
      QseriesFormalization.PartIV.Ch19.partitionGenFun R = 1 := by
    rw [mul_comm]
    exact QseriesFormalization.PartIV.Ch19.partitionGenFun_mul_qPochInfPS R
  have hpow : (QseriesFormalization.PartIV.Ch19.qPochInfPS R) ^ 24 *
      (QseriesFormalization.PartIV.Ch19.partitionGenFun R) ^ 24 = 1 := by
    rw [← mul_pow, hqJ, one_pow]
  unfold discriminantPS etaPS
  -- Goal: X * qPochInfPS R ^ 24 * partitionGenFun R ^ 24 = X
  rw [mul_assoc, hpow, mul_one]

/-- The Ramanujan tau generating function `Δ_PS` factors as `X · η^24`. -/
theorem discriminantPS_eq_X_mul_etaPS_pow_24 :
    discriminantPS R = PowerSeries.X * (etaPS R) ^ 24 := rfl

section DiscriminantEulerProduct

open scoped PowerSeries.WithPiTopology

/-- **Formal Euler product expansion of the discriminant**:
`Δ_PS R = X · (∏' i, (1 - X^(i+1)))^24` in `R⟦X⟧`.

This is the formal-PS version of the classical identity for Ramanujan's tau function:
`Δ(q) = q · ∏(1 - q^n)^24`. Uses Ch19's `qPochInfPS_eq_tprod` (the unconditional
formal Euler product). -/
theorem discriminantPS_eq_X_mul_tprod_pow_24
    (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] :
    discriminantPS R = PowerSeries.X *
      (∏' i : Nat, ((1 : R⟦X⟧) - PowerSeries.X ^ (i + 1))) ^ 24 := by
  rw [discriminantPS_eq_X_mul_etaPS_pow_24]
  rw [show etaPS R = QseriesFormalization.PartIV.Ch19.qPochInfPS R from rfl]
  rw [QseriesFormalization.PartIV.Ch19.qPochInfPS_eq_tprod]

/-- The Ramanujan tau coefficient sequence equals the coefficient sequence of
`X · (∏'(1 - X^(i+1)))^24` in `R⟦X⟧`. -/
theorem ramanujanTau_eq_coeff_X_mul_tprod_pow_24
    (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
    (n : Nat) :
    ramanujanTau R n = (PowerSeries.X *
      (∏' i : Nat, ((1 : R⟦X⟧) - PowerSeries.X ^ (i + 1))) ^ 24).coeff n := by
  unfold ramanujanTau
  rw [discriminantPS_eq_X_mul_tprod_pow_24]

end DiscriminantEulerProduct

/-- **Naturality of etaPS** under ring homs (= map_qPochInfPS via definitional equality). -/
theorem map_etaPS {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    PowerSeries.map f (etaPS R) = etaPS S :=
  QseriesFormalization.PartIV.Ch19.map_qPochInfPS f

/-- **Naturality of discriminantPS**: for `f : R →+* S`,
`PowerSeries.map f (discriminantPS R) = discriminantPS S`. -/
theorem map_discriminantPS {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    PowerSeries.map f (discriminantPS R) = discriminantPS S := by
  rw [discriminantPS_eq_X_mul_etaPS_pow_24, discriminantPS_eq_X_mul_etaPS_pow_24,
      map_mul, map_pow, PowerSeries.map_X, map_etaPS]

/-- **Cast of ramanujanTau from ℤ to R**: `(ramanujanTau ℤ n : R) = ramanujanTau R n`. -/
theorem cast_ramanujanTau_int (R : Type*) [CommRing R] (n : Nat) :
    ((ramanujanTau ℤ n : ℤ) : R) = ramanujanTau R n := by
  have h_map := map_discriminantPS (Int.castRingHom R)
  show ((Int.castRingHom R) ((discriminantPS ℤ).coeff n) : R) =
       (discriminantPS R).coeff n
  rw [← PowerSeries.coeff_map (Int.castRingHom R), h_map]

theorem ramanujanTau_congr_sigma11_mod_691_through_two_hundred
    (n : Nat) (hn : n ≤ 200) :
    (ramanujanTau ℤ n : ZMod 691) = (sigma11 n : ZMod 691) := by
  rw [cast_ramanujanTau_int (ZMod 691) n]
  rw [ramanujanTau_eq_tauCoeffMod691FromVec 199 n (by omega)]
  have h := tauCoeffMod691_congr_sigma11_mod691_through_two_hundred ⟨n, by omega⟩
  simpa [sigma11Mod691_eq_sigma11] using h

/-- Ramanujan's mod-691 congruence verified coefficientwise through `n = 300`. -/
theorem ramanujanTau_congr_sigma11_mod_691_through_three_hundred
    (n : Nat) (hn : n ≤ 300) :
    (ramanujanTau ℤ n : ZMod 691) = (sigma11 n : ZMod 691) := by
  rw [cast_ramanujanTau_int (ZMod 691) n]
  rw [ramanujanTau_eq_tauCoeffMod691FromVec 299 n (by omega)]
  have h := tauCoeffMod691_congr_sigma11_mod691_through_three_hundred ⟨n, by omega⟩
  simpa [sigma11Mod691_eq_sigma11] using h

/-- Finite Lehmer verification through `n = 300`, certified by reduction modulo `691`. -/
theorem ramanujanTau_ne_zero_through_three_hundred
    (n : Nat) (hn0 : 1 ≤ n) (hn300 : n ≤ 300) :
    ramanujanTau ℤ n ≠ 0 := by
  intro hzero
  have hmod : (ramanujanTau ℤ n : ZMod 691) = 0 := by
    rw [hzero]
    norm_num
  rw [cast_ramanujanTau_int (ZMod 691) n] at hmod
  rw [ramanujanTau_eq_tauCoeffMod691FromVec 299 n (by omega)] at hmod
  have hnsub : n - 1 < 300 := by omega
  have hne :=
    tauCoeffMod691_ne_zero_through_three_hundred ⟨n - 1, hnsub⟩
  exact hne (by
    have hsucc : n - 1 + 1 = n := by omega
    simpa [hsucc] using hmod)

/-- If the mod-691 formal discriminant is identified with the reduced weight-12
Eisenstein coefficient series, then Ramanujan's congruence follows for every
coefficient. -/
theorem ramanujanTau_congr_sigma11_mod_691_of_discriminantPS_eq_eisensteinE12PSMod691
    (h : discriminantPS (ZMod 691) = eisensteinE12PSMod691) (n : Nat) :
    (ramanujanTau ℤ n : ZMod 691) = (sigma11 n : ZMod 691) := by
  rw [cast_ramanujanTau_int (ZMod 691) n]
  unfold ramanujanTau
  simpa using congrArg (fun f : (ZMod 691)⟦X⟧ => f.coeff n) h

private theorem zmod691_ps_natCast_691 :
    (691 : (ZMod 691)⟦X⟧) = 0 := by
  change PowerSeries.C (691 : ZMod 691) = 0
  have h : (691 : ZMod 691) = 0 := by
    native_decide
  rw [h]
  simp

private theorem zmod691_199_mul_65520 :
    (199 : ZMod 691) * (65520 : ZMod 691) = 1 := by
  native_decide

/-- The purely algebraic mod-691 bridge: the two weight-12 Eisenstein identities
imply `S_11 = Delta` after reduction modulo 691. -/
theorem eisensteinS11PS_eq_discriminantPS_mod_691_of_eisenstein_identities
    (hDelta : eisensteinDeltaIdentity (ZMod 691))
    (hLinear : eisensteinWeight12LinearIdentity (ZMod 691)) :
    eisensteinS11PS (ZMod 691) = discriminantPS (ZMod 691) := by
  let PS := (ZMod 691)⟦X⟧
  let E4 : PS := eisensteinE4PS (ZMod 691)
  let E6 : PS := eisensteinE6PS (ZMod 691)
  let S : PS := eisensteinS11PS (ZMod 691)
  let D : PS := discriminantPS (ZMod 691)
  change E4 ^ 3 - E6 ^ 2 = (1728 : PS) * D at hDelta
  change (441 : PS) * E4 ^ 3 + (250 : PS) * E6 ^ 2 =
    (691 : PS) + (65520 : PS) * S at hLinear
  change S = D
  ext n
  have hDeltaCoeff := congrArg (fun f : PS => f.coeff n) hDelta
  change (E4 ^ 3 - E6 ^ 2).coeff n = ((1728 : PS) * D).coeff n at hDeltaCoeff
  rw [map_sub] at hDeltaCoeff
  change (E4 ^ 3).coeff n - (E6 ^ 2).coeff n =
    (PowerSeries.C (1728 : ZMod 691) * D).coeff n at hDeltaCoeff
  rw [PowerSeries.coeff_C_mul] at hDeltaCoeff
  have hLinearCoeff := congrArg (fun f : PS => f.coeff n) hLinear
  change
      ((441 : PS) * E4 ^ 3 + (250 : PS) * E6 ^ 2).coeff n =
        ((691 : PS) + (65520 : PS) * S).coeff n
    at hLinearCoeff
  rw [map_add, map_add] at hLinearCoeff
  rw [zmod691_ps_natCast_691] at hLinearCoeff
  change
      (PowerSeries.C (441 : ZMod 691) * E4 ^ 3).coeff n +
          (PowerSeries.C (250 : ZMod 691) * E6 ^ 2).coeff n =
        (0 : PS).coeff n + (PowerSeries.C (65520 : ZMod 691) * S).coeff n
    at hLinearCoeff
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_C_mul] at hLinearCoeff
  simp only [map_zero, zero_add] at hLinearCoeff
  have h691 : (691 : ZMod 691) = 0 := by
    native_decide
  have h4411728 : (441 : ZMod 691) * (1728 : ZMod 691) = (65520 : ZMod 691) := by
    native_decide
  have hcoeff : (65520 : ZMod 691) * S.coeff n =
      (65520 : ZMod 691) * D.coeff n := by
    calc
      (65520 : ZMod 691) * S.coeff n
          = (441 : ZMod 691) * (E4 ^ 3).coeff n +
              (250 : ZMod 691) * (E6 ^ 2).coeff n := by
              rw [hLinearCoeff]
      _ = (441 : ZMod 691) * ((E4 ^ 3).coeff n - (E6 ^ 2).coeff n) +
            (691 : ZMod 691) * (E6 ^ 2).coeff n := by ring
      _ = (441 : ZMod 691) * ((1728 : ZMod 691) * D.coeff n) +
            (691 : ZMod 691) * (E6 ^ 2).coeff n := by rw [hDeltaCoeff]
      _ = ((441 : ZMod 691) * (1728 : ZMod 691)) * D.coeff n +
            (0 : ZMod 691) * (E6 ^ 2).coeff n := by
            rw [h691]
            ring
      _ = (65520 : ZMod 691) * D.coeff n := by
            rw [h4411728]
            ring
  calc
    S.coeff n = 1 * S.coeff n := by ring
    _ = ((199 : ZMod 691) * (65520 : ZMod 691)) * S.coeff n := by
          rw [zmod691_199_mul_65520]
    _ = (199 : ZMod 691) * ((65520 : ZMod 691) * S.coeff n) := by ring
    _ = (199 : ZMod 691) * ((65520 : ZMod 691) * D.coeff n) := by rw [hcoeff]
    _ = ((199 : ZMod 691) * (65520 : ZMod 691)) * D.coeff n := by ring
    _ = 1 * D.coeff n := by rw [zmod691_199_mul_65520]
    _ = D.coeff n := by ring

theorem discriminantPS_eq_eisensteinE12PSMod691_of_eisenstein_identities
    (hDelta : eisensteinDeltaIdentity (ZMod 691))
    (hLinear : eisensteinWeight12LinearIdentity (ZMod 691)) :
    discriminantPS (ZMod 691) = eisensteinE12PSMod691 := by
  rw [eisensteinE12PSMod691_eq_eisensteinS11PS]
  exact (eisensteinS11PS_eq_discriminantPS_mod_691_of_eisenstein_identities
    hDelta hLinear).symm

theorem ramanujanTau_congr_sigma11_mod_691_of_eisenstein_identities
    (hDelta : eisensteinDeltaIdentity (ZMod 691))
    (hLinear : eisensteinWeight12LinearIdentity (ZMod 691)) (n : Nat) :
    (ramanujanTau ℤ n : ZMod 691) = (sigma11 n : ZMod 691) :=
  ramanujanTau_congr_sigma11_mod_691_of_discriminantPS_eq_eisensteinE12PSMod691
    (discriminantPS_eq_eisensteinE12PSMod691_of_eisenstein_identities hDelta hLinear) n

/-- **A1 Bridge: `ramanujanTau` via finite Euler product** in `R⟦X⟧`.

For any `N ≥ 1` and `n ≤ N`:
  `ramanujanTau R n = (X · ∏_{i < N}(1 - X^(i+1))^24).coeff n`.

This matches the form of Ripple's `deltaEulerCoeffZ`/`deltaEulerProductTruncZ`
(which uses the same finite product for ℤ⟦X⟧). -/
theorem ramanujanTau_eq_coeff_finite_product
    (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
    (n N : Nat) (hn : 0 < n) (hnN : n ≤ N) :
    ramanujanTau R n =
      (PowerSeries.X *
        (∏ i ∈ Finset.range N, ((1 : R⟦X⟧) - PowerSeries.X ^ (i + 1))) ^ 24).coeff n := by
  unfold ramanujanTau
  rw [discriminantPS_eq_X_mul_etaPS_pow_24]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hn)
  rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul]
  show ((QseriesFormalization.PartIV.Ch19.qPochInfPS R) ^ 24).coeff m =
      ((∏ i ∈ Finset.range N, ((1 : R⟦X⟧) - PowerSeries.X ^ (i + 1))) ^ 24).coeff m
  exact QseriesFormalization.PartIV.Ch19.coeff_qPochInfPS_pow_eq_coeff_finite_product_pow
    R 24 m N (by omega)

/-- **A1 Bridge (Ripple-form): `ramanujanTau` via prod-of-power**.

For `N ≥ n ≥ 1`:
  `ramanujanTau R n = (X · ∏_{i < N}(1 - X^(i+1))^24).coeff n`

(distributing the power into the product). This matches Ripple's
`deltaEulerCoeffZ` definition `(deltaEulerProductTruncZ (n+1)).coeff n`
where `deltaEulerProductTruncZ N := X · ∏_{m<N}(1-X^(m+1))^24`. -/
theorem ramanujanTau_eq_coeff_prod_of_pow
    (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
    (n N : Nat) (hn : 0 < n) (hnN : n ≤ N) :
    ramanujanTau R n =
      (PowerSeries.X *
        ∏ i ∈ Finset.range N, ((1 : R⟦X⟧) - PowerSeries.X ^ (i + 1)) ^ 24).coeff n := by
  rw [ramanujanTau_eq_coeff_finite_product R n N hn hnN]
  congr 2
  exact (Finset.prod_pow _ 24 _).symm

/-- **Frobenius for the discriminant** in `(ZMod p)⟦X⟧`:
`Δ_PS^p = expand_p (Δ_PS)`.

Proof: by Frobenius for power series in char p, and the multiplicativity of expand. -/
theorem discriminantPS_pow_eq_expand (p : Nat) [Fact (Nat.Prime p)] (hp : p ≠ 0) :
    (discriminantPS (ZMod p)) ^ p =
      PowerSeries.expand p hp (discriminantPS (ZMod p)) := by
  -- discriminantPS = X * etaPS^24, etaPS = qPochInfPS
  unfold discriminantPS etaPS
  -- LHS: (X * qPoch^24)^p = X^p * qPoch^(24p)
  rw [mul_pow]
  -- RHS: expand p (X * qPoch^24) = expand p X * expand p (qPoch^24)
  rw [map_mul, map_pow]
  rw [PowerSeries.expand_X]
  -- qPoch^p = expand p qPoch (already in Ch19)
  have hqPoch_p : (QseriesFormalization.PartIV.Ch19.qPochInfPS (ZMod p)) ^ p =
      PowerSeries.expand p hp (QseriesFormalization.PartIV.Ch19.qPochInfPS (ZMod p)) :=
    QseriesFormalization.PartIV.Ch19.qPochInfPS_pow_eq_expand p hp
  -- so qPoch^(24p) = (qPoch^p)^24 = (expand p qPoch)^24
  rw [show ((QseriesFormalization.PartIV.Ch19.qPochInfPS (ZMod p)) ^ 24) ^ p =
      ((QseriesFormalization.PartIV.Ch19.qPochInfPS (ZMod p)) ^ p) ^ 24 from by ring,
      hqPoch_p]

end FormalPS

end Ch20
end PartIV
end QseriesFormalization
