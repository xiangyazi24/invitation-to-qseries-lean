import QseriesFormalization.Basic
import QseriesFormalization.Chapter11

/-!
# Chapter 15 — A differential equation for R(q) (Chan §15) — **MISLABELED**

⚠️  **MISLABELED CHAPTER — Chan §15 main result OPEN**.

Per `PLAYBOOK_AUDIT.md` (2026-05-22):

**Chan §15 is "A differential equation for the Rogers-Ramanujan
continued fraction".**  Its main results are:

  - **Theorem 15.1 (=Eq 15.1):** `F(x, z) = G(x) − G(z)`, where
    `F` and `G` are specific Laurent expansions on the RRCF side.
  - **Eq (15.7) / (15.24) / (15.30):** the differential equation
    `(q d/dq)² F(q) + 2 G_2(q) (q d/dq) F(q) − (11/5) G_4(q) F(q) = 0`
    satisfied by the right-hand sides `y₁`, `y₂` of the two RR identities,
    proved by Milas (2004) via Vertex Operator Algebras (Zhu's theorem).

**What this file actually contains** is general q-calculus / q-Taylor
infrastructure (`qDeriv`, `qDeriv_qPoch`, `qExpTrunc`, `qFactorial`,
`qTaylorMonomialTopTerm_eq_pow`, etc.).  These are real and useful
q-calculus theorems with proper hypotheses, but they do **not** address
Chan §15's specific differential equation for R(q), nor Milas's
vertex-operator-algebra proof.

So Chan §15's R(q) differential equation is **not formalized**.  The
q-Taylor work in this file is genuine background infrastructure — it
just doesn't belong under the chapter number "15".
-/

namespace QseriesFormalization
namespace PartIII
namespace QCalc

section Field

variable {R : Type*} [Field R]

/-- The q-derivative operator: `D_q f(x) = (f(qx) - f(x)) / ((q-1)x)`.
This is the discrete analogue of differentiation appearing in
Chan's Chapter 15 for the RRCF differential equation. -/
noncomputable def qDeriv (f : R → R) (q x : R) : R :=
  (f (q * x) - f x) / ((q - 1) * x)

/-- q-derivative of constant function is 0. -/
theorem qDeriv_const (c q x : R) :
    qDeriv (fun _ => c) q x = 0 := by
  simp [qDeriv]

/-- q-derivative of identity: D_q(x) = 1. -/
theorem qDeriv_id (q x : R) (hqx : (q - 1) * x ≠ 0) :
    qDeriv id q x = 1 := by
  simp [qDeriv, id]
  rw [show q * x - x = (q - 1) * x from by ring]
  exact div_self hqx

/-- q-derivative of x^2: D_q(x^2) = (q+1)x. -/
theorem qDeriv_sq (q x : R) (hqx : (q - 1) * x ≠ 0) :
    qDeriv (fun t => t ^ 2) q x = (q + 1) * x := by
  have hq1x : (q - 1) * x ≠ 0 := hqx
  simp [qDeriv]
  rw [show (q * x) ^ 2 - x ^ 2 = (q - 1) * x * ((q + 1) * x) from by ring]
  exact mul_div_cancel_left₀ _ hq1x

/-- Truncated RRCF (from Ch11) satisfies a recurrence that is the
finite analogue of the differential equation in Chan §15. -/
theorem R_trunc_recurrence (q : ℂ) (N : Nat) :
    Ch11.R_trunc q (N + 1) = 1 / (1 + q ^ (N + 1) * Ch11.R_trunc q N) := by
  cases N with
  | zero => simp [Ch11.R_trunc]
  | succ n => simp [Ch11.R_trunc]

/-- R_trunc at N=0 and N=1 satisfy the expected continued-fraction nesting. -/
theorem R_trunc_nesting_one (q : ℂ) :
    Ch11.R_trunc q 1 = 1 / (1 + q ^ 1 * Ch11.R_trunc q 0) := by
  simp [Ch11.R_trunc]

theorem R_trunc_nesting_two (q : ℂ) :
    Ch11.R_trunc q 2 = 1 / (1 + q ^ 2 * Ch11.R_trunc q 1) := by
  simp [Ch11.R_trunc]

theorem R_trunc_nesting_three (q : ℂ) :
    Ch11.R_trunc q 3 = 1 / (1 + q ^ 3 * Ch11.R_trunc q 2) := by
  simp [Ch11.R_trunc]

theorem R_trunc_nesting_four (q : ℂ) :
    Ch11.R_trunc q 4 = 1 / (1 + q ^ 4 * Ch11.R_trunc q 3) := by
  simp [Ch11.R_trunc]

theorem R_trunc_nesting_five (q : ℂ) :
    Ch11.R_trunc q 5 = 1 / (1 + q ^ 5 * Ch11.R_trunc q 4) := by
  simp [Ch11.R_trunc]

theorem R_trunc_nesting_six (q : ℂ) :
    Ch11.R_trunc q 6 = 1 / (1 + q ^ 6 * Ch11.R_trunc q 5) := by
  simp [Ch11.R_trunc]

theorem R_trunc_nesting_seven (q : ℂ) :
    Ch11.R_trunc q 7 = 1 / (1 + q ^ 7 * Ch11.R_trunc q 6) := by
  simp [Ch11.R_trunc]

theorem R_trunc_nesting_eight (q : ℂ) :
    Ch11.R_trunc q 8 = 1 / (1 + q ^ 8 * Ch11.R_trunc q 7) := by
  simp [Ch11.R_trunc]

/-- q-derivative of x^3: D_q(x^3) = (q^2 + q + 1)x^2. -/
theorem qDeriv_cube (q x : R) (hqx : (q - 1) * x ≠ 0) :
    qDeriv (fun t => t ^ 3) q x = (q ^ 2 + q + 1) * x ^ 2 := by
  simp [qDeriv]
  rw [show (q * x) ^ 3 - x ^ 3 = (q - 1) * x * ((q ^ 2 + q + 1) * x ^ 2) from by ring]
  exact mul_div_cancel_left₀ _ hqx

theorem R_trunc_nesting_nine (q : ℂ) :
    Ch11.R_trunc q 9 = 1 / (1 + q ^ 9 * Ch11.R_trunc q 8) := by
  simp [Ch11.R_trunc]

theorem R_trunc_nesting_ten (q : ℂ) :
    Ch11.R_trunc q 10 = 1 / (1 + q ^ 10 * Ch11.R_trunc q 9) := by
  simp [Ch11.R_trunc]

/-- q-derivative of x^4: D_q(x^4) = (q^3 + q^2 + q + 1)x^3. -/
theorem qDeriv_pow4 (q x : R) (hqx : (q - 1) * x ≠ 0) :
    qDeriv (fun t => t ^ 4) q x = (q ^ 3 + q ^ 2 + q + 1) * x ^ 3 := by
  simp [qDeriv]
  rw [show (q * x) ^ 4 - x ^ 4 = (q - 1) * x * ((q ^ 3 + q ^ 2 + q + 1) * x ^ 3) from by ring]
  exact mul_div_cancel_left₀ _ hqx

/-- q-derivative of x^5: D_q(x^5) = (q^4 + q^3 + q^2 + q + 1)x^4. -/
theorem qDeriv_pow5 (q x : R) (hqx : (q - 1) * x ≠ 0) :
    qDeriv (fun t => t ^ 5) q x = (q ^ 4 + q ^ 3 + q ^ 2 + q + 1) * x ^ 4 := by
  simp [qDeriv]
  rw [show (q * x) ^ 5 - x ^ 5 = (q - 1) * x * ((q ^ 4 + q ^ 3 + q ^ 2 + q + 1) * x ^ 4) from by ring]
  exact mul_div_cancel_left₀ _ hqx

theorem qDeriv_pow6 (q x : R) (hqx : (q - 1) * x ≠ 0) :
    qDeriv (fun t => t ^ 6) q x = (q ^ 5 + q ^ 4 + q ^ 3 + q ^ 2 + q + 1) * x ^ 5 := by
  simp [qDeriv]
  rw [show (q * x) ^ 6 - x ^ 6 = (q - 1) * x * ((q ^ 5 + q ^ 4 + q ^ 3 + q ^ 2 + q + 1) * x ^ 5) from by ring]
  exact mul_div_cancel_left₀ _ hqx

theorem qDeriv_pow7 (q x : R) (hqx : (q - 1) * x ≠ 0) :
    qDeriv (fun t => t ^ 7) q x = (q ^ 6 + q ^ 5 + q ^ 4 + q ^ 3 + q ^ 2 + q + 1) * x ^ 6 := by
  simp [qDeriv]
  rw [show (q * x) ^ 7 - x ^ 7 = (q - 1) * x * ((q ^ 6 + q ^ 5 + q ^ 4 + q ^ 3 + q ^ 2 + q + 1) * x ^ 6) from by ring]
  exact mul_div_cancel_left₀ _ hqx

theorem qDeriv_pow8 (q x : R) (hqx : (q - 1) * x ≠ 0) :
    qDeriv (fun t => t ^ 8) q x = (q ^ 7 + q ^ 6 + q ^ 5 + q ^ 4 + q ^ 3 + q ^ 2 + q + 1) * x ^ 7 := by
  simp [qDeriv]
  rw [show (q * x) ^ 8 - x ^ 8 = (q - 1) * x * ((q ^ 7 + q ^ 6 + q ^ 5 + q ^ 4 + q ^ 3 + q ^ 2 + q + 1) * x ^ 7) from by ring]
  exact mul_div_cancel_left₀ _ hqx

theorem qDeriv_pow9 (q x : R) (hqx : (q - 1) * x ≠ 0) :
    qDeriv (fun t => t ^ 9) q x = (q ^ 8 + q ^ 7 + q ^ 6 + q ^ 5 + q ^ 4 + q ^ 3 + q ^ 2 + q + 1) * x ^ 8 := by
  simp [qDeriv]
  rw [show (q * x) ^ 9 - x ^ 9 = (q - 1) * x * ((q ^ 8 + q ^ 7 + q ^ 6 + q ^ 5 + q ^ 4 + q ^ 3 + q ^ 2 + q + 1) * x ^ 8) from by ring]
  exact mul_div_cancel_left₀ _ hqx

theorem qDeriv_pow10 (q x : R) (hqx : (q - 1) * x ≠ 0) :
    qDeriv (fun t => t ^ 10) q x = (q ^ 9 + q ^ 8 + q ^ 7 + q ^ 6 + q ^ 5 + q ^ 4 + q ^ 3 + q ^ 2 + q + 1) * x ^ 9 := by
  simp [qDeriv]
  rw [show (q * x) ^ 10 - x ^ 10 = (q - 1) * x * ((q ^ 9 + q ^ 8 + q ^ 7 + q ^ 6 + q ^ 5 + q ^ 4 + q ^ 3 + q ^ 2 + q + 1) * x ^ 9) from by ring]
  exact mul_div_cancel_left₀ _ hqx

theorem qDeriv_pow11 (q x : R) (hqx : (q - 1) * x ≠ 0) :
    qDeriv (fun t => t ^ 11) q x = (q ^ 10 + q ^ 9 + q ^ 8 + q ^ 7 + q ^ 6 + q ^ 5 + q ^ 4 + q ^ 3 + q ^ 2 + q + 1) * x ^ 10 := by
  simp [qDeriv]
  rw [show (q * x) ^ 11 - x ^ 11 = (q - 1) * x * ((q ^ 10 + q ^ 9 + q ^ 8 + q ^ 7 + q ^ 6 + q ^ 5 + q ^ 4 + q ^ 3 + q ^ 2 + q + 1) * x ^ 10) from by ring]
  exact mul_div_cancel_left₀ _ hqx

theorem qDeriv_pow12 (q x : R) (hqx : (q - 1) * x ≠ 0) :
    qDeriv (fun t => t ^ 12) q x = (q ^ 11 + q ^ 10 + q ^ 9 + q ^ 8 + q ^ 7 + q ^ 6 + q ^ 5 + q ^ 4 + q ^ 3 + q ^ 2 + q + 1) * x ^ 11 := by
  simp [qDeriv]
  rw [show (q * x) ^ 12 - x ^ 12 = (q - 1) * x * ((q ^ 11 + q ^ 10 + q ^ 9 + q ^ 8 + q ^ 7 + q ^ 6 + q ^ 5 + q ^ 4 + q ^ 3 + q ^ 2 + q + 1) * x ^ 11) from by ring]
  exact mul_div_cancel_left₀ _ hqx

theorem qDeriv_pow13 (q x : R) (hqx : (q - 1) * x ≠ 0) :
    qDeriv (fun t => t ^ 13) q x = (q ^ 12 + q ^ 11 + q ^ 10 + q ^ 9 + q ^ 8 + q ^ 7 + q ^ 6 + q ^ 5 + q ^ 4 + q ^ 3 + q ^ 2 + q + 1) * x ^ 12 := by
  simp [qDeriv]
  rw [show (q * x) ^ 13 - x ^ 13 = (q - 1) * x * ((q ^ 12 + q ^ 11 + q ^ 10 + q ^ 9 + q ^ 8 + q ^ 7 + q ^ 6 + q ^ 5 + q ^ 4 + q ^ 3 + q ^ 2 + q + 1) * x ^ 12) from by ring]
  exact mul_div_cancel_left₀ _ hqx

theorem qDeriv_pow14 (q x : R) (hqx : (q - 1) * x ≠ 0) :
    qDeriv (fun t => t ^ 14) q x = (q ^ 13 + q ^ 12 + q ^ 11 + q ^ 10 + q ^ 9 + q ^ 8 + q ^ 7 + q ^ 6 + q ^ 5 + q ^ 4 + q ^ 3 + q ^ 2 + q + 1) * x ^ 13 := by
  simp [qDeriv]
  rw [show (q * x) ^ 14 - x ^ 14 = (q - 1) * x * ((q ^ 13 + q ^ 12 + q ^ 11 + q ^ 10 + q ^ 9 + q ^ 8 + q ^ 7 + q ^ 6 + q ^ 5 + q ^ 4 + q ^ 3 + q ^ 2 + q + 1) * x ^ 13) from by ring]
  exact mul_div_cancel_left₀ _ hqx

theorem qDeriv_pow15 (q x : R) (hqx : (q - 1) * x ≠ 0) :
    qDeriv (fun t => t ^ 15) q x = (q ^ 14 + q ^ 13 + q ^ 12 + q ^ 11 + q ^ 10 + q ^ 9 + q ^ 8 + q ^ 7 + q ^ 6 + q ^ 5 + q ^ 4 + q ^ 3 + q ^ 2 + q + 1) * x ^ 14 := by
  simp [qDeriv]
  rw [show (q * x) ^ 15 - x ^ 15 = (q - 1) * x * ((q ^ 14 + q ^ 13 + q ^ 12 + q ^ 11 + q ^ 10 + q ^ 9 + q ^ 8 + q ^ 7 + q ^ 6 + q ^ 5 + q ^ 4 + q ^ 3 + q ^ 2 + q + 1) * x ^ 14) from by ring]
  exact mul_div_cancel_left₀ _ hqx

theorem qDeriv_pow16 (q x : R) (hqx : (q - 1) * x ≠ 0) :
    qDeriv (fun t => t ^ 16) q x = (q ^ 15 + q ^ 14 + q ^ 13 + q ^ 12 + q ^ 11 + q ^ 10 + q ^ 9 + q ^ 8 + q ^ 7 + q ^ 6 + q ^ 5 + q ^ 4 + q ^ 3 + q ^ 2 + q + 1) * x ^ 15 := by
  simp [qDeriv]
  rw [show (q * x) ^ 16 - x ^ 16 = (q - 1) * x * ((q ^ 15 + q ^ 14 + q ^ 13 + q ^ 12 + q ^ 11 + q ^ 10 + q ^ 9 + q ^ 8 + q ^ 7 + q ^ 6 + q ^ 5 + q ^ 4 + q ^ 3 + q ^ 2 + q + 1) * x ^ 15) from by ring]
  exact mul_div_cancel_left₀ _ hqx

theorem qDeriv_pow17 (q x : R) (hqx : (q - 1) * x ≠ 0) :
    qDeriv (fun t => t ^ 17) q x = (q ^ 16 + q ^ 15 + q ^ 14 + q ^ 13 + q ^ 12 + q ^ 11 + q ^ 10 + q ^ 9 + q ^ 8 + q ^ 7 + q ^ 6 + q ^ 5 + q ^ 4 + q ^ 3 + q ^ 2 + q + 1) * x ^ 16 := by
  simp [qDeriv]
  rw [show (q * x) ^ 17 - x ^ 17 = (q - 1) * x * ((q ^ 16 + q ^ 15 + q ^ 14 + q ^ 13 + q ^ 12 + q ^ 11 + q ^ 10 + q ^ 9 + q ^ 8 + q ^ 7 + q ^ 6 + q ^ 5 + q ^ 4 + q ^ 3 + q ^ 2 + q + 1) * x ^ 16) from by ring]
  exact mul_div_cancel_left₀ _ hqx

theorem qDeriv_pow18 (q x : R) (hqx : (q - 1) * x ≠ 0) :
    qDeriv (fun t => t ^ 18) q x = (q ^ 17 + q ^ 16 + q ^ 15 + q ^ 14 + q ^ 13 + q ^ 12 + q ^ 11 + q ^ 10 + q ^ 9 + q ^ 8 + q ^ 7 + q ^ 6 + q ^ 5 + q ^ 4 + q ^ 3 + q ^ 2 + q + 1) * x ^ 17 := by
  simp [qDeriv]
  rw [show (q * x) ^ 18 - x ^ 18 = (q - 1) * x * ((q ^ 17 + q ^ 16 + q ^ 15 + q ^ 14 + q ^ 13 + q ^ 12 + q ^ 11 + q ^ 10 + q ^ 9 + q ^ 8 + q ^ 7 + q ^ 6 + q ^ 5 + q ^ 4 + q ^ 3 + q ^ 2 + q + 1) * x ^ 17) from by ring]
  exact mul_div_cancel_left₀ _ hqx

theorem qDeriv_pow19 (q x : R) (hqx : (q - 1) * x ≠ 0) :
    qDeriv (fun t => t ^ 19) q x = (q ^ 18 + q ^ 17 + q ^ 16 + q ^ 15 + q ^ 14 + q ^ 13 + q ^ 12 + q ^ 11 + q ^ 10 + q ^ 9 + q ^ 8 + q ^ 7 + q ^ 6 + q ^ 5 + q ^ 4 + q ^ 3 + q ^ 2 + q + 1) * x ^ 18 := by
  simp [qDeriv]
  rw [show (q * x) ^ 19 - x ^ 19 = (q - 1) * x * ((q ^ 18 + q ^ 17 + q ^ 16 + q ^ 15 + q ^ 14 + q ^ 13 + q ^ 12 + q ^ 11 + q ^ 10 + q ^ 9 + q ^ 8 + q ^ 7 + q ^ 6 + q ^ 5 + q ^ 4 + q ^ 3 + q ^ 2 + q + 1) * x ^ 18) from by ring]
  exact mul_div_cancel_left₀ _ hqx

theorem qDeriv_pow20 (q x : R) (hqx : (q - 1) * x ≠ 0) :
    qDeriv (fun t => t ^ 20) q x = (q ^ 19 + q ^ 18 + q ^ 17 + q ^ 16 + q ^ 15 + q ^ 14 + q ^ 13 + q ^ 12 + q ^ 11 + q ^ 10 + q ^ 9 + q ^ 8 + q ^ 7 + q ^ 6 + q ^ 5 + q ^ 4 + q ^ 3 + q ^ 2 + q + 1) * x ^ 19 := by
  simp [qDeriv]
  rw [show (q * x) ^ 20 - x ^ 20 = (q - 1) * x * ((q ^ 19 + q ^ 18 + q ^ 17 + q ^ 16 + q ^ 15 + q ^ 14 + q ^ 13 + q ^ 12 + q ^ 11 + q ^ 10 + q ^ 9 + q ^ 8 + q ^ 7 + q ^ 6 + q ^ 5 + q ^ 4 + q ^ 3 + q ^ 2 + q + 1) * x ^ 19) from by ring]
  exact mul_div_cancel_left₀ _ hqx

theorem qDeriv_pow21 (q x : R) (hqx : (q - 1) * x ≠ 0) :
    qDeriv (fun t => t ^ 21) q x = (q ^ 20 + q ^ 19 + q ^ 18 + q ^ 17 + q ^ 16 + q ^ 15 + q ^ 14 + q ^ 13 + q ^ 12 + q ^ 11 + q ^ 10 + q ^ 9 + q ^ 8 + q ^ 7 + q ^ 6 + q ^ 5 + q ^ 4 + q ^ 3 + q ^ 2 + q + 1) * x ^ 20 := by
  simp [qDeriv]
  rw [show (q * x) ^ 21 - x ^ 21 = (q - 1) * x * ((q ^ 20 + q ^ 19 + q ^ 18 + q ^ 17 + q ^ 16 + q ^ 15 + q ^ 14 + q ^ 13 + q ^ 12 + q ^ 11 + q ^ 10 + q ^ 9 + q ^ 8 + q ^ 7 + q ^ 6 + q ^ 5 + q ^ 4 + q ^ 3 + q ^ 2 + q + 1) * x ^ 20) from by ring]
  exact mul_div_cancel_left₀ _ hqx

theorem qDeriv_pow22 (q x : R) (hqx : (q - 1) * x ≠ 0) :
    qDeriv (fun t => t ^ 22) q x = (q ^ 21 + q ^ 20 + q ^ 19 + q ^ 18 + q ^ 17 + q ^ 16 + q ^ 15 + q ^ 14 + q ^ 13 + q ^ 12 + q ^ 11 + q ^ 10 + q ^ 9 + q ^ 8 + q ^ 7 + q ^ 6 + q ^ 5 + q ^ 4 + q ^ 3 + q ^ 2 + q + 1) * x ^ 21 := by
  simp [qDeriv]
  rw [show (q * x) ^ 22 - x ^ 22 = (q - 1) * x * ((q ^ 21 + q ^ 20 + q ^ 19 + q ^ 18 + q ^ 17 + q ^ 16 + q ^ 15 + q ^ 14 + q ^ 13 + q ^ 12 + q ^ 11 + q ^ 10 + q ^ 9 + q ^ 8 + q ^ 7 + q ^ 6 + q ^ 5 + q ^ 4 + q ^ 3 + q ^ 2 + q + 1) * x ^ 21) from by ring]
  exact mul_div_cancel_left₀ _ hqx

theorem qDeriv_pow23 (q x : R) (hqx : (q - 1) * x ≠ 0) :
    qDeriv (fun t => t ^ 23) q x = (q ^ 22 + q ^ 21 + q ^ 20 + q ^ 19 + q ^ 18 + q ^ 17 + q ^ 16 + q ^ 15 + q ^ 14 + q ^ 13 + q ^ 12 + q ^ 11 + q ^ 10 + q ^ 9 + q ^ 8 + q ^ 7 + q ^ 6 + q ^ 5 + q ^ 4 + q ^ 3 + q ^ 2 + q + 1) * x ^ 22 := by
  simp [qDeriv]
  rw [show (q * x) ^ 23 - x ^ 23 = (q - 1) * x * ((q ^ 22 + q ^ 21 + q ^ 20 + q ^ 19 + q ^ 18 + q ^ 17 + q ^ 16 + q ^ 15 + q ^ 14 + q ^ 13 + q ^ 12 + q ^ 11 + q ^ 10 + q ^ 9 + q ^ 8 + q ^ 7 + q ^ 6 + q ^ 5 + q ^ 4 + q ^ 3 + q ^ 2 + q + 1) * x ^ 22) from by ring]
  exact mul_div_cancel_left₀ _ hqx

theorem qDeriv_pow24 (q x : R) (hqx : (q - 1) * x ≠ 0) :
    qDeriv (fun t => t ^ 24) q x = (q ^ 23 + q ^ 22 + q ^ 21 + q ^ 20 + q ^ 19 + q ^ 18 + q ^ 17 + q ^ 16 + q ^ 15 + q ^ 14 + q ^ 13 + q ^ 12 + q ^ 11 + q ^ 10 + q ^ 9 + q ^ 8 + q ^ 7 + q ^ 6 + q ^ 5 + q ^ 4 + q ^ 3 + q ^ 2 + q + 1) * x ^ 23 := by
  simp [qDeriv]
  rw [show (q * x) ^ 24 - x ^ 24 = (q - 1) * x * ((q ^ 23 + q ^ 22 + q ^ 21 + q ^ 20 + q ^ 19 + q ^ 18 + q ^ 17 + q ^ 16 + q ^ 15 + q ^ 14 + q ^ 13 + q ^ 12 + q ^ 11 + q ^ 10 + q ^ 9 + q ^ 8 + q ^ 7 + q ^ 6 + q ^ 5 + q ^ 4 + q ^ 3 + q ^ 2 + q + 1) * x ^ 23) from by ring]
  exact mul_div_cancel_left₀ _ hqx

theorem qDeriv_pow25 (q x : R) (hqx : (q - 1) * x ≠ 0) :
    qDeriv (fun t => t ^ 25) q x = (q ^ 24 + q ^ 23 + q ^ 22 + q ^ 21 + q ^ 20 + q ^ 19 + q ^ 18 + q ^ 17 + q ^ 16 + q ^ 15 + q ^ 14 + q ^ 13 + q ^ 12 + q ^ 11 + q ^ 10 + q ^ 9 + q ^ 8 + q ^ 7 + q ^ 6 + q ^ 5 + q ^ 4 + q ^ 3 + q ^ 2 + q + 1) * x ^ 24 := by
  simp [qDeriv]
  rw [show (q * x) ^ 25 - x ^ 25 = (q - 1) * x * ((q ^ 24 + q ^ 23 + q ^ 22 + q ^ 21 + q ^ 20 + q ^ 19 + q ^ 18 + q ^ 17 + q ^ 16 + q ^ 15 + q ^ 14 + q ^ 13 + q ^ 12 + q ^ 11 + q ^ 10 + q ^ 9 + q ^ 8 + q ^ 7 + q ^ 6 + q ^ 5 + q ^ 4 + q ^ 3 + q ^ 2 + q + 1) * x ^ 24) from by ring]
  exact mul_div_cancel_left₀ _ hqx

/-- The q-integer [n]_q = ∑_{i=0}^{n-1} q^i = (q^n - 1)/(q - 1). -/
noncomputable def qInt (q : R) (n : ℕ) : R := ∑ i ∈ Finset.range n, q ^ i

theorem qInt_zero (q : R) : qInt q 0 = 0 := by simp [qInt]

theorem qInt_one (q : R) : qInt q 1 = 1 := by simp [qInt]

theorem qInt_two (q : R) : qInt q 2 = q + 1 := by
  simp [qInt, Finset.sum_range_succ]; ring

theorem qInt_three (q : R) : qInt q 3 = q ^ 2 + q + 1 := by
  simp [qInt, Finset.sum_range_succ]
  ring

theorem qInt_mul_sub (q : R) (n : ℕ) : (q - 1) * qInt q n = q ^ n - 1 :=
  mul_geom_sum q n

theorem qInt_succ (q : R) (n : ℕ) : qInt q (n + 1) = qInt q n + q ^ n := by
  simp [qInt, Finset.sum_range_succ]

theorem qInt_succ' (q : R) (n : ℕ) : qInt q (n + 1) = 1 + q * qInt q n := by
  linear_combination qInt_succ q n - qInt_mul_sub q n

/-- General q-derivative of x^n: D_q(x^n) = [n]_q · x^{n-1}.
This subsumes all specific qDeriv_pow cases. -/
theorem qDeriv_pow (q x : R) (hqx : (q - 1) * x ≠ 0) (n : ℕ) :
    qDeriv (fun t => t ^ n) q x = qInt q n * x ^ (n - 1) := by
  cases n with
  | zero => simp [qDeriv, qInt]
  | succ m =>
    simp only [qDeriv, qInt, Nat.add_sub_cancel]
    have key : (q * x) ^ (m + 1) - x ^ (m + 1) =
        ((q - 1) * x) * ((∑ i ∈ Finset.range (m + 1), q ^ i) * x ^ m) := by
      have hg : (q - 1) * ∑ i ∈ Finset.range (m + 1), q ^ i = q ^ (m + 1) - 1 :=
        mul_geom_sum q (m + 1)
      calc (q * x) ^ (m + 1) - x ^ (m + 1)
          = q ^ (m + 1) * x ^ (m + 1) - x ^ (m + 1) := by rw [mul_pow]
        _ = (q ^ (m + 1) - 1) * x ^ (m + 1) := by ring
        _ = ((q - 1) * ∑ i ∈ Finset.range (m + 1), q ^ i) * x ^ (m + 1) := by rw [hg]
        _ = ((q - 1) * x) * ((∑ i ∈ Finset.range (m + 1), q ^ i) * x ^ m) := by ring
    rw [key]
    exact mul_div_cancel_left₀ _ hqx

/-- q-derivative is additive: D_q(f + g) = D_q(f) + D_q(g). -/
theorem qDeriv_add (f g : R → R) (q x : R) :
    qDeriv (fun t => f t + g t) q x = qDeriv f q x + qDeriv g q x := by
  unfold qDeriv
  rw [show f (q * x) + g (q * x) - (f x + g x) =
      (f (q * x) - f x) + (g (q * x) - g x) from by ring, add_div]

/-- q-derivative is homogeneous: D_q(c·f) = c · D_q(f). -/
theorem qDeriv_smul (c : R) (f : R → R) (q x : R) :
    qDeriv (fun t => c * f t) q x = c * qDeriv f q x := by
  unfold qDeriv
  rw [show c * f (q * x) - c * f x = c * (f (q * x) - f x) from by ring, mul_div_assoc]

/-- q-derivative Leibniz rule (product rule):
D_q(f·g)(x) = f(qx) · D_q(g)(x) + g(x) · D_q(f)(x).
This is Chan §15's key identity for q-calculus. -/
theorem qDeriv_mul (f g : R → R) (q x : R) (hqx : (q - 1) * x ≠ 0) :
    qDeriv (fun t => f t * g t) q x =
    f (q * x) * qDeriv g q x + g x * qDeriv f q x := by
  have := hqx
  unfold qDeriv
  field_simp
  ring

/-- Alternative form of Leibniz rule:
D_q(f·g)(x) = g(qx) · D_q(f)(x) + f(x) · D_q(g)(x). -/
theorem qDeriv_mul' (f g : R → R) (q x : R) (hqx : (q - 1) * x ≠ 0) :
    qDeriv (fun t => f t * g t) q x =
    g (q * x) * qDeriv f q x + f x * qDeriv g q x := by
  have := hqx
  unfold qDeriv
  field_simp
  ring

/-- q-derivative of subtraction: D_q(f - g) = D_q(f) - D_q(g). -/
theorem qDeriv_sub (f g : R → R) (q x : R) :
    qDeriv (fun t => f t - g t) q x = qDeriv f q x - qDeriv g q x := by
  unfold qDeriv
  rw [show f (q * x) - g (q * x) - (f x - g x) =
      (f (q * x) - f x) - (g (q * x) - g x) from by ring, sub_div]

/-- Iterated q-derivative: D_q^0 f = f, D_q^{n+1} f = D_q(D_q^n f). -/
noncomputable def qDerivIter (f : R → R) (q : R) : ℕ → R → R
  | 0 => f
  | n + 1 => fun x => qDeriv (qDerivIter f q n) q x

theorem qDerivIter_zero (f : R → R) (q : R) : qDerivIter f q 0 = f := rfl

theorem qDerivIter_succ (f : R → R) (q : R) (n : ℕ) :
    qDerivIter f q (n + 1) = fun x => qDeriv (qDerivIter f q n) q x := rfl

/-- D_q^2(x^n) = [n]_q · [n-1]_q · x^{n-2} for n ≥ 2. -/
theorem qDerivIter_two_pow (q x : R) (hqx : (q - 1) * x ≠ 0)
    (hqqx : (q - 1) * (q * x) ≠ 0) (n : ℕ) (hn : 2 ≤ n) :
    qDerivIter (fun t => t ^ n) q 2 x =
    qInt q n * qInt q (n - 1) * x ^ (n - 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  simp only [qDerivIter, qDeriv, show m + 2 - 1 = m + 1 from by omega,
    show m + 2 - 2 = m from by omega]
  have inner_at_x : ((q * x) ^ (m + 2) - x ^ (m + 2)) / ((q - 1) * x) =
      qInt q (m + 2) * x ^ (m + 1) := by
    have := qDeriv_pow q x hqx (m + 2)
    simp only [qDeriv, show m + 2 - 1 = m + 1 from by omega] at this
    exact this
  have inner_at_qx : ((q * (q * x)) ^ (m + 2) - (q * x) ^ (m + 2)) / ((q - 1) * (q * x)) =
      qInt q (m + 2) * (q * x) ^ (m + 1) := by
    have := qDeriv_pow q (q * x) hqqx (m + 2)
    simp only [qDeriv, show m + 2 - 1 = m + 1 from by omega] at this
    exact this
  rw [inner_at_qx, inner_at_x]
  have inner2 : ((q * x) ^ (m + 1) - x ^ (m + 1)) / ((q - 1) * x) =
      qInt q (m + 1) * x ^ m := by
    have := qDeriv_pow q x hqx (m + 1)
    simp only [qDeriv, show m + 1 - 1 = m from by omega] at this
    exact this
  rw [show qInt q (m + 2) * (q * x) ^ (m + 1) - qInt q (m + 2) * x ^ (m + 1) =
      qInt q (m + 2) * ((q * x) ^ (m + 1) - x ^ (m + 1)) from by ring,
    mul_div_assoc, inner2]
  ring

/-- q-factorial: [n]_q! = [1]_q · [2]_q · ⋯ · [n]_q. -/
noncomputable def qFactorial (q : R) : ℕ → R
  | 0 => 1
  | n + 1 => qFactorial q n * qInt q (n + 1)

theorem qFactorial_zero (q : R) : qFactorial q 0 = 1 := rfl

theorem qFactorial_one (q : R) : qFactorial q 1 = 1 := by
  simp [qFactorial, qInt_one]

theorem qFactorial_two (q : R) : qFactorial q 2 = 1 + q := by
  simp [qFactorial, qInt_one, qInt_two]; ring

theorem qFactorial_three (q : R) :
    qFactorial q 3 = (1 + q) * (q ^ 2 + q + 1) := by
  change qFactorial q 2 * qInt q 3 = (1 + q) * (q ^ 2 + q + 1)
  rw [qFactorial_two, qInt_three]

theorem qFactorial_succ (q : R) (n : ℕ) :
    qFactorial q (n + 1) = qFactorial q n * qInt q (n + 1) := rfl

theorem qFactorial_ne_zero (q : R) (hq : ∀ k, 1 ≤ k → qInt q k ≠ 0) (n : ℕ) :
    qFactorial q n ≠ 0 := by
  induction n with
  | zero => exact one_ne_zero
  | succ m ih => exact mul_ne_zero ih (hq (m + 1) (by omega))

/-- Truncated q-exponential: e_q(x;N) = ∑_{k=0}^{N} x^k / [k]_q!. -/
noncomputable def qExpTrunc (q x : R) : ℕ → R
  | 0 => 1
  | n + 1 => qExpTrunc q x n + x ^ (n + 1) / qFactorial q (n + 1)

theorem qExpTrunc_zero (q x : R) : qExpTrunc q x 0 = 1 := rfl

theorem qExpTrunc_one (q x : R) : qExpTrunc q x 1 = 1 + x := by
  simp [qExpTrunc, qFactorial, qInt_one]

theorem qExpTrunc_succ (q x : R) (n : ℕ) :
    qExpTrunc q x (n + 1) = qExpTrunc q x n + x ^ (n + 1) / qFactorial q (n + 1) := rfl

/-- D_q(1 - z) = -1. -/
theorem qDeriv_one_sub_id (q x : R) (hqx : (q - 1) * x ≠ 0) :
    qDeriv (fun z => 1 - z) q x = -1 := by
  simp only [qDeriv]
  rw [show (1 - q * x - (1 - x)) / ((q - 1) * x) = (-(q - 1) * x) / ((q - 1) * x) from by
    congr 1; ring, show -(q - 1) * x = -1 * ((q - 1) * x) from by ring]
  exact mul_div_cancel_right₀ (-1) hqx

/-- D_q(1 - z·c) = -c for any constant c. -/
theorem qDeriv_one_sub_mul_const (q x c : R) (hqx : (q - 1) * x ≠ 0) :
    qDeriv (fun z => 1 - z * c) q x = -c := by
  simp only [qDeriv]
  rw [show (1 - q * x * c - (1 - x * c)) / ((q - 1) * x) =
      (-c * ((q - 1) * x)) / ((q - 1) * x) from by congr 1; ring]
  exact mul_div_cancel_right₀ (-c) hqx

/-- The q-derivative of the q-Pochhammer symbol:
D_q((z;q)_n)(a) = -[n]_q · (aq;q)_{n-1}.
This connects q-calculus to the partition-theoretic q-Pochhammer. -/
theorem qDeriv_qPoch (q a : R) (hqa : (q - 1) * a ≠ 0) (n : ℕ) :
    qDeriv (fun z => qPoch z q n) q a = -qInt q n * qPoch (a * q) q (n - 1) := by
  induction n with
  | zero =>
    simp [qDeriv, qInt_zero, qPoch_zero]
  | succ m ih =>
    have heq : (fun z => qPoch z q (m + 1)) = (fun z => qPoch z q m * (1 - z * q ^ m)) := by
      ext z; simp [qPoch_succ]
    rw [heq, qDeriv_mul (fun z => qPoch z q m) (fun z => 1 - z * q ^ m) q a hqa,
      qDeriv_one_sub_mul_const q a (q ^ m) hqa, ih,
      show q * a = a * q from mul_comm q a]
    cases m with
    | zero => simp [qPoch, qInt_zero, qInt_one]
    | succ k =>
      simp only [Nat.succ_sub_one]
      rw [qInt_succ q (k + 1)]
      have hexp : qPoch (a * q) q (k + 1) = qPoch (a * q) q k * (1 - a * q ^ (k + 1)) := by
        rw [qPoch_succ]; ring_nf
      rw [hexp]
      ring

/-- q-falling factorial: [n]_q^{(k)} = [n]_q · [n-1]_q · ⋯ · [n-k+1]_q.
This is the q-analog of the falling factorial n(n-1)⋯(n-k+1). -/
noncomputable def qFallingFactorial (q : R) (n k : ℕ) : R :=
  ∏ i ∈ Finset.range k, qInt q (n - i)

theorem qFallingFactorial_zero (q : R) (n : ℕ) : qFallingFactorial q n 0 = 1 := by
  simp [qFallingFactorial]

theorem qFallingFactorial_succ (q : R) (n k : ℕ) :
    qFallingFactorial q n (k + 1) = qFallingFactorial q n k * qInt q (n - k) := by
  simp [qFallingFactorial, Finset.prod_range_succ]

/-- Iterated q-derivative of x^n:
D_q^k(x^n) = [n]_q · [n-1]_q · ⋯ · [n-k+1]_q · x^{n-k}.
The hypothesis requires (q-1)·(q^j·x) ≠ 0 for all j < k,
ensuring each q-derivative step is well-defined. -/
theorem qDerivIter_pow_aux (q : R) (n k : ℕ) (hk : k ≤ n) :
    ∀ x : R, (∀ j : ℕ, j < k → (q - 1) * (q ^ j * x) ≠ 0) →
    qDerivIter (fun t => t ^ n) q k x = qFallingFactorial q n k * x ^ (n - k) := by
  induction k with
  | zero =>
    intro x _
    simp [qDerivIter, qFallingFactorial_zero]
  | succ m ihm =>
    intro x hiter
    have hm_le : m ≤ n := by omega
    have hm_iter : ∀ j : ℕ, j < m → (q - 1) * (q ^ j * x) ≠ 0 :=
      fun j hj => hiter j (by omega)
    have ih_x := ihm hm_le x hm_iter
    have hqx_iter : ∀ j : ℕ, j < m → (q - 1) * (q ^ j * (q * x)) ≠ 0 := by
      intro j hj
      rw [show q ^ j * (q * x) = q ^ (j + 1) * x from by ring]
      exact hiter (j + 1) (by omega)
    have ih_qx := ihm hm_le (q * x) hqx_iter
    simp only [qDerivIter, qDeriv]
    rw [ih_qx, ih_x]
    rw [show qFallingFactorial q n m * (q * x) ^ (n - m) -
        qFallingFactorial q n m * x ^ (n - m) =
        qFallingFactorial q n m * ((q * x) ^ (n - m) - x ^ (n - m)) from by ring,
      mul_div_assoc]
    have hqx0 : (q - 1) * x ≠ 0 := by
      have := hiter 0 (by omega)
      simpa using this
    have inner := qDeriv_pow q x hqx0 (n - m)
    simp only [qDeriv] at inner
    rw [inner, qFallingFactorial_succ]
    rw [show qFallingFactorial q n m * (qInt q (n - m) * x ^ (n - m - 1)) =
        qFallingFactorial q n m * qInt q (n - m) * x ^ (n - m - 1) from by ring,
      show n - m - 1 = n - (m + 1) from by omega]

theorem qDerivIter_pow (q x : R) (n k : ℕ) (hk : k ≤ n)
    (hiter : ∀ j : ℕ, j < k → (q - 1) * (q ^ j * x) ≠ 0) :
    qDerivIter (fun t => t ^ n) q k x = qFallingFactorial q n k * x ^ (n - k) :=
  qDerivIter_pow_aux q n k hk x hiter

/-- q-factorial expressed as a Finset product: [n]_q! = ∏ i in range n, [i+1]_q. -/
theorem qFactorial_eq_prod (q : R) (n : ℕ) :
    qFactorial q n = ∏ i ∈ Finset.range n, qInt q (i + 1) := by
  induction n with
  | zero => simp [qFactorial_zero]
  | succ m ih => rw [qFactorial_succ, ih, Finset.prod_range_succ]

/-- q-falling factorial with k = n gives q-factorial:
[n]_q^{(n)} = [n]_q! -/
theorem qFallingFactorial_self (q : R) (n : ℕ) :
    qFallingFactorial q n n = qFactorial q n := by
  cases n with
  | zero => simp [qFallingFactorial, qFactorial]
  | succ m =>
    rw [qFactorial_eq_prod, qFallingFactorial]
    refine Finset.prod_nbij' (fun i => m - i) (fun i => m - i) ?_ ?_ ?_ ?_ ?_
    · intro i hi; simp only [Finset.mem_range] at hi ⊢; omega
    · intro i hi; simp only [Finset.mem_range] at hi ⊢; omega
    · intro i hi
      simp only [Finset.mem_range] at hi
      show m - (m - i) = i; omega
    · intro i hi
      simp only [Finset.mem_range] at hi
      show m - (m - i) = i; omega
    · intro i hi
      simp only [Finset.mem_range] at hi
      show qInt q (m + 1 - i) = qInt q (m - i + 1)
      congr 1; omega

/-- Special case: D_q^n(x^n) = [n]_q! as a constant function.
Since x^{n-n} = x^0 = 1, the iterated derivative becomes a constant. -/
theorem qDerivIter_pow_self (q x : R) (n : ℕ)
    (hiter : ∀ j : ℕ, j < n → (q - 1) * (q ^ j * x) ≠ 0) :
    qDerivIter (fun t => t ^ n) q n x = qFactorial q n := by
  rw [qDerivIter_pow q x n n le_rfl hiter, qFallingFactorial_self,
    show n - n = 0 from by omega, pow_zero, mul_one]

/-- [n]_q^{(1)} = [n]_q: the q-falling factorial of depth 1 is just the q-integer. -/
theorem qFallingFactorial_one (q : R) (n : ℕ) :
    qFallingFactorial q n 1 = qInt q n := by
  simp [qFallingFactorial]

/-- [n]_q^{(2)} = [n]_q · [n-1]_q. -/
theorem qFallingFactorial_two (q : R) (n : ℕ) :
    qFallingFactorial q n 2 = qInt q n * qInt q (n - 1) := by
  simp [qFallingFactorial, Finset.prod_range_succ]

/-- The q-falling factorial vanishes when k > n because qInt q 0 = 0 appears as a factor. -/
theorem qFallingFactorial_eq_zero_of_gt (q : R) (n k : ℕ) (hk : n < k) :
    qFallingFactorial q n k = 0 := by
  rw [qFallingFactorial]
  apply Finset.prod_eq_zero (Finset.mem_range.mpr hk)
  simp [qInt_zero]

/-- The q-falling factorial is the ratio of q-factorials:
[n]_q^{(k)} = [n]_q! / [n-k]_q! when [n-k]_q! ≠ 0. -/
theorem qFallingFactorial_eq_div (q : R) (n k : ℕ) (hk : k ≤ n)
    (hfac : qFactorial q (n - k) ≠ 0) :
    qFallingFactorial q n k = qFactorial q n / qFactorial q (n - k) := by
  have h_split : ∀ k n : ℕ, k ≤ n → qFactorial q n = qFallingFactorial q n k * qFactorial q (n - k) := by
    intro k
    induction k with
    | zero => intro n' _; simp [qFallingFactorial_zero]
    | succ m ih =>
      intro n' h_le'
      have h_succ : n' - m = (n' - (m + 1)) + 1 := by omega
      rw [qFallingFactorial_succ, mul_assoc]
      rw [show qInt q (n' - m) * qFactorial q (n' - (m + 1)) = qFactorial q (n' - m) from by
        rw [mul_comm, h_succ, qFactorial_succ]]
      exact ih n' (by omega)
  rw [h_split k n hk, mul_div_cancel_right₀ _ hfac]

/-- `[n+1]_q / [n+1]_q! = 1 / [n]_q!` when `[n+1]_q ≠ 0`. -/
theorem qInt_div_qFactorial_succ (q : R) (n : ℕ)
    (hqn : qInt q (n + 1) ≠ 0) :
    qInt q (n + 1) / qFactorial q (n + 1) = 1 / qFactorial q n := by
  rw [qFactorial_succ, div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev]
  rw [← mul_assoc, mul_inv_cancel₀ hqn, one_mul]

/-- Helper: D_q(x^{n+1}/[n+1]_q!) = x^n/[n]_q!.
This is the q-analog of d/dx(x^{n+1}/(n+1)!) = x^n/n!. -/
private theorem qDeriv_pow_div_factorial (q a : R) (hqa : (q - 1) * a ≠ 0)
    (n : ℕ) (_hfac : qFactorial q (n + 1) ≠ 0)
    (hqn : qInt q (n + 1) ≠ 0) :
    qDeriv (fun x => x ^ (n + 1) / qFactorial q (n + 1)) q a =
      a ^ n / qFactorial q n := by
  rw [show (fun x => x ^ (n + 1) / qFactorial q (n + 1)) =
      (fun x => (qFactorial q (n + 1))⁻¹ * x ^ (n + 1)) from by
    ext x; rw [div_eq_mul_inv, mul_comm]]
  rw [qDeriv_smul, qDeriv_pow q a hqa (n + 1)]
  simp only [Nat.add_sub_cancel]
  calc
    (qFactorial q (n + 1))⁻¹ * (qInt q (n + 1) * a ^ n)
        = (qInt q (n + 1) / qFactorial q (n + 1)) * a ^ n := by
      rw [div_eq_mul_inv]
      ring
    _ = (1 / qFactorial q n) * a ^ n := by
      rw [qInt_div_qFactorial_succ q n hqn]
    _ = a ^ n / qFactorial q n := by
      rw [div_eq_mul_inv]
      ring

/-- The q-derivative of the truncated q-exponential:
D_q(e_q(x; n+1)) = e_q(x; n). This is the q-analog of d/dx(e^x) = e^x. -/
theorem qDeriv_qExpTrunc (q a : R) (hqa : (q - 1) * a ≠ 0)
    (hq_int : ∀ k, 1 ≤ k → qInt q k ≠ 0) (n : ℕ) :
    qDeriv (fun x => qExpTrunc q x (n + 1)) q a = qExpTrunc q a n := by
  induction n with
  | zero =>
    -- D_q(1 + x/[1]_q!) = D_q(1) + D_q(x/1) = 0 + 1 = 1 = e_q(a;0)
    rw [show (fun x => qExpTrunc q x (0 + 1)) =
        (fun x => qExpTrunc q x 0 + x ^ (0 + 1) / qFactorial q (0 + 1)) from by
      ext; rfl]
    rw [qDeriv_add]
    rw [show (fun x => qExpTrunc q x 0) = (fun _ => (1 : R)) from by ext; rfl]
    rw [qDeriv_const]
    rw [qDeriv_pow_div_factorial q a hqa 0
      (qFactorial_ne_zero q hq_int 1) (hq_int 1 (by omega))]
    simp [qExpTrunc_zero, qFactorial_zero, zero_add]
  | succ m ih =>
    rw [show (fun x => qExpTrunc q x (m + 2)) =
        (fun x => qExpTrunc q x (m + 1) + x ^ (m + 2) / qFactorial q (m + 2)) from by
      ext; rfl]
    rw [qDeriv_add, ih]
    rw [qDeriv_pow_div_factorial q a hqa (m + 1)
      (qFactorial_ne_zero q hq_int (m + 2)) (hq_int (m + 2) (by omega))]
    rfl

/-- After `n` q-derivatives, `x^n` is constant, so the next q-derivative vanishes. -/
theorem qDerivIter_pow_succ_self (q x : R) (n : ℕ)
    (hiter : ∀ j : ℕ, j ≤ n → (q - 1) * (q ^ j * x) ≠ 0) :
    qDerivIter (fun t => t ^ n) q (n + 1) x = 0 := by
  rw [qDerivIter_succ]
  simp only [qDeriv]
  have h_qx : qDerivIter (fun t => t ^ n) q n (q * x) = qFactorial q n := by
    apply qDerivIter_pow_self
    intro j hj
    rw [show q ^ j * (q * x) = q ^ (j + 1) * x from by
      rw [pow_succ]
      ring]
    exact hiter (j + 1) (by omega)
  have h_x : qDerivIter (fun t => t ^ n) q n x = qFactorial q n := by
    apply qDerivIter_pow_self
    intro j hj
    exact hiter j (by omega)
  rw [h_qx, h_x]
  simp [zero_div]

/-- The top q-Taylor monomial term extracted from `x^n`.
It is written at a nonzero expansion point because this file's `qDeriv`
is a difference quotient with denominator `(q - 1) * x`. -/
noncomputable def qTaylorMonomialTopTerm (q x : R) (n : ℕ) : R :=
  (qDerivIter (fun t => t ^ n) q n x / qFactorial q n) * x ^ n

/-- The top q-Taylor term of the monomial `x^n` reconstructs `x^n`. -/
theorem qTaylorMonomialTopTerm_eq_pow (q x : R) (n : ℕ)
    (hiter : ∀ j : ℕ, j < n → (q - 1) * (q ^ j * x) ≠ 0)
    (hfac : qFactorial q n ≠ 0) :
    qTaylorMonomialTopTerm q x n = x ^ n := by
  unfold qTaylorMonomialTopTerm
  rw [qDerivIter_pow_self q x n hiter, div_self hfac, one_mul]

/-- The zeroth top q-Taylor monomial term is the constant monomial. -/
theorem qTaylorMonomialTopTerm_zero (q x : R) :
    qTaylorMonomialTopTerm q x 0 = 1 := by
  simp [qTaylorMonomialTopTerm, qDerivIter, qFactorial]

/-- The first top q-Taylor monomial term reconstructs `x`. -/
theorem qTaylorMonomialTopTerm_one (q x : R) (hqx : (q - 1) * x ≠ 0) :
    qTaylorMonomialTopTerm q x 1 = x := by
  rw [qTaylorMonomialTopTerm_eq_pow q x 1]
  · simp
  · intro j hj
    have hj0 : j = 0 := by omega
    subst j
    simpa using hqx
  · simp [qFactorial_one]

/-- The second top q-Taylor monomial term reconstructs `x^2`. -/
theorem qTaylorMonomialTopTerm_two (q x : R)
    (h0 : (q - 1) * x ≠ 0) (h1 : (q - 1) * (q * x) ≠ 0)
    (hfac : 1 + q ≠ 0) :
    qTaylorMonomialTopTerm q x 2 = x ^ 2 := by
  rw [qTaylorMonomialTopTerm_eq_pow q x 2]
  · intro j hj
    interval_cases j
    · simpa using h0
    · simpa using h1
  · simpa [qFactorial_two, add_comm] using hfac

/-- The third top q-Taylor monomial term reconstructs `x^3`. -/
theorem qTaylorMonomialTopTerm_three (q x : R)
    (h0 : (q - 1) * x ≠ 0) (h1 : (q - 1) * (q * x) ≠ 0)
    (h2 : (q - 1) * (q ^ 2 * x) ≠ 0)
    (hfac : (1 + q) * (q ^ 2 + q + 1) ≠ 0) :
    qTaylorMonomialTopTerm q x 3 = x ^ 3 := by
  rw [qTaylorMonomialTopTerm_eq_pow q x 3]
  · intro j hj
    interval_cases j
    · simpa using h0
    · simpa using h1
    · simpa using h2
  · simpa [qFactorial_three] using hfac

/-- A finite polynomial written in the monomial basis. -/
noncomputable def qPolynomialTrunc (coeff : ℕ → R) (N : ℕ) (x : R) : R :=
  natSum (fun n => coeff n * x ^ n) N

/-- The finite polynomial reconstructed from the top q-Taylor monomial terms. -/
noncomputable def qTaylorPolynomialTopTrunc (coeff : ℕ → R) (q x : R) (N : ℕ) : R :=
  natSum (fun n => coeff n * qTaylorMonomialTopTerm q x n) N

/-- The monomial-basis polynomial truncation satisfies the usual successor
recurrence. -/
theorem qPolynomialTrunc_succ (coeff : ℕ → R) (N : ℕ) (x : R) :
    qPolynomialTrunc coeff (N + 1) x =
      qPolynomialTrunc coeff N x + coeff (N + 1) * x ^ (N + 1) := by
  simp [qPolynomialTrunc, natSum]

/-- The top-term q-Taylor reconstruction satisfies the same finite successor
recurrence, with the top q-Taylor monomial in the new degree. -/
theorem qTaylorPolynomialTopTrunc_succ (coeff : ℕ → R) (q x : R) (N : ℕ) :
    qTaylorPolynomialTopTrunc coeff q x (N + 1) =
      qTaylorPolynomialTopTrunc coeff q x N +
        coeff (N + 1) * qTaylorMonomialTopTerm q x (N + 1) := by
  simp [qTaylorPolynomialTopTrunc, natSum]

/-- The zeroth monomial-basis polynomial truncation is the constant term. -/
theorem qPolynomialTrunc_zero (coeff : ℕ → R) (x : R) :
    qPolynomialTrunc coeff 0 x = coeff 0 := by
  simp [qPolynomialTrunc, natSum]

/-- The first monomial-basis polynomial truncation is `c₀ + c₁ x`. -/
theorem qPolynomialTrunc_one (coeff : ℕ → R) (x : R) :
    qPolynomialTrunc coeff 1 x = coeff 0 + coeff 1 * x := by
  simp [qPolynomialTrunc, natSum]

/-- The second monomial-basis polynomial truncation is
`c₀ + c₁ x + c₂ x²`. -/
theorem qPolynomialTrunc_two (coeff : ℕ → R) (x : R) :
    qPolynomialTrunc coeff 2 x = coeff 0 + coeff 1 * x + coeff 2 * x ^ 2 := by
  simp [qPolynomialTrunc, natSum]

/-- The third monomial-basis polynomial truncation is
`c₀ + c₁ x + c₂ x² + c₃ x³`. -/
theorem qPolynomialTrunc_three (coeff : ℕ → R) (x : R) :
    qPolynomialTrunc coeff 3 x =
      coeff 0 + coeff 1 * x + coeff 2 * x ^ 2 + coeff 3 * x ^ 3 := by
  rw [show (3 : ℕ) = 2 + 1 by norm_num, qPolynomialTrunc_succ,
    qPolynomialTrunc_two]

/-- The zeroth top-term q-Taylor truncation is the constant term. -/
theorem qTaylorPolynomialTopTrunc_zero (coeff : ℕ → R) (q x : R) :
    qTaylorPolynomialTopTrunc coeff q x 0 = coeff 0 := by
  simp [qTaylorPolynomialTopTrunc, natSum, qTaylorMonomialTopTerm_zero]

/-- The first top-term q-Taylor truncation reconstructs `c₀ + c₁ x`. -/
theorem qTaylorPolynomialTopTrunc_one (coeff : ℕ → R) (q x : R)
    (hqx : (q - 1) * x ≠ 0) :
    qTaylorPolynomialTopTrunc coeff q x 1 = coeff 0 + coeff 1 * x := by
  simp [qTaylorPolynomialTopTrunc, natSum, qTaylorMonomialTopTerm_zero,
    qTaylorMonomialTopTerm_one q x hqx]

/-- A finite `natSum` of the zero function is zero. -/
theorem natSum_zero_function (N : ℕ) :
    natSum (fun _ => (0 : R)) N = 0 := by
  induction N with
  | zero =>
      simp [natSum]
  | succ N ih =>
      rw [natSum_succ, ih]
      simp

/-- The monomial-basis polynomial with zero coefficients is zero. -/
theorem qPolynomialTrunc_zero_coeff (N : ℕ) (x : R) :
    qPolynomialTrunc (fun _ => (0 : R)) N x = 0 := by
  unfold qPolynomialTrunc
  simpa using natSum_zero_function (R := R) N

/-- The top-term q-Taylor reconstruction with zero coefficients is zero. -/
theorem qTaylorPolynomialTopTrunc_zero_coeff (q x : R) (N : ℕ) :
    qTaylorPolynomialTopTrunc (fun _ => (0 : R)) q x N = 0 := by
  unfold qTaylorPolynomialTopTrunc
  simpa using natSum_zero_function (R := R) N

/-- Finite monomial-basis polynomials are additive in their coefficient
sequence. -/
theorem qPolynomialTrunc_add (coeff₁ coeff₂ : ℕ → R) (N : ℕ) (x : R) :
    qPolynomialTrunc (fun n => coeff₁ n + coeff₂ n) N x =
      qPolynomialTrunc coeff₁ N x + qPolynomialTrunc coeff₂ N x := by
  unfold qPolynomialTrunc
  induction N with
  | zero =>
      simp [natSum]
  | succ N ih =>
      repeat rw [natSum_succ]
      rw [ih]
      ring

/-- Finite monomial-basis polynomials are homogeneous in their coefficient
sequence. -/
theorem qPolynomialTrunc_smul (c : R) (coeff : ℕ → R) (N : ℕ) (x : R) :
    qPolynomialTrunc (fun n => c * coeff n) N x = c * qPolynomialTrunc coeff N x := by
  unfold qPolynomialTrunc
  induction N with
  | zero =>
      simp [natSum]
  | succ N ih =>
      repeat rw [natSum_succ]
      rw [ih]
      ring

/-- Finite monomial-basis polynomials are negated by negating their
coefficient sequence. -/
theorem qPolynomialTrunc_neg (coeff : ℕ → R) (N : ℕ) (x : R) :
    qPolynomialTrunc (fun n => - coeff n) N x = - qPolynomialTrunc coeff N x := by
  simpa using (qPolynomialTrunc_smul (R := R) (-1) coeff N x)

/-- Finite monomial-basis polynomials subtract coefficientwise. -/
theorem qPolynomialTrunc_sub (coeff₁ coeff₂ : ℕ → R) (N : ℕ) (x : R) :
    qPolynomialTrunc (fun n => coeff₁ n - coeff₂ n) N x =
      qPolynomialTrunc coeff₁ N x - qPolynomialTrunc coeff₂ N x := by
  unfold qPolynomialTrunc
  induction N with
  | zero =>
      simp [natSum]
  | succ N ih =>
      repeat rw [natSum_succ]
      rw [ih]
      ring

/-- A monomial-basis polynomial truncation only depends on the coefficients
up to the truncation bound. -/
theorem qPolynomialTrunc_congr {coeff₁ coeff₂ : ℕ → R} {N : ℕ} (x : R)
    (hcoeff : ∀ n : ℕ, n ≤ N → coeff₁ n = coeff₂ n) :
    qPolynomialTrunc coeff₁ N x = qPolynomialTrunc coeff₂ N x := by
  induction N with
  | zero =>
      simp [qPolynomialTrunc, natSum, hcoeff 0 (by omega)]
  | succ N ih =>
      rw [qPolynomialTrunc_succ, qPolynomialTrunc_succ]
      rw [ih (fun n hn => hcoeff n (by omega)), hcoeff (N + 1) (by omega)]

/-- Enlarging a monomial truncation bound does not change the value when all
new coefficients vanish. -/
theorem qPolynomialTrunc_eq_of_coeff_zero_above {coeff : ℕ → R} {M N : ℕ}
    (x : R) (hMN : M ≤ N)
    (hzero : ∀ n : ℕ, M < n → n ≤ N → coeff n = 0) :
    qPolynomialTrunc coeff N x = qPolynomialTrunc coeff M x := by
  induction N generalizing M with
  | zero =>
      have hM : M = 0 := by omega
      subst M
      rfl
  | succ N ih =>
      by_cases htop : M = N + 1
      · subst M
        rfl
      · have hMN' : M ≤ N := by omega
        rw [qPolynomialTrunc_succ,
          ih hMN' (fun n hm hn => hzero n hm (by omega))]
        have hcoeff : coeff (N + 1) = 0 := hzero (N + 1) (by omega) le_rfl
        rw [hcoeff, zero_mul, add_zero]

/-- The repository's inclusive `natSum` agrees with the usual Finset sum over
`range (N+1)`. -/
theorem natSum_eq_sum_range (f : ℕ → R) (N : ℕ) :
    natSum f N = ∑ n ∈ Finset.range (N + 1), f n := by
  induction N with
  | zero =>
      simp [natSum]
  | succ N ih =>
      rw [natSum_succ, ih]
      simp [Finset.sum_range_succ, Nat.add_assoc]

/-- A coefficient sequence coming from a Mathlib polynomial evaluates to the
same value as that polynomial when truncated at its degree. -/
theorem qPolynomialTrunc_coeff_natDegree_eq_eval (p : Polynomial R) (x : R) :
    qPolynomialTrunc (fun n => p.coeff n) p.natDegree x = p.eval x := by
  unfold qPolynomialTrunc
  rw [natSum_eq_sum_range]
  exact (Polynomial.eval_eq_sum_range (p := p) x).symm

/-- A coefficient sequence coming from a Mathlib polynomial evaluates to the
same value as that polynomial at any truncation bound above its degree. -/
theorem qPolynomialTrunc_coeff_eq_eval_of_natDegree_le (p : Polynomial R) (x : R)
    {N : ℕ} (hN : p.natDegree ≤ N) :
    qPolynomialTrunc (fun n => p.coeff n) N x = p.eval x := by
  unfold qPolynomialTrunc
  rw [natSum_eq_sum_range]
  exact (Polynomial.eval_eq_sum_range' (p := p) (n := N + 1) (by omega) x).symm

/-- Strict-bound version of polynomial truncation: truncating beyond the
degree evaluates the original polynomial. -/
theorem qPolynomialTrunc_coeff_eq_eval_of_natDegree_lt (p : Polynomial R) (x : R)
    {N : ℕ} (hN : p.natDegree < N) :
    qPolynomialTrunc (fun n => p.coeff n) N x = p.eval x :=
  qPolynomialTrunc_coeff_eq_eval_of_natDegree_le p x (Nat.le_of_lt hN)

/-- Truncating a polynomial coefficient sequence above its `natDegree` gives
the same monomial truncation as truncating exactly at `natDegree`. -/
theorem qPolynomialTrunc_coeff_eq_natDegree_of_natDegree_le (p : Polynomial R)
    (x : R) {N : ℕ} (hN : p.natDegree ≤ N) :
    qPolynomialTrunc (fun n => p.coeff n) N x =
      qPolynomialTrunc (fun n => p.coeff n) p.natDegree x := by
  apply qPolynomialTrunc_eq_of_coeff_zero_above x hN
  intro n hn _hnN
  exact Polynomial.coeff_eq_zero_of_natDegree_lt hn

/-- A coefficient function that agrees with a polynomial through `natDegree`
and vanishes up to a larger truncation bound reconstructs that polynomial's
evaluation. This is the weaker, practical form of coefficient congruence. -/
theorem qPolynomialTrunc_coeff_congr_zero_tail_eq_eval
    (p : Polynomial R) (coeff : ℕ → R) (x : R) {N : ℕ}
    (hN : p.natDegree ≤ N)
    (hcoeff : ∀ n : ℕ, n ≤ p.natDegree → coeff n = p.coeff n)
    (hzero : ∀ n : ℕ, p.natDegree < n → n ≤ N → coeff n = 0) :
    qPolynomialTrunc coeff N x = p.eval x := by
  rw [qPolynomialTrunc_eq_of_coeff_zero_above x hN hzero]
  rw [qPolynomialTrunc_congr x hcoeff]
  exact qPolynomialTrunc_coeff_natDegree_eq_eval p x

/-- Strict-bound version of the weakened coefficient-congruence polynomial
evaluation theorem. -/
theorem qPolynomialTrunc_coeff_congr_zero_tail_eq_eval_of_natDegree_lt
    (p : Polynomial R) (coeff : ℕ → R) (x : R) {N : ℕ}
    (hN : p.natDegree < N)
    (hcoeff : ∀ n : ℕ, n ≤ p.natDegree → coeff n = p.coeff n)
    (hzero : ∀ n : ℕ, p.natDegree < n → n ≤ N → coeff n = 0) :
    qPolynomialTrunc coeff N x = p.eval x :=
  qPolynomialTrunc_coeff_congr_zero_tail_eq_eval p coeff x
    (Nat.le_of_lt hN) hcoeff hzero

/-- Global-tail version: if an external coefficient function agrees with a
polynomial through `natDegree` and vanishes in every higher degree, any larger
truncation evaluates the polynomial. -/
theorem qPolynomialTrunc_coeff_congr_global_zero_tail_eq_eval
    (p : Polynomial R) (coeff : ℕ → R) (x : R) {N : ℕ}
    (hN : p.natDegree ≤ N)
    (hcoeff : ∀ n : ℕ, n ≤ p.natDegree → coeff n = p.coeff n)
    (hzero : ∀ n : ℕ, p.natDegree < n → coeff n = 0) :
    qPolynomialTrunc coeff N x = p.eval x :=
  qPolynomialTrunc_coeff_congr_zero_tail_eq_eval p coeff x hN hcoeff
    (fun n hn _hnN => hzero n hn)

/-- The top-term q-Taylor reconstruction is additive in the coefficient
sequence. -/
theorem qTaylorPolynomialTopTrunc_add (coeff₁ coeff₂ : ℕ → R) (q x : R) (N : ℕ) :
    qTaylorPolynomialTopTrunc (fun n => coeff₁ n + coeff₂ n) q x N =
      qTaylorPolynomialTopTrunc coeff₁ q x N + qTaylorPolynomialTopTrunc coeff₂ q x N := by
  unfold qTaylorPolynomialTopTrunc
  induction N with
  | zero =>
      simp [natSum]
      ring
  | succ N ih =>
      repeat rw [natSum_succ]
      rw [ih]
      ring

/-- The top-term q-Taylor reconstruction is homogeneous in the coefficient
sequence. -/
theorem qTaylorPolynomialTopTrunc_smul (c : R) (coeff : ℕ → R) (q x : R) (N : ℕ) :
    qTaylorPolynomialTopTrunc (fun n => c * coeff n) q x N =
      c * qTaylorPolynomialTopTrunc coeff q x N := by
  unfold qTaylorPolynomialTopTrunc
  induction N with
  | zero =>
      simp [natSum]
      ring
  | succ N ih =>
      repeat rw [natSum_succ]
      rw [ih]
      ring

/-- The top-term q-Taylor reconstruction is negated by negating its
coefficient sequence. -/
theorem qTaylorPolynomialTopTrunc_neg (coeff : ℕ → R) (q x : R) (N : ℕ) :
    qTaylorPolynomialTopTrunc (fun n => - coeff n) q x N =
      - qTaylorPolynomialTopTrunc coeff q x N := by
  simpa using (qTaylorPolynomialTopTrunc_smul (R := R) (-1) coeff q x N)

/-- The top-term q-Taylor reconstruction subtracts coefficientwise. -/
theorem qTaylorPolynomialTopTrunc_sub (coeff₁ coeff₂ : ℕ → R) (q x : R) (N : ℕ) :
    qTaylorPolynomialTopTrunc (fun n => coeff₁ n - coeff₂ n) q x N =
      qTaylorPolynomialTopTrunc coeff₁ q x N - qTaylorPolynomialTopTrunc coeff₂ q x N := by
  unfold qTaylorPolynomialTopTrunc
  induction N with
  | zero =>
      simp [natSum]
      ring
  | succ N ih =>
      repeat rw [natSum_succ]
      rw [ih]
      ring

/-- The top-term q-Taylor truncation only depends on the coefficients up to
the truncation bound. -/
theorem qTaylorPolynomialTopTrunc_congr {coeff₁ coeff₂ : ℕ → R} {N : ℕ} (q x : R)
    (hcoeff : ∀ n : ℕ, n ≤ N → coeff₁ n = coeff₂ n) :
    qTaylorPolynomialTopTrunc coeff₁ q x N =
      qTaylorPolynomialTopTrunc coeff₂ q x N := by
  induction N with
  | zero =>
      simp [qTaylorPolynomialTopTrunc, natSum, hcoeff 0 (by omega)]
  | succ N ih =>
      rw [qTaylorPolynomialTopTrunc_succ, qTaylorPolynomialTopTrunc_succ]
      rw [ih (fun n hn => hcoeff n (by omega)), hcoeff (N + 1) (by omega)]

/-- Enlarging a top-term q-Taylor truncation bound does not change the value
when all new coefficients vanish. -/
theorem qTaylorPolynomialTopTrunc_eq_of_coeff_zero_above {coeff : ℕ → R} {M N : ℕ}
    (q x : R) (hMN : M ≤ N)
    (hzero : ∀ n : ℕ, M < n → n ≤ N → coeff n = 0) :
    qTaylorPolynomialTopTrunc coeff q x N =
      qTaylorPolynomialTopTrunc coeff q x M := by
  induction N generalizing M with
  | zero =>
      have hM : M = 0 := by omega
      subst M
      rfl
  | succ N ih =>
      by_cases htop : M = N + 1
      · subst M
        rfl
      · have hMN' : M ≤ N := by omega
        rw [qTaylorPolynomialTopTrunc_succ,
          ih hMN' (fun n hm hn => hzero n hm (by omega))]
        have hcoeff : coeff (N + 1) = 0 := hzero (N + 1) (by omega) le_rfl
        rw [hcoeff, zero_mul, add_zero]

/-- q-Taylor reconstruction for a finite polynomial in monomial form, using
the highest nonzero q-derivative of each monomial. -/
theorem qTaylorPolynomialTopTrunc_eq (coeff : ℕ → R) (q x : R) (N : ℕ)
    (hiter : ∀ n : ℕ, n ≤ N →
      ∀ j : ℕ, j < n → (q - 1) * (q ^ j * x) ≠ 0)
    (hfac : ∀ n : ℕ, n ≤ N → qFactorial q n ≠ 0) :
    qTaylorPolynomialTopTrunc coeff q x N = qPolynomialTrunc coeff N x := by
  unfold qTaylorPolynomialTopTrunc qPolynomialTrunc
  induction N with
  | zero =>
      rw [natSum_zero, natSum_zero]
      rw [qTaylorMonomialTopTerm_eq_pow q x 0
        (fun j hj => False.elim (by omega)) (hfac 0 le_rfl)]
  | succ N ih =>
      rw [natSum_succ, natSum_succ]
      rw [ih
        (fun n hn j hj => hiter n (by omega) j hj)
        (fun n hn => hfac n (by omega))]
      rw [qTaylorMonomialTopTerm_eq_pow q x (N + 1)
        (fun j hj => hiter (N + 1) le_rfl j hj) (hfac (N + 1) le_rfl)]

/-- A cleaner q-Taylor reconstruction theorem for finite polynomials: under
standard nonzero assumptions on `q`, the base point, and the q-integers, the
top-term q-Taylor reconstruction equals the original polynomial. -/
theorem qTaylorPolynomialTopTrunc_eq_of_nonzero (coeff : ℕ → R) (q x : R) (N : ℕ)
    (hq0 : q ≠ 0) (hq1 : q ≠ 1) (hx : x ≠ 0)
    (hq_int : ∀ k, 1 ≤ k → qInt q k ≠ 0) :
    qTaylorPolynomialTopTrunc coeff q x N = qPolynomialTrunc coeff N x := by
  apply qTaylorPolynomialTopTrunc_eq
  · intro _n _hn j _hj
    apply mul_ne_zero
    · exact sub_ne_zero.mpr hq1
    · apply mul_ne_zero
      · exact pow_ne_zero j hq0
      · exact hx
  · intro n _hn
    exact qFactorial_ne_zero q hq_int n

/-- q-Taylor reconstruction is insensitive to changing coefficients beyond the
truncation bound. -/
theorem qTaylorPolynomialTopTrunc_eq_of_coeff_congr {coeff₁ coeff₂ : ℕ → R}
    (q x : R) (N : ℕ)
    (hcoeff : ∀ n : ℕ, n ≤ N → coeff₁ n = coeff₂ n)
    (hiter : ∀ n : ℕ, n ≤ N →
      ∀ j : ℕ, j < n → (q - 1) * (q ^ j * x) ≠ 0)
    (hfac : ∀ n : ℕ, n ≤ N → qFactorial q n ≠ 0) :
    qTaylorPolynomialTopTrunc coeff₁ q x N = qPolynomialTrunc coeff₂ N x := by
  rw [qTaylorPolynomialTopTrunc_congr q x hcoeff,
    qTaylorPolynomialTopTrunc_eq coeff₂ q x N hiter hfac]

/-- Clean nonzero-assumption version of coefficientwise q-Taylor
reconstruction: coefficients beyond the truncation bound do not matter. -/
theorem qTaylorPolynomialTopTrunc_eq_of_coeff_congr_nonzero
    {coeff₁ coeff₂ : ℕ → R} (q x : R) (N : ℕ)
    (hcoeff : ∀ n : ℕ, n ≤ N → coeff₁ n = coeff₂ n)
    (hq0 : q ≠ 0) (hq1 : q ≠ 1) (hx : x ≠ 0)
    (hq_int : ∀ k, 1 ≤ k → qInt q k ≠ 0) :
    qTaylorPolynomialTopTrunc coeff₁ q x N = qPolynomialTrunc coeff₂ N x := by
  rw [qTaylorPolynomialTopTrunc_congr q x hcoeff,
    qTaylorPolynomialTopTrunc_eq_of_nonzero coeff₂ q x N hq0 hq1 hx hq_int]

/-- q-Taylor reconstruction of an actual Mathlib polynomial, truncated at its
degree. -/
theorem qTaylorPolynomialTopTrunc_coeff_natDegree_eq_eval (p : Polynomial R)
    (q x : R) (hq0 : q ≠ 0) (hq1 : q ≠ 1) (hx : x ≠ 0)
    (hq_int : ∀ k, 1 ≤ k → qInt q k ≠ 0) :
    qTaylorPolynomialTopTrunc (fun n => p.coeff n) q x p.natDegree = p.eval x := by
  rw [qTaylorPolynomialTopTrunc_eq_of_nonzero
    (fun n => p.coeff n) q x p.natDegree hq0 hq1 hx hq_int,
    qPolynomialTrunc_coeff_natDegree_eq_eval]

/-- q-Taylor reconstruction of an actual Mathlib polynomial at any truncation
bound above its degree. -/
theorem qTaylorPolynomialTopTrunc_coeff_eq_eval_of_natDegree_le (p : Polynomial R)
    (q x : R) {N : ℕ} (hN : p.natDegree ≤ N)
    (hq0 : q ≠ 0) (hq1 : q ≠ 1) (hx : x ≠ 0)
    (hq_int : ∀ k, 1 ≤ k → qInt q k ≠ 0) :
    qTaylorPolynomialTopTrunc (fun n => p.coeff n) q x N = p.eval x := by
  rw [qTaylorPolynomialTopTrunc_eq_of_nonzero
    (fun n => p.coeff n) q x N hq0 hq1 hx hq_int,
    qPolynomialTrunc_coeff_eq_eval_of_natDegree_le p x hN]

/-- Strict-bound version of q-Taylor reconstruction for Mathlib polynomials. -/
theorem qTaylorPolynomialTopTrunc_coeff_eq_eval_of_natDegree_lt (p : Polynomial R)
    (q x : R) {N : ℕ} (hN : p.natDegree < N)
    (hq0 : q ≠ 0) (hq1 : q ≠ 1) (hx : x ≠ 0)
    (hq_int : ∀ k, 1 ≤ k → qInt q k ≠ 0) :
    qTaylorPolynomialTopTrunc (fun n => p.coeff n) q x N = p.eval x :=
  qTaylorPolynomialTopTrunc_coeff_eq_eval_of_natDegree_le
    p q x (Nat.le_of_lt hN) hq0 hq1 hx hq_int

/-- The q-Taylor truncation of a polynomial coefficient sequence is already
stable at the polynomial's `natDegree`; higher truncation bounds only add zero
coefficient terms. -/
theorem qTaylorPolynomialTopTrunc_coeff_eq_natDegree_of_natDegree_le
    (p : Polynomial R) (q x : R) {N : ℕ} (hN : p.natDegree ≤ N) :
    qTaylorPolynomialTopTrunc (fun n => p.coeff n) q x N =
      qTaylorPolynomialTopTrunc (fun n => p.coeff n) q x p.natDegree := by
  apply qTaylorPolynomialTopTrunc_eq_of_coeff_zero_above q x hN
  intro n hn _hnN
  exact Polynomial.coeff_eq_zero_of_natDegree_lt hn

/-- q-Taylor reconstruction from an externally supplied coefficient function:
it is enough to match the polynomial coefficients through `natDegree` and make
the added tail coefficients vanish up to the chosen truncation bound. -/
theorem qTaylorPolynomialTopTrunc_coeff_congr_zero_tail_eq_eval
    (p : Polynomial R) (coeff : ℕ → R) (q x : R) {N : ℕ}
    (hN : p.natDegree ≤ N)
    (hcoeff : ∀ n : ℕ, n ≤ p.natDegree → coeff n = p.coeff n)
    (hzero : ∀ n : ℕ, p.natDegree < n → n ≤ N → coeff n = 0)
    (hq0 : q ≠ 0) (hq1 : q ≠ 1) (hx : x ≠ 0)
    (hq_int : ∀ k, 1 ≤ k → qInt q k ≠ 0) :
    qTaylorPolynomialTopTrunc coeff q x N = p.eval x := by
  rw [qTaylorPolynomialTopTrunc_eq_of_coeff_zero_above q x hN hzero]
  rw [qTaylorPolynomialTopTrunc_congr q x hcoeff]
  exact qTaylorPolynomialTopTrunc_coeff_natDegree_eq_eval p q x hq0 hq1 hx hq_int

/-- Strict-bound version of q-Taylor reconstruction from an externally
supplied coefficient function with a vanishing added tail. -/
theorem qTaylorPolynomialTopTrunc_coeff_congr_zero_tail_eq_eval_of_natDegree_lt
    (p : Polynomial R) (coeff : ℕ → R) (q x : R) {N : ℕ}
    (hN : p.natDegree < N)
    (hcoeff : ∀ n : ℕ, n ≤ p.natDegree → coeff n = p.coeff n)
    (hzero : ∀ n : ℕ, p.natDegree < n → n ≤ N → coeff n = 0)
    (hq0 : q ≠ 0) (hq1 : q ≠ 1) (hx : x ≠ 0)
    (hq_int : ∀ k, 1 ≤ k → qInt q k ≠ 0) :
    qTaylorPolynomialTopTrunc coeff q x N = p.eval x :=
  qTaylorPolynomialTopTrunc_coeff_congr_zero_tail_eq_eval p coeff q x
    (Nat.le_of_lt hN) hcoeff hzero hq0 hq1 hx hq_int

/-- Global-tail version of q-Taylor reconstruction from external coefficients:
matching through `natDegree` and vanishing in every higher degree is enough for
any truncation bound above `natDegree`. -/
theorem qTaylorPolynomialTopTrunc_coeff_congr_global_zero_tail_eq_eval
    (p : Polynomial R) (coeff : ℕ → R) (q x : R) {N : ℕ}
    (hN : p.natDegree ≤ N)
    (hcoeff : ∀ n : ℕ, n ≤ p.natDegree → coeff n = p.coeff n)
    (hzero : ∀ n : ℕ, p.natDegree < n → coeff n = 0)
    (hq0 : q ≠ 0) (hq1 : q ≠ 1) (hx : x ≠ 0)
    (hq_int : ∀ k, 1 ≤ k → qInt q k ≠ 0) :
    qTaylorPolynomialTopTrunc coeff q x N = p.eval x :=
  qTaylorPolynomialTopTrunc_coeff_congr_zero_tail_eq_eval p coeff q x
    hN hcoeff (fun n hn _hnN => hzero n hn) hq0 hq1 hx hq_int

/-- q-Taylor reconstruction of a Mathlib polynomial from any coefficient
function agreeing with the polynomial coefficients through a truncation bound
above the degree. -/
theorem qTaylorPolynomialTopTrunc_coeff_congr_eq_eval_of_natDegree_le
    (p : Polynomial R) (coeff : ℕ → R) (q x : R) {N : ℕ}
    (hcoeff : ∀ n : ℕ, n ≤ N → coeff n = p.coeff n)
    (hN : p.natDegree ≤ N)
    (hq0 : q ≠ 0) (hq1 : q ≠ 1) (hx : x ≠ 0)
    (hq_int : ∀ k, 1 ≤ k → qInt q k ≠ 0) :
    qTaylorPolynomialTopTrunc coeff q x N = p.eval x := by
  rw [qTaylorPolynomialTopTrunc_eq_of_coeff_congr_nonzero
    q x N hcoeff hq0 hq1 hx hq_int,
    qPolynomialTrunc_coeff_eq_eval_of_natDegree_le p x hN]

/-- Strict-bound version of q-Taylor polynomial reconstruction from an
externally supplied coefficient function. -/
theorem qTaylorPolynomialTopTrunc_coeff_congr_eq_eval_of_natDegree_lt
    (p : Polynomial R) (coeff : ℕ → R) (q x : R) {N : ℕ}
    (hcoeff : ∀ n : ℕ, n ≤ N → coeff n = p.coeff n)
    (hN : p.natDegree < N)
    (hq0 : q ≠ 0) (hq1 : q ≠ 1) (hx : x ≠ 0)
    (hq_int : ∀ k, 1 ≤ k → qInt q k ≠ 0) :
    qTaylorPolynomialTopTrunc coeff q x N = p.eval x :=
  qTaylorPolynomialTopTrunc_coeff_congr_eq_eval_of_natDegree_le
    p coeff q x hcoeff (Nat.le_of_lt hN) hq0 hq1 hx hq_int

/-- The second top-term q-Taylor truncation reconstructs
`c₀ + c₁ x + c₂ x²`. -/
theorem qTaylorPolynomialTopTrunc_two (coeff : ℕ → R) (q x : R)
    (h0 : (q - 1) * x ≠ 0) (h1 : (q - 1) * (q * x) ≠ 0)
    (hfac : 1 + q ≠ 0) :
    qTaylorPolynomialTopTrunc coeff q x 2 = coeff 0 + coeff 1 * x + coeff 2 * x ^ 2 := by
  rw [qTaylorPolynomialTopTrunc_eq coeff q x 2]
  · simp [qPolynomialTrunc, natSum]
  · intro n hn j hj
    interval_cases n
    · omega
    · interval_cases j
      simpa using h0
    · interval_cases j
      · simpa using h0
      · simpa using h1
  · intro n hn
    interval_cases n
    · simp [qFactorial_zero]
    · simp [qFactorial_one]
    · simpa [qFactorial_two, add_comm] using hfac

/-- The third top-term q-Taylor truncation reconstructs
`c₀ + c₁ x + c₂ x² + c₃ x³`. -/
theorem qTaylorPolynomialTopTrunc_three (coeff : ℕ → R) (q x : R)
    (h0 : (q - 1) * x ≠ 0) (h1 : (q - 1) * (q * x) ≠ 0)
    (h2 : (q - 1) * (q ^ 2 * x) ≠ 0)
    (hfac2 : 1 + q ≠ 0)
    (hfac3 : (1 + q) * (q ^ 2 + q + 1) ≠ 0) :
    qTaylorPolynomialTopTrunc coeff q x 3 =
      coeff 0 + coeff 1 * x + coeff 2 * x ^ 2 + coeff 3 * x ^ 3 := by
  rw [show (3 : ℕ) = 2 + 1 by norm_num, qTaylorPolynomialTopTrunc_succ,
    qTaylorPolynomialTopTrunc_two coeff q x h0 h1 hfac2,
    qTaylorMonomialTopTerm_three q x h0 h1 h2 hfac3]

/-- Under standard nonzero assumptions, the third top-term q-Taylor
truncation reconstructs `c₀ + c₁ x + c₂ x² + c₃ x³`. This avoids unfolding
the iterated q-derivative directly and uses the general polynomial
reconstruction theorem. -/
theorem qTaylorPolynomialTopTrunc_three_of_nonzero (coeff : ℕ → R) (q x : R)
    (hq0 : q ≠ 0) (hq1 : q ≠ 1) (hx : x ≠ 0)
    (hq_int : ∀ k, 1 ≤ k → qInt q k ≠ 0) :
    qTaylorPolynomialTopTrunc coeff q x 3 =
      coeff 0 + coeff 1 * x + coeff 2 * x ^ 2 + coeff 3 * x ^ 3 := by
  rw [qTaylorPolynomialTopTrunc_eq_of_nonzero coeff q x 3 hq0 hq1 hx hq_int,
    qPolynomialTrunc_three]

theorem R_trunc_nesting_eleven (q : ℂ) :
    Ch11.R_trunc q 11 = 1 / (1 + q ^ 11 * Ch11.R_trunc q 10) := by
  simp [Ch11.R_trunc]

theorem R_trunc_nesting_twelve (q : ℂ) :
    Ch11.R_trunc q 12 = 1 / (1 + q ^ 12 * Ch11.R_trunc q 11) := by
  simp [Ch11.R_trunc]

theorem R_trunc_nesting_thirteen (q : ℂ) :
    Ch11.R_trunc q 13 = 1 / (1 + q ^ 13 * Ch11.R_trunc q 12) := by
  simp [Ch11.R_trunc]

theorem R_trunc_nesting_fourteen (q : ℂ) :
    Ch11.R_trunc q 14 = 1 / (1 + q ^ 14 * Ch11.R_trunc q 13) := by
  simp [Ch11.R_trunc]

theorem R_trunc_nesting_fifteen (q : ℂ) :
    Ch11.R_trunc q 15 = 1 / (1 + q ^ 15 * Ch11.R_trunc q 14) := by
  simp [Ch11.R_trunc]

theorem R_trunc_nesting_sixteen (q : ℂ) :
    Ch11.R_trunc q 16 = 1 / (1 + q ^ 16 * Ch11.R_trunc q 15) := by
  simp [Ch11.R_trunc]

theorem R_trunc_nesting_seventeen (q : ℂ) :
    Ch11.R_trunc q 17 = 1 / (1 + q ^ 17 * Ch11.R_trunc q 16) := by
  simp [Ch11.R_trunc]

theorem R_trunc_nesting_eighteen (q : ℂ) :
    Ch11.R_trunc q 18 = 1 / (1 + q ^ 18 * Ch11.R_trunc q 17) := by
  simp [Ch11.R_trunc]

theorem R_trunc_nesting_nineteen (q : ℂ) :
    Ch11.R_trunc q 19 = 1 / (1 + q ^ 19 * Ch11.R_trunc q 18) := by
  simp [Ch11.R_trunc]

theorem R_trunc_nesting_twenty (q : ℂ) :
    Ch11.R_trunc q 20 = 1 / (1 + q ^ 20 * Ch11.R_trunc q 19) := by
  simp [Ch11.R_trunc]

theorem R_trunc_nesting_twentyone (q : ℂ) :
    Ch11.R_trunc q 21 = 1 / (1 + q ^ 21 * Ch11.R_trunc q 20) := by
  simp [Ch11.R_trunc]

theorem R_trunc_nesting_twentytwo (q : ℂ) :
    Ch11.R_trunc q 22 = 1 / (1 + q ^ 22 * Ch11.R_trunc q 21) := by
  simp [Ch11.R_trunc]

theorem R_trunc_nesting_twentythree (q : ℂ) :
    Ch11.R_trunc q 23 = 1 / (1 + q ^ 23 * Ch11.R_trunc q 22) := by
  simp [Ch11.R_trunc]

theorem R_trunc_nesting_twentyfour (q : ℂ) :
    Ch11.R_trunc q 24 = 1 / (1 + q ^ 24 * Ch11.R_trunc q 23) := by
  simp [Ch11.R_trunc]

theorem R_trunc_nesting_twentyfive (q : ℂ) :
    Ch11.R_trunc q 25 = 1 / (1 + q ^ 25 * Ch11.R_trunc q 24) := by
  simp [Ch11.R_trunc]

theorem R_trunc_nesting_twentysix (q : ℂ) :
    Ch11.R_trunc q 26 = 1 / (1 + q ^ 26 * Ch11.R_trunc q 25) := by
  simp [Ch11.R_trunc]

theorem R_trunc_nesting_twentyseven (q : ℂ) :
    Ch11.R_trunc q 27 = 1 / (1 + q ^ 27 * Ch11.R_trunc q 26) := by
  simp [Ch11.R_trunc]

theorem R_trunc_nesting_twentyeight (q : ℂ) :
    Ch11.R_trunc q 28 = 1 / (1 + q ^ 28 * Ch11.R_trunc q 27) := by
  simp [Ch11.R_trunc]

theorem R_trunc_nesting_twentynine (q : ℂ) :
    Ch11.R_trunc q 29 = 1 / (1 + q ^ 29 * Ch11.R_trunc q 28) := by
  simp [Ch11.R_trunc]

theorem R_trunc_nesting_thirty (q : ℂ) :
    Ch11.R_trunc q 30 = 1 / (1 + q ^ 30 * Ch11.R_trunc q 29) := by
  simp [Ch11.R_trunc]

theorem R_trunc_nesting_thirtyone (q : ℂ) :
    Ch11.R_trunc q 31 = 1 / (1 + q ^ 31 * Ch11.R_trunc q 30) := by
  simp [Ch11.R_trunc]

theorem R_trunc_nesting_thirtytwo (q : ℂ) :
    Ch11.R_trunc q 32 = 1 / (1 + q ^ 32 * Ch11.R_trunc q 31) := by
  simp [Ch11.R_trunc]

theorem R_trunc_nesting_thirtythree (q : ℂ) :
    Ch11.R_trunc q 33 = 1 / (1 + q ^ 33 * Ch11.R_trunc q 32) := by
  simp [Ch11.R_trunc]

theorem R_trunc_nesting_thirtyfour (q : ℂ) :
    Ch11.R_trunc q 34 = 1 / (1 + q ^ 34 * Ch11.R_trunc q 33) := by
  simp [Ch11.R_trunc]

theorem R_trunc_nesting_thirtyfive (q : ℂ) :
    Ch11.R_trunc q 35 = 1 / (1 + q ^ 35 * Ch11.R_trunc q 34) := by
  simp [Ch11.R_trunc]

theorem R_trunc_nesting_thirtysix (q : ℂ) :
    Ch11.R_trunc q 36 = 1 / (1 + q ^ 36 * Ch11.R_trunc q 35) := by
  simp [Ch11.R_trunc]

theorem R_trunc_nesting_thirtyseven (q : ℂ) :
    Ch11.R_trunc q 37 = 1 / (1 + q ^ 37 * Ch11.R_trunc q 36) := by
  simp [Ch11.R_trunc]

theorem R_trunc_nesting_thirtyeight (q : ℂ) :
    Ch11.R_trunc q 38 = 1 / (1 + q ^ 38 * Ch11.R_trunc q 37) := by
  simp [Ch11.R_trunc]

theorem R_trunc_nesting_thirtynine (q : ℂ) :
    Ch11.R_trunc q 39 = 1 / (1 + q ^ 39 * Ch11.R_trunc q 38) := by
  simp [Ch11.R_trunc]

theorem R_trunc_nesting_forty (q : ℂ) :
    Ch11.R_trunc q 40 = 1 / (1 + q ^ 40 * Ch11.R_trunc q 39) := by
  simp [Ch11.R_trunc]

theorem R_trunc_nesting_fortyone (q : ℂ) :
    Ch11.R_trunc q 41 = 1 / (1 + q ^ 41 * Ch11.R_trunc q 40) := by
  simp [Ch11.R_trunc]

theorem R_trunc_nesting_fortytwo (q : ℂ) :
    Ch11.R_trunc q 42 = 1 / (1 + q ^ 42 * Ch11.R_trunc q 41) := by
  simp [Ch11.R_trunc]

theorem R_trunc_nesting_fortythree (q : ℂ) :
    Ch11.R_trunc q 43 = 1 / (1 + q ^ 43 * Ch11.R_trunc q 42) := by
  simp [Ch11.R_trunc]

theorem R_trunc_nesting_fortyfour (q : ℂ) :
    Ch11.R_trunc q 44 = 1 / (1 + q ^ 44 * Ch11.R_trunc q 43) := by
  simp [Ch11.R_trunc]

theorem R_trunc_nesting_fortyfive (q : ℂ) :
    Ch11.R_trunc q 45 = 1 / (1 + q ^ 45 * Ch11.R_trunc q 44) := by
  simp [Ch11.R_trunc]

theorem R_trunc_nesting_fortysix (q : ℂ) :
    Ch11.R_trunc q 46 = 1 / (1 + q ^ 46 * Ch11.R_trunc q 45) := by
  simp [Ch11.R_trunc]

theorem R_trunc_nesting_fortyseven (q : ℂ) :
    Ch11.R_trunc q 47 = 1 / (1 + q ^ 47 * Ch11.R_trunc q 46) := by
  simp [Ch11.R_trunc]

theorem R_trunc_nesting_fortyeight (q : ℂ) :
    Ch11.R_trunc q 48 = 1 / (1 + q ^ 48 * Ch11.R_trunc q 47) := by
  simp [Ch11.R_trunc]

theorem R_trunc_nesting_fortynine (q : ℂ) :
    Ch11.R_trunc q 49 = 1 / (1 + q ^ 49 * Ch11.R_trunc q 48) := by
  simp [Ch11.R_trunc]

theorem R_trunc_nesting_fifty (q : ℂ) :
    Ch11.R_trunc q 50 = 1 / (1 + q ^ 50 * Ch11.R_trunc q 49) := by
  simp [Ch11.R_trunc]

theorem R_trunc_nesting_fiftyone (q : ℂ) :
    Ch11.R_trunc q 51 = 1 / (1 + q ^ 51 * Ch11.R_trunc q 50) := by
  simp [Ch11.R_trunc]

theorem R_trunc_nesting_fiftytwo (q : ℂ) :
    Ch11.R_trunc q 52 = 1 / (1 + q ^ 52 * Ch11.R_trunc q 51) := by
  simp [Ch11.R_trunc]

theorem R_trunc_nesting_fiftythree (q : ℂ) :
    Ch11.R_trunc q 53 = 1 / (1 + q ^ 53 * Ch11.R_trunc q 52) := by
  simp [Ch11.R_trunc]

theorem R_trunc_nesting_fiftyfour (q : ℂ) :
    Ch11.R_trunc q 54 = 1 / (1 + q ^ 54 * Ch11.R_trunc q 53) := by
  simp [Ch11.R_trunc]

theorem R_trunc_nesting_fiftyfive (q : ℂ) :
    Ch11.R_trunc q 55 = 1 / (1 + q ^ 55 * Ch11.R_trunc q 54) := by
  simp [Ch11.R_trunc]

theorem R_trunc_nesting_fiftysix (q : ℂ) :
    Ch11.R_trunc q 56 = 1 / (1 + q ^ 56 * Ch11.R_trunc q 55) := by
  simp [Ch11.R_trunc]

theorem R_trunc_nesting_fiftyseven (q : ℂ) :
    Ch11.R_trunc q 57 = 1 / (1 + q ^ 57 * Ch11.R_trunc q 56) := by
  simp [Ch11.R_trunc]

theorem R_trunc_nesting_fiftyeight (q : ℂ) :
    Ch11.R_trunc q 58 = 1 / (1 + q ^ 58 * Ch11.R_trunc q 57) := by
  simp [Ch11.R_trunc]

theorem R_trunc_nesting_fiftynine (q : ℂ) :
    Ch11.R_trunc q 59 = 1 / (1 + q ^ 59 * Ch11.R_trunc q 58) := by
  simp [Ch11.R_trunc]

theorem R_trunc_nesting_sixty (q : ℂ) :
    Ch11.R_trunc q 60 = 1 / (1 + q ^ 60 * Ch11.R_trunc q 59) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_sixtyone (q : ℂ) :
    Ch11.R_trunc q 61 = 1 / (1 + q ^ 61 * Ch11.R_trunc q 60) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_sixtytwo (q : ℂ) :
    Ch11.R_trunc q 62 = 1 / (1 + q ^ 62 * Ch11.R_trunc q 61) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_sixtythree (q : ℂ) :
    Ch11.R_trunc q 63 = 1 / (1 + q ^ 63 * Ch11.R_trunc q 62) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_sixtyfour (q : ℂ) :
    Ch11.R_trunc q 64 = 1 / (1 + q ^ 64 * Ch11.R_trunc q 63) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_sixtyfive (q : ℂ) :
    Ch11.R_trunc q 65 = 1 / (1 + q ^ 65 * Ch11.R_trunc q 64) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_sixtysix (q : ℂ) :
    Ch11.R_trunc q 66 = 1 / (1 + q ^ 66 * Ch11.R_trunc q 65) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_sixtyseven (q : ℂ) :
    Ch11.R_trunc q 67 = 1 / (1 + q ^ 67 * Ch11.R_trunc q 66) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_sixtyeight (q : ℂ) :
    Ch11.R_trunc q 68 = 1 / (1 + q ^ 68 * Ch11.R_trunc q 67) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_sixtynine (q : ℂ) :
    Ch11.R_trunc q 69 = 1 / (1 + q ^ 69 * Ch11.R_trunc q 68) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_seventy (q : ℂ) :
    Ch11.R_trunc q 70 = 1 / (1 + q ^ 70 * Ch11.R_trunc q 69) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_seventyone (q : ℂ) :
    Ch11.R_trunc q 71 = 1 / (1 + q ^ 71 * Ch11.R_trunc q 70) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_seventytwo (q : ℂ) :
    Ch11.R_trunc q 72 = 1 / (1 + q ^ 72 * Ch11.R_trunc q 71) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_seventythree (q : ℂ) :
    Ch11.R_trunc q 73 = 1 / (1 + q ^ 73 * Ch11.R_trunc q 72) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_seventyfour (q : ℂ) :
    Ch11.R_trunc q 74 = 1 / (1 + q ^ 74 * Ch11.R_trunc q 73) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_seventyfive (q : ℂ) :
    Ch11.R_trunc q 75 = 1 / (1 + q ^ 75 * Ch11.R_trunc q 74) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_seventysix (q : ℂ) :
    Ch11.R_trunc q 76 = 1 / (1 + q ^ 76 * Ch11.R_trunc q 75) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_seventyseven (q : ℂ) :
    Ch11.R_trunc q 77 = 1 / (1 + q ^ 77 * Ch11.R_trunc q 76) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_seventyeight (q : ℂ) :
    Ch11.R_trunc q 78 = 1 / (1 + q ^ 78 * Ch11.R_trunc q 77) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_seventynine (q : ℂ) :
    Ch11.R_trunc q 79 = 1 / (1 + q ^ 79 * Ch11.R_trunc q 78) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_eighty (q : ℂ) :
    Ch11.R_trunc q 80 = 1 / (1 + q ^ 80 * Ch11.R_trunc q 79) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_eightyone (q : ℂ) :
    Ch11.R_trunc q 81 = 1 / (1 + q ^ 81 * Ch11.R_trunc q 80) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_eightytwo (q : ℂ) :
    Ch11.R_trunc q 82 = 1 / (1 + q ^ 82 * Ch11.R_trunc q 81) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_eightythree (q : ℂ) :
    Ch11.R_trunc q 83 = 1 / (1 + q ^ 83 * Ch11.R_trunc q 82) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_eightyfour (q : ℂ) :
    Ch11.R_trunc q 84 = 1 / (1 + q ^ 84 * Ch11.R_trunc q 83) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_eightyfive (q : ℂ) :
    Ch11.R_trunc q 85 = 1 / (1 + q ^ 85 * Ch11.R_trunc q 84) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_eightysix (q : ℂ) :
    Ch11.R_trunc q 86 = 1 / (1 + q ^ 86 * Ch11.R_trunc q 85) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_eightyseven (q : ℂ) :
    Ch11.R_trunc q 87 = 1 / (1 + q ^ 87 * Ch11.R_trunc q 86) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_eightyeight (q : ℂ) :
    Ch11.R_trunc q 88 = 1 / (1 + q ^ 88 * Ch11.R_trunc q 87) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_eightynine (q : ℂ) :
    Ch11.R_trunc q 89 = 1 / (1 + q ^ 89 * Ch11.R_trunc q 88) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_ninety (q : ℂ) :
    Ch11.R_trunc q 90 = 1 / (1 + q ^ 90 * Ch11.R_trunc q 89) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_ninetyone (q : ℂ) :
    Ch11.R_trunc q 91 = 1 / (1 + q ^ 91 * Ch11.R_trunc q 90) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_ninetytwo (q : ℂ) :
    Ch11.R_trunc q 92 = 1 / (1 + q ^ 92 * Ch11.R_trunc q 91) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_ninetythree (q : ℂ) :
    Ch11.R_trunc q 93 = 1 / (1 + q ^ 93 * Ch11.R_trunc q 92) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_ninetyfour (q : ℂ) :
    Ch11.R_trunc q 94 = 1 / (1 + q ^ 94 * Ch11.R_trunc q 93) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_ninetyfive (q : ℂ) :
    Ch11.R_trunc q 95 = 1 / (1 + q ^ 95 * Ch11.R_trunc q 94) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_ninetysix (q : ℂ) :
    Ch11.R_trunc q 96 = 1 / (1 + q ^ 96 * Ch11.R_trunc q 95) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_ninetyseven (q : ℂ) :
    Ch11.R_trunc q 97 = 1 / (1 + q ^ 97 * Ch11.R_trunc q 96) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_ninetyeight (q : ℂ) :
    Ch11.R_trunc q 98 = 1 / (1 + q ^ 98 * Ch11.R_trunc q 97) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_ninetynine (q : ℂ) :
    Ch11.R_trunc q 99 = 1 / (1 + q ^ 99 * Ch11.R_trunc q 98) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundred (q : ℂ) :
    Ch11.R_trunc q 100 = 1 / (1 + q ^ 100 * Ch11.R_trunc q 99) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredone (q : ℂ) :
    Ch11.R_trunc q 101 = 1 / (1 + q ^ 101 * Ch11.R_trunc q 100) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredtwo (q : ℂ) :
    Ch11.R_trunc q 102 = 1 / (1 + q ^ 102 * Ch11.R_trunc q 101) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredthree (q : ℂ) :
    Ch11.R_trunc q 103 = 1 / (1 + q ^ 103 * Ch11.R_trunc q 102) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredfour (q : ℂ) :
    Ch11.R_trunc q 104 = 1 / (1 + q ^ 104 * Ch11.R_trunc q 103) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredfive (q : ℂ) :
    Ch11.R_trunc q 105 = 1 / (1 + q ^ 105 * Ch11.R_trunc q 104) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredsix (q : ℂ) :
    Ch11.R_trunc q 106 = 1 / (1 + q ^ 106 * Ch11.R_trunc q 105) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredseven (q : ℂ) :
    Ch11.R_trunc q 107 = 1 / (1 + q ^ 107 * Ch11.R_trunc q 106) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredeight (q : ℂ) :
    Ch11.R_trunc q 108 = 1 / (1 + q ^ 108 * Ch11.R_trunc q 107) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundrednine (q : ℂ) :
    Ch11.R_trunc q 109 = 1 / (1 + q ^ 109 * Ch11.R_trunc q 108) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredten (q : ℂ) :
    Ch11.R_trunc q 110 = 1 / (1 + q ^ 110 * Ch11.R_trunc q 109) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredeleven (q : ℂ) :
    Ch11.R_trunc q 111 = 1 / (1 + q ^ 111 * Ch11.R_trunc q 110) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredtwelve (q : ℂ) :
    Ch11.R_trunc q 112 = 1 / (1 + q ^ 112 * Ch11.R_trunc q 111) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredthirteen (q : ℂ) :
    Ch11.R_trunc q 113 = 1 / (1 + q ^ 113 * Ch11.R_trunc q 112) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredfourteen (q : ℂ) :
    Ch11.R_trunc q 114 = 1 / (1 + q ^ 114 * Ch11.R_trunc q 113) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredfifteen (q : ℂ) :
    Ch11.R_trunc q 115 = 1 / (1 + q ^ 115 * Ch11.R_trunc q 114) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredsixteen (q : ℂ) :
    Ch11.R_trunc q 116 = 1 / (1 + q ^ 116 * Ch11.R_trunc q 115) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredseventeen (q : ℂ) :
    Ch11.R_trunc q 117 = 1 / (1 + q ^ 117 * Ch11.R_trunc q 116) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredeighteen (q : ℂ) :
    Ch11.R_trunc q 118 = 1 / (1 + q ^ 118 * Ch11.R_trunc q 117) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundrednineteen (q : ℂ) :
    Ch11.R_trunc q 119 = 1 / (1 + q ^ 119 * Ch11.R_trunc q 118) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredtwenty (q : ℂ) :
    Ch11.R_trunc q 120 = 1 / (1 + q ^ 120 * Ch11.R_trunc q 119) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredtwentyone (q : ℂ) :
    Ch11.R_trunc q 121 = 1 / (1 + q ^ 121 * Ch11.R_trunc q 120) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredtwentytwo (q : ℂ) :
    Ch11.R_trunc q 122 = 1 / (1 + q ^ 122 * Ch11.R_trunc q 121) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredtwentythree (q : ℂ) :
    Ch11.R_trunc q 123 = 1 / (1 + q ^ 123 * Ch11.R_trunc q 122) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredtwentyfour (q : ℂ) :
    Ch11.R_trunc q 124 = 1 / (1 + q ^ 124 * Ch11.R_trunc q 123) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredtwentyfive (q : ℂ) :
    Ch11.R_trunc q 125 = 1 / (1 + q ^ 125 * Ch11.R_trunc q 124) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredtwentysix (q : ℂ) :
    Ch11.R_trunc q 126 = 1 / (1 + q ^ 126 * Ch11.R_trunc q 125) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredtwentyseven (q : ℂ) :
    Ch11.R_trunc q 127 = 1 / (1 + q ^ 127 * Ch11.R_trunc q 126) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredtwentyeight (q : ℂ) :
    Ch11.R_trunc q 128 = 1 / (1 + q ^ 128 * Ch11.R_trunc q 127) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredtwentynine (q : ℂ) :
    Ch11.R_trunc q 129 = 1 / (1 + q ^ 129 * Ch11.R_trunc q 128) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredthirty (q : ℂ) :
    Ch11.R_trunc q 130 = 1 / (1 + q ^ 130 * Ch11.R_trunc q 129) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredthirtyone (q : ℂ) :
    Ch11.R_trunc q 131 = 1 / (1 + q ^ 131 * Ch11.R_trunc q 130) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredthirtytwo (q : ℂ) :
    Ch11.R_trunc q 132 = 1 / (1 + q ^ 132 * Ch11.R_trunc q 131) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredthirtythree (q : ℂ) :
    Ch11.R_trunc q 133 = 1 / (1 + q ^ 133 * Ch11.R_trunc q 132) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredthirtyfour (q : ℂ) :
    Ch11.R_trunc q 134 = 1 / (1 + q ^ 134 * Ch11.R_trunc q 133) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredthirtyfive (q : ℂ) :
    Ch11.R_trunc q 135 = 1 / (1 + q ^ 135 * Ch11.R_trunc q 134) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredthirtysix (q : ℂ) :
    Ch11.R_trunc q 136 = 1 / (1 + q ^ 136 * Ch11.R_trunc q 135) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredthirtyseven (q : ℂ) :
    Ch11.R_trunc q 137 = 1 / (1 + q ^ 137 * Ch11.R_trunc q 136) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredthirtyeight (q : ℂ) :
    Ch11.R_trunc q 138 = 1 / (1 + q ^ 138 * Ch11.R_trunc q 137) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredthirtynine (q : ℂ) :
    Ch11.R_trunc q 139 = 1 / (1 + q ^ 139 * Ch11.R_trunc q 138) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredforty (q : ℂ) :
    Ch11.R_trunc q 140 = 1 / (1 + q ^ 140 * Ch11.R_trunc q 139) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredfortyone (q : ℂ) :
    Ch11.R_trunc q 141 = 1 / (1 + q ^ 141 * Ch11.R_trunc q 140) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredfortytwo (q : ℂ) :
    Ch11.R_trunc q 142 = 1 / (1 + q ^ 142 * Ch11.R_trunc q 141) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredfortythree (q : ℂ) :
    Ch11.R_trunc q 143 = 1 / (1 + q ^ 143 * Ch11.R_trunc q 142) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredfortyfour (q : ℂ) :
    Ch11.R_trunc q 144 = 1 / (1 + q ^ 144 * Ch11.R_trunc q 143) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredfortyfive (q : ℂ) :
    Ch11.R_trunc q 145 = 1 / (1 + q ^ 145 * Ch11.R_trunc q 144) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredfortysix (q : ℂ) :
    Ch11.R_trunc q 146 = 1 / (1 + q ^ 146 * Ch11.R_trunc q 145) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredfortyseven (q : ℂ) :
    Ch11.R_trunc q 147 = 1 / (1 + q ^ 147 * Ch11.R_trunc q 146) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredfortyeight (q : ℂ) :
    Ch11.R_trunc q 148 = 1 / (1 + q ^ 148 * Ch11.R_trunc q 147) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredfortynine (q : ℂ) :
    Ch11.R_trunc q 149 = 1 / (1 + q ^ 149 * Ch11.R_trunc q 148) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredfifty (q : ℂ) :
    Ch11.R_trunc q 150 = 1 / (1 + q ^ 150 * Ch11.R_trunc q 149) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredfiftyone (q : ℂ) :
    Ch11.R_trunc q 151 = 1 / (1 + q ^ 151 * Ch11.R_trunc q 150) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredfiftytwo (q : ℂ) :
    Ch11.R_trunc q 152 = 1 / (1 + q ^ 152 * Ch11.R_trunc q 151) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredfiftythree (q : ℂ) :
    Ch11.R_trunc q 153 = 1 / (1 + q ^ 153 * Ch11.R_trunc q 152) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredfiftyfour (q : ℂ) :
    Ch11.R_trunc q 154 = 1 / (1 + q ^ 154 * Ch11.R_trunc q 153) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredfiftyfive (q : ℂ) :
    Ch11.R_trunc q 155 = 1 / (1 + q ^ 155 * Ch11.R_trunc q 154) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredfiftysix (q : ℂ) :
    Ch11.R_trunc q 156 = 1 / (1 + q ^ 156 * Ch11.R_trunc q 155) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredfiftyseven (q : ℂ) :
    Ch11.R_trunc q 157 = 1 / (1 + q ^ 157 * Ch11.R_trunc q 156) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredfiftyeight (q : ℂ) :
    Ch11.R_trunc q 158 = 1 / (1 + q ^ 158 * Ch11.R_trunc q 157) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredfiftynine (q : ℂ) :
    Ch11.R_trunc q 159 = 1 / (1 + q ^ 159 * Ch11.R_trunc q 158) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredsixty (q : ℂ) :
    Ch11.R_trunc q 160 = 1 / (1 + q ^ 160 * Ch11.R_trunc q 159) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredsixtyone (q : ℂ) :
    Ch11.R_trunc q 161 = 1 / (1 + q ^ 161 * Ch11.R_trunc q 160) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredsixtytwo (q : ℂ) :
    Ch11.R_trunc q 162 = 1 / (1 + q ^ 162 * Ch11.R_trunc q 161) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredsixtythree (q : ℂ) :
    Ch11.R_trunc q 163 = 1 / (1 + q ^ 163 * Ch11.R_trunc q 162) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredsixtyfour (q : ℂ) :
    Ch11.R_trunc q 164 = 1 / (1 + q ^ 164 * Ch11.R_trunc q 163) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredsixtyfive (q : ℂ) :
    Ch11.R_trunc q 165 = 1 / (1 + q ^ 165 * Ch11.R_trunc q 164) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredsixtysix (q : ℂ) :
    Ch11.R_trunc q 166 = 1 / (1 + q ^ 166 * Ch11.R_trunc q 165) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredsixtyseven (q : ℂ) :
    Ch11.R_trunc q 167 = 1 / (1 + q ^ 167 * Ch11.R_trunc q 166) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredsixtyeight (q : ℂ) :
    Ch11.R_trunc q 168 = 1 / (1 + q ^ 168 * Ch11.R_trunc q 167) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredsixtynine (q : ℂ) :
    Ch11.R_trunc q 169 = 1 / (1 + q ^ 169 * Ch11.R_trunc q 168) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredseventy (q : ℂ) :
    Ch11.R_trunc q 170 = 1 / (1 + q ^ 170 * Ch11.R_trunc q 169) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredseventyone (q : ℂ) :
    Ch11.R_trunc q 171 = 1 / (1 + q ^ 171 * Ch11.R_trunc q 170) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredseventytwo (q : ℂ) :
    Ch11.R_trunc q 172 = 1 / (1 + q ^ 172 * Ch11.R_trunc q 171) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredseventythree (q : ℂ) :
    Ch11.R_trunc q 173 = 1 / (1 + q ^ 173 * Ch11.R_trunc q 172) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredseventyfour (q : ℂ) :
    Ch11.R_trunc q 174 = 1 / (1 + q ^ 174 * Ch11.R_trunc q 173) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredseventyfive (q : ℂ) :
    Ch11.R_trunc q 175 = 1 / (1 + q ^ 175 * Ch11.R_trunc q 174) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredseventysix (q : ℂ) :
    Ch11.R_trunc q 176 = 1 / (1 + q ^ 176 * Ch11.R_trunc q 175) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredseventyseven (q : ℂ) :
    Ch11.R_trunc q 177 = 1 / (1 + q ^ 177 * Ch11.R_trunc q 176) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredseventyeight (q : ℂ) :
    Ch11.R_trunc q 178 = 1 / (1 + q ^ 178 * Ch11.R_trunc q 177) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredseventynine (q : ℂ) :
    Ch11.R_trunc q 179 = 1 / (1 + q ^ 179 * Ch11.R_trunc q 178) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredeighty (q : ℂ) :
    Ch11.R_trunc q 180 = 1 / (1 + q ^ 180 * Ch11.R_trunc q 179) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredeightyone (q : ℂ) :
    Ch11.R_trunc q 181 = 1 / (1 + q ^ 181 * Ch11.R_trunc q 180) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredeightytwo (q : ℂ) :
    Ch11.R_trunc q 182 = 1 / (1 + q ^ 182 * Ch11.R_trunc q 181) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredeightythree (q : ℂ) :
    Ch11.R_trunc q 183 = 1 / (1 + q ^ 183 * Ch11.R_trunc q 182) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredeightyfour (q : ℂ) :
    Ch11.R_trunc q 184 = 1 / (1 + q ^ 184 * Ch11.R_trunc q 183) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredeightyfive (q : ℂ) :
    Ch11.R_trunc q 185 = 1 / (1 + q ^ 185 * Ch11.R_trunc q 184) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredeightysix (q : ℂ) :
    Ch11.R_trunc q 186 = 1 / (1 + q ^ 186 * Ch11.R_trunc q 185) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredeightyseven (q : ℂ) :
    Ch11.R_trunc q 187 = 1 / (1 + q ^ 187 * Ch11.R_trunc q 186) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredeightyeight (q : ℂ) :
    Ch11.R_trunc q 188 = 1 / (1 + q ^ 188 * Ch11.R_trunc q 187) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredeightynine (q : ℂ) :
    Ch11.R_trunc q 189 = 1 / (1 + q ^ 189 * Ch11.R_trunc q 188) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredninety (q : ℂ) :
    Ch11.R_trunc q 190 = 1 / (1 + q ^ 190 * Ch11.R_trunc q 189) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredninetyone (q : ℂ) :
    Ch11.R_trunc q 191 = 1 / (1 + q ^ 191 * Ch11.R_trunc q 190) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredninetytwo (q : ℂ) :
    Ch11.R_trunc q 192 = 1 / (1 + q ^ 192 * Ch11.R_trunc q 191) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredninetythree (q : ℂ) :
    Ch11.R_trunc q 193 = 1 / (1 + q ^ 193 * Ch11.R_trunc q 192) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredninetyfour (q : ℂ) :
    Ch11.R_trunc q 194 = 1 / (1 + q ^ 194 * Ch11.R_trunc q 193) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredninetyfive (q : ℂ) :
    Ch11.R_trunc q 195 = 1 / (1 + q ^ 195 * Ch11.R_trunc q 194) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredninetysix (q : ℂ) :
    Ch11.R_trunc q 196 = 1 / (1 + q ^ 196 * Ch11.R_trunc q 195) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredninetyseven (q : ℂ) :
    Ch11.R_trunc q 197 = 1 / (1 + q ^ 197 * Ch11.R_trunc q 196) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredninetyeight (q : ℂ) :
    Ch11.R_trunc q 198 = 1 / (1 + q ^ 198 * Ch11.R_trunc q 197) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_onehundredninetynine (q : ℂ) :
    Ch11.R_trunc q 199 = 1 / (1 + q ^ 199 * Ch11.R_trunc q 198) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundred (q : ℂ) :
    Ch11.R_trunc q 200 = 1 / (1 + q ^ 200 * Ch11.R_trunc q 199) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredone (q : ℂ) :
    Ch11.R_trunc q 201 = 1 / (1 + q ^ 201 * Ch11.R_trunc q 200) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredtwo (q : ℂ) :
    Ch11.R_trunc q 202 = 1 / (1 + q ^ 202 * Ch11.R_trunc q 201) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredthree (q : ℂ) :
    Ch11.R_trunc q 203 = 1 / (1 + q ^ 203 * Ch11.R_trunc q 202) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredfour (q : ℂ) :
    Ch11.R_trunc q 204 = 1 / (1 + q ^ 204 * Ch11.R_trunc q 203) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredfive (q : ℂ) :
    Ch11.R_trunc q 205 = 1 / (1 + q ^ 205 * Ch11.R_trunc q 204) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredsix (q : ℂ) :
    Ch11.R_trunc q 206 = 1 / (1 + q ^ 206 * Ch11.R_trunc q 205) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredseven (q : ℂ) :
    Ch11.R_trunc q 207 = 1 / (1 + q ^ 207 * Ch11.R_trunc q 206) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredeight (q : ℂ) :
    Ch11.R_trunc q 208 = 1 / (1 + q ^ 208 * Ch11.R_trunc q 207) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundrednine (q : ℂ) :
    Ch11.R_trunc q 209 = 1 / (1 + q ^ 209 * Ch11.R_trunc q 208) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredten (q : ℂ) :
    Ch11.R_trunc q 210 = 1 / (1 + q ^ 210 * Ch11.R_trunc q 209) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredeleven (q : ℂ) :
    Ch11.R_trunc q 211 = 1 / (1 + q ^ 211 * Ch11.R_trunc q 210) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredtwelve (q : ℂ) :
    Ch11.R_trunc q 212 = 1 / (1 + q ^ 212 * Ch11.R_trunc q 211) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredthirteen (q : ℂ) :
    Ch11.R_trunc q 213 = 1 / (1 + q ^ 213 * Ch11.R_trunc q 212) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredfourteen (q : ℂ) :
    Ch11.R_trunc q 214 = 1 / (1 + q ^ 214 * Ch11.R_trunc q 213) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredfifteen (q : ℂ) :
    Ch11.R_trunc q 215 = 1 / (1 + q ^ 215 * Ch11.R_trunc q 214) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredsixteen (q : ℂ) :
    Ch11.R_trunc q 216 = 1 / (1 + q ^ 216 * Ch11.R_trunc q 215) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredseventeen (q : ℂ) :
    Ch11.R_trunc q 217 = 1 / (1 + q ^ 217 * Ch11.R_trunc q 216) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredeighteen (q : ℂ) :
    Ch11.R_trunc q 218 = 1 / (1 + q ^ 218 * Ch11.R_trunc q 217) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundrednineteen (q : ℂ) :
    Ch11.R_trunc q 219 = 1 / (1 + q ^ 219 * Ch11.R_trunc q 218) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredtwenty (q : ℂ) :
    Ch11.R_trunc q 220 = 1 / (1 + q ^ 220 * Ch11.R_trunc q 219) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredtwentyone (q : ℂ) :
    Ch11.R_trunc q 221 = 1 / (1 + q ^ 221 * Ch11.R_trunc q 220) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredtwentytwo (q : ℂ) :
    Ch11.R_trunc q 222 = 1 / (1 + q ^ 222 * Ch11.R_trunc q 221) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredtwentythree (q : ℂ) :
    Ch11.R_trunc q 223 = 1 / (1 + q ^ 223 * Ch11.R_trunc q 222) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredtwentyfour (q : ℂ) :
    Ch11.R_trunc q 224 = 1 / (1 + q ^ 224 * Ch11.R_trunc q 223) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredtwentyfive (q : ℂ) :
    Ch11.R_trunc q 225 = 1 / (1 + q ^ 225 * Ch11.R_trunc q 224) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredtwentysix (q : ℂ) :
    Ch11.R_trunc q 226 = 1 / (1 + q ^ 226 * Ch11.R_trunc q 225) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredtwentyseven (q : ℂ) :
    Ch11.R_trunc q 227 = 1 / (1 + q ^ 227 * Ch11.R_trunc q 226) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredtwentyeight (q : ℂ) :
    Ch11.R_trunc q 228 = 1 / (1 + q ^ 228 * Ch11.R_trunc q 227) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredtwentynine (q : ℂ) :
    Ch11.R_trunc q 229 = 1 / (1 + q ^ 229 * Ch11.R_trunc q 228) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredthirty (q : ℂ) :
    Ch11.R_trunc q 230 = 1 / (1 + q ^ 230 * Ch11.R_trunc q 229) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredthirtyone (q : ℂ) :
    Ch11.R_trunc q 231 = 1 / (1 + q ^ 231 * Ch11.R_trunc q 230) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredthirtytwo (q : ℂ) :
    Ch11.R_trunc q 232 = 1 / (1 + q ^ 232 * Ch11.R_trunc q 231) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredthirtythree (q : ℂ) :
    Ch11.R_trunc q 233 = 1 / (1 + q ^ 233 * Ch11.R_trunc q 232) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredthirtyfour (q : ℂ) :
    Ch11.R_trunc q 234 = 1 / (1 + q ^ 234 * Ch11.R_trunc q 233) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredthirtyfive (q : ℂ) :
    Ch11.R_trunc q 235 = 1 / (1 + q ^ 235 * Ch11.R_trunc q 234) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredthirtysix (q : ℂ) :
    Ch11.R_trunc q 236 = 1 / (1 + q ^ 236 * Ch11.R_trunc q 235) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredthirtyseven (q : ℂ) :
    Ch11.R_trunc q 237 = 1 / (1 + q ^ 237 * Ch11.R_trunc q 236) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredthirtyeight (q : ℂ) :
    Ch11.R_trunc q 238 = 1 / (1 + q ^ 238 * Ch11.R_trunc q 237) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredthirtynine (q : ℂ) :
    Ch11.R_trunc q 239 = 1 / (1 + q ^ 239 * Ch11.R_trunc q 238) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredforty (q : ℂ) :
    Ch11.R_trunc q 240 = 1 / (1 + q ^ 240 * Ch11.R_trunc q 239) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredfortyone (q : ℂ) :
    Ch11.R_trunc q 241 = 1 / (1 + q ^ 241 * Ch11.R_trunc q 240) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredfortytwo (q : ℂ) :
    Ch11.R_trunc q 242 = 1 / (1 + q ^ 242 * Ch11.R_trunc q 241) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredfortythree (q : ℂ) :
    Ch11.R_trunc q 243 = 1 / (1 + q ^ 243 * Ch11.R_trunc q 242) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredfortyfour (q : ℂ) :
    Ch11.R_trunc q 244 = 1 / (1 + q ^ 244 * Ch11.R_trunc q 243) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredfortyfive (q : ℂ) :
    Ch11.R_trunc q 245 = 1 / (1 + q ^ 245 * Ch11.R_trunc q 244) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredfortysix (q : ℂ) :
    Ch11.R_trunc q 246 = 1 / (1 + q ^ 246 * Ch11.R_trunc q 245) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredfortyseven (q : ℂ) :
    Ch11.R_trunc q 247 = 1 / (1 + q ^ 247 * Ch11.R_trunc q 246) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredfortyeight (q : ℂ) :
    Ch11.R_trunc q 248 = 1 / (1 + q ^ 248 * Ch11.R_trunc q 247) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredfortynine (q : ℂ) :
    Ch11.R_trunc q 249 = 1 / (1 + q ^ 249 * Ch11.R_trunc q 248) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredfifty (q : ℂ) :
    Ch11.R_trunc q 250 = 1 / (1 + q ^ 250 * Ch11.R_trunc q 249) := by
  simp [Ch11.R_trunc]


set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredfiftyone (q : ℂ) :
    Ch11.R_trunc q 251 = 1 / (1 + q ^ 251 * Ch11.R_trunc q 250) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredfiftytwo (q : ℂ) :
    Ch11.R_trunc q 252 = 1 / (1 + q ^ 252 * Ch11.R_trunc q 251) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredfiftythree (q : ℂ) :
    Ch11.R_trunc q 253 = 1 / (1 + q ^ 253 * Ch11.R_trunc q 252) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredfiftyfour (q : ℂ) :
    Ch11.R_trunc q 254 = 1 / (1 + q ^ 254 * Ch11.R_trunc q 253) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredfiftyfive (q : ℂ) :
    Ch11.R_trunc q 255 = 1 / (1 + q ^ 255 * Ch11.R_trunc q 254) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredfiftysix (q : ℂ) :
    Ch11.R_trunc q 256 = 1 / (1 + q ^ 256 * Ch11.R_trunc q 255) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredfiftyseven (q : ℂ) :
    Ch11.R_trunc q 257 = 1 / (1 + q ^ 257 * Ch11.R_trunc q 256) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredfiftyeight (q : ℂ) :
    Ch11.R_trunc q 258 = 1 / (1 + q ^ 258 * Ch11.R_trunc q 257) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredfiftynine (q : ℂ) :
    Ch11.R_trunc q 259 = 1 / (1 + q ^ 259 * Ch11.R_trunc q 258) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredsixty (q : ℂ) :
    Ch11.R_trunc q 260 = 1 / (1 + q ^ 260 * Ch11.R_trunc q 259) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredsixtyone (q : ℂ) :
    Ch11.R_trunc q 261 = 1 / (1 + q ^ 261 * Ch11.R_trunc q 260) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredsixtytwo (q : ℂ) :
    Ch11.R_trunc q 262 = 1 / (1 + q ^ 262 * Ch11.R_trunc q 261) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredsixtythree (q : ℂ) :
    Ch11.R_trunc q 263 = 1 / (1 + q ^ 263 * Ch11.R_trunc q 262) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredsixtyfour (q : ℂ) :
    Ch11.R_trunc q 264 = 1 / (1 + q ^ 264 * Ch11.R_trunc q 263) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredsixtyfive (q : ℂ) :
    Ch11.R_trunc q 265 = 1 / (1 + q ^ 265 * Ch11.R_trunc q 264) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredsixtysix (q : ℂ) :
    Ch11.R_trunc q 266 = 1 / (1 + q ^ 266 * Ch11.R_trunc q 265) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredsixtyseven (q : ℂ) :
    Ch11.R_trunc q 267 = 1 / (1 + q ^ 267 * Ch11.R_trunc q 266) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredsixtyeight (q : ℂ) :
    Ch11.R_trunc q 268 = 1 / (1 + q ^ 268 * Ch11.R_trunc q 267) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredsixtynine (q : ℂ) :
    Ch11.R_trunc q 269 = 1 / (1 + q ^ 269 * Ch11.R_trunc q 268) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredseventy (q : ℂ) :
    Ch11.R_trunc q 270 = 1 / (1 + q ^ 270 * Ch11.R_trunc q 269) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredseventyone (q : ℂ) :
    Ch11.R_trunc q 271 = 1 / (1 + q ^ 271 * Ch11.R_trunc q 270) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredseventytwo (q : ℂ) :
    Ch11.R_trunc q 272 = 1 / (1 + q ^ 272 * Ch11.R_trunc q 271) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredseventythree (q : ℂ) :
    Ch11.R_trunc q 273 = 1 / (1 + q ^ 273 * Ch11.R_trunc q 272) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredseventyfour (q : ℂ) :
    Ch11.R_trunc q 274 = 1 / (1 + q ^ 274 * Ch11.R_trunc q 273) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredseventyfive (q : ℂ) :
    Ch11.R_trunc q 275 = 1 / (1 + q ^ 275 * Ch11.R_trunc q 274) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredseventysix (q : ℂ) :
    Ch11.R_trunc q 276 = 1 / (1 + q ^ 276 * Ch11.R_trunc q 275) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredseventyseven (q : ℂ) :
    Ch11.R_trunc q 277 = 1 / (1 + q ^ 277 * Ch11.R_trunc q 276) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredseventyeight (q : ℂ) :
    Ch11.R_trunc q 278 = 1 / (1 + q ^ 278 * Ch11.R_trunc q 277) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredseventynine (q : ℂ) :
    Ch11.R_trunc q 279 = 1 / (1 + q ^ 279 * Ch11.R_trunc q 278) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_nesting_twohundredeighty (q : ℂ) :
    Ch11.R_trunc q 280 = 1 / (1 + q ^ 280 * Ch11.R_trunc q 279) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_twohundredeightyone (q : ℂ) :
    Ch11.R_trunc q 281 = 1 / (1 + q ^ 281 * Ch11.R_trunc q 280) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_twohundredeightytwo (q : ℂ) :
    Ch11.R_trunc q 282 = 1 / (1 + q ^ 282 * Ch11.R_trunc q 281) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_twohundredeightythree (q : ℂ) :
    Ch11.R_trunc q 283 = 1 / (1 + q ^ 283 * Ch11.R_trunc q 282) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_twohundredeightyfour (q : ℂ) :
    Ch11.R_trunc q 284 = 1 / (1 + q ^ 284 * Ch11.R_trunc q 283) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_twohundredeightyfive (q : ℂ) :
    Ch11.R_trunc q 285 = 1 / (1 + q ^ 285 * Ch11.R_trunc q 284) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_twohundredeightysix (q : ℂ) :
    Ch11.R_trunc q 286 = 1 / (1 + q ^ 286 * Ch11.R_trunc q 285) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_twohundredeightyseven (q : ℂ) :
    Ch11.R_trunc q 287 = 1 / (1 + q ^ 287 * Ch11.R_trunc q 286) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_twohundredeightyeight (q : ℂ) :
    Ch11.R_trunc q 288 = 1 / (1 + q ^ 288 * Ch11.R_trunc q 287) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_twohundredeightynine (q : ℂ) :
    Ch11.R_trunc q 289 = 1 / (1 + q ^ 289 * Ch11.R_trunc q 288) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_twohundredninety (q : ℂ) :
    Ch11.R_trunc q 290 = 1 / (1 + q ^ 290 * Ch11.R_trunc q 289) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_twohundredninetyone (q : ℂ) :
    Ch11.R_trunc q 291 = 1 / (1 + q ^ 291 * Ch11.R_trunc q 290) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_twohundredninetytwo (q : ℂ) :
    Ch11.R_trunc q 292 = 1 / (1 + q ^ 292 * Ch11.R_trunc q 291) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_twohundredninetythree (q : ℂ) :
    Ch11.R_trunc q 293 = 1 / (1 + q ^ 293 * Ch11.R_trunc q 292) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_twohundredninetyfour (q : ℂ) :
    Ch11.R_trunc q 294 = 1 / (1 + q ^ 294 * Ch11.R_trunc q 293) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_twohundredninetyfive (q : ℂ) :
    Ch11.R_trunc q 295 = 1 / (1 + q ^ 295 * Ch11.R_trunc q 294) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_twohundredninetysix (q : ℂ) :
    Ch11.R_trunc q 296 = 1 / (1 + q ^ 296 * Ch11.R_trunc q 295) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_twohundredninetyseven (q : ℂ) :
    Ch11.R_trunc q 297 = 1 / (1 + q ^ 297 * Ch11.R_trunc q 296) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_twohundredninetyeight (q : ℂ) :
    Ch11.R_trunc q 298 = 1 / (1 + q ^ 298 * Ch11.R_trunc q 297) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_twohundredninetynine (q : ℂ) :
    Ch11.R_trunc q 299 = 1 / (1 + q ^ 299 * Ch11.R_trunc q 298) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundred (q : ℂ) :
    Ch11.R_trunc q 300 = 1 / (1 + q ^ 300 * Ch11.R_trunc q 299) := by
  simp [Ch11.R_trunc]


set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredone (q : ℂ) :
    Ch11.R_trunc q 301 = 1 / (1 + q ^ 301 * Ch11.R_trunc q 300) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredtwo (q : ℂ) :
    Ch11.R_trunc q 302 = 1 / (1 + q ^ 302 * Ch11.R_trunc q 301) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredthree (q : ℂ) :
    Ch11.R_trunc q 303 = 1 / (1 + q ^ 303 * Ch11.R_trunc q 302) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredfour (q : ℂ) :
    Ch11.R_trunc q 304 = 1 / (1 + q ^ 304 * Ch11.R_trunc q 303) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredfive (q : ℂ) :
    Ch11.R_trunc q 305 = 1 / (1 + q ^ 305 * Ch11.R_trunc q 304) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredsix (q : ℂ) :
    Ch11.R_trunc q 306 = 1 / (1 + q ^ 306 * Ch11.R_trunc q 305) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredseven (q : ℂ) :
    Ch11.R_trunc q 307 = 1 / (1 + q ^ 307 * Ch11.R_trunc q 306) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredeight (q : ℂ) :
    Ch11.R_trunc q 308 = 1 / (1 + q ^ 308 * Ch11.R_trunc q 307) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundrednine (q : ℂ) :
    Ch11.R_trunc q 309 = 1 / (1 + q ^ 309 * Ch11.R_trunc q 308) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredten (q : ℂ) :
    Ch11.R_trunc q 310 = 1 / (1 + q ^ 310 * Ch11.R_trunc q 309) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredeleven (q : ℂ) :
    Ch11.R_trunc q 311 = 1 / (1 + q ^ 311 * Ch11.R_trunc q 310) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredtwelve (q : ℂ) :
    Ch11.R_trunc q 312 = 1 / (1 + q ^ 312 * Ch11.R_trunc q 311) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredthirteen (q : ℂ) :
    Ch11.R_trunc q 313 = 1 / (1 + q ^ 313 * Ch11.R_trunc q 312) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredfourteen (q : ℂ) :
    Ch11.R_trunc q 314 = 1 / (1 + q ^ 314 * Ch11.R_trunc q 313) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredfifteen (q : ℂ) :
    Ch11.R_trunc q 315 = 1 / (1 + q ^ 315 * Ch11.R_trunc q 314) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredsixteen (q : ℂ) :
    Ch11.R_trunc q 316 = 1 / (1 + q ^ 316 * Ch11.R_trunc q 315) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredseventeen (q : ℂ) :
    Ch11.R_trunc q 317 = 1 / (1 + q ^ 317 * Ch11.R_trunc q 316) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredeighteen (q : ℂ) :
    Ch11.R_trunc q 318 = 1 / (1 + q ^ 318 * Ch11.R_trunc q 317) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundrednineteen (q : ℂ) :
    Ch11.R_trunc q 319 = 1 / (1 + q ^ 319 * Ch11.R_trunc q 318) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredtwenty (q : ℂ) :
    Ch11.R_trunc q 320 = 1 / (1 + q ^ 320 * Ch11.R_trunc q 319) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredtwentyone (q : ℂ) :
    Ch11.R_trunc q 321 = 1 / (1 + q ^ 321 * Ch11.R_trunc q 320) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredtwentytwo (q : ℂ) :
    Ch11.R_trunc q 322 = 1 / (1 + q ^ 322 * Ch11.R_trunc q 321) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredtwentythree (q : ℂ) :
    Ch11.R_trunc q 323 = 1 / (1 + q ^ 323 * Ch11.R_trunc q 322) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredtwentyfour (q : ℂ) :
    Ch11.R_trunc q 324 = 1 / (1 + q ^ 324 * Ch11.R_trunc q 323) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredtwentyfive (q : ℂ) :
    Ch11.R_trunc q 325 = 1 / (1 + q ^ 325 * Ch11.R_trunc q 324) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredtwentysix (q : ℂ) :
    Ch11.R_trunc q 326 = 1 / (1 + q ^ 326 * Ch11.R_trunc q 325) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredtwentyseven (q : ℂ) :
    Ch11.R_trunc q 327 = 1 / (1 + q ^ 327 * Ch11.R_trunc q 326) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredtwentyeight (q : ℂ) :
    Ch11.R_trunc q 328 = 1 / (1 + q ^ 328 * Ch11.R_trunc q 327) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredtwentynine (q : ℂ) :
    Ch11.R_trunc q 329 = 1 / (1 + q ^ 329 * Ch11.R_trunc q 328) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredthirty (q : ℂ) :
    Ch11.R_trunc q 330 = 1 / (1 + q ^ 330 * Ch11.R_trunc q 329) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredthirtyone (q : ℂ) :
    Ch11.R_trunc q 331 = 1 / (1 + q ^ 331 * Ch11.R_trunc q 330) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredthirtytwo (q : ℂ) :
    Ch11.R_trunc q 332 = 1 / (1 + q ^ 332 * Ch11.R_trunc q 331) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredthirtythree (q : ℂ) :
    Ch11.R_trunc q 333 = 1 / (1 + q ^ 333 * Ch11.R_trunc q 332) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredthirtyfour (q : ℂ) :
    Ch11.R_trunc q 334 = 1 / (1 + q ^ 334 * Ch11.R_trunc q 333) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredthirtyfive (q : ℂ) :
    Ch11.R_trunc q 335 = 1 / (1 + q ^ 335 * Ch11.R_trunc q 334) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredthirtysix (q : ℂ) :
    Ch11.R_trunc q 336 = 1 / (1 + q ^ 336 * Ch11.R_trunc q 335) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredthirtyseven (q : ℂ) :
    Ch11.R_trunc q 337 = 1 / (1 + q ^ 337 * Ch11.R_trunc q 336) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredthirtyeight (q : ℂ) :
    Ch11.R_trunc q 338 = 1 / (1 + q ^ 338 * Ch11.R_trunc q 337) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredthirtynine (q : ℂ) :
    Ch11.R_trunc q 339 = 1 / (1 + q ^ 339 * Ch11.R_trunc q 338) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredforty (q : ℂ) :
    Ch11.R_trunc q 340 = 1 / (1 + q ^ 340 * Ch11.R_trunc q 339) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredfortyone (q : ℂ) :
    Ch11.R_trunc q 341 = 1 / (1 + q ^ 341 * Ch11.R_trunc q 340) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredfortytwo (q : ℂ) :
    Ch11.R_trunc q 342 = 1 / (1 + q ^ 342 * Ch11.R_trunc q 341) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredfortythree (q : ℂ) :
    Ch11.R_trunc q 343 = 1 / (1 + q ^ 343 * Ch11.R_trunc q 342) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredfortyfour (q : ℂ) :
    Ch11.R_trunc q 344 = 1 / (1 + q ^ 344 * Ch11.R_trunc q 343) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredfortyfive (q : ℂ) :
    Ch11.R_trunc q 345 = 1 / (1 + q ^ 345 * Ch11.R_trunc q 344) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredfortysix (q : ℂ) :
    Ch11.R_trunc q 346 = 1 / (1 + q ^ 346 * Ch11.R_trunc q 345) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredfortyseven (q : ℂ) :
    Ch11.R_trunc q 347 = 1 / (1 + q ^ 347 * Ch11.R_trunc q 346) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredfortyeight (q : ℂ) :
    Ch11.R_trunc q 348 = 1 / (1 + q ^ 348 * Ch11.R_trunc q 347) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredfortynine (q : ℂ) :
    Ch11.R_trunc q 349 = 1 / (1 + q ^ 349 * Ch11.R_trunc q 348) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredfifty (q : ℂ) :
    Ch11.R_trunc q 350 = 1 / (1 + q ^ 350 * Ch11.R_trunc q 349) := by
  simp [Ch11.R_trunc]


set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredfiftyone (q : ℂ) :
    Ch11.R_trunc q 351 = 1 / (1 + q ^ 351 * Ch11.R_trunc q 350) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredfiftytwo (q : ℂ) :
    Ch11.R_trunc q 352 = 1 / (1 + q ^ 352 * Ch11.R_trunc q 351) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredfiftythree (q : ℂ) :
    Ch11.R_trunc q 353 = 1 / (1 + q ^ 353 * Ch11.R_trunc q 352) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredfiftyfour (q : ℂ) :
    Ch11.R_trunc q 354 = 1 / (1 + q ^ 354 * Ch11.R_trunc q 353) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredfiftyfive (q : ℂ) :
    Ch11.R_trunc q 355 = 1 / (1 + q ^ 355 * Ch11.R_trunc q 354) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredfiftysix (q : ℂ) :
    Ch11.R_trunc q 356 = 1 / (1 + q ^ 356 * Ch11.R_trunc q 355) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredfiftyseven (q : ℂ) :
    Ch11.R_trunc q 357 = 1 / (1 + q ^ 357 * Ch11.R_trunc q 356) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredfiftyeight (q : ℂ) :
    Ch11.R_trunc q 358 = 1 / (1 + q ^ 358 * Ch11.R_trunc q 357) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredfiftynine (q : ℂ) :
    Ch11.R_trunc q 359 = 1 / (1 + q ^ 359 * Ch11.R_trunc q 358) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredsixty (q : ℂ) :
    Ch11.R_trunc q 360 = 1 / (1 + q ^ 360 * Ch11.R_trunc q 359) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredsixtyone (q : ℂ) :
    Ch11.R_trunc q 361 = 1 / (1 + q ^ 361 * Ch11.R_trunc q 360) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredsixtytwo (q : ℂ) :
    Ch11.R_trunc q 362 = 1 / (1 + q ^ 362 * Ch11.R_trunc q 361) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredsixtythree (q : ℂ) :
    Ch11.R_trunc q 363 = 1 / (1 + q ^ 363 * Ch11.R_trunc q 362) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredsixtyfour (q : ℂ) :
    Ch11.R_trunc q 364 = 1 / (1 + q ^ 364 * Ch11.R_trunc q 363) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredsixtyfive (q : ℂ) :
    Ch11.R_trunc q 365 = 1 / (1 + q ^ 365 * Ch11.R_trunc q 364) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredsixtysix (q : ℂ) :
    Ch11.R_trunc q 366 = 1 / (1 + q ^ 366 * Ch11.R_trunc q 365) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredsixtyseven (q : ℂ) :
    Ch11.R_trunc q 367 = 1 / (1 + q ^ 367 * Ch11.R_trunc q 366) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredsixtyeight (q : ℂ) :
    Ch11.R_trunc q 368 = 1 / (1 + q ^ 368 * Ch11.R_trunc q 367) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredsixtynine (q : ℂ) :
    Ch11.R_trunc q 369 = 1 / (1 + q ^ 369 * Ch11.R_trunc q 368) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredseventy (q : ℂ) :
    Ch11.R_trunc q 370 = 1 / (1 + q ^ 370 * Ch11.R_trunc q 369) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredseventyone (q : ℂ) :
    Ch11.R_trunc q 371 = 1 / (1 + q ^ 371 * Ch11.R_trunc q 370) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredseventytwo (q : ℂ) :
    Ch11.R_trunc q 372 = 1 / (1 + q ^ 372 * Ch11.R_trunc q 371) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredseventythree (q : ℂ) :
    Ch11.R_trunc q 373 = 1 / (1 + q ^ 373 * Ch11.R_trunc q 372) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredseventyfour (q : ℂ) :
    Ch11.R_trunc q 374 = 1 / (1 + q ^ 374 * Ch11.R_trunc q 373) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredseventyfive (q : ℂ) :
    Ch11.R_trunc q 375 = 1 / (1 + q ^ 375 * Ch11.R_trunc q 374) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredseventysix (q : ℂ) :
    Ch11.R_trunc q 376 = 1 / (1 + q ^ 376 * Ch11.R_trunc q 375) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredseventyseven (q : ℂ) :
    Ch11.R_trunc q 377 = 1 / (1 + q ^ 377 * Ch11.R_trunc q 376) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredseventyeight (q : ℂ) :
    Ch11.R_trunc q 378 = 1 / (1 + q ^ 378 * Ch11.R_trunc q 377) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredseventynine (q : ℂ) :
    Ch11.R_trunc q 379 = 1 / (1 + q ^ 379 * Ch11.R_trunc q 378) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredeighty (q : ℂ) :
    Ch11.R_trunc q 380 = 1 / (1 + q ^ 380 * Ch11.R_trunc q 379) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredeightyone (q : ℂ) :
    Ch11.R_trunc q 381 = 1 / (1 + q ^ 381 * Ch11.R_trunc q 380) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredeightytwo (q : ℂ) :
    Ch11.R_trunc q 382 = 1 / (1 + q ^ 382 * Ch11.R_trunc q 381) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredeightythree (q : ℂ) :
    Ch11.R_trunc q 383 = 1 / (1 + q ^ 383 * Ch11.R_trunc q 382) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredeightyfour (q : ℂ) :
    Ch11.R_trunc q 384 = 1 / (1 + q ^ 384 * Ch11.R_trunc q 383) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredeightyfive (q : ℂ) :
    Ch11.R_trunc q 385 = 1 / (1 + q ^ 385 * Ch11.R_trunc q 384) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredeightysix (q : ℂ) :
    Ch11.R_trunc q 386 = 1 / (1 + q ^ 386 * Ch11.R_trunc q 385) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredeightyseven (q : ℂ) :
    Ch11.R_trunc q 387 = 1 / (1 + q ^ 387 * Ch11.R_trunc q 386) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredeightyeight (q : ℂ) :
    Ch11.R_trunc q 388 = 1 / (1 + q ^ 388 * Ch11.R_trunc q 387) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredeightynine (q : ℂ) :
    Ch11.R_trunc q 389 = 1 / (1 + q ^ 389 * Ch11.R_trunc q 388) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredninety (q : ℂ) :
    Ch11.R_trunc q 390 = 1 / (1 + q ^ 390 * Ch11.R_trunc q 389) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredninetyone (q : ℂ) :
    Ch11.R_trunc q 391 = 1 / (1 + q ^ 391 * Ch11.R_trunc q 390) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredninetytwo (q : ℂ) :
    Ch11.R_trunc q 392 = 1 / (1 + q ^ 392 * Ch11.R_trunc q 391) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredninetythree (q : ℂ) :
    Ch11.R_trunc q 393 = 1 / (1 + q ^ 393 * Ch11.R_trunc q 392) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredninetyfour (q : ℂ) :
    Ch11.R_trunc q 394 = 1 / (1 + q ^ 394 * Ch11.R_trunc q 393) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredninetyfive (q : ℂ) :
    Ch11.R_trunc q 395 = 1 / (1 + q ^ 395 * Ch11.R_trunc q 394) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredninetysix (q : ℂ) :
    Ch11.R_trunc q 396 = 1 / (1 + q ^ 396 * Ch11.R_trunc q 395) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredninetyseven (q : ℂ) :
    Ch11.R_trunc q 397 = 1 / (1 + q ^ 397 * Ch11.R_trunc q 396) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredninetyeight (q : ℂ) :
    Ch11.R_trunc q 398 = 1 / (1 + q ^ 398 * Ch11.R_trunc q 397) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_threehundredninetynine (q : ℂ) :
    Ch11.R_trunc q 399 = 1 / (1 + q ^ 399 * Ch11.R_trunc q 398) := by
  simp [Ch11.R_trunc]

set_option maxRecDepth 4000 in
theorem R_trunc_nesting_fourhundred (q : ℂ) :
    Ch11.R_trunc q 400 = 1 / (1 + q ^ 400 * Ch11.R_trunc q 399) := by
  simp [Ch11.R_trunc]

end Field

end QCalc
end PartIII
end QseriesFormalization
