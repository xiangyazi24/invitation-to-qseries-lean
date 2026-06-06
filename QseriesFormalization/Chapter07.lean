import QseriesFormalization.Basic
import QseriesFormalization.Chapter04

/-!
# Chapter 7 — Part II: Rogers-Ramanujan: first proof (functional equation)

(Hei-Chi Chan, *An Invitation to q-Series*, Ch 7, pp. 47-52.)

Stub: definitions and theorem statements to be filled in as we work
through the chapter.
-/

namespace QseriesFormalization
namespace PartII
namespace Ch07

section Field

variable {R : Type*} [Field R]

/-- Truncated LHS of the Rogers-Ramanujan identity for parameter `a ∈ {0,1}`:
`∑_{n=0}^N q^{n² + a n} / (q;q)_n`. -/
noncomputable def rogersRamanujanLHSTrunc (q : R) (a N : Nat) : R :=
  natSum (fun n => q ^ (n * n + a * n) / qPochhammer q n) N

/-- Recursion: `rogersRamanujanLHSTrunc q a (N+1) =
rogersRamanujanLHSTrunc q a N + q^((N+1)² + a(N+1)) / (q;q)_(N+1)`. -/
theorem rogersRamanujanLHSTrunc_succ (q : R) (a N : Nat) :
    rogersRamanujanLHSTrunc q a (N + 1) =
      rogersRamanujanLHSTrunc q a N +
        q ^ ((N + 1) * (N + 1) + a * (N + 1)) / qPochhammer q (N + 1) := by
  simp [rogersRamanujanLHSTrunc]

/-- Truncated RHS: partial product
`∏_{n=1}^N 1 / ((1 - q^{5n-1-a}) (1 - q^{5n-4+a}))`. -/
noncomputable def rogersRamanujanRHSTrunc (q : R) (a N : Nat) : R :=
  match N with
  | 0 => 1
  | Nat.succ n =>
      rogersRamanujanRHSTrunc q a n /
        ((1 - q ^ (5 * (n + 1) - 1 - a)) *
          (1 - q ^ (5 * (n + 1) - 4 + a)))

/-- Recursion wrapper for `rogersRamanujanRHSTrunc`. -/
theorem rogersRamanujanRHSTrunc_succ (q : R) (a n : Nat) :
    rogersRamanujanRHSTrunc q a (n + 1) =
      rogersRamanujanRHSTrunc q a n /
        ((1 - q ^ (5 * (n + 1) - 1 - a)) *
          (1 - q ^ (5 * (n + 1) - 4 + a))) := rfl

theorem rogersRamanujan_a0_zero (q : R) :
    rogersRamanujanLHSTrunc q 0 0 = 1 ∧ rogersRamanujanRHSTrunc q 0 0 = 1 := by
  simp [rogersRamanujanLHSTrunc, rogersRamanujanRHSTrunc]

theorem rogersRamanujan_a1_zero (q : R) :
    rogersRamanujanLHSTrunc q 1 0 = 1 ∧ rogersRamanujanRHSTrunc q 1 0 = 1 := by
  simp [rogersRamanujanLHSTrunc, rogersRamanujanRHSTrunc]

/--
LHS truncation at `N = 1` for parameter `a`.

The second summand has exponent `1^2 + a * 1 = 1 + a`, so the finite
value is `1 + q^(1+a)/(1-q)`.
-/
theorem rogersRamanujanLHSTrunc_one (q : R) (a : Nat) :
    rogersRamanujanLHSTrunc q a 1 = 1 + q ^ (1 + a) / (1 - q) := by
  simp [rogersRamanujanLHSTrunc, natSum, qPochhammer]

/--
LHS truncation at `N = 2` for parameter `a`.

The three summands are `1`, `q^(1+a)/(1-q)`, and
`q^(4+2*a)/((1-q)*(1-q^2))`.
-/
theorem rogersRamanujanLHSTrunc_two (q : R) (a : Nat) :
    rogersRamanujanLHSTrunc q a 2 =
      1 + q ^ (1 + a) / (1 - q) +
      q ^ (4 + 2 * a) / ((1 - q) * (1 - q ^ 2)) := by
  simp [rogersRamanujanLHSTrunc, natSum, qPochhammer, Nat.mul_comm]

/--
LHS truncation at `N = 3` for parameter `a`.

The four summands are `1`, `q^(1+a)/(1-q)`,
`q^(4+2*a)/((1-q)*(1-q^2))`, and
`q^(9+3*a)/((1-q)*(1-q^2)*(1-q^3))`.
-/
theorem rogersRamanujanLHSTrunc_three (q : R) (a : Nat) :
    rogersRamanujanLHSTrunc q a 3 =
      1 + q ^ (1 + a) / (1 - q) +
      q ^ (4 + 2 * a) / ((1 - q) * (1 - q ^ 2)) +
      q ^ (9 + 3 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3)) := by
  simp [rogersRamanujanLHSTrunc, natSum, qPochhammer, Nat.mul_comm]

/-- LHS truncation at `N = 4` for parameter `a`. -/
theorem rogersRamanujanLHSTrunc_four (q : R) (a : Nat) :
    rogersRamanujanLHSTrunc q a 4 =
      1 + q ^ (1 + a) / (1 - q) +
      q ^ (4 + 2 * a) / ((1 - q) * (1 - q ^ 2)) +
      q ^ (9 + 3 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3)) +
      q ^ (16 + 4 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4)) := by
  simp [rogersRamanujanLHSTrunc, natSum, qPochhammer, Nat.mul_comm]

/-- LHS truncation at `N = 5` for parameter `a`. -/
theorem rogersRamanujanLHSTrunc_five (q : R) (a : Nat) :
    rogersRamanujanLHSTrunc q a 5 =
      1 + q ^ (1 + a) / (1 - q) +
      q ^ (4 + 2 * a) / ((1 - q) * (1 - q ^ 2)) +
      q ^ (9 + 3 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3)) +
      q ^ (16 + 4 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4)) +
      q ^ (25 + 5 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5)) := by
  simp [rogersRamanujanLHSTrunc, natSum, qPochhammer, Nat.mul_comm]

/-- LHS truncation at `N = 6` for parameter `a`. -/
theorem rogersRamanujanLHSTrunc_six (q : R) (a : Nat) :
    rogersRamanujanLHSTrunc q a 6 =
      1 + q ^ (1 + a) / (1 - q) +
      q ^ (4 + 2 * a) / ((1 - q) * (1 - q ^ 2)) +
      q ^ (9 + 3 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3)) +
      q ^ (16 + 4 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4)) +
      q ^ (25 + 5 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5)) +
      q ^ (36 + 6 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6)) := by
  simp [rogersRamanujanLHSTrunc, natSum, qPochhammer, Nat.mul_comm]

/-- LHS truncation at `N = 7` for parameter `a`. -/
theorem rogersRamanujanLHSTrunc_seven (q : R) (a : Nat) :
    rogersRamanujanLHSTrunc q a 7 =
      1 + q ^ (1 + a) / (1 - q) +
      q ^ (4 + 2 * a) / ((1 - q) * (1 - q ^ 2)) +
      q ^ (9 + 3 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3)) +
      q ^ (16 + 4 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4)) +
      q ^ (25 + 5 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5)) +
      q ^ (36 + 6 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6)) +
      q ^ (49 + 7 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7)) := by
  simp [rogersRamanujanLHSTrunc, natSum, qPochhammer, Nat.mul_comm]

theorem rogersRamanujanLHSTrunc_eight (q : R) (a : Nat) :
    rogersRamanujanLHSTrunc q a 8 =
      1 + q ^ (1 + a) / (1 - q) +
      q ^ (4 + 2 * a) / ((1 - q) * (1 - q ^ 2)) +
      q ^ (9 + 3 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3)) +
      q ^ (16 + 4 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4)) +
      q ^ (25 + 5 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5)) +
      q ^ (36 + 6 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6)) +
      q ^ (49 + 7 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7)) +
      q ^ (64 + 8 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8)) := by
  simp [rogersRamanujanLHSTrunc, natSum, qPochhammer, Nat.mul_comm]

theorem rogersRamanujanLHSTrunc_nine (q : R) (a : Nat) :
    rogersRamanujanLHSTrunc q a 9 =
      1 + q ^ (1 + a) / (1 - q) +
      q ^ (4 + 2 * a) / ((1 - q) * (1 - q ^ 2)) +
      q ^ (9 + 3 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3)) +
      q ^ (16 + 4 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4)) +
      q ^ (25 + 5 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5)) +
      q ^ (36 + 6 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6)) +
      q ^ (49 + 7 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7)) +
      q ^ (64 + 8 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8)) +
      q ^ (81 + 9 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9)) := by
  simp [rogersRamanujanLHSTrunc, natSum, qPochhammer, Nat.mul_comm]

theorem rogersRamanujanLHSTrunc_ten (q : R) (a : Nat) :
    rogersRamanujanLHSTrunc q a 10 =
      1 + q ^ (1 + a) / (1 - q) +
      q ^ (4 + 2 * a) / ((1 - q) * (1 - q ^ 2)) +
      q ^ (9 + 3 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3)) +
      q ^ (16 + 4 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4)) +
      q ^ (25 + 5 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5)) +
      q ^ (36 + 6 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6)) +
      q ^ (49 + 7 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7)) +
      q ^ (64 + 8 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8)) +
      q ^ (81 + 9 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9)) +
      q ^ (100 + 10 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10)) := by
  simp [rogersRamanujanLHSTrunc, natSum, qPochhammer, Nat.mul_comm]

/-- RHS truncation at `N = 1` for parameter `a = 0`. -/
theorem rogersRamanujanRHSTrunc_one_a0 (q : R) (_hq : (1 - q ^ 4) ≠ 0)
    (_hq' : (1 - q) ≠ 0) :
    rogersRamanujanRHSTrunc q 0 1 = 1 / ((1 - q ^ 4) * (1 - q)) := by
  simp [rogersRamanujanRHSTrunc]

/-- RHS truncation at `N = 1` for parameter `a = 1`. -/
theorem rogersRamanujanRHSTrunc_one_a1 (q : R) (_hq : (1 - q ^ 3) ≠ 0)
    (_hq' : (1 - q ^ 2) ≠ 0) :
    rogersRamanujanRHSTrunc q 1 1 = 1 / ((1 - q ^ 3) * (1 - q ^ 2)) := by
  simp [rogersRamanujanRHSTrunc]

/-- RHS truncation at `N = 2` for parameter `a = 0`. -/
theorem rogersRamanujanRHSTrunc_two_a0 (q : R)
    (h1 : (1 - q) ≠ 0) (h4 : (1 - q ^ 4) ≠ 0)
    (h6 : (1 - q ^ 6) ≠ 0) (h9 : (1 - q ^ 9) ≠ 0) :
    rogersRamanujanRHSTrunc q 0 2 =
      1 / ((1 - q ^ 9) * (1 - q ^ 6) * (1 - q ^ 4) * (1 - q)) := by
  simp [rogersRamanujanRHSTrunc]
  field_simp [h1, h4, h6, h9]

/-- RHS truncation at `N = 2` for parameter `a = 1`. -/
theorem rogersRamanujanRHSTrunc_two_a1 (q : R)
    (h2 : (1 - q ^ 2) ≠ 0) (h3 : (1 - q ^ 3) ≠ 0)
    (h7 : (1 - q ^ 7) ≠ 0) (h8 : (1 - q ^ 8) ≠ 0) :
    rogersRamanujanRHSTrunc q 1 2 =
      1 / ((1 - q ^ 8) * (1 - q ^ 7) * (1 - q ^ 3) * (1 - q ^ 2)) := by
  simp [rogersRamanujanRHSTrunc]
  field_simp [h2, h3, h7, h8]

/-- RHS truncation at `N = 3` for parameter `a = 0`. -/
theorem rogersRamanujanRHSTrunc_three_a0 (q : R)
    (h1 : (1 - q) ≠ 0) (h4 : (1 - q ^ 4) ≠ 0)
    (h6 : (1 - q ^ 6) ≠ 0) (h9 : (1 - q ^ 9) ≠ 0)
    (h11 : (1 - q ^ 11) ≠ 0) (h14 : (1 - q ^ 14) ≠ 0) :
    rogersRamanujanRHSTrunc q 0 3 =
      1 / ((1 - q ^ 14) * (1 - q ^ 11) * (1 - q ^ 9) * (1 - q ^ 6) *
           (1 - q ^ 4) * (1 - q)) := by
  simp [rogersRamanujanRHSTrunc]
  field_simp [h1, h4, h6, h9, h11, h14]

/-- RHS truncation at `N = 3` for parameter `a = 1`. -/
theorem rogersRamanujanRHSTrunc_three_a1 (q : R)
    (h2 : (1 - q ^ 2) ≠ 0) (h3 : (1 - q ^ 3) ≠ 0)
    (h7 : (1 - q ^ 7) ≠ 0) (h8 : (1 - q ^ 8) ≠ 0)
    (h12 : (1 - q ^ 12) ≠ 0) (h13 : (1 - q ^ 13) ≠ 0) :
    rogersRamanujanRHSTrunc q 1 3 =
      1 / ((1 - q ^ 13) * (1 - q ^ 12) * (1 - q ^ 8) * (1 - q ^ 7) *
           (1 - q ^ 3) * (1 - q ^ 2)) := by
  simp [rogersRamanujanRHSTrunc]
  field_simp [h2, h3, h7, h8, h12, h13]

/-- RHS truncation at `N = 4` for parameter `a = 0`. -/
theorem rogersRamanujanRHSTrunc_four_a0 (q : R)
    (h1 : (1 - q) ≠ 0) (h4 : (1 - q ^ 4) ≠ 0)
    (h6 : (1 - q ^ 6) ≠ 0) (h9 : (1 - q ^ 9) ≠ 0)
    (h11 : (1 - q ^ 11) ≠ 0) (h14 : (1 - q ^ 14) ≠ 0)
    (h16 : (1 - q ^ 16) ≠ 0) (h19 : (1 - q ^ 19) ≠ 0) :
    rogersRamanujanRHSTrunc q 0 4 =
      1 / ((1 - q ^ 19) * (1 - q ^ 16) * (1 - q ^ 14) * (1 - q ^ 11) *
           (1 - q ^ 9) * (1 - q ^ 6) * (1 - q ^ 4) * (1 - q)) := by
  simp [rogersRamanujanRHSTrunc]
  field_simp [h1, h4, h6, h9, h11, h14, h16, h19]

/-- RHS truncation at `N = 4` for parameter `a = 1`. -/
theorem rogersRamanujanRHSTrunc_four_a1 (q : R)
    (h2 : (1 - q ^ 2) ≠ 0) (h3 : (1 - q ^ 3) ≠ 0)
    (h7 : (1 - q ^ 7) ≠ 0) (h8 : (1 - q ^ 8) ≠ 0)
    (h12 : (1 - q ^ 12) ≠ 0) (h13 : (1 - q ^ 13) ≠ 0)
    (h17 : (1 - q ^ 17) ≠ 0) (h18 : (1 - q ^ 18) ≠ 0) :
    rogersRamanujanRHSTrunc q 1 4 =
      1 / ((1 - q ^ 18) * (1 - q ^ 17) * (1 - q ^ 13) * (1 - q ^ 12) *
           (1 - q ^ 8) * (1 - q ^ 7) * (1 - q ^ 3) * (1 - q ^ 2)) := by
  simp [rogersRamanujanRHSTrunc]
  field_simp [h2, h3, h7, h8, h12, h13, h17, h18]

/-- RHS truncation at `N = 5` for parameter `a = 0`. -/
theorem rogersRamanujanRHSTrunc_five_a0 (q : R)
    (h1 : (1 - q) ≠ 0) (h4 : (1 - q ^ 4) ≠ 0)
    (h6 : (1 - q ^ 6) ≠ 0) (h9 : (1 - q ^ 9) ≠ 0)
    (h11 : (1 - q ^ 11) ≠ 0) (h14 : (1 - q ^ 14) ≠ 0)
    (h16 : (1 - q ^ 16) ≠ 0) (h19 : (1 - q ^ 19) ≠ 0)
    (h21 : (1 - q ^ 21) ≠ 0) (h24 : (1 - q ^ 24) ≠ 0) :
    rogersRamanujanRHSTrunc q 0 5 =
      1 / ((1 - q ^ 24) * (1 - q ^ 21) * (1 - q ^ 19) * (1 - q ^ 16) *
           (1 - q ^ 14) * (1 - q ^ 11) * (1 - q ^ 9) * (1 - q ^ 6) *
           (1 - q ^ 4) * (1 - q)) := by
  simp [rogersRamanujanRHSTrunc]
  field_simp [h1, h4, h6, h9, h11, h14, h16, h19, h21, h24]

/-- RHS truncation at `N = 5` for parameter `a = 1`. -/
theorem rogersRamanujanRHSTrunc_five_a1 (q : R)
    (h2 : (1 - q ^ 2) ≠ 0) (h3 : (1 - q ^ 3) ≠ 0)
    (h7 : (1 - q ^ 7) ≠ 0) (h8 : (1 - q ^ 8) ≠ 0)
    (h12 : (1 - q ^ 12) ≠ 0) (h13 : (1 - q ^ 13) ≠ 0)
    (h17 : (1 - q ^ 17) ≠ 0) (h18 : (1 - q ^ 18) ≠ 0)
    (h22 : (1 - q ^ 22) ≠ 0) (h23 : (1 - q ^ 23) ≠ 0) :
    rogersRamanujanRHSTrunc q 1 5 =
      1 / ((1 - q ^ 23) * (1 - q ^ 22) * (1 - q ^ 18) * (1 - q ^ 17) *
           (1 - q ^ 13) * (1 - q ^ 12) * (1 - q ^ 8) * (1 - q ^ 7) *
           (1 - q ^ 3) * (1 - q ^ 2)) := by
  simp [rogersRamanujanRHSTrunc]
  field_simp [h2, h3, h7, h8, h12, h13, h17, h18, h22, h23]

/-- RHS truncation at `N = 6` for parameter `a = 0`. -/
theorem rogersRamanujanRHSTrunc_six_a0 (q : R)
    (h1 : (1 - q) ≠ 0) (h4 : (1 - q ^ 4) ≠ 0)
    (h6 : (1 - q ^ 6) ≠ 0) (h9 : (1 - q ^ 9) ≠ 0)
    (h11 : (1 - q ^ 11) ≠ 0) (h14 : (1 - q ^ 14) ≠ 0)
    (h16 : (1 - q ^ 16) ≠ 0) (h19 : (1 - q ^ 19) ≠ 0)
    (h21 : (1 - q ^ 21) ≠ 0) (h24 : (1 - q ^ 24) ≠ 0)
    (h26 : (1 - q ^ 26) ≠ 0) (h29 : (1 - q ^ 29) ≠ 0) :
    rogersRamanujanRHSTrunc q 0 6 =
      1 / ((1 - q ^ 29) * (1 - q ^ 26) * (1 - q ^ 24) * (1 - q ^ 21) *
           (1 - q ^ 19) * (1 - q ^ 16) * (1 - q ^ 14) * (1 - q ^ 11) *
           (1 - q ^ 9) * (1 - q ^ 6) * (1 - q ^ 4) * (1 - q)) := by
  simp [rogersRamanujanRHSTrunc]
  field_simp [h1, h4, h6, h9, h11, h14, h16, h19, h21, h24, h26, h29]

/-- RHS truncation at `N = 6` for parameter `a = 1`. -/
theorem rogersRamanujanRHSTrunc_six_a1 (q : R)
    (h2 : (1 - q ^ 2) ≠ 0) (h3 : (1 - q ^ 3) ≠ 0)
    (h7 : (1 - q ^ 7) ≠ 0) (h8 : (1 - q ^ 8) ≠ 0)
    (h12 : (1 - q ^ 12) ≠ 0) (h13 : (1 - q ^ 13) ≠ 0)
    (h17 : (1 - q ^ 17) ≠ 0) (h18 : (1 - q ^ 18) ≠ 0)
    (h22 : (1 - q ^ 22) ≠ 0) (h23 : (1 - q ^ 23) ≠ 0)
    (h27 : (1 - q ^ 27) ≠ 0) (h28 : (1 - q ^ 28) ≠ 0) :
    rogersRamanujanRHSTrunc q 1 6 =
      1 / ((1 - q ^ 28) * (1 - q ^ 27) * (1 - q ^ 23) * (1 - q ^ 22) *
           (1 - q ^ 18) * (1 - q ^ 17) * (1 - q ^ 13) * (1 - q ^ 12) *
           (1 - q ^ 8) * (1 - q ^ 7) * (1 - q ^ 3) * (1 - q ^ 2)) := by
  simp [rogersRamanujanRHSTrunc]
  field_simp [h2, h3, h7, h8, h12, h13, h17, h18, h22, h23, h27, h28]

/-- RHS truncation at `N = 7` for parameter `a = 0`. -/
theorem rogersRamanujanRHSTrunc_seven_a0 (q : R)
    (h1 : (1 - q) ≠ 0) (h4 : (1 - q ^ 4) ≠ 0)
    (h6 : (1 - q ^ 6) ≠ 0) (h9 : (1 - q ^ 9) ≠ 0)
    (h11 : (1 - q ^ 11) ≠ 0) (h14 : (1 - q ^ 14) ≠ 0)
    (h16 : (1 - q ^ 16) ≠ 0) (h19 : (1 - q ^ 19) ≠ 0)
    (h21 : (1 - q ^ 21) ≠ 0) (h24 : (1 - q ^ 24) ≠ 0)
    (h26 : (1 - q ^ 26) ≠ 0) (h29 : (1 - q ^ 29) ≠ 0)
    (h31 : (1 - q ^ 31) ≠ 0) (h34 : (1 - q ^ 34) ≠ 0) :
    rogersRamanujanRHSTrunc q 0 7 =
      1 / ((1 - q ^ 34) * (1 - q ^ 31) * (1 - q ^ 29) * (1 - q ^ 26) *
           (1 - q ^ 24) * (1 - q ^ 21) * (1 - q ^ 19) * (1 - q ^ 16) *
           (1 - q ^ 14) * (1 - q ^ 11) * (1 - q ^ 9) * (1 - q ^ 6) *
           (1 - q ^ 4) * (1 - q)) := by
  simp [rogersRamanujanRHSTrunc]
  field_simp [h1, h4, h6, h9, h11, h14, h16, h19, h21, h24, h26, h29, h31, h34]

/-- RHS truncation at `N = 7` for parameter `a = 1`. -/
theorem rogersRamanujanRHSTrunc_seven_a1 (q : R)
    (h2 : (1 - q ^ 2) ≠ 0) (h3 : (1 - q ^ 3) ≠ 0)
    (h7 : (1 - q ^ 7) ≠ 0) (h8 : (1 - q ^ 8) ≠ 0)
    (h12 : (1 - q ^ 12) ≠ 0) (h13 : (1 - q ^ 13) ≠ 0)
    (h17 : (1 - q ^ 17) ≠ 0) (h18 : (1 - q ^ 18) ≠ 0)
    (h22 : (1 - q ^ 22) ≠ 0) (h23 : (1 - q ^ 23) ≠ 0)
    (h27 : (1 - q ^ 27) ≠ 0) (h28 : (1 - q ^ 28) ≠ 0)
    (h32 : (1 - q ^ 32) ≠ 0) (h33 : (1 - q ^ 33) ≠ 0) :
    rogersRamanujanRHSTrunc q 1 7 =
      1 / ((1 - q ^ 33) * (1 - q ^ 32) * (1 - q ^ 28) * (1 - q ^ 27) *
           (1 - q ^ 23) * (1 - q ^ 22) * (1 - q ^ 18) * (1 - q ^ 17) *
           (1 - q ^ 13) * (1 - q ^ 12) * (1 - q ^ 8) * (1 - q ^ 7) *
           (1 - q ^ 3) * (1 - q ^ 2)) := by
  simp [rogersRamanujanRHSTrunc]
  field_simp [h2, h3, h7, h8, h12, h13, h17, h18, h22, h23, h27, h28, h32, h33]

/-- RHS truncation at `N = 8` for parameter `a = 0`. -/
theorem rogersRamanujanRHSTrunc_eight_a0 (q : R)
    (h1 : (1 - q) ≠ 0) (h4 : (1 - q ^ 4) ≠ 0)
    (h6 : (1 - q ^ 6) ≠ 0) (h9 : (1 - q ^ 9) ≠ 0)
    (h11 : (1 - q ^ 11) ≠ 0) (h14 : (1 - q ^ 14) ≠ 0)
    (h16 : (1 - q ^ 16) ≠ 0) (h19 : (1 - q ^ 19) ≠ 0)
    (h21 : (1 - q ^ 21) ≠ 0) (h24 : (1 - q ^ 24) ≠ 0)
    (h26 : (1 - q ^ 26) ≠ 0) (h29 : (1 - q ^ 29) ≠ 0)
    (h31 : (1 - q ^ 31) ≠ 0) (h34 : (1 - q ^ 34) ≠ 0)
    (h36 : (1 - q ^ 36) ≠ 0) (h39 : (1 - q ^ 39) ≠ 0) :
    rogersRamanujanRHSTrunc q 0 8 =
      1 / ((1 - q ^ 39) * (1 - q ^ 36) * (1 - q ^ 34) * (1 - q ^ 31) *
           (1 - q ^ 29) * (1 - q ^ 26) * (1 - q ^ 24) * (1 - q ^ 21) *
           (1 - q ^ 19) * (1 - q ^ 16) * (1 - q ^ 14) * (1 - q ^ 11) *
           (1 - q ^ 9) * (1 - q ^ 6) * (1 - q ^ 4) * (1 - q)) := by
  simp [rogersRamanujanRHSTrunc]
  field_simp [h1, h4, h6, h9, h11, h14, h16, h19, h21, h24, h26, h29, h31, h34, h36, h39]

/-- RHS truncation at `N = 8` for parameter `a = 1`. -/
theorem rogersRamanujanRHSTrunc_eight_a1 (q : R)
    (h2 : (1 - q ^ 2) ≠ 0) (h3 : (1 - q ^ 3) ≠ 0)
    (h7 : (1 - q ^ 7) ≠ 0) (h8 : (1 - q ^ 8) ≠ 0)
    (h12 : (1 - q ^ 12) ≠ 0) (h13 : (1 - q ^ 13) ≠ 0)
    (h17 : (1 - q ^ 17) ≠ 0) (h18 : (1 - q ^ 18) ≠ 0)
    (h22 : (1 - q ^ 22) ≠ 0) (h23 : (1 - q ^ 23) ≠ 0)
    (h27 : (1 - q ^ 27) ≠ 0) (h28 : (1 - q ^ 28) ≠ 0)
    (h32 : (1 - q ^ 32) ≠ 0) (h33 : (1 - q ^ 33) ≠ 0)
    (h37 : (1 - q ^ 37) ≠ 0) (h38 : (1 - q ^ 38) ≠ 0) :
    rogersRamanujanRHSTrunc q 1 8 =
      1 / ((1 - q ^ 38) * (1 - q ^ 37) * (1 - q ^ 33) * (1 - q ^ 32) *
           (1 - q ^ 28) * (1 - q ^ 27) * (1 - q ^ 23) * (1 - q ^ 22) *
           (1 - q ^ 18) * (1 - q ^ 17) * (1 - q ^ 13) * (1 - q ^ 12) *
           (1 - q ^ 8) * (1 - q ^ 7) * (1 - q ^ 3) * (1 - q ^ 2)) := by
  simp [rogersRamanujanRHSTrunc]
  field_simp [h2, h3, h7, h8, h12, h13, h17, h18, h22, h23, h27, h28, h32, h33, h37, h38]

/-- RHS truncation at `N = 9` for parameter `a = 0`. -/
theorem rogersRamanujanRHSTrunc_nine_a0 (q : R)
    (h1 : (1 - q) ≠ 0) (h4 : (1 - q ^ 4) ≠ 0)
    (h6 : (1 - q ^ 6) ≠ 0) (h9 : (1 - q ^ 9) ≠ 0)
    (h11 : (1 - q ^ 11) ≠ 0) (h14 : (1 - q ^ 14) ≠ 0)
    (h16 : (1 - q ^ 16) ≠ 0) (h19 : (1 - q ^ 19) ≠ 0)
    (h21 : (1 - q ^ 21) ≠ 0) (h24 : (1 - q ^ 24) ≠ 0)
    (h26 : (1 - q ^ 26) ≠ 0) (h29 : (1 - q ^ 29) ≠ 0)
    (h31 : (1 - q ^ 31) ≠ 0) (h34 : (1 - q ^ 34) ≠ 0)
    (h36 : (1 - q ^ 36) ≠ 0) (h39 : (1 - q ^ 39) ≠ 0)
    (h41 : (1 - q ^ 41) ≠ 0) (h44 : (1 - q ^ 44) ≠ 0) :
    rogersRamanujanRHSTrunc q 0 9 =
      1 / ((1 - q ^ 44) * (1 - q ^ 41) * (1 - q ^ 39) * (1 - q ^ 36) *
           (1 - q ^ 34) * (1 - q ^ 31) * (1 - q ^ 29) * (1 - q ^ 26) *
           (1 - q ^ 24) * (1 - q ^ 21) * (1 - q ^ 19) * (1 - q ^ 16) *
           (1 - q ^ 14) * (1 - q ^ 11) * (1 - q ^ 9) * (1 - q ^ 6) *
           (1 - q ^ 4) * (1 - q)) := by
  simp [rogersRamanujanRHSTrunc]
  field_simp [h1, h4, h6, h9, h11, h14, h16, h19, h21, h24, h26, h29, h31, h34, h36, h39, h41, h44]

/-- RHS truncation at `N = 9` for parameter `a = 1`. -/
theorem rogersRamanujanRHSTrunc_nine_a1 (q : R)
    (h2 : (1 - q ^ 2) ≠ 0) (h3 : (1 - q ^ 3) ≠ 0)
    (h7 : (1 - q ^ 7) ≠ 0) (h8 : (1 - q ^ 8) ≠ 0)
    (h12 : (1 - q ^ 12) ≠ 0) (h13 : (1 - q ^ 13) ≠ 0)
    (h17 : (1 - q ^ 17) ≠ 0) (h18 : (1 - q ^ 18) ≠ 0)
    (h22 : (1 - q ^ 22) ≠ 0) (h23 : (1 - q ^ 23) ≠ 0)
    (h27 : (1 - q ^ 27) ≠ 0) (h28 : (1 - q ^ 28) ≠ 0)
    (h32 : (1 - q ^ 32) ≠ 0) (h33 : (1 - q ^ 33) ≠ 0)
    (h37 : (1 - q ^ 37) ≠ 0) (h38 : (1 - q ^ 38) ≠ 0)
    (h42 : (1 - q ^ 42) ≠ 0) (h43 : (1 - q ^ 43) ≠ 0) :
    rogersRamanujanRHSTrunc q 1 9 =
      1 / ((1 - q ^ 43) * (1 - q ^ 42) * (1 - q ^ 38) * (1 - q ^ 37) *
           (1 - q ^ 33) * (1 - q ^ 32) * (1 - q ^ 28) * (1 - q ^ 27) *
           (1 - q ^ 23) * (1 - q ^ 22) * (1 - q ^ 18) * (1 - q ^ 17) *
           (1 - q ^ 13) * (1 - q ^ 12) * (1 - q ^ 8) * (1 - q ^ 7) *
           (1 - q ^ 3) * (1 - q ^ 2)) := by
  simp [rogersRamanujanRHSTrunc]
  field_simp [h2, h3, h7, h8, h12, h13, h17, h18, h22, h23, h27, h28, h32, h33, h37, h38, h42, h43]

/-- RHS truncation at `N = 10` for parameter `a = 0`. -/
theorem rogersRamanujanRHSTrunc_ten_a0 (q : R)
    (h1 : (1 - q) ≠ 0) (h4 : (1 - q ^ 4) ≠ 0)
    (h6 : (1 - q ^ 6) ≠ 0) (h9 : (1 - q ^ 9) ≠ 0)
    (h11 : (1 - q ^ 11) ≠ 0) (h14 : (1 - q ^ 14) ≠ 0)
    (h16 : (1 - q ^ 16) ≠ 0) (h19 : (1 - q ^ 19) ≠ 0)
    (h21 : (1 - q ^ 21) ≠ 0) (h24 : (1 - q ^ 24) ≠ 0)
    (h26 : (1 - q ^ 26) ≠ 0) (h29 : (1 - q ^ 29) ≠ 0)
    (h31 : (1 - q ^ 31) ≠ 0) (h34 : (1 - q ^ 34) ≠ 0)
    (h36 : (1 - q ^ 36) ≠ 0) (h39 : (1 - q ^ 39) ≠ 0)
    (h41 : (1 - q ^ 41) ≠ 0) (h44 : (1 - q ^ 44) ≠ 0)
    (h46 : (1 - q ^ 46) ≠ 0) (h49 : (1 - q ^ 49) ≠ 0) :
    rogersRamanujanRHSTrunc q 0 10 =
      1 / ((1 - q ^ 49) * (1 - q ^ 46) * (1 - q ^ 44) * (1 - q ^ 41) *
           (1 - q ^ 39) * (1 - q ^ 36) * (1 - q ^ 34) * (1 - q ^ 31) *
           (1 - q ^ 29) * (1 - q ^ 26) * (1 - q ^ 24) * (1 - q ^ 21) *
           (1 - q ^ 19) * (1 - q ^ 16) * (1 - q ^ 14) * (1 - q ^ 11) *
           (1 - q ^ 9) * (1 - q ^ 6) * (1 - q ^ 4) * (1 - q)) := by
  simp [rogersRamanujanRHSTrunc]
  field_simp [h1, h4, h6, h9, h11, h14, h16, h19, h21, h24, h26, h29, h31, h34, h36, h39, h41, h44, h46, h49]

/-- RHS truncation at `N = 10` for parameter `a = 1`. -/
theorem rogersRamanujanRHSTrunc_ten_a1 (q : R)
    (h2 : (1 - q ^ 2) ≠ 0) (h3 : (1 - q ^ 3) ≠ 0)
    (h7 : (1 - q ^ 7) ≠ 0) (h8 : (1 - q ^ 8) ≠ 0)
    (h12 : (1 - q ^ 12) ≠ 0) (h13 : (1 - q ^ 13) ≠ 0)
    (h17 : (1 - q ^ 17) ≠ 0) (h18 : (1 - q ^ 18) ≠ 0)
    (h22 : (1 - q ^ 22) ≠ 0) (h23 : (1 - q ^ 23) ≠ 0)
    (h27 : (1 - q ^ 27) ≠ 0) (h28 : (1 - q ^ 28) ≠ 0)
    (h32 : (1 - q ^ 32) ≠ 0) (h33 : (1 - q ^ 33) ≠ 0)
    (h37 : (1 - q ^ 37) ≠ 0) (h38 : (1 - q ^ 38) ≠ 0)
    (h42 : (1 - q ^ 42) ≠ 0) (h43 : (1 - q ^ 43) ≠ 0)
    (h47 : (1 - q ^ 47) ≠ 0) (h48 : (1 - q ^ 48) ≠ 0) :
    rogersRamanujanRHSTrunc q 1 10 =
      1 / ((1 - q ^ 48) * (1 - q ^ 47) * (1 - q ^ 43) * (1 - q ^ 42) *
           (1 - q ^ 38) * (1 - q ^ 37) * (1 - q ^ 33) * (1 - q ^ 32) *
           (1 - q ^ 28) * (1 - q ^ 27) * (1 - q ^ 23) * (1 - q ^ 22) *
           (1 - q ^ 18) * (1 - q ^ 17) * (1 - q ^ 13) * (1 - q ^ 12) *
           (1 - q ^ 8) * (1 - q ^ 7) * (1 - q ^ 3) * (1 - q ^ 2)) := by
  simp [rogersRamanujanRHSTrunc]
  field_simp [h2, h3, h7, h8, h12, h13, h17, h18, h22, h23, h27, h28, h32, h33, h37, h38, h42, h43, h47, h48]

theorem rogersRamanujanRHSTrunc_eleven_zero (q : R)
    (h1 : (1 - q) ≠ 0) (h4 : (1 - q ^ 4) ≠ 0)
    (h6 : (1 - q ^ 6) ≠ 0) (h9 : (1 - q ^ 9) ≠ 0)
    (h11 : (1 - q ^ 11) ≠ 0) (h14 : (1 - q ^ 14) ≠ 0)
    (h16 : (1 - q ^ 16) ≠ 0) (h19 : (1 - q ^ 19) ≠ 0)
    (h21 : (1 - q ^ 21) ≠ 0) (h24 : (1 - q ^ 24) ≠ 0)
    (h26 : (1 - q ^ 26) ≠ 0) (h29 : (1 - q ^ 29) ≠ 0)
    (h31 : (1 - q ^ 31) ≠ 0) (h34 : (1 - q ^ 34) ≠ 0)
    (h36 : (1 - q ^ 36) ≠ 0) (h39 : (1 - q ^ 39) ≠ 0)
    (h41 : (1 - q ^ 41) ≠ 0) (h44 : (1 - q ^ 44) ≠ 0)
    (h46 : (1 - q ^ 46) ≠ 0) (h49 : (1 - q ^ 49) ≠ 0)
    (h51 : (1 - q ^ 51) ≠ 0) (h54 : (1 - q ^ 54) ≠ 0) :
    rogersRamanujanRHSTrunc q 0 11 =
      1 / ((1 - q ^ 54) * (1 - q ^ 51) * (1 - q ^ 49) * (1 - q ^ 46) *
           (1 - q ^ 44) * (1 - q ^ 41) * (1 - q ^ 39) * (1 - q ^ 36) *
           (1 - q ^ 34) * (1 - q ^ 31) * (1 - q ^ 29) * (1 - q ^ 26) *
           (1 - q ^ 24) * (1 - q ^ 21) * (1 - q ^ 19) * (1 - q ^ 16) *
           (1 - q ^ 14) * (1 - q ^ 11) * (1 - q ^ 9) * (1 - q ^ 6) *
           (1 - q ^ 4) * (1 - q)) := by
  simp [rogersRamanujanRHSTrunc]
  field_simp [h1, h4, h6, h9, h11, h14, h16, h19, h21, h24, h26, h29, h31, h34, h36, h39, h41, h44, h46, h49, h51, h54]

theorem rogersRamanujanRHSTrunc_eleven_one (q : R)
    (h2 : (1 - q ^ 2) ≠ 0) (h3 : (1 - q ^ 3) ≠ 0)
    (h7 : (1 - q ^ 7) ≠ 0) (h8 : (1 - q ^ 8) ≠ 0)
    (h12 : (1 - q ^ 12) ≠ 0) (h13 : (1 - q ^ 13) ≠ 0)
    (h17 : (1 - q ^ 17) ≠ 0) (h18 : (1 - q ^ 18) ≠ 0)
    (h22 : (1 - q ^ 22) ≠ 0) (h23 : (1 - q ^ 23) ≠ 0)
    (h27 : (1 - q ^ 27) ≠ 0) (h28 : (1 - q ^ 28) ≠ 0)
    (h32 : (1 - q ^ 32) ≠ 0) (h33 : (1 - q ^ 33) ≠ 0)
    (h37 : (1 - q ^ 37) ≠ 0) (h38 : (1 - q ^ 38) ≠ 0)
    (h42 : (1 - q ^ 42) ≠ 0) (h43 : (1 - q ^ 43) ≠ 0)
    (h47 : (1 - q ^ 47) ≠ 0) (h48 : (1 - q ^ 48) ≠ 0)
    (h52 : (1 - q ^ 52) ≠ 0) (h53 : (1 - q ^ 53) ≠ 0) :
    rogersRamanujanRHSTrunc q 1 11 =
      1 / ((1 - q ^ 53) * (1 - q ^ 52) * (1 - q ^ 48) * (1 - q ^ 47) *
           (1 - q ^ 43) * (1 - q ^ 42) * (1 - q ^ 38) * (1 - q ^ 37) *
           (1 - q ^ 33) * (1 - q ^ 32) * (1 - q ^ 28) * (1 - q ^ 27) *
           (1 - q ^ 23) * (1 - q ^ 22) * (1 - q ^ 18) * (1 - q ^ 17) *
           (1 - q ^ 13) * (1 - q ^ 12) * (1 - q ^ 8) * (1 - q ^ 7) *
           (1 - q ^ 3) * (1 - q ^ 2)) := by
  simp [rogersRamanujanRHSTrunc]
  field_simp [h2, h3, h7, h8, h12, h13, h17, h18, h22, h23, h27, h28, h32, h33, h37, h38, h42, h43, h47, h48, h52, h53]

theorem rogersRamanujanRHSTrunc_twelve_zero (q : R)
    (h1 : (1 - q) ≠ 0) (h4 : (1 - q ^ 4) ≠ 0)
    (h6 : (1 - q ^ 6) ≠ 0) (h9 : (1 - q ^ 9) ≠ 0)
    (h11 : (1 - q ^ 11) ≠ 0) (h14 : (1 - q ^ 14) ≠ 0)
    (h16 : (1 - q ^ 16) ≠ 0) (h19 : (1 - q ^ 19) ≠ 0)
    (h21 : (1 - q ^ 21) ≠ 0) (h24 : (1 - q ^ 24) ≠ 0)
    (h26 : (1 - q ^ 26) ≠ 0) (h29 : (1 - q ^ 29) ≠ 0)
    (h31 : (1 - q ^ 31) ≠ 0) (h34 : (1 - q ^ 34) ≠ 0)
    (h36 : (1 - q ^ 36) ≠ 0) (h39 : (1 - q ^ 39) ≠ 0)
    (h41 : (1 - q ^ 41) ≠ 0) (h44 : (1 - q ^ 44) ≠ 0)
    (h46 : (1 - q ^ 46) ≠ 0) (h49 : (1 - q ^ 49) ≠ 0)
    (h51 : (1 - q ^ 51) ≠ 0) (h54 : (1 - q ^ 54) ≠ 0)
    (h56 : (1 - q ^ 56) ≠ 0) (h59 : (1 - q ^ 59) ≠ 0) :
    rogersRamanujanRHSTrunc q 0 12 =
      1 / ((1 - q ^ 59) * (1 - q ^ 56) * (1 - q ^ 54) * (1 - q ^ 51) *
           (1 - q ^ 49) * (1 - q ^ 46) * (1 - q ^ 44) * (1 - q ^ 41) *
           (1 - q ^ 39) * (1 - q ^ 36) * (1 - q ^ 34) * (1 - q ^ 31) *
           (1 - q ^ 29) * (1 - q ^ 26) * (1 - q ^ 24) * (1 - q ^ 21) *
           (1 - q ^ 19) * (1 - q ^ 16) * (1 - q ^ 14) * (1 - q ^ 11) *
           (1 - q ^ 9) * (1 - q ^ 6) * (1 - q ^ 4) * (1 - q)) := by
  simp [rogersRamanujanRHSTrunc]
  field_simp [h1, h4, h6, h9, h11, h14, h16, h19, h21, h24, h26, h29, h31, h34, h36, h39, h41, h44, h46, h49, h51, h54, h56, h59]

theorem rogersRamanujanRHSTrunc_twelve_one (q : R)
    (h2 : (1 - q ^ 2) ≠ 0) (h3 : (1 - q ^ 3) ≠ 0)
    (h7 : (1 - q ^ 7) ≠ 0) (h8 : (1 - q ^ 8) ≠ 0)
    (h12 : (1 - q ^ 12) ≠ 0) (h13 : (1 - q ^ 13) ≠ 0)
    (h17 : (1 - q ^ 17) ≠ 0) (h18 : (1 - q ^ 18) ≠ 0)
    (h22 : (1 - q ^ 22) ≠ 0) (h23 : (1 - q ^ 23) ≠ 0)
    (h27 : (1 - q ^ 27) ≠ 0) (h28 : (1 - q ^ 28) ≠ 0)
    (h32 : (1 - q ^ 32) ≠ 0) (h33 : (1 - q ^ 33) ≠ 0)
    (h37 : (1 - q ^ 37) ≠ 0) (h38 : (1 - q ^ 38) ≠ 0)
    (h42 : (1 - q ^ 42) ≠ 0) (h43 : (1 - q ^ 43) ≠ 0)
    (h47 : (1 - q ^ 47) ≠ 0) (h48 : (1 - q ^ 48) ≠ 0)
    (h52 : (1 - q ^ 52) ≠ 0) (h53 : (1 - q ^ 53) ≠ 0)
    (h57 : (1 - q ^ 57) ≠ 0) (h58 : (1 - q ^ 58) ≠ 0) :
    rogersRamanujanRHSTrunc q 1 12 =
      1 / ((1 - q ^ 58) * (1 - q ^ 57) * (1 - q ^ 53) * (1 - q ^ 52) *
           (1 - q ^ 48) * (1 - q ^ 47) * (1 - q ^ 43) * (1 - q ^ 42) *
           (1 - q ^ 38) * (1 - q ^ 37) * (1 - q ^ 33) * (1 - q ^ 32) *
           (1 - q ^ 28) * (1 - q ^ 27) * (1 - q ^ 23) * (1 - q ^ 22) *
           (1 - q ^ 18) * (1 - q ^ 17) * (1 - q ^ 13) * (1 - q ^ 12) *
           (1 - q ^ 8) * (1 - q ^ 7) * (1 - q ^ 3) * (1 - q ^ 2)) := by
  simp [rogersRamanujanRHSTrunc]
  field_simp [h2, h3, h7, h8, h12, h13, h17, h18, h22, h23, h27, h28, h32, h33, h37, h38, h42, h43, h47, h48, h52, h53, h57, h58]

theorem rogersRamanujanRHSTrunc_thirteen_zero (q : R)
    (h1 : (1 - q) ≠ 0)
    (h4 : (1 - q ^ 4) ≠ 0)
    (h6 : (1 - q ^ 6) ≠ 0)
    (h9 : (1 - q ^ 9) ≠ 0)
    (h11 : (1 - q ^ 11) ≠ 0)
    (h14 : (1 - q ^ 14) ≠ 0)
    (h16 : (1 - q ^ 16) ≠ 0)
    (h19 : (1 - q ^ 19) ≠ 0)
    (h21 : (1 - q ^ 21) ≠ 0)
    (h24 : (1 - q ^ 24) ≠ 0)
    (h26 : (1 - q ^ 26) ≠ 0)
    (h29 : (1 - q ^ 29) ≠ 0)
    (h31 : (1 - q ^ 31) ≠ 0)
    (h34 : (1 - q ^ 34) ≠ 0)
    (h36 : (1 - q ^ 36) ≠ 0)
    (h39 : (1 - q ^ 39) ≠ 0)
    (h41 : (1 - q ^ 41) ≠ 0)
    (h44 : (1 - q ^ 44) ≠ 0)
    (h46 : (1 - q ^ 46) ≠ 0)
    (h49 : (1 - q ^ 49) ≠ 0)
    (h51 : (1 - q ^ 51) ≠ 0)
    (h54 : (1 - q ^ 54) ≠ 0)
    (h56 : (1 - q ^ 56) ≠ 0)
    (h59 : (1 - q ^ 59) ≠ 0)
    (h61 : (1 - q ^ 61) ≠ 0)
    (h64 : (1 - q ^ 64) ≠ 0)
    :
    rogersRamanujanRHSTrunc q 0 13 =
      1 / ((1 - q ^ 64) * (1 - q ^ 61) * (1 - q ^ 59) * (1 - q ^ 56) *
           (1 - q ^ 54) * (1 - q ^ 51) * (1 - q ^ 49) * (1 - q ^ 46) *
           (1 - q ^ 44) * (1 - q ^ 41) * (1 - q ^ 39) * (1 - q ^ 36) *
           (1 - q ^ 34) * (1 - q ^ 31) * (1 - q ^ 29) * (1 - q ^ 26) *
           (1 - q ^ 24) * (1 - q ^ 21) * (1 - q ^ 19) * (1 - q ^ 16) *
           (1 - q ^ 14) * (1 - q ^ 11) * (1 - q ^ 9) * (1 - q ^ 6) *
           (1 - q ^ 4) * (1 - q)) := by
  simp [rogersRamanujanRHSTrunc]
  field_simp [h1, h4, h6, h9, h11, h14, h16, h19, h21, h24, h26, h29, h31, h34, h36, h39, h41, h44, h46, h49, h51, h54, h56, h59, h61, h64]

theorem rogersRamanujanRHSTrunc_thirteen_one (q : R)
    (h2 : (1 - q ^ 2) ≠ 0)
    (h3 : (1 - q ^ 3) ≠ 0)
    (h7 : (1 - q ^ 7) ≠ 0)
    (h8 : (1 - q ^ 8) ≠ 0)
    (h12 : (1 - q ^ 12) ≠ 0)
    (h13 : (1 - q ^ 13) ≠ 0)
    (h17 : (1 - q ^ 17) ≠ 0)
    (h18 : (1 - q ^ 18) ≠ 0)
    (h22 : (1 - q ^ 22) ≠ 0)
    (h23 : (1 - q ^ 23) ≠ 0)
    (h27 : (1 - q ^ 27) ≠ 0)
    (h28 : (1 - q ^ 28) ≠ 0)
    (h32 : (1 - q ^ 32) ≠ 0)
    (h33 : (1 - q ^ 33) ≠ 0)
    (h37 : (1 - q ^ 37) ≠ 0)
    (h38 : (1 - q ^ 38) ≠ 0)
    (h42 : (1 - q ^ 42) ≠ 0)
    (h43 : (1 - q ^ 43) ≠ 0)
    (h47 : (1 - q ^ 47) ≠ 0)
    (h48 : (1 - q ^ 48) ≠ 0)
    (h52 : (1 - q ^ 52) ≠ 0)
    (h53 : (1 - q ^ 53) ≠ 0)
    (h57 : (1 - q ^ 57) ≠ 0)
    (h58 : (1 - q ^ 58) ≠ 0)
    (h62 : (1 - q ^ 62) ≠ 0)
    (h63 : (1 - q ^ 63) ≠ 0)
    :
    rogersRamanujanRHSTrunc q 1 13 =
      1 / ((1 - q ^ 63) * (1 - q ^ 62) * (1 - q ^ 58) * (1 - q ^ 57) *
           (1 - q ^ 53) * (1 - q ^ 52) * (1 - q ^ 48) * (1 - q ^ 47) *
           (1 - q ^ 43) * (1 - q ^ 42) * (1 - q ^ 38) * (1 - q ^ 37) *
           (1 - q ^ 33) * (1 - q ^ 32) * (1 - q ^ 28) * (1 - q ^ 27) *
           (1 - q ^ 23) * (1 - q ^ 22) * (1 - q ^ 18) * (1 - q ^ 17) *
           (1 - q ^ 13) * (1 - q ^ 12) * (1 - q ^ 8) * (1 - q ^ 7) *
           (1 - q ^ 3) * (1 - q ^ 2)) := by
  simp [rogersRamanujanRHSTrunc]
  field_simp [h2, h3, h7, h8, h12, h13, h17, h18, h22, h23, h27, h28, h32, h33, h37, h38, h42, h43, h47, h48, h52, h53, h57, h58, h62, h63]

theorem rogersRamanujanRHSTrunc_fourteen_zero (q : R)
    (h1 : (1 - q) ≠ 0)
    (h4 : (1 - q ^ 4) ≠ 0)
    (h6 : (1 - q ^ 6) ≠ 0)
    (h9 : (1 - q ^ 9) ≠ 0)
    (h11 : (1 - q ^ 11) ≠ 0)
    (h14 : (1 - q ^ 14) ≠ 0)
    (h16 : (1 - q ^ 16) ≠ 0)
    (h19 : (1 - q ^ 19) ≠ 0)
    (h21 : (1 - q ^ 21) ≠ 0)
    (h24 : (1 - q ^ 24) ≠ 0)
    (h26 : (1 - q ^ 26) ≠ 0)
    (h29 : (1 - q ^ 29) ≠ 0)
    (h31 : (1 - q ^ 31) ≠ 0)
    (h34 : (1 - q ^ 34) ≠ 0)
    (h36 : (1 - q ^ 36) ≠ 0)
    (h39 : (1 - q ^ 39) ≠ 0)
    (h41 : (1 - q ^ 41) ≠ 0)
    (h44 : (1 - q ^ 44) ≠ 0)
    (h46 : (1 - q ^ 46) ≠ 0)
    (h49 : (1 - q ^ 49) ≠ 0)
    (h51 : (1 - q ^ 51) ≠ 0)
    (h54 : (1 - q ^ 54) ≠ 0)
    (h56 : (1 - q ^ 56) ≠ 0)
    (h59 : (1 - q ^ 59) ≠ 0)
    (h61 : (1 - q ^ 61) ≠ 0)
    (h64 : (1 - q ^ 64) ≠ 0)
    (h66 : (1 - q ^ 66) ≠ 0)
    (h69 : (1 - q ^ 69) ≠ 0)
    :
    rogersRamanujanRHSTrunc q 0 14 =
      1 / ((1 - q ^ 69) * (1 - q ^ 66) * (1 - q ^ 64) * (1 - q ^ 61) *
           (1 - q ^ 59) * (1 - q ^ 56) * (1 - q ^ 54) * (1 - q ^ 51) *
           (1 - q ^ 49) * (1 - q ^ 46) * (1 - q ^ 44) * (1 - q ^ 41) *
           (1 - q ^ 39) * (1 - q ^ 36) * (1 - q ^ 34) * (1 - q ^ 31) *
           (1 - q ^ 29) * (1 - q ^ 26) * (1 - q ^ 24) * (1 - q ^ 21) *
           (1 - q ^ 19) * (1 - q ^ 16) * (1 - q ^ 14) * (1 - q ^ 11) *
           (1 - q ^ 9) * (1 - q ^ 6) * (1 - q ^ 4) * (1 - q)) := by
  simp [rogersRamanujanRHSTrunc]
  field_simp [h1, h4, h6, h9, h11, h14, h16, h19, h21, h24, h26, h29, h31, h34, h36, h39, h41, h44, h46, h49, h51, h54, h56, h59, h61, h64, h66, h69]

theorem rogersRamanujanRHSTrunc_fourteen_one (q : R)
    (h2 : (1 - q ^ 2) ≠ 0)
    (h3 : (1 - q ^ 3) ≠ 0)
    (h7 : (1 - q ^ 7) ≠ 0)
    (h8 : (1 - q ^ 8) ≠ 0)
    (h12 : (1 - q ^ 12) ≠ 0)
    (h13 : (1 - q ^ 13) ≠ 0)
    (h17 : (1 - q ^ 17) ≠ 0)
    (h18 : (1 - q ^ 18) ≠ 0)
    (h22 : (1 - q ^ 22) ≠ 0)
    (h23 : (1 - q ^ 23) ≠ 0)
    (h27 : (1 - q ^ 27) ≠ 0)
    (h28 : (1 - q ^ 28) ≠ 0)
    (h32 : (1 - q ^ 32) ≠ 0)
    (h33 : (1 - q ^ 33) ≠ 0)
    (h37 : (1 - q ^ 37) ≠ 0)
    (h38 : (1 - q ^ 38) ≠ 0)
    (h42 : (1 - q ^ 42) ≠ 0)
    (h43 : (1 - q ^ 43) ≠ 0)
    (h47 : (1 - q ^ 47) ≠ 0)
    (h48 : (1 - q ^ 48) ≠ 0)
    (h52 : (1 - q ^ 52) ≠ 0)
    (h53 : (1 - q ^ 53) ≠ 0)
    (h57 : (1 - q ^ 57) ≠ 0)
    (h58 : (1 - q ^ 58) ≠ 0)
    (h62 : (1 - q ^ 62) ≠ 0)
    (h63 : (1 - q ^ 63) ≠ 0)
    (h67 : (1 - q ^ 67) ≠ 0)
    (h68 : (1 - q ^ 68) ≠ 0)
    :
    rogersRamanujanRHSTrunc q 1 14 =
      1 / ((1 - q ^ 68) * (1 - q ^ 67) * (1 - q ^ 63) * (1 - q ^ 62) *
           (1 - q ^ 58) * (1 - q ^ 57) * (1 - q ^ 53) * (1 - q ^ 52) *
           (1 - q ^ 48) * (1 - q ^ 47) * (1 - q ^ 43) * (1 - q ^ 42) *
           (1 - q ^ 38) * (1 - q ^ 37) * (1 - q ^ 33) * (1 - q ^ 32) *
           (1 - q ^ 28) * (1 - q ^ 27) * (1 - q ^ 23) * (1 - q ^ 22) *
           (1 - q ^ 18) * (1 - q ^ 17) * (1 - q ^ 13) * (1 - q ^ 12) *
           (1 - q ^ 8) * (1 - q ^ 7) * (1 - q ^ 3) * (1 - q ^ 2)) := by
  simp [rogersRamanujanRHSTrunc]
  field_simp [h2, h3, h7, h8, h12, h13, h17, h18, h22, h23, h27, h28, h32, h33, h37, h38, h42, h43, h47, h48, h52, h53, h57, h58, h62, h63, h67, h68]

theorem rogersRamanujanRHSTrunc_fifteen_zero (q : R)
    (h1 : (1 - q) ≠ 0)
    (h4 : (1 - q ^ 4) ≠ 0)
    (h6 : (1 - q ^ 6) ≠ 0)
    (h9 : (1 - q ^ 9) ≠ 0)
    (h11 : (1 - q ^ 11) ≠ 0)
    (h14 : (1 - q ^ 14) ≠ 0)
    (h16 : (1 - q ^ 16) ≠ 0)
    (h19 : (1 - q ^ 19) ≠ 0)
    (h21 : (1 - q ^ 21) ≠ 0)
    (h24 : (1 - q ^ 24) ≠ 0)
    (h26 : (1 - q ^ 26) ≠ 0)
    (h29 : (1 - q ^ 29) ≠ 0)
    (h31 : (1 - q ^ 31) ≠ 0)
    (h34 : (1 - q ^ 34) ≠ 0)
    (h36 : (1 - q ^ 36) ≠ 0)
    (h39 : (1 - q ^ 39) ≠ 0)
    (h41 : (1 - q ^ 41) ≠ 0)
    (h44 : (1 - q ^ 44) ≠ 0)
    (h46 : (1 - q ^ 46) ≠ 0)
    (h49 : (1 - q ^ 49) ≠ 0)
    (h51 : (1 - q ^ 51) ≠ 0)
    (h54 : (1 - q ^ 54) ≠ 0)
    (h56 : (1 - q ^ 56) ≠ 0)
    (h59 : (1 - q ^ 59) ≠ 0)
    (h61 : (1 - q ^ 61) ≠ 0)
    (h64 : (1 - q ^ 64) ≠ 0)
    (h66 : (1 - q ^ 66) ≠ 0)
    (h69 : (1 - q ^ 69) ≠ 0)
    (h71 : (1 - q ^ 71) ≠ 0)
    (h74 : (1 - q ^ 74) ≠ 0)
    :
    rogersRamanujanRHSTrunc q 0 15 =
      1 / ((1 - q ^ 74) * (1 - q ^ 71) * (1 - q ^ 69) * (1 - q ^ 66) *
           (1 - q ^ 64) * (1 - q ^ 61) * (1 - q ^ 59) * (1 - q ^ 56) *
           (1 - q ^ 54) * (1 - q ^ 51) * (1 - q ^ 49) * (1 - q ^ 46) *
           (1 - q ^ 44) * (1 - q ^ 41) * (1 - q ^ 39) * (1 - q ^ 36) *
           (1 - q ^ 34) * (1 - q ^ 31) * (1 - q ^ 29) * (1 - q ^ 26) *
           (1 - q ^ 24) * (1 - q ^ 21) * (1 - q ^ 19) * (1 - q ^ 16) *
           (1 - q ^ 14) * (1 - q ^ 11) * (1 - q ^ 9) * (1 - q ^ 6) *
           (1 - q ^ 4) * (1 - q)) := by
  simp [rogersRamanujanRHSTrunc]
  field_simp [h1, h4, h6, h9, h11, h14, h16, h19, h21, h24, h26, h29, h31, h34, h36, h39, h41, h44, h46, h49, h51, h54, h56, h59, h61, h64, h66, h69, h71, h74]

theorem rogersRamanujanRHSTrunc_fifteen_one (q : R)
    (h2 : (1 - q ^ 2) ≠ 0)
    (h3 : (1 - q ^ 3) ≠ 0)
    (h7 : (1 - q ^ 7) ≠ 0)
    (h8 : (1 - q ^ 8) ≠ 0)
    (h12 : (1 - q ^ 12) ≠ 0)
    (h13 : (1 - q ^ 13) ≠ 0)
    (h17 : (1 - q ^ 17) ≠ 0)
    (h18 : (1 - q ^ 18) ≠ 0)
    (h22 : (1 - q ^ 22) ≠ 0)
    (h23 : (1 - q ^ 23) ≠ 0)
    (h27 : (1 - q ^ 27) ≠ 0)
    (h28 : (1 - q ^ 28) ≠ 0)
    (h32 : (1 - q ^ 32) ≠ 0)
    (h33 : (1 - q ^ 33) ≠ 0)
    (h37 : (1 - q ^ 37) ≠ 0)
    (h38 : (1 - q ^ 38) ≠ 0)
    (h42 : (1 - q ^ 42) ≠ 0)
    (h43 : (1 - q ^ 43) ≠ 0)
    (h47 : (1 - q ^ 47) ≠ 0)
    (h48 : (1 - q ^ 48) ≠ 0)
    (h52 : (1 - q ^ 52) ≠ 0)
    (h53 : (1 - q ^ 53) ≠ 0)
    (h57 : (1 - q ^ 57) ≠ 0)
    (h58 : (1 - q ^ 58) ≠ 0)
    (h62 : (1 - q ^ 62) ≠ 0)
    (h63 : (1 - q ^ 63) ≠ 0)
    (h67 : (1 - q ^ 67) ≠ 0)
    (h68 : (1 - q ^ 68) ≠ 0)
    (h72 : (1 - q ^ 72) ≠ 0)
    (h73 : (1 - q ^ 73) ≠ 0)
    :
    rogersRamanujanRHSTrunc q 1 15 =
      1 / ((1 - q ^ 73) * (1 - q ^ 72) * (1 - q ^ 68) * (1 - q ^ 67) *
           (1 - q ^ 63) * (1 - q ^ 62) * (1 - q ^ 58) * (1 - q ^ 57) *
           (1 - q ^ 53) * (1 - q ^ 52) * (1 - q ^ 48) * (1 - q ^ 47) *
           (1 - q ^ 43) * (1 - q ^ 42) * (1 - q ^ 38) * (1 - q ^ 37) *
           (1 - q ^ 33) * (1 - q ^ 32) * (1 - q ^ 28) * (1 - q ^ 27) *
           (1 - q ^ 23) * (1 - q ^ 22) * (1 - q ^ 18) * (1 - q ^ 17) *
           (1 - q ^ 13) * (1 - q ^ 12) * (1 - q ^ 8) * (1 - q ^ 7) *
           (1 - q ^ 3) * (1 - q ^ 2)) := by
  simp [rogersRamanujanRHSTrunc]
  field_simp [h2, h3, h7, h8, h12, h13, h17, h18, h22, h23, h27, h28, h32, h33, h37, h38, h42, h43, h47, h48, h52, h53, h57, h58, h62, h63, h67, h68, h72, h73]


/-! ### Theorem 7.3 — The a-deformed Rogers-Ramanujan identity (Chan Eq. 7.4)

The exponent `λ(r) = r(5r+1)/2` (Chan Eq. 7.5) and the function
`C_r(a) = 1 / ((q)_1 (q)_2 ⋯ (q)_r (aq^r)(aq^{r+1})⋯)`
(Chan Eq. 7.6). Theorem 7.3 states:
  `∑_{n≥0} q^{n²+(1-m)n} a^n / (q)_n
     = ∑_{r≥0} (-1)^r a^{2r} q^{λ(r)-mr} (1 - a^m q^{2mr}) C_r(a)`.
Setting `m = 2, a = q` recovers the first Rogers-Ramanujan identity. -/

/-- The pentagonal exponent `λ(r) = r(5r+1)/2` from Chan Eq. (7.5). -/
def lambdaRR (r : Nat) : Nat := r * (5 * r + 1) / 2

theorem lambdaRR_zero : lambdaRR 0 = 0 := by simp [lambdaRR]
theorem lambdaRR_one : lambdaRR 1 = 3 := by simp [lambdaRR]
theorem lambdaRR_two : lambdaRR 2 = 11 := by simp [lambdaRR]
theorem lambdaRR_three : lambdaRR 3 = 24 := by simp [lambdaRR]

/-- The auxiliary function `C_r(a)` from Chan Eq. (7.6):
`C_r(a) = 1 / ((q;q)_r · (aq^r; q)_∞)`.
Finite truncation: `C_r(a, N) = 1 / ((q;q)_r · (aq;q)_{N})` for large `N`.
Here we define just the finite version with explicit denominator. -/
noncomputable def crTrunc (a q : R) (r N : Nat) : R :=
  1 / (qPochhammer q r * qPoch (a * q ^ r) q N)

theorem crTrunc_zero (a q : R) (N : Nat) :
    crTrunc a q 0 N = 1 / qPoch a q N := by
  simp [crTrunc, qPochhammer]

/-- The `ε` operator from Chan Def. 7.1: `ε f(a) = f(aq)`.
This is a shift operator on the variable `a`. -/
noncomputable def epsilonShift (f : R → R) (q : R) (a : R) : R := f (a * q)

theorem epsilonShift_pow (q a : R) (n : Nat) :
    epsilonShift (fun x => x ^ n) q a = (a * q) ^ n := rfl

/-- The key property of `C_r(a)` under the ε-shift (Chan Eq. 7.7):
`ε C_r(a) = (1 - ax^r) C_r(a)` holds at the truncated level. This
connects `C_r(aq)` to `(1 - a·q^r) · C_r(a)`. -/
theorem crTrunc_shift (a q : R) (r N : Nat)
    (hd : qPochhammer q r * qPoch (a * q * q ^ r) q N ≠ 0)
    (hd' : qPochhammer q r * qPoch (a * q ^ r) q (N + 1) ≠ 0) :
    crTrunc (a * q) q r N =
      (1 - a * q ^ r) * crTrunc a q r (N + 1) := by
  have hshift : qPoch (a * q ^ r) q (N + 1) = (1 - a * q ^ r) * qPoch (a * q ^ r * q) q N := by
    clear hd hd'
    induction N with
    | zero => simp [qPoch]
    | succ N ih => rw [qPoch_succ, ih, qPoch_succ]; ring
  simp only [crTrunc]
  rw [show a * q * q ^ r = a * q ^ r * q from by ring, hshift]
  have haqr : (1 : R) - a * q ^ r ≠ 0 := by
    intro h; apply hd'; rw [hshift]; simp [h]
  have hqp : qPoch (a * q ^ r * q) q N ≠ 0 := by
    intro h; apply hd
    rw [show a * q * q ^ r = a * q ^ r * q from by ring]; simp [h]
  have hqph : qPochhammer q r ≠ 0 := by intro h; apply hd'; simp [h]
  field_simp [haqr, hqp, hqph]

/-! ### Rogers-Ramanujan functional equation (Chan §7.1)

The generalized Rogers-Ramanujan function is
`J(x, q, N) = ∑_{n=0}^N x^n q^{n²} / (q;q)_n`.

The key functional equation is  `J(x) - J(xq) = xq · J(xq², N-1)`,
which holds termwise because `x^n q^{n²} (1 - q^n) / (q;q)_n`
telescopes via `(1 - q^n) / (q;q)_n = 1 / (q;q)_{n-1}`. -/

noncomputable def rrJ (x q : R) : Nat → R
  | 0 => 1
  | Nat.succ n => rrJ x q n + x ^ (n + 1) * q ^ ((n + 1) * (n + 1)) / qPochhammer q (n + 1)

theorem rrJ_zero (x q : R) : rrJ x q 0 = 1 := rfl

theorem rrJ_succ (x q : R) (n : Nat) :
    rrJ x q (n + 1) = rrJ x q n + x ^ (n + 1) * q ^ ((n + 1) * (n + 1)) / qPochhammer q (n + 1) :=
  rfl

theorem rrJ_eq_natSum (x q : R) (N : Nat) :
    rrJ x q N = natSum (fun n => x ^ n * q ^ (n * n) / qPochhammer q n) N := by
  induction N with
  | zero => simp [rrJ, natSum, qPochhammer]
  | succ N ih => simp [rrJ_succ, natSum_succ, ih]

theorem rrJ_connects_to_lhsTrunc (q : R) (a N : Nat) :
    rogersRamanujanLHSTrunc q a N = natSum (fun n => q ^ (n * n + a * n) / qPochhammer q n) N := by
  rfl

theorem rrJ_one_eq_lhsTrunc_zero (q : R) (N : Nat) :
    rrJ 1 q N = rogersRamanujanLHSTrunc q 0 N := by
  rw [rrJ_eq_natSum, rogersRamanujanLHSTrunc]
  congr 1; ext n; simp

theorem rrJ_q_eq_lhsTrunc_one (q : R) (N : Nat) :
    rrJ q q N = rogersRamanujanLHSTrunc q 1 N := by
  rw [rrJ_eq_natSum, rogersRamanujanLHSTrunc]
  congr 1; ext n
  simp [pow_add, pow_mul, mul_div_assoc]
  ring

noncomputable def rrJTermDiff (x q : R) (n : Nat) : R :=
  x ^ n * q ^ (n * n) / qPochhammer q n - (x * q) ^ n * q ^ (n * n) / qPochhammer q n

theorem rrJTermDiff_zero (x q : R) : rrJTermDiff x q 0 = 0 := by
  simp [rrJTermDiff, qPochhammer]

theorem rrJTermDiff_eq (x q : R) (n : Nat) :
    rrJTermDiff x q n = x ^ n * q ^ (n * n) * (1 - q ^ n) / qPochhammer q n := by
  simp [rrJTermDiff, mul_pow]
  ring

theorem rrJTermDiff_succ_eq (x q : R) (n : Nat) (hq : qPochhammer q (n + 1) ≠ 0) :
    rrJTermDiff x q (n + 1) =
      x ^ (n + 1) * q ^ ((n + 1) * (n + 1)) / qPochhammer q n := by
  rw [rrJTermDiff_eq]
  rw [qPochhammer_succ]
  have hqn : qPochhammer q n ≠ 0 := by
    intro h; apply hq; simp [qPochhammer_succ, h]
  have hqn1 : (1 : R) - q ^ (n + 1) ≠ 0 := by
    intro h; apply hq; simp [qPochhammer_succ, h, mul_comm]
  field_simp [hqn, hqn1]

noncomputable def rrJShiftedTerm (x q : R) (n : Nat) : R :=
  x ^ (n + 1) * q ^ ((n + 1) * (n + 1)) / qPochhammer q n

theorem rrJShiftedTerm_eq_xq_times (x q : R) (n : Nat) :
    rrJShiftedTerm x q n =
      x * q * ((x * q ^ 2) ^ n * q ^ (n * n) / qPochhammer q n) := by
  simp [rrJShiftedTerm]
  ring

theorem rrJ_functional_eq_terms (x q : R) (n : Nat) (hq : qPochhammer q (n + 1) ≠ 0) :
    rrJTermDiff x q (n + 1) = x * q * ((x * q ^ 2) ^ n * q ^ (n * n) / qPochhammer q n) := by
  rw [rrJTermDiff_succ_eq x q n hq]
  ring

/-! The finite functional equation:
`rrJ x q (N+1) - rrJ (x*q) q (N+1) = x*q * rrJ (x*q²) q N`

under appropriate nonvanishing of `(q;q)_n` for `n ≤ N+1`. -/

theorem rrJ_functional_eq_zero (x q : R) (h1 : (1 : R) - q ≠ 0) :
    rrJ x q 1 - rrJ (x * q) q 1 = x * q * rrJ (x * q ^ 2) q 0 := by
  simp [rrJ, qPochhammer]
  field_simp [h1]

theorem rrJ_functional_eq_one (x q : R)
    (h1 : (1 : R) - q ≠ 0) (h2 : (1 : R) - q ^ 2 ≠ 0) :
    rrJ x q 2 - rrJ (x * q) q 2 = x * q * rrJ (x * q ^ 2) q 1 := by
  simp [rrJ, qPochhammer]
  field_simp [h1, h2]
  ring

theorem rrJ_functional_eq_two (x q : R)
    (h1 : (1 : R) - q ≠ 0) (h2 : (1 : R) - q ^ 2 ≠ 0)
    (h3 : (1 : R) - q ^ 3 ≠ 0) :
    rrJ x q 3 - rrJ (x * q) q 3 = x * q * rrJ (x * q ^ 2) q 2 := by
  simp [rrJ, qPochhammer]
  field_simp [h1, h2, h3]
  ring

/-! #### General functional equation by induction

The finite functional equation `J(x, N+1) - J(xq, N+1) = xq · J(xq², N)`
holds for all `N` under nonvanishing of `(q;q)_m` for `m ≤ N+1`. -/

theorem rrJ_succ_diff (x q : R) (N : Nat) :
    rrJ x q (N + 1) - rrJ (x * q) q (N + 1) =
      (rrJ x q N - rrJ (x * q) q N) +
      (x ^ (N + 1) * q ^ ((N + 1) * (N + 1)) / qPochhammer q (N + 1) -
       (x * q) ^ (N + 1) * q ^ ((N + 1) * (N + 1)) / qPochhammer q (N + 1)) := by
  simp [rrJ_succ]; ring

theorem rrJTermDiff_succ_eq_xq_shifted (x q : R) (N : Nat) (hq : qPochhammer q (N + 1) ≠ 0) :
    x ^ (N + 1) * q ^ ((N + 1) * (N + 1)) / qPochhammer q (N + 1) -
    (x * q) ^ (N + 1) * q ^ ((N + 1) * (N + 1)) / qPochhammer q (N + 1) =
      x * q * ((x * q ^ 2) ^ N * q ^ (N * N) / qPochhammer q N) := by
  have h := rrJ_functional_eq_terms x q N hq
  simp only [rrJTermDiff] at h
  exact h

theorem rrJ_functional_eq (x q : R) (N : Nat) (hq : ∀ m, m ≤ N + 1 → qPochhammer q m ≠ 0) :
    rrJ x q (N + 1) - rrJ (x * q) q (N + 1) = x * q * rrJ (x * q ^ 2) q N := by
  induction N with
  | zero =>
    simp [rrJ, qPochhammer]
    have h1 : (1 : R) - q ≠ 0 := by
      have := hq 1 (by omega)
      simpa [qPochhammer] using this
    field_simp [h1]
  | succ N ih =>
    rw [rrJ_succ_diff]
    have hq_prev : ∀ m, m ≤ N + 1 → qPochhammer q m ≠ 0 :=
      fun m hm => hq m (by omega)
    rw [ih hq_prev]
    rw [rrJTermDiff_succ_eq_xq_shifted x q (N + 1) (hq (N + 2) (by omega))]
    rw [rrJ_succ (x * q ^ 2) q N]
    ring

/-- Rogers–Ramanujan finite functional equation specialised to the
existing `rogersRamanujanLHSTrunc` truncations: at `x = 1` the LHS
of the rrJ functional equation is the parameter-`a = 0` truncation,
and `rrJ q q` is the parameter-`a = 1` truncation. -/
theorem rogersRamanujanLHSTrunc_functional_eq (q : R) (N : Nat)
    (hq : ∀ m, m ≤ N + 1 → qPochhammer q m ≠ 0) :
    rogersRamanujanLHSTrunc q 0 (N + 1) -
      rogersRamanujanLHSTrunc q 1 (N + 1) =
        q * rrJ (q ^ 2) q N := by
  rw [← rrJ_one_eq_lhsTrunc_zero, ← rrJ_q_eq_lhsTrunc_one]
  have hfe := rrJ_functional_eq 1 q N hq
  simpa using hfe

end Field

/-! ### Infinite Rogers-Ramanujan series: convergence infrastructure

For complex `q` with `‖q‖ < 1`, the finite q-Pochhammer `(q;q)_n` is nonzero,
and the terms `x^n q^{n²} / (q;q)_n` decay super-exponentially. -/

section Complex

open scoped Topology
open Filter

/-- Each factor `(1 - q^{k+1})` is nonzero when `‖q‖ < 1`. -/
theorem one_sub_pow_ne_zero_of_norm_lt_one (q : ℂ) (hq : ‖q‖ < 1) (k : ℕ) :
    (1 : ℂ) - q ^ (k + 1) ≠ 0 := by
  have hne : q ^ (k + 1) ≠ 1 := by
    intro heq
    have h1 : ‖q ^ (k + 1)‖ = 1 := by rw [heq]; simp
    rw [norm_pow] at h1
    have h2 : ‖q‖ ^ (k + 1) < 1 := by
      calc ‖q‖ ^ (k + 1) ≤ ‖q‖ ^ 1 := by
            apply pow_le_pow_of_le_one (norm_nonneg q) hq.le (by omega)
          _ < 1 := by simpa using hq
    linarith
  exact sub_ne_zero.mpr (Ne.symm hne)

/-- The finite q-Pochhammer symbol `(q;q)_n` is nonzero when `‖q‖ < 1`. -/
theorem qPochhammer_ne_zero_of_norm_lt_one (q : ℂ) (hq : ‖q‖ < 1) (n : ℕ) :
    qPochhammer q n ≠ 0 := by
  induction n with
  | zero => simp [qPochhammer]
  | succ n ih =>
    rw [qPochhammer_succ]
    exact mul_ne_zero ih (one_sub_pow_ne_zero_of_norm_lt_one q hq n)

/-- `‖(q;q)_n‖ > 0` when `‖q‖ < 1`. -/
theorem norm_qPochhammer_pos (q : ℂ) (hq : ‖q‖ < 1) (n : ℕ) :
    (0 : ℝ) < ‖qPochhammer q n‖ :=
  norm_pos_iff.mpr (qPochhammer_ne_zero_of_norm_lt_one q hq n)

/-- `rrJ 0 q N = 1` for all `N`: at `x = 0`, only the `n = 0` term survives. -/
theorem rrJ_at_zero (q : ℂ) (N : ℕ) : rrJ (0 : ℂ) q N = 1 := by
  induction N with
  | zero => rfl
  | succ N ih => simp [rrJ_succ, ih]

/-- The hypothesis `∀ m ≤ N+1, qPochhammer q m ≠ 0` is automatic for `‖q‖ < 1`. -/
theorem qPochhammer_all_ne_zero_of_norm_lt_one (q : ℂ) (hq : ‖q‖ < 1) (N : ℕ) :
    ∀ m, m ≤ N + 1 → qPochhammer q m ≠ 0 :=
  fun m _ => qPochhammer_ne_zero_of_norm_lt_one q hq m

/-- The finite functional equation for `‖q‖ < 1` with no explicit nonvanishing hypotheses. -/
theorem rrJ_functional_eq_complex (x q : ℂ) (hq : ‖q‖ < 1) (N : ℕ) :
    rrJ x q (N + 1) - rrJ (x * q) q (N + 1) = x * q * rrJ (x * q ^ 2) q N :=
  rrJ_functional_eq x q N (qPochhammer_all_ne_zero_of_norm_lt_one q hq N)

/-- Rearranged functional equation: `J(x, N+1) = J(xq, N+1) + xq · J(xq², N)`. -/
theorem rrJ_eq_shift_add (x q : ℂ) (hq : ‖q‖ < 1) (N : ℕ) :
    rrJ x q (N + 1) =
      rrJ (x * q) q (N + 1) + x * q * rrJ (x * q ^ 2) q N := by
  have h := rrJ_functional_eq_complex x q hq N; linear_combination h

/-- Ratio form: `J(x, N+1) / J(xq², N) = J(xq, N+1) / J(xq², N) + xq`. -/
theorem rrJ_ratio_eq (x q : ℂ) (hq : ‖q‖ < 1) (N : ℕ)
    (hJ : rrJ (x * q ^ 2) q N ≠ 0) :
    rrJ x q (N + 1) / rrJ (x * q ^ 2) q N =
      rrJ (x * q) q (N + 1) / rrJ (x * q ^ 2) q N + x * q := by
  have h := rrJ_eq_shift_add x q hq N
  rw [h, add_div, mul_div_cancel_right₀ _ hJ]

/-- Lower bound on each q-Pochhammer factor: `‖1 - q^(k+1)‖ ≥ 1 - ‖q‖`. -/
theorem norm_one_sub_pow_ge (q : ℂ) (hq : ‖q‖ < 1) (k : ℕ) :
    1 - ‖q‖ ≤ ‖(1 : ℂ) - q ^ (k + 1)‖ := by
  have hqk : ‖q‖ ^ (k + 1) ≤ ‖q‖ := by
    calc ‖q‖ ^ (k + 1) ≤ ‖q‖ ^ 1 :=
          pow_le_pow_of_le_one (norm_nonneg q) hq.le (by omega)
      _ = ‖q‖ := pow_one _
  calc 1 - ‖q‖ ≤ 1 - ‖q‖ ^ (k + 1) := by linarith
    _ = ‖(1 : ℂ)‖ - ‖q ^ (k + 1)‖ := by simp [norm_pow]
    _ ≤ ‖(1 : ℂ) - q ^ (k + 1)‖ := norm_sub_norm_le 1 (q ^ (k + 1))

/-- Lower bound on q-Pochhammer norm: `‖(q;q)_n‖ ≥ (1 - ‖q‖)^n`. -/
theorem norm_qPochhammer_ge (q : ℂ) (hq : ‖q‖ < 1) (n : ℕ) :
    (1 - ‖q‖) ^ n ≤ ‖qPochhammer q n‖ := by
  induction n with
  | zero => simp [qPochhammer]
  | succ n ih =>
    rw [qPochhammer_succ, norm_mul, pow_succ]
    exact mul_le_mul ih (norm_one_sub_pow_ge q hq n) (by linarith) (by positivity)

/-- The `n`-th term of J(x,q): `x^n * q^{n²} / (q;q)_n`. -/
noncomputable def rrJTerm (x q : ℂ) (n : ℕ) : ℂ :=
  x ^ n * q ^ (n * n) / qPochhammer q n

/-- The terms of J(x,q) are summable for `‖q‖ < 1`. -/
theorem summable_rrJTerm (x q : ℂ) (hq : ‖q‖ < 1) :
    Summable (rrJTerm x q) := by
  have h1q : (0 : ℝ) < 1 - ‖q‖ := by linarith
  set C := ‖x‖ / (1 - ‖q‖) with hC_def
  have hC_nn : 0 ≤ C := div_nonneg (norm_nonneg x) h1q.le
  have hqtend : Tendsto (fun n : ℕ => C * ‖q‖ ^ n) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg q) hq)
  obtain ⟨N₀, hN₀⟩ : ∃ N₀, ∀ n ≥ N₀, C * ‖q‖ ^ n < 1 / 2 :=
    (hqtend.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).exists_forall_of_atTop
  have hgeom : Summable fun n : ℕ => ((1 : ℝ) / 2) ^ n :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  exact hgeom.of_norm_bounded_eventually_nat (by
    rw [Filter.eventually_atTop]
    refine ⟨N₀, fun n hn => ?_⟩
    have hqn_bound : C * ‖q‖ ^ n < 1 / 2 := hN₀ n hn
    have hden_ge : (1 - ‖q‖) ^ n ≤ ‖qPochhammer q n‖ := norm_qPochhammer_ge q hq n
    simp only [rrJTerm, norm_div, norm_mul, norm_pow]
    calc ‖x‖ ^ n * ‖q‖ ^ (n * n) / ‖qPochhammer q n‖
        ≤ ‖x‖ ^ n * ‖q‖ ^ (n * n) / (1 - ‖q‖) ^ n := by
          exact div_le_div_of_nonneg_left (by positivity) (by positivity) hden_ge
      _ = C ^ n * ‖q‖ ^ (n * n) := by rw [hC_def, div_pow]; ring
      _ = (C * ‖q‖ ^ n) ^ n := by rw [mul_pow]; ring_nf
      _ ≤ (1 / 2) ^ n := pow_le_pow_left₀ (by positivity) (le_of_lt hqn_bound) n)

/-- The infinite Rogers-Ramanujan series `J(x, q) = ∑_{n≥0} x^n q^{n²} / (q;q)_n`. -/
noncomputable def rrJInf (x q : ℂ) : ℂ := ∑' n, rrJTerm x q n

/-- `rrJTerm` agrees with the summand in the finite `rrJ`. -/
theorem rrJTerm_eq (x q : ℂ) (n : ℕ) :
    rrJTerm x q n = x ^ n * q ^ (n * n) / qPochhammer q n := rfl

/-- `rrJ x q N` has a `HasSum` that converges to `rrJInf`. -/
theorem hasSum_rrJTerm (x q : ℂ) (hq : ‖q‖ < 1) :
    HasSum (rrJTerm x q) (rrJInf x q) := by
  exact (summable_rrJTerm x q hq).hasSum

/-- Termwise FE over ℂ: `rrJTermDiff x q (n+1) = x*q * rrJTerm (x*q²) q n`. -/
theorem rrJTermDiff_succ_eq_xq_rrJTerm (x q : ℂ) (hq : ‖q‖ < 1) (n : ℕ) :
    rrJTermDiff x q (n + 1) = x * q * rrJTerm (x * q ^ 2) q n := by
  have hqn := qPochhammer_ne_zero_of_norm_lt_one q hq (n + 1)
  rw [rrJ_functional_eq_terms x q n hqn]
  simp [rrJTerm]

/-- The rrJTermDiff equals the difference of rrJTerms. -/
theorem rrJTermDiff_eq_sub (x q : ℂ) (n : ℕ) :
    rrJTermDiff x q n = rrJTerm x q n - rrJTerm (x * q) q n := by
  simp [rrJTerm, rrJTermDiff, mul_pow]

/-- The termwise difference is summable. -/
theorem summable_rrJTermDiff (x q : ℂ) (hq : ‖q‖ < 1) :
    Summable (fun n => rrJTermDiff x q n) := by
  have heq : (fun n => rrJTermDiff x q n) = (fun n => rrJTerm x q n - rrJTerm (x * q) q n) := by
    ext n; exact rrJTermDiff_eq_sub x q n
  rw [heq]
  exact (summable_rrJTerm x q hq).sub (summable_rrJTerm (x * q) q hq)

/-- Infinite functional equation:
`J(x, q) - J(xq, q) = xq · J(xq², q)`.

Proved by decomposing the tsum of termwise differences:
`∑' n, diff(n) = diff(0) + ∑' n, diff(n+1) = 0 + xq · ∑' n, rrJTerm(xq², n)`. -/
theorem rrJInf_functional_eq (x q : ℂ) (hq : ‖q‖ < 1) :
    rrJInf x q - rrJInf (x * q) q = x * q * rrJInf (x * q ^ 2) q := by
  simp only [rrJInf]
  rw [← (summable_rrJTerm x q hq).tsum_sub (summable_rrJTerm (x * q) q hq)]
  have hdiff : (fun n => rrJTerm x q n - rrJTerm (x * q) q n) =
      (fun n => rrJTermDiff x q n) := by
    ext n; exact (rrJTermDiff_eq_sub x q n).symm
  rw [hdiff, (summable_rrJTermDiff x q hq).tsum_eq_zero_add]
  simp [rrJTermDiff_zero]
  rw [show (fun n => rrJTermDiff x q (n + 1)) =
      (fun n => x * q * rrJTerm (x * q ^ 2) q n) from by
    ext n; exact rrJTermDiff_succ_eq_xq_rrJTerm x q hq n]
  rw [tsum_mul_left]

/-- Bridge: `natSum f N = ∑ n in Finset.range (N+1), f n`. -/
private theorem natSum_eq_sum_range' (f : ℕ → ℂ) (N : ℕ) :
    natSum f N = ∑ n ∈ Finset.range (N + 1), f n := by
  induction N with
  | zero => simp [natSum]
  | succ N ih => simp [natSum, ih, Finset.sum_range_succ]

/-- The finite `rrJ x q N` converges to `rrJInf x q` as `N → ∞`. -/
theorem tendsto_rrJ (x q : ℂ) (hq : ‖q‖ < 1) :
    Tendsto (fun N => rrJ x q N) atTop (𝓝 (rrJInf x q)) := by
  have hhs := (hasSum_rrJTerm x q hq).tendsto_sum_nat
  have hshift : Tendsto (· + 1 : ℕ → ℕ) atTop atTop :=
    tendsto_atTop_atTop.mpr (fun n => ⟨n, fun m hm => by omega⟩)
  have hcomp := hhs.comp hshift
  simp only [Function.comp_def] at hcomp
  refine hcomp.congr (fun N => ?_)
  rw [rrJ_eq_natSum]
  exact (natSum_eq_sum_range' _ N).symm

/-- The truncated G function `rogersRamanujanLHSTrunc q 0 N` converges to `rrJInf 1 q`. -/
theorem tendsto_rrLHSTrunc_zero (q : ℂ) (hq : ‖q‖ < 1) :
    Tendsto (rogersRamanujanLHSTrunc q 0) atTop (𝓝 (rrJInf 1 q)) := by
  have : rogersRamanujanLHSTrunc q 0 = rrJ 1 q := by
    ext N; exact (rrJ_one_eq_lhsTrunc_zero q N).symm
  rw [this]; exact tendsto_rrJ 1 q hq

/-- The truncated H function `rogersRamanujanLHSTrunc q 1 N` converges to `rrJInf q q`. -/
theorem tendsto_rrLHSTrunc_one (q : ℂ) (hq : ‖q‖ < 1) :
    Tendsto (rogersRamanujanLHSTrunc q 1) atTop (𝓝 (rrJInf q q)) := by
  have : rogersRamanujanLHSTrunc q 1 = rrJ q q := by
    ext N; exact (rrJ_q_eq_lhsTrunc_one q N).symm
  rw [this]; exact tendsto_rrJ q q hq

/-- `J(0, q) = 1`. -/
theorem rrJInf_zero (q : ℂ) (_hq : ‖q‖ < 1) : rrJInf 0 q = 1 := by
  simp only [rrJInf]
  have : (fun n => rrJTerm 0 q n) = (fun n => if n = 0 then (1 : ℂ) else 0) := by
    ext n; cases n with
    | zero => simp [rrJTerm, qPochhammer]
    | succ n => simp [rrJTerm]
  rw [this, tsum_ite_eq]

/-- Rearranged infinite FE: `J(x,q) = J(xq,q) + xq · J(xq²,q)`. -/
theorem rrJInf_eq_shift_add (x q : ℂ) (hq : ‖q‖ < 1) :
    rrJInf x q = rrJInf (x * q) q + x * q * rrJInf (x * q ^ 2) q := by
  have h := rrJInf_functional_eq x q hq; linear_combination h

/-- `rrJInf x q` is nonzero when `x = 0` (it equals 1). -/
theorem rrJInf_ne_zero_at_zero (q : ℂ) (hq : ‖q‖ < 1) : rrJInf 0 q ≠ 0 := by
  rw [rrJInf_zero q hq]; exact one_ne_zero

/-- Infinite FE at `x = 1`: `J(1) - J(q) = q · J(q²)`. -/
theorem rrJInf_one_sub_q (q : ℂ) (hq : ‖q‖ < 1) :
    rrJInf 1 q - rrJInf q q = q * rrJInf (q ^ 2) q := by
  have h := rrJInf_functional_eq 1 q hq; simpa using h

/-- Infinite FE at `x = q`: `J(q) - J(q²) = q² · J(q³)`. -/
theorem rrJInf_q_sub_qsq (q : ℂ) (hq : ‖q‖ < 1) :
    rrJInf q q - rrJInf (q ^ 2) q = q ^ 2 * rrJInf (q ^ 3) q := by
  have h := rrJInf_functional_eq q q hq
  convert h using 1 <;> ring

/-- Infinite G - H = q · J(q²): the Rogers-Ramanujan sum-side relation. -/
theorem rrJInf_GH_diff (q : ℂ) (hq : ‖q‖ < 1) :
    rrJInf 1 q - rrJInf q q = q * rrJInf (q ^ 2) q :=
  rrJInf_one_sub_q q hq

/-- Specialization at `x = 1`: the finite functional equation gives
`G(N+1) - H(N+1) = q · J(q², N)` where `G = rogersRamanujanLHSTrunc q 0`
and `H = rogersRamanujanLHSTrunc q 1`. -/
theorem rogersRamanujan_GH_diff_complex (q : ℂ) (hq : ‖q‖ < 1) (N : ℕ) :
    rogersRamanujanLHSTrunc q 0 (N + 1) - rogersRamanujanLHSTrunc q 1 (N + 1) =
      q * rrJ (q ^ 2) q N :=
  rogersRamanujanLHSTrunc_functional_eq q N (qPochhammer_all_ne_zero_of_norm_lt_one q hq N)

/-- The Rogers-Ramanujan continued fraction ratio: when J(q) ≠ 0,
`J(1)/J(q) = 1 + q · J(q²)/J(q)`. -/
theorem rrJInf_ratio_one_q (q : ℂ) (hq : ‖q‖ < 1) (hJq : rrJInf q q ≠ 0) :
    rrJInf 1 q / rrJInf q q = 1 + q * (rrJInf (q ^ 2) q / rrJInf q q) := by
  have h := rrJInf_eq_shift_add 1 q hq
  simp at h
  rw [h, add_div, mul_div_assoc]
  simp [hJq]

/-- Iterated FE: `J(xq^{2k})` satisfies the recurrence
`J(xq^{2k}) = J(xq^{2k+1}) + xq^{2k+1} · J(xq^{2k+2})`. -/
theorem rrJInf_iterate (x q : ℂ) (hq : ‖q‖ < 1) (k : ℕ) :
    rrJInf (x * q ^ (2 * k)) q =
      rrJInf (x * q ^ (2 * k + 1)) q +
        x * q ^ (2 * k + 1) * rrJInf (x * q ^ (2 * k + 2)) q := by
  have h := rrJInf_eq_shift_add (x * q ^ (2 * k)) q hq
  convert h using 1 <;> ring

/-- The Rogers-Ramanujan continued fraction ratio at x=1:
when `G = J(1,q)` and `H = J(q,q)`, `G/H = 1 + q·J(q²)/H`. -/
noncomputable def rogersRamanujanRatio (q : ℂ) : ℂ :=
  rrJInf q q / rrJInf 1 q

/-- The continued fraction ratio satisfies the FE-based recursion
when G ≠ 0. `R(q) = 1/(1 + q · R'(q))` where `R'` involves shifted J. -/
theorem rogersRamanujanRatio_functional_eq (q : ℂ) (hq : ‖q‖ < 1)
    (hG : rrJInf 1 q ≠ 0) :
    rogersRamanujanRatio q =
      rrJInf q q / (rrJInf q q + q * rrJInf (q ^ 2) q) := by
  simp only [rogersRamanujanRatio]
  rw [rrJInf_eq_shift_add 1 q hq]
  simp

/-- As `N → ∞`, the shifted argument `x · q^N → 0` for `‖q‖ < 1`. -/
theorem tendsto_shift_atTop_nhds_zero (x q : ℂ) (hq : ‖q‖ < 1) :
    Tendsto (fun N : ℕ => x * q ^ N) atTop (𝓝 0) := by
  have h_q_pow : Tendsto (fun N : ℕ => q ^ N) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq
  have := h_q_pow.const_mul x
  simpa using this

/-- Norm formula for rrJTerm. -/
theorem norm_rrJTerm_eq (x q : ℂ) (n : ℕ) :
    ‖rrJTerm x q n‖ = ‖x‖ ^ n * ‖q‖ ^ (n * n) / ‖qPochhammer q n‖ := by
  simp [rrJTerm, norm_pow]

/-- `rrJTerm 0 q n = 1` when `n = 0` and `0` otherwise. -/
theorem rrJTerm_zero_arg (q : ℂ) (n : ℕ) :
    rrJTerm 0 q n = if n = 0 then (1 : ℂ) else 0 := by
  cases n with
  | zero => simp [rrJTerm, qPochhammer]
  | succ n => simp [rrJTerm]

/-- For ‖y‖ ≤ 1 and n ≥ 1: `‖rrJTerm y q n‖ ≤ ‖y‖ · ‖rrJTerm 1 q n‖`. -/
theorem norm_rrJTerm_le_y_mul (y q : ℂ) (hy : ‖y‖ ≤ 1) (n : ℕ) (hn : 1 ≤ n) :
    ‖rrJTerm y q n‖ ≤ ‖y‖ * ‖rrJTerm 1 q n‖ := by
  rw [norm_rrJTerm_eq, norm_rrJTerm_eq]
  simp only [norm_one, one_pow, one_mul]
  have hy_nn : 0 ≤ ‖y‖ := norm_nonneg _
  have hq_nn : 0 ≤ ‖q‖ ^ (n * n) := pow_nonneg (norm_nonneg _) _
  have hpoch_nn : 0 ≤ ‖qPochhammer q n‖ := norm_nonneg _
  have hy_pow : ‖y‖ ^ n ≤ ‖y‖ := by
    rcases Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0) with ⟨k, rfl⟩
    rw [pow_succ]
    have hyk_le : ‖y‖ ^ k ≤ 1 := pow_le_one₀ hy_nn hy
    nlinarith
  rw [show ‖y‖ * (‖q‖ ^ (n * n) / ‖qPochhammer q n‖) =
      ‖y‖ * ‖q‖ ^ (n * n) / ‖qPochhammer q n‖ from by ring]
  apply div_le_div_of_nonneg_right _ hpoch_nn
  exact mul_le_mul_of_nonneg_right hy_pow hq_nn

/-- The norm of rrJTerm is summable. -/
theorem summable_norm_rrJTerm (x q : ℂ) (hq : ‖q‖ < 1) :
    Summable fun n : ℕ => ‖rrJTerm x q n‖ := by
  have h1q : (0 : ℝ) < 1 - ‖q‖ := by linarith
  set C := ‖x‖ / (1 - ‖q‖) with hC_def
  have hqtend : Tendsto (fun n : ℕ => C * ‖q‖ ^ n) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg q) hq)
  obtain ⟨N₀, hN₀⟩ : ∃ N₀, ∀ n ≥ N₀, C * ‖q‖ ^ n < 1 / 2 :=
    (hqtend.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).exists_forall_of_atTop
  have hgeom : Summable fun n : ℕ => ((1 : ℝ) / 2) ^ n :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  refine hgeom.of_norm_bounded_eventually_nat ?_
  rw [Filter.eventually_atTop]
  refine ⟨N₀, fun n hn => ?_⟩
  have hqn_bound : C * ‖q‖ ^ n < 1 / 2 := hN₀ n hn
  have hden_ge : (1 - ‖q‖) ^ n ≤ ‖qPochhammer q n‖ := norm_qPochhammer_ge q hq n
  have h_nn : 0 ≤ ‖rrJTerm x q n‖ := norm_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg h_nn, norm_rrJTerm_eq]
  calc ‖x‖ ^ n * ‖q‖ ^ (n * n) / ‖qPochhammer q n‖
      ≤ ‖x‖ ^ n * ‖q‖ ^ (n * n) / (1 - ‖q‖) ^ n := by
        exact div_le_div_of_nonneg_left (by positivity) (by positivity) hden_ge
    _ = C ^ n * ‖q‖ ^ (n * n) := by rw [hC_def, div_pow]; ring
    _ = (C * ‖q‖ ^ n) ^ n := by rw [mul_pow]; ring_nf
    _ ≤ (1 / 2) ^ n := pow_le_pow_left₀ (by positivity) (le_of_lt hqn_bound) n

/-- Bound `‖rrJInf y q - 1‖ ≤ ‖y‖ · C(q)` for `‖y‖ ≤ 1`. -/
theorem norm_rrJInf_sub_one_le (y q : ℂ) (hq : ‖q‖ < 1) (hy : ‖y‖ ≤ 1) :
    ‖rrJInf y q - 1‖ ≤
      ‖y‖ * ∑' n : ℕ, ‖rrJTerm 1 q (n + 1)‖ := by
  -- rrJInf y q - 1 = ∑'_{n≥1} rrJTerm y q n (since term 0 = 1).
  have h_hsum : HasSum (rrJTerm y q) (rrJInf y q) :=
    (summable_rrJTerm y q hq).hasSum
  have h_t0 : rrJTerm y q 0 = 1 := by simp [rrJTerm, qPochhammer]
  have h_shifted : HasSum (fun n : ℕ => rrJTerm y q (n + 1)) (rrJInf y q - 1) := by
    have := (hasSum_nat_add_iff' (f := rrJTerm y q) 1).mpr h_hsum
    simp [h_t0] at this
    exact this
  -- Take norm of both sides.
  have h_summable_shifted : Summable fun n : ℕ => ‖rrJTerm y q (n + 1)‖ :=
    (summable_norm_rrJTerm y q hq).comp_injective (i := fun n => n + 1)
      (fun a b h => Nat.add_right_cancel h)
  -- Triangle inequality.
  have h_norm_le : ‖rrJInf y q - 1‖ ≤ ∑' n : ℕ, ‖rrJTerm y q (n + 1)‖ :=
    h_shifted.tsum_eq ▸ (norm_tsum_le_tsum_norm h_summable_shifted)
  -- Bound each shifted term by ‖y‖ · ‖rrJTerm 1 q (n+1)‖.
  have h_summable_one_shifted : Summable fun n : ℕ => ‖rrJTerm 1 q (n + 1)‖ :=
    (summable_norm_rrJTerm 1 q hq).comp_injective (i := fun n => n + 1)
      (fun a b h => Nat.add_right_cancel h)
  have h_term_bound : ∀ n : ℕ, ‖rrJTerm y q (n + 1)‖ ≤ ‖y‖ * ‖rrJTerm 1 q (n + 1)‖ := by
    intro n
    exact norm_rrJTerm_le_y_mul y q hy (n + 1) (by omega)
  have h_tsum_bound :
      ∑' n : ℕ, ‖rrJTerm y q (n + 1)‖ ≤ ‖y‖ * ∑' n : ℕ, ‖rrJTerm 1 q (n + 1)‖ := by
    rw [← tsum_mul_left]
    exact h_summable_shifted.tsum_le_tsum h_term_bound (h_summable_one_shifted.mul_left _)
  linarith

/-- `rrJInf · q` is continuous at `0`: any sequence `y_N → 0` (eventually with ‖y_N‖≤1)
gives `rrJInf y_N q → 1`. -/
theorem tendsto_rrJInf_of_tendsto_zero (q : ℂ) (hq : ‖q‖ < 1)
    {y : ℕ → ℂ} (hy : Tendsto y atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => rrJInf (y N) q) atTop (𝓝 1) := by
  -- |rrJInf y q - 1| ≤ ‖y‖ · C(q), and ‖y_N‖ → 0.
  set C : ℝ := ∑' n : ℕ, ‖rrJTerm 1 q (n + 1)‖ with hC_def
  have hC_nn : 0 ≤ C := tsum_nonneg fun n => norm_nonneg _
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε' : 0 < ε / (C + 1) := by positivity
  rw [Metric.tendsto_atTop] at hy
  obtain ⟨N₁, hN₁⟩ := hy (min (ε / (C + 1)) 1) (by positivity)
  refine ⟨N₁, fun N hN => ?_⟩
  have hy_close : ‖y N‖ < min (ε / (C + 1)) 1 := by
    have := hN₁ N hN
    rwa [dist_zero_right] at this
  have hy_lt_eps : ‖y N‖ < ε / (C + 1) := lt_of_lt_of_le hy_close (min_le_left _ _)
  have hy_lt_one : ‖y N‖ < 1 := lt_of_lt_of_le hy_close (min_le_right _ _)
  have hy_le_one : ‖y N‖ ≤ 1 := hy_lt_one.le
  have h_bound := norm_rrJInf_sub_one_le (y N) q hq hy_le_one
  rw [dist_eq_norm]
  -- ‖rrJInf y N q - 1‖ ≤ ‖y N‖ · C < (ε/(C+1)) · (C+1) ≤ ε.
  calc ‖rrJInf (y N) q - 1‖
      ≤ ‖y N‖ * C := h_bound
    _ ≤ ‖y N‖ * (C + 1) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); linarith
    _ < (ε / (C + 1)) * (C + 1) := by
        apply mul_lt_mul_of_pos_right hy_lt_eps; linarith
    _ = ε := by
        field_simp

/-- The shifted `rrJInf (x · q^(N+1)) q → 1` as `N → ∞`. -/
theorem tendsto_rrJInf_shift (x q : ℂ) (hq : ‖q‖ < 1) :
    Tendsto (fun N : ℕ => rrJInf (x * q ^ (N + 1)) q) atTop (𝓝 1) := by
  have h_q_pow : Tendsto (fun N : ℕ => q ^ (N + 1)) atTop (𝓝 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq
    have h_shift : Tendsto (fun N : ℕ => N + 1) atTop atTop :=
      tendsto_atTop_mono (fun N => Nat.le_succ N) tendsto_id
    exact h.comp h_shift
  have h_shift : Tendsto (fun N : ℕ => x * q ^ (N + 1)) atTop (𝓝 0) := by
    have := h_q_pow.const_mul x
    simpa using this
  exact tendsto_rrJInf_of_tendsto_zero q hq h_shift

/-- Finite telescoping form of the functional equation:
`J(x) - J(xq^(N+1)) = ∑_{k=0}^{N} xq^(k+1) · J(xq^(k+2))`. -/
theorem rrJInf_telescope_finite (x q : ℂ) (hq : ‖q‖ < 1) (N : ℕ) :
    rrJInf x q - rrJInf (x * q ^ (N + 1)) q =
      (Finset.range (N + 1)).sum
        (fun k => x * q ^ (k + 1) * rrJInf (x * q ^ (k + 2)) q) := by
  induction N with
  | zero =>
    -- J(x) - J(xq) = xq · J(xq²).
    have h := rrJInf_functional_eq x q hq
    simp [pow_one]
    convert h using 2
  | succ N ih =>
    -- Telescope: split J(x) - J(xq^(N+2)) = [J(x) - J(xq^(N+1))] + [J(xq^(N+1)) - J(xq^(N+2))].
    have h_split :
        rrJInf x q - rrJInf (x * q ^ (N + 1 + 1)) q =
          (rrJInf x q - rrJInf (x * q ^ (N + 1)) q) +
            (rrJInf (x * q ^ (N + 1)) q - rrJInf (x * q ^ (N + 1 + 1)) q) := by
      ring
    rw [h_split, ih]
    -- FE at `x * q^(N+1)`.
    have h_FE := rrJInf_functional_eq (x * q ^ (N + 1)) q hq
    have h_pow1 : x * q ^ (N + 1) * q = x * q ^ (N + 1 + 1) := by ring
    have h_pow2 : x * q ^ (N + 1) * q ^ 2 = x * q ^ (N + 1 + 2) := by ring
    rw [h_pow1, h_pow2] at h_FE
    -- The second bracket = the new term.
    rw [h_FE]
    -- Expand both sides into (sum at N) + term_N + term_{N+1} form.
    simp only [Finset.sum_range_succ]

/-- The infinite telescoping form: partial sums tend to `J(x) - 1`. -/
theorem rrJInf_telescope_infinite (x q : ℂ) (hq : ‖q‖ < 1) :
    Tendsto
      (fun N : ℕ => (Finset.range (N + 1)).sum
        (fun k => x * q ^ (k + 1) * rrJInf (x * q ^ (k + 2)) q))
      atTop (𝓝 (rrJInf x q - 1)) := by
  have h_tele : ∀ N : ℕ,
      (Finset.range (N + 1)).sum
        (fun k => x * q ^ (k + 1) * rrJInf (x * q ^ (k + 2)) q) =
      rrJInf x q - rrJInf (x * q ^ (N + 1)) q := fun N =>
    (rrJInf_telescope_finite x q hq N).symm
  have h_target : Tendsto (fun N : ℕ => rrJInf x q - rrJInf (x * q ^ (N + 1)) q)
      atTop (𝓝 (rrJInf x q - 1)) := by
    have h_const : Tendsto (fun _ : ℕ => rrJInf x q) atTop (𝓝 (rrJInf x q)) :=
      tendsto_const_nhds
    have h_J1 := tendsto_rrJInf_shift x q hq
    have := h_const.sub h_J1
    simpa using this
  refine h_target.congr ?_
  intro N
  exact (h_tele N).symm

/-! ## Rogers-Ramanujan first identity — Step 4 (conditional on Step 1 reduction)

Given the **Step 1** sum-to-theta reduction (proved separately via Schur+Tannery),
we can derive the R-R first/second product form. This conditional theorem makes
the dependency explicit. -/

/-- R-R first identity given Step 1: `rrJInf 1 q · (q;q)_∞ = ∑'_j (-1)^j q^(j(5j+1)/2)`. -/
theorem rogersRamanujan_first_given_step1
    (q : ℂ) (hq : ‖q‖ < 1) (hq_ne : q ≠ 0)
    (h_step1 :
      rrJInf 1 q * PartI.Ch04.eulerPentagonalInfiniteProduct q =
        ∑' j : ℤ, (-1 : ℂ) ^ j * q ^ (j * (5 * j + 1) / 2)) :
    rrJInf 1 q * (∏' n : ℕ, PartI.Ch04.rrMod5Factor q 1 n) *
      (∏' n : ℕ, PartI.Ch04.rrMod5Factor q 4 n) = 1 := by
  -- LHS goal · (∏'·2)·(∏'·3)·(∏'·5) = rrJInf 1 q · (q;q)_∞ = ∑'_j ... = (∏'·5)·(∏'·3)·(∏'·2).
  -- Combined: rrJInf 1 q · (∏'·1)·(∏'·4) = 1.
  have h_step2 := PartI.Ch04.theta_sum_1_eq_mod5_product q hq hq_ne
  have h_step3 := PartI.Ch04.eulerPentagonalInfiniteProduct_eq_mod5_regroup q hq
  have h_ne5 := PartI.Ch04.tprod_rrMod5Factor_ne_zero q hq 5 (by norm_num)
  have h_ne3 := PartI.Ch04.tprod_rrMod5Factor_ne_zero q hq 3 (by norm_num)
  have h_ne2 := PartI.Ch04.tprod_rrMod5Factor_ne_zero q hq 2 (by norm_num)
  -- Substitute everything; multiply both sides by (∏'·2)·(∏'·3)·(∏'·5).
  have h_combined :
      rrJInf 1 q *
        ((∏' n, PartI.Ch04.rrMod5Factor q 1 n) *
         (∏' n, PartI.Ch04.rrMod5Factor q 2 n) *
         (∏' n, PartI.Ch04.rrMod5Factor q 3 n) *
         (∏' n, PartI.Ch04.rrMod5Factor q 4 n) *
         (∏' n, PartI.Ch04.rrMod5Factor q 5 n)) =
      (∏' n, PartI.Ch04.rrMod5Factor q 5 n) *
      (∏' n, PartI.Ch04.rrMod5Factor q 3 n) *
      (∏' n, PartI.Ch04.rrMod5Factor q 2 n) := by
    rw [show
        rrJInf 1 q *
          ((∏' n, PartI.Ch04.rrMod5Factor q 1 n) *
           (∏' n, PartI.Ch04.rrMod5Factor q 2 n) *
           (∏' n, PartI.Ch04.rrMod5Factor q 3 n) *
           (∏' n, PartI.Ch04.rrMod5Factor q 4 n) *
           (∏' n, PartI.Ch04.rrMod5Factor q 5 n)) =
        (rrJInf 1 q * PartI.Ch04.eulerPentagonalInfiniteProduct q) by
      rw [h_step3]]
    rw [h_step1, h_step2]
  -- From h_combined, cancel (∏'·2)·(∏'·3)·(∏'·5) on both sides.
  have h_factor :
      (∏' n, PartI.Ch04.rrMod5Factor q 2 n) *
      (∏' n, PartI.Ch04.rrMod5Factor q 3 n) *
      (∏' n, PartI.Ch04.rrMod5Factor q 5 n) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero h_ne2 h_ne3) h_ne5
  have h_simplified :
      rrJInf 1 q * (∏' n, PartI.Ch04.rrMod5Factor q 1 n) *
        (∏' n, PartI.Ch04.rrMod5Factor q 4 n) *
      ((∏' n, PartI.Ch04.rrMod5Factor q 2 n) *
       (∏' n, PartI.Ch04.rrMod5Factor q 3 n) *
       (∏' n, PartI.Ch04.rrMod5Factor q 5 n)) =
      (∏' n, PartI.Ch04.rrMod5Factor q 2 n) *
      (∏' n, PartI.Ch04.rrMod5Factor q 3 n) *
      (∏' n, PartI.Ch04.rrMod5Factor q 5 n) := by
    have := h_combined
    linear_combination this
  -- Cancel the nonzero factor.
  have := mul_right_cancel₀ h_factor (h_simplified.trans (one_mul _).symm)
  exact this

end Complex

end Ch07
end PartII
end QseriesFormalization
