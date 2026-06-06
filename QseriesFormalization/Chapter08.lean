import QseriesFormalization.Basic

/-!
# Chapter 8 — `D_n(q, a)` series

⚠️  **SHADOW CHAPTER**.

Per `PLAYBOOK_AUDIT.md` (2026-05-22): this file currently contains only the
finite truncation `D_partialSum q a N := ∑_{k=0}^N q^{k²+ak}/(q;q)_k` and
closed-form unfoldings `D_partialSum_zero..thirteen`.  Chan's Ch 8 main
identity for the `D_n(q, a)` series (the Bailey/Slater-type infinite-product
or theta-series representation as `N → ∞`) is **not** formalized here.

Until a real chapter-main theorem is added, this file is auxiliary
scaffolding only.
-/

namespace QseriesFormalization
namespace PartII
namespace Ch08

section Field

variable {R : Type*} [Field R]

/-- Partial-sum truncation for Chan Ch 8's `D_n(q, a)` series. -/
noncomputable def D_partialSum (q : R) (a : Nat) (N : Nat) : R :=
  natSum (fun n => q ^ (n * n + a * n) / qPochhammer q n) N

/-- N=0 sanity for the partial-sum truncation. -/
theorem D_partialSum_zero (q : R) (a : Nat) :
    D_partialSum q a 0 = 1 / qPochhammer q 0 := by
  simp [D_partialSum, natSum]

/-- Recursion: `D_partialSum q a (N+1) = D_partialSum q a N + (the new term)`.
This is the structural step that all the `D_partialSum_k` closed-form
theorems implicitly reuse; pulling it out lets later work avoid
re-expanding `natSum` for every truncation depth. -/
@[simp] theorem D_partialSum_succ (q : R) (a : Nat) (N : Nat) :
    D_partialSum q a (N + 1) =
      D_partialSum q a N +
      q ^ ((N + 1) * (N + 1) + a * (N + 1)) / qPochhammer q (N + 1) := by
  simp [D_partialSum]

/-- Truncated `D_N(q, a)` from Chan Ch 8, represented by its finite partial sum. -/
noncomputable def D_trunc (q : R) (a : Nat) (N : Nat) : R :=
  D_partialSum q a N

/-- N=0 sanity: D_trunc q a 0 = 1. -/
@[simp] theorem D_trunc_zero (q : R) (a : Nat) : D_trunc q a 0 = 1 := by
  simp [D_trunc, D_partialSum, natSum]

/-- Recursion for `D_trunc`, mirroring `D_partialSum_succ`. -/
theorem D_trunc_succ (q : R) (a : Nat) (N : Nat) :
    D_trunc q a (N + 1) =
      D_trunc q a N +
      q ^ ((N + 1) * (N + 1) + a * (N + 1)) / qPochhammer q (N + 1) := by
  simp [D_trunc]

/-- N=1 closed form for D_partialSum. -/
theorem D_partialSum_one (q : R) (a : Nat) :
    D_partialSum q a 1 = 1 + q ^ (1 + a) / (1 - q) := by
  simp [D_partialSum, natSum, qPochhammer]

/-- N=1 closed form for D_trunc. -/
theorem D_trunc_one (q : R) (a : Nat) :
    D_trunc q a 1 = 1 + q ^ (1 + a) / (1 - q) := by
  exact D_partialSum_one q a

/-- N=2 closed form for D_partialSum. -/
theorem D_partialSum_two (q : R) (a : Nat) :
    D_partialSum q a 2 =
      1 + q ^ (1 + a) / (1 - q) +
      q ^ (4 + 2 * a) / ((1 - q) * (1 - q ^ 2)) := by
  simp [D_partialSum, natSum, qPochhammer, Nat.mul_comm]

/-- N=2 closed form for D_trunc. -/
theorem D_trunc_two (q : R) (a : Nat) :
    D_trunc q a 2 =
      1 + q ^ (1 + a) / (1 - q) +
      q ^ (4 + 2 * a) / ((1 - q) * (1 - q ^ 2)) := by
  exact D_partialSum_two q a

/-- N=3 closed form for D_partialSum. -/
theorem D_partialSum_three (q : R) (a : Nat) :
    D_partialSum q a 3 =
      1 + q ^ (1 + a) / (1 - q) +
      q ^ (4 + 2 * a) / ((1 - q) * (1 - q ^ 2)) +
      q ^ (9 + 3 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3)) := by
  simp [D_partialSum, natSum, qPochhammer, Nat.mul_comm]

/-- N=3 closed form for D_trunc. -/
theorem D_trunc_three (q : R) (a : Nat) :
    D_trunc q a 3 =
      1 + q ^ (1 + a) / (1 - q) +
      q ^ (4 + 2 * a) / ((1 - q) * (1 - q ^ 2)) +
      q ^ (9 + 3 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3)) := by
  exact D_partialSum_three q a

/-- N=4 closed form for D_partialSum. -/
theorem D_partialSum_four (q : R) (a : Nat) :
    D_partialSum q a 4 =
      1 + q ^ (1 + a) / (1 - q) +
      q ^ (4 + 2 * a) / ((1 - q) * (1 - q ^ 2)) +
      q ^ (9 + 3 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3)) +
      q ^ (16 + 4 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4)) := by
  simp [D_partialSum, natSum, qPochhammer, Nat.mul_comm]

/-- N=4 closed form for D_trunc. -/
theorem D_trunc_four (q : R) (a : Nat) :
    D_trunc q a 4 = D_partialSum q a 4 := rfl

/-- N=5 closed form for D_partialSum. -/
theorem D_partialSum_five (q : R) (a : Nat) :
    D_partialSum q a 5 =
      1 + q ^ (1 + a) / (1 - q) +
      q ^ (4 + 2 * a) / ((1 - q) * (1 - q ^ 2)) +
      q ^ (9 + 3 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3)) +
      q ^ (16 + 4 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4)) +
      q ^ (25 + 5 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5)) := by
  simp [D_partialSum, natSum, qPochhammer, Nat.mul_comm]

/-- N=5 closed form for D_trunc. -/
theorem D_trunc_five (q : R) (a : Nat) :
    D_trunc q a 5 = D_partialSum q a 5 := rfl

/-- N=6 closed form for D_partialSum. -/
theorem D_partialSum_six (q : R) (a : Nat) :
    D_partialSum q a 6 =
      1 + q ^ (1 + a) / (1 - q) +
      q ^ (4 + 2 * a) / ((1 - q) * (1 - q ^ 2)) +
      q ^ (9 + 3 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3)) +
      q ^ (16 + 4 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4)) +
      q ^ (25 + 5 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5)) +
      q ^ (36 + 6 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6)) := by
  simp [D_partialSum, natSum, qPochhammer, Nat.mul_comm]

/-- N=6 closed form for D_trunc. -/
theorem D_trunc_six (q : R) (a : Nat) :
    D_trunc q a 6 = D_partialSum q a 6 := rfl

/-- N=7 closed form for D_partialSum. -/
theorem D_partialSum_seven (q : R) (a : Nat) :
    D_partialSum q a 7 =
      1 + q ^ (1 + a) / (1 - q) +
      q ^ (4 + 2 * a) / ((1 - q) * (1 - q ^ 2)) +
      q ^ (9 + 3 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3)) +
      q ^ (16 + 4 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4)) +
      q ^ (25 + 5 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5)) +
      q ^ (36 + 6 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6)) +
      q ^ (49 + 7 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7)) := by
  simp [D_partialSum, natSum, qPochhammer, Nat.mul_comm]

/-- N=7 closed form for D_trunc. -/
theorem D_trunc_seven (q : R) (a : Nat) :
    D_trunc q a 7 = D_partialSum q a 7 := rfl

/-- N=8 closed form for D_partialSum. -/
theorem D_partialSum_eight (q : R) (a : Nat) :
    D_partialSum q a 8 =
      1 + q ^ (1 + a) / (1 - q) +
      q ^ (4 + 2 * a) / ((1 - q) * (1 - q ^ 2)) +
      q ^ (9 + 3 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3)) +
      q ^ (16 + 4 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4)) +
      q ^ (25 + 5 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5)) +
      q ^ (36 + 6 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6)) +
      q ^ (49 + 7 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7)) +
      q ^ (64 + 8 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8)) := by
  simp [D_partialSum, natSum, qPochhammer, Nat.mul_comm]

/-- N=8 closed form for D_trunc. -/
theorem D_trunc_eight (q : R) (a : Nat) :
    D_trunc q a 8 = D_partialSum q a 8 := rfl

/-- N=9 closed form for D_partialSum. -/
theorem D_partialSum_nine (q : R) (a : Nat) :
    D_partialSum q a 9 =
      1 + q ^ (1 + a) / (1 - q) +
      q ^ (4 + 2 * a) / ((1 - q) * (1 - q ^ 2)) +
      q ^ (9 + 3 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3)) +
      q ^ (16 + 4 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4)) +
      q ^ (25 + 5 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5)) +
      q ^ (36 + 6 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6)) +
      q ^ (49 + 7 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7)) +
      q ^ (64 + 8 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8)) +
      q ^ (81 + 9 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9)) := by
  simp [D_partialSum, natSum, qPochhammer, Nat.mul_comm]

/-- N=9 closed form for D_trunc. -/
theorem D_trunc_nine (q : R) (a : Nat) :
    D_trunc q a 9 = D_partialSum q a 9 := rfl

/-- N=10 closed form for D_partialSum. -/
theorem D_partialSum_ten (q : R) (a : Nat) :
    D_partialSum q a 10 =
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
  simp [D_partialSum, natSum, qPochhammer, Nat.mul_comm]

/-- N=10 closed form for D_trunc. -/
theorem D_trunc_ten (q : R) (a : Nat) :
    D_trunc q a 10 = D_partialSum q a 10 := rfl

/-- N=11 closed form for D_partialSum. -/
theorem D_partialSum_eleven (q : R) (a : Nat) :
    D_partialSum q a 11 =
      1 + q ^ (1 + a) / (1 - q) +
      q ^ (4 + 2 * a) / ((1 - q) * (1 - q ^ 2)) +
      q ^ (9 + 3 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3)) +
      q ^ (16 + 4 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4)) +
      q ^ (25 + 5 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5)) +
      q ^ (36 + 6 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6)) +
      q ^ (49 + 7 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7)) +
      q ^ (64 + 8 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8)) +
      q ^ (81 + 9 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9)) +
      q ^ (100 + 10 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10)) +
      q ^ (121 + 11 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) * (1 - q ^ 11)) := by
  simp [D_partialSum, natSum, qPochhammer, Nat.mul_comm]

/-- N=11 closed form for D_trunc. -/
theorem D_trunc_eleven (q : R) (a : Nat) :
    D_trunc q a 11 = D_partialSum q a 11 := rfl

/-- N=12 closed form for D_partialSum. -/
theorem D_partialSum_twelve (q : R) (a : Nat) :
    D_partialSum q a 12 =
      1 + q ^ (1 + a) / (1 - q) +
      q ^ (4 + 2 * a) / ((1 - q) * (1 - q ^ 2)) +
      q ^ (9 + 3 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3)) +
      q ^ (16 + 4 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4)) +
      q ^ (25 + 5 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5)) +
      q ^ (36 + 6 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6)) +
      q ^ (49 + 7 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7)) +
      q ^ (64 + 8 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8)) +
      q ^ (81 + 9 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9)) +
      q ^ (100 + 10 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10)) +
      q ^ (121 + 11 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) * (1 - q ^ 11)) +
      q ^ (144 + 12 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) * (1 - q ^ 11) * (1 - q ^ 12)) := by
  simp [D_partialSum, natSum, qPochhammer, Nat.mul_comm]

/-- N=12 closed form for D_trunc. -/
theorem D_trunc_twelve (q : R) (a : Nat) :
    D_trunc q a 12 = D_partialSum q a 12 := rfl

/-- N=13 closed form for D_partialSum. -/
theorem D_partialSum_thirteen (q : R) (a : Nat) :
    D_partialSum q a 13 =
      1 + q ^ (1 + a) / (1 - q) +
      q ^ (4 + 2 * a) / ((1 - q) * (1 - q ^ 2)) +
      q ^ (9 + 3 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3)) +
      q ^ (16 + 4 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4)) +
      q ^ (25 + 5 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5)) +
      q ^ (36 + 6 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6)) +
      q ^ (49 + 7 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7)) +
      q ^ (64 + 8 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8)) +
      q ^ (81 + 9 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9)) +
      q ^ (100 + 10 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10)) +
      q ^ (121 + 11 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) * (1 - q ^ 11)) +
      q ^ (144 + 12 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) * (1 - q ^ 11) * (1 - q ^ 12)) +
      q ^ (169 + 13 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) * (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13)) := by
  simp [D_partialSum, natSum, qPochhammer, Nat.mul_comm]

/-- N=13 closed form for D_trunc. -/
theorem D_trunc_thirteen (q : R) (a : Nat) :
    D_trunc q a 13 = D_partialSum q a 13 := rfl

/-- N=14 closed form for D_partialSum. -/
theorem D_partialSum_fourteen (q : R) (a : Nat) :
    D_partialSum q a 14 =
      1 + q ^ (1 + a) / (1 - q) +
      q ^ (4 + 2 * a) / ((1 - q) * (1 - q ^ 2)) +
      q ^ (9 + 3 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3)) +
      q ^ (16 + 4 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4)) +
      q ^ (25 + 5 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5)) +
      q ^ (36 + 6 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6)) +
      q ^ (49 + 7 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7)) +
      q ^ (64 + 8 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8)) +
      q ^ (81 + 9 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9)) +
      q ^ (100 + 10 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10)) +
      q ^ (121 + 11 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) * (1 - q ^ 11)) +
      q ^ (144 + 12 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) * (1 - q ^ 11) * (1 - q ^ 12)) +
      q ^ (169 + 13 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) * (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13)) +
      q ^ (196 + 14 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) * (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14)) := by
  simp [D_partialSum, natSum, qPochhammer, Nat.mul_comm]

/-- N=14 closed form for D_trunc. -/
theorem D_trunc_fourteen (q : R) (a : Nat) :
    D_trunc q a 14 = D_partialSum q a 14 := rfl

/-- N=15 closed form for D_partialSum. -/
theorem D_partialSum_fifteen (q : R) (a : Nat) :
    D_partialSum q a 15 =
      1 + q ^ (1 + a) / (1 - q) +
      q ^ (4 + 2 * a) / ((1 - q) * (1 - q ^ 2)) +
      q ^ (9 + 3 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3)) +
      q ^ (16 + 4 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4)) +
      q ^ (25 + 5 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5)) +
      q ^ (36 + 6 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6)) +
      q ^ (49 + 7 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7)) +
      q ^ (64 + 8 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8)) +
      q ^ (81 + 9 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9)) +
      q ^ (100 + 10 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10)) +
      q ^ (121 + 11 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) * (1 - q ^ 11)) +
      q ^ (144 + 12 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) * (1 - q ^ 11) * (1 - q ^ 12)) +
      q ^ (169 + 13 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) * (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13)) +
      q ^ (196 + 14 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) * (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14)) +
      q ^ (225 + 15 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) * (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15)) := by
  simp [D_partialSum, natSum, qPochhammer, Nat.mul_comm]

/-- N=15 closed form for D_trunc. -/
theorem D_trunc_fifteen (q : R) (a : Nat) :
    D_trunc q a 15 = D_partialSum q a 15 := rfl

/-- N=16 closed form for D_partialSum. -/
theorem D_partialSum_sixteen (q : R) (a : Nat) :
    D_partialSum q a 16 =
      1 + q ^ (1 + a) / (1 - q) +
      q ^ (4 + 2 * a) / ((1 - q) * (1 - q ^ 2)) +
      q ^ (9 + 3 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3)) +
      q ^ (16 + 4 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4)) +
      q ^ (25 + 5 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5)) +
      q ^ (36 + 6 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6)) +
      q ^ (49 + 7 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7)) +
      q ^ (64 + 8 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8)) +
      q ^ (81 + 9 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9)) +
      q ^ (100 + 10 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10)) +
      q ^ (121 + 11 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) * (1 - q ^ 11)) +
      q ^ (144 + 12 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) * (1 - q ^ 11) * (1 - q ^ 12)) +
      q ^ (169 + 13 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) * (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13)) +
      q ^ (196 + 14 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) * (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14)) +
      q ^ (225 + 15 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) * (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15)) +
      q ^ (256 + 16 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) * (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) * (1 - q ^ 16)) := by
  simp [D_partialSum, natSum, qPochhammer, Nat.mul_comm]

/-- N=16 closed form for D_trunc. -/
theorem D_trunc_sixteen (q : R) (a : Nat) :
    D_trunc q a 16 = D_partialSum q a 16 := rfl

set_option maxHeartbeats 400000 in
/-- N=17 closed form for D_partialSum. -/
theorem D_partialSum_seventeen (q : R) (a : Nat) :
    D_partialSum q a 17 =
      1 + q ^ (1 + a) / (1 - q) +
      q ^ (4 + 2 * a) / ((1 - q) * (1 - q ^ 2)) +
      q ^ (9 + 3 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3)) +
      q ^ (16 + 4 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4)) +
      q ^ (25 + 5 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5)) +
      q ^ (36 + 6 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6)) +
      q ^ (49 + 7 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7)) +
      q ^ (64 + 8 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8)) +
      q ^ (81 + 9 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9)) +
      q ^ (100 + 10 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10)) +
      q ^ (121 + 11 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) * (1 - q ^ 11)) +
      q ^ (144 + 12 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) * (1 - q ^ 11) * (1 - q ^ 12)) +
      q ^ (169 + 13 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) * (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13)) +
      q ^ (196 + 14 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) * (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14)) +
      q ^ (225 + 15 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) * (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15)) +
      q ^ (256 + 16 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) * (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) * (1 - q ^ 16)) +
      q ^ (289 + 17 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) * (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) * (1 - q ^ 16) * (1 - q ^ 17)) := by
  simp [D_partialSum, natSum, qPochhammer, Nat.mul_comm]

/-- N=17 closed form for D_trunc. -/
theorem D_trunc_seventeen (q : R) (a : Nat) :
    D_trunc q a 17 = D_partialSum q a 17 := rfl

set_option maxHeartbeats 400000 in
/-- N=18 closed form for D_partialSum. -/
theorem D_partialSum_eighteen (q : R) (a : Nat) :
    D_partialSum q a 18 =
      1 + q ^ (1 + a) / (1 - q) +
      q ^ (4 + 2 * a) / ((1 - q) * (1 - q ^ 2)) +
      q ^ (9 + 3 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3)) +
      q ^ (16 + 4 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4)) +
      q ^ (25 + 5 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5)) +
      q ^ (36 + 6 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6)) +
      q ^ (49 + 7 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7)) +
      q ^ (64 + 8 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8)) +
      q ^ (81 + 9 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9)) +
      q ^ (100 + 10 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10)) +
      q ^ (121 + 11 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) * (1 - q ^ 11)) +
      q ^ (144 + 12 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) * (1 - q ^ 11) * (1 - q ^ 12)) +
      q ^ (169 + 13 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) * (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13)) +
      q ^ (196 + 14 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) * (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14)) +
      q ^ (225 + 15 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) * (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15)) +
      q ^ (256 + 16 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) * (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) * (1 - q ^ 16)) +
      q ^ (289 + 17 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) * (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) * (1 - q ^ 16) * (1 - q ^ 17)) +
      q ^ (324 + 18 * a) / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) * (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) * (1 - q ^ 16) * (1 - q ^ 17) * (1 - q ^ 18)) := by
  simp [D_partialSum, natSum, qPochhammer, Nat.mul_comm]

/-- N=18 closed form for D_trunc. -/
theorem D_trunc_eighteen (q : R) (a : Nat) :
    D_trunc q a 18 = D_partialSum q a 18 := rfl
end Field

end Ch08
end PartII
end QseriesFormalization
