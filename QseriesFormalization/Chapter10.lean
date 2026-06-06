import QseriesFormalization.Basic

/-!
# Chapter 10 — Ramanujan's mock theta `f(q)`

⚠️  **SHADOW CHAPTER**.

Per `PLAYBOOK_AUDIT.md` (2026-05-22): this file currently contains only the
finite truncation `ramanujanMockF_trunc q N := ∑_{n=0}^N q^{n²}/(-q;q)_n²`
and closed-form unfoldings `ramanujanMockF_trunc_zero..thirteen`.  Chan's
Ch 10 main results about `f(q)` (the Watson-type identity, the
mock-modular / weight-1/2 quasimodular characterisation, or the Hurwitz
class number / Eichler integral connections) are **not** formalized here.

Until a real chapter-main theorem is added, this file is auxiliary
scaffolding only.
-/

namespace QseriesFormalization
namespace PartII
namespace Ch10

section Field

variable {R : Type*} [Field R]

/-- Ramanujan's third-order mock theta `f(q) := ∑_{n=0}^N q^{n²} / (-q;q)_n²`,
finite truncation. -/
noncomputable def ramanujanMockF_trunc (q : R) (N : Nat) : R :=
  natSum (fun n => q ^ (n * n) / (qPoch (-q) q n) ^ 2) N

/-- N=0 sanity: ramanujanMockF_trunc q 0 = 1. -/
@[simp] theorem ramanujanMockF_trunc_zero (q : R) :
    ramanujanMockF_trunc q 0 = 1 := by
  simp [ramanujanMockF_trunc, natSum, qPoch]

/-- Recursion: `ramanujanMockF_trunc q (N+1) = ramanujanMockF_trunc q N
+ (the new term)`. Pulls the structural step out of the case-by-case
N=k theorems so downstream proofs can recurse without re-expanding
`natSum` each time. -/
@[simp] theorem ramanujanMockF_trunc_succ (q : R) (N : Nat) :
    ramanujanMockF_trunc q (N + 1) =
      ramanujanMockF_trunc q N +
        q ^ ((N + 1) * (N + 1)) / (qPoch (-q) q (N + 1)) ^ 2 := by
  simp [ramanujanMockF_trunc]

/-- N=1 sanity: `f(0) + f(1) = 1 + q / (1 + q)^2`. -/
theorem ramanujanMockF_trunc_one (q : R) :
    ramanujanMockF_trunc q 1 = 1 + q / (1 + q)^2 := by
  simp [ramanujanMockF_trunc, natSum, qPoch]

/-- N=2 sanity: the first three terms of Ramanujan's mock theta `f(q)`. -/
theorem ramanujanMockF_trunc_two (q : R) :
    ramanujanMockF_trunc q 2 =
      1 + q / (1 + q)^2 + q^4 / ((1 + q)^2 * (1 + q^2)^2) := by
  simp [ramanujanMockF_trunc, natSum, qPoch]
  ring_nf

/-- N=3 sanity: the first four terms of Ramanujan's mock theta `f(q)`. -/
theorem ramanujanMockF_trunc_three (q : R) :
    ramanujanMockF_trunc q 3 =
      1 + q / (1 + q)^2 + q^4 / ((1 + q)^2 * (1 + q^2)^2) +
      q^9 / ((1 + q) * (1 + q^2) * (1 + q^3))^2 := by
  simp [ramanujanMockF_trunc, natSum, qPoch]
  ring_nf

/-- N=4: the first five terms of Ramanujan's mock theta `f(q)`. -/
theorem ramanujanMockF_trunc_four (q : R) :
    ramanujanMockF_trunc q 4 =
      1 + q / (1 + q)^2 + q^4 / ((1 + q)^2 * (1 + q^2)^2) +
      q^9 / ((1 + q) * (1 + q^2) * (1 + q^3))^2 +
      q^16 / ((1 + q) * (1 + q^2) * (1 + q^3) * (1 + q^4))^2 := by
  simp [ramanujanMockF_trunc, natSum, qPoch]
  ring_nf

/-- N=5: the first six terms of Ramanujan's mock theta `f(q)`. -/
theorem ramanujanMockF_trunc_five (q : R) :
    ramanujanMockF_trunc q 5 =
      1 + q / (1 + q)^2 + q^4 / ((1 + q)^2 * (1 + q^2)^2) +
      q^9 / ((1 + q) * (1 + q^2) * (1 + q^3))^2 +
      q^16 / ((1 + q) * (1 + q^2) * (1 + q^3) * (1 + q^4))^2 +
      q^25 / ((1 + q) * (1 + q^2) * (1 + q^3) * (1 + q^4) * (1 + q^5))^2 := by
  simp [ramanujanMockF_trunc, natSum, qPoch]
  ring_nf

theorem ramanujanMockF_trunc_six (q : R) :
    ramanujanMockF_trunc q 6 =
      1 + q / (1 + q)^2 + q^4 / ((1 + q)^2 * (1 + q^2)^2) +
      q^9 / ((1 + q) * (1 + q^2) * (1 + q^3))^2 +
      q^16 / ((1 + q) * (1 + q^2) * (1 + q^3) * (1 + q^4))^2 +
      q^25 / ((1 + q) * (1 + q^2) * (1 + q^3) * (1 + q^4) * (1 + q^5))^2 +
      q^36 / ((1 + q) * (1 + q^2) * (1 + q^3) * (1 + q^4) * (1 + q^5) * (1 + q^6))^2 := by
  simp [ramanujanMockF_trunc, natSum, qPoch]
  ring_nf

theorem ramanujanMockF_trunc_seven (q : R) :
    ramanujanMockF_trunc q 7 =
      1 + q / (1 + q)^2 + q^4 / ((1 + q)^2 * (1 + q^2)^2) +
      q^9 / ((1 + q) * (1 + q^2) * (1 + q^3))^2 +
      q^16 / ((1 + q) * (1 + q^2) * (1 + q^3) * (1 + q^4))^2 +
      q^25 / ((1 + q) * (1 + q^2) * (1 + q^3) * (1 + q^4) * (1 + q^5))^2 +
      q^36 / ((1 + q) * (1 + q^2) * (1 + q^3) * (1 + q^4) * (1 + q^5) * (1 + q^6))^2 +
      q^49 / ((1 + q) * (1 + q^2) * (1 + q^3) * (1 + q^4) * (1 + q^5) * (1 + q^6) * (1 + q^7))^2 := by
  simp [ramanujanMockF_trunc, natSum, qPoch]
  ring_nf

theorem ramanujanMockF_trunc_eight (q : R) :
    ramanujanMockF_trunc q 8 =
      1 + q / (1 + q)^2 + q^4 / ((1 + q)^2 * (1 + q^2)^2) +
      q^9 / ((1 + q) * (1 + q^2) * (1 + q^3))^2 +
      q^16 / ((1 + q) * (1 + q^2) * (1 + q^3) * (1 + q^4))^2 +
      q^25 / ((1 + q) * (1 + q^2) * (1 + q^3) * (1 + q^4) * (1 + q^5))^2 +
      q^36 / ((1 + q) * (1 + q^2) * (1 + q^3) * (1 + q^4) * (1 + q^5) * (1 + q^6))^2 +
      q^49 / ((1 + q) * (1 + q^2) * (1 + q^3) * (1 + q^4) * (1 + q^5) * (1 + q^6) * (1 + q^7))^2 +
      q^64 / ((1 + q) * (1 + q^2) * (1 + q^3) * (1 + q^4) * (1 + q^5) * (1 + q^6) * (1 + q^7) * (1 + q^8))^2 := by
  simp [ramanujanMockF_trunc, natSum, qPoch]
  ring_nf

set_option maxHeartbeats 400000 in
theorem ramanujanMockF_trunc_nine (q : R) :
    ramanujanMockF_trunc q 9 =
      1 + q / (1 + q)^2 + q^4 / ((1 + q)^2 * (1 + q^2)^2) +
      q^9 / ((1 + q) * (1 + q^2) * (1 + q^3))^2 +
      q^16 / ((1 + q) * (1 + q^2) * (1 + q^3) * (1 + q^4))^2 +
      q^25 / ((1 + q) * (1 + q^2) * (1 + q^3) * (1 + q^4) * (1 + q^5))^2 +
      q^36 / ((1 + q) * (1 + q^2) * (1 + q^3) * (1 + q^4) * (1 + q^5) * (1 + q^6))^2 +
      q^49 / ((1 + q) * (1 + q^2) * (1 + q^3) * (1 + q^4) * (1 + q^5) * (1 + q^6) * (1 + q^7))^2 +
      q^64 / ((1 + q) * (1 + q^2) * (1 + q^3) * (1 + q^4) * (1 + q^5) * (1 + q^6) * (1 + q^7) * (1 + q^8))^2 +
      q^81 / ((1 + q) * (1 + q^2) * (1 + q^3) * (1 + q^4) * (1 + q^5) * (1 + q^6) * (1 + q^7) * (1 + q^8) * (1 + q^9))^2 := by
  simp [ramanujanMockF_trunc, natSum, qPoch]
  ring_nf

set_option maxHeartbeats 800000 in
theorem ramanujanMockF_trunc_ten (q : R) :
    ramanujanMockF_trunc q 10 =
      1 + q / (1 + q)^2 + q^4 / ((1 + q)^2 * (1 + q^2)^2) +
      q^9 / ((1 + q) * (1 + q^2) * (1 + q^3))^2 +
      q^16 / ((1 + q) * (1 + q^2) * (1 + q^3) * (1 + q^4))^2 +
      q^25 / ((1 + q) * (1 + q^2) * (1 + q^3) * (1 + q^4) * (1 + q^5))^2 +
      q^36 / ((1 + q) * (1 + q^2) * (1 + q^3) * (1 + q^4) * (1 + q^5) * (1 + q^6))^2 +
      q^49 / ((1 + q) * (1 + q^2) * (1 + q^3) * (1 + q^4) * (1 + q^5) * (1 + q^6) * (1 + q^7))^2 +
      q^64 / ((1 + q) * (1 + q^2) * (1 + q^3) * (1 + q^4) * (1 + q^5) * (1 + q^6) * (1 + q^7) * (1 + q^8))^2 +
      q^81 / ((1 + q) * (1 + q^2) * (1 + q^3) * (1 + q^4) * (1 + q^5) * (1 + q^6) * (1 + q^7) * (1 + q^8) * (1 + q^9))^2 +
      q^100 / ((1 + q) * (1 + q^2) * (1 + q^3) * (1 + q^4) * (1 + q^5) * (1 + q^6) * (1 + q^7) * (1 + q^8) * (1 + q^9) * (1 + q^10))^2 := by
  simp [ramanujanMockF_trunc, natSum, qPoch]
  ring_nf

set_option maxHeartbeats 1600000 in
theorem ramanujanMockF_trunc_eleven (q : R) :
    ramanujanMockF_trunc q 11 =
      1 + q / (1 + q)^2 + q^4 / ((1 + q)^2 * (1 + q^2)^2) +
      q^9 / ((1 + q) * (1 + q^2) * (1 + q^3))^2 +
      q^16 / ((1 + q) * (1 + q^2) * (1 + q^3) * (1 + q^4))^2 +
      q^25 / ((1 + q) * (1 + q^2) * (1 + q^3) * (1 + q^4) * (1 + q^5))^2 +
      q^36 / ((1 + q) * (1 + q^2) * (1 + q^3) * (1 + q^4) * (1 + q^5) * (1 + q^6))^2 +
      q^49 / ((1 + q) * (1 + q^2) * (1 + q^3) * (1 + q^4) * (1 + q^5) * (1 + q^6) * (1 + q^7))^2 +
      q^64 / ((1 + q) * (1 + q^2) * (1 + q^3) * (1 + q^4) * (1 + q^5) * (1 + q^6) * (1 + q^7) * (1 + q^8))^2 +
      q^81 / ((1 + q) * (1 + q^2) * (1 + q^3) * (1 + q^4) * (1 + q^5) * (1 + q^6) * (1 + q^7) * (1 + q^8) * (1 + q^9))^2 +
      q^100 / ((1 + q) * (1 + q^2) * (1 + q^3) * (1 + q^4) * (1 + q^5) * (1 + q^6) * (1 + q^7) * (1 + q^8) * (1 + q^9) * (1 + q^10))^2 +
      q^121 / ((1 + q) * (1 + q^2) * (1 + q^3) * (1 + q^4) * (1 + q^5) * (1 + q^6) * (1 + q^7) * (1 + q^8) * (1 + q^9) * (1 + q^10) * (1 + q^11))^2 := by
  simp [ramanujanMockF_trunc, natSum, qPoch]
  ring_nf

set_option maxHeartbeats 3200000 in
theorem ramanujanMockF_trunc_twelve (q : R) :
    ramanujanMockF_trunc q 12 =
      1 + q / (1 + q)^2 + q^4 / ((1 + q)^2 * (1 + q^2)^2) +
      q^9 / ((1 + q) * (1 + q^2) * (1 + q^3))^2 +
      q^16 / ((1 + q) * (1 + q^2) * (1 + q^3) * (1 + q^4))^2 +
      q^25 / ((1 + q) * (1 + q^2) * (1 + q^3) * (1 + q^4) * (1 + q^5))^2 +
      q^36 / ((1 + q) * (1 + q^2) * (1 + q^3) * (1 + q^4) * (1 + q^5) * (1 + q^6))^2 +
      q^49 / ((1 + q) * (1 + q^2) * (1 + q^3) * (1 + q^4) * (1 + q^5) * (1 + q^6) * (1 + q^7))^2 +
      q^64 / ((1 + q) * (1 + q^2) * (1 + q^3) * (1 + q^4) * (1 + q^5) * (1 + q^6) * (1 + q^7) * (1 + q^8))^2 +
      q^81 / ((1 + q) * (1 + q^2) * (1 + q^3) * (1 + q^4) * (1 + q^5) * (1 + q^6) * (1 + q^7) * (1 + q^8) * (1 + q^9))^2 +
      q^100 / ((1 + q) * (1 + q^2) * (1 + q^3) * (1 + q^4) * (1 + q^5) * (1 + q^6) * (1 + q^7) * (1 + q^8) * (1 + q^9) * (1 + q^10))^2 +
      q^121 / ((1 + q) * (1 + q^2) * (1 + q^3) * (1 + q^4) * (1 + q^5) * (1 + q^6) * (1 + q^7) * (1 + q^8) * (1 + q^9) * (1 + q^10) * (1 + q^11))^2 +
      q^144 / ((1 + q) * (1 + q^2) * (1 + q^3) * (1 + q^4) * (1 + q^5) * (1 + q^6) * (1 + q^7) * (1 + q^8) * (1 + q^9) * (1 + q^10) * (1 + q^11) * (1 + q^12))^2 := by
  simp [ramanujanMockF_trunc, natSum, qPoch]
  ring_nf

set_option maxHeartbeats 6400000 in
set_option maxRecDepth 2000 in
theorem ramanujanMockF_trunc_thirteen (q : R) :
    ramanujanMockF_trunc q 13 =
      1 + q / (1 + q)^2 + q^4 / ((1 + q)^2 * (1 + q^2)^2) +
      q^9 / ((1 + q) * (1 + q^2) * (1 + q^3))^2 +
      q^16 / ((1 + q) * (1 + q^2) * (1 + q^3) * (1 + q^4))^2 +
      q^25 / ((1 + q) * (1 + q^2) * (1 + q^3) * (1 + q^4) * (1 + q^5))^2 +
      q^36 / ((1 + q) * (1 + q^2) * (1 + q^3) * (1 + q^4) * (1 + q^5) * (1 + q^6))^2 +
      q^49 / ((1 + q) * (1 + q^2) * (1 + q^3) * (1 + q^4) * (1 + q^5) * (1 + q^6) * (1 + q^7))^2 +
      q^64 / ((1 + q) * (1 + q^2) * (1 + q^3) * (1 + q^4) * (1 + q^5) * (1 + q^6) * (1 + q^7) * (1 + q^8))^2 +
      q^81 / ((1 + q) * (1 + q^2) * (1 + q^3) * (1 + q^4) * (1 + q^5) * (1 + q^6) * (1 + q^7) * (1 + q^8) * (1 + q^9))^2 +
      q^100 / ((1 + q) * (1 + q^2) * (1 + q^3) * (1 + q^4) * (1 + q^5) * (1 + q^6) * (1 + q^7) * (1 + q^8) * (1 + q^9) * (1 + q^10))^2 +
      q^121 / ((1 + q) * (1 + q^2) * (1 + q^3) * (1 + q^4) * (1 + q^5) * (1 + q^6) * (1 + q^7) * (1 + q^8) * (1 + q^9) * (1 + q^10) * (1 + q^11))^2 +
      q^144 / ((1 + q) * (1 + q^2) * (1 + q^3) * (1 + q^4) * (1 + q^5) * (1 + q^6) * (1 + q^7) * (1 + q^8) * (1 + q^9) * (1 + q^10) * (1 + q^11) * (1 + q^12))^2 +
      q^169 / ((1 + q) * (1 + q^2) * (1 + q^3) * (1 + q^4) * (1 + q^5) * (1 + q^6) * (1 + q^7) * (1 + q^8) * (1 + q^9) * (1 + q^10) * (1 + q^11) * (1 + q^12) * (1 + q^13))^2 := by
  simp [ramanujanMockF_trunc, natSum, qPoch]
  ring_nf


end Field

end Ch10
end PartII
end QseriesFormalization
