import QseriesFormalization.Pending.Chapter08_FiniteRR

/-!
# Chapter 8 Gaussian-polynomial side

This file records the closed Rogers-Ramanujan cases of Chan Theorem 8.1.
The Gaussian-polynomial side `DFinite` is defined in the imported finite-RR
development; here we expose that definition and prove only the `a = 0, 1`
identity cases.
-/

namespace QseriesFormalization
namespace PartII
namespace Ch08

section Field

variable {R : Type*} [Field R]

/-- `DFinite` is Chan's finite alternating Gaussian-polynomial side. -/
theorem DFinite_gaussian_polynomial_side (q : R) (a N : Nat) :
    DFinite q a N = bilateralSum (DFiniteTerm q a N) (DFiniteBound a N) := rfl

/-- Chan Theorem 8.1 for the first Rogers-Ramanujan case `a = 0`. -/
theorem chan_theorem_8_1_a0 (q : R) (N : Nat) :
    EFinite q 0 N = DFinite q 0 N :=
  EFinite_eq_DFinite_a0 q N

/-- Chan Theorem 8.1 for the second Rogers-Ramanujan case `a = 1`. -/
theorem chan_theorem_8_1_a1 (q : R) (N : Nat) :
    EFinite q 1 N = DFinite q 1 N :=
  EFinite_eq_DFinite_a1 q N

/-- The closed part of Chan Theorem 8.1: only `a = 0` and `a = 1`. -/
theorem chan_theorem_8_1_of_a_eq_zero_or_one (q : R) {a N : Nat}
    (ha : a = 0 ∨ a = 1) :
    EFinite q a N = DFinite q a N := by
  rcases ha with rfl | rfl
  · exact chan_theorem_8_1_a0 q N
  · exact chan_theorem_8_1_a1 q N

end Field

end Ch08
end PartII
end QseriesFormalization
