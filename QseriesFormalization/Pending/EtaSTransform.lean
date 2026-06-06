import Mathlib.NumberTheory.ModularForms.DedekindEta
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import QseriesFormalization.Chapter04_T43

/-!
# Pending: eta S-transform via theta constants

This file proves the theta-constant part of the standard route to the
Dedekind eta S-transform.

Mathlib already proves the Poisson-summation input
`jacobiTheta_S_smul`.  The two-variable theta functional equation gives the
S-transform of the classical theta constants `theta2` and `theta4`, while
`jacobiTheta_S_smul` gives `theta3`.

The eta step is split into a proved Jacobi product bridge and one remaining
analytic branch hypothesis:

* `EtaPow24ThetaDeltaFormula`: the Jacobi product formula
  `eta^24 = (theta2 theta3 theta4)^8 / 256`.
* `EtaSBranchFormula`: the local branch extraction at `τ = 5i`, from the
  24th-power identity and positivity of eta on the imaginary axis.

No proof placeholders are used here.
-/

namespace QseriesFormalization
namespace Pending
namespace EtaSTransform

open Complex

open scoped Real UpperHalfPlane

/-- The square-root factor appearing in the theta S-transform. -/
noncomputable def thetaSFactor (τ : ℂ) : ℂ :=
  (-Complex.I * τ) ^ (1 / 2 : ℂ)

/-- Classical `theta2`, expressed through Mathlib's two-variable theta. -/
noncomputable def theta2 (τ : ℂ) : ℂ :=
  Complex.exp (π * Complex.I * τ / 4) * jacobiTheta₂ (τ / 2) τ

/-- Classical `theta3`. -/
noncomputable def theta3 (τ : ℂ) : ℂ :=
  jacobiTheta τ

/-- Classical `theta4`, as `theta3(z = 1/2, τ)`. -/
noncomputable def theta4 (τ : ℂ) : ℂ :=
  jacobiTheta₂ (1 / 2) τ

/-- The theta-product model of the modular discriminant. -/
noncomputable def thetaDelta (τ : ℂ) : ℂ :=
  (theta2 τ * theta3 τ * theta4 τ) ^ 8 / 256

private noncomputable def qHalf (τ : ℂ) : ℂ :=
  Function.Periodic.qParam 2 τ

private theorem qHalf_eq_exp (τ : ℂ) :
    qHalf τ = Complex.exp (π * Complex.I * τ) := by
  rw [qHalf, Function.Periodic.qParam]
  congr 1
  field_simp
  norm_num
  ring

private theorem qHalf_norm_lt_one (τ : _root_.UpperHalfPlane) :
    ‖qHalf (τ : ℂ)‖ < 1 := by
  simpa [qHalf] using _root_.UpperHalfPlane.norm_qParam_lt_one 2 τ

private theorem qHalf_ne_zero (τ : ℂ) : qHalf τ ≠ 0 := by
  rw [qHalf_eq_exp]
  exact Complex.exp_ne_zero _

private theorem theta3_eq_jacobiInfiniteSeries (τ : _root_.UpperHalfPlane) :
    theta3 (τ : ℂ) =
      QseriesFormalization.PartI.Ch02.jacobiInfiniteSeries (qHalf (τ : ℂ)) 1 := by
  rw [theta3, QseriesFormalization.PartI.Ch02.jacobiInfiniteSeries, qHalf_eq_exp]
  refine tsum_congr fun n => ?_
  rw [one_zpow]
  simp only [one_mul]
  rw [← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

private theorem neg_one_zpow_eq_exp_pi_I (n : ℤ) :
    ((-1 : ℂ) ^ n) = Complex.exp ((n : ℂ) * (π * Complex.I)) := by
  rw [← Complex.exp_pi_mul_I, ← Complex.exp_int_mul]

private theorem theta4_eq_jacobiInfiniteSeries (τ : _root_.UpperHalfPlane) :
    theta4 (τ : ℂ) =
      QseriesFormalization.PartI.Ch02.jacobiInfiniteSeries (qHalf (τ : ℂ)) (-1) := by
  rw [theta4, QseriesFormalization.PartI.Ch02.jacobiInfiniteSeries, qHalf_eq_exp]
  refine tsum_congr fun n => ?_
  rw [jacobiTheta₂_term]
  rw [neg_one_zpow_eq_exp_pi_I n]
  rw [← Complex.exp_int_mul]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem theta2_eq_exp_mul_jacobiInfiniteSeries (τ : _root_.UpperHalfPlane) :
    theta2 (τ : ℂ) =
      Complex.exp (π * Complex.I * (τ : ℂ) / 4) *
        QseriesFormalization.PartI.Ch02.jacobiInfiniteSeries (qHalf (τ : ℂ)) (qHalf (τ : ℂ)) := by
  rw [theta2, QseriesFormalization.PartI.Ch02.jacobiInfiniteSeries, qHalf_eq_exp]
  congr 1
  refine tsum_congr fun n => ?_
  rw [jacobiTheta₂_term]
  rw [← Complex.exp_int_mul]
  rw [← Complex.exp_int_mul]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem theta3_eq_jacobiInfiniteProduct (τ : _root_.UpperHalfPlane) :
    theta3 (τ : ℂ) =
      QseriesFormalization.PartI.Ch02.jacobiInfiniteProduct (qHalf (τ : ℂ)) 1 := by
  rw [theta3_eq_jacobiInfiniteSeries τ]
  rw [← QseriesFormalization.PartI.Ch02.jacobiTripleProduct
    (qHalf (τ : ℂ)) 1 (qHalf_norm_lt_one τ) (by norm_num : (1 : ℂ) ≠ 0)]

private theorem theta4_eq_jacobiInfiniteProduct (τ : _root_.UpperHalfPlane) :
    theta4 (τ : ℂ) =
      QseriesFormalization.PartI.Ch02.jacobiInfiniteProduct (qHalf (τ : ℂ)) (-1) := by
  rw [theta4_eq_jacobiInfiniteSeries τ]
  rw [← QseriesFormalization.PartI.Ch02.jacobiTripleProduct
    (qHalf (τ : ℂ)) (-1) (qHalf_norm_lt_one τ) (by norm_num : (-1 : ℂ) ≠ 0)]

private theorem theta2_eq_exp_mul_jacobiInfiniteProduct (τ : _root_.UpperHalfPlane) :
    theta2 (τ : ℂ) =
      Complex.exp (π * Complex.I * (τ : ℂ) / 4) *
        QseriesFormalization.PartI.Ch02.jacobiInfiniteProduct
          (qHalf (τ : ℂ)) (qHalf (τ : ℂ)) := by
  rw [theta2_eq_exp_mul_jacobiInfiniteSeries τ]
  rw [← QseriesFormalization.PartI.Ch02.jacobiTripleProduct
    (qHalf (τ : ℂ)) (qHalf (τ : ℂ)) (qHalf_norm_lt_one τ) (qHalf_ne_zero (τ : ℂ))]

private noncomputable def evenProduct (Q : ℂ) : ℂ :=
  ∏' n : ℕ, QseriesFormalization.PartI.Ch02.jacobiProductEvenFactor Q n

private noncomputable def oddProduct (Q c : ℂ) : ℂ :=
  ∏' n : ℕ, QseriesFormalization.PartI.Ch02.jacobiProductOddFactor Q c n

private noncomputable def plusProduct (Q : ℂ) : ℂ :=
  ∏' n : ℕ, (1 + (Q ^ 2) ^ (n + 1))

private noncomputable def oddSquareProduct (Q : ℂ) : ℂ :=
  ∏' n : ℕ, (1 - (Q ^ 2) ^ (2 * n + 1))

private theorem oddFactor_self_eq_plusFactor (Q : ℂ) (n : ℕ) :
    QseriesFormalization.PartI.Ch02.jacobiProductOddFactor Q Q n =
      1 + (Q ^ 2) ^ (n + 1) := by
  simp [QseriesFormalization.PartI.Ch02.jacobiProductOddFactor]
  rw [show 2 * (n + 1) - 1 = 2 * n + 1 by omega]
  rw [show (Q ^ 2) ^ (n + 1) = Q ^ (2 * (n + 1)) by rw [pow_mul]]
  rw [show 2 * (n + 1) = 1 + (2 * n + 1) by omega]
  rw [pow_add]
  ring

private theorem oddFactor_inv_self_succ_eq_plusFactor (Q : ℂ) (hQ0 : Q ≠ 0) (n : ℕ) :
    QseriesFormalization.PartI.Ch02.jacobiProductOddFactor Q Q⁻¹ (n + 1) =
      1 + (Q ^ 2) ^ (n + 1) := by
  simp [QseriesFormalization.PartI.Ch02.jacobiProductOddFactor]
  rw [show 2 * (n + 1 + 1) - 1 = 2 * n + 3 by omega]
  rw [show (Q ^ 2) ^ (n + 1) = Q ^ (2 * (n + 1)) by rw [pow_mul]]
  rw [show 2 * (n + 1) = 2 * n + 2 by omega]
  field_simp [hQ0]
  rw [show 2 * n + 3 = (2 * n + 2) + 1 by omega]
  rw [pow_add]
  ring

private theorem oddFactor_one_mul_neg_one_eq_oddSquareFactor (Q : ℂ) (n : ℕ) :
    QseriesFormalization.PartI.Ch02.jacobiProductOddFactor Q 1 n *
        QseriesFormalization.PartI.Ch02.jacobiProductOddFactor Q (-1) n =
      1 - (Q ^ 2) ^ (2 * n + 1) := by
  simp [QseriesFormalization.PartI.Ch02.jacobiProductOddFactor]
  rw [show 2 * (n + 1) - 1 = 2 * n + 1 by omega]
  rw [show (Q ^ 2) ^ (2 * n + 1) = (Q ^ (2 * n + 1)) ^ 2 by
    calc
      (Q ^ 2) ^ (2 * n + 1) = Q ^ (2 * (2 * n + 1)) := by rw [pow_mul]
      _ = Q ^ ((2 * n + 1) * 2) := by
        congr 1
        ring
      _ = (Q ^ (2 * n + 1)) ^ 2 := by rw [pow_mul]]
  ring

private theorem pow_two_mul_add_one_add_one (a : ℂ) (n : ℕ) :
    a ^ (2 * n + 1 + 1) = (a ^ (n + 1)) ^ 2 := by
  rw [show 2 * n + 1 + 1 = (n + 1) * 2 by omega]
  rw [pow_mul]

private theorem oddProduct_self_eq_plusProduct (Q : ℂ) :
    oddProduct Q Q = plusProduct Q := by
  rw [oddProduct, plusProduct]
  refine tprod_congr fun n => ?_
  exact oddFactor_self_eq_plusFactor Q n

private theorem oddProduct_inv_self_eq_two_mul_plusProduct (Q : ℂ)
    (hQ : ‖Q‖ < 1) (hQ0 : Q ≠ 0) :
    oddProduct Q Q⁻¹ = 2 * plusProduct Q := by
  rw [oddProduct]
  have htail :
      Multipliable fun n : ℕ =>
        QseriesFormalization.PartI.Ch02.jacobiProductOddFactor Q Q⁻¹ (n + 1) := by
    exact (QseriesFormalization.PartI.Ch02.multipliable_jacobiProductOddFactor Q Q hQ).congr
      fun n => by rw [oddFactor_inv_self_succ_eq_plusFactor Q hQ0 n,
        ← oddFactor_self_eq_plusFactor Q n]
  rw [tprod_eq_zero_mul' htail]
  have hzero :
      QseriesFormalization.PartI.Ch02.jacobiProductOddFactor Q Q⁻¹ 0 = 2 := by
    simp [QseriesFormalization.PartI.Ch02.jacobiProductOddFactor, hQ0]
    field_simp [hQ0]
    norm_num
  rw [hzero]
  congr 1
  rw [plusProduct]
  refine tprod_congr fun n => ?_
  exact oddFactor_inv_self_succ_eq_plusFactor Q hQ0 n

private theorem oddProduct_one_mul_neg_one_eq_oddSquareProduct (Q : ℂ) (hQ : ‖Q‖ < 1) :
    oddProduct Q 1 * oddProduct Q (-1) = oddSquareProduct Q := by
  rw [oddProduct, oddProduct, oddSquareProduct]
  have h1 := QseriesFormalization.PartI.Ch02.multipliable_jacobiProductOddFactor Q 1 hQ
  have hm1 := QseriesFormalization.PartI.Ch02.multipliable_jacobiProductOddFactor Q (-1) hQ
  rw [← Multipliable.tprod_mul h1 hm1]
  refine tprod_congr fun n => ?_
  exact oddFactor_one_mul_neg_one_eq_oddSquareFactor Q n

private theorem plusProduct_mul_oddSquareProduct_eq_one (Q : ℂ) (hQ : ‖Q‖ < 1) :
    plusProduct Q * oddSquareProduct Q = 1 := by
  let R : ℂ := Q ^ 2
  let f : ℕ → ℂ := fun n => 1 - R ^ (n + 1)
  have hR : ‖R‖ < 1 := by
    dsimp [R]
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg Q) hQ (by norm_num)
  have hR2 : ‖R ^ 2‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg R) hR (by norm_num)
  have hfull : Multipliable f := by
    simpa [f, QseriesFormalization.PartI.Ch04.eulerPentagonalProductFactor]
      using QseriesFormalization.PartI.Ch04.multipliable_eulerPentagonalProductFactor R hR
  have hfull_ne : (∏' n : ℕ, f n) ≠ 0 := by
    simpa [f, QseriesFormalization.PartI.Ch04.eulerPentagonalInfiniteProduct,
      QseriesFormalization.PartI.Ch04.eulerPentagonalProductFactor]
      using QseriesFormalization.PartI.Ch04.eulerPentagonalInfiniteProduct_ne_zero R hR
  have hplus : Multipliable fun n : ℕ => 1 + R ^ (n + 1) := by
    exact (QseriesFormalization.PartI.Ch02.multipliable_jacobiProductOddFactor Q Q hQ).congr
      fun n => by
        dsimp [R]
        rw [oddFactor_self_eq_plusFactor Q n]
  have hodd : Multipliable fun n : ℕ => f (2 * n) := by
    have hsum := QseriesFormalization.PartI.Ch02.summable_norm_mul_geometric_complex
      (-R) (R ^ 2) hR2
    refine (multipliable_one_add_of_summable hsum).congr fun n => ?_
    dsimp [f]
    rw [show R ^ (2 * n + 1) = R * (R ^ 2) ^ n by
      rw [show 2 * n + 1 = 1 + 2 * n by omega, pow_add, pow_mul]
      ring]
    ring
  have heven : Multipliable fun n : ℕ => f (2 * n + 1) := by
    have hsum := QseriesFormalization.PartI.Ch02.summable_norm_mul_geometric_complex
      (-(R ^ 2)) (R ^ 2) hR2
    refine (multipliable_one_add_of_summable hsum).congr fun n => ?_
    dsimp [f]
    rw [show R ^ (2 * n + 1 + 1) = R ^ 2 * (R ^ 2) ^ n by
      rw [show 2 * n + 1 + 1 = 2 + 2 * n by omega, pow_add, pow_mul]]
    ring
  have hsplit :
      (∏' n : ℕ, f (2 * n)) * (∏' n : ℕ, f (2 * n + 1)) =
        ∏' n : ℕ, f n :=
    tprod_even_mul_odd hodd heven
  have heven_eq :
      (∏' n : ℕ, f (2 * n + 1)) =
        (∏' n : ℕ, f n) * (∏' n : ℕ, (1 + R ^ (n + 1))) := by
    calc
      (∏' n : ℕ, f (2 * n + 1)) =
          ∏' n : ℕ, (f n * (1 + R ^ (n + 1))) := by
            refine tprod_congr fun n => ?_
            change 1 - R ^ (2 * n + 1 + 1) =
              (1 - R ^ (n + 1)) * (1 + R ^ (n + 1))
            rw [pow_two_mul_add_one_add_one R n]
            ring
      _ = (∏' n : ℕ, f n) * (∏' n : ℕ, (1 + R ^ (n + 1))) := by
            rw [Multipliable.tprod_mul hfull hplus]
  have hmain :
      (∏' n : ℕ, f (2 * n)) *
          ((∏' n : ℕ, f n) * (∏' n : ℕ, (1 + R ^ (n + 1)))) =
        ∏' n : ℕ, f n := by
    simpa [heven_eq] using hsplit
  have hcancel :
      (∏' n : ℕ, f n) *
          ((∏' n : ℕ, (1 + R ^ (n + 1))) * (∏' n : ℕ, f (2 * n))) =
        (∏' n : ℕ, f n) * 1 := by
    calc
      (∏' n : ℕ, f n) *
          ((∏' n : ℕ, (1 + R ^ (n + 1))) * (∏' n : ℕ, f (2 * n)))
          =
        (∏' n : ℕ, f (2 * n)) *
          ((∏' n : ℕ, f n) * (∏' n : ℕ, (1 + R ^ (n + 1)))) := by ring
      _ = (∏' n : ℕ, f n) := hmain
      _ = (∏' n : ℕ, f n) * 1 := by ring
  have hgeneric :
      (∏' n : ℕ, (1 + R ^ (n + 1))) * (∏' n : ℕ, f (2 * n)) = 1 :=
    mul_left_cancel₀ hfull_ne hcancel
  simpa [plusProduct, oddSquareProduct, R, f] using hgeneric

private theorem jacobiInfiniteProduct_self_one_neg_one (Q : ℂ)
    (hQ : ‖Q‖ < 1) (hQ0 : Q ≠ 0) :
    QseriesFormalization.PartI.Ch02.jacobiInfiniteProduct Q Q *
        QseriesFormalization.PartI.Ch02.jacobiInfiniteProduct Q 1 *
        QseriesFormalization.PartI.Ch02.jacobiInfiniteProduct Q (-1) =
      2 * (evenProduct Q) ^ 3 := by
  rw [QseriesFormalization.PartI.Ch02.jacobiInfiniteProduct_eq_tprod_components Q Q hQ,
    QseriesFormalization.PartI.Ch02.jacobiInfiniteProduct_eq_tprod_components Q 1 hQ,
    QseriesFormalization.PartI.Ch02.jacobiInfiniteProduct_eq_tprod_components Q (-1) hQ]
  have hneg_inv : ((-1 : ℂ)⁻¹) = -1 := by norm_num
  rw [inv_one, hneg_inv]
  change (evenProduct Q * oddProduct Q Q * oddProduct Q Q⁻¹) *
        (evenProduct Q * oddProduct Q 1 * oddProduct Q 1) *
        (evenProduct Q * oddProduct Q (-1) * oddProduct Q (-1)) =
      2 * (evenProduct Q) ^ 3
  rw [oddProduct_self_eq_plusProduct Q,
    oddProduct_inv_self_eq_two_mul_plusProduct Q hQ hQ0]
  have hodd := oddProduct_one_mul_neg_one_eq_oddSquareProduct Q hQ
  have hplusodd := plusProduct_mul_oddSquareProduct_eq_one Q hQ
  calc
    (evenProduct Q * plusProduct Q * (2 * plusProduct Q)) *
        (evenProduct Q * oddProduct Q 1 * oddProduct Q 1) *
        (evenProduct Q * oddProduct Q (-1) * oddProduct Q (-1))
        =
      2 * (evenProduct Q) ^ 3 *
        (plusProduct Q * plusProduct Q) *
        ((oddProduct Q 1 * oddProduct Q (-1)) *
          (oddProduct Q 1 * oddProduct Q (-1))) := by
          ring
    _ =
      2 * (evenProduct Q) ^ 3 *
        (plusProduct Q * plusProduct Q) *
        (oddSquareProduct Q * oddSquareProduct Q) := by
          rw [hodd]
    _ =
      2 * (evenProduct Q) ^ 3 *
        ((plusProduct Q * oddSquareProduct Q) *
          (plusProduct Q * oddSquareProduct Q)) := by
          ring
    _ = 2 * (evenProduct Q) ^ 3 := by
          rw [hplusodd]
          ring

private theorem theta_product_eq_two_exp_mul_evenProduct (τ : _root_.UpperHalfPlane) :
    theta2 (τ : ℂ) * theta3 (τ : ℂ) * theta4 (τ : ℂ) =
      2 * Complex.exp (π * Complex.I * (τ : ℂ) / 4) *
        (evenProduct (qHalf (τ : ℂ))) ^ 3 := by
  rw [theta2_eq_exp_mul_jacobiInfiniteProduct τ,
    theta3_eq_jacobiInfiniteProduct τ, theta4_eq_jacobiInfiniteProduct τ]
  have hprod := jacobiInfiniteProduct_self_one_neg_one
    (qHalf (τ : ℂ)) (qHalf_norm_lt_one τ) (qHalf_ne_zero (τ : ℂ))
  calc
    (Complex.exp (π * Complex.I * (τ : ℂ) / 4) *
          QseriesFormalization.PartI.Ch02.jacobiInfiniteProduct
            (qHalf (τ : ℂ)) (qHalf (τ : ℂ))) *
        QseriesFormalization.PartI.Ch02.jacobiInfiniteProduct (qHalf (τ : ℂ)) 1 *
        QseriesFormalization.PartI.Ch02.jacobiInfiniteProduct (qHalf (τ : ℂ)) (-1)
        =
      Complex.exp (π * Complex.I * (τ : ℂ) / 4) *
        (QseriesFormalization.PartI.Ch02.jacobiInfiniteProduct
            (qHalf (τ : ℂ)) (qHalf (τ : ℂ)) *
          QseriesFormalization.PartI.Ch02.jacobiInfiniteProduct (qHalf (τ : ℂ)) 1 *
          QseriesFormalization.PartI.Ch02.jacobiInfiniteProduct (qHalf (τ : ℂ)) (-1)) := by
          ring
    _ = Complex.exp (π * Complex.I * (τ : ℂ) / 4) *
        (2 * (evenProduct (qHalf (τ : ℂ))) ^ 3) := by
          rw [hprod]
    _ = 2 * Complex.exp (π * Complex.I * (τ : ℂ) / 4) *
        (evenProduct (qHalf (τ : ℂ))) ^ 3 := by
          ring

private theorem eta_q_eq_qHalf_even (τ : ℂ) (n : ℕ) :
    ModularForm.eta_q n τ = qHalf τ ^ (2 * (n + 1)) := by
  rw [ModularForm.eta_q_eq_cexp, qHalf_eq_exp]
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

private theorem eta_eq_qParam_mul_evenProduct (τ : ℂ) :
    ModularForm.eta τ = Function.Periodic.qParam 24 τ * evenProduct (qHalf τ) := by
  rw [ModularForm.eta, evenProduct]
  congr 1
  refine tprod_congr fun n => ?_
  rw [eta_q_eq_qHalf_even τ n]
  rfl

private theorem qParam_twenty_four_pow_three (τ : ℂ) :
    Function.Periodic.qParam 24 τ ^ 3 =
      Complex.exp (π * Complex.I * τ / 4) := by
  rw [Function.Periodic.qParam]
  rw [← Complex.exp_nat_mul]
  congr 1
  field_simp
  norm_num
  ring

private theorem eta_pow_three_eq_exp_mul_evenProduct (τ : _root_.UpperHalfPlane) :
    ModularForm.eta (τ : ℂ) ^ 3 =
      Complex.exp (π * Complex.I * (τ : ℂ) / 4) *
        (evenProduct (qHalf (τ : ℂ))) ^ 3 := by
  rw [eta_eq_qParam_mul_evenProduct]
  rw [mul_pow, qParam_twenty_four_pow_three]

private theorem eta_pow_three_eq_theta_product_half (τ : _root_.UpperHalfPlane) :
    ModularForm.eta (τ : ℂ) ^ 3 =
      theta2 (τ : ℂ) * theta3 (τ : ℂ) * theta4 (τ : ℂ) / 2 := by
  rw [eta_pow_three_eq_exp_mul_evenProduct τ]
  rw [theta_product_eq_two_exp_mul_evenProduct τ]
  ring

private theorem upper_ne_zero (τ : _root_.UpperHalfPlane) : (τ : ℂ) ≠ 0 := by
  intro h
  have him : im (τ : ℂ) = im (0 : ℂ) := by rw [h]
  rw [zero_im] at him
  exact (ne_of_gt τ.2) him

private theorem thetaSFactor_ne_zero (τ : _root_.UpperHalfPlane) :
    thetaSFactor (τ : ℂ) ≠ 0 := by
  rw [thetaSFactor, Ne, cpow_eq_zero_iff, not_and_or]
  exact Or.inl <| mul_ne_zero (neg_ne_zero.mpr I_ne_zero) (upper_ne_zero τ)

private theorem modular_S_coe (τ : _root_.UpperHalfPlane) :
    ((ModularGroup.S • τ : _root_.UpperHalfPlane) : ℂ) = -1 / (τ : ℂ) := by
  rw [_root_.UpperHalfPlane.modular_S_smul]
  change (-(τ : ℂ))⁻¹ = -1 / (τ : ℂ)
  rw [inv_neg, div_eq_mul_inv]
  ring

private theorem thetaSFactor_sq (τ : _root_.UpperHalfPlane) :
    thetaSFactor (τ : ℂ) ^ 2 = -Complex.I * (τ : ℂ) := by
  rw [thetaSFactor]
  rw [show (1 / 2 : ℂ) = ((2 : ℕ)⁻¹ : ℂ) by norm_num]
  exact Complex.cpow_nat_inv_pow (-Complex.I * (τ : ℂ))
    (by norm_num : (2 : ℕ) ≠ 0)

private theorem thetaSFactor_pow_twenty_four (τ : _root_.UpperHalfPlane) :
    thetaSFactor (τ : ℂ) ^ 24 = (τ : ℂ) ^ 12 := by
  calc
    thetaSFactor (τ : ℂ) ^ 24 =
        (thetaSFactor (τ : ℂ) ^ 2) ^ 12 := by ring
    _ = (-Complex.I * (τ : ℂ)) ^ 12 := by rw [thetaSFactor_sq]
    _ = (τ : ℂ) ^ 12 := by
      rw [mul_pow]
      have hI : (-Complex.I) ^ 12 = (1 : ℂ) := by
        calc
          (-Complex.I) ^ 12 = Complex.I ^ 12 := by ring
          _ = Complex.I ^ (12 % 4) := Complex.I_pow_eq_pow_mod 12
          _ = 1 := by norm_num
      rw [hI, one_mul]

/-- `theta3(-1/τ) = (-iτ)^(1/2) theta3(τ)`. -/
theorem theta3_S (τ : _root_.UpperHalfPlane) :
    theta3 (((ModularGroup.S • τ : _root_.UpperHalfPlane) : ℂ)) =
      thetaSFactor (τ : ℂ) * theta3 (τ : ℂ) := by
  simpa [theta3, thetaSFactor] using jacobiTheta_S_smul τ

/-- `theta2(-1/τ) = (-iτ)^(1/2) theta4(τ)`. -/
theorem theta2_S (τ : _root_.UpperHalfPlane) :
    theta2 (((ModularGroup.S • τ : _root_.UpperHalfPlane) : ℂ)) =
      thetaSFactor (τ : ℂ) * theta4 (τ : ℂ) := by
  let f := thetaSFactor (τ : ℂ)
  let e : ℂ := Complex.exp (-π * Complex.I / (4 * (τ : ℂ)))
  let A : ℂ := jacobiTheta₂ ((1 / 2 : ℂ) / (τ : ℂ)) (-1 / (τ : ℂ))
  have hf : f ≠ 0 := by
    dsimp [f]
    exact thetaSFactor_ne_zero τ
  have h_even :
      jacobiTheta₂ ((-1 / (τ : ℂ)) / 2) (-1 / (τ : ℂ)) = A := by
    dsimp [A]
    have hz : ((-1 / (τ : ℂ)) / 2 : ℂ) = -((1 / 2 : ℂ) / (τ : ℂ)) := by
      field_simp [upper_ne_zero τ]
    rw [hz, jacobiTheta₂_neg_left]
  have h_exp :
      Complex.exp (π * Complex.I * (-1 / (τ : ℂ)) / 4) = e := by
    dsimp [e]
    congr 1
    field_simp [upper_ne_zero τ]
  have h_fe :
      theta4 (τ : ℂ) = (1 / f) * e * A := by
    have h := jacobiTheta₂_functional_equation (1 / 2 : ℂ) (τ : ℂ)
    have h_exp_arg :
        Complex.exp (-(π * Complex.I * (2 ^ 2 : ℂ)⁻¹) / (τ : ℂ)) = e := by
      dsimp [e]
      congr 1
      field_simp [upper_ne_zero τ]
      norm_num
    simpa [theta4, f, A, thetaSFactor, h_exp_arg] using h
  calc
    theta2 (((ModularGroup.S • τ : _root_.UpperHalfPlane) : ℂ))
        = e * A := by
          rw [theta2, modular_S_coe, h_exp, h_even]
    _ = f * theta4 (τ : ℂ) := by
          rw [h_fe]
          field_simp [hf]

/-- `theta4(-1/τ) = (-iτ)^(1/2) theta2(τ)`. -/
theorem theta4_S (τ : _root_.UpperHalfPlane) :
    theta4 (((ModularGroup.S • τ : _root_.UpperHalfPlane) : ℂ)) =
      thetaSFactor (τ : ℂ) * theta2 (τ : ℂ) := by
  let f := thetaSFactor (τ : ℂ)
  let B : ℂ := jacobiTheta₂ (1 / 2 : ℂ) (-1 / (τ : ℂ))
  have hf : f ≠ 0 := by
    dsimp [f]
    exact thetaSFactor_ne_zero τ
  have h_exp :
      Complex.exp (π * Complex.I * (τ : ℂ) / 4) *
          (1 / f * Complex.exp (-π * Complex.I * ((τ : ℂ) / 2) ^ 2 / (τ : ℂ)) * B) =
        (1 / f) * B := by
    have ht : (τ : ℂ) ≠ 0 := upper_ne_zero τ
    have hcancel :
        π * Complex.I * (τ : ℂ) / 4 +
            (-π * Complex.I * ((τ : ℂ) / 2) ^ 2 / (τ : ℂ)) = 0 := by
      field_simp [ht]
      norm_num
    calc
      Complex.exp (π * Complex.I * (τ : ℂ) / 4) *
          (1 / f * Complex.exp (-π * Complex.I * ((τ : ℂ) / 2) ^ 2 / (τ : ℂ)) * B)
          =
            (1 / f) *
              (Complex.exp (π * Complex.I * (τ : ℂ) / 4) *
                Complex.exp (-π * Complex.I * ((τ : ℂ) / 2) ^ 2 / (τ : ℂ))) * B := by ring
      _ = (1 / f) * B := by
            rw [← Complex.exp_add, hcancel, Complex.exp_zero]
            ring
  have h_fe :
      theta2 (τ : ℂ) = (1 / f) * B := by
    have h := jacobiTheta₂_functional_equation ((τ : ℂ) / 2) (τ : ℂ)
    rw [theta2, h]
    dsimp [f, B, thetaSFactor]
    have h_arg :
        jacobiTheta₂ (((τ : ℂ) / 2) / (τ : ℂ)) (-1 / (τ : ℂ)) = B := by
      dsimp [B]
      congr 1
      field_simp [upper_ne_zero τ]
    rw [h_arg]
    exact h_exp
  calc
    theta4 (((ModularGroup.S • τ : _root_.UpperHalfPlane) : ℂ))
        = B := by rw [theta4, modular_S_coe]
    _ = f * theta2 (τ : ℂ) := by
          rw [h_fe]
          field_simp [hf]

/-- The theta-product transforms with factor `(-iτ)^(3/2)`. -/
theorem theta_product_S (τ : _root_.UpperHalfPlane) :
    theta2 (((ModularGroup.S • τ : _root_.UpperHalfPlane) : ℂ)) *
        theta3 (((ModularGroup.S • τ : _root_.UpperHalfPlane) : ℂ)) *
        theta4 (((ModularGroup.S • τ : _root_.UpperHalfPlane) : ℂ)) =
      (thetaSFactor (τ : ℂ)) ^ 3 *
        (theta2 (τ : ℂ) * theta3 (τ : ℂ) * theta4 (τ : ℂ)) := by
  rw [theta2_S, theta3_S, theta4_S]
  ring

/-- The theta-product discriminant transforms as a weight-12 form under `S`. -/
theorem thetaDelta_S (τ : _root_.UpperHalfPlane) :
    thetaDelta (((ModularGroup.S • τ : _root_.UpperHalfPlane) : ℂ)) =
      (τ : ℂ) ^ 12 * thetaDelta (τ : ℂ) := by
  rw [thetaDelta, thetaDelta, theta_product_S]
  rw [show ((thetaSFactor (τ : ℂ)) ^ 3 *
        (theta2 (τ : ℂ) * theta3 (τ : ℂ) * theta4 (τ : ℂ))) ^ 8 =
        (thetaSFactor (τ : ℂ)) ^ 24 *
          (theta2 (τ : ℂ) * theta3 (τ : ℂ) * theta4 (τ : ℂ)) ^ 8 by ring]
  rw [thetaSFactor_pow_twenty_four]
  ring

/-- The Jacobi product bridge: `eta^24` equals the theta-product discriminant. -/
theorem EtaPow24ThetaDeltaFormula (τ : _root_.UpperHalfPlane) :
    ModularForm.eta (τ : ℂ) ^ 24 = thetaDelta (τ : ℂ) := by
  have hprod :
      theta2 (τ : ℂ) * theta3 (τ : ℂ) * theta4 (τ : ℂ) =
        2 * ModularForm.eta (τ : ℂ) ^ 3 := by
    rw [theta_product_eq_two_exp_mul_evenProduct τ,
      eta_pow_three_eq_exp_mul_evenProduct τ]
    ring
  rw [thetaDelta, hprod]
  ring

/-- Consequence of the theta calculation and the eta/theta product formula. -/
theorem eta_pow_twenty_four_S_of_thetaDelta (τ : _root_.UpperHalfPlane) :
    ModularForm.eta (((ModularGroup.S • τ : _root_.UpperHalfPlane) : ℂ)) ^ 24 =
      (τ : ℂ) ^ 12 * ModularForm.eta (τ : ℂ) ^ 24 := by
  rw [EtaPow24ThetaDeltaFormula (ModularGroup.S • τ), thetaDelta_S,
    ← EtaPow24ThetaDeltaFormula τ]

/-- The global analytic branch statement needed for the full eta S-transform. -/
def GlobalEtaSBranchFormula : Prop :=
  (∀ τ : _root_.UpperHalfPlane,
    ModularForm.eta (((ModularGroup.S • τ : _root_.UpperHalfPlane) : ℂ)) ^ 24 =
      (thetaSFactor (τ : ℂ) * ModularForm.eta (τ : ℂ)) ^ 24) →
    ∀ τ : _root_.UpperHalfPlane,
      ModularForm.eta (((ModularGroup.S • τ : _root_.UpperHalfPlane) : ℂ)) =
        thetaSFactor (τ : ℂ) * ModularForm.eta (τ : ℂ)

private theorem eta_pow_twenty_four_target
    (τ : _root_.UpperHalfPlane) :
    ModularForm.eta (((ModularGroup.S • τ : _root_.UpperHalfPlane) : ℂ)) ^ 24 =
      (thetaSFactor (τ : ℂ) * ModularForm.eta (τ : ℂ)) ^ 24 := by
  rw [eta_pow_twenty_four_S_of_thetaDelta]
  rw [mul_pow, thetaSFactor_pow_twenty_four]

/-- Eta S-transform, reduced to the branch step. -/
theorem eta_S_transform_of_thetaDelta_and_branch
    (h_branch : GlobalEtaSBranchFormula) (τ : _root_.UpperHalfPlane) :
    ModularForm.eta (((ModularGroup.S • τ : _root_.UpperHalfPlane) : ℂ)) =
      thetaSFactor (τ : ℂ) * ModularForm.eta (τ : ℂ) :=
  h_branch eta_pow_twenty_four_target τ

/-! ## Local branch extraction at `τ = 5i` -/

private noncomputable def tau5 : _root_.UpperHalfPlane :=
  _root_.UpperHalfPlane.mk ((5 : ℂ) * Complex.I) (by norm_num)

private theorem tau5_coe :
    ((tau5 : _root_.UpperHalfPlane) : ℂ) = (5 : ℂ) * Complex.I :=
  rfl

private theorem tau5_S_coe :
    ((ModularGroup.S • tau5 : _root_.UpperHalfPlane) : ℂ) = Complex.I / 5 := by
  rw [_root_.UpperHalfPlane.modular_S_smul]
  change (-(tau5 : ℂ))⁻¹ = Complex.I / 5
  rw [tau5_coe]
  field_simp [Complex.I_mul_I]
  rw [sq, Complex.I_mul_I]

private theorem thetaSFactor_tau5 :
    thetaSFactor ((tau5 : _root_.UpperHalfPlane) : ℂ) = (Real.sqrt 5 : ℂ) := by
  rw [thetaSFactor, tau5_coe]
  rw [show -Complex.I * ((5 : ℂ) * Complex.I) = (5 : ℂ) by
    ring_nf
    simp]
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num]
  change (((5 : ℝ) : ℂ) ^ ((1 / 2 : ℝ) : ℂ)) = (Real.sqrt 5 : ℂ)
  have h := Complex.ofReal_cpow (x := (5 : ℝ)) (by norm_num) (1 / 2 : ℝ)
  rw [← h]
  rw [← Real.sqrt_eq_rpow]

private theorem qParam_twenty_four_imag_eq (t : ℝ) :
    Function.Periodic.qParam 24 (((t : ℂ) * Complex.I)) =
      ((Real.exp (-(2 * Real.pi * t / 24))) : ℂ) := by
  rw [Function.Periodic.qParam]
  change Complex.exp
      (2 * (Real.pi : ℂ) * Complex.I * ((t : ℂ) * Complex.I) / (24 : ℂ)) =
    ((Real.exp (-(2 * Real.pi * t / 24))) : ℂ)
  have harg :
      2 * (Real.pi : ℂ) * Complex.I * ((t : ℂ) * Complex.I) / (24 : ℂ) =
        ((-(2 * Real.pi * t / 24) : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
    ring
  rw [harg, Complex.ofReal_exp]

private theorem eta_q_imag_eq (n : ℕ) (t : ℝ) :
    ModularForm.eta_q n (((t : ℂ) * Complex.I)) =
      ((Real.exp (-(2 * Real.pi * (n + 1) * t))) : ℂ) := by
  rw [ModularForm.eta_q_eq_cexp]
  have harg :
      2 * (Real.pi : ℂ) * Complex.I * (n + 1 : ℂ) * ((t : ℂ) * Complex.I) =
        ((-(2 * Real.pi * (n + 1) * t) : ℝ) : ℂ) := by
    simp [Complex.ext_iff]
  rw [harg, Complex.ofReal_exp]

private noncomputable def realEtaProduct (t : ℝ) : ℝ :=
  ∏' n : ℕ, (1 - Real.exp (-(2 * Real.pi * (n + 1) * t)))

private noncomputable def etaImagRealValue (t : ℝ) : ℝ :=
  Real.exp (-(2 * Real.pi * t / 24)) * realEtaProduct t

private theorem summable_exp_eta_imag (t : ℝ) (ht : 0 < t) :
    Summable fun n : ℕ => Real.exp (-(2 * Real.pi * (n + 1) * t)) := by
  have hpos : 0 < 2 * Real.pi * t := by positivity
  have hc : -(2 * Real.pi * t) < 0 := by linarith
  have hs := Real.summable_exp_nat_mul_of_ge (c := -(2 * Real.pi * t)) hc
    (f := fun i : ℕ => (i + 1 : ℝ)) (by intro i; norm_num)
  convert hs using 1
  ext n
  ring_nf

private theorem realEtaProduct_pos (t : ℝ) (ht : 0 < t) :
    0 < realEtaProduct t := by
  have hsumexp := summable_exp_eta_imag t ht
  have hsumneg :
      Summable fun n : ℕ => -Real.exp (-(2 * Real.pi * (n + 1) * t)) :=
    hsumexp.neg
  have hfacpos :
      ∀ n : ℕ, 0 < 1 + -Real.exp (-(2 * Real.pi * (n + 1) * t)) := by
    intro n
    change 0 < 1 - Real.exp (-(2 * Real.pi * (n + 1) * t))
    refine sub_pos.mpr ?_
    rw [Real.exp_lt_one_iff]
    have hpos : 0 < 2 * Real.pi * (n + 1 : ℝ) * t := by positivity
    linarith
  have hlog := Real.summable_log_one_add_of_summable hsumneg
  have htp := Real.rexp_tsum_eq_tprod hfacpos hlog
  dsimp [realEtaProduct]
  rw [show (∏' n : ℕ, (1 - Real.exp (-(2 * Real.pi * (n + 1) * t)))) =
      ∏' n : ℕ, (1 + -Real.exp (-(2 * Real.pi * (n + 1) * t))) by
    refine tprod_congr fun n => by ring]
  rw [← htp]
  positivity

private theorem etaImagRealValue_pos (t : ℝ) (ht : 0 < t) :
    0 < etaImagRealValue t := by
  dsimp [etaImagRealValue]
  exact mul_pos (Real.exp_pos _) (realEtaProduct_pos t ht)

private theorem eta_imag_eq_ofReal (t : ℝ) :
    ModularForm.eta (((t : ℂ) * Complex.I)) = (etaImagRealValue t : ℂ) := by
  rw [ModularForm.eta, qParam_twenty_four_imag_eq]
  have hprod_map :
      (((∏' n : ℕ,
          (1 - Real.exp (-(2 * Real.pi * (n + 1) * t))) : ℝ)) : ℂ) =
        ∏' n : ℕ,
          (((1 - Real.exp (-(2 * Real.pi * (n + 1) * t))) : ℝ) : ℂ) := by
    simpa using (Topology.IsClosedEmbedding.map_tprod
      (f := fun n : ℕ => (1 - Real.exp (-(2 * Real.pi * (n + 1) * t)) : ℝ))
      (g := (algebraMap ℝ ℂ)) Complex.isUniformEmbedding_ofReal.isClosedEmbedding)
  have hprod :
      (∏' n : ℕ, (1 - ModularForm.eta_q n (((t : ℂ) * Complex.I)))) =
        (((∏' n : ℕ,
          (1 - Real.exp (-(2 * Real.pi * (n + 1) * t))) : ℝ)) : ℂ) := by
    rw [hprod_map]
    refine tprod_congr fun n => ?_
    rw [eta_q_imag_eq]
    norm_num
  rw [hprod]
  rw [← Complex.ofReal_mul]
  rfl

/-- Local branch extraction for eta at `τ = 5i`.  This is the Chapter 12
special case of the eta S-transform and does not assert the global branch. -/
theorem EtaSBranchFormula :
    ModularForm.eta (Complex.I / 5) =
      (Real.sqrt 5 : ℂ) * ModularForm.eta ((5 : ℂ) * Complex.I) := by
  have hpow := eta_pow_twenty_four_target tau5
  rw [tau5_S_coe, thetaSFactor_tau5, tau5_coe] at hpow
  have hleft :
      ModularForm.eta (Complex.I / 5) = (etaImagRealValue (1 / 5) : ℂ) := by
    have h := eta_imag_eq_ofReal (1 / 5)
    convert h using 1
    norm_num [div_eq_mul_inv]
    ring_nf
  have hright_eta :
      ModularForm.eta ((5 : ℂ) * Complex.I) = (etaImagRealValue 5 : ℂ) := by
    simpa using eta_imag_eq_ofReal 5
  have hright :
      (Real.sqrt 5 : ℂ) * ModularForm.eta ((5 : ℂ) * Complex.I) =
        ((Real.sqrt 5 * etaImagRealValue 5 : ℝ) : ℂ) := by
    rw [hright_eta, ← Complex.ofReal_mul]
  have hleft_pos : 0 < etaImagRealValue (1 / 5) := by
    exact etaImagRealValue_pos (1 / 5) (by norm_num)
  have hright_pos : 0 < Real.sqrt 5 * etaImagRealValue 5 := by
    exact mul_pos (Real.sqrt_pos.mpr (by norm_num)) (etaImagRealValue_pos 5 (by norm_num))
  have hpow_realC :
      (((etaImagRealValue (1 / 5)) ^ 24 : ℝ) : ℂ) =
        (((Real.sqrt 5 * etaImagRealValue 5) ^ 24 : ℝ) : ℂ) := by
    simpa [hleft, hright, Complex.ofReal_pow] using hpow
  have hpow_real :
      (etaImagRealValue (1 / 5)) ^ 24 =
        (Real.sqrt 5 * etaImagRealValue 5) ^ 24 :=
    Complex.ofReal_injective hpow_realC
  have hreal :
      etaImagRealValue (1 / 5) = Real.sqrt 5 * etaImagRealValue 5 :=
    (pow_left_inj₀ hleft_pos.le hright_pos.le (by norm_num : (24 : ℕ) ≠ 0)).mp hpow_real
  rw [hleft, hright, hreal]

end EtaSTransform
end Pending
end QseriesFormalization
