import QseriesFormalization.Pending.Chapter12_SpecialValue
import QseriesFormalization.Pending.EtaSTransform
import QseriesFormalization.Pending.RamanujanQuinticJTP
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# Chan Theorem 11.4

This file packages the analytic Rogers-Ramanujan continued-fraction product
value at `q = exp (-2π)` and proves the final quadratic algebra used in
Chan's Theorem 11.4.
-/

namespace QseriesFormalization
namespace Pending
namespace ChanTheorem114

open Complex
open Filter
open scoped Topology

open QseriesFormalization.PartI.Ch04
open QseriesFormalization.Pending.JTPFormalPSPentagonal
open QseriesFormalization.Pending.RamanujanQuintic
open QseriesFormalization.Pending.RamanujanQuinticJTP
open QseriesFormalization.Pending.Ch12SpecialValue

noncomputable def rrcfRProductAtFifthRoot (q : ℂ) : ℂ :=
  q * pentagonal014Analytic (q ^ 5) / pentagonal023Analytic (q ^ 5)

noncomputable def expNegTwoPiFifth : ℂ :=
  (Real.exp (-(2 * Real.pi / 5)) : ℂ)

noncomputable def rrcfR_exp_neg_two_pi : ℂ :=
  rrcfRProductAtFifthRoot expNegTwoPiFifth

private theorem inv_eq_pow_four_of_primitive_fifth {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ 5) :
    ζ⁻¹ = ζ ^ 4 := by
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by norm_num)
  apply mul_left_cancel₀ hζ0
  calc
    ζ * ζ⁻¹ = 1 := by rw [mul_inv_cancel₀ hζ0]
    _ = ζ ^ 5 := hζ.pow_eq_one.symm
    _ = ζ * ζ ^ 4 := by ring

private theorem inv_sq_eq_pow_three_of_primitive_fifth {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ 5) :
    (ζ ^ 2)⁻¹ = ζ ^ 3 := by
  have hζ2 : IsPrimitiveRoot (ζ ^ 2) 5 :=
    hζ.pow_of_coprime 2 (by norm_num)
  have h := inv_eq_pow_four_of_primitive_fifth hζ2
  have hpow : (ζ ^ 2) ^ 4 = ζ ^ 3 := by
    calc
      (ζ ^ 2) ^ 4 = ζ ^ 8 := by ring
      _ = ζ ^ (5 + 3) := by norm_num
      _ = ζ ^ 5 * ζ ^ 3 := by rw [pow_add]
      _ = ζ ^ 3 := by rw [hζ.pow_eq_one, one_mul]
  rw [h, hpow]

private theorem section83_pair_factor_eq_euler
    {ζ q : ℂ} (hζ : IsPrimitiveRoot ζ 5) (n : ℕ) :
    section83JTPTripleFactorAnalytic ζ q n *
        section83JTPTripleFactorAnalytic (ζ ^ 2) q n =
      eulerPentagonalProductFactor q n *
        eulerPentagonalProductFactor (q ^ 5) n := by
  let y : ℂ := q ^ (n + 1)
  have hprod := prod_one_sub_primitive_fifth (A := ℂ) (μ := ζ) (y := y) hζ
  norm_num [Fin.prod_univ_five] at hprod
  have hprod' :
      (1 - y) * (1 - ζ * y) * (1 - ζ ^ 2 * y) *
          (1 - ζ ^ 3 * y) * (1 - ζ ^ 4 * y) =
        1 - y ^ 5 := by
    simpa [pow_zero, pow_one, mul_assoc] using hprod
  have hy5 : (q ^ 5) ^ (n + 1) = y ^ 5 := by
    dsimp [y]
    rw [← pow_mul, ← pow_mul]
    congr 1
    omega
  dsimp [y] at hprod'
  simp only [section83JTPTripleFactorAnalytic, constQFactorAnalytic,
    eulerPentagonalProductFactor, inv_eq_pow_four_of_primitive_fifth hζ,
    inv_sq_eq_pow_three_of_primitive_fifth hζ, hy5, one_mul]
  calc
    (1 - q ^ (n + 1)) * (1 - ζ * q ^ (n + 1)) *
          (1 - ζ ^ 4 * q ^ (n + 1)) *
        ((1 - q ^ (n + 1)) * (1 - ζ ^ 2 * q ^ (n + 1)) *
          (1 - ζ ^ 3 * q ^ (n + 1))) =
        (1 - q ^ (n + 1)) *
          ((1 - q ^ (n + 1)) * (1 - ζ * q ^ (n + 1)) *
            (1 - ζ ^ 2 * q ^ (n + 1)) *
            (1 - ζ ^ 3 * q ^ (n + 1)) *
            (1 - ζ ^ 4 * q ^ (n + 1))) := by ring
    _ = (1 - q ^ (n + 1)) * (1 - (q ^ (n + 1)) ^ 5) := by
      rw [hprod']
    _ = (1 - q ^ (n + 1)) * (1 - (q ^ (n + 1)) ^ 5) := rfl

private theorem norm_pow_lt_one {q : ℂ} (hq : ‖q‖ < 1) {n : ℕ} (hn : n ≠ 0) :
    ‖q ^ n‖ < 1 := by
  rw [norm_pow]
  exact pow_lt_one₀ (norm_nonneg q) hq hn

private theorem section83_pair_product_eq_euler
    {ζ q : ℂ} (hζ : IsPrimitiveRoot ζ 5) (hq : ‖q‖ < 1) :
    section83JTPProductAnalytic ζ q *
        section83JTPProductAnalytic (ζ ^ 2) q =
      eulerPentagonalInfiniteProduct q *
        eulerPentagonalInfiniteProduct (q ^ 5) := by
  have hq5 : ‖q ^ 5‖ < 1 := norm_pow_lt_one hq (by norm_num)
  have hleft :
      Tendsto
        (fun N : ℕ =>
          (∏ n ∈ Finset.range N, section83JTPTripleFactorAnalytic ζ q n) *
            (∏ n ∈ Finset.range N, section83JTPTripleFactorAnalytic (ζ ^ 2) q n))
        atTop
        (𝓝 (section83JTPProductAnalytic ζ q *
          section83JTPProductAnalytic (ζ ^ 2) q)) :=
    (tendsto_section83JTPProductAnalytic_partial ζ q hq).mul
      (tendsto_section83JTPProductAnalytic_partial (ζ ^ 2) q hq)
  have hright :
      Tendsto
        (fun N : ℕ =>
          (∏ n ∈ Finset.range N, eulerPentagonalProductFactor q n) *
            (∏ n ∈ Finset.range N, eulerPentagonalProductFactor (q ^ 5) n))
        atTop
        (𝓝 (eulerPentagonalInfiniteProduct q *
          eulerPentagonalInfiniteProduct (q ^ 5))) :=
    (multipliable_eulerPentagonalProductFactor q hq).tendsto_prod_tprod_nat.mul
      (multipliable_eulerPentagonalProductFactor (q ^ 5) hq5).tendsto_prod_tprod_nat
  have hpartial : ∀ N : ℕ,
      (∏ n ∈ Finset.range N, section83JTPTripleFactorAnalytic ζ q n) *
          (∏ n ∈ Finset.range N, section83JTPTripleFactorAnalytic (ζ ^ 2) q n) =
        (∏ n ∈ Finset.range N, eulerPentagonalProductFactor q n) *
          (∏ n ∈ Finset.range N, eulerPentagonalProductFactor (q ^ 5) n) := by
    intro N
    calc
      (∏ n ∈ Finset.range N, section83JTPTripleFactorAnalytic ζ q n) *
          (∏ n ∈ Finset.range N, section83JTPTripleFactorAnalytic (ζ ^ 2) q n) =
          ∏ n ∈ Finset.range N,
            (section83JTPTripleFactorAnalytic ζ q n *
              section83JTPTripleFactorAnalytic (ζ ^ 2) q n) := by
            rw [Finset.prod_mul_distrib]
      _ = ∏ n ∈ Finset.range N,
            (eulerPentagonalProductFactor q n *
              eulerPentagonalProductFactor (q ^ 5) n) := by
            refine Finset.prod_congr rfl fun n _ => ?_
            exact section83_pair_factor_eq_euler hζ n
      _ = (∏ n ∈ Finset.range N, eulerPentagonalProductFactor q n) *
          (∏ n ∈ Finset.range N, eulerPentagonalProductFactor (q ^ 5) n) := by
            rw [Finset.prod_mul_distrib]
  have hleft_rhs :
      Tendsto
        (fun N : ℕ =>
          (∏ n ∈ Finset.range N, eulerPentagonalProductFactor q n) *
            (∏ n ∈ Finset.range N, eulerPentagonalProductFactor (q ^ 5) n))
        atTop
        (𝓝 (section83JTPProductAnalytic ζ q *
          section83JTPProductAnalytic (ζ ^ 2) q)) := by
    refine hleft.congr' ?_
    exact Eventually.of_forall fun N => hpartial N
  exact tendsto_nhds_unique hleft_rhs hright

private theorem chan_theorem_11_3_analytic
    {ζ q : ℂ} (hζ : IsPrimitiveRoot ζ 5) (hq : ‖q‖ < 1) :
    (pentagonal023Analytic (q ^ 5)) ^ 2 -
        q * pentagonal023Analytic (q ^ 5) * pentagonal014Analytic (q ^ 5) -
        q ^ 2 * (pentagonal014Analytic (q ^ 5)) ^ 2 =
      eulerPentagonalInfiniteProduct q *
        eulerPentagonalInfiniteProduct (q ^ 5) := by
  let G : ℂ := pentagonal023Analytic (q ^ 5)
  let H : ℂ := pentagonal014Analytic (q ^ 5)
  let α : ℂ := quinticPeriodAlpha ζ
  let β : ℂ := quinticPeriodBeta ζ
  have hsum : α + β = -1 := by
    dsimp [α, β]
    exact quinticPeriod_sum (R := ℂ) hζ
  have hmul : α * β = -1 := by
    dsimp [α, β]
    exact quinticPeriod_mul (R := ℂ) hζ
  have hsum' : β + α = -1 := by
    rw [add_comm, hsum]
  have hmul' : β * α = -1 := by
    rw [mul_comm, hmul]
  have halg :
      (G + β * q * H) * (G + α * q * H) =
        G ^ 2 - q * G * H - q ^ 2 * H ^ 2 := by
    calc
      (G + β * q * H) * (G + α * q * H) =
          G ^ 2 + (β + α) * q * G * H + (β * α) * q ^ 2 * H ^ 2 := by ring
      _ = G ^ 2 - q * G * H - q ^ 2 * H ^ 2 := by
        rw [hsum', hmul']
        ring
  have hprod := section83_pair_product_eq_euler hζ hq
  have h14 := section83JTPProductAnalytic_eq_rhs_pair14_eval hζ hq
  have h23 := section83JTPProductAnalytic_eq_rhs_pair23_eval hζ hq
  dsimp [G, H, α, β] at halg
  rw [h14, h23] at hprod
  rw [← halg]
  exact hprod

private theorem tprod_rrMod5Factor_five_eq_euler_fifth (q : ℂ) :
    (∏' n : ℕ, rrMod5Factor q 5 n) =
      eulerPentagonalInfiniteProduct (q ^ 5) := by
  unfold eulerPentagonalInfiniteProduct
  refine tprod_congr fun n => ?_
  unfold rrMod5Factor eulerPentagonalProductFactor
  rw [show 5 + 5 * n = 5 * (n + 1) by omega, pow_mul]

private theorem pentagonal014_mul_pentagonal023_eq_euler_mul_euler_fifth
    (q : ℂ) (hq : ‖q‖ < 1) :
    pentagonal014Analytic q * pentagonal023Analytic q =
      eulerPentagonalInfiniteProduct q *
        eulerPentagonalInfiniteProduct (q ^ 5) := by
  have h014 := pentagonal014ProductAnalytic_eq_pentagonal014Analytic q hq
  have h023 := pentagonal023ProductAnalytic_eq_pentagonal023Analytic q hq
  have hE := eulerPentagonalInfiniteProduct_eq_mod5_regroup q hq
  have h5 := tprod_rrMod5Factor_five_eq_euler_fifth q
  rw [← h014, ← h023, hE, ← h5]
  unfold pentagonal014ProductAnalytic pentagonal023ProductAnalytic
  ring

private theorem pentagonal014Analytic_ne_zero (q : ℂ) (hq : ‖q‖ < 1) :
    pentagonal014Analytic q ≠ 0 := by
  have h := pentagonal014ProductAnalytic_eq_pentagonal014Analytic q hq
  rw [← h]
  unfold pentagonal014ProductAnalytic
  refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
  · exact tprod_rrMod5Factor_ne_zero q hq 5 (by norm_num)
  · exact tprod_rrMod5Factor_ne_zero q hq 4 (by norm_num)
  · exact tprod_rrMod5Factor_ne_zero q hq 1 (by norm_num)

private theorem pentagonal023Analytic_ne_zero (q : ℂ) (hq : ‖q‖ < 1) :
    pentagonal023Analytic q ≠ 0 := by
  have h := pentagonal023ProductAnalytic_eq_pentagonal023Analytic q hq
  rw [← h]
  unfold pentagonal023ProductAnalytic
  refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
  · exact tprod_rrMod5Factor_ne_zero q hq 5 (by norm_num)
  · exact tprod_rrMod5Factor_ne_zero q hq 3 (by norm_num)
  · exact tprod_rrMod5Factor_ne_zero q hq 2 (by norm_num)

private theorem rrcfRProductAtFifthRoot_euler_equation
    {ζ q : ℂ} (hζ : IsPrimitiveRoot ζ 5) (hq : ‖q‖ < 1) (hq0 : q ≠ 0) :
    1 / rrcfRProductAtFifthRoot q - 1 - rrcfRProductAtFifthRoot q =
      eulerPentagonalInfiniteProduct q /
        (q * eulerPentagonalInfiniteProduct (q ^ 25)) := by
  let G : ℂ := pentagonal023Analytic (q ^ 5)
  let H : ℂ := pentagonal014Analytic (q ^ 5)
  have hq5 : ‖q ^ 5‖ < 1 := norm_pow_lt_one hq (by norm_num)
  have hq25 : ‖q ^ 25‖ < 1 := norm_pow_lt_one hq (by norm_num)
  have hG0 : G ≠ 0 := by
    dsimp [G]
    exact pentagonal023Analytic_ne_zero (q ^ 5) hq5
  have hH0 : H ≠ 0 := by
    dsimp [H]
    exact pentagonal014Analytic_ne_zero (q ^ 5) hq5
  have hE5 : eulerPentagonalInfiniteProduct (q ^ 5) ≠ 0 :=
    eulerPentagonalInfiniteProduct_ne_zero (q ^ 5) hq5
  have hE25 : eulerPentagonalInfiniteProduct (q ^ 25) ≠ 0 :=
    eulerPentagonalInfiniteProduct_ne_zero (q ^ 25) hq25
  have h113 := chan_theorem_11_3_analytic hζ hq
  have hHG :=
    pentagonal014_mul_pentagonal023_eq_euler_mul_euler_fifth (q ^ 5) hq5
  have hpow25 : (q ^ 5) ^ 5 = q ^ 25 := by
    rw [← pow_mul]
  rw [hpow25] at hHG
  have hfrac :
      1 / rrcfRProductAtFifthRoot q - 1 - rrcfRProductAtFifthRoot q =
        (G ^ 2 - q * G * H - q ^ 2 * H ^ 2) / (q * H * G) := by
    dsimp [rrcfRProductAtFifthRoot]
    change 1 / (q * H / G) - 1 - q * H / G =
      (G ^ 2 - q * G * H - q ^ 2 * H ^ 2) / (q * H * G)
    field_simp [hq0, hG0, hH0]
  calc
    1 / rrcfRProductAtFifthRoot q - 1 - rrcfRProductAtFifthRoot q =
        (G ^ 2 - q * G * H - q ^ 2 * H ^ 2) / (q * H * G) := hfrac
    _ = (eulerPentagonalInfiniteProduct q *
          eulerPentagonalInfiniteProduct (q ^ 5)) / (q * H * G) := by
          dsimp [G, H]
          rw [h113]
    _ = eulerPentagonalInfiniteProduct q /
          (q * eulerPentagonalInfiniteProduct (q ^ 25)) := by
          dsimp [G, H] at hHG ⊢
          rw [show q * pentagonal014Analytic (q ^ 5) *
                pentagonal023Analytic (q ^ 5) =
                q * (pentagonal014Analytic (q ^ 5) *
                  pentagonal023Analytic (q ^ 5)) by ring,
              hHG]
          field_simp [hq0, hE5, hE25]

private theorem eta_eq_qParam_mul_eulerPentagonalInfiniteProduct (z : ℂ) :
    ModularForm.eta z =
      Function.Periodic.qParam 24 z *
        eulerPentagonalInfiniteProduct (Function.Periodic.qParam 1 z) :=
  rfl

private theorem qParam_one_imag_eq (t : ℝ) :
    Function.Periodic.qParam 1 (((t : ℂ) * Complex.I)) =
      ((Real.exp (-(2 * Real.pi * t))) : ℂ) := by
  rw [Function.Periodic.qParam]
  change Complex.exp
      (2 * (Real.pi : ℂ) * Complex.I * ((t : ℂ) * Complex.I) / (1 : ℂ)) =
    ((Real.exp (-(2 * Real.pi * t))) : ℂ)
  have harg :
      2 * (Real.pi : ℂ) * Complex.I * ((t : ℂ) * Complex.I) / (1 : ℂ) =
        ((-(2 * Real.pi * t) : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  rw [harg, Complex.ofReal_exp]

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
    ring_nf
  rw [harg, Complex.ofReal_exp]

private theorem qParam_one_i_div_five :
    Function.Periodic.qParam 1 (Complex.I / 5) = expNegTwoPiFifth := by
  have h := qParam_one_imag_eq (1 / 5)
  convert h using 2
  · norm_num [div_eq_mul_inv]
    ring_nf
  · dsimp [expNegTwoPiFifth]
    congr 1
    ring_nf

private theorem expNegTwoPiFifth_pow_twenty_five :
    expNegTwoPiFifth ^ 25 =
      ((Real.exp (-(2 * Real.pi * 5))) : ℂ) := by
  dsimp [expNegTwoPiFifth]
  rw [← Complex.ofReal_pow, ← Real.exp_nat_mul]
  congr 1
  ring_nf

private theorem qParam_one_five_i :
    Function.Periodic.qParam 1 ((5 : ℂ) * Complex.I) =
      expNegTwoPiFifth ^ 25 := by
  change Function.Periodic.qParam 1 (((5 : ℝ) : ℂ) * Complex.I) =
    expNegTwoPiFifth ^ 25
  rw [qParam_one_imag_eq 5, expNegTwoPiFifth_pow_twenty_five]

private theorem qParam_twenty_four_i_div_five :
    Function.Periodic.qParam 24 (Complex.I / 5) =
      ((Real.exp (-(2 * Real.pi * (1 / 5) / 24))) : ℂ) := by
  have h := qParam_twenty_four_imag_eq (1 / 5)
  convert h using 2
  · norm_num [div_eq_mul_inv]
    ring_nf

private theorem qParam_twenty_four_five_i :
    Function.Periodic.qParam 24 ((5 : ℂ) * Complex.I) =
      ((Real.exp (-(2 * Real.pi * 5 / 24))) : ℂ) := by
  simpa using qParam_twenty_four_imag_eq 5

private theorem expNegTwoPiFifth_ne_zero : expNegTwoPiFifth ≠ 0 := by
  dsimp [expNegTwoPiFifth]
  exact Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)

private theorem qParam_twenty_four_five_i_ne_zero :
    Function.Periodic.qParam 24 ((5 : ℂ) * Complex.I) ≠ 0 := by
  rw [qParam_twenty_four_five_i]
  exact Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)

private theorem qParam_twenty_four_ratio :
    Function.Periodic.qParam 24 (Complex.I / 5) /
        Function.Periodic.qParam 24 ((5 : ℂ) * Complex.I) =
      expNegTwoPiFifth⁻¹ := by
  rw [qParam_twenty_four_i_div_five, qParam_twenty_four_five_i]
  dsimp [expNegTwoPiFifth]
  rw [← Complex.ofReal_div, ← Complex.ofReal_inv]
  congr 1
  rw [← Real.exp_sub, ← Real.exp_neg]
  congr 1
  ring_nf

private theorem norm_expNegTwoPiFifth_lt_one : ‖expNegTwoPiFifth‖ < 1 := by
  dsimp [expNegTwoPiFifth]
  rw [Complex.ofReal_exp, Complex.norm_exp]
  simp
  positivity

private theorem eta_product_ratio_at_tau5 :
    eulerPentagonalInfiniteProduct expNegTwoPiFifth /
        (expNegTwoPiFifth *
          eulerPentagonalInfiniteProduct (expNegTwoPiFifth ^ 25)) =
      (Real.sqrt 5 : ℂ) := by
  let A : ℂ := Function.Periodic.qParam 24 (Complex.I / 5)
  let B : ℂ := Function.Periodic.qParam 24 ((5 : ℂ) * Complex.I)
  let E0 : ℂ := eulerPentagonalInfiniteProduct expNegTwoPiFifth
  let E25 : ℂ := eulerPentagonalInfiniteProduct (expNegTwoPiFifth ^ 25)
  have hq25 : ‖expNegTwoPiFifth ^ 25‖ < 1 :=
    norm_pow_lt_one norm_expNegTwoPiFifth_lt_one (by norm_num)
  have hE25 : E25 ≠ 0 := by
    dsimp [E25]
    exact eulerPentagonalInfiniteProduct_ne_zero (expNegTwoPiFifth ^ 25) hq25
  have hB : B ≠ 0 := by
    dsimp [B]
    exact qParam_twenty_four_five_i_ne_zero
  have hratio : A / B = expNegTwoPiFifth⁻¹ := by
    dsimp [A, B]
    exact qParam_twenty_four_ratio
  have heta := EtaSTransform.EtaSBranchFormula
  rw [eta_eq_qParam_mul_eulerPentagonalInfiniteProduct,
    eta_eq_qParam_mul_eulerPentagonalInfiniteProduct,
    qParam_one_i_div_five, qParam_one_five_i] at heta
  change A * E0 = (Real.sqrt 5 : ℂ) * (B * E25) at heta
  calc
    E0 / (expNegTwoPiFifth * E25) =
        expNegTwoPiFifth⁻¹ * (E0 / E25) := by
          field_simp [expNegTwoPiFifth_ne_zero, hE25]
    _ = (A / B) * (E0 / E25) := by rw [hratio]
    _ = (A * E0) / (B * E25) := by
          field_simp [hB, hE25]
    _ = (Real.sqrt 5 : ℂ) := by
          rw [heta]
          field_simp [hB, hE25]

private noncomputable def realRRMod5Product (x : ℝ) (k : ℕ) : ℝ :=
  ∏' n : ℕ, (1 - x ^ (k + 5 * n))

private theorem norm_ofReal_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    ‖((x : ℝ) : ℂ)‖ = x := by
  simp [hx]

private theorem summable_real_rrMod5_tail
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (k : ℕ) :
    Summable fun n : ℕ => -(x ^ (k + 5 * n)) := by
  have hx5 : x ^ 5 < 1 := pow_lt_one₀ hx0.le hx1 (by norm_num)
  have hgeom : Summable fun n : ℕ => (x ^ 5) ^ n :=
    summable_geometric_of_lt_one (by positivity) hx5
  have hscaled : Summable fun n : ℕ => x ^ k * (x ^ 5) ^ n :=
    hgeom.mul_left (x ^ k)
  refine hscaled.neg.congr fun n => ?_
  rw [neg_inj]
  rw [show x ^ (k + 5 * n) = x ^ k * (x ^ 5) ^ n by
    rw [pow_add, pow_mul]]

private theorem realRRMod5Product_pos
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (k : ℕ) (hk : 1 ≤ k) :
    0 < realRRMod5Product x k := by
  have hsumneg := summable_real_rrMod5_tail hx0 hx1 k
  have hfacpos :
      ∀ n : ℕ, 0 < 1 + -(x ^ (k + 5 * n)) := by
    intro n
    change 0 < 1 - x ^ (k + 5 * n)
    refine sub_pos.mpr ?_
    exact pow_lt_one₀ hx0.le hx1 (by omega)
  have hlog := Real.summable_log_one_add_of_summable hsumneg
  have htp := Real.rexp_tsum_eq_tprod hfacpos hlog
  dsimp [realRRMod5Product]
  rw [show (∏' n : ℕ, (1 - x ^ (k + 5 * n))) =
      ∏' n : ℕ, (1 + -(x ^ (k + 5 * n))) by
    refine tprod_congr fun n => by ring]
  rw [← htp]
  positivity

private theorem tprod_rrMod5Factor_ofReal (x : ℝ) (k : ℕ) :
    (∏' n : ℕ, rrMod5Factor ((x : ℝ) : ℂ) k n) =
      ((realRRMod5Product x k : ℝ) : ℂ) := by
  have hprod_map :
      (((∏' n : ℕ, (1 - x ^ (k + 5 * n))) : ℝ) : ℂ) =
        ∏' n : ℕ, (((1 - x ^ (k + 5 * n)) : ℝ) : ℂ) := by
    simpa using (Topology.IsClosedEmbedding.map_tprod
      (f := fun n : ℕ => (1 - x ^ (k + 5 * n) : ℝ))
      (g := (algebraMap ℝ ℂ)) Complex.isUniformEmbedding_ofReal.isClosedEmbedding)
  dsimp [realRRMod5Product]
  rw [hprod_map]
  refine tprod_congr fun n => ?_
  simp [Complex.ofReal_pow]

private theorem ofReal_norm_lt_one {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    ‖((x : ℝ) : ℂ)‖ < 1 := by
  rw [norm_ofReal_of_nonneg hx0.le]
  exact hx1

private theorem pentagonal014Analytic_ofReal_pos
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    ∃ y : ℝ, 0 < y ∧ pentagonal014Analytic ((x : ℝ) : ℂ) = (y : ℂ) := by
  have hq : ‖((x : ℝ) : ℂ)‖ < 1 := ofReal_norm_lt_one hx0 hx1
  have hprod := pentagonal014ProductAnalytic_eq_pentagonal014Analytic ((x : ℝ) : ℂ) hq
  let P5 : ℝ := realRRMod5Product x 5
  let P4 : ℝ := realRRMod5Product x 4
  let P1 : ℝ := realRRMod5Product x 1
  refine ⟨P5 * P4 * P1, ?_, ?_⟩
  · exact mul_pos (mul_pos
      (realRRMod5Product_pos hx0 hx1 5 (by norm_num))
      (realRRMod5Product_pos hx0 hx1 4 (by norm_num)))
      (realRRMod5Product_pos hx0 hx1 1 (by norm_num))
  · rw [← hprod]
    unfold pentagonal014ProductAnalytic
    rw [tprod_rrMod5Factor_ofReal x 5, tprod_rrMod5Factor_ofReal x 4,
      tprod_rrMod5Factor_ofReal x 1]
    simp [P5, P4, P1]

private theorem pentagonal023Analytic_ofReal_pos
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    ∃ y : ℝ, 0 < y ∧ pentagonal023Analytic ((x : ℝ) : ℂ) = (y : ℂ) := by
  have hq : ‖((x : ℝ) : ℂ)‖ < 1 := ofReal_norm_lt_one hx0 hx1
  have hprod := pentagonal023ProductAnalytic_eq_pentagonal023Analytic ((x : ℝ) : ℂ) hq
  let P5 : ℝ := realRRMod5Product x 5
  let P3 : ℝ := realRRMod5Product x 3
  let P2 : ℝ := realRRMod5Product x 2
  refine ⟨P5 * P3 * P2, ?_, ?_⟩
  · exact mul_pos (mul_pos
      (realRRMod5Product_pos hx0 hx1 5 (by norm_num))
      (realRRMod5Product_pos hx0 hx1 3 (by norm_num)))
      (realRRMod5Product_pos hx0 hx1 2 (by norm_num))
  · rw [← hprod]
    unfold pentagonal023ProductAnalytic
    rw [tprod_rrMod5Factor_ofReal x 5, tprod_rrMod5Factor_ofReal x 3,
      tprod_rrMod5Factor_ofReal x 2]
    simp [P5, P3, P2]

private theorem rrcfR_exp_neg_two_pi_ofReal_pos :
    ∃ x : ℝ, 0 < x ∧ rrcfR_exp_neg_two_pi = (x : ℂ) := by
  let a : ℝ := Real.exp (-(2 * Real.pi / 5))
  have ha0 : 0 < a := Real.exp_pos _
  have ha1 : a < 1 := by
    dsimp [a]
    rw [Real.exp_lt_one_iff]
    have hpos : 0 < 2 * Real.pi / 5 := by positivity
    linarith
  have h014 := pentagonal014Analytic_ofReal_pos
    (x := a ^ 5) (by positivity) (pow_lt_one₀ ha0.le ha1 (by norm_num))
  have h023 := pentagonal023Analytic_ofReal_pos
    (x := a ^ 5) (by positivity) (pow_lt_one₀ ha0.le ha1 (by norm_num))
  rcases h014 with ⟨H, hHpos, hH⟩
  rcases h023 with ⟨G, hGpos, hG⟩
  refine ⟨a * H / G, div_pos (mul_pos ha0 hHpos) hGpos, ?_⟩
  have hG0 : (G : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt hGpos)
  dsimp [rrcfR_exp_neg_two_pi, rrcfRProductAtFifthRoot, expNegTwoPiFifth, a]
  rw [show (((Real.exp (-(2 * Real.pi / 5)) : ℝ) : ℂ) ^ 5) =
        ((a ^ 5 : ℝ) : ℂ) by
      dsimp [a]
      rw [Complex.ofReal_pow]]
  rw [hH, hG, ← Complex.ofReal_mul, ← Complex.ofReal_div]

private theorem sqrt_five_sq : (Real.sqrt 5) ^ 2 = (5 : ℝ) := by
  rw [Real.sq_sqrt (by norm_num)]

private theorem special_value_pos : 0 < ramanujanRRCFSpecialValue := by
  let s : ℝ := Real.sqrt 5
  let b : ℝ := (1 + s) / 2
  let t : ℝ := Real.sqrt ((5 + s) / 2)
  have hs2 : s ^ 2 = 5 := by
    dsimp [s]
    exact sqrt_five_sq
  have hb_nonneg : 0 ≤ b := by
    dsimp [b, s]
    positivity
  have ht_sq : t ^ 2 = (5 + s) / 2 := by
    dsimp [t]
    rw [Real.sq_sqrt]
    positivity
  have hb_sq : b ^ 2 = (3 + s) / 2 := by
    dsimp [b]
    nlinarith
  have hb_lt_t : b < t := by
    calc
      b = Real.sqrt (b ^ 2) := (Real.sqrt_sq hb_nonneg).symm
      _ < Real.sqrt ((5 + s) / 2) := by
        apply Real.sqrt_lt_sqrt
        · positivity
        · nlinarith
      _ = t := rfl
  dsimp [ramanujanRRCFSpecialValue, t, b, s] at hb_lt_t ⊢
  linarith

private theorem special_value_quadratic :
    ramanujanRRCFSpecialValue ^ 2 +
        (1 + Real.sqrt 5) * ramanujanRRCFSpecialValue - 1 = 0 := by
  let s : ℝ := Real.sqrt 5
  let b : ℝ := (1 + s) / 2
  let t : ℝ := Real.sqrt ((5 + s) / 2)
  have hs2 : s ^ 2 = 5 := by
    dsimp [s]
    exact sqrt_five_sq
  have ht_sq : t ^ 2 = (5 + s) / 2 := by
    dsimp [t]
    rw [Real.sq_sqrt]
    positivity
  dsimp [ramanujanRRCFSpecialValue, t, b, s]
  nlinarith

private theorem positive_quadratic_solution_unique
    {x y a : ℝ} (ha : 0 ≤ a) (hxpos : 0 < x) (hypos : 0 < y)
    (hx : x ^ 2 + a * x - 1 = 0) (hy : y ^ 2 + a * y - 1 = 0) :
    x = y := by
  have hsub : (x - y) * (x + y + a) = 0 := by
    nlinarith
  have hfacpos : 0 < x + y + a := by
    linarith
  rcases mul_eq_zero.mp hsub with hxy | hfac
  · linarith
  · nlinarith

/-- The final algebraic step in Chan Theorem 11.4: the positive real solution
of `1/x - 1 - x = sqrt 5` is Ramanujan's special value. -/
theorem eq_special_value_of_eta_equation
    {x : ℝ} (hxpos : 0 < x)
    (h : 1 / x - 1 - x = Real.sqrt 5) :
    x = ramanujanRRCFSpecialValue := by
  have hxne : x ≠ 0 := ne_of_gt hxpos
  have hxquad : x ^ 2 + (1 + Real.sqrt 5) * x - 1 = 0 := by
    field_simp [hxne] at h
    nlinarith
  exact positive_quadratic_solution_unique
    (by positivity) hxpos special_value_pos hxquad special_value_quadratic

private theorem rrcfR_exp_neg_two_pi_eta_equation :
    1 / rrcfR_exp_neg_two_pi - 1 - rrcfR_exp_neg_two_pi =
      (Real.sqrt 5 : ℂ) := by
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)
  have hζ : IsPrimitiveRoot ζ 5 := by
    simpa [ζ] using Complex.isPrimitiveRoot_exp 5 (by norm_num : (5 : ℕ) ≠ 0)
  have h :=
    rrcfRProductAtFifthRoot_euler_equation
      (q := expNegTwoPiFifth) hζ norm_expNegTwoPiFifth_lt_one
      expNegTwoPiFifth_ne_zero
  rw [eta_product_ratio_at_tau5] at h
  simpa [rrcfR_exp_neg_two_pi] using h

/-- Chan Theorem 11.4 in the product-normalized analytic model of `R(e^{-2π})`. -/
theorem chan_theorem_11_4 :
    rrcfR_exp_neg_two_pi = (ramanujanRRCFSpecialValue : ℂ) := by
  rcases rrcfR_exp_neg_two_pi_ofReal_pos with ⟨x, hxpos, hx⟩
  have heqC := rrcfR_exp_neg_two_pi_eta_equation
  rw [hx] at heqC
  have hleft :
      (((1 / x - 1 - x : ℝ) : ℂ)) =
        1 / (x : ℂ) - 1 - (x : ℂ) := by
    simp
  have heqR : 1 / x - 1 - x = Real.sqrt 5 := by
    apply Complex.ofReal_injective
    rw [hleft]
    exact heqC
  have hxval := eq_special_value_of_eta_equation hxpos heqR
  rw [hxval] at hx
  exact hx

/-- Chan Theorem 11.4, with the closed form expanded. -/
theorem chan_theorem_11_4_closed_form :
    rrcfR_exp_neg_two_pi =
      ((Real.sqrt ((5 + Real.sqrt 5) / 2) -
          (1 + Real.sqrt 5) / 2 : ℝ) : ℂ) := by
  simpa [ramanujanRRCFSpecialValue] using chan_theorem_11_4

end ChanTheorem114
end Pending
end QseriesFormalization
