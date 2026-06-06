import QseriesFormalization.Chapter20
import QseriesFormalization.Pending.Chapter15_FormalDeriv
import QseriesFormalization.Pending.Chapter20_LiouvilleConvolution
import Mathlib.Tactic

/-!
# Chapter 20: formal Eisenstein series and the discriminant

This pending file sets up the formal power-series route to

`E4^3 - E6^2 = 1728 * Delta`.

The nontrivial arithmetic input is the pair of Ramanujan differential
equations for the formal Eisenstein series.  Once those two sigma-convolution
identities are available, the final identity follows from the same first-order
theta equation as `Delta`, with the first nonzero coefficient fixing the
solution.
-/

namespace QseriesFormalization
namespace Pending
namespace Ch20Eisenstein

open PowerSeries
open scoped PowerSeries

open QseriesFormalization.Pending.Ch15FormalDeriv
open QseriesFormalization.PartIV.Ch20

/-- The divisor-power sum `sigma_r(n) = sum_{d | n} d^r`, packaged as a
formal power series over `Q`. -/
noncomputable def divisorSigmaPS (r : Nat) : ℚ⟦X⟧ :=
  PowerSeries.mk fun n => ((Nat.divisorSum n fun d => d ^ r : Nat) : ℚ)

@[simp] theorem coeff_divisorSigmaPS (r n : Nat) :
    (divisorSigmaPS r).coeff n =
      ((Nat.divisorSum n fun d => d ^ r : Nat) : ℚ) := by
  simp [divisorSigmaPS]

/-- Formal `E2 = 1 - 24 * sum sigma_1(n) X^n`. -/
noncomputable def eisensteinE2PS : ℚ⟦X⟧ :=
  1 - PowerSeries.C (24 : ℚ) * divisorSigmaPS 1

/-- Formal `E4 = 1 + 240 * sum sigma_3(n) X^n`. -/
noncomputable def eisensteinE4PS : ℚ⟦X⟧ :=
  1 + PowerSeries.C (240 : ℚ) * divisorSigmaPS 3

/-- Formal `E6 = 1 - 504 * sum sigma_5(n) X^n`. -/
noncomputable def eisensteinE6PS : ℚ⟦X⟧ :=
  1 - PowerSeries.C (504 : ℚ) * divisorSigmaPS 5

/-- The Eisenstein-side discriminant numerator. -/
noncomputable def eisensteinDiscriminantLHS : ℚ⟦X⟧ :=
  eisensteinE4PS ^ 3 - eisensteinE6PS ^ 2

/-- The eta-product-side discriminant scaled by `1728`. -/
noncomputable def eisensteinDiscriminantRHS : ℚ⟦X⟧ :=
  PowerSeries.C (1728 : ℚ) * discriminantPS ℚ

@[simp] theorem coeff_zero_divisorSigmaPS (r : Nat) :
    (divisorSigmaPS r).coeff 0 = 0 := by
  simp [divisorSigmaPS, Nat.divisorSum]

@[simp] theorem coeff_one_divisorSigmaPS (r : Nat) :
    (divisorSigmaPS r).coeff 1 = 1 := by
  simp [divisorSigmaPS, Nat.divisorSum]

@[simp] theorem coeff_zero_eisensteinE2PS :
    eisensteinE2PS.coeff 0 = 1 := by
  unfold eisensteinE2PS
  rw [map_sub, PowerSeries.coeff_one, PowerSeries.coeff_C_mul]
  simp

@[simp] theorem coeff_zero_eisensteinE4PS :
    eisensteinE4PS.coeff 0 = 1 := by
  unfold eisensteinE4PS
  rw [map_add, PowerSeries.coeff_one, PowerSeries.coeff_C_mul]
  simp

@[simp] theorem coeff_one_eisensteinE4PS :
    eisensteinE4PS.coeff 1 = 240 := by
  unfold eisensteinE4PS
  rw [map_add, PowerSeries.coeff_one, PowerSeries.coeff_C_mul]
  norm_num [Nat.divisorSum]

@[simp] theorem coeff_zero_eisensteinE6PS :
    eisensteinE6PS.coeff 0 = 1 := by
  unfold eisensteinE6PS
  rw [map_sub, PowerSeries.coeff_one, PowerSeries.coeff_C_mul]
  simp

@[simp] theorem coeff_one_eisensteinE6PS :
    eisensteinE6PS.coeff 1 = -504 := by
  unfold eisensteinE6PS
  rw [map_sub, PowerSeries.coeff_one, PowerSeries.coeff_C_mul]
  norm_num [Nat.divisorSum]

theorem coeff_one_mul (f g : ℚ⟦X⟧) :
    (f * g).coeff 1 = f.coeff 0 * g.coeff 1 + f.coeff 1 * g.coeff 0 := by
  rw [PowerSeries.coeff_mul]
  rw [show (Finset.antidiagonal 1 : Finset (Nat × Nat)) = {(0, 1), (1, 0)} from rfl]
  simp

theorem coeff_zero_mul (f g : ℚ⟦X⟧) :
    (f * g).coeff 0 = f.coeff 0 * g.coeff 0 := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul]
  simp [PowerSeries.coeff_zero_eq_constantCoeff_apply]

theorem coeff_zero_pow (f : ℚ⟦X⟧) (n : Nat) :
    (f ^ n).coeff 0 = f.coeff 0 ^ n := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow]
  simp [PowerSeries.coeff_zero_eq_constantCoeff_apply]

theorem coeff_one_pow_two (f : ℚ⟦X⟧) :
    (f ^ 2).coeff 1 = 2 * f.coeff 0 * f.coeff 1 := by
  rw [pow_two, coeff_one_mul]
  ring

theorem coeff_one_pow_three (f : ℚ⟦X⟧) :
    (f ^ 3).coeff 1 = 3 * f.coeff 0 ^ 2 * f.coeff 1 := by
  rw [show f ^ 3 = f ^ 2 * f by ring, coeff_one_mul, coeff_one_pow_two]
  have h0 : (f ^ 2).coeff 0 = f.coeff 0 * f.coeff 0 := by
    rw [pow_two, coeff_zero_mul]
  rw [h0]
  ring

theorem coeff_zero_eisensteinDiscriminantLHS :
    eisensteinDiscriminantLHS.coeff 0 = 0 := by
  unfold eisensteinDiscriminantLHS
  rw [map_sub, coeff_zero_pow, coeff_zero_pow]
  norm_num

theorem coeff_one_eisensteinDiscriminantLHS :
    eisensteinDiscriminantLHS.coeff 1 = 1728 := by
  unfold eisensteinDiscriminantLHS
  rw [map_sub, coeff_one_pow_three, coeff_one_pow_two]
  simp
  norm_num

theorem coeff_zero_eisensteinDiscriminantRHS :
    eisensteinDiscriminantRHS.coeff 0 = 0 := by
  unfold eisensteinDiscriminantRHS
  rw [PowerSeries.coeff_C_mul]
  change (1728 : ℚ) * ramanujanTau ℚ 0 = 0
  rw [ramanujanTau_zero]
  ring

theorem coeff_one_eisensteinDiscriminantRHS :
    eisensteinDiscriminantRHS.coeff 1 = 1728 := by
  unfold eisensteinDiscriminantRHS
  rw [PowerSeries.coeff_C_mul]
  change (1728 : ℚ) * ramanujanTau ℚ 1 = 1728
  rw [ramanujanTau_one]
  ring

/-- Naturality of `thetaOp` for the cast `Z -> Q`. -/
theorem map_thetaOp_int_rat (f : ℤ⟦X⟧) :
    PowerSeries.map (Int.castRingHom ℚ) (thetaOp f) =
      thetaOp (PowerSeries.map (Int.castRingHom ℚ) f) := by
  ext n
  simp [PowerSeries.coeff_map, coeff_thetaOp]

/-- The Chapter 20 `sigma_1` series over `Z`, cast to `Q`, is the local
`divisorSigmaPS 1`. -/
theorem map_ch20_divisorSigmaPS_int_rat :
    PowerSeries.map (Int.castRingHom ℚ)
        (QseriesFormalization.PartIV.Ch20.divisorSigmaPS ℤ) =
      divisorSigmaPS 1 := by
  ext n
  rw [PowerSeries.coeff_map, QseriesFormalization.PartIV.Ch20.coeff_divisorSigmaPS,
    coeff_divisorSigmaPS]
  unfold Nat.divisorSum
  simp [pow_one]

/-- The eta-product discriminant satisfies `theta Delta = E2 * Delta` over
`Q[[X]]`.  This is the rational cast of the Chapter 20 product-structure
identity for `Delta`. -/
theorem thetaOp_discriminantPS_eq_eisensteinE2PS_mul :
    thetaOp (discriminantPS ℚ) = eisensteinE2PS * discriminantPS ℚ := by
  have hmap := congrArg (PowerSeries.map (Int.castRingHom ℚ))
    QseriesFormalization.PartIV.Ch20.thetaOp_discriminantPS_eq
  rw [map_thetaOp_int_rat,
    QseriesFormalization.PartIV.Ch20.map_discriminantPS,
    map_sub, map_mul, map_mul,
    QseriesFormalization.PartIV.Ch20.map_discriminantPS,
    map_ch20_divisorSigmaPS_int_rat] at hmap
  have h24 :
      PowerSeries.map (Int.castRingHom ℚ) (24 : ℤ⟦X⟧) =
        PowerSeries.C (24 : ℚ) := by
    rw [show (24 : ℤ⟦X⟧) = PowerSeries.C (24 : ℤ) from rfl,
      PowerSeries.map_C]
    norm_num
  rw [h24] at hmap
  calc
    thetaOp (discriminantPS ℚ)
        = discriminantPS ℚ -
          PowerSeries.C (24 : ℚ) * discriminantPS ℚ * divisorSigmaPS 1 := by
            simpa using hmap
    _ = eisensteinE2PS * discriminantPS ℚ := by
            unfold eisensteinE2PS
            ring

/-- The scaled discriminant satisfies the same theta equation. -/
theorem eisensteinDiscriminantRHS_theta_eq :
    thetaOp eisensteinDiscriminantRHS =
      eisensteinE2PS * eisensteinDiscriminantRHS := by
  unfold eisensteinDiscriminantRHS
  rw [thetaOp_C_mul, thetaOp_discriminantPS_eq_eisensteinE2PS_mul]
  ring

/-- If `A.coeff 0 = 1`, then `theta f = A*f` recursively determines every
coefficient from the coefficients in degrees `0` and `1`. -/
theorem eq_zero_of_theta_eq_mul_coeff_zero_one {A f : ℚ⟦X⟧}
    (hA0 : A.coeff 0 = 1)
    (hf0 : f.coeff 0 = 0)
    (hf1 : f.coeff 1 = 0)
    (hf : thetaOp f = A * f) :
    f = 0 := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn0 : n = 0
      · simpa [hn0] using hf0
      by_cases hn1 : n = 1
      · simpa [hn1] using hf1
      have hn2 : 2 ≤ n := by omega
      have hc : (thetaOp f).coeff n = (A * f).coeff n := by
        simpa using congrArg (fun s : ℚ⟦X⟧ => s.coeff n) hf
      rw [coeff_thetaOp, PowerSeries.coeff_mul] at hc
      have hmem : (0, n) ∈ Finset.antidiagonal n := by
        simp
      have hsum :
          (∑ ij ∈ Finset.antidiagonal n, A.coeff ij.1 * f.coeff ij.2) =
            A.coeff 0 * f.coeff n := by
        refine Finset.sum_eq_single (0, n) ?_ ?_
        · rintro ⟨i, j⟩ hij hijne
          have hijsum : i + j = n := Finset.mem_antidiagonal.mp hij
          have hi_ne_zero : i ≠ 0 := by
            intro hi
            subst i
            have hj : j = n := by omega
            exact hijne (by ext <;> simp [hj])
          have hjlt : j < n := by omega
          have hfj : f.coeff j = 0 := ih j hjlt
          rw [hfj, mul_zero]
        · intro hnot
          exact False.elim (hnot hmem)
      rw [hsum, hA0, one_mul] at hc
      have hmul : f.coeff n * ((n : ℚ) - 1) = 0 := by
        calc
          f.coeff n * ((n : ℚ) - 1)
              = f.coeff n * (n : ℚ) - f.coeff n := by ring
          _ = 0 := by
              rw [hc]
              ring
      have hne : ((n : ℚ) - 1) ≠ 0 := by
        apply sub_ne_zero.mpr
        norm_num
        exact hn1
      exact (mul_eq_zero.mp hmul).resolve_right hne

/-- Uniqueness for the theta equation `theta f = A*f` when `A.coeff 0 = 1`.
For this case the degree-one coefficient is the free initial datum. -/
theorem eq_of_same_theta_eq_mul_coeff_zero_one {A f g : ℚ⟦X⟧}
    (hA0 : A.coeff 0 = 1)
    (hf : thetaOp f = A * f)
    (hg : thetaOp g = A * g)
    (h0 : f.coeff 0 = g.coeff 0)
    (h1 : f.coeff 1 = g.coeff 1) :
    f = g := by
  have hdiff : thetaOp (f - g) = A * (f - g) := by
    rw [thetaOp_sub, hf, hg]
    ring
  have hdiff0 : (f - g).coeff 0 = 0 := by
    rw [map_sub, h0, sub_self]
  have hdiff1 : (f - g).coeff 1 = 0 := by
    rw [map_sub, h1, sub_self]
  exact sub_eq_zero.mp
    (eq_zero_of_theta_eq_mul_coeff_zero_one hA0 hdiff0 hdiff1 hdiff)

/-- Ramanujan's formal theta equation for `E4`, stated in a denominator-free
form.  Proving this is exactly the `sigma_1 * sigma_3` convolution identity. -/
def RamanujanThetaE4 : Prop :=
  (3 : ℚ⟦X⟧) * thetaOp eisensteinE4PS =
    eisensteinE2PS * eisensteinE4PS - eisensteinE6PS

/-- Ramanujan's formal theta equation for `E6`, stated in a denominator-free
form.  Proving this is exactly the `sigma_1 * sigma_5` convolution identity. -/
def RamanujanThetaE6 : Prop :=
  (2 : ℚ⟦X⟧) * thetaOp eisensteinE6PS =
    eisensteinE2PS * eisensteinE6PS - eisensteinE4PS ^ 2

/-- The residual of `3*theta(E4) = E2*E4 - E6`. -/
noncomputable def residual3E4PS : ℚ⟦X⟧ :=
  (3 : ℚ⟦X⟧) * thetaOp eisensteinE4PS -
    (eisensteinE2PS * eisensteinE4PS - eisensteinE6PS)

/-- The residual of `2*theta(E6) = E2*E6 - E4^2`. -/
noncomputable def residual2E6PS : ℚ⟦X⟧ :=
  (2 : ℚ⟦X⟧) * thetaOp eisensteinE6PS -
    (eisensteinE2PS * eisensteinE6PS - eisensteinE4PS ^ 2)

theorem eq_zero_of_theta_eq_mul_coeff_zero {C f : ℚ⟦X⟧}
    (hC0 : C.coeff 0 = 0)
    (hf0 : f.coeff 0 = 0)
    (hf : thetaOp f = C * f) :
    f = 0 := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn0 : n = 0
      · simpa [hn0] using hf0
      have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
      have hc : (thetaOp f).coeff n = (C * f).coeff n := by
        simpa using congrArg (fun s : ℚ⟦X⟧ => s.coeff n) hf
      rw [coeff_thetaOp, PowerSeries.coeff_mul] at hc
      have hsum :
          (∑ ij ∈ Finset.antidiagonal n, C.coeff ij.1 * f.coeff ij.2) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro ij hij
        have hijsum : ij.1 + ij.2 = n := Finset.mem_antidiagonal.mp hij
        by_cases hjn : ij.2 = n
        · have hi0 : ij.1 = 0 := by omega
          rw [hi0, hC0, zero_mul]
        · have hjlt : ij.2 < n := by omega
          have hfj : f.coeff ij.2 = 0 := ih ij.2 hjlt
          rw [hfj, mul_zero]
      rw [hsum] at hc
      have hn_ne : (n : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hnpos
      exact (mul_eq_zero.mp hc).resolve_right hn_ne

/-! ## Coefficient form of the two Ramanujan theta equations -/

/-- Integer-valued divisor-power sum used for executable residual checks. -/
def sigmaPowZ (r n : Nat) : Int :=
  (Nat.divisorSum n fun d => d ^ r : Int)

/-- Coefficient of `E2 = 1 - 24 S1`, as an integer. -/
def eisensteinE2CoeffZ (n : Nat) : Int :=
  if n = 0 then 1 else -24 * sigmaPowZ 1 n

/-- Coefficient of `E4 = 1 + 240 S3`, as an integer. -/
def eisensteinE4CoeffZ (n : Nat) : Int :=
  if n = 0 then 1 else 240 * sigmaPowZ 3 n

/-- Coefficient of `E6 = 1 - 504 S5`, as an integer. -/
def eisensteinE6CoeffZ (n : Nat) : Int :=
  if n = 0 then 1 else -504 * sigmaPowZ 5 n

/-- Additive Cauchy convolution of two integer coefficient functions. -/
def convCoeffZ (a b : Nat → Int) (n : Nat) : Int :=
  ∑ ij ∈ Finset.antidiagonal n, a ij.1 * b ij.2

/-- Coefficient residual for `3 theta(E4) = E2 * E4 - E6`. -/
def ramanujanThetaE4ResidualCoeffZ (n : Nat) : Int :=
  3 * (n : Int) * eisensteinE4CoeffZ n -
    (convCoeffZ eisensteinE2CoeffZ eisensteinE4CoeffZ n - eisensteinE6CoeffZ n)

/-- Coefficient residual for `2 theta(E6) = E2 * E6 - E4^2`. -/
def ramanujanThetaE6ResidualCoeffZ (n : Nat) : Int :=
  2 * (n : Int) * eisensteinE6CoeffZ n -
    (convCoeffZ eisensteinE2CoeffZ eisensteinE6CoeffZ n -
      convCoeffZ eisensteinE4CoeffZ eisensteinE4CoeffZ n)

def sigma1Sigma3ConvZ (n : Nat) : Int :=
  ∑ k ∈ Finset.Icc 1 (n - 1), sigmaPowZ 1 k * sigmaPowZ 3 (n - k)

def sigma1Sigma5ConvZ (n : Nat) : Int :=
  ∑ k ∈ Finset.Icc 1 (n - 1), sigmaPowZ 1 k * sigmaPowZ 5 (n - k)

def sigma3Sigma3ConvZ (n : Nat) : Int :=
  ∑ k ∈ Finset.Icc 1 (n - 1), sigmaPowZ 3 k * sigmaPowZ 3 (n - k)

/-- Divisor sums as bounded factor-pair sums.  This is the basic Finset
rewrite needed to turn the `sigma_1 * sigma_3` convolution into a finite
four-variable sum. -/
lemma sigmaPowZ_eq_sum_factorPairs_of_pos_le (r k N : Nat)
    (hk0 : 0 < k) (hkN : k ≤ N) :
    sigmaPowZ r k =
      ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
        if a * b = k then ((a ^ r : Nat) : Int) else 0 := by
  unfold sigmaPowZ Nat.divisorSum
  rw [Nat.cast_sum]
  calc
    (∑ d ∈ Finset.Icc 1 k, ↑(if d ∣ k then d ^ r else 0 : Nat))
        = ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
            if a * b = k then ((a ^ r : Nat) : Int) else 0 := by
      rw [← Finset.sum_subset (s₁ := Finset.Icc 1 k) (s₂ := Finset.Icc 1 N)]
      · refine Finset.sum_congr rfl ?_
        intro a ha
        rw [Nat.cast_ite]
        by_cases hdiv : a ∣ k
        · rw [if_pos hdiv]
          rcases hdiv with ⟨b, hb⟩
          have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
          have ha0 : 0 < a := ha1
          have hbpos : 0 < b := by
            by_contra hb0not
            have hb0 : b = 0 := Nat.eq_zero_of_not_pos hb0not
            subst b
            have hkpos : 0 < k := hk0
            simp at hb
            omega
          have hbN : b ≤ N := by
            have hbk : b ≤ k := by
              rw [hb]
              exact Nat.le_mul_of_pos_left b ha0
            exact le_trans hbk hkN
          rw [Finset.sum_eq_single b]
          · simp [hb]
          · intro b' _ hbne
            by_cases h : a * b' = k
            · have hb' : b' = b := by
                exact Nat.mul_left_cancel ha0 (by rw [h, hb])
              exact False.elim (hbne hb')
            · simp [h]
          · intro hbnot
            exact False.elim (hbnot (Finset.mem_Icc.mpr ⟨hbpos, hbN⟩))
        · rw [if_neg hdiv]
          symm
          apply Finset.sum_eq_zero
          intro b _
          by_cases h : a * b = k
          · exact False.elim (hdiv ⟨b, h.symm⟩)
          · simp [h]
      · intro a ha
        exact Finset.mem_Icc.mpr
          ⟨(Finset.mem_Icc.mp ha).1, le_trans (Finset.mem_Icc.mp ha).2 hkN⟩
      · intro a haN haNotSmall
        have ha1 : 1 ≤ a := (Finset.mem_Icc.mp haN).1
        have hka : k < a := by
          have hnot : ¬ a ≤ k := by
            intro hak
            exact haNotSmall (Finset.mem_Icc.mpr ⟨ha1, hak⟩)
          omega
        apply Finset.sum_eq_zero
        intro b hbmem
        by_cases h : a * b = k
        · have hbpos : 0 < b := (Finset.mem_Icc.mp hbmem).1
          have : a ≤ k := by
            rw [← h]
            exact Nat.le_mul_of_pos_right a hbpos
          omega
        · simp [h]

/-- The `sigma_1 * sigma_3` convolution after expanding each divisor sum into
bounded factor pairs.  The summation variables are `k,a,b,c,d`, with
`a*b = k` and `c*d = n-k`. -/
def sigma1Sigma3FactorPairSplitSumZ (n : Nat) : Int :=
  ∑ k ∈ Finset.Icc 1 (n - 1),
    (∑ a ∈ Finset.Icc 1 n, ∑ b ∈ Finset.Icc 1 n,
      if a * b = k then ((a ^ 1 : Nat) : Int) else 0) *
    (∑ c ∈ Finset.Icc 1 n, ∑ d ∈ Finset.Icc 1 n,
      if c * d = n - k then ((c ^ 3 : Nat) : Int) else 0)

theorem sigma1Sigma3ConvZ_eq_factorPairSplitSumZ (n : Nat) :
    sigma1Sigma3ConvZ n = sigma1Sigma3FactorPairSplitSumZ n := by
  unfold sigma1Sigma3ConvZ sigma1Sigma3FactorPairSplitSumZ
  apply Finset.sum_congr rfl
  intro k hk
  have hk0 : 0 < k := (Finset.mem_Icc.mp hk).1
  have hkn1 : k ≤ n - 1 := (Finset.mem_Icc.mp hk).2
  have hkn : k ≤ n := by omega
  have hnk0 : 0 < n - k := by omega
  have hnkle : n - k ≤ n := by omega
  rw [sigmaPowZ_eq_sum_factorPairs_of_pos_le 1 k n hk0 hkn,
    sigmaPowZ_eq_sum_factorPairs_of_pos_le 3 (n - k) n hnk0 hnkle]

/-- The E4 theta equation, converted to the integer convolution identity that
matches `E2 = 1 - 24*S1`, `E4 = 1 + 240*S3`, and `E6 = 1 - 504*S5`. -/
def ramanujanThetaE4ArithmeticIdentityAt (n : Nat) : Prop :=
  (720 : Int) * (n : Int) * sigmaPowZ 3 n =
    (240 : Int) * sigmaPowZ 3 n - 24 * sigmaPowZ 1 n -
      5760 * sigma1Sigma3ConvZ n + 504 * sigmaPowZ 5 n

/-- The standard Lahiri/Ramanujan `sigma_1 * sigma_3` convolution identity,
cleared of denominators:

`240 * sum_{k=1}^{n-1} sigma_1(k) sigma_3(n-k)
  = 21 sigma_5(n) + (10 - 30n) sigma_3(n) - sigma_1(n)`.

This is equivalent to the `E4` Ramanujan theta equation with the
normalizations used in this file. -/
def lahiriSigma1Sigma3IdentityAt (n : Nat) : Prop :=
  (240 : Int) * sigma1Sigma3ConvZ n =
    21 * sigmaPowZ 5 n + (10 - 30 * (n : Int)) * sigmaPowZ 3 n -
      sigmaPowZ 1 n

/-- Difference between the two sides of the Lahiri `sigma_1 * sigma_3`
convolution identity. -/
def lahiriSigma1Sigma3DiffCoeffZ (n : Nat) : Int :=
  (240 : Int) * sigma1Sigma3ConvZ n -
    (21 * sigmaPowZ 5 n + (10 - 30 * (n : Int)) * sigmaPowZ 3 n -
      sigmaPowZ 1 n)

noncomputable def lahiriSigma1Sigma3DiffPS : ℚ⟦X⟧ :=
  PowerSeries.mk fun n => (lahiriSigma1Sigma3DiffCoeffZ n : ℚ)

@[simp] theorem coeff_lahiriSigma1Sigma3DiffPS (n : Nat) :
    lahiriSigma1Sigma3DiffPS.coeff n =
      (lahiriSigma1Sigma3DiffCoeffZ n : ℚ) := by
  simp [lahiriSigma1Sigma3DiffPS]

theorem lahiriSigma1Sigma3IdentityAt_of_diffCoeffZ_eq_zero
    (n : Nat) (h : lahiriSigma1Sigma3DiffCoeffZ n = 0) :
    lahiriSigma1Sigma3IdentityAt n := by
  unfold lahiriSigma1Sigma3DiffCoeffZ at h
  unfold lahiriSigma1Sigma3IdentityAt
  nlinarith

theorem diffCoeffZ_eq_zero_of_lahiriSigma1Sigma3IdentityAt
    (n : Nat) (h : lahiriSigma1Sigma3IdentityAt n) :
    lahiriSigma1Sigma3DiffCoeffZ n = 0 := by
  unfold lahiriSigma1Sigma3IdentityAt at h
  unfold lahiriSigma1Sigma3DiffCoeffZ
  nlinarith

theorem lahiriSigma1Sigma3DiffCoeffZ_zero :
    lahiriSigma1Sigma3DiffCoeffZ 0 = 0 := by
  native_decide

theorem lahiriSigma1Sigma3DiffCoeffZ_one :
    lahiriSigma1Sigma3DiffCoeffZ 1 = 0 := by
  native_decide

@[simp] theorem coeff_zero_lahiriSigma1Sigma3DiffPS :
    lahiriSigma1Sigma3DiffPS.coeff 0 = 0 := by
  simp [lahiriSigma1Sigma3DiffCoeffZ_zero]

@[simp] theorem coeff_one_lahiriSigma1Sigma3DiffPS :
    lahiriSigma1Sigma3DiffPS.coeff 1 = 0 := by
  simp [lahiriSigma1Sigma3DiffCoeffZ_one]

def lahiriSigma1Sigma3DiffThetaE2ResidualCoeffZ (n : Nat) : Int :=
  (n : Int) * lahiriSigma1Sigma3DiffCoeffZ n -
    convCoeffZ eisensteinE2CoeffZ lahiriSigma1Sigma3DiffCoeffZ n

def lahiriSigma1Sigma3DiffThetaE2ResidualThroughCheck (N : Nat) : Bool :=
  (List.range (N + 1)).all fun n =>
    decide (lahiriSigma1Sigma3DiffThetaE2ResidualCoeffZ n = 0)

def lahiriSigma1Sigma3DiffThetaE2ResidualThrough100Check : Bool :=
  lahiriSigma1Sigma3DiffThetaE2ResidualThroughCheck 100

set_option maxHeartbeats 8000000 in
theorem lahiriSigma1Sigma3DiffThetaE2ResidualThrough100Check_true :
    lahiriSigma1Sigma3DiffThetaE2ResidualThrough100Check = true := by
  native_decide

theorem lahiriSigma1Sigma3Identity_all_of_diff_theta_eq
    (hθ : thetaOp lahiriSigma1Sigma3DiffPS =
      eisensteinE2PS * lahiriSigma1Sigma3DiffPS) :
    ∀ n : Nat, lahiriSigma1Sigma3IdentityAt n := by
  have hzero : lahiriSigma1Sigma3DiffPS = 0 :=
    eq_zero_of_theta_eq_mul_coeff_zero_one
      coeff_zero_eisensteinE2PS
      coeff_zero_lahiriSigma1Sigma3DiffPS
      coeff_one_lahiriSigma1Sigma3DiffPS
      hθ
  intro n
  apply lahiriSigma1Sigma3IdentityAt_of_diffCoeffZ_eq_zero
  have hq : (lahiriSigma1Sigma3DiffCoeffZ n : ℚ) = 0 := by
    have hc := congrArg (fun f : ℚ⟦X⟧ => f.coeff n) hzero
    simpa [lahiriSigma1Sigma3DiffPS] using hc
  exact_mod_cast hq

/-- The variant suggested in one handoff prompt.  With the present
normalizations it is false already at `n = 2`. -/
def proposedLahiriSigma1Sigma3IdentityAt (n : Nat) : Prop :=
  (240 : Int) * sigma1Sigma3ConvZ n =
    sigmaPowZ 5 n - (6 * (n : Int) - 1) * sigmaPowZ 3 n +
      (6 * (n : Int) - 2) * sigmaPowZ 1 n

/-- The sign/coefficient variant suggested in the prompt.  With the present
normalizations it is false already at `n = 1`. -/
def proposedE4ArithmeticIdentityAt (n : Nat) : Prop :=
  (720 : Int) * (n : Int) * sigmaPowZ 3 n =
    (-24 : Int) * sigmaPowZ 3 n - 240 * sigmaPowZ 1 n +
      504 * sigmaPowZ 5 n + 24 * 240 * sigma1Sigma3ConvZ n

instance decidableLahiriSigma1Sigma3IdentityAt (n : Nat) :
    Decidable (lahiriSigma1Sigma3IdentityAt n) := by
  unfold lahiriSigma1Sigma3IdentityAt
  infer_instance

instance decidableProposedLahiriSigma1Sigma3IdentityAt (n : Nat) :
    Decidable (proposedLahiriSigma1Sigma3IdentityAt n) := by
  unfold proposedLahiriSigma1Sigma3IdentityAt
  infer_instance

instance decidableRamanujanThetaE4ArithmeticIdentityAt (n : Nat) :
    Decidable (ramanujanThetaE4ArithmeticIdentityAt n) := by
  unfold ramanujanThetaE4ArithmeticIdentityAt
  infer_instance

instance decidableProposedE4ArithmeticIdentityAt (n : Nat) :
    Decidable (proposedE4ArithmeticIdentityAt n) := by
  unfold proposedE4ArithmeticIdentityAt
  infer_instance

theorem proposedE4ArithmeticIdentityAt_one_false :
    ¬ proposedE4ArithmeticIdentityAt 1 := by
  native_decide

/-- The handoff-prompt Lahiri formula is not compatible with the current
normalization of `sigmaPowZ`; `n = 2` is already a counterexample. -/
theorem proposedLahiriSigma1Sigma3IdentityAt_two_false :
    ¬ proposedLahiriSigma1Sigma3IdentityAt 2 := by
  native_decide

/-- The denominator-cleared Lahiri/Ramanujan convolution identity implies the
coefficient arithmetic form of the `E4` theta equation. -/
theorem ramanujanThetaE4ArithmeticIdentityAt_of_lahiri
    (n : Nat) (h : lahiriSigma1Sigma3IdentityAt n) :
    ramanujanThetaE4ArithmeticIdentityAt n := by
  change (240 : Int) * sigma1Sigma3ConvZ n =
      21 * sigmaPowZ 5 n + (10 - 30 * (n : Int)) * sigmaPowZ 3 n -
        sigmaPowZ 1 n at h
  change (720 : Int) * (n : Int) * sigmaPowZ 3 n =
    (240 : Int) * sigmaPowZ 3 n - 24 * sigmaPowZ 1 n -
      5760 * sigma1Sigma3ConvZ n + 504 * sigmaPowZ 5 n
  nlinarith

/-- The arithmetic coefficient form of the `E4` theta equation is equivalent
to the standard Lahiri convolution identity. -/
theorem lahiriSigma1Sigma3IdentityAt_of_ramanujanThetaE4ArithmeticIdentityAt
    (n : Nat) (h : ramanujanThetaE4ArithmeticIdentityAt n) :
    lahiriSigma1Sigma3IdentityAt n := by
  change (720 : Int) * (n : Int) * sigmaPowZ 3 n =
    (240 : Int) * sigmaPowZ 3 n - 24 * sigmaPowZ 1 n -
      5760 * sigma1Sigma3ConvZ n + 504 * sigmaPowZ 5 n at h
  change (240 : Int) * sigma1Sigma3ConvZ n =
      21 * sigmaPowZ 5 n + (10 - 30 * (n : Int)) * sigmaPowZ 3 n -
        sigmaPowZ 1 n
  nlinarith

theorem lahiriSigma1Sigma3IdentityAt_iff_ramanujanThetaE4ArithmeticIdentityAt
    (n : Nat) :
    lahiriSigma1Sigma3IdentityAt n ↔ ramanujanThetaE4ArithmeticIdentityAt n :=
  ⟨ramanujanThetaE4ArithmeticIdentityAt_of_lahiri n,
    lahiriSigma1Sigma3IdentityAt_of_ramanujanThetaE4ArithmeticIdentityAt n⟩

theorem lahiriSigma1Sigma3IdentityAt_all (n : Nat) :
    lahiriSigma1Sigma3IdentityAt n := by
  unfold lahiriSigma1Sigma3IdentityAt
  simpa [sigmaPowZ, sigma1Sigma3ConvZ,
    _root_.QseriesFormalization.Pending.Ch20LiouvilleConvolution.sigmaPowZ,
    _root_.QseriesFormalization.Pending.Ch20LiouvilleConvolution.sigma1Sigma3ConvZ]
    using
      _root_.QseriesFormalization.Pending.Ch20LiouvilleConvolution.twoforty_mul_sigma1Sigma3ConvZ_eq_lahiri n

theorem ramanujanThetaE4ArithmeticIdentityAt_all (n : Nat) :
    ramanujanThetaE4ArithmeticIdentityAt n :=
  ramanujanThetaE4ArithmeticIdentityAt_of_lahiri n
    (lahiriSigma1Sigma3IdentityAt_all n)

def lahiriSigma1Sigma3IdentityThrough100Check : Bool :=
  (List.range 101).all fun n =>
    decide (n < 2 ∨ lahiriSigma1Sigma3IdentityAt n)

set_option maxHeartbeats 8000000 in
theorem lahiriSigma1Sigma3IdentityThrough100Check_true :
    lahiriSigma1Sigma3IdentityThrough100Check = true := by
  native_decide

theorem lahiriSigma1Sigma3Identity_through_one_hundred
    (n : Nat) (hn2 : 2 ≤ n) (hn100 : n ≤ 100) :
    lahiriSigma1Sigma3IdentityAt n := by
  have hall := List.all_eq_true.mp lahiriSigma1Sigma3IdentityThrough100Check_true
  have hnrange : n ∈ List.range 101 := List.mem_range.mpr (by omega)
  have hbody := hall n hnrange
  have hcase : n < 2 ∨ lahiriSigma1Sigma3IdentityAt n :=
    of_decide_eq_true hbody
  rcases hcase with hnlt | h
  · omega
  · exact h

/-- Same executable Lahiri check, scaled to degree `500`. -/
def lahiriSigma1Sigma3IdentityThrough500Check : Bool :=
  (List.range 501).all fun n =>
    decide (n < 2 ∨ lahiriSigma1Sigma3IdentityAt n)

set_option maxHeartbeats 50000000 in
theorem lahiriSigma1Sigma3IdentityThrough500Check_true :
    lahiriSigma1Sigma3IdentityThrough500Check = true := by
  native_decide

theorem lahiriSigma1Sigma3Identity_through_five_hundred
    (n : Nat) (hn2 : 2 ≤ n) (hn500 : n ≤ 500) :
    lahiriSigma1Sigma3IdentityAt n := by
  have hall := List.all_eq_true.mp lahiriSigma1Sigma3IdentityThrough500Check_true
  have hnrange : n ∈ List.range 501 := List.mem_range.mpr (by omega)
  have hbody := hall n hnrange
  have hcase : n < 2 ∨ lahiriSigma1Sigma3IdentityAt n :=
    of_decide_eq_true hbody
  rcases hcase with hnlt | h
  · omega
  · exact h

def ramanujanThetaE4ArithmeticIdentityThrough100Check : Bool :=
  (List.range 101).all fun n =>
    decide (n = 0 ∨ ramanujanThetaE4ArithmeticIdentityAt n)

set_option maxHeartbeats 8000000 in
theorem ramanujanThetaE4ArithmeticIdentityThrough100Check_true :
    ramanujanThetaE4ArithmeticIdentityThrough100Check = true := by
  native_decide

theorem ramanujanThetaE4ArithmeticIdentity_through_one_hundred
    (n : Nat) (hn1 : 1 ≤ n) (hn100 : n ≤ 100) :
    ramanujanThetaE4ArithmeticIdentityAt n := by
  have hall := List.all_eq_true.mp ramanujanThetaE4ArithmeticIdentityThrough100Check_true
  have hnrange : n ∈ List.range 101 := List.mem_range.mpr (by omega)
  have hbody := hall n hnrange
  have hcase : n = 0 ∨ ramanujanThetaE4ArithmeticIdentityAt n :=
    of_decide_eq_true hbody
  rcases hcase with hn0 | h
  · omega
  · exact h

theorem coeff_eisensteinE2PS_eq_coeffZ (n : Nat) :
    eisensteinE2PS.coeff n = (eisensteinE2CoeffZ n : ℚ) := by
  unfold eisensteinE2PS eisensteinE2CoeffZ sigmaPowZ
  rw [map_sub, PowerSeries.coeff_one, PowerSeries.coeff_C_mul, coeff_divisorSigmaPS]
  by_cases hn : n = 0
  · subst n
    norm_num [Nat.divisorSum]
  · simp [hn]

theorem coeff_eisensteinE4PS_eq_coeffZ (n : Nat) :
    eisensteinE4PS.coeff n = (eisensteinE4CoeffZ n : ℚ) := by
  unfold eisensteinE4PS eisensteinE4CoeffZ sigmaPowZ
  rw [map_add, PowerSeries.coeff_one, PowerSeries.coeff_C_mul, coeff_divisorSigmaPS]
  by_cases hn : n = 0
  · subst n
    norm_num [Nat.divisorSum]
  · simp [hn]

theorem coeff_eisensteinE6PS_eq_coeffZ (n : Nat) :
    eisensteinE6PS.coeff n = (eisensteinE6CoeffZ n : ℚ) := by
  unfold eisensteinE6PS eisensteinE6CoeffZ sigmaPowZ
  rw [map_sub, PowerSeries.coeff_one, PowerSeries.coeff_C_mul, coeff_divisorSigmaPS]
  by_cases hn : n = 0
  · subst n
    norm_num [Nat.divisorSum]
  · simp [hn]

theorem coeff_mul_eq_convCoeffZ
    (a b : Nat → Int) (f g : ℚ⟦X⟧)
    (hf : ∀ n, f.coeff n = (a n : ℚ))
    (hg : ∀ n, g.coeff n = (b n : ℚ)) (n : Nat) :
    (f * g).coeff n = (convCoeffZ a b n : ℚ) := by
  rw [PowerSeries.coeff_mul]
  unfold convCoeffZ
  rw [Int.cast_sum]
  apply Finset.sum_congr rfl
  intro ij _
  rw [hf, hg]
  norm_num

theorem coeff_lahiriSigma1Sigma3DiffThetaE2Residual (n : Nat) :
    (thetaOp lahiriSigma1Sigma3DiffPS -
      eisensteinE2PS * lahiriSigma1Sigma3DiffPS).coeff n =
      (lahiriSigma1Sigma3DiffThetaE2ResidualCoeffZ n : ℚ) := by
  unfold lahiriSigma1Sigma3DiffThetaE2ResidualCoeffZ
  rw [map_sub, coeff_thetaOp,
    coeff_mul_eq_convCoeffZ eisensteinE2CoeffZ lahiriSigma1Sigma3DiffCoeffZ
      eisensteinE2PS lahiriSigma1Sigma3DiffPS
      coeff_eisensteinE2PS_eq_coeffZ coeff_lahiriSigma1Sigma3DiffPS,
    coeff_lahiriSigma1Sigma3DiffPS]
  push_cast
  ring

theorem lahiriSigma1Sigma3Diff_thetaE2_residual_coeff_zero_through_one_hundred
    (n : Nat) (hn : n ≤ 100) :
    (thetaOp lahiriSigma1Sigma3DiffPS -
      eisensteinE2PS * lahiriSigma1Sigma3DiffPS).coeff n = 0 := by
  have hall :=
    List.all_eq_true.mp lahiriSigma1Sigma3DiffThetaE2ResidualThrough100Check_true
  have hnrange : n ∈ List.range 101 := List.mem_range.mpr (by omega)
  have hbody := hall n hnrange
  have hz : lahiriSigma1Sigma3DiffThetaE2ResidualCoeffZ n = 0 := by
    exact of_decide_eq_true hbody
  have hc := coeff_lahiriSigma1Sigma3DiffThetaE2Residual n
  rw [hz] at hc
  simpa using hc

theorem coeff_ramanujanThetaE4Residual (n : Nat) :
    residual3E4PS.coeff n =
      (ramanujanThetaE4ResidualCoeffZ n : ℚ) := by
  unfold residual3E4PS
  change ((PowerSeries.C (3 : ℚ)) * thetaOp eisensteinE4PS -
        (eisensteinE2PS * eisensteinE4PS - eisensteinE6PS)).coeff n =
      (ramanujanThetaE4ResidualCoeffZ n : ℚ)
  unfold ramanujanThetaE4ResidualCoeffZ
  rw [map_sub, PowerSeries.coeff_C_mul, coeff_thetaOp, map_sub,
    coeff_mul_eq_convCoeffZ eisensteinE2CoeffZ eisensteinE4CoeffZ
      eisensteinE2PS eisensteinE4PS
      coeff_eisensteinE2PS_eq_coeffZ coeff_eisensteinE4PS_eq_coeffZ,
    coeff_eisensteinE4PS_eq_coeffZ, coeff_eisensteinE6PS_eq_coeffZ]
  push_cast
  ring

theorem coeff_ramanujanThetaE6Residual (n : Nat) :
    residual2E6PS.coeff n =
      (ramanujanThetaE6ResidualCoeffZ n : ℚ) := by
  unfold residual2E6PS
  change ((PowerSeries.C (2 : ℚ)) * thetaOp eisensteinE6PS -
        (eisensteinE2PS * eisensteinE6PS - eisensteinE4PS ^ 2)).coeff n =
      (ramanujanThetaE6ResidualCoeffZ n : ℚ)
  unfold ramanujanThetaE6ResidualCoeffZ
  rw [map_sub, PowerSeries.coeff_C_mul, coeff_thetaOp, map_sub,
    coeff_mul_eq_convCoeffZ eisensteinE2CoeffZ eisensteinE6CoeffZ
      eisensteinE2PS eisensteinE6PS
      coeff_eisensteinE2PS_eq_coeffZ coeff_eisensteinE6PS_eq_coeffZ,
    pow_two,
    coeff_mul_eq_convCoeffZ eisensteinE4CoeffZ eisensteinE4CoeffZ
      eisensteinE4PS eisensteinE4PS
      coeff_eisensteinE4PS_eq_coeffZ coeff_eisensteinE4PS_eq_coeffZ,
    coeff_eisensteinE6PS_eq_coeffZ]
  push_cast
  ring

/-! ### Direct coefficient check for the Eisenstein discriminant theta equation -/

def sigmaConvCoeffZ (r s n : Nat) : Int :=
  convCoeffZ (sigmaPowZ r) (sigmaPowZ s) n

def sigmaTripleConvCoeffZ (r s t n : Nat) : Int :=
  convCoeffZ (sigmaConvCoeffZ r s) (sigmaPowZ t) n

def eisensteinDiscriminantLHSMixedCoeffZ (n : Nat) : Int :=
  720 * sigmaPowZ 3 n + 1008 * sigmaPowZ 5 n +
    172800 * sigmaConvCoeffZ 3 3 n +
    13824000 * sigmaTripleConvCoeffZ 3 3 3 n -
    254016 * sigmaConvCoeffZ 5 5 n

def eisensteinDiscriminantLHSThetaResidualMixedCoeffZ (n : Nat) : Int :=
  ((n : Int) - 1) * eisensteinDiscriminantLHSMixedCoeffZ n +
    24 * convCoeffZ (sigmaPowZ 1) eisensteinDiscriminantLHSMixedCoeffZ n

def eisensteinE4SquaredCoeffZ (n : Nat) : Int :=
  convCoeffZ eisensteinE4CoeffZ eisensteinE4CoeffZ n

def eisensteinE4CubedCoeffZ (n : Nat) : Int :=
  convCoeffZ eisensteinE4SquaredCoeffZ eisensteinE4CoeffZ n

def eisensteinE6SquaredCoeffZ (n : Nat) : Int :=
  convCoeffZ eisensteinE6CoeffZ eisensteinE6CoeffZ n

def eisensteinDiscriminantLHSCoeffZ (n : Nat) : Int :=
  eisensteinE4CubedCoeffZ n - eisensteinE6SquaredCoeffZ n

def eisensteinDiscriminantLHSThetaResidualCoeffZ (n : Nat) : Int :=
  (n : Int) * eisensteinDiscriminantLHSCoeffZ n -
    convCoeffZ eisensteinE2CoeffZ eisensteinDiscriminantLHSCoeffZ n

theorem coeff_divisorSigmaPS_eq_sigmaPowZ (r n : Nat) :
    (divisorSigmaPS r).coeff n = (sigmaPowZ r n : ℚ) := by
  simp [sigmaPowZ]

theorem coeff_sigmaConvCoeffZ (r s n : Nat) :
    (divisorSigmaPS r * divisorSigmaPS s).coeff n =
      (sigmaConvCoeffZ r s n : ℚ) := by
  unfold sigmaConvCoeffZ
  exact coeff_mul_eq_convCoeffZ (sigmaPowZ r) (sigmaPowZ s)
    (divisorSigmaPS r) (divisorSigmaPS s)
    (coeff_divisorSigmaPS_eq_sigmaPowZ r)
    (coeff_divisorSigmaPS_eq_sigmaPowZ s) n

theorem coeff_sigmaTripleConvCoeffZ (r s t n : Nat) :
    ((divisorSigmaPS r * divisorSigmaPS s) * divisorSigmaPS t).coeff n =
      (sigmaTripleConvCoeffZ r s t n : ℚ) := by
  unfold sigmaTripleConvCoeffZ
  exact coeff_mul_eq_convCoeffZ (sigmaConvCoeffZ r s) (sigmaPowZ t)
    (divisorSigmaPS r * divisorSigmaPS s) (divisorSigmaPS t)
    (coeff_sigmaConvCoeffZ r s)
    (coeff_divisorSigmaPS_eq_sigmaPowZ t) n

theorem coeff_mul_natCast_rat (f : ℚ⟦X⟧) (m n : Nat) :
    (f * (m : ℚ⟦X⟧)).coeff n = f.coeff n * (m : ℚ) := by
  have hm : (m : ℚ⟦X⟧) = PowerSeries.C (m : ℚ) :=
    (map_natCast (PowerSeries.C : ℚ →+* ℚ⟦X⟧) m).symm
  rw [hm, mul_comm, PowerSeries.coeff_C_mul, mul_comm]

theorem coeff_mul_C_rat (f : ℚ⟦X⟧) (q : ℚ) (n : Nat) :
    (f * PowerSeries.C q).coeff n = f.coeff n * q := by
  rw [mul_comm, PowerSeries.coeff_C_mul, mul_comm]

theorem coeff_eisensteinDiscriminantLHS_eq_mixedCoeffZ (n : Nat) :
    eisensteinDiscriminantLHS.coeff n =
      (eisensteinDiscriminantLHSMixedCoeffZ n : ℚ) := by
  have hformal : eisensteinDiscriminantLHS =
      PowerSeries.C (240 : ℚ) * divisorSigmaPS 3 * (3 : ℚ⟦X⟧) +
      PowerSeries.C (240 : ℚ) ^ 2 * divisorSigmaPS 3 ^ 2 * (3 : ℚ⟦X⟧) +
      PowerSeries.C (240 : ℚ) ^ 3 * divisorSigmaPS 3 ^ 3 +
      (PowerSeries.C (504 : ℚ) * divisorSigmaPS 5 * (2 : ℚ⟦X⟧) -
        PowerSeries.C (504 : ℚ) ^ 2 * divisorSigmaPS 5 ^ 2) := by
    unfold eisensteinDiscriminantLHS eisensteinE4PS eisensteinE6PS
    ring_nf
  rw [hformal]
  have h1 :
      (PowerSeries.C (240 : ℚ) * divisorSigmaPS 3 * (3 : ℚ⟦X⟧)).coeff n =
        (720 * sigmaPowZ 3 n : ℚ) := by
    change (((PowerSeries.C (240 : ℚ) * divisorSigmaPS 3) *
      (3 : ℚ⟦X⟧)).coeff n = (720 * sigmaPowZ 3 n : ℚ))
    have hthree : (3 : ℚ⟦X⟧) = PowerSeries.C (3 : ℚ) :=
      (map_natCast (PowerSeries.C : ℚ →+* ℚ⟦X⟧) 3).symm
    rw [hthree]
    rw [coeff_mul_C_rat, PowerSeries.coeff_C_mul,
      coeff_divisorSigmaPS_eq_sigmaPowZ]
    ring
  have h2 :
      (PowerSeries.C (240 : ℚ) ^ 2 * divisorSigmaPS 3 ^ 2 *
          (3 : ℚ⟦X⟧)).coeff n =
        (172800 * sigmaConvCoeffZ 3 3 n : ℚ) := by
    change (((PowerSeries.C (240 : ℚ) ^ 2 * divisorSigmaPS 3 ^ 2) *
      (3 : ℚ⟦X⟧)).coeff n = (172800 * sigmaConvCoeffZ 3 3 n : ℚ))
    have hthree : (3 : ℚ⟦X⟧) = PowerSeries.C (3 : ℚ) :=
      (map_natCast (PowerSeries.C : ℚ →+* ℚ⟦X⟧) 3).symm
    have hC :
        PowerSeries.C (240 : ℚ) ^ 2 =
          PowerSeries.C ((240 : ℚ) ^ 2) :=
      (map_pow (PowerSeries.C : ℚ →+* ℚ⟦X⟧) (240 : ℚ) 2).symm
    rw [hthree]
    rw [coeff_mul_C_rat, hC,
      show divisorSigmaPS 3 ^ 2 = divisorSigmaPS 3 * divisorSigmaPS 3 by ring,
      PowerSeries.coeff_C_mul, coeff_sigmaConvCoeffZ]
    ring
  have h3 :
      (PowerSeries.C (240 : ℚ) ^ 3 * divisorSigmaPS 3 ^ 3).coeff n =
        (13824000 * sigmaTripleConvCoeffZ 3 3 3 n : ℚ) := by
    have hC :
        PowerSeries.C (240 : ℚ) ^ 3 =
          PowerSeries.C ((240 : ℚ) ^ 3) :=
      (map_pow (PowerSeries.C : ℚ →+* ℚ⟦X⟧) (240 : ℚ) 3).symm
    rw [hC,
      show divisorSigmaPS 3 ^ 3 =
        (divisorSigmaPS 3 * divisorSigmaPS 3) * divisorSigmaPS 3 by ring,
      PowerSeries.coeff_C_mul, coeff_sigmaTripleConvCoeffZ]
    ring
  have h4 :
      (PowerSeries.C (504 : ℚ) * divisorSigmaPS 5 * (2 : ℚ⟦X⟧)).coeff n =
        (1008 * sigmaPowZ 5 n : ℚ) := by
    change (((PowerSeries.C (504 : ℚ) * divisorSigmaPS 5) *
      (2 : ℚ⟦X⟧)).coeff n = (1008 * sigmaPowZ 5 n : ℚ))
    have htwo : (2 : ℚ⟦X⟧) = PowerSeries.C (2 : ℚ) :=
      (map_natCast (PowerSeries.C : ℚ →+* ℚ⟦X⟧) 2).symm
    rw [htwo]
    rw [coeff_mul_C_rat, PowerSeries.coeff_C_mul,
      coeff_divisorSigmaPS_eq_sigmaPowZ]
    ring
  have h5 :
      (PowerSeries.C (504 : ℚ) ^ 2 * divisorSigmaPS 5 ^ 2).coeff n =
        (254016 * sigmaConvCoeffZ 5 5 n : ℚ) := by
    have hC :
        PowerSeries.C (504 : ℚ) ^ 2 =
          PowerSeries.C ((504 : ℚ) ^ 2) :=
      (map_pow (PowerSeries.C : ℚ →+* ℚ⟦X⟧) (504 : ℚ) 2).symm
    rw [hC,
      show divisorSigmaPS 5 ^ 2 = divisorSigmaPS 5 * divisorSigmaPS 5 by ring,
      PowerSeries.coeff_C_mul, coeff_sigmaConvCoeffZ]
    ring
  unfold eisensteinDiscriminantLHSMixedCoeffZ
  rw [map_add, map_add, map_add, map_sub, h1, h2, h3, h4, h5]
  push_cast
  ring

theorem convCoeffZ_eisensteinE2CoeffZ_left (a : Nat → Int) (n : Nat) :
    convCoeffZ eisensteinE2CoeffZ a n =
      a n - 24 * convCoeffZ (sigmaPowZ 1) a n := by
  unfold convCoeffZ
  have hcoeff : ∀ i : Nat,
      eisensteinE2CoeffZ i =
        (if i = 0 then 1 else 0) - 24 * sigmaPowZ 1 i := by
    intro i
    unfold eisensteinE2CoeffZ
    by_cases hi : i = 0
    · subst i
      norm_num [sigmaPowZ, Nat.divisorSum]
    · simp [hi]
  calc
    (∑ ij ∈ Finset.antidiagonal n, eisensteinE2CoeffZ ij.1 * a ij.2)
        = ∑ ij ∈ Finset.antidiagonal n,
            (((if ij.1 = 0 then 1 else 0) - 24 * sigmaPowZ 1 ij.1) *
              a ij.2) := by
            apply Finset.sum_congr rfl
            intro ij _
            rw [hcoeff]
    _ = (∑ ij ∈ Finset.antidiagonal n,
            (if ij.1 = 0 then 1 else 0 : Int) * a ij.2) -
          24 * ∑ ij ∈ Finset.antidiagonal n, sigmaPowZ 1 ij.1 * a ij.2 := by
            simp_rw [sub_mul, mul_assoc]
            rw [Finset.sum_sub_distrib, Finset.mul_sum]
    _ = a n - 24 * ∑ ij ∈ Finset.antidiagonal n,
          sigmaPowZ 1 ij.1 * a ij.2 := by
            have hdelta :
                (∑ ij ∈ Finset.antidiagonal n,
                    (if ij.1 = 0 then 1 else 0 : Int) * a ij.2) = a n := by
              calc
                (∑ ij ∈ Finset.antidiagonal n,
                    (if ij.1 = 0 then 1 else 0 : Int) * a ij.2)
                    = (if (0 : Nat) = 0 then 1 else 0 : Int) * a n := by
                        refine Finset.sum_eq_single (0, n) ?_ ?_
                        · rintro ⟨i, j⟩ hij hne
                          have hijsum : i + j = n := Finset.mem_antidiagonal.mp hij
                          by_cases hi : i = 0
                          · subst i
                            have hj : j = n := by omega
                            subst j
                            exact False.elim (hne rfl)
                          · simp [hi]
                        · intro hnot
                          exact False.elim (hnot (by simp))
                _ = a n := by simp
            rw [hdelta]

theorem range_eq_insert_Icc_one_pred (n : Nat) (hn : n ≠ 0) :
    Finset.range n = insert 0 (Finset.Icc 1 (n - 1)) := by
  ext k
  simp
  omega

theorem convCoeffZ_sigmaPowZ_one_eisensteinE4CoeffZ (n : Nat) :
    convCoeffZ (sigmaPowZ 1) eisensteinE4CoeffZ n =
      sigmaPowZ 1 n + 240 * sigma1Sigma3ConvZ n := by
  by_cases hn : n = 0
  · subst n
    norm_num [convCoeffZ, sigmaPowZ, sigma1Sigma3ConvZ, eisensteinE4CoeffZ,
      Nat.divisorSum]
  · unfold convCoeffZ sigma1Sigma3ConvZ
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    rw [Finset.sum_range_succ]
    have hlast :
        sigmaPowZ 1 n * eisensteinE4CoeffZ (n - n) = sigmaPowZ 1 n := by
      simp [eisensteinE4CoeffZ]
    rw [hlast]
    have hmiddle :
        (∑ x ∈ Finset.range n, sigmaPowZ 1 x * eisensteinE4CoeffZ (n - x)) =
          240 * ∑ x ∈ Finset.Icc 1 (n - 1),
            sigmaPowZ 1 x * sigmaPowZ 3 (n - x) := by
      rw [range_eq_insert_Icc_one_pred n hn]
      rw [Finset.sum_insert]
      · simp [sigmaPowZ, Nat.divisorSum]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        have hx1 : 1 ≤ x := (Finset.mem_Icc.mp hx).1
        have hxn : x ≤ n - 1 := (Finset.mem_Icc.mp hx).2
        have hn_sub_ne : n - x ≠ 0 := by omega
        simp [eisensteinE4CoeffZ, hn_sub_ne]
        have hsig1 :
            (∑ d ∈ Finset.Icc 1 x, if d ∣ x then (d : Int) else 0) =
              sigmaPowZ 1 x := by
          simp [sigmaPowZ, Nat.divisorSum]
        have hsig3 :
            (∑ d ∈ Finset.Icc 1 (n - x),
              if d ∣ n - x then (d : Int) ^ 3 else 0) =
              sigmaPowZ 3 (n - x) := by
          simp [sigmaPowZ, Nat.divisorSum]
        have hring :
            sigmaPowZ 1 x * (240 * sigmaPowZ 3 (n - x)) =
              240 * (sigmaPowZ 1 x * sigmaPowZ 3 (n - x)) := by
          ring
        simpa [hsig1, hsig3] using hring
      · simp
    rw [hmiddle]
    ring

theorem ramanujanThetaE4ResidualCoeffZ_eq_zero_all (n : Nat) :
    ramanujanThetaE4ResidualCoeffZ n = 0 := by
  have h := ramanujanThetaE4ArithmeticIdentityAt_all n
  unfold ramanujanThetaE4ArithmeticIdentityAt at h
  unfold ramanujanThetaE4ResidualCoeffZ
  rw [convCoeffZ_eisensteinE2CoeffZ_left,
    convCoeffZ_sigmaPowZ_one_eisensteinE4CoeffZ]
  by_cases hn : n = 0
  · subst n
    norm_num [eisensteinE4CoeffZ, eisensteinE6CoeffZ, sigmaPowZ,
      sigma1Sigma3ConvZ, Nat.divisorSum]
  · simp [eisensteinE4CoeffZ, eisensteinE6CoeffZ, hn]
    nlinarith

theorem coeff_eisensteinE4PS_sq_eq_coeffZ (n : Nat) :
    (eisensteinE4PS ^ 2).coeff n =
      (eisensteinE4SquaredCoeffZ n : ℚ) := by
  rw [pow_two]
  unfold eisensteinE4SquaredCoeffZ
  exact coeff_mul_eq_convCoeffZ eisensteinE4CoeffZ eisensteinE4CoeffZ
    eisensteinE4PS eisensteinE4PS
    coeff_eisensteinE4PS_eq_coeffZ coeff_eisensteinE4PS_eq_coeffZ n

theorem coeff_eisensteinE4PS_cube_eq_coeffZ (n : Nat) :
    (eisensteinE4PS ^ 3).coeff n =
      (eisensteinE4CubedCoeffZ n : ℚ) := by
  rw [show eisensteinE4PS ^ 3 = eisensteinE4PS ^ 2 * eisensteinE4PS by ring]
  unfold eisensteinE4CubedCoeffZ
  exact coeff_mul_eq_convCoeffZ eisensteinE4SquaredCoeffZ eisensteinE4CoeffZ
    (eisensteinE4PS ^ 2) eisensteinE4PS
    coeff_eisensteinE4PS_sq_eq_coeffZ coeff_eisensteinE4PS_eq_coeffZ n

theorem coeff_eisensteinE6PS_sq_eq_coeffZ (n : Nat) :
    (eisensteinE6PS ^ 2).coeff n =
      (eisensteinE6SquaredCoeffZ n : ℚ) := by
  rw [pow_two]
  unfold eisensteinE6SquaredCoeffZ
  exact coeff_mul_eq_convCoeffZ eisensteinE6CoeffZ eisensteinE6CoeffZ
    eisensteinE6PS eisensteinE6PS
    coeff_eisensteinE6PS_eq_coeffZ coeff_eisensteinE6PS_eq_coeffZ n

theorem coeff_eisensteinDiscriminantLHS_eq_coeffZ (n : Nat) :
    eisensteinDiscriminantLHS.coeff n =
      (eisensteinDiscriminantLHSCoeffZ n : ℚ) := by
  unfold eisensteinDiscriminantLHS eisensteinDiscriminantLHSCoeffZ
  rw [map_sub, coeff_eisensteinE4PS_cube_eq_coeffZ,
    coeff_eisensteinE6PS_sq_eq_coeffZ]
  push_cast
  ring

theorem coeff_eisensteinDiscriminantLHSThetaResidual (n : Nat) :
    (thetaOp eisensteinDiscriminantLHS -
      eisensteinE2PS * eisensteinDiscriminantLHS).coeff n =
      (eisensteinDiscriminantLHSThetaResidualCoeffZ n : ℚ) := by
  unfold eisensteinDiscriminantLHSThetaResidualCoeffZ
  rw [map_sub, coeff_thetaOp,
    coeff_mul_eq_convCoeffZ eisensteinE2CoeffZ eisensteinDiscriminantLHSCoeffZ
      eisensteinE2PS eisensteinDiscriminantLHS
      coeff_eisensteinE2PS_eq_coeffZ coeff_eisensteinDiscriminantLHS_eq_coeffZ,
    coeff_eisensteinDiscriminantLHS_eq_coeffZ]
  push_cast
  ring

theorem coeff_eisensteinDiscriminantLHSThetaResidual_mixedCoeffZ (n : Nat) :
    (thetaOp eisensteinDiscriminantLHS -
      eisensteinE2PS * eisensteinDiscriminantLHS).coeff n =
      (eisensteinDiscriminantLHSThetaResidualMixedCoeffZ n : ℚ) := by
  unfold eisensteinDiscriminantLHSThetaResidualMixedCoeffZ
  rw [map_sub, coeff_thetaOp,
    coeff_mul_eq_convCoeffZ eisensteinE2CoeffZ eisensteinDiscriminantLHSMixedCoeffZ
      eisensteinE2PS eisensteinDiscriminantLHS
      coeff_eisensteinE2PS_eq_coeffZ coeff_eisensteinDiscriminantLHS_eq_mixedCoeffZ,
    coeff_eisensteinDiscriminantLHS_eq_mixedCoeffZ,
    convCoeffZ_eisensteinE2CoeffZ_left]
  push_cast
  ring

def eisensteinDiscriminantLHSThetaResidualCoeffZThroughCheck (N : Nat) : Bool :=
  (List.range (N + 1)).all fun n =>
    decide (eisensteinDiscriminantLHSThetaResidualCoeffZ n = 0)

def eisensteinDiscriminantLHSThetaResidualMixedCoeffZThroughCheck (N : Nat) : Bool :=
  (List.range (N + 1)).all fun n =>
    decide (eisensteinDiscriminantLHSThetaResidualMixedCoeffZ n = 0)

def eisensteinDiscriminantLHSThetaResidualCoeffZThrough100Check : Bool :=
  eisensteinDiscriminantLHSThetaResidualCoeffZThroughCheck 100

set_option maxHeartbeats 8000000 in
theorem eisensteinDiscriminantLHSThetaResidualCoeffZThrough100Check_true :
    eisensteinDiscriminantLHSThetaResidualCoeffZThrough100Check = true := by
  native_decide

def eisensteinDiscriminantLHSThetaResidualMixedCoeffZThrough100Check : Bool :=
  eisensteinDiscriminantLHSThetaResidualMixedCoeffZThroughCheck 100

theorem eisensteinDiscriminantLHS_theta_residual_coeff_zero_through_of_check
    {N : Nat}
    (hcheck : eisensteinDiscriminantLHSThetaResidualCoeffZThroughCheck N = true)
    (n : Nat) (hn : n ≤ N) :
    (thetaOp eisensteinDiscriminantLHS -
      eisensteinE2PS * eisensteinDiscriminantLHS).coeff n = 0 := by
  have hall := List.all_eq_true.mp hcheck
  have hnrange : n ∈ List.range (N + 1) := List.mem_range.mpr (by omega)
  have hbody := hall n hnrange
  have hz : eisensteinDiscriminantLHSThetaResidualCoeffZ n = 0 := by
    exact of_decide_eq_true hbody
  have hc := coeff_eisensteinDiscriminantLHSThetaResidual n
  rw [hz] at hc
  simpa using hc

theorem eisensteinDiscriminantLHS_theta_residual_coeff_zero_through_one_hundred
    (n : Nat) (hn : n ≤ 100) :
    (thetaOp eisensteinDiscriminantLHS -
      eisensteinE2PS * eisensteinDiscriminantLHS).coeff n = 0 :=
  eisensteinDiscriminantLHS_theta_residual_coeff_zero_through_of_check
    eisensteinDiscriminantLHSThetaResidualCoeffZThrough100Check_true n hn

theorem eisensteinDiscriminantLHS_theta_eq_of_residualCoeffZ_eq_zero
    (h : ∀ n : Nat, eisensteinDiscriminantLHSThetaResidualCoeffZ n = 0) :
    thetaOp eisensteinDiscriminantLHS =
      eisensteinE2PS * eisensteinDiscriminantLHS := by
  apply sub_eq_zero.mp
  ext n
  have hc := coeff_eisensteinDiscriminantLHSThetaResidual n
  rw [h n] at hc
  simpa using hc

theorem eisensteinDiscriminantLHS_theta_eq_of_mixedResidualCoeffZ_eq_zero
    (h : ∀ n : Nat, eisensteinDiscriminantLHSThetaResidualMixedCoeffZ n = 0) :
    thetaOp eisensteinDiscriminantLHS =
      eisensteinE2PS * eisensteinDiscriminantLHS := by
  apply sub_eq_zero.mp
  ext n
  have hc := coeff_eisensteinDiscriminantLHSThetaResidual_mixedCoeffZ n
  rw [h n] at hc
  simpa using hc

/-- If the coefficient residual for `E4` vanishes in every degree, then the
formal Ramanujan theta equation for `E4` follows. -/
theorem RamanujanThetaE4_of_residualCoeffZ_eq_zero
    (h : ∀ n : Nat, ramanujanThetaE4ResidualCoeffZ n = 0) :
    RamanujanThetaE4 := by
  unfold RamanujanThetaE4
  apply sub_eq_zero.mp
  ext n
  have hc := coeff_ramanujanThetaE4Residual n
  unfold residual3E4PS at hc
  rw [h n] at hc
  simpa using hc

theorem RamanujanThetaE4_all : RamanujanThetaE4 :=
  RamanujanThetaE4_of_residualCoeffZ_eq_zero
    ramanujanThetaE4ResidualCoeffZ_eq_zero_all

/-- If the coefficient residual for `E6` vanishes in every degree, then the
formal Ramanujan theta equation for `E6` follows. -/
theorem RamanujanThetaE6_of_residualCoeffZ_eq_zero
    (h : ∀ n : Nat, ramanujanThetaE6ResidualCoeffZ n = 0) :
    RamanujanThetaE6 := by
  unfold RamanujanThetaE6
  apply sub_eq_zero.mp
  ext n
  have hc := coeff_ramanujanThetaE6Residual n
  unfold residual2E6PS at hc
  rw [h n] at hc
  simpa using hc

theorem convCoeffZ_sigmaPowZ_one_eisensteinE6CoeffZ (n : Nat) :
    convCoeffZ (sigmaPowZ 1) eisensteinE6CoeffZ n =
      sigmaPowZ 1 n - 504 * sigma1Sigma5ConvZ n := by
  by_cases hn : n = 0
  · subst n
    norm_num [convCoeffZ, sigmaPowZ, sigma1Sigma5ConvZ, eisensteinE6CoeffZ,
      Nat.divisorSum]
  · unfold convCoeffZ sigma1Sigma5ConvZ
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    rw [Finset.sum_range_succ]
    have hlast :
        sigmaPowZ 1 n * eisensteinE6CoeffZ (n - n) = sigmaPowZ 1 n := by
      simp [eisensteinE6CoeffZ]
    rw [hlast]
    have hmiddle :
        (∑ x ∈ Finset.range n, sigmaPowZ 1 x * eisensteinE6CoeffZ (n - x)) =
          -504 * ∑ x ∈ Finset.Icc 1 (n - 1),
            sigmaPowZ 1 x * sigmaPowZ 5 (n - x) := by
      rw [range_eq_insert_Icc_one_pred n hn]
      rw [Finset.sum_insert]
      · have hsigma0 : sigmaPowZ 1 0 = 0 := by
          simp [sigmaPowZ, Nat.divisorSum]
        have hzeroTerm :
            sigmaPowZ 1 0 * eisensteinE6CoeffZ (n - 0) = 0 := by
          rw [hsigma0, zero_mul]
        rw [hzeroTerm, zero_add]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        have hx1 : 1 ≤ x := (Finset.mem_Icc.mp hx).1
        have hxn : x ≤ n - 1 := (Finset.mem_Icc.mp hx).2
        have hn_sub_ne : n - x ≠ 0 := by omega
        simp [eisensteinE6CoeffZ, hn_sub_ne]
        have hsig1 :
            (∑ d ∈ Finset.Icc 1 x, if d ∣ x then (d : Int) else 0) =
              sigmaPowZ 1 x := by
          simp [sigmaPowZ, Nat.divisorSum]
        have hsig5 :
            (∑ d ∈ Finset.Icc 1 (n - x),
              if d ∣ n - x then (d : Int) ^ 5 else 0) =
              sigmaPowZ 5 (n - x) := by
          simp [sigmaPowZ, Nat.divisorSum]
        have hring :
            sigmaPowZ 1 x * (-504 * sigmaPowZ 5 (n - x)) =
              -504 * (sigmaPowZ 1 x * sigmaPowZ 5 (n - x)) := by
          ring
        simpa [hsig1, hsig5] using hring
      · simp
    rw [hmiddle]
    ring

theorem convCoeffZ_eisensteinE4CoeffZ_eisensteinE4CoeffZ (n : Nat) :
    convCoeffZ eisensteinE4CoeffZ eisensteinE4CoeffZ n =
      (if n = 0 then 1 else 0) + 480 * sigmaPowZ 3 n +
        57600 * sigma3Sigma3ConvZ n := by
  by_cases hn : n = 0
  · subst n
    norm_num [convCoeffZ, sigmaPowZ, sigma3Sigma3ConvZ, eisensteinE4CoeffZ,
      Nat.divisorSum]
  · unfold convCoeffZ sigma3Sigma3ConvZ
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    rw [Finset.sum_range_succ]
    have hlast :
        eisensteinE4CoeffZ n * eisensteinE4CoeffZ (n - n) =
          240 * sigmaPowZ 3 n := by
      simp [eisensteinE4CoeffZ, hn]
    rw [hlast]
    rw [range_eq_insert_Icc_one_pred n hn]
    rw [Finset.sum_insert]
    · simp [eisensteinE4CoeffZ, hn]
      have hsum :
          (∑ x ∈ Finset.Icc 1 (n - 1),
            if n - x = 0 then if x = 0 then 1 else 240 * sigmaPowZ 3 x
            else if x = 0 then 240 * sigmaPowZ 3 (n - x)
            else 240 * sigmaPowZ 3 x * (240 * sigmaPowZ 3 (n - x))) =
            57600 * ∑ x ∈ Finset.Icc 1 (n - 1),
              sigmaPowZ 3 x * sigmaPowZ 3 (n - x) := by
        calc
          (∑ x ∈ Finset.Icc 1 (n - 1),
            if n - x = 0 then if x = 0 then 1 else 240 * sigmaPowZ 3 x
            else if x = 0 then 240 * sigmaPowZ 3 (n - x)
            else 240 * sigmaPowZ 3 x * (240 * sigmaPowZ 3 (n - x)))
              = ∑ x ∈ Finset.Icc 1 (n - 1),
                  57600 * (sigmaPowZ 3 x * sigmaPowZ 3 (n - x)) := by
                apply Finset.sum_congr rfl
                intro x hx
                have hx0 : x ≠ 0 := by
                  have hx1 : 1 ≤ x := (Finset.mem_Icc.mp hx).1
                  omega
                have hn_sub_ne : n - x ≠ 0 := by
                  have hx1 : 1 ≤ x := (Finset.mem_Icc.mp hx).1
                  have hxn : x ≤ n - 1 := (Finset.mem_Icc.mp hx).2
                  omega
                simp [hx0, hn_sub_ne]
                ring
          _ = 57600 * ∑ x ∈ Finset.Icc 1 (n - 1),
                sigmaPowZ 3 x * sigmaPowZ 3 (n - x) := by
              rw [Finset.mul_sum]
      rw [hsum]
      ring
    · simp

/-- Coefficient arithmetic form of Ramanujan's `E6` theta equation. -/
def ramanujanThetaE6ArithmeticIdentityAt (n : Nat) : Prop :=
  (-1008 : Int) * (n : Int) * sigmaPowZ 5 n =
    -504 * sigmaPowZ 5 n - 24 * sigmaPowZ 1 n +
      12096 * sigma1Sigma5ConvZ n - 480 * sigmaPowZ 3 n -
        57600 * sigma3Sigma3ConvZ n

theorem ramanujanThetaE6ResidualCoeffZ_eq_zero_of_arithmeticIdentityAt
    (n : Nat) (h : ramanujanThetaE6ArithmeticIdentityAt n) :
    ramanujanThetaE6ResidualCoeffZ n = 0 := by
  unfold ramanujanThetaE6ResidualCoeffZ
  rw [convCoeffZ_eisensteinE2CoeffZ_left,
    convCoeffZ_sigmaPowZ_one_eisensteinE6CoeffZ,
    convCoeffZ_eisensteinE4CoeffZ_eisensteinE4CoeffZ]
  unfold ramanujanThetaE6ArithmeticIdentityAt at h
  by_cases hn : n = 0
  · subst n
    norm_num [eisensteinE4CoeffZ, eisensteinE6CoeffZ, sigmaPowZ,
      sigma1Sigma5ConvZ, sigma3Sigma3ConvZ, Nat.divisorSum]
  · simp [eisensteinE6CoeffZ, hn]
    nlinarith

theorem RamanujanThetaE6_of_arithmeticIdentity_all
    (h : ∀ n : Nat, ramanujanThetaE6ArithmeticIdentityAt n) :
    RamanujanThetaE6 :=
  RamanujanThetaE6_of_residualCoeffZ_eq_zero
    (fun n => ramanujanThetaE6ResidualCoeffZ_eq_zero_of_arithmeticIdentityAt n (h n))

theorem ramanujanThetaE6ArithmeticIdentityAt_all (n : Nat) :
    ramanujanThetaE6ArithmeticIdentityAt n := by
  unfold ramanujanThetaE6ArithmeticIdentityAt
  have h :
      (12096 : Int) * sigma1Sigma5ConvZ n -
        57600 * sigma3Sigma3ConvZ n =
          -1008 * (n : Int) * sigmaPowZ 5 n +
            504 * sigmaPowZ 5 n + 24 * sigmaPowZ 1 n +
              480 * sigmaPowZ 3 n := by
    simpa [sigmaPowZ, sigma1Sigma5ConvZ, sigma3Sigma3ConvZ,
      _root_.QseriesFormalization.Pending.Ch20LiouvilleConvolution.sigmaPowZ,
      _root_.QseriesFormalization.Pending.Ch20LiouvilleConvolution.sigmaSigmaConvZ]
      using
        _root_.QseriesFormalization.Pending.Ch20LiouvilleConvolution.e6_sigma_convolution_identity n
  nlinarith

theorem RamanujanThetaE6_all : RamanujanThetaE6 :=
  RamanujanThetaE6_of_arithmeticIdentity_all
    ramanujanThetaE6ArithmeticIdentityAt_all

theorem coeff_zero_residual3E4PS : residual3E4PS.coeff 0 = 0 := by
  have hc := coeff_ramanujanThetaE4Residual 0
  norm_num [ramanujanThetaE4ResidualCoeffZ, eisensteinE4CoeffZ,
    eisensteinE2CoeffZ, eisensteinE6CoeffZ, convCoeffZ, sigmaPowZ,
    Nat.divisorSum] at hc
  simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hc

theorem coeff_zero_residual2E6PS : residual2E6PS.coeff 0 = 0 := by
  have hc := coeff_ramanujanThetaE6Residual 0
  norm_num [ramanujanThetaE6ResidualCoeffZ, eisensteinE4CoeffZ,
    eisensteinE2CoeffZ, eisensteinE6CoeffZ, convCoeffZ, sigmaPowZ,
    Nat.divisorSum] at hc
  simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hc

theorem residual3E4PS_eq_zero_of_theta_eq_mul
    {C : ℚ⟦X⟧} (hC0 : C.coeff 0 = 0)
    (hθ : thetaOp residual3E4PS = C * residual3E4PS) :
    residual3E4PS = 0 :=
  eq_zero_of_theta_eq_mul_coeff_zero hC0 coeff_zero_residual3E4PS hθ

theorem residual2E6PS_eq_zero_of_theta_eq_mul
    {C : ℚ⟦X⟧} (hC0 : C.coeff 0 = 0)
    (hθ : thetaOp residual2E6PS = C * residual2E6PS) :
    residual2E6PS = 0 :=
  eq_zero_of_theta_eq_mul_coeff_zero hC0 coeff_zero_residual2E6PS hθ

theorem RamanujanThetaE4_of_residual3E4PS_eq_zero
    (h : residual3E4PS = 0) :
    RamanujanThetaE4 := by
  unfold RamanujanThetaE4
  unfold residual3E4PS at h
  exact sub_eq_zero.mp h

theorem RamanujanThetaE6_of_residual2E6PS_eq_zero
    (h : residual2E6PS = 0) :
    RamanujanThetaE6 := by
  unfold RamanujanThetaE6
  unfold residual2E6PS at h
  exact sub_eq_zero.mp h

theorem RamanujanThetaE4_of_residual3E4PS_theta_eq_mul
    {C : ℚ⟦X⟧} (hC0 : C.coeff 0 = 0)
    (hθ : thetaOp residual3E4PS = C * residual3E4PS) :
    RamanujanThetaE4 :=
  RamanujanThetaE4_of_residual3E4PS_eq_zero
    (residual3E4PS_eq_zero_of_theta_eq_mul hC0 hθ)

theorem RamanujanThetaE6_of_residual2E6PS_theta_eq_mul
    {C : ℚ⟦X⟧} (hC0 : C.coeff 0 = 0)
    (hθ : thetaOp residual2E6PS = C * residual2E6PS) :
    RamanujanThetaE6 :=
  RamanujanThetaE6_of_residual2E6PS_eq_zero
    (residual2E6PS_eq_zero_of_theta_eq_mul hC0 hθ)

def residual3E4CoeffQ (n : Nat) : ℚ :=
  (ramanujanThetaE4ResidualCoeffZ n : ℚ)

def residual2E6CoeffQ (n : Nat) : ℚ :=
  (ramanujanThetaE6ResidualCoeffZ n : ℚ)

theorem eq_zero_of_const_coeff_recurrence
    {a : Nat → ℚ} {k : Nat} {c : Nat → ℚ}
    (hk : 0 < k)
    (hc0 : c 0 ≠ 0)
    (hinit : ∀ n, n < k → a n = 0)
    (hrec : ∀ n, k ≤ n →
      c 0 * a n + ∑ i ∈ Finset.Icc 1 k, c i * a (n - i) = 0) :
    ∀ n, a n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hnk : n < k
      · exact hinit n hnk
      · have hkn : k ≤ n := le_of_not_gt hnk
        have hsum :
            (∑ i ∈ Finset.Icc 1 k, c i * a (n - i)) = 0 := by
          refine Finset.sum_eq_zero ?_
          intro i hi
          have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
          have hik : i ≤ k := (Finset.mem_Icc.mp hi).2
          have hilt : n - i < n := by
            exact Nat.sub_lt (lt_of_lt_of_le hk hkn) hi1
          rw [ih (n - i) hilt, mul_zero]
        have hr := hrec n hkn
        rw [hsum, add_zero] at hr
        exact (mul_eq_zero.mp hr).resolve_left hc0

theorem RamanujanThetaE4_of_residual3E4CoeffQ_eq_zero
    (h : ∀ n : Nat, residual3E4CoeffQ n = 0) :
    RamanujanThetaE4 := by
  unfold RamanujanThetaE4
  apply sub_eq_zero.mp
  ext n
  have hc := coeff_ramanujanThetaE4Residual n
  unfold residual3E4PS at hc
  have hz := h n
  unfold residual3E4CoeffQ at hz
  rw [hz] at hc
  simpa using hc

theorem RamanujanThetaE6_of_residual2E6CoeffQ_eq_zero
    (h : ∀ n : Nat, residual2E6CoeffQ n = 0) :
    RamanujanThetaE6 := by
  unfold RamanujanThetaE6
  apply sub_eq_zero.mp
  ext n
  have hc := coeff_ramanujanThetaE6Residual n
  unfold residual2E6PS at hc
  have hz := h n
  unfold residual2E6CoeffQ at hz
  rw [hz] at hc
  simpa using hc

theorem RamanujanThetaE4_of_residual3E4_const_coeff_recurrence
    {k : Nat} {c : Nat → ℚ}
    (hk : 0 < k)
    (hc0 : c 0 ≠ 0)
    (hinit : ∀ n, n < k → residual3E4CoeffQ n = 0)
    (hrec : ∀ n, k ≤ n →
      c 0 * residual3E4CoeffQ n +
        ∑ i ∈ Finset.Icc 1 k, c i * residual3E4CoeffQ (n - i) = 0) :
    RamanujanThetaE4 :=
  RamanujanThetaE4_of_residual3E4CoeffQ_eq_zero
    (eq_zero_of_const_coeff_recurrence hk hc0 hinit hrec)

theorem RamanujanThetaE6_of_residual2E6_const_coeff_recurrence
    {k : Nat} {c : Nat → ℚ}
    (hk : 0 < k)
    (hc0 : c 0 ≠ 0)
    (hinit : ∀ n, n < k → residual2E6CoeffQ n = 0)
    (hrec : ∀ n, k ≤ n →
      c 0 * residual2E6CoeffQ n +
        ∑ i ∈ Finset.Icc 1 k, c i * residual2E6CoeffQ (n - i) = 0) :
    RamanujanThetaE6 :=
  RamanujanThetaE6_of_residual2E6CoeffQ_eq_zero
    (eq_zero_of_const_coeff_recurrence hk hc0 hinit hrec)

/-- Executable finite certificate for the two Ramanujan theta residuals through
degree `N`. -/
def ramanujanThetaResidualCoeffZThroughCheck (N : Nat) : Bool :=
  (List.range (N + 1)).all fun n =>
    decide (ramanujanThetaE4ResidualCoeffZ n = 0 ∧
      ramanujanThetaE6ResidualCoeffZ n = 0)

/-- The original small finite certificate through degree `10`. -/
def ramanujanThetaResidualCoeffZThrough10Check : Bool :=
  ramanujanThetaResidualCoeffZThroughCheck 10

theorem ramanujanThetaResidualCoeffZThrough10Check_true :
    ramanujanThetaResidualCoeffZThrough10Check = true := by
  native_decide

/-- The same executable residual check scaled to degree `50`. -/
def ramanujanThetaResidualCoeffZThrough50Check : Bool :=
  ramanujanThetaResidualCoeffZThroughCheck 50

theorem ramanujanThetaResidualCoeffZThrough50Check_true :
    ramanujanThetaResidualCoeffZThrough50Check = true := by
  native_decide

/-- The same executable residual check scaled to degree `100`. -/
def ramanujanThetaResidualCoeffZThrough100Check : Bool :=
  ramanujanThetaResidualCoeffZThroughCheck 100

set_option maxHeartbeats 8000000 in
theorem ramanujanThetaResidualCoeffZThrough100Check_true :
    ramanujanThetaResidualCoeffZThrough100Check = true := by
  native_decide

/-- The same executable residual check scaled to degree `500`. -/
def ramanujanThetaResidualCoeffZThrough500Check : Bool :=
  ramanujanThetaResidualCoeffZThroughCheck 500

set_option maxHeartbeats 50000000 in
theorem ramanujanThetaResidualCoeffZThrough500Check_true :
    ramanujanThetaResidualCoeffZThrough500Check = true := by
  native_decide

theorem ramanujanThetaResidual_coeff_zero_through_of_check
    {N : Nat} (hcheck : ramanujanThetaResidualCoeffZThroughCheck N = true)
    (n : Nat) (hn : n ≤ N) :
    (((3 : ℚ⟦X⟧) * thetaOp eisensteinE4PS -
        (eisensteinE2PS * eisensteinE4PS - eisensteinE6PS)).coeff n = 0) ∧
    (((2 : ℚ⟦X⟧) * thetaOp eisensteinE6PS -
        (eisensteinE2PS * eisensteinE6PS - eisensteinE4PS ^ 2)).coeff n = 0) := by
  have hall := List.all_eq_true.mp hcheck
  have hnrange : n ∈ List.range (N + 1) := List.mem_range.mpr (by omega)
  have hbody := hall n hnrange
  have hpair :
      ramanujanThetaE4ResidualCoeffZ n = 0 ∧
        ramanujanThetaE6ResidualCoeffZ n = 0 := by
    exact of_decide_eq_true hbody
  constructor
  · have hc := coeff_ramanujanThetaE4Residual n
    rw [hpair.1] at hc
    simpa using hc
  · have hc := coeff_ramanujanThetaE6Residual n
    rw [hpair.2] at hc
    simpa using hc

theorem ramanujanThetaResidual_coeff_zero_through_ten
    (n : Nat) (hn : n ≤ 10) :
    (((3 : ℚ⟦X⟧) * thetaOp eisensteinE4PS -
        (eisensteinE2PS * eisensteinE4PS - eisensteinE6PS)).coeff n = 0) ∧
    (((2 : ℚ⟦X⟧) * thetaOp eisensteinE6PS -
        (eisensteinE2PS * eisensteinE6PS - eisensteinE4PS ^ 2)).coeff n = 0) :=
  ramanujanThetaResidual_coeff_zero_through_of_check
    ramanujanThetaResidualCoeffZThrough10Check_true n hn

theorem ramanujanThetaResidual_coeff_zero_through_fifty
    (n : Nat) (hn : n ≤ 50) :
    (((3 : ℚ⟦X⟧) * thetaOp eisensteinE4PS -
        (eisensteinE2PS * eisensteinE4PS - eisensteinE6PS)).coeff n = 0) ∧
    (((2 : ℚ⟦X⟧) * thetaOp eisensteinE6PS -
        (eisensteinE2PS * eisensteinE6PS - eisensteinE4PS ^ 2)).coeff n = 0) :=
  ramanujanThetaResidual_coeff_zero_through_of_check
    ramanujanThetaResidualCoeffZThrough50Check_true n hn

theorem ramanujanThetaResidual_coeff_zero_through_one_hundred
    (n : Nat) (hn : n ≤ 100) :
    (((3 : ℚ⟦X⟧) * thetaOp eisensteinE4PS -
        (eisensteinE2PS * eisensteinE4PS - eisensteinE6PS)).coeff n = 0) ∧
    (((2 : ℚ⟦X⟧) * thetaOp eisensteinE6PS -
        (eisensteinE2PS * eisensteinE6PS - eisensteinE4PS ^ 2)).coeff n = 0) :=
  ramanujanThetaResidual_coeff_zero_through_of_check
    ramanujanThetaResidualCoeffZThrough100Check_true n hn

theorem ramanujanThetaResidual_coeff_zero_through_five_hundred
    (n : Nat) (hn : n ≤ 500) :
    (((3 : ℚ⟦X⟧) * thetaOp eisensteinE4PS -
        (eisensteinE2PS * eisensteinE4PS - eisensteinE6PS)).coeff n = 0) ∧
    (((2 : ℚ⟦X⟧) * thetaOp eisensteinE6PS -
        (eisensteinE2PS * eisensteinE6PS - eisensteinE4PS ^ 2)).coeff n = 0) :=
  ramanujanThetaResidual_coeff_zero_through_of_check
    ramanujanThetaResidualCoeffZThrough500Check_true n hn

/-- The Eisenstein-side numerator satisfies `theta F = E2 * F`, assuming the
two Ramanujan theta equations for `E4` and `E6`. -/
theorem eisensteinDiscriminantLHS_theta_eq_of_ramanujan
    (hE4 : RamanujanThetaE4) (hE6 : RamanujanThetaE6) :
    thetaOp eisensteinDiscriminantLHS =
      eisensteinE2PS * eisensteinDiscriminantLHS := by
  unfold RamanujanThetaE4 at hE4
  unfold RamanujanThetaE6 at hE6
  unfold eisensteinDiscriminantLHS
  calc
    thetaOp (eisensteinE4PS ^ 3 - eisensteinE6PS ^ 2)
        = (3 : ℚ⟦X⟧) * eisensteinE4PS ^ 2 * thetaOp eisensteinE4PS -
          (2 : ℚ⟦X⟧) * eisensteinE6PS * thetaOp eisensteinE6PS := by
            rw [thetaOp_sub, thetaOp_pow, thetaOp_pow]
            norm_num
    _ = eisensteinE4PS ^ 2 * ((3 : ℚ⟦X⟧) * thetaOp eisensteinE4PS) -
          eisensteinE6PS * ((2 : ℚ⟦X⟧) * thetaOp eisensteinE6PS) := by
            ring
    _ = eisensteinE4PS ^ 2 *
          (eisensteinE2PS * eisensteinE4PS - eisensteinE6PS) -
          eisensteinE6PS *
          (eisensteinE2PS * eisensteinE6PS - eisensteinE4PS ^ 2) := by
            rw [hE4, hE6]
    _ = eisensteinE2PS *
          (eisensteinE4PS ^ 3 - eisensteinE6PS ^ 2) := by
            ring

/-- Conditional assembly theorem: once the two formal Ramanujan differential
equations are proved from the sigma-convolution identities, the formal
Eisenstein discriminant identity follows. -/
theorem eisensteinE4_cubed_sub_eisensteinE6_squared_eq_1728_discriminantPS
    (hE4 : RamanujanThetaE4) (hE6 : RamanujanThetaE6) :
    eisensteinE4PS ^ 3 - eisensteinE6PS ^ 2 =
      (PowerSeries.C (1728 : ℚ)) * discriminantPS ℚ := by
  change eisensteinDiscriminantLHS = eisensteinDiscriminantRHS
  apply eq_of_same_theta_eq_mul_coeff_zero_one (A := eisensteinE2PS)
  · exact coeff_zero_eisensteinE2PS
  · exact eisensteinDiscriminantLHS_theta_eq_of_ramanujan hE4 hE6
  · exact eisensteinDiscriminantRHS_theta_eq
  · rw [coeff_zero_eisensteinDiscriminantLHS, coeff_zero_eisensteinDiscriminantRHS]
  · rw [coeff_one_eisensteinDiscriminantLHS, coeff_one_eisensteinDiscriminantRHS]

theorem eisensteinE4_cubed_sub_eisensteinE6_squared_eq_1728_discriminantPS_of_RamanujanThetaE6
    (hE6 : RamanujanThetaE6) :
    eisensteinE4PS ^ 3 - eisensteinE6PS ^ 2 =
      (PowerSeries.C (1728 : ℚ)) * discriminantPS ℚ :=
  eisensteinE4_cubed_sub_eisensteinE6_squared_eq_1728_discriminantPS
    RamanujanThetaE4_all hE6

theorem eisensteinE4_cubed_sub_eisensteinE6_squared_eq_1728_discriminantPS_of_lhs_theta
    (hF : thetaOp eisensteinDiscriminantLHS =
      eisensteinE2PS * eisensteinDiscriminantLHS) :
    eisensteinE4PS ^ 3 - eisensteinE6PS ^ 2 =
      (PowerSeries.C (1728 : ℚ)) * discriminantPS ℚ := by
  change eisensteinDiscriminantLHS = eisensteinDiscriminantRHS
  apply eq_of_same_theta_eq_mul_coeff_zero_one (A := eisensteinE2PS)
  · exact coeff_zero_eisensteinE2PS
  · exact hF
  · exact eisensteinDiscriminantRHS_theta_eq
  · rw [coeff_zero_eisensteinDiscriminantLHS, coeff_zero_eisensteinDiscriminantRHS]
  · rw [coeff_one_eisensteinDiscriminantLHS, coeff_one_eisensteinDiscriminantRHS]

theorem eisensteinE4_cubed_sub_eisensteinE6_squared_eq_1728_discriminantPS_of_lhs_residualCoeffZ
    (h : ∀ n : Nat, eisensteinDiscriminantLHSThetaResidualCoeffZ n = 0) :
    eisensteinE4PS ^ 3 - eisensteinE6PS ^ 2 =
      (PowerSeries.C (1728 : ℚ)) * discriminantPS ℚ :=
  eisensteinE4_cubed_sub_eisensteinE6_squared_eq_1728_discriminantPS_of_lhs_theta
    (eisensteinDiscriminantLHS_theta_eq_of_residualCoeffZ_eq_zero h)

theorem eisensteinE4_cubed_sub_eisensteinE6_squared_eq_1728_discriminantPS_of_lhs_mixedResidualCoeffZ
    (h : ∀ n : Nat, eisensteinDiscriminantLHSThetaResidualMixedCoeffZ n = 0) :
    eisensteinE4PS ^ 3 - eisensteinE6PS ^ 2 =
      (PowerSeries.C (1728 : ℚ)) * discriminantPS ℚ :=
  eisensteinE4_cubed_sub_eisensteinE6_squared_eq_1728_discriminantPS_of_lhs_theta
    (eisensteinDiscriminantLHS_theta_eq_of_mixedResidualCoeffZ_eq_zero h)

end Ch20Eisenstein
end Pending
end QseriesFormalization
