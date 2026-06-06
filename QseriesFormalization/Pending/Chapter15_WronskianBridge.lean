import QseriesFormalization.Pending.Chapter15_FormalDeriv
import QseriesFormalization.Pending.Chapter15_R_ODE
import QseriesFormalization.Pending.Chapter15_CoeffVerification
import QseriesFormalization.Pending.JTP_FormalPS_Pentagonal
import QseriesFormalization.Pending.Chapter16_MBI_Proof

/-!
# Chapter 15 — Wronskian bridge: E5-free products and Rogers–Ramanujan derivative

## Mathematical content

The Rogers–Ramanujan Wronskian identity (denominator-cleared form):

  `A · B + 5 · (B · θ(A) − A · θ(B)) = E⁴ · A² · B²`

where:
- `A = rrProductA = (q;q⁵)∞ · (q⁴;q⁵)∞` (E5-free product, `qPochAPPS 1 5 * qPochAPPS 4 5`)
- `B = rrProductB = (q²;q⁵)∞ · (q³;q⁵)∞` (E5-free product, `qPochAPPS 2 5 * qPochAPPS 3 5`)
- `E = qPochInfPS = (q;q)∞`
- `θ = thetaOp` (Euler's theta operator `X d/dX`)

IMPORTANT: `rrProductA/B` do NOT include the `(q⁵;q⁵)∞` factor. They differ
from `pentagonalProduct014PS` and `pentagonalProduct023PS`:
  `pentagonalProduct014PS = rrProductA * qPochAPPS 5 5`
  `pentagonalProduct023PS = rrProductB * qPochAPPS 5 5`

## Proof chain (numerically verified, degree 30, Python)

1. `E = A · B · E₅` (five residue classes mod 5)
2. `A·B + 5·(B·θA − A·θB) = E⁴·A²·B²` (Wronskian, k=2 Milas–Mortenson–Ono)
3. Dividing (2) by `A·B`: `1 + 5·(B·θA − A·θB)/(A·B) = E⁴·A·B = chan15LHSPS`
4. `chan15LHSPS · E₅ = E⁴·A·B·E₅ = E⁴·E = E⁵` ✓
-/

namespace QseriesFormalization
namespace Pending
namespace Ch15WronskianBridge

open Filter
open PowerSeries
open scoped Topology PowerSeries PowerSeries.WithPiTopology
open QseriesFormalization.PartIV.Ch19
open QseriesFormalization.Pending.Ch15FormalDeriv
open QseriesFormalization.Pending.Ch15RODE
open QseriesFormalization.Pending.Ch15CoeffVerification
open QseriesFormalization.Pending.JacobiCubeAnalyticToFormal
open QseriesFormalization.Pending.JTPFormalPSPentagonal
open QseriesFormalization.Pending.Ch16MBIProof

/-! ## E5-free Rogers–Ramanujan products -/

/-- `(q;q⁵)∞ · (q⁴;q⁵)∞` — first RR product without `(q⁵;q⁵)∞`. -/
noncomputable def rrProductA
    (R : Type*) [CommRing R] [TopologicalSpace R] : R⟦X⟧ :=
  qPochAPPS R 1 5 * qPochAPPS R 4 5

/-- `(q²;q⁵)∞ · (q³;q⁵)∞` — second RR product without `(q⁵;q⁵)∞`. -/
noncomputable def rrProductB
    (R : Type*) [CommRing R] [TopologicalSpace R] : R⟦X⟧ :=
  qPochAPPS R 2 5 * qPochAPPS R 3 5

/-! ## Computable coefficient vectors for finite Wronskian checks -/

/-- Coefficients `0..N` of the constant series `1`. -/
def oneCoeffVec (N : Nat) : Vector Int (N + 1) :=
  Vector.ofFn fun j : Fin (N + 1) => if j.1 = 0 then 1 else 0

/-- Safe coefficient access for a vector truncated at degree `N`. -/
def coeffVecGet (N : Nat) (v : Vector Int (N + 1)) (n : Nat) : Int :=
  if h : n < N + 1 then v.get ⟨n, h⟩ else 0

/-- Coefficients `0..N` of the single factor `1 - X^d`. -/
def oneMinusXPowCoeffVec (N d : Nat) : Vector Int (N + 1) :=
  Vector.ofFn fun j : Fin (N + 1) =>
    if j.1 = 0 then 1 else if j.1 = d then -1 else 0

/-- Truncated convolution product, keeping coefficients `0..N`. -/
def truncConvolveCoeffVec
    (N : Nat) (u v : Vector Int (N + 1)) : Vector Int (N + 1) :=
  Vector.ofFn fun j : Fin (N + 1) =>
    ∑ k ∈ Finset.range (j.1 + 1),
      coeffVecGet N u k * coeffVecGet N v (j.1 - k)

/-- Coefficients `0..N` of `(q^a; q^step)_∞`, computed by truncated convolution. -/
def qPochAPCoeffVec (N a step : Nat) : Vector Int (N + 1) :=
  (List.range (N + 1)).foldl
    (fun v k =>
      let d := a + step * k
      if d ≤ N then
        truncConvolveCoeffVec N v (oneMinusXPowCoeffVec N d)
      else
        v)
    (oneCoeffVec N)

/-- Coefficients `0..N` of `(q;q^5)_∞ * (q^4;q^5)_∞`. -/
def rrProductACoeffVec (N : Nat) : Vector Int (N + 1) :=
  truncConvolveCoeffVec N (qPochAPCoeffVec N 1 5) (qPochAPCoeffVec N 4 5)

/-- Coefficients `0..N` of `(q^2;q^5)_∞ * (q^3;q^5)_∞`. -/
def rrProductBCoeffVec (N : Nat) : Vector Int (N + 1) :=
  truncConvolveCoeffVec N (qPochAPCoeffVec N 2 5) (qPochAPCoeffVec N 3 5)

/-- Pointwise addition of truncated coefficient vectors. -/
def addCoeffVec (N : Nat) (u v : Vector Int (N + 1)) : Vector Int (N + 1) :=
  Vector.ofFn fun j : Fin (N + 1) => u.get j + v.get j

/-- Pointwise subtraction of truncated coefficient vectors. -/
def subCoeffVec (N : Nat) (u v : Vector Int (N + 1)) : Vector Int (N + 1) :=
  Vector.ofFn fun j : Fin (N + 1) => u.get j - v.get j

/-- Scalar multiplication of a truncated coefficient vector. -/
def scaleCoeffVec (N : Nat) (c : Int) (v : Vector Int (N + 1)) :
    Vector Int (N + 1) :=
  Vector.ofFn fun j : Fin (N + 1) => c * v.get j

/-- Coefficients `0..N` of `theta f = X d f / dX`. -/
def thetaCoeffVec (N : Nat) (v : Vector Int (N + 1)) : Vector Int (N + 1) :=
  Vector.ofFn fun j : Fin (N + 1) => (j.1 : Int) * v.get j

/-- Truncated powers of a coefficient vector. -/
def truncPowCoeffVec (N : Nat) (v : Vector Int (N + 1)) :
    Nat → Vector Int (N + 1)
  | 0 => oneCoeffVec N
  | e + 1 => truncConvolveCoeffVec N (truncPowCoeffVec N v e) v

/-- Coefficients `0..N` of `(q;q)_∞`, computed as `∏_{d=1}^N (1-q^d)`. -/
def qPochInfCoeffVec (N : Nat) : Vector Int (N + 1) :=
  qPochAPCoeffVec N 1 1

/-- Coefficients `0..N` of `AB + 5 * (B * theta A - A * theta B)`. -/
def wronskianLHSCoeffVec (N : Nat) : Vector Int (N + 1) :=
  let A := rrProductACoeffVec N
  let B := rrProductBCoeffVec N
  let AB := truncConvolveCoeffVec N A B
  let BthetaA := truncConvolveCoeffVec N B (thetaCoeffVec N A)
  let AthetaB := truncConvolveCoeffVec N A (thetaCoeffVec N B)
  addCoeffVec N AB (scaleCoeffVec N 5 (subCoeffVec N BthetaA AthetaB))

/-- Coefficients `0..N` of `E^4 * A^2 * B^2`. -/
def wronskianRHSCoeffVec (N : Nat) : Vector Int (N + 1) :=
  let E := qPochInfCoeffVec N
  let A := rrProductACoeffVec N
  let B := rrProductBCoeffVec N
  truncConvolveCoeffVec N (truncPowCoeffVec N E 4)
    (truncConvolveCoeffVec N (truncPowCoeffVec N A 2) (truncPowCoeffVec N B 2))

set_option maxHeartbeats 800000 in
set_option maxRecDepth 8192 in
/-- The Rogers-Ramanujan Wronskian coefficient identity through degree 15. -/
theorem wronskianCoeffVec_eq_fifteen :
    wronskianLHSCoeffVec 15 = wronskianRHSCoeffVec 15 := by
  decide

/-! ## Relation to pentagonalProduct014PS / pentagonalProduct023PS -/

theorem pentagonalProduct014PS_eq_rrProductA_mul_qPochAPPS55
    (R : Type*) [CommRing R] [TopologicalSpace R] :
    pentagonalProduct014PS R = rrProductA R * qPochAPPS R 5 5 := by
  unfold pentagonalProduct014PS rrProductA
  ring

theorem pentagonalProduct023PS_eq_rrProductB_mul_qPochAPPS55
    (R : Type*) [CommRing R] [TopologicalSpace R] :
    pentagonalProduct023PS R = rrProductB R * qPochAPPS R 5 5 := by
  unfold pentagonalProduct023PS rrProductB
  ring

/-! ## The product P₁₄ · P₂₃ in rrProduct notation -/

/-- `pentagonalProduct014PS · pentagonalProduct023PS = rrProductA · rrProductB · (qPochAPPS 5 5)²` -/
theorem pentagonalProducts_eq_rrProducts_mul_qPochAPPS55_sq
    (R : Type*) [CommRing R] [TopologicalSpace R] :
    pentagonalProduct014PS R * pentagonalProduct023PS R =
      rrProductA R * rrProductB R * (qPochAPPS R 5 5) ^ 2 := by
  rw [pentagonalProduct014PS_eq_rrProductA_mul_qPochAPPS55,
    pentagonalProduct023PS_eq_rrProductB_mul_qPochAPPS55]
  ring

private def finFiveSigmaNatEquivNatBridge : (Sigma fun _ : Fin 5 => ℕ) ≃ ℕ where
  toFun p := 5 * p.2 + p.1.val
  invFun k := Sigma.mk ⟨k % 5, Nat.mod_lt k (by decide)⟩ (k / 5)
  left_inv := by
    rintro ⟨i, n⟩
    simp
    constructor
    · ext
      exact Nat.mod_eq_of_lt i.2
    · have hi : i.val < 5 := i.2
      omega
  right_inv := by
    intro k
    exact Nat.div_add_mod k 5

/-- The five residue classes modulo `5` split Euler's product into the two
E5-free Rogers-Ramanujan factors and the extra `(q^5;q^5)_∞` factor. -/
theorem qPochInfPS_eq_rrProducts_rat :
    qPochInfPS ℚ =
      rrProductA ℚ * rrProductB ℚ * qPochAPPS ℚ 5 5 := by
  let f : ℕ → ℚ⟦X⟧ := fun k => (1 : ℚ⟦X⟧) - PowerSeries.X ^ (k + 1)
  let e : (Sigma fun _ : Fin 5 => ℕ) ≃ ℕ := finFiveSigmaNatEquivNatBridge
  have hf : HasProd f (qPochInfPS ℚ) := by
    rw [qPochInfPS_eq_tprod ℚ]
    exact (multipliable_one_sub_X_pow_succ ℚ).hasProd
  have hsig : HasProd (f ∘ e) (qPochInfPS ℚ) :=
    (Equiv.hasProd_iff e).mpr hf
  have hfiber : ∀ i : Fin 5,
      HasProd (fun n : ℕ => (f ∘ e) (Sigma.mk i n))
        (qPochAPPS ℚ (i.val + 1) 5) := by
    intro i
    convert hasProd_qPochAPPS ℚ (i.val + 1) 5 (by norm_num) using 1
    ext n
    simp [f, e, finFiveSigmaNatEquivNatBridge, apFactorPS]
    congr 1
    ring
  have hfin : HasProd (fun i : Fin 5 => qPochAPPS ℚ (i.val + 1) 5)
      (qPochInfPS ℚ) := hsig.sigma hfiber
  have hfin' : HasProd (fun i : Fin 5 => qPochAPPS ℚ (i.val + 1) 5)
      (∏ i : Fin 5, qPochAPPS ℚ (i.val + 1) 5) := hasProd_fintype _
  have hprod : qPochInfPS ℚ = ∏ i : Fin 5, qPochAPPS ℚ (i.val + 1) 5 :=
    hfin.unique hfin'
  have hsplit : qPochInfPS ℚ =
      qPochAPPS ℚ 1 5 * qPochAPPS ℚ 2 5 * qPochAPPS ℚ 3 5 *
        qPochAPPS ℚ 4 5 * qPochAPPS ℚ 5 5 := by
    rw [hprod]
    norm_num [Fin.prod_univ_five]
  rw [hsplit]
  unfold rrProductA rrProductB
  ring

private theorem continuous_expand_bridge (R : Type*) [CommRing R] [TopologicalSpace R]
    (s : ℕ) (hs : s ≠ 0) :
    Continuous (PowerSeries.expand s hs : R⟦X⟧ → R⟦X⟧) := by
  rw [continuous_iff_continuousAt]
  intro φ
  rw [ContinuousAt, PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
  intro n
  simp_rw [PowerSeries.coeff_expand s hs]
  by_cases hdiv : s ∣ n
  · simpa [hdiv] using
      (PowerSeries.WithPiTopology.continuous_coeff R (n / s)).tendsto φ
  · simpa [hdiv] using tendsto_const_nhds

theorem expand_five_qPochInfPS_eq_qPochAPPS55_rat :
    PowerSeries.expand 5 (by decide) (qPochInfPS ℚ) = qPochAPPS ℚ 5 5 := by
  rw [qPochInfPS_eq_tprod ℚ]
  rw [(multipliable_one_sub_X_pow_succ ℚ).map_tprod
    (PowerSeries.expand 5 (by decide)) (continuous_expand_bridge ℚ 5 (by decide))]
  unfold qPochAPPS
  apply tprod_congr
  intro n
  calc
    PowerSeries.expand 5 (by decide) ((1 : ℚ⟦X⟧) - PowerSeries.X ^ (n + 1))
        = (1 : ℚ⟦X⟧) - PowerSeries.X ^ (5 * (n + 1)) := by
          rw [map_sub, map_one, map_pow, PowerSeries.expand_X, ← pow_mul]
    _ = apFactorPS ℚ 5 5 n := by
          rw [apFactorPS]
          congr 1
          ring

theorem isUnit_qPochAPPS55_rat :
    IsUnit (qPochAPPS ℚ 5 5) := by
  rw [← expand_five_qPochInfPS_eq_qPochAPPS55_rat]
  have hcoeff :
      (PowerSeries.expand 5 (by decide : (5 : ℕ) ≠ 0) (qPochInfPS ℚ)).coeff 0 = 1 := by
    rw [PowerSeries.coeff_expand]
    simp [coeff_zero_qPochInfPS]
  rw [PowerSeries.isUnit_iff_constantCoeff,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply, hcoeff]
  exact isUnit_one

theorem pentagonal014SeriesPS_eq_rrProductA_mul_qPochAPPS55_rat :
    pentagonal014SeriesPS ℚ = rrProductA ℚ * qPochAPPS ℚ 5 5 := by
  rw [← pentagonalProduct014PS_eq_pentagonal014SeriesPS_rat,
    pentagonalProduct014PS_eq_rrProductA_mul_qPochAPPS55]

theorem pentagonal023SeriesPS_eq_rrProductB_mul_qPochAPPS55_rat :
    pentagonal023SeriesPS ℚ = rrProductB ℚ * qPochAPPS ℚ 5 5 := by
  rw [← pentagonalProduct023PS_eq_pentagonal023SeriesPS_rat,
    pentagonalProduct023PS_eq_rrProductB_mul_qPochAPPS55]

/-! ## Logarithmic theta derivative of the AP products -/

noncomputable def divisorGeomPSLocal (R : Type*) [CommRing R] (d : Nat) : R⟦X⟧ :=
  PowerSeries.mk fun n => if d ∣ n ∧ 0 < n then (1 : R) else 0

@[simp] theorem coeff_divisorGeomPSLocal (R : Type*) [CommRing R] (d n : Nat) :
    (divisorGeomPSLocal R d).coeff n = if d ∣ n ∧ 0 < n then (1 : R) else 0 := by
  simp [divisorGeomPSLocal]

private theorem coeff_X_pow_mul_eq_zero_of_lt_local (R : Type*) [CommRing R]
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

private theorem coeff_X_pow_mul_cases_local (R : Type*) [CommRing R]
    (G : R⟦X⟧) (d n : Nat) :
    (PowerSeries.X ^ d * G).coeff n = if d ≤ n then G.coeff (n - d) else 0 := by
  by_cases hdn : d ≤ n
  · have h := PowerSeries.coeff_X_pow_mul G d (n - d)
    rw [if_pos hdn]
    simpa [Nat.sub_add_cancel hdn, Nat.add_comm] using h
  · rw [if_neg hdn]
    exact coeff_X_pow_mul_eq_zero_of_lt_local R G (Nat.lt_of_not_ge hdn)

theorem one_sub_X_pow_mul_divisorGeomPSLocal
    (R : Type*) [CommRing R] {d : Nat} (hd : 0 < d) :
    ((1 : R⟦X⟧) - PowerSeries.X ^ d) * divisorGeomPSLocal R d =
      PowerSeries.X ^ d := by
  ext n
  rw [sub_mul]
  simp only [map_sub]
  rw [coeff_X_pow_mul_cases_local R (divisorGeomPSLocal R d) d n]
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

theorem thetaOp_X_pow_local (R : Type*) [CommRing R] (d : Nat) :
    thetaOp (PowerSeries.X ^ d : R⟦X⟧) =
      PowerSeries.C (d : R) * PowerSeries.X ^ d := by
  ext n
  rw [coeff_thetaOp, PowerSeries.coeff_C_mul]
  rw [PowerSeries.coeff_X_pow]
  split_ifs with h <;> subst_vars <;> simp

theorem thetaOp_one_sub_X_pow_local (R : Type*) [CommRing R] (d : Nat) :
    thetaOp ((1 : R⟦X⟧) - PowerSeries.X ^ d) =
      -PowerSeries.C (d : R) * PowerSeries.X ^ d := by
  rw [thetaOp_sub, thetaOp_one, thetaOp_X_pow_local]
  ring

noncomputable def qPochAPFinitePS (R : Type*) [CommRing R]
    (r m N : ℕ) : R⟦X⟧ :=
  ∏ n ∈ Finset.range N, apFactorPS R r m n

noncomputable def apDivisorSigmaFinitePS (R : Type*) [CommRing R]
    (r m N : ℕ) : R⟦X⟧ :=
  PowerSeries.mk fun n =>
    ∑ k ∈ Finset.range N,
      if r + m * k ∣ n ∧ 0 < n then ((r + m * k : ℕ) : R) else 0

noncomputable def apDivisorSigmaPS (R : Type*) [CommRing R]
    (r m : ℕ) : R⟦X⟧ :=
  PowerSeries.mk fun n =>
    ∑ k ∈ Finset.range (n + 1),
      if r + m * k ∣ n ∧ 0 < n then ((r + m * k : ℕ) : R) else 0

@[simp] theorem coeff_apDivisorSigmaFinitePS (R : Type*) [CommRing R]
    (r m N n : ℕ) :
    (apDivisorSigmaFinitePS R r m N).coeff n =
      ∑ k ∈ Finset.range N,
        if r + m * k ∣ n ∧ 0 < n then ((r + m * k : ℕ) : R) else 0 := by
  simp [apDivisorSigmaFinitePS]

@[simp] theorem coeff_apDivisorSigmaPS (R : Type*) [CommRing R]
    (r m n : ℕ) :
    (apDivisorSigmaPS R r m).coeff n =
      ∑ k ∈ Finset.range (n + 1),
        if r + m * k ∣ n ∧ 0 < n then ((r + m * k : ℕ) : R) else 0 := by
  simp [apDivisorSigmaPS]

theorem qPochAPFinitePS_succ (R : Type*) [CommRing R] (r m N : ℕ) :
    qPochAPFinitePS R r m (N + 1) =
      qPochAPFinitePS R r m N * apFactorPS R r m N := by
  simp [qPochAPFinitePS, Finset.prod_range_succ]

theorem apDivisorSigmaFinitePS_succ (R : Type*) [CommRing R] (r m N : ℕ) :
    apDivisorSigmaFinitePS R r m (N + 1) =
      apDivisorSigmaFinitePS R r m N +
        PowerSeries.C (((r + m * N : ℕ) : R)) *
          divisorGeomPSLocal R (r + m * N) := by
  ext n
  rw [map_add, PowerSeries.coeff_C_mul, coeff_apDivisorSigmaFinitePS,
    coeff_apDivisorSigmaFinitePS,
    coeff_divisorGeomPSLocal]
  rw [Finset.sum_range_succ]
  by_cases h : r + m * N ∣ n ∧ 0 < n <;> simp [h]

theorem thetaOp_qPochAPFinitePS (R : Type*) [CommRing R]
    {r m : ℕ} (hr : 0 < r) (N : ℕ) :
    thetaOp (qPochAPFinitePS R r m N) =
      -qPochAPFinitePS R r m N * apDivisorSigmaFinitePS R r m N := by
  induction N with
  | zero =>
      have hzero : apDivisorSigmaFinitePS R r m 0 = 0 := by
        ext n
        simp [apDivisorSigmaFinitePS]
      simp [qPochAPFinitePS, hzero]
  | succ N ih =>
      rw [qPochAPFinitePS_succ, apDivisorSigmaFinitePS_succ]
      rw [thetaOp_mul, apFactorPS, thetaOp_one_sub_X_pow_local, ih]
      have hdpos : 0 < r + m * N := by omega
      have hgeom :=
        one_sub_X_pow_mul_divisorGeomPSLocal R (d := r + m * N) hdpos
      calc
        (qPochAPFinitePS R r m N *
              (-C ↑(r + m * N) * X ^ (r + m * N)) +
            apFactorPS R r m N *
              (-qPochAPFinitePS R r m N * apDivisorSigmaFinitePS R r m N))
            =
          -qPochAPFinitePS R r m N * apDivisorSigmaFinitePS R r m N *
              apFactorPS R r m N -
            qPochAPFinitePS R r m N * (C ↑(r + m * N) * X ^ (r + m * N)) := by
            ring
        _ =
          -qPochAPFinitePS R r m N * apDivisorSigmaFinitePS R r m N *
              apFactorPS R r m N -
            qPochAPFinitePS R r m N *
              (C ↑(r + m * N) *
                (apFactorPS R r m N *
                  divisorGeomPSLocal R (r + m * N))) := by
            rw [apFactorPS, hgeom]
        _ =
          -(qPochAPFinitePS R r m N * apFactorPS R r m N) *
            (apDivisorSigmaFinitePS R r m N +
              C ↑(r + m * N) *
                divisorGeomPSLocal R (r + m * N)) := by
            ring

theorem qPochAPFinitePS_coeff_stable_five
    (R : Type*) [CommRing R] (r k N : ℕ) (hk : k < r + 5 * N) :
    (qPochAPFinitePS R r 5 (N + 1)).coeff k =
      (qPochAPFinitePS R r 5 N).coeff k := by
  rw [qPochAPFinitePS_succ]
  exact coeff_mul_apFactorPS_eq_of_lt R (qPochAPFinitePS R r 5 N) k r 5 N hk

theorem qPochAPFinitePS_coeff_eq_of_le_five
    (R : Type*) [CommRing R] {r k N M : ℕ}
    (hk : k < r + 5 * N) (hNM : N ≤ M) :
    (qPochAPFinitePS R r 5 M).coeff k =
      (qPochAPFinitePS R r 5 N).coeff k := by
  induction M, hNM using Nat.le_induction with
  | base => rfl
  | succ M hNM ih =>
      rw [qPochAPFinitePS_coeff_stable_five R r k M (by omega), ih]

theorem coeff_qPochAPPS_eq_qPochAPFinitePS_five_rat
    (r k : ℕ) (hr : 0 < r) :
    (qPochAPPS ℚ r 5).coeff k =
      (qPochAPFinitePS ℚ r 5 (k + 1)).coeff k := by
  have h_tendsto : Tendsto
      (fun N : ℕ => qPochAPFinitePS ℚ r 5 N) atTop
      (𝓝 (qPochAPPS ℚ r 5)) := by
    simpa [qPochAPFinitePS] using tendsto_qPochAPPS_partial ℚ r 5 (by norm_num)
  have h_coeff_tendsto : Tendsto
      (fun N : ℕ => (qPochAPFinitePS ℚ r 5 N).coeff k) atTop
      (𝓝 ((qPochAPPS ℚ r 5).coeff k)) :=
    ((PowerSeries.WithPiTopology.continuous_coeff ℚ k).tendsto _).comp h_tendsto
  have h_const_tendsto : Tendsto
      (fun N : ℕ => (qPochAPFinitePS ℚ r 5 N).coeff k) atTop
      (𝓝 ((qPochAPFinitePS ℚ r 5 (k + 1)).coeff k)) := by
    apply Filter.Tendsto.congr' _ tendsto_const_nhds
    rw [Filter.EventuallyEq, Filter.eventually_atTop]
    refine ⟨k + 1, fun N hN => ?_⟩
    exact (qPochAPFinitePS_coeff_eq_of_le_five ℚ
      (r := r) (k := k) (N := k + 1) (M := N) (by omega) hN).symm
  exact tendsto_nhds_unique h_coeff_tendsto h_const_tendsto

theorem coeff_apDivisorSigmaFinitePS_eq_apDivisorSigmaPS_five
    (R : Type*) [CommRing R] (r n N : ℕ) (hr : 0 < r) (hN : n + 1 ≤ N) :
    (apDivisorSigmaFinitePS R r 5 N).coeff n =
      (apDivisorSigmaPS R r 5).coeff n := by
  rw [coeff_apDivisorSigmaFinitePS, coeff_apDivisorSigmaPS]
  rw [← Finset.sum_range_add_sum_Ico
    (fun k => if r + 5 * k ∣ n ∧ 0 < n then ((r + 5 * k : ℕ) : R) else 0) hN]
  have htail : (∑ k ∈ Finset.Ico (n + 1) N,
      (if r + 5 * k ∣ n ∧ 0 < n then ((r + 5 * k : ℕ) : R) else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hgt : n < r + 5 * k := by nlinarith [hr, hk.1]
    have hnot : ¬ (r + 5 * k ∣ n ∧ 0 < n) := by
      intro h
      exact Nat.not_lt_of_ge (Nat.le_of_dvd h.2 h.1) hgt
    simp [hnot]
  rw [htail, add_zero]

theorem thetaOp_qPochAPPS_five_rat (r : ℕ) (hr : 0 < r) :
    thetaOp (qPochAPPS ℚ r 5) =
      -qPochAPPS ℚ r 5 * apDivisorSigmaPS ℚ r 5 := by
  ext n
  let N := n + 1
  have hcoeff_q := coeff_qPochAPPS_eq_qPochAPFinitePS_five_rat r n hr
  have htheta :
      (thetaOp (qPochAPPS ℚ r 5)).coeff n =
        (thetaOp (qPochAPFinitePS ℚ r 5 N)).coeff n := by
    rw [coeff_thetaOp, coeff_thetaOp, hcoeff_q]
  have hfin := congrArg (fun f : ℚ⟦X⟧ => f.coeff n)
    (thetaOp_qPochAPFinitePS ℚ (r := r) (m := 5) hr N)
  have hfin' :
      (thetaOp (qPochAPFinitePS ℚ r 5 N)).coeff n =
        (-qPochAPFinitePS ℚ r 5 N *
          apDivisorSigmaFinitePS ℚ r 5 N).coeff n := by
    simpa using hfin
  rw [htheta, hfin']
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [map_neg, map_neg]
  have hp_sum : p.1 + p.2 = n := Finset.mem_antidiagonal.mp hp
  have hp1 : p.1 ≤ n := by omega
  have hp2N : p.2 + 1 ≤ N := by omega
  have hp1N : p.1 + 1 ≤ N := by omega
  have hq_stable :
      (qPochAPFinitePS ℚ r 5 N).coeff p.1 =
        (qPochAPFinitePS ℚ r 5 (p.1 + 1)).coeff p.1 :=
    qPochAPFinitePS_coeff_eq_of_le_five ℚ (r := r) (k := p.1)
      (N := p.1 + 1) (M := N) (by omega) hp1N
  rw [hq_stable]
  rw [← coeff_qPochAPPS_eq_qPochAPFinitePS_five_rat r p.1 hr]
  rw [coeff_apDivisorSigmaFinitePS_eq_apDivisorSigmaPS_five ℚ r p.2 N hr hp2N]

theorem thetaOp_rrProductA_rat :
    thetaOp (rrProductA ℚ) =
      -rrProductA ℚ *
        (apDivisorSigmaPS ℚ 1 5 + apDivisorSigmaPS ℚ 4 5) := by
  unfold rrProductA
  rw [thetaOp_mul, thetaOp_qPochAPPS_five_rat 1 (by norm_num),
    thetaOp_qPochAPPS_five_rat 4 (by norm_num)]
  ring

theorem thetaOp_rrProductB_rat :
    thetaOp (rrProductB ℚ) =
      -rrProductB ℚ *
        (apDivisorSigmaPS ℚ 2 5 + apDivisorSigmaPS ℚ 3 5) := by
  unfold rrProductB
  rw [thetaOp_mul, thetaOp_qPochAPPS_five_rat 2 (by norm_num),
    thetaOp_qPochAPPS_five_rat 3 (by norm_num)]
  ring

private noncomputable def residueDivisorSigmaCoeff (r n : ℕ) : ℚ :=
  ∑ d ∈ Finset.range (n + 1),
    if d ∣ n ∧ 0 < n ∧ d % 5 = r then (d : ℚ) else 0

private theorem apDivisorSigmaPS_coeff_eq_residue_range_rat
    {r n : ℕ} (_hr0 : 0 < r) (hr5 : r < 5) :
    (apDivisorSigmaPS ℚ r 5).coeff n =
      residueDivisorSigmaCoeff r n := by
  unfold residueDivisorSigmaCoeff
  rw [coeff_apDivisorSigmaPS]
  refine Finset.sum_bij_ne_zero
    (s := Finset.range (n + 1)) (t := Finset.range (n + 1))
    (f := fun k =>
      if r + 5 * k ∣ n ∧ 0 < n then ((r + 5 * k : ℕ) : ℚ) else 0)
    (g := fun d =>
      if d ∣ n ∧ 0 < n ∧ d % 5 = r then (d : ℚ) else 0)
    (fun k _ _ => r + 5 * k) ?_ ?_ ?_ ?_
  · intro k _hk hfk
    by_cases hcond : r + 5 * k ∣ n ∧ 0 < n
    · exact Finset.mem_range.mpr
        (Nat.lt_succ_of_le (Nat.le_of_dvd hcond.2 hcond.1))
    · exact False.elim (hfk (by simp [hcond]))
  · intro k₁ _hk₁ _hfk₁ k₂ _hk₂ _hfk₂ h
    have h' : 5 * k₁ = 5 * k₂ := Nat.add_left_cancel h
    exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 5) h'
  · intro d hd hgd
    by_cases hcond : d ∣ n ∧ 0 < n ∧ d % 5 = r
    · refine ⟨d / 5, ?_, ?_, ?_⟩
      · exact Finset.mem_range.mpr
          (lt_of_le_of_lt (Nat.div_le_self d 5) (Finset.mem_range.mp hd))
      · have hd_eq : r + 5 * (d / 5) = d := by
          have h := Nat.mod_add_div d 5
          rw [hcond.2.2] at h
          omega
        have hdne : d ≠ 0 := Nat.ne_of_gt (Nat.pos_of_dvd_of_pos hcond.1 hcond.2.1)
        simp [hd_eq, hcond.1, hcond.2.1, hdne]
      · have h := Nat.mod_add_div d 5
        rw [hcond.2.2] at h
        omega
    · exact False.elim (hgd (by simp [hcond]))
  · intro k _hk hfk
    by_cases hcond : r + 5 * k ∣ n ∧ 0 < n
    · have hmod : (r + 5 * k) % 5 = r := by
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr5]
      simp [hcond, hmod]
    · exact False.elim (hfk (by simp [hcond]))

private theorem chan15_divisor_sum_eq_range_rat (n : ℕ) (hn : 0 < n) :
    (((∑ d ∈ n.divisors, (d : ℤ) * legendre5 d) : ℤ) : ℚ) =
      ∑ d ∈ Finset.range (n + 1),
        if d ∣ n ∧ 0 < d then (d : ℚ) * ((legendre5 d : ℤ) : ℚ) else 0 := by
  let f : ℕ → ℚ := fun d =>
    if d ∣ n ∧ 0 < d then (d : ℚ) * ((legendre5 d : ℤ) : ℚ) else 0
  have hcast :
      (((∑ d ∈ n.divisors, (d : ℤ) * legendre5 d) : ℤ) : ℚ) =
        ∑ d ∈ n.divisors, (d : ℚ) * ((legendre5 d : ℤ) : ℚ) := by
    rw [Int.cast_sum]
    apply Finset.sum_congr rfl
    intro d _hd
    norm_num
  have hdiv_to_f :
      (∑ d ∈ n.divisors, (d : ℚ) * ((legendre5 d : ℤ) : ℚ)) =
        ∑ d ∈ n.divisors, f d := by
    apply Finset.sum_congr rfl
    intro d hd
    have hmem := (Nat.mem_divisors.mp hd)
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
    simp [f, hmem.1, hdpos]
  have hsubset : n.divisors ⊆ Finset.range (n + 1) := by
    intro d hd
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.divisor_le hd))
  have hsum :
      (∑ d ∈ n.divisors, f d) =
        ∑ d ∈ Finset.range (n + 1), f d := by
    refine Finset.sum_subset hsubset ?_
    intro d _hdr hnot
    have hnotcond : ¬ (d ∣ n ∧ 0 < d) := by
      intro hcond
      exact hnot (Nat.mem_divisors.mpr ⟨hcond.1, Nat.ne_of_gt hn⟩)
    simp [f, hnotcond]
  calc
    (((∑ d ∈ n.divisors, (d : ℤ) * legendre5 d) : ℤ) : ℚ)
        = ∑ d ∈ n.divisors, (d : ℚ) * ((legendre5 d : ℤ) : ℚ) := hcast
    _ = ∑ d ∈ n.divisors, f d := hdiv_to_f
    _ = ∑ d ∈ Finset.range (n + 1), f d := hsum

private theorem chan15_range_legendre_eq_residue_coeffs (n : ℕ) (hn : 0 < n) :
    (∑ d ∈ Finset.range (n + 1),
        if d ∣ n ∧ 0 < d then (d : ℚ) * ((legendre5 d : ℤ) : ℚ) else 0) =
      residueDivisorSigmaCoeff 1 n - residueDivisorSigmaCoeff 2 n -
        residueDivisorSigmaCoeff 3 n + residueDivisorSigmaCoeff 4 n := by
  unfold residueDivisorSigmaCoeff
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _hd
  by_cases hdivpos : d ∣ n ∧ 0 < d
  · have hdmodlt : d % 5 < 5 := Nat.mod_lt d (by norm_num)
    interval_cases hmod : d % 5 <;>
      simp [hdivpos, hn, hmod, legendre5]
  · have hnot1 : ¬ (d ∣ n ∧ 0 < n ∧ d % 5 = 1) := by
      intro h
      exact hdivpos ⟨h.1, Nat.pos_of_dvd_of_pos h.1 h.2.1⟩
    have hnot2 : ¬ (d ∣ n ∧ 0 < n ∧ d % 5 = 2) := by
      intro h
      exact hdivpos ⟨h.1, Nat.pos_of_dvd_of_pos h.1 h.2.1⟩
    have hnot3 : ¬ (d ∣ n ∧ 0 < n ∧ d % 5 = 3) := by
      intro h
      exact hdivpos ⟨h.1, Nat.pos_of_dvd_of_pos h.1 h.2.1⟩
    have hnot4 : ¬ (d ∣ n ∧ 0 < n ∧ d % 5 = 4) := by
      intro h
      exact hdivpos ⟨h.1, Nat.pos_of_dvd_of_pos h.1 h.2.1⟩
    simp [hdivpos, hnot1, hnot2, hnot3, hnot4]

theorem chan15LHSPS_eq_one_plus_apSigmas_rat :
    chan15LHSPS ℚ =
      1 + 5 * ((apDivisorSigmaPS ℚ 2 5 + apDivisorSigmaPS ℚ 3 5) -
        (apDivisorSigmaPS ℚ 1 5 + apDivisorSigmaPS ℚ 4 5)) := by
  ext n
  by_cases hn0 : n = 0
  · subst n
    simp [apDivisorSigmaPS, chan15LHSPS, chan15LHSCoeff, chan15LHSCoeffInt]
  · have hn : 0 < n := Nat.pos_of_ne_zero hn0
    have hs1 := apDivisorSigmaPS_coeff_eq_residue_range_rat
      (r := 1) (n := n) (by norm_num) (by norm_num)
    have hs2 := apDivisorSigmaPS_coeff_eq_residue_range_rat
      (r := 2) (n := n) (by norm_num) (by norm_num)
    have hs3 := apDivisorSigmaPS_coeff_eq_residue_range_rat
      (r := 3) (n := n) (by norm_num) (by norm_num)
    have hs4 := apDivisorSigmaPS_coeff_eq_residue_range_rat
      (r := 4) (n := n) (by norm_num) (by norm_num)
    have hsum :
        (((∑ d ∈ n.divisors, (d : ℤ) * legendre5 d) : ℤ) : ℚ) =
          residueDivisorSigmaCoeff 1 n - residueDivisorSigmaCoeff 2 n -
            residueDivisorSigmaCoeff 3 n + residueDivisorSigmaCoeff 4 n := by
      rw [chan15_divisor_sum_eq_range_rat n hn,
        chan15_range_legendre_eq_residue_coeffs n hn]
    have hleft :
        (chan15LHSPS ℚ).coeff n =
          -5 * (residueDivisorSigmaCoeff 1 n - residueDivisorSigmaCoeff 2 n -
            residueDivisorSigmaCoeff 3 n + residueDivisorSigmaCoeff 4 n) := by
      rw [coeff_chan15LHSPS, chan15LHSCoeff, chan15LHSCoeffInt, if_neg hn0]
      rw [Int.cast_mul, hsum]
      norm_num
    have hright :
        (1 + 5 * ((apDivisorSigmaPS ℚ 2 5 + apDivisorSigmaPS ℚ 3 5) -
            (apDivisorSigmaPS ℚ 1 5 + apDivisorSigmaPS ℚ 4 5))).coeff n =
          5 * ((residueDivisorSigmaCoeff 2 n + residueDivisorSigmaCoeff 3 n) -
            (residueDivisorSigmaCoeff 1 n + residueDivisorSigmaCoeff 4 n)) := by
      change
        (1 + PowerSeries.C (5 : ℚ) *
          ((apDivisorSigmaPS ℚ 2 5 + apDivisorSigmaPS ℚ 3 5) -
            (apDivisorSigmaPS ℚ 1 5 + apDivisorSigmaPS ℚ 4 5))).coeff n =
          5 * ((residueDivisorSigmaCoeff 2 n + residueDivisorSigmaCoeff 3 n) -
            (residueDivisorSigmaCoeff 1 n + residueDivisorSigmaCoeff 4 n))
      rw [map_add, PowerSeries.coeff_one, if_neg hn0, PowerSeries.coeff_C_mul]
      rw [map_sub, map_add, map_add, hs1, hs2, hs3, hs4]
      ring
    rw [hleft, hright]
    ring

theorem rr_wronskian_lhs_eq_chan15LHSPS_mul_rrProducts :
    rrProductA ℚ * rrProductB ℚ +
      5 * (rrProductB ℚ * thetaOp (rrProductA ℚ) -
           rrProductA ℚ * thetaOp (rrProductB ℚ)) =
    chan15LHSPS ℚ * rrProductA ℚ * rrProductB ℚ := by
  rw [chan15LHSPS_eq_one_plus_apSigmas_rat,
    thetaOp_rrProductA_rat, thetaOp_rrProductB_rat]
  ring

theorem rogers_ramanujan_wronskian_cleared_from_chan :
    rrProductA ℚ * rrProductB ℚ +
      5 * (rrProductB ℚ * thetaOp (rrProductA ℚ) -
           rrProductA ℚ * thetaOp (rrProductB ℚ)) =
    (qPochInfPS ℚ) ^ 4 * (rrProductA ℚ) ^ 2 * (rrProductB ℚ) ^ 2 := by
  let C : ℚ⟦X⟧ := qPochAPPS ℚ 5 5
  let W : ℚ⟦X⟧ :=
    rrProductA ℚ * rrProductB ℚ +
      5 * (rrProductB ℚ * thetaOp (rrProductA ℚ) -
           rrProductA ℚ * thetaOp (rrProductB ℚ))
  let RHS : ℚ⟦X⟧ := (qPochInfPS ℚ) ^ 4 * (rrProductA ℚ) ^ 2 * (rrProductB ℚ) ^ 2
  have hchanC : chan15LHSPS ℚ * C = (qPochInfPS ℚ) ^ 5 := by
    calc
      chan15LHSPS ℚ * C =
          chan15LHSPS ℚ *
            PowerSeries.expand 5 (by decide : (5 : ℕ) ≠ 0) (qPochInfPS ℚ) := by
            simp only [C, expand_five_qPochInfPS_eq_qPochAPPS55_rat]
      _ = (qPochInfPS ℚ) ^ 5 := chan_theorem_11_7 ℚ
  have hmul_chan :
      C * (chan15LHSPS ℚ * rrProductA ℚ * rrProductB ℚ) = C * RHS := by
    calc
      C * (chan15LHSPS ℚ * rrProductA ℚ * rrProductB ℚ)
          = (chan15LHSPS ℚ * C) * rrProductA ℚ * rrProductB ℚ := by ring
      _ = (qPochInfPS ℚ) ^ 5 * rrProductA ℚ * rrProductB ℚ := by rw [hchanC]
      _ = C * RHS := by
            simp only [C, RHS]
            rw [qPochInfPS_eq_rrProducts_rat]
            ring
  have hmul : C * W = C * RHS := by
    simp only [W]
    rw [rr_wronskian_lhs_eq_chan15LHSPS_mul_rrProducts]
    exact hmul_chan
  have hunit : IsUnit C := by
    simpa [C] using isUnit_qPochAPPS55_rat
  have hW : W = RHS := hunit.mul_right_inj.mp hmul
  simpa [W, RHS] using hW

/-! ## Coefficientwise Wronskian reduction to Jacobi cube -/

/-- Raw Cauchy-product coefficient of
`P14*P23 + 5*(P23*theta(P14) - P14*theta(P23))`. -/
def pentagonalWronskianCoeff (N : ℕ) : ℚ :=
  (∑ ij ∈ Finset.antidiagonal N,
    pentagonal014Coeff ℚ ij.1 * pentagonal023Coeff ℚ ij.2) +
  5 *
    ((∑ ij ∈ Finset.antidiagonal N,
        pentagonal023Coeff ℚ ij.1 * pentagonal014Coeff ℚ ij.2 * (ij.2 : ℚ)) -
      (∑ ij ∈ Finset.antidiagonal N,
        pentagonal014Coeff ℚ ij.1 * pentagonal023Coeff ℚ ij.2 * (ij.2 : ℚ)))

/-- Cauchy-product coefficient of `(jacobiThetaPS ℚ)^2`. -/
def jacobiThetaSquareCoeff (N : ℕ) : ℚ :=
  ∑ ij ∈ Finset.antidiagonal N,
    ((jacobiTripleSign ij.1 : ℤ) : ℚ) * ((jacobiTripleSign ij.2 : ℤ) : ℚ)

theorem coeff_pentagonal_wronskian_lhs (N : ℕ) :
    (pentagonal014SeriesPS ℚ * pentagonal023SeriesPS ℚ +
      5 * (pentagonal023SeriesPS ℚ * thetaOp (pentagonal014SeriesPS ℚ) -
           pentagonal014SeriesPS ℚ * thetaOp (pentagonal023SeriesPS ℚ))).coeff N =
      pentagonalWronskianCoeff N := by
  change
    (pentagonal014SeriesPS ℚ * pentagonal023SeriesPS ℚ +
      PowerSeries.C (5 : ℚ) *
        (pentagonal023SeriesPS ℚ * thetaOp (pentagonal014SeriesPS ℚ) -
          pentagonal014SeriesPS ℚ * thetaOp (pentagonal023SeriesPS ℚ))).coeff N =
      pentagonalWronskianCoeff N
  rw [map_add, PowerSeries.coeff_C_mul]
  simp [pentagonalWronskianCoeff, PowerSeries.coeff_mul, coeff_thetaOp]
  ring_nf

theorem coeff_jacobiThetaPS_sq (N : ℕ) :
    ((jacobiThetaPS ℚ)^2).coeff N = jacobiThetaSquareCoeff N := by
  simp [jacobiThetaSquareCoeff, pow_two, PowerSeries.coeff_mul]

theorem wronskian_at_pentagonal_level_of_coeff_identity
    (hcoeff : ∀ N : ℕ, pentagonalWronskianCoeff N = jacobiThetaSquareCoeff N) :
    pentagonal014SeriesPS ℚ * pentagonal023SeriesPS ℚ +
      5 * (pentagonal023SeriesPS ℚ * thetaOp (pentagonal014SeriesPS ℚ) -
           pentagonal014SeriesPS ℚ * thetaOp (pentagonal023SeriesPS ℚ)) =
    (qPochInfPS ℚ) ^ 6 := by
  rw [qPochInfPS_pow_six_eq_jacobiThetaPS_pow_two]
  ext N
  rw [coeff_pentagonal_wronskian_lhs, coeff_jacobiThetaPS_sq, hcoeff N]

set_option maxHeartbeats 800000 in
set_option maxRecDepth 8192 in
/-- The coefficient identity checked by native computation through degree `50`. -/
theorem pentagonalWronskianCoeff_eq_jacobiThetaSquareCoeff_le_fifty :
    ∀ N : ℕ, N ≤ 50 → pentagonalWronskianCoeff N = jacobiThetaSquareCoeff N := by
  native_decide

/-! ## Primary pentagonal-level Wronskian target -/

/-- **Pentagonal-level Wronskian (primary target, over ℚ).**

This is the cleaner form using the Jacobi triple product specialisations
`P₁₄ = pentagonal014SeriesPS` and `P₂₃ = pentagonal023SeriesPS`, both of which
include the `(q^5;q^5)_∞` factor:

  `P₁₄ · P₂₃ + 5 · (P₂₃ · θ(P₁₄) − P₁₄ · θ(P₂₃)) = E⁶`

The coefficientwise bridge above reduces this theorem to
`∀ N, pentagonalWronskianCoeff N = jacobiThetaSquareCoeff N`. -/
theorem wronskian_at_pentagonal_level :
    pentagonal014SeriesPS ℚ * pentagonal023SeriesPS ℚ +
      5 * (pentagonal023SeriesPS ℚ * thetaOp (pentagonal014SeriesPS ℚ) -
           pentagonal014SeriesPS ℚ * thetaOp (pentagonal023SeriesPS ℚ)) =
    (qPochInfPS ℚ) ^ 6 := by
  let C : ℚ⟦X⟧ := qPochAPPS ℚ 5 5
  let W : ℚ⟦X⟧ :=
    rrProductA ℚ * rrProductB ℚ +
      5 * (rrProductB ℚ * thetaOp (rrProductA ℚ) -
           rrProductA ℚ * thetaOp (rrProductB ℚ))
  calc
    pentagonal014SeriesPS ℚ * pentagonal023SeriesPS ℚ +
        5 * (pentagonal023SeriesPS ℚ * thetaOp (pentagonal014SeriesPS ℚ) -
             pentagonal014SeriesPS ℚ * thetaOp (pentagonal023SeriesPS ℚ))
        = C ^ 2 * W := by
          rw [pentagonal014SeriesPS_eq_rrProductA_mul_qPochAPPS55_rat,
            pentagonal023SeriesPS_eq_rrProductB_mul_qPochAPPS55_rat]
          simp only [C, W]
          rw [thetaOp_mul, thetaOp_mul]
          ring
    _ = C ^ 2 *
          ((qPochInfPS ℚ) ^ 4 * (rrProductA ℚ) ^ 2 * (rrProductB ℚ) ^ 2) := by
          simp only [W]
          rw [rogers_ramanujan_wronskian_cleared_from_chan]
    _ = (qPochInfPS ℚ) ^ 6 := by
          simp only [C]
          rw [qPochInfPS_eq_rrProducts_rat]
          ring

/-- The pentagonal-level Wronskian implies the E5-free Rogers-Ramanujan
Wronskian by cancelling the unit `(q^5;q^5)_∞^2`. -/
theorem rogers_ramanujan_wronskian_cleared_of_pentagonal_level
    (hpent :
      pentagonal014SeriesPS ℚ * pentagonal023SeriesPS ℚ +
        5 * (pentagonal023SeriesPS ℚ * thetaOp (pentagonal014SeriesPS ℚ) -
             pentagonal014SeriesPS ℚ * thetaOp (pentagonal023SeriesPS ℚ)) =
      (qPochInfPS ℚ) ^ 6) :
    rrProductA ℚ * rrProductB ℚ +
      5 * (rrProductB ℚ * thetaOp (rrProductA ℚ) -
           rrProductA ℚ * thetaOp (rrProductB ℚ)) =
    (qPochInfPS ℚ) ^ 4 * (rrProductA ℚ) ^ 2 * (rrProductB ℚ) ^ 2 := by
  let C : ℚ⟦X⟧ := qPochAPPS ℚ 5 5
  let W : ℚ⟦X⟧ :=
    rrProductA ℚ * rrProductB ℚ +
      5 * (rrProductB ℚ * thetaOp (rrProductA ℚ) -
           rrProductA ℚ * thetaOp (rrProductB ℚ))
  let RHS : ℚ⟦X⟧ := (qPochInfPS ℚ) ^ 4 * (rrProductA ℚ) ^ 2 * (rrProductB ℚ) ^ 2
  have hpent' : C ^ 2 * W = (qPochInfPS ℚ) ^ 6 := by
    rw [← hpent]
    rw [pentagonal014SeriesPS_eq_rrProductA_mul_qPochAPPS55_rat,
      pentagonal023SeriesPS_eq_rrProductB_mul_qPochAPPS55_rat]
    simp only [C, W]
    rw [thetaOp_mul, thetaOp_mul]
    ring
  have hRHS : C ^ 2 * RHS = (qPochInfPS ℚ) ^ 6 := by
    simp only [C, RHS]
    rw [qPochInfPS_eq_rrProducts_rat]
    ring
  have hcancel : C ^ 2 * W = C ^ 2 * RHS := by
    rw [hpent', hRHS]
  have hunit : IsUnit (C ^ 2) := by
    exact (show IsUnit C by simpa [C] using isUnit_qPochAPPS55_rat).pow 2
  have hW : W = RHS := hunit.mul_right_inj.mp hcancel
  simpa [W, RHS] using hW

/-! ## The Wronskian identity -/

/-- **Rogers–Ramanujan Wronskian (denominator-cleared, over ℚ).**

  `A · B + 5 · (B · θA − A · θB) = E⁴ · A² · B²`

Numerically verified (Python, degree 30). This is the k=2 case of the
Milas–Mortenson–Ono Wronskian theorem for Andrews–Gordon characters.

Equivalent statements:
- Ramanujan's derivative formula: `θ log R(q) = (1/5) · E⁵/E₅`
- `5·(G·θH − H·θG) + G·H = E⁴` where `G = 1/A`, `H = 1/B`

The proof requires the Rogers–Ramanujan Wronskian as genuine mathematical
content — it is NOT a consequence of the product decomposition alone. -/
theorem rogers_ramanujan_wronskian_cleared :
    rrProductA ℚ * rrProductB ℚ +
      5 * (rrProductB ℚ * thetaOp (rrProductA ℚ) -
           rrProductA ℚ * thetaOp (rrProductB ℚ)) =
    (qPochInfPS ℚ) ^ 4 * (rrProductA ℚ) ^ 2 * (rrProductB ℚ) ^ 2 := by
  exact rogers_ramanujan_wronskian_cleared_of_pentagonal_level
    wronskian_at_pentagonal_level

/-! ## Bridge: Wronskian ⟹ chan15LHSPS · E₅ = E⁵ -/

/-- **Step 1**: `chan15LHSPS ℚ = E⁴ · A · B` (dividing Wronskian by A·B).

Proof sketch: From `A·B + 5·(B·θA − A·θB) = E⁴·A²·B²`, dividing by `A·B`:
  `1 + 5·θlog(A/B) = E⁴·A·B`
And `chan15LHSPS = 1 − 5·∑χ₅(d)·d·Xᵈ/(1−Xᵈ) = 1 + 5·θlog(A/B)`.

The Lambert-to-theta-log bridge is the arithmetic content that relates the
Legendre-symbol divisor sum to the logarithmic derivative of A/B.
Numerically verified (Python, degree 30). -/
theorem chan15LHSPS_eq_qPochInfPS_pow4_mul_rrProducts
    (_hwron : rrProductA ℚ * rrProductB ℚ +
      5 * (rrProductB ℚ * thetaOp (rrProductA ℚ) -
           rrProductA ℚ * thetaOp (rrProductB ℚ)) =
      (qPochInfPS ℚ) ^ 4 * (rrProductA ℚ) ^ 2 * (rrProductB ℚ) ^ 2) :
    chan15LHSPS ℚ =
      (qPochInfPS ℚ) ^ 4 * rrProductA ℚ * rrProductB ℚ := by
  have hmul :
      chan15LHSPS ℚ * qPochAPPS ℚ 5 5 =
        ((qPochInfPS ℚ) ^ 4 * rrProductA ℚ * rrProductB ℚ) *
          qPochAPPS ℚ 5 5 := by
    calc
      chan15LHSPS ℚ * qPochAPPS ℚ 5 5 =
          chan15LHSPS ℚ *
            PowerSeries.expand 5 (by decide : (5 : ℕ) ≠ 0) (qPochInfPS ℚ) := by
            rw [expand_five_qPochInfPS_eq_qPochAPPS55_rat]
      _ = (qPochInfPS ℚ) ^ 5 := by
            exact chan_theorem_11_7 ℚ
      _ = ((qPochInfPS ℚ) ^ 4 * rrProductA ℚ * rrProductB ℚ) *
          qPochAPPS ℚ 5 5 := by
            rw [qPochInfPS_eq_rrProducts_rat]
            ring
  have hmul' :
      qPochAPPS ℚ 5 5 * chan15LHSPS ℚ =
        qPochAPPS ℚ 5 5 *
          ((qPochInfPS ℚ) ^ 4 * rrProductA ℚ * rrProductB ℚ) := by
    calc
      qPochAPPS ℚ 5 5 * chan15LHSPS ℚ =
          chan15LHSPS ℚ * qPochAPPS ℚ 5 5 := by ring
      _ = ((qPochInfPS ℚ) ^ 4 * rrProductA ℚ * rrProductB ℚ) *
          qPochAPPS ℚ 5 5 := hmul
      _ = qPochAPPS ℚ 5 5 *
          ((qPochInfPS ℚ) ^ 4 * rrProductA ℚ * rrProductB ℚ) := by ring
  exact isUnit_qPochAPPS55_rat.mul_right_inj.mp hmul'

/-- **Step 2**: `chan15LHSPS · E₅ = E⁵` from `chan15 = E⁴·A·B` and `E = A·B·E₅`.

Proof: `chan15·E₅ = E⁴·A·B·E₅ = E⁴·E = E⁵`. -/
theorem chan_theorem_11_7_rat_of_wronskian_and_factorization
    (hchan15 : chan15LHSPS ℚ =
      (qPochInfPS ℚ) ^ 4 * rrProductA ℚ * rrProductB ℚ)
    (hE : qPochInfPS ℚ =
      rrProductA ℚ * rrProductB ℚ * qPochAPPS ℚ 5 5)
    (hE5 : PowerSeries.expand 5 (by decide : (5 : ℕ) ≠ 0) (qPochInfPS ℚ) =
      qPochAPPS ℚ 5 5) :
    chan15LHSPS ℚ *
        PowerSeries.expand 5 (by decide) (qPochInfPS ℚ) =
      (qPochInfPS ℚ) ^ 5 := by
  rw [hchan15, hE5]
  rw [show (qPochInfPS ℚ) ^ 5 = (qPochInfPS ℚ) ^ 4 * qPochInfPS ℚ by ring]
  rw [hE]
  ring

/-! ## Remaining primary target

The file now takes `wronskian_at_pentagonal_level` as the primary Wronskian
target.  The E5-free statement `rogers_ramanujan_wronskian_cleared` is derived
from it by `rogers_ramanujan_wronskian_cleared_of_pentagonal_level`, using the
factorisations `P₁₄ = A·E₅`, `P₂₃ = B·E₅`, Leibniz for `thetaOp`, and unit
cancellation of `E₅²`.

The coefficientwise section reduces the primary target to the finite
double-sum identity
`∀ N, pentagonalWronskianCoeff N = jacobiThetaSquareCoeff N`, with native
verification currently recorded through degree `50`. -/

end Ch15WronskianBridge
end Pending
end QseriesFormalization
