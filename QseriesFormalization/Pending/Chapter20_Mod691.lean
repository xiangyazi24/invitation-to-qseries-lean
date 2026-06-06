import QseriesFormalization.Chapter20

/-!
# Chapter 20 — mod-691 finite verification through the first obstruction

This file keeps the large decidable computation out of `Chapter20.lean`.
It mirrors the `tauEtaPowVec` convolution engine from Chapter 20, but performs
the convolution directly in `ZMod 691` so the finite verification remains small.
-/

namespace QseriesFormalization
namespace Pending
namespace Ch20Mod691

open QseriesFormalization.PartIV.Ch20
open PowerSeries
open scoped PowerSeries

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- Eta coefficient reduced modulo 691, using the Chapter 20 coefficient source
`tauEtaCoeffZ`. -/
def tauEtaCoeffMod691 (n : Nat) : ZMod 691 :=
  (tauEtaCoeffZ n : ZMod 691)

/-- One truncated convolution step for powers of `(q;q)_∞`, computed in
`ZMod 691`.  This is the mod-691 analogue of `tauEtaPowStep`. -/
def tauEtaPowStepMod691 (N : Nat) (v : Vector (ZMod 691) (N + 1)) :
    Vector (ZMod 691) (N + 1) :=
  Vector.ofFn fun j : Fin (N + 1) =>
    ∑ i : Fin (j.1 + 1),
      v.get ⟨i.1, by omega⟩ * tauEtaCoeffMod691 (j.1 - i.1)

/-- Coefficients `0..N` of `(q;q)_∞^k`, computed by repeated truncated
convolution in `ZMod 691`. -/
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
      rfl

theorem ramanujanTau_succ_eq_tauEtaPowVecMod691 {N n : Nat} (hN : n < N + 1) :
    ramanujanTau (ZMod 691) (n + 1) =
      (tauEtaPowVecMod691 N 24).get ⟨n, hN⟩ := by
  unfold ramanujanTau discriminantPS
  rw [PowerSeries.coeff_succ_X_mul]
  rw [← tauEtaPowVecMod691_spec N 24 ⟨n, hN⟩]

/-- A mod-691 divisor-power sum, avoiding large integer powers during
decidable evaluation. -/
def sigma11Mod691 (n : Nat) : ZMod 691 :=
  ∑ d ∈ Finset.Icc 1 n, if d ∣ n then (d : ZMod 691) ^ 11 else 0

theorem sigma11Mod691_eq (n : Nat) :
    sigma11Mod691 n = (sigma11 n : ZMod 691) := by
  unfold sigma11Mod691 sigma11 Nat.divisorSum
  push_cast
  apply Finset.sum_congr rfl
  intro d _
  by_cases h : d ∣ n <;> simp [h]

/-- Local reduced weight-12 Eisenstein coefficient series.  Its constant term
is zero modulo 691, matching the local convention `sigma11 0 = 0`. -/
noncomputable def eisensteinE12PSMod691 : (ZMod 691)⟦X⟧ :=
  PowerSeries.mk fun n => (sigma11 n : ZMod 691)

@[simp] theorem coeff_eisensteinE12PSMod691 (n : Nat) :
    (eisensteinE12PSMod691).coeff n = (sigma11 n : ZMod 691) := by
  simp [eisensteinE12PSMod691]

/-- The fixed finite Boolean check used by `native_decide`.

Index `i : Fin 200` checks the congruence at `n = i + 1`.  The local `let`
ensures the `eta^24` coefficient vector is computed once. -/
def tauSigmaMod691Through200Check : Bool :=
  let tauV := tauEtaPowVecMod691 199 24
  (List.range 200).all fun i =>
    if h : i < 200 then
      decide (tauV.get ⟨i, h⟩ = sigma11Mod691 (i + 1))
    else false

set_option maxHeartbeats 8000000 in
/-- Decidable certificate for `τ(n) ≡ σ₁₁(n) (mod 691)`, `1 ≤ n ≤ 200`,
computed with the Chapter 20 eta-coefficient convolution engine reduced
modulo 691. -/
theorem tauSigmaMod691Through200Check_true :
    tauSigmaMod691Through200Check = true := by
  native_decide

/-- Ramanujan's mod-691 congruence verified through `n = 200`.

The `n = 0` case is included to match the local `sigma11 0 = 0` convention. -/
theorem ramanujanTau_congr_sigma11_mod_691_through_200
    (n : Nat) (hn : n ≤ 200) :
    (ramanujanTau ℤ n : ZMod 691) = (sigma11 n : ZMod 691) := by
  cases n with
  | zero =>
      simp [PartIV.Ch20.ramanujanTau_zero, sigma11, Nat.divisorSum]
  | succ m =>
      have hm : m < 200 := by omega
      have hcheck :
          (tauEtaPowVecMod691 199 24).get ⟨m, by omega⟩ =
            sigma11Mod691 (m + 1) := by
        have hall := List.all_eq_true.mp tauSigmaMod691Through200Check_true
        have hmrange : m ∈ List.range 200 := List.mem_range.mpr hm
        have hmtrue := hall m hmrange
        simp [hm] at hmtrue
        exact hmtrue
      rw [cast_ramanujanTau_int]
      rw [ramanujanTau_succ_eq_tauEtaPowVecMod691 (N := 199) (n := m) (by omega)]
      rw [hcheck, sigma11Mod691_eq]

/-- Strict-bound variant of the through-200 finite congruence. -/
theorem ramanujanTau_congr_sigma11_mod_691_lt_201
    (n : Nat) (hn : n < 201) :
    (ramanujanTau ℤ n : ZMod 691) = (sigma11 n : ZMod 691) :=
  ramanujanTau_congr_sigma11_mod_691_through_200 n (by omega)

/-- Complement-bound variant of the through-200 finite congruence. -/
theorem ramanujanTau_congr_sigma11_mod_691_of_not_201_le
    {n : Nat} (hn : ¬ 201 ≤ n) :
    (ramanujanTau ℤ n : ZMod 691) = (sigma11 n : ZMod 691) :=
  ramanujanTau_congr_sigma11_mod_691_through_200 n (by omega)

/-- Difference form of Ramanujan's mod-691 congruence through `n = 200`. -/
theorem ramanujanTau_sub_sigma11_mod_691_eq_zero_through_200
    (n : Nat) (hn : n ≤ 200) :
    (ramanujanTau ℤ n : ZMod 691) - (sigma11 n : ZMod 691) = 0 := by
  rw [ramanujanTau_congr_sigma11_mod_691_through_200 n hn]
  simp

/-- Strict-bound difference form of the through-200 congruence. -/
theorem ramanujanTau_sub_sigma11_mod_691_eq_zero_lt_201
    (n : Nat) (hn : n < 201) :
    (ramanujanTau ℤ n : ZMod 691) - (sigma11 n : ZMod 691) = 0 :=
  ramanujanTau_sub_sigma11_mod_691_eq_zero_through_200 n (by omega)

/-- Complement-bound difference form of the through-200 congruence. -/
theorem ramanujanTau_sub_sigma11_mod_691_eq_zero_of_not_201_le
    {n : Nat} (hn : ¬ 201 ≤ n) :
    (ramanujanTau ℤ n : ZMod 691) - (sigma11 n : ZMod 691) = 0 :=
  ramanujanTau_sub_sigma11_mod_691_eq_zero_through_200 n (by omega)

/-- Reverse-difference form of Ramanujan's mod-691 congruence through
`n = 200`. -/
theorem sigma11_sub_ramanujanTau_mod_691_eq_zero_through_200
    (n : Nat) (hn : n ≤ 200) :
    (sigma11 n : ZMod 691) - (ramanujanTau ℤ n : ZMod 691) = 0 := by
  rw [← ramanujanTau_congr_sigma11_mod_691_through_200 n hn]
  simp

/-- Strict-bound reverse-difference form of the through-200 congruence. -/
theorem sigma11_sub_ramanujanTau_mod_691_eq_zero_lt_201
    (n : Nat) (hn : n < 201) :
    (sigma11 n : ZMod 691) - (ramanujanTau ℤ n : ZMod 691) = 0 :=
  sigma11_sub_ramanujanTau_mod_691_eq_zero_through_200 n (by omega)

/-- Complement-bound reverse-difference form of the through-200 congruence. -/
theorem sigma11_sub_ramanujanTau_mod_691_eq_zero_of_not_201_le
    {n : Nat} (hn : ¬ 201 ≤ n) :
    (sigma11 n : ZMod 691) - (ramanujanTau ℤ n : ZMod 691) = 0 :=
  sigma11_sub_ramanujanTau_mod_691_eq_zero_through_200 n (by omega)

/-- The same finite Boolean check extended to `n = 250`. -/
def tauSigmaMod691Through250Check : Bool :=
  let tauV := tauEtaPowVecMod691 249 24
  (List.range 250).all fun i =>
    if h : i < 250 then
      decide (tauV.get ⟨i, h⟩ = sigma11Mod691 (i + 1))
    else false

set_option maxHeartbeats 12000000 in
/-- Decidable certificate for `τ(n) ≡ σ₁₁(n) (mod 691)`, `1 ≤ n ≤ 250`. -/
theorem tauSigmaMod691Through250Check_true :
    tauSigmaMod691Through250Check = true := by
  native_decide

/-- Ramanujan's mod-691 congruence verified through `n = 250`. -/
theorem ramanujanTau_congr_sigma11_mod_691_through_250
    (n : Nat) (hn : n ≤ 250) :
    (ramanujanTau ℤ n : ZMod 691) = (sigma11 n : ZMod 691) := by
  cases n with
  | zero =>
      simp [PartIV.Ch20.ramanujanTau_zero, sigma11, Nat.divisorSum]
  | succ m =>
      have hm : m < 250 := by omega
      have hcheck :
          (tauEtaPowVecMod691 249 24).get ⟨m, by omega⟩ =
            sigma11Mod691 (m + 1) := by
        have hall := List.all_eq_true.mp tauSigmaMod691Through250Check_true
        have hmrange : m ∈ List.range 250 := List.mem_range.mpr hm
        have hmtrue := hall m hmrange
        simp [hm] at hmtrue
        exact hmtrue
      rw [cast_ramanujanTau_int]
      rw [ramanujanTau_succ_eq_tauEtaPowVecMod691 (N := 249) (n := m) (by omega)]
      rw [hcheck, sigma11Mod691_eq]

/-- Strict-bound variant of the through-250 finite congruence. -/
theorem ramanujanTau_congr_sigma11_mod_691_lt_251
    (n : Nat) (hn : n < 251) :
    (ramanujanTau ℤ n : ZMod 691) = (sigma11 n : ZMod 691) :=
  ramanujanTau_congr_sigma11_mod_691_through_250 n (by omega)

/-- Complement-bound variant of the through-250 finite congruence. -/
theorem ramanujanTau_congr_sigma11_mod_691_of_not_251_le
    {n : Nat} (hn : ¬ 251 ≤ n) :
    (ramanujanTau ℤ n : ZMod 691) = (sigma11 n : ZMod 691) :=
  ramanujanTau_congr_sigma11_mod_691_through_250 n (by omega)

/-- Difference form of Ramanujan's mod-691 congruence through `n = 250`. -/
theorem ramanujanTau_sub_sigma11_mod_691_eq_zero_through_250
    (n : Nat) (hn : n ≤ 250) :
    (ramanujanTau ℤ n : ZMod 691) - (sigma11 n : ZMod 691) = 0 := by
  rw [ramanujanTau_congr_sigma11_mod_691_through_250 n hn]
  simp

/-- Strict-bound difference form of the through-250 congruence. -/
theorem ramanujanTau_sub_sigma11_mod_691_eq_zero_lt_251
    (n : Nat) (hn : n < 251) :
    (ramanujanTau ℤ n : ZMod 691) - (sigma11 n : ZMod 691) = 0 :=
  ramanujanTau_sub_sigma11_mod_691_eq_zero_through_250 n (by omega)

/-- Complement-bound difference form of the through-250 congruence. -/
theorem ramanujanTau_sub_sigma11_mod_691_eq_zero_of_not_251_le
    {n : Nat} (hn : ¬ 251 ≤ n) :
    (ramanujanTau ℤ n : ZMod 691) - (sigma11 n : ZMod 691) = 0 :=
  ramanujanTau_sub_sigma11_mod_691_eq_zero_through_250 n (by omega)

/-- Reverse-difference form of Ramanujan's mod-691 congruence through
`n = 250`. -/
theorem sigma11_sub_ramanujanTau_mod_691_eq_zero_through_250
    (n : Nat) (hn : n ≤ 250) :
    (sigma11 n : ZMod 691) - (ramanujanTau ℤ n : ZMod 691) = 0 := by
  rw [← ramanujanTau_congr_sigma11_mod_691_through_250 n hn]
  simp

/-- Strict-bound reverse-difference form of the through-250 congruence. -/
theorem sigma11_sub_ramanujanTau_mod_691_eq_zero_lt_251
    (n : Nat) (hn : n < 251) :
    (sigma11 n : ZMod 691) - (ramanujanTau ℤ n : ZMod 691) = 0 :=
  sigma11_sub_ramanujanTau_mod_691_eq_zero_through_250 n (by omega)

/-- Complement-bound reverse-difference form of the through-250 congruence. -/
theorem sigma11_sub_ramanujanTau_mod_691_eq_zero_of_not_251_le
    {n : Nat} (hn : ¬ 251 ≤ n) :
    (sigma11 n : ZMod 691) - (ramanujanTau ℤ n : ZMod 691) = 0 :=
  sigma11_sub_ramanujanTau_mod_691_eq_zero_through_250 n (by omega)

/-- New concrete checkpoint: `τ(201) ≡ σ₁₁(201) (mod 691)`. -/
theorem ramanujanTau_congr_sigma11_mod_691_201 :
    (ramanujanTau ℤ 201 : ZMod 691) = (sigma11 201 : ZMod 691) :=
  ramanujanTau_congr_sigma11_mod_691_through_250 201 (by norm_num)

/-- New concrete checkpoint: `τ(225) ≡ σ₁₁(225) (mod 691)`. -/
theorem ramanujanTau_congr_sigma11_mod_691_225 :
    (ramanujanTau ℤ 225 : ZMod 691) = (sigma11 225 : ZMod 691) :=
  ramanujanTau_congr_sigma11_mod_691_through_250 225 (by norm_num)

/-- New concrete checkpoint: `τ(250) ≡ σ₁₁(250) (mod 691)`. -/
theorem ramanujanTau_congr_sigma11_mod_691_250 :
    (ramanujanTau ℤ 250 : ZMod 691) = (sigma11 250 : ZMod 691) :=
  ramanujanTau_congr_sigma11_mod_691_through_250 250 (by norm_num)

/-- Concrete zero-difference checkpoint: `τ(201)-σ₁₁(201)=0 (mod 691)`. -/
theorem ramanujanTau_sub_sigma11_mod_691_eq_zero_201 :
    (ramanujanTau ℤ 201 : ZMod 691) - (sigma11 201 : ZMod 691) = 0 :=
  ramanujanTau_sub_sigma11_mod_691_eq_zero_through_250 201 (by norm_num)

/-- Concrete zero-difference checkpoint: `τ(225)-σ₁₁(225)=0 (mod 691)`. -/
theorem ramanujanTau_sub_sigma11_mod_691_eq_zero_225 :
    (ramanujanTau ℤ 225 : ZMod 691) - (sigma11 225 : ZMod 691) = 0 :=
  ramanujanTau_sub_sigma11_mod_691_eq_zero_through_250 225 (by norm_num)

/-- Concrete zero-difference checkpoint: `τ(250)-σ₁₁(250)=0 (mod 691)`. -/
theorem ramanujanTau_sub_sigma11_mod_691_eq_zero_250 :
    (ramanujanTau ℤ 250 : ZMod 691) - (sigma11 250 : ZMod 691) = 0 :=
  ramanujanTau_sub_sigma11_mod_691_eq_zero_through_250 250 (by norm_num)

/-- Concrete reverse zero-difference checkpoint:
`σ₁₁(201)-τ(201)=0 (mod 691)`. -/
theorem sigma11_sub_ramanujanTau_mod_691_eq_zero_201 :
    (sigma11 201 : ZMod 691) - (ramanujanTau ℤ 201 : ZMod 691) = 0 :=
  sigma11_sub_ramanujanTau_mod_691_eq_zero_through_250 201 (by norm_num)

/-- Concrete reverse zero-difference checkpoint:
`σ₁₁(225)-τ(225)=0 (mod 691)`. -/
theorem sigma11_sub_ramanujanTau_mod_691_eq_zero_225 :
    (sigma11 225 : ZMod 691) - (ramanujanTau ℤ 225 : ZMod 691) = 0 :=
  sigma11_sub_ramanujanTau_mod_691_eq_zero_through_250 225 (by norm_num)

/-- Concrete reverse zero-difference checkpoint:
`σ₁₁(250)-τ(250)=0 (mod 691)`. -/
theorem sigma11_sub_ramanujanTau_mod_691_eq_zero_250 :
    (sigma11 250 : ZMod 691) - (ramanujanTau ℤ 250 : ZMod 691) = 0 :=
  sigma11_sub_ramanujanTau_mod_691_eq_zero_through_250 250 (by norm_num)

/-- Coefficient-level form: the discriminant and the reduced Eisenstein `E_12`
series agree through degree `200`. -/
theorem coeff_discriminantPS_eq_eisensteinE12PSMod691_through_200
    (n : Nat) (hn : n ≤ 200) :
    (discriminantPS (ZMod 691)).coeff n =
      (eisensteinE12PSMod691).coeff n := by
  change ramanujanTau (ZMod 691) n = (eisensteinE12PSMod691).coeff n
  rw [← PartIV.Ch20.cast_ramanujanTau_int (ZMod 691) n]
  rw [coeff_eisensteinE12PSMod691]
  exact ramanujanTau_congr_sigma11_mod_691_through_200 n hn

/-- Difference form of the same finite coefficient identity. -/
theorem coeff_discriminantPS_sub_eisensteinE12PSMod691_eq_zero_through_200
    (n : Nat) (hn : n ≤ 200) :
    (discriminantPS (ZMod 691) - eisensteinE12PSMod691).coeff n = 0 := by
  rw [map_sub]
  rw [coeff_discriminantPS_eq_eisensteinE12PSMod691_through_200 n hn]
  simp

/-- Reverse-difference form of the through-200 finite coefficient identity. -/
theorem coeff_eisensteinE12PSMod691_sub_discriminantPS_eq_zero_through_200
    (n : Nat) (hn : n ≤ 200) :
    (eisensteinE12PSMod691 - discriminantPS (ZMod 691)).coeff n = 0 := by
  rw [map_sub]
  rw [← coeff_discriminantPS_eq_eisensteinE12PSMod691_through_200 n hn]
  simp

/-- Truncated formal-PS equality through degree `200`. -/
theorem trunc_discriminantPS_eq_eisensteinE12PSMod691_through_200 :
    PowerSeries.trunc 201 (discriminantPS (ZMod 691)) =
      PowerSeries.trunc 201 eisensteinE12PSMod691 := by
  ext n
  by_cases hn : n < 201
  · rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc, if_pos hn, if_pos hn]
    exact coeff_discriminantPS_eq_eisensteinE12PSMod691_through_200 n (by omega)
  · rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc, if_neg hn, if_neg hn]

/-- Symmetric truncated formal-PS equality through degree `200`. -/
theorem trunc_eisensteinE12PSMod691_eq_discriminantPS_through_200 :
    PowerSeries.trunc 201 eisensteinE12PSMod691 =
      PowerSeries.trunc 201 (discriminantPS (ZMod 691)) :=
  trunc_discriminantPS_eq_eisensteinE12PSMod691_through_200.symm

/-- Truncated zero-difference form through degree `200`. -/
theorem trunc_discriminantPS_sub_eisensteinE12PSMod691_eq_zero_through_200 :
    PowerSeries.trunc 201 (discriminantPS (ZMod 691) - eisensteinE12PSMod691) = 0 := by
  ext n
  by_cases hn : n < 201
  · rw [PowerSeries.coeff_trunc, if_pos hn]
    exact coeff_discriminantPS_sub_eisensteinE12PSMod691_eq_zero_through_200 n (by omega)
  · rw [PowerSeries.coeff_trunc, if_neg hn]
    simp

/-- Truncated reverse zero-difference form through degree `200`. -/
theorem trunc_eisensteinE12PSMod691_sub_discriminantPS_eq_zero_through_200 :
    PowerSeries.trunc 201 (eisensteinE12PSMod691 - discriminantPS (ZMod 691)) = 0 := by
  ext n
  by_cases hn : n < 201
  · rw [PowerSeries.coeff_trunc, if_pos hn]
    exact coeff_eisensteinE12PSMod691_sub_discriminantPS_eq_zero_through_200 n (by omega)
  · rw [PowerSeries.coeff_trunc, if_neg hn]
    simp

/-- Coefficient-level form of the through-250 finite mod-691 congruence. -/
theorem coeff_discriminantPS_eq_eisensteinE12PSMod691_through_250
    (n : Nat) (hn : n ≤ 250) :
    (discriminantPS (ZMod 691)).coeff n =
      (eisensteinE12PSMod691).coeff n := by
  change ramanujanTau (ZMod 691) n = (eisensteinE12PSMod691).coeff n
  rw [← PartIV.Ch20.cast_ramanujanTau_int (ZMod 691) n]
  rw [coeff_eisensteinE12PSMod691]
  exact ramanujanTau_congr_sigma11_mod_691_through_250 n hn

/-- Strict-bound coefficient-level form of the through-250 congruence. -/
theorem coeff_discriminantPS_eq_eisensteinE12PSMod691_lt_251
    (n : Nat) (hn : n < 251) :
    (discriminantPS (ZMod 691)).coeff n =
      (eisensteinE12PSMod691).coeff n :=
  coeff_discriminantPS_eq_eisensteinE12PSMod691_through_250 n (by omega)

/-- Difference form of the through-250 finite coefficient identity. -/
theorem coeff_discriminantPS_sub_eisensteinE12PSMod691_eq_zero_through_250
    (n : Nat) (hn : n ≤ 250) :
    (discriminantPS (ZMod 691) - eisensteinE12PSMod691).coeff n = 0 := by
  rw [map_sub]
  rw [coeff_discriminantPS_eq_eisensteinE12PSMod691_through_250 n hn]
  simp

/-- Reverse-difference form of the through-250 finite coefficient identity. -/
theorem coeff_eisensteinE12PSMod691_sub_discriminantPS_eq_zero_through_250
    (n : Nat) (hn : n ≤ 250) :
    (eisensteinE12PSMod691 - discriminantPS (ZMod 691)).coeff n = 0 := by
  rw [map_sub]
  rw [← coeff_discriminantPS_eq_eisensteinE12PSMod691_through_250 n hn]
  simp

/-- Truncated formal-PS equality through degree `250`. -/
theorem trunc_discriminantPS_eq_eisensteinE12PSMod691_through_250 :
    PowerSeries.trunc 251 (discriminantPS (ZMod 691)) =
      PowerSeries.trunc 251 eisensteinE12PSMod691 := by
  ext n
  by_cases hn : n < 251
  · rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc, if_pos hn, if_pos hn]
    exact coeff_discriminantPS_eq_eisensteinE12PSMod691_through_250 n (by omega)
  · rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc, if_neg hn, if_neg hn]

/-- Symmetric truncated formal-PS equality through degree `250`. -/
theorem trunc_eisensteinE12PSMod691_eq_discriminantPS_through_250 :
    PowerSeries.trunc 251 eisensteinE12PSMod691 =
      PowerSeries.trunc 251 (discriminantPS (ZMod 691)) :=
  trunc_discriminantPS_eq_eisensteinE12PSMod691_through_250.symm

/-- Truncated zero-difference form through degree `250`. -/
theorem trunc_discriminantPS_sub_eisensteinE12PSMod691_eq_zero_through_250 :
    PowerSeries.trunc 251 (discriminantPS (ZMod 691) - eisensteinE12PSMod691) = 0 := by
  ext n
  by_cases hn : n < 251
  · rw [PowerSeries.coeff_trunc, if_pos hn]
    exact coeff_discriminantPS_sub_eisensteinE12PSMod691_eq_zero_through_250 n (by omega)
  · rw [PowerSeries.coeff_trunc, if_neg hn]
    simp

/-- Truncated reverse zero-difference form through degree `250`. -/
theorem trunc_eisensteinE12PSMod691_sub_discriminantPS_eq_zero_through_250 :
    PowerSeries.trunc 251 (eisensteinE12PSMod691 - discriminantPS (ZMod 691)) = 0 := by
  ext n
  by_cases hn : n < 251
  · rw [PowerSeries.coeff_trunc, if_pos hn]
    exact coeff_eisensteinE12PSMod691_sub_discriminantPS_eq_zero_through_250 n (by omega)
  · rw [PowerSeries.coeff_trunc, if_neg hn]
    simp

/-- Concrete coefficient checkpoint at degree `201`. -/
theorem coeff_discriminantPS_eq_eisensteinE12PSMod691_201 :
    (discriminantPS (ZMod 691)).coeff 201 =
      (eisensteinE12PSMod691).coeff 201 :=
  coeff_discriminantPS_eq_eisensteinE12PSMod691_through_250 201 (by norm_num)

/-- Concrete coefficient checkpoint at degree `225`. -/
theorem coeff_discriminantPS_eq_eisensteinE12PSMod691_225 :
    (discriminantPS (ZMod 691)).coeff 225 =
      (eisensteinE12PSMod691).coeff 225 :=
  coeff_discriminantPS_eq_eisensteinE12PSMod691_through_250 225 (by norm_num)

/-- Concrete coefficient checkpoint at degree `250`. -/
theorem coeff_discriminantPS_eq_eisensteinE12PSMod691_250 :
    (discriminantPS (ZMod 691)).coeff 250 =
      (eisensteinE12PSMod691).coeff 250 :=
  coeff_discriminantPS_eq_eisensteinE12PSMod691_through_250 250 (by norm_num)

/-- Concrete zero-difference coefficient checkpoint at degree `201`. -/
theorem coeff_discriminantPS_sub_eisensteinE12PSMod691_eq_zero_201 :
    (discriminantPS (ZMod 691) - eisensteinE12PSMod691).coeff 201 = 0 :=
  coeff_discriminantPS_sub_eisensteinE12PSMod691_eq_zero_through_250 201 (by norm_num)

/-- Concrete zero-difference coefficient checkpoint at degree `225`. -/
theorem coeff_discriminantPS_sub_eisensteinE12PSMod691_eq_zero_225 :
    (discriminantPS (ZMod 691) - eisensteinE12PSMod691).coeff 225 = 0 :=
  coeff_discriminantPS_sub_eisensteinE12PSMod691_eq_zero_through_250 225 (by norm_num)

/-- Concrete zero-difference coefficient checkpoint at degree `250`. -/
theorem coeff_discriminantPS_sub_eisensteinE12PSMod691_eq_zero_250 :
    (discriminantPS (ZMod 691) - eisensteinE12PSMod691).coeff 250 = 0 :=
  coeff_discriminantPS_sub_eisensteinE12PSMod691_eq_zero_through_250 250 (by norm_num)

/-- Concrete reverse zero-difference coefficient checkpoint at degree `201`. -/
theorem coeff_eisensteinE12PSMod691_sub_discriminantPS_eq_zero_201 :
    (eisensteinE12PSMod691 - discriminantPS (ZMod 691)).coeff 201 = 0 :=
  coeff_eisensteinE12PSMod691_sub_discriminantPS_eq_zero_through_250 201 (by norm_num)

/-- Concrete reverse zero-difference coefficient checkpoint at degree `225`. -/
theorem coeff_eisensteinE12PSMod691_sub_discriminantPS_eq_zero_225 :
    (eisensteinE12PSMod691 - discriminantPS (ZMod 691)).coeff 225 = 0 :=
  coeff_eisensteinE12PSMod691_sub_discriminantPS_eq_zero_through_250 225 (by norm_num)

/-- Concrete reverse zero-difference coefficient checkpoint at degree `250`. -/
theorem coeff_eisensteinE12PSMod691_sub_discriminantPS_eq_zero_250 :
    (eisensteinE12PSMod691 - discriminantPS (ZMod 691)).coeff 250 = 0 :=
  coeff_eisensteinE12PSMod691_sub_discriminantPS_eq_zero_through_250 250 (by norm_num)

/-- The same finite Boolean check extended to `n = 300`. -/
def tauSigmaMod691Through300Check : Bool :=
  let tauV := tauEtaPowVecMod691 299 24
  (List.range 300).all fun i =>
    if h : i < 300 then
      decide (tauV.get ⟨i, h⟩ = sigma11Mod691 (i + 1))
    else false

set_option maxHeartbeats 20000000 in
/-- Decidable certificate for `τ(n) ≡ σ₁₁(n) (mod 691)`, `1 ≤ n ≤ 300`. -/
theorem tauSigmaMod691Through300Check_true :
    tauSigmaMod691Through300Check = true := by
  native_decide

/-- Ramanujan's mod-691 congruence verified through `n = 300`. -/
theorem ramanujanTau_congr_sigma11_mod_691_through_300
    (n : Nat) (hn : n ≤ 300) :
    (ramanujanTau ℤ n : ZMod 691) = (sigma11 n : ZMod 691) := by
  cases n with
  | zero =>
      simp [PartIV.Ch20.ramanujanTau_zero, sigma11, Nat.divisorSum]
  | succ m =>
      have hm : m < 300 := by omega
      have hcheck :
          (tauEtaPowVecMod691 299 24).get ⟨m, by omega⟩ =
            sigma11Mod691 (m + 1) := by
        have hall := List.all_eq_true.mp tauSigmaMod691Through300Check_true
        have hmrange : m ∈ List.range 300 := List.mem_range.mpr hm
        have hmtrue := hall m hmrange
        simp [hm] at hmtrue
        exact hmtrue
      rw [cast_ramanujanTau_int]
      rw [ramanujanTau_succ_eq_tauEtaPowVecMod691 (N := 299) (n := m) (by omega)]
      rw [hcheck, sigma11Mod691_eq]

/-- Strict-bound variant of the through-300 finite congruence. -/
theorem ramanujanTau_congr_sigma11_mod_691_lt_301
    (n : Nat) (hn : n < 301) :
    (ramanujanTau ℤ n : ZMod 691) = (sigma11 n : ZMod 691) :=
  ramanujanTau_congr_sigma11_mod_691_through_300 n (by omega)

/-- Complement-bound variant of the through-300 finite congruence. -/
theorem ramanujanTau_congr_sigma11_mod_691_of_not_301_le
    {n : Nat} (hn : ¬ 301 ≤ n) :
    (ramanujanTau ℤ n : ZMod 691) = (sigma11 n : ZMod 691) :=
  ramanujanTau_congr_sigma11_mod_691_through_300 n (by omega)

/-- Difference form of Ramanujan's mod-691 congruence through `n = 300`. -/
theorem ramanujanTau_sub_sigma11_mod_691_eq_zero_through_300
    (n : Nat) (hn : n ≤ 300) :
    (ramanujanTau ℤ n : ZMod 691) - (sigma11 n : ZMod 691) = 0 := by
  rw [ramanujanTau_congr_sigma11_mod_691_through_300 n hn]
  simp

/-- Strict-bound difference form of Ramanujan's mod-691 congruence. -/
theorem ramanujanTau_sub_sigma11_mod_691_eq_zero_lt_301
    (n : Nat) (hn : n < 301) :
    (ramanujanTau ℤ n : ZMod 691) - (sigma11 n : ZMod 691) = 0 :=
  ramanujanTau_sub_sigma11_mod_691_eq_zero_through_300 n (by omega)

/-- Reverse-difference form of Ramanujan's mod-691 congruence through
`n = 300`. -/
theorem sigma11_sub_ramanujanTau_mod_691_eq_zero_through_300
    (n : Nat) (hn : n ≤ 300) :
    (sigma11 n : ZMod 691) - (ramanujanTau ℤ n : ZMod 691) = 0 := by
  rw [← ramanujanTau_congr_sigma11_mod_691_through_300 n hn]
  simp

/-- Strict-bound reverse-difference form of Ramanujan's mod-691 congruence. -/
theorem sigma11_sub_ramanujanTau_mod_691_eq_zero_lt_301
    (n : Nat) (hn : n < 301) :
    (sigma11 n : ZMod 691) - (ramanujanTau ℤ n : ZMod 691) = 0 :=
  sigma11_sub_ramanujanTau_mod_691_eq_zero_through_300 n (by omega)

/-- Complement-bound reverse-difference form of Ramanujan's mod-691
congruence. -/
theorem sigma11_sub_ramanujanTau_mod_691_eq_zero_of_not_301_le
    {n : Nat} (hn : ¬ 301 ≤ n) :
    (sigma11 n : ZMod 691) - (ramanujanTau ℤ n : ZMod 691) = 0 :=
  sigma11_sub_ramanujanTau_mod_691_eq_zero_through_300 n (by omega)

/-- Coefficient-level form of the through-300 finite mod-691 congruence. -/
theorem coeff_discriminantPS_eq_eisensteinE12PSMod691_through_300
    (n : Nat) (hn : n ≤ 300) :
    (discriminantPS (ZMod 691)).coeff n =
      (eisensteinE12PSMod691).coeff n := by
  change ramanujanTau (ZMod 691) n = (eisensteinE12PSMod691).coeff n
  rw [← PartIV.Ch20.cast_ramanujanTau_int (ZMod 691) n]
  rw [coeff_eisensteinE12PSMod691]
  exact ramanujanTau_congr_sigma11_mod_691_through_300 n hn

/-- Strict-bound coefficient-level form of the through-300 congruence. -/
theorem coeff_discriminantPS_eq_eisensteinE12PSMod691_lt_301
    (n : Nat) (hn : n < 301) :
    (discriminantPS (ZMod 691)).coeff n =
      (eisensteinE12PSMod691).coeff n :=
  coeff_discriminantPS_eq_eisensteinE12PSMod691_through_300 n (by omega)

/-- Complement-bound coefficient-level form of the through-300 congruence. -/
theorem coeff_discriminantPS_eq_eisensteinE12PSMod691_of_not_301_le
    {n : Nat} (hn : ¬ 301 ≤ n) :
    (discriminantPS (ZMod 691)).coeff n =
      (eisensteinE12PSMod691).coeff n :=
  coeff_discriminantPS_eq_eisensteinE12PSMod691_through_300 n (by omega)

/-- Difference form of the through-300 finite coefficient identity. -/
theorem coeff_discriminantPS_sub_eisensteinE12PSMod691_eq_zero_through_300
    (n : Nat) (hn : n ≤ 300) :
    (discriminantPS (ZMod 691) - eisensteinE12PSMod691).coeff n = 0 := by
  rw [map_sub]
  rw [coeff_discriminantPS_eq_eisensteinE12PSMod691_through_300 n hn]
  simp

/-- Strict-bound difference form of the through-300 finite coefficient
identity. -/
theorem coeff_discriminantPS_sub_eisensteinE12PSMod691_eq_zero_lt_301
    (n : Nat) (hn : n < 301) :
    (discriminantPS (ZMod 691) - eisensteinE12PSMod691).coeff n = 0 :=
  coeff_discriminantPS_sub_eisensteinE12PSMod691_eq_zero_through_300 n (by omega)

/-- Complement-bound difference form of the through-300 finite coefficient
identity. -/
theorem coeff_discriminantPS_sub_eisensteinE12PSMod691_eq_zero_of_not_301_le
    {n : Nat} (hn : ¬ 301 ≤ n) :
    (discriminantPS (ZMod 691) - eisensteinE12PSMod691).coeff n = 0 :=
  coeff_discriminantPS_sub_eisensteinE12PSMod691_eq_zero_through_300 n (by omega)

/-- Reverse-difference form of the through-300 finite coefficient identity. -/
theorem coeff_eisensteinE12PSMod691_sub_discriminantPS_eq_zero_through_300
    (n : Nat) (hn : n ≤ 300) :
    (eisensteinE12PSMod691 - discriminantPS (ZMod 691)).coeff n = 0 := by
  rw [map_sub]
  rw [← coeff_discriminantPS_eq_eisensteinE12PSMod691_through_300 n hn]
  simp

/-- Strict-bound reverse-difference form of the through-300 finite coefficient
identity. -/
theorem coeff_eisensteinE12PSMod691_sub_discriminantPS_eq_zero_lt_301
    (n : Nat) (hn : n < 301) :
    (eisensteinE12PSMod691 - discriminantPS (ZMod 691)).coeff n = 0 :=
  coeff_eisensteinE12PSMod691_sub_discriminantPS_eq_zero_through_300 n (by omega)

/-- Complement-bound reverse-difference form of the through-300 finite
coefficient identity. -/
theorem coeff_eisensteinE12PSMod691_sub_discriminantPS_eq_zero_of_not_301_le
    {n : Nat} (hn : ¬ 301 ≤ n) :
    (eisensteinE12PSMod691 - discriminantPS (ZMod 691)).coeff n = 0 :=
  coeff_eisensteinE12PSMod691_sub_discriminantPS_eq_zero_through_300 n (by omega)

/-- Truncated formal-PS equality through degree `300`. -/
theorem trunc_discriminantPS_eq_eisensteinE12PSMod691_through_300 :
    PowerSeries.trunc 301 (discriminantPS (ZMod 691)) =
      PowerSeries.trunc 301 eisensteinE12PSMod691 := by
  ext n
  by_cases hn : n < 301
  · rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc, if_pos hn, if_pos hn]
    exact coeff_discriminantPS_eq_eisensteinE12PSMod691_through_300 n (by omega)
  · rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc, if_neg hn, if_neg hn]

/-- Symmetric truncated formal-PS equality through degree `300`. -/
theorem trunc_eisensteinE12PSMod691_eq_discriminantPS_through_300 :
    PowerSeries.trunc 301 eisensteinE12PSMod691 =
      PowerSeries.trunc 301 (discriminantPS (ZMod 691)) :=
  trunc_discriminantPS_eq_eisensteinE12PSMod691_through_300.symm

/-- Truncated zero-difference form through degree `300`. -/
theorem trunc_discriminantPS_sub_eisensteinE12PSMod691_eq_zero_through_300 :
    PowerSeries.trunc 301 (discriminantPS (ZMod 691) - eisensteinE12PSMod691) = 0 := by
  ext n
  by_cases hn : n < 301
  · rw [PowerSeries.coeff_trunc, if_pos hn]
    exact coeff_discriminantPS_sub_eisensteinE12PSMod691_eq_zero_through_300 n (by omega)
  · rw [PowerSeries.coeff_trunc, if_neg hn]
    simp

/-- Truncated reverse zero-difference form through degree `300`. -/
theorem trunc_eisensteinE12PSMod691_sub_discriminantPS_eq_zero_through_300 :
    PowerSeries.trunc 301 (eisensteinE12PSMod691 - discriminantPS (ZMod 691)) = 0 := by
  ext n
  by_cases hn : n < 301
  · rw [PowerSeries.coeff_trunc, if_pos hn]
    exact coeff_eisensteinE12PSMod691_sub_discriminantPS_eq_zero_through_300 n (by omega)
  · rw [PowerSeries.coeff_trunc, if_neg hn]
    simp

/-- There is no mod-691 `τ`/`σ₁₁` congruence counterexample through `n = 300`. -/
theorem not_exists_le_300_ramanujanTau_congr_sigma11_mod_691_counterexample :
    ¬ ∃ n : Nat, n ≤ 300 ∧
      (ramanujanTau ℤ n : ZMod 691) ≠ (sigma11 n : ZMod 691) := by
  rintro ⟨n, hn, hne⟩
  exact hne (ramanujanTau_congr_sigma11_mod_691_through_300 n hn)

/-- Strict-bound form: there is no mod-691 `τ`/`σ₁₁` congruence
counterexample below `301`. -/
theorem not_exists_lt_301_ramanujanTau_congr_sigma11_mod_691_counterexample :
    ¬ ∃ n : Nat, n < 301 ∧
      (ramanujanTau ℤ n : ZMod 691) ≠ (sigma11 n : ZMod 691) := by
  rintro ⟨n, hn, hne⟩
  exact hne (ramanujanTau_congr_sigma11_mod_691_lt_301 n hn)

/-- There is no nonzero forward `τ - σ₁₁` difference through `n = 300`. -/
theorem not_exists_le_300_ramanujanTau_sub_sigma11_mod_691_ne_zero :
    ¬ ∃ n : Nat, n ≤ 300 ∧
      (ramanujanTau ℤ n : ZMod 691) - (sigma11 n : ZMod 691) ≠ 0 := by
  rintro ⟨n, hn, hne⟩
  exact hne (ramanujanTau_sub_sigma11_mod_691_eq_zero_through_300 n hn)

/-- Strict-bound form: there is no nonzero forward `τ - σ₁₁` difference below
`301`. -/
theorem not_exists_lt_301_ramanujanTau_sub_sigma11_mod_691_ne_zero :
    ¬ ∃ n : Nat, n < 301 ∧
      (ramanujanTau ℤ n : ZMod 691) - (sigma11 n : ZMod 691) ≠ 0 := by
  rintro ⟨n, hn, hne⟩
  exact hne (ramanujanTau_sub_sigma11_mod_691_eq_zero_lt_301 n hn)

/-- There is no nonzero reverse `σ₁₁ - τ` difference through `n = 300`. -/
theorem not_exists_le_300_sigma11_sub_ramanujanTau_mod_691_ne_zero :
    ¬ ∃ n : Nat, n ≤ 300 ∧
      (sigma11 n : ZMod 691) - (ramanujanTau ℤ n : ZMod 691) ≠ 0 := by
  rintro ⟨n, hn, hne⟩
  exact hne (sigma11_sub_ramanujanTau_mod_691_eq_zero_through_300 n hn)

/-- Strict-bound form: there is no nonzero reverse `σ₁₁ - τ` difference below
`301`. -/
theorem not_exists_lt_301_sigma11_sub_ramanujanTau_mod_691_ne_zero :
    ¬ ∃ n : Nat, n < 301 ∧
      (sigma11 n : ZMod 691) - (ramanujanTau ℤ n : ZMod 691) ≠ 0 := by
  rintro ⟨n, hn, hne⟩
  exact hne (sigma11_sub_ramanujanTau_mod_691_eq_zero_lt_301 n hn)

/-- There is no coefficient mismatch between the reduced discriminant and
local Eisenstein `E_12` series through degree `300`. -/
theorem not_exists_le_300_coeff_discriminantPS_ne_eisensteinE12PSMod691 :
    ¬ ∃ n : Nat, n ≤ 300 ∧
      (discriminantPS (ZMod 691)).coeff n ≠ eisensteinE12PSMod691.coeff n := by
  rintro ⟨n, hn, hne⟩
  exact hne (coeff_discriminantPS_eq_eisensteinE12PSMod691_through_300 n hn)

/-- Strict-bound form: there is no coefficient mismatch below degree `301`. -/
theorem not_exists_lt_301_coeff_discriminantPS_ne_eisensteinE12PSMod691 :
    ¬ ∃ n : Nat, n < 301 ∧
      (discriminantPS (ZMod 691)).coeff n ≠ eisensteinE12PSMod691.coeff n := by
  rintro ⟨n, hn, hne⟩
  exact hne (coeff_discriminantPS_eq_eisensteinE12PSMod691_lt_301 n hn)

/-- The forward coefficient difference has no nonzero coefficient through
degree `300`. -/
theorem not_exists_le_300_coeff_discriminantPS_sub_eisensteinE12PSMod691_ne_zero :
    ¬ ∃ n : Nat, n ≤ 300 ∧
      (discriminantPS (ZMod 691) - eisensteinE12PSMod691).coeff n ≠ 0 := by
  rintro ⟨n, hn, hne⟩
  exact hne (coeff_discriminantPS_sub_eisensteinE12PSMod691_eq_zero_through_300 n hn)

/-- Strict-bound form: the forward coefficient difference has no nonzero
coefficient below degree `301`. -/
theorem not_exists_lt_301_coeff_discriminantPS_sub_eisensteinE12PSMod691_ne_zero :
    ¬ ∃ n : Nat, n < 301 ∧
      (discriminantPS (ZMod 691) - eisensteinE12PSMod691).coeff n ≠ 0 := by
  rintro ⟨n, hn, hne⟩
  exact hne (coeff_discriminantPS_sub_eisensteinE12PSMod691_eq_zero_lt_301 n hn)

/-- The reverse coefficient difference has no nonzero coefficient through
degree `300`. -/
theorem not_exists_le_300_coeff_eisensteinE12PSMod691_sub_discriminantPS_ne_zero :
    ¬ ∃ n : Nat, n ≤ 300 ∧
      (eisensteinE12PSMod691 - discriminantPS (ZMod 691)).coeff n ≠ 0 := by
  rintro ⟨n, hn, hne⟩
  exact hne (coeff_eisensteinE12PSMod691_sub_discriminantPS_eq_zero_through_300 n hn)

/-- Strict-bound form: the reverse coefficient difference has no nonzero
coefficient below degree `301`. -/
theorem not_exists_lt_301_coeff_eisensteinE12PSMod691_sub_discriminantPS_ne_zero :
    ¬ ∃ n : Nat, n < 301 ∧
      (eisensteinE12PSMod691 - discriminantPS (ZMod 691)).coeff n ≠ 0 := by
  rintro ⟨n, hn, hne⟩
  exact hne (coeff_eisensteinE12PSMod691_sub_discriminantPS_eq_zero_lt_301 n hn)

/-- Concrete checkpoint: `τ(260) ≡ σ₁₁(260) (mod 691)`. -/
theorem ramanujanTau_congr_sigma11_mod_691_260 :
    (ramanujanTau ℤ 260 : ZMod 691) = (sigma11 260 : ZMod 691) :=
  ramanujanTau_congr_sigma11_mod_691_through_300 260 (by norm_num)

/-- Concrete checkpoint: `τ(275) ≡ σ₁₁(275) (mod 691)`. -/
theorem ramanujanTau_congr_sigma11_mod_691_275 :
    (ramanujanTau ℤ 275 : ZMod 691) = (sigma11 275 : ZMod 691) :=
  ramanujanTau_congr_sigma11_mod_691_through_300 275 (by norm_num)

/-- Concrete checkpoint: `τ(288) ≡ σ₁₁(288) (mod 691)`. -/
theorem ramanujanTau_congr_sigma11_mod_691_288 :
    (ramanujanTau ℤ 288 : ZMod 691) = (sigma11 288 : ZMod 691) :=
  ramanujanTau_congr_sigma11_mod_691_through_300 288 (by norm_num)

/-- Concrete checkpoint: `τ(299) ≡ σ₁₁(299) (mod 691)`. -/
theorem ramanujanTau_congr_sigma11_mod_691_299 :
    (ramanujanTau ℤ 299 : ZMod 691) = (sigma11 299 : ZMod 691) :=
  ramanujanTau_congr_sigma11_mod_691_through_300 299 (by norm_num)

/-- Concrete checkpoint: `τ(300) ≡ σ₁₁(300) (mod 691)`. -/
theorem ramanujanTau_congr_sigma11_mod_691_300 :
    (ramanujanTau ℤ 300 : ZMod 691) = (sigma11 300 : ZMod 691) :=
  ramanujanTau_congr_sigma11_mod_691_through_300 300 (by norm_num)

/-- Concrete coefficient checkpoint at degree `260`. -/
theorem coeff_discriminantPS_eq_eisensteinE12PSMod691_260 :
    (discriminantPS (ZMod 691)).coeff 260 =
      (eisensteinE12PSMod691).coeff 260 :=
  coeff_discriminantPS_eq_eisensteinE12PSMod691_through_300 260 (by norm_num)

/-- Concrete coefficient checkpoint at degree `275`. -/
theorem coeff_discriminantPS_eq_eisensteinE12PSMod691_275 :
    (discriminantPS (ZMod 691)).coeff 275 =
      (eisensteinE12PSMod691).coeff 275 :=
  coeff_discriminantPS_eq_eisensteinE12PSMod691_through_300 275 (by norm_num)

/-- Concrete coefficient checkpoint at degree `288`. -/
theorem coeff_discriminantPS_eq_eisensteinE12PSMod691_288 :
    (discriminantPS (ZMod 691)).coeff 288 =
      (eisensteinE12PSMod691).coeff 288 :=
  coeff_discriminantPS_eq_eisensteinE12PSMod691_through_300 288 (by norm_num)

/-- Concrete coefficient checkpoint at degree `299`. -/
theorem coeff_discriminantPS_eq_eisensteinE12PSMod691_299 :
    (discriminantPS (ZMod 691)).coeff 299 =
      (eisensteinE12PSMod691).coeff 299 :=
  coeff_discriminantPS_eq_eisensteinE12PSMod691_through_300 299 (by norm_num)

/-- Concrete coefficient checkpoint at degree `300`. -/
theorem coeff_discriminantPS_eq_eisensteinE12PSMod691_300 :
    (discriminantPS (ZMod 691)).coeff 300 =
      (eisensteinE12PSMod691).coeff 300 :=
  coeff_discriminantPS_eq_eisensteinE12PSMod691_through_300 300 (by norm_num)

/-- Concrete zero-difference checkpoint at degree `260`. -/
theorem coeff_discriminantPS_sub_eisensteinE12PSMod691_eq_zero_260 :
    (discriminantPS (ZMod 691) - eisensteinE12PSMod691).coeff 260 = 0 :=
  coeff_discriminantPS_sub_eisensteinE12PSMod691_eq_zero_through_300 260 (by norm_num)

/-- Concrete zero-difference checkpoint at degree `275`. -/
theorem coeff_discriminantPS_sub_eisensteinE12PSMod691_eq_zero_275 :
    (discriminantPS (ZMod 691) - eisensteinE12PSMod691).coeff 275 = 0 :=
  coeff_discriminantPS_sub_eisensteinE12PSMod691_eq_zero_through_300 275 (by norm_num)

/-- Concrete zero-difference checkpoint at degree `288`. -/
theorem coeff_discriminantPS_sub_eisensteinE12PSMod691_eq_zero_288 :
    (discriminantPS (ZMod 691) - eisensteinE12PSMod691).coeff 288 = 0 :=
  coeff_discriminantPS_sub_eisensteinE12PSMod691_eq_zero_through_300 288 (by norm_num)

/-- Concrete zero-difference checkpoint at degree `299`. -/
theorem coeff_discriminantPS_sub_eisensteinE12PSMod691_eq_zero_299 :
    (discriminantPS (ZMod 691) - eisensteinE12PSMod691).coeff 299 = 0 :=
  coeff_discriminantPS_sub_eisensteinE12PSMod691_eq_zero_through_300 299 (by norm_num)

/-- Concrete zero-difference checkpoint at degree `300`. -/
theorem coeff_discriminantPS_sub_eisensteinE12PSMod691_eq_zero_300 :
    (discriminantPS (ZMod 691) - eisensteinE12PSMod691).coeff 300 = 0 :=
  coeff_discriminantPS_sub_eisensteinE12PSMod691_eq_zero_through_300 300 (by norm_num)

/-- Concrete reverse-difference checkpoint: `σ₁₁(260)-τ(260)=0 (mod 691)`. -/
theorem sigma11_sub_ramanujanTau_mod_691_eq_zero_260 :
    (sigma11 260 : ZMod 691) - (ramanujanTau ℤ 260 : ZMod 691) = 0 :=
  sigma11_sub_ramanujanTau_mod_691_eq_zero_through_300 260 (by norm_num)

/-- Concrete reverse-difference checkpoint: `σ₁₁(275)-τ(275)=0 (mod 691)`. -/
theorem sigma11_sub_ramanujanTau_mod_691_eq_zero_275 :
    (sigma11 275 : ZMod 691) - (ramanujanTau ℤ 275 : ZMod 691) = 0 :=
  sigma11_sub_ramanujanTau_mod_691_eq_zero_through_300 275 (by norm_num)

/-- Concrete reverse-difference checkpoint: `σ₁₁(288)-τ(288)=0 (mod 691)`. -/
theorem sigma11_sub_ramanujanTau_mod_691_eq_zero_288 :
    (sigma11 288 : ZMod 691) - (ramanujanTau ℤ 288 : ZMod 691) = 0 :=
  sigma11_sub_ramanujanTau_mod_691_eq_zero_through_300 288 (by norm_num)

/-- Concrete reverse-difference checkpoint: `σ₁₁(299)-τ(299)=0 (mod 691)`. -/
theorem sigma11_sub_ramanujanTau_mod_691_eq_zero_299 :
    (sigma11 299 : ZMod 691) - (ramanujanTau ℤ 299 : ZMod 691) = 0 :=
  sigma11_sub_ramanujanTau_mod_691_eq_zero_through_300 299 (by norm_num)

/-- Concrete reverse-difference checkpoint: `σ₁₁(300)-τ(300)=0 (mod 691)`. -/
theorem sigma11_sub_ramanujanTau_mod_691_eq_zero_300 :
    (sigma11 300 : ZMod 691) - (ramanujanTau ℤ 300 : ZMod 691) = 0 :=
  sigma11_sub_ramanujanTau_mod_691_eq_zero_through_300 300 (by norm_num)

/-- Concrete reverse zero-difference coefficient checkpoint at degree `260`. -/
theorem coeff_eisensteinE12PSMod691_sub_discriminantPS_eq_zero_260 :
    (eisensteinE12PSMod691 - discriminantPS (ZMod 691)).coeff 260 = 0 :=
  coeff_eisensteinE12PSMod691_sub_discriminantPS_eq_zero_through_300 260 (by norm_num)

/-- Concrete reverse zero-difference coefficient checkpoint at degree `275`. -/
theorem coeff_eisensteinE12PSMod691_sub_discriminantPS_eq_zero_275 :
    (eisensteinE12PSMod691 - discriminantPS (ZMod 691)).coeff 275 = 0 :=
  coeff_eisensteinE12PSMod691_sub_discriminantPS_eq_zero_through_300 275 (by norm_num)

/-- Concrete reverse zero-difference coefficient checkpoint at degree `288`. -/
theorem coeff_eisensteinE12PSMod691_sub_discriminantPS_eq_zero_288 :
    (eisensteinE12PSMod691 - discriminantPS (ZMod 691)).coeff 288 = 0 :=
  coeff_eisensteinE12PSMod691_sub_discriminantPS_eq_zero_through_300 288 (by norm_num)

/-- Concrete reverse zero-difference coefficient checkpoint at degree `299`. -/
theorem coeff_eisensteinE12PSMod691_sub_discriminantPS_eq_zero_299 :
    (eisensteinE12PSMod691 - discriminantPS (ZMod 691)).coeff 299 = 0 :=
  coeff_eisensteinE12PSMod691_sub_discriminantPS_eq_zero_through_300 299 (by norm_num)

/-- Concrete reverse zero-difference coefficient checkpoint at degree `300`. -/
theorem coeff_eisensteinE12PSMod691_sub_discriminantPS_eq_zero_300 :
    (eisensteinE12PSMod691 - discriminantPS (ZMod 691)).coeff 300 = 0 :=
  coeff_eisensteinE12PSMod691_sub_discriminantPS_eq_zero_through_300 300 (by norm_num)

/-- Coefficients `1..200` of the finite mod-691 congruence are nonzero when
checked on the reduced `sigma11` side. -/
def sigma11Mod691NonzeroThrough200Check : Bool :=
  (List.range 200).all fun i =>
    decide (sigma11Mod691 (i + 1) ≠ 0)

set_option maxHeartbeats 4000000 in
theorem sigma11Mod691NonzeroThrough200Check_true :
    sigma11Mod691NonzeroThrough200Check = true := by
  native_decide

/-- `σ₁₁(n)` is nonzero modulo 691 for `1 ≤ n ≤ 200`. -/
theorem sigma11_mod_691_ne_zero_through_200
    (n : Nat) (hn0 : 1 ≤ n) (hn200 : n ≤ 200) :
    (sigma11 n : ZMod 691) ≠ 0 := by
  cases n with
  | zero => omega
  | succ m =>
      have hm : m < 200 := by omega
      have hall := List.all_eq_true.mp sigma11Mod691NonzeroThrough200Check_true
      have hmrange : m ∈ List.range 200 := List.mem_range.mpr hm
      have hmtrue := hall m hmrange
      simp [sigma11Mod691_eq] at hmtrue
      exact hmtrue

/-- Therefore the reduced tau value is nonzero for `1 ≤ n ≤ 200`. -/
theorem ramanujanTau_mod_691_ne_zero_through_200
    (n : Nat) (hn0 : 1 ≤ n) (hn200 : n ≤ 200) :
    (ramanujanTau ℤ n : ZMod 691) ≠ 0 := by
  intro hzero
  have hsigma := sigma11_mod_691_ne_zero_through_200 n hn0 hn200
  exact hsigma (by
    rw [← ramanujanTau_congr_sigma11_mod_691_through_200 n hn200, hzero])

/-- Nonzero coefficients of the local reduced Eisenstein `E_12` series through
degree `200`, excluding the constant term. -/
theorem coeff_eisensteinE12PSMod691_ne_zero_through_200
    (n : Nat) (hn0 : 1 ≤ n) (hn200 : n ≤ 200) :
    eisensteinE12PSMod691.coeff n ≠ 0 := by
  rw [coeff_eisensteinE12PSMod691]
  exact sigma11_mod_691_ne_zero_through_200 n hn0 hn200

/-- Nonzero coefficients of `discriminantPS (ZMod 691)` through degree `200`,
excluding the constant term. -/
theorem coeff_discriminantPS_mod_691_ne_zero_through_200
    (n : Nat) (hn0 : 1 ≤ n) (hn200 : n ≤ 200) :
    (discriminantPS (ZMod 691)).coeff n ≠ 0 := by
  change ramanujanTau (ZMod 691) n ≠ 0
  rw [← PartIV.Ch20.cast_ramanujanTau_int (ZMod 691) n]
  exact ramanujanTau_mod_691_ne_zero_through_200 n hn0 hn200

/-- Coefficients `1..300` of the reduced `sigma11` side are nonzero modulo
`691`. -/
def sigma11Mod691NonzeroThrough300Check : Bool :=
  (List.range 300).all fun i =>
    decide (sigma11Mod691 (i + 1) ≠ 0)

set_option maxHeartbeats 6000000 in
theorem sigma11Mod691NonzeroThrough300Check_true :
    sigma11Mod691NonzeroThrough300Check = true := by
  native_decide

/-- `σ₁₁(n)` is nonzero modulo 691 for `1 ≤ n ≤ 300`. -/
theorem sigma11_mod_691_ne_zero_through_300
    (n : Nat) (hn0 : 1 ≤ n) (hn300 : n ≤ 300) :
    (sigma11 n : ZMod 691) ≠ 0 := by
  cases n with
  | zero => omega
  | succ m =>
      have hm : m < 300 := by omega
      have hall := List.all_eq_true.mp sigma11Mod691NonzeroThrough300Check_true
      have hmrange : m ∈ List.range 300 := List.mem_range.mpr hm
      have hmtrue := hall m hmrange
      simp [sigma11Mod691_eq] at hmtrue
      exact hmtrue

/-- Strict-bound nonvanishing form for `σ₁₁(n) mod 691`, excluding `n = 0`. -/
theorem sigma11_mod_691_ne_zero_lt_301
    (n : Nat) (hn0 : 0 < n) (hn301 : n < 301) :
    (sigma11 n : ZMod 691) ≠ 0 :=
  sigma11_mod_691_ne_zero_through_300 n (by omega) (by omega)

/-- Complement-bound nonvanishing form for `σ₁₁(n) mod 691`, excluding
`n = 0`. -/
theorem sigma11_mod_691_ne_zero_of_not_301_le
    {n : Nat} (hn0 : 0 < n) (hn301 : ¬ 301 ≤ n) :
    (sigma11 n : ZMod 691) ≠ 0 :=
  sigma11_mod_691_ne_zero_through_300 n (by omega) (by omega)

/-- Concrete nonvanishing checkpoint: `σ₁₁(201) ≠ 0 (mod 691)`. -/
theorem sigma11_mod_691_ne_zero_201 :
    (sigma11 201 : ZMod 691) ≠ 0 :=
  sigma11_mod_691_ne_zero_through_300 201 (by norm_num) (by norm_num)

/-- Concrete nonvanishing checkpoint: `σ₁₁(225) ≠ 0 (mod 691)`. -/
theorem sigma11_mod_691_ne_zero_225 :
    (sigma11 225 : ZMod 691) ≠ 0 :=
  sigma11_mod_691_ne_zero_through_300 225 (by norm_num) (by norm_num)

/-- Concrete nonvanishing checkpoint: `σ₁₁(250) ≠ 0 (mod 691)`. -/
theorem sigma11_mod_691_ne_zero_250 :
    (sigma11 250 : ZMod 691) ≠ 0 :=
  sigma11_mod_691_ne_zero_through_300 250 (by norm_num) (by norm_num)

/-- Concrete nonvanishing checkpoint: `σ₁₁(260) ≠ 0 (mod 691)`. -/
theorem sigma11_mod_691_ne_zero_260 :
    (sigma11 260 : ZMod 691) ≠ 0 :=
  sigma11_mod_691_ne_zero_through_300 260 (by norm_num) (by norm_num)

/-- Concrete nonvanishing checkpoint: `σ₁₁(275) ≠ 0 (mod 691)`. -/
theorem sigma11_mod_691_ne_zero_275 :
    (sigma11 275 : ZMod 691) ≠ 0 :=
  sigma11_mod_691_ne_zero_through_300 275 (by norm_num) (by norm_num)

/-- Concrete nonvanishing checkpoint: `σ₁₁(288) ≠ 0 (mod 691)`. -/
theorem sigma11_mod_691_ne_zero_288 :
    (sigma11 288 : ZMod 691) ≠ 0 :=
  sigma11_mod_691_ne_zero_through_300 288 (by norm_num) (by norm_num)

/-- Concrete nonvanishing checkpoint: `σ₁₁(299) ≠ 0 (mod 691)`. -/
theorem sigma11_mod_691_ne_zero_299 :
    (sigma11 299 : ZMod 691) ≠ 0 :=
  sigma11_mod_691_ne_zero_through_300 299 (by norm_num) (by norm_num)

/-- Concrete nonvanishing checkpoint: `σ₁₁(300) ≠ 0 (mod 691)`. -/
theorem sigma11_mod_691_ne_zero_300 :
    (sigma11 300 : ZMod 691) ≠ 0 :=
  sigma11_mod_691_ne_zero_through_300 300 (by norm_num) (by norm_num)

/-- The reduced tau value is nonzero for `1 ≤ n ≤ 300`. -/
theorem ramanujanTau_mod_691_ne_zero_through_300
    (n : Nat) (hn0 : 1 ≤ n) (hn300 : n ≤ 300) :
    (ramanujanTau ℤ n : ZMod 691) ≠ 0 := by
  intro hzero
  have hsigma := sigma11_mod_691_ne_zero_through_300 n hn0 hn300
  exact hsigma (by
    rw [← ramanujanTau_congr_sigma11_mod_691_through_300 n hn300, hzero])

/-- Strict-bound nonvanishing form for `τ(n) mod 691`, excluding `n = 0`. -/
theorem ramanujanTau_mod_691_ne_zero_lt_301
    (n : Nat) (hn0 : 0 < n) (hn301 : n < 301) :
    (ramanujanTau ℤ n : ZMod 691) ≠ 0 :=
  ramanujanTau_mod_691_ne_zero_through_300 n (by omega) (by omega)

/-- Complement-bound nonvanishing form for `τ(n) mod 691`, excluding
`n = 0`. -/
theorem ramanujanTau_mod_691_ne_zero_of_not_301_le
    {n : Nat} (hn0 : 0 < n) (hn301 : ¬ 301 ≤ n) :
    (ramanujanTau ℤ n : ZMod 691) ≠ 0 :=
  ramanujanTau_mod_691_ne_zero_through_300 n (by omega) (by omega)

/-- Concrete nonvanishing checkpoint: `τ(201) ≠ 0 (mod 691)`. -/
theorem ramanujanTau_mod_691_ne_zero_201 :
    (ramanujanTau ℤ 201 : ZMod 691) ≠ 0 :=
  ramanujanTau_mod_691_ne_zero_through_300 201 (by norm_num) (by norm_num)

/-- Concrete nonvanishing checkpoint: `τ(225) ≠ 0 (mod 691)`. -/
theorem ramanujanTau_mod_691_ne_zero_225 :
    (ramanujanTau ℤ 225 : ZMod 691) ≠ 0 :=
  ramanujanTau_mod_691_ne_zero_through_300 225 (by norm_num) (by norm_num)

/-- Concrete nonvanishing checkpoint: `τ(250) ≠ 0 (mod 691)`. -/
theorem ramanujanTau_mod_691_ne_zero_250 :
    (ramanujanTau ℤ 250 : ZMod 691) ≠ 0 :=
  ramanujanTau_mod_691_ne_zero_through_300 250 (by norm_num) (by norm_num)

/-- Concrete nonvanishing checkpoint: `τ(260) ≠ 0 (mod 691)`. -/
theorem ramanujanTau_mod_691_ne_zero_260 :
    (ramanujanTau ℤ 260 : ZMod 691) ≠ 0 :=
  ramanujanTau_mod_691_ne_zero_through_300 260 (by norm_num) (by norm_num)

/-- Concrete nonvanishing checkpoint: `τ(275) ≠ 0 (mod 691)`. -/
theorem ramanujanTau_mod_691_ne_zero_275 :
    (ramanujanTau ℤ 275 : ZMod 691) ≠ 0 :=
  ramanujanTau_mod_691_ne_zero_through_300 275 (by norm_num) (by norm_num)

/-- Concrete nonvanishing checkpoint: `τ(288) ≠ 0 (mod 691)`. -/
theorem ramanujanTau_mod_691_ne_zero_288 :
    (ramanujanTau ℤ 288 : ZMod 691) ≠ 0 :=
  ramanujanTau_mod_691_ne_zero_through_300 288 (by norm_num) (by norm_num)

/-- Concrete nonvanishing checkpoint: `τ(299) ≠ 0 (mod 691)`. -/
theorem ramanujanTau_mod_691_ne_zero_299 :
    (ramanujanTau ℤ 299 : ZMod 691) ≠ 0 :=
  ramanujanTau_mod_691_ne_zero_through_300 299 (by norm_num) (by norm_num)

/-- Concrete nonvanishing checkpoint: `τ(300) ≠ 0 (mod 691)`. -/
theorem ramanujanTau_mod_691_ne_zero_300 :
    (ramanujanTau ℤ 300 : ZMod 691) ≠ 0 :=
  ramanujanTau_mod_691_ne_zero_through_300 300 (by norm_num) (by norm_num)

/-- Integer nonvanishing through `n = 300`, certified by reduction modulo
`691`. -/
theorem ramanujanTau_ne_zero_through_300
    (n : Nat) (hn0 : 1 ≤ n) (hn300 : n ≤ 300) :
    ramanujanTau ℤ n ≠ 0 := by
  intro hzero
  exact ramanujanTau_mod_691_ne_zero_through_300 n hn0 hn300 (by
    rw [hzero]
    norm_num)

/-- Strict-bound integer nonvanishing through `n < 301`, excluding `n = 0`. -/
theorem ramanujanTau_ne_zero_lt_301
    (n : Nat) (hn0 : 0 < n) (hn301 : n < 301) :
    ramanujanTau ℤ n ≠ 0 :=
  ramanujanTau_ne_zero_through_300 n (by omega) (by omega)

/-- Complement-bound integer nonvanishing through `n < 301`, excluding
`n = 0`. -/
theorem ramanujanTau_ne_zero_of_not_301_le
    {n : Nat} (hn0 : 0 < n) (hn301 : ¬ 301 ≤ n) :
    ramanujanTau ℤ n ≠ 0 :=
  ramanujanTau_ne_zero_through_300 n (by omega) (by omega)

/-- Integer nonvanishing checkpoint certified by reduction modulo `691`:
`τ(201) ≠ 0`. -/
theorem ramanujanTau_ne_zero_201 :
    ramanujanTau ℤ 201 ≠ 0 := by
  exact ramanujanTau_ne_zero_through_300 201 (by norm_num) (by norm_num)

/-- Integer nonvanishing checkpoint certified by reduction modulo `691`:
`τ(225) ≠ 0`. -/
theorem ramanujanTau_ne_zero_225 :
    ramanujanTau ℤ 225 ≠ 0 := by
  exact ramanujanTau_ne_zero_through_300 225 (by norm_num) (by norm_num)

/-- Integer nonvanishing checkpoint certified by reduction modulo `691`:
`τ(250) ≠ 0`. -/
theorem ramanujanTau_ne_zero_250 :
    ramanujanTau ℤ 250 ≠ 0 := by
  exact ramanujanTau_ne_zero_through_300 250 (by norm_num) (by norm_num)

/-- Integer nonvanishing checkpoint certified by reduction modulo `691`:
`τ(260) ≠ 0`. -/
theorem ramanujanTau_ne_zero_260 :
    ramanujanTau ℤ 260 ≠ 0 := by
  exact ramanujanTau_ne_zero_through_300 260 (by norm_num) (by norm_num)

/-- Integer nonvanishing checkpoint certified by reduction modulo `691`:
`τ(275) ≠ 0`. -/
theorem ramanujanTau_ne_zero_275 :
    ramanujanTau ℤ 275 ≠ 0 := by
  exact ramanujanTau_ne_zero_through_300 275 (by norm_num) (by norm_num)

/-- Integer nonvanishing checkpoint certified by reduction modulo `691`:
`τ(288) ≠ 0`. -/
theorem ramanujanTau_ne_zero_288 :
    ramanujanTau ℤ 288 ≠ 0 := by
  exact ramanujanTau_ne_zero_through_300 288 (by norm_num) (by norm_num)

/-- Integer nonvanishing checkpoint certified by reduction modulo `691`:
`τ(299) ≠ 0`. -/
theorem ramanujanTau_ne_zero_299 :
    ramanujanTau ℤ 299 ≠ 0 := by
  exact ramanujanTau_ne_zero_through_300 299 (by norm_num) (by norm_num)

/-- Integer nonvanishing checkpoint certified by reduction modulo `691`:
`τ(300) ≠ 0`. -/
theorem ramanujanTau_ne_zero_300 :
    ramanujanTau ℤ 300 ≠ 0 := by
  exact ramanujanTau_ne_zero_through_300 300 (by norm_num) (by norm_num)

/-- Nonzero coefficients of the local reduced Eisenstein `E_12` series through
degree `300`, excluding the constant term. -/
theorem coeff_eisensteinE12PSMod691_ne_zero_through_300
    (n : Nat) (hn0 : 1 ≤ n) (hn300 : n ≤ 300) :
    eisensteinE12PSMod691.coeff n ≠ 0 := by
  rw [coeff_eisensteinE12PSMod691]
  exact sigma11_mod_691_ne_zero_through_300 n hn0 hn300

/-- Strict-bound nonzero coefficients of the local reduced Eisenstein `E_12`
series, excluding the constant term. -/
theorem coeff_eisensteinE12PSMod691_ne_zero_lt_301
    (n : Nat) (hn0 : 0 < n) (hn301 : n < 301) :
    eisensteinE12PSMod691.coeff n ≠ 0 :=
  coeff_eisensteinE12PSMod691_ne_zero_through_300 n (by omega) (by omega)

/-- Complement-bound nonzero coefficients of the local reduced Eisenstein
`E_12` series, excluding the constant term. -/
theorem coeff_eisensteinE12PSMod691_ne_zero_of_not_301_le
    {n : Nat} (hn0 : 0 < n) (hn301 : ¬ 301 ≤ n) :
    eisensteinE12PSMod691.coeff n ≠ 0 :=
  coeff_eisensteinE12PSMod691_ne_zero_through_300 n (by omega) (by omega)

/-- Concrete nonzero reduced Eisenstein coefficient at degree `201`. -/
theorem coeff_eisensteinE12PSMod691_ne_zero_201 :
    eisensteinE12PSMod691.coeff 201 ≠ 0 :=
  coeff_eisensteinE12PSMod691_ne_zero_through_300 201 (by norm_num) (by norm_num)

/-- Concrete nonzero reduced Eisenstein coefficient at degree `225`. -/
theorem coeff_eisensteinE12PSMod691_ne_zero_225 :
    eisensteinE12PSMod691.coeff 225 ≠ 0 :=
  coeff_eisensteinE12PSMod691_ne_zero_through_300 225 (by norm_num) (by norm_num)

/-- Concrete nonzero reduced Eisenstein coefficient at degree `250`. -/
theorem coeff_eisensteinE12PSMod691_ne_zero_250 :
    eisensteinE12PSMod691.coeff 250 ≠ 0 :=
  coeff_eisensteinE12PSMod691_ne_zero_through_300 250 (by norm_num) (by norm_num)

/-- Concrete nonzero reduced Eisenstein coefficient at degree `260`. -/
theorem coeff_eisensteinE12PSMod691_ne_zero_260 :
    eisensteinE12PSMod691.coeff 260 ≠ 0 :=
  coeff_eisensteinE12PSMod691_ne_zero_through_300 260 (by norm_num) (by norm_num)

/-- Concrete nonzero reduced Eisenstein coefficient at degree `275`. -/
theorem coeff_eisensteinE12PSMod691_ne_zero_275 :
    eisensteinE12PSMod691.coeff 275 ≠ 0 :=
  coeff_eisensteinE12PSMod691_ne_zero_through_300 275 (by norm_num) (by norm_num)

/-- Concrete nonzero reduced Eisenstein coefficient at degree `288`. -/
theorem coeff_eisensteinE12PSMod691_ne_zero_288 :
    eisensteinE12PSMod691.coeff 288 ≠ 0 :=
  coeff_eisensteinE12PSMod691_ne_zero_through_300 288 (by norm_num) (by norm_num)

/-- Concrete nonzero reduced Eisenstein coefficient at degree `299`. -/
theorem coeff_eisensteinE12PSMod691_ne_zero_299 :
    eisensteinE12PSMod691.coeff 299 ≠ 0 :=
  coeff_eisensteinE12PSMod691_ne_zero_through_300 299 (by norm_num) (by norm_num)

/-- Concrete nonzero reduced Eisenstein coefficient at degree `300`. -/
theorem coeff_eisensteinE12PSMod691_ne_zero_300 :
    eisensteinE12PSMod691.coeff 300 ≠ 0 :=
  coeff_eisensteinE12PSMod691_ne_zero_through_300 300 (by norm_num) (by norm_num)

/-- Nonzero coefficients of `discriminantPS (ZMod 691)` through degree `300`,
excluding the constant term. -/
theorem coeff_discriminantPS_mod_691_ne_zero_through_300
    (n : Nat) (hn0 : 1 ≤ n) (hn300 : n ≤ 300) :
    (discriminantPS (ZMod 691)).coeff n ≠ 0 := by
  change ramanujanTau (ZMod 691) n ≠ 0
  rw [← PartIV.Ch20.cast_ramanujanTau_int (ZMod 691) n]
  exact ramanujanTau_mod_691_ne_zero_through_300 n hn0 hn300

/-- Strict-bound nonzero coefficients of `discriminantPS (ZMod 691)`,
excluding the constant term. -/
theorem coeff_discriminantPS_mod_691_ne_zero_lt_301
    (n : Nat) (hn0 : 0 < n) (hn301 : n < 301) :
    (discriminantPS (ZMod 691)).coeff n ≠ 0 :=
  coeff_discriminantPS_mod_691_ne_zero_through_300 n (by omega) (by omega)

/-- Complement-bound nonzero coefficients of `discriminantPS (ZMod 691)`,
excluding the constant term. -/
theorem coeff_discriminantPS_mod_691_ne_zero_of_not_301_le
    {n : Nat} (hn0 : 0 < n) (hn301 : ¬ 301 ≤ n) :
    (discriminantPS (ZMod 691)).coeff n ≠ 0 :=
  coeff_discriminantPS_mod_691_ne_zero_through_300 n (by omega) (by omega)

/-- Concrete nonzero discriminant coefficient at degree `201`. -/
theorem coeff_discriminantPS_mod_691_ne_zero_201 :
    (discriminantPS (ZMod 691)).coeff 201 ≠ 0 :=
  coeff_discriminantPS_mod_691_ne_zero_through_300 201 (by norm_num) (by norm_num)

/-- Concrete nonzero discriminant coefficient at degree `225`. -/
theorem coeff_discriminantPS_mod_691_ne_zero_225 :
    (discriminantPS (ZMod 691)).coeff 225 ≠ 0 :=
  coeff_discriminantPS_mod_691_ne_zero_through_300 225 (by norm_num) (by norm_num)

/-- Concrete nonzero discriminant coefficient at degree `250`. -/
theorem coeff_discriminantPS_mod_691_ne_zero_250 :
    (discriminantPS (ZMod 691)).coeff 250 ≠ 0 :=
  coeff_discriminantPS_mod_691_ne_zero_through_300 250 (by norm_num) (by norm_num)

/-- Concrete nonzero discriminant coefficient at degree `260`. -/
theorem coeff_discriminantPS_mod_691_ne_zero_260 :
    (discriminantPS (ZMod 691)).coeff 260 ≠ 0 :=
  coeff_discriminantPS_mod_691_ne_zero_through_300 260 (by norm_num) (by norm_num)

/-- Concrete nonzero discriminant coefficient at degree `275`. -/
theorem coeff_discriminantPS_mod_691_ne_zero_275 :
    (discriminantPS (ZMod 691)).coeff 275 ≠ 0 :=
  coeff_discriminantPS_mod_691_ne_zero_through_300 275 (by norm_num) (by norm_num)

/-- Concrete nonzero discriminant coefficient at degree `288`. -/
theorem coeff_discriminantPS_mod_691_ne_zero_288 :
    (discriminantPS (ZMod 691)).coeff 288 ≠ 0 :=
  coeff_discriminantPS_mod_691_ne_zero_through_300 288 (by norm_num) (by norm_num)

/-- Concrete nonzero discriminant coefficient at degree `299`. -/
theorem coeff_discriminantPS_mod_691_ne_zero_299 :
    (discriminantPS (ZMod 691)).coeff 299 ≠ 0 :=
  coeff_discriminantPS_mod_691_ne_zero_through_300 299 (by norm_num) (by norm_num)

/-- Concrete nonzero discriminant coefficient at degree `300`. -/
theorem coeff_discriminantPS_mod_691_ne_zero_300 :
    (discriminantPS (ZMod 691)).coeff 300 ≠ 0 :=
  coeff_discriminantPS_mod_691_ne_zero_through_300 300 (by norm_num) (by norm_num)

/-- Nonzero integer coefficients of `discriminantPS ℤ` through degree `300`,
excluding the constant term. -/
theorem coeff_discriminantPS_int_ne_zero_through_300
    (n : Nat) (hn0 : 1 ≤ n) (hn300 : n ≤ 300) :
    (discriminantPS ℤ).coeff n ≠ 0 := by
  change ramanujanTau ℤ n ≠ 0
  exact ramanujanTau_ne_zero_through_300 n hn0 hn300

/-- Strict-bound nonzero integer coefficients of `discriminantPS ℤ`, excluding
the constant term. -/
theorem coeff_discriminantPS_int_ne_zero_lt_301
    (n : Nat) (hn0 : 0 < n) (hn301 : n < 301) :
    (discriminantPS ℤ).coeff n ≠ 0 :=
  coeff_discriminantPS_int_ne_zero_through_300 n (by omega) (by omega)

/-- Complement-bound nonzero integer coefficients of `discriminantPS ℤ`,
excluding the constant term. -/
theorem coeff_discriminantPS_int_ne_zero_of_not_301_le
    {n : Nat} (hn0 : 0 < n) (hn301 : ¬ 301 ≤ n) :
    (discriminantPS ℤ).coeff n ≠ 0 :=
  coeff_discriminantPS_int_ne_zero_through_300 n (by omega) (by omega)

/-- Concrete nonzero integer discriminant coefficient at degree `201`. -/
theorem coeff_discriminantPS_int_ne_zero_201 :
    (discriminantPS ℤ).coeff 201 ≠ 0 :=
  coeff_discriminantPS_int_ne_zero_through_300 201 (by norm_num) (by norm_num)

/-- Concrete nonzero integer discriminant coefficient at degree `225`. -/
theorem coeff_discriminantPS_int_ne_zero_225 :
    (discriminantPS ℤ).coeff 225 ≠ 0 :=
  coeff_discriminantPS_int_ne_zero_through_300 225 (by norm_num) (by norm_num)

/-- Concrete nonzero integer discriminant coefficient at degree `250`. -/
theorem coeff_discriminantPS_int_ne_zero_250 :
    (discriminantPS ℤ).coeff 250 ≠ 0 :=
  coeff_discriminantPS_int_ne_zero_through_300 250 (by norm_num) (by norm_num)

/-- Concrete nonzero integer discriminant coefficient at degree `260`. -/
theorem coeff_discriminantPS_int_ne_zero_260 :
    (discriminantPS ℤ).coeff 260 ≠ 0 :=
  coeff_discriminantPS_int_ne_zero_through_300 260 (by norm_num) (by norm_num)

/-- Concrete nonzero integer discriminant coefficient at degree `275`. -/
theorem coeff_discriminantPS_int_ne_zero_275 :
    (discriminantPS ℤ).coeff 275 ≠ 0 :=
  coeff_discriminantPS_int_ne_zero_through_300 275 (by norm_num) (by norm_num)

/-- Concrete nonzero integer discriminant coefficient at degree `288`. -/
theorem coeff_discriminantPS_int_ne_zero_288 :
    (discriminantPS ℤ).coeff 288 ≠ 0 :=
  coeff_discriminantPS_int_ne_zero_through_300 288 (by norm_num) (by norm_num)

/-- Concrete nonzero integer discriminant coefficient at degree `299`. -/
theorem coeff_discriminantPS_int_ne_zero_299 :
    (discriminantPS ℤ).coeff 299 ≠ 0 :=
  coeff_discriminantPS_int_ne_zero_through_300 299 (by norm_num) (by norm_num)

/-- Concrete nonzero integer discriminant coefficient at degree `300`. -/
theorem coeff_discriminantPS_int_ne_zero_300 :
    (discriminantPS ℤ).coeff 300 ≠ 0 :=
  coeff_discriminantPS_int_ne_zero_through_300 300 (by norm_num) (by norm_num)

/-- There is no zero value of `σ₁₁(n)` modulo `691` for `1 ≤ n ≤ 300`. -/
theorem not_exists_le_300_sigma11_mod_691_eq_zero :
    ¬ ∃ n : Nat, 1 ≤ n ∧ n ≤ 300 ∧ (sigma11 n : ZMod 691) = 0 := by
  rintro ⟨n, hn0, hn300, hzero⟩
  exact sigma11_mod_691_ne_zero_through_300 n hn0 hn300 hzero

/-- Strict-bound form: there is no zero value of `σ₁₁(n)` modulo `691` for
`0 < n < 301`. -/
theorem not_exists_lt_301_sigma11_mod_691_eq_zero :
    ¬ ∃ n : Nat, 0 < n ∧ n < 301 ∧ (sigma11 n : ZMod 691) = 0 := by
  rintro ⟨n, hn0, hn301, hzero⟩
  exact sigma11_mod_691_ne_zero_lt_301 n hn0 hn301 hzero

/-- There is no zero value of `τ(n)` modulo `691` for `1 ≤ n ≤ 300`. -/
theorem not_exists_le_300_ramanujanTau_mod_691_eq_zero :
    ¬ ∃ n : Nat, 1 ≤ n ∧ n ≤ 300 ∧
      (ramanujanTau ℤ n : ZMod 691) = 0 := by
  rintro ⟨n, hn0, hn300, hzero⟩
  exact ramanujanTau_mod_691_ne_zero_through_300 n hn0 hn300 hzero

/-- Strict-bound form: there is no zero value of `τ(n)` modulo `691` for
`0 < n < 301`. -/
theorem not_exists_lt_301_ramanujanTau_mod_691_eq_zero :
    ¬ ∃ n : Nat, 0 < n ∧ n < 301 ∧
      (ramanujanTau ℤ n : ZMod 691) = 0 := by
  rintro ⟨n, hn0, hn301, hzero⟩
  exact ramanujanTau_mod_691_ne_zero_lt_301 n hn0 hn301 hzero

/-- There is no integer zero value of `τ(n)` for `1 ≤ n ≤ 300`. -/
theorem not_exists_le_300_ramanujanTau_eq_zero :
    ¬ ∃ n : Nat, 1 ≤ n ∧ n ≤ 300 ∧ ramanujanTau ℤ n = 0 := by
  rintro ⟨n, hn0, hn300, hzero⟩
  exact ramanujanTau_ne_zero_through_300 n hn0 hn300 hzero

/-- Strict-bound form: there is no integer zero value of `τ(n)` for
`0 < n < 301`. -/
theorem not_exists_lt_301_ramanujanTau_eq_zero :
    ¬ ∃ n : Nat, 0 < n ∧ n < 301 ∧ ramanujanTau ℤ n = 0 := by
  rintro ⟨n, hn0, hn301, hzero⟩
  exact ramanujanTau_ne_zero_lt_301 n hn0 hn301 hzero

/-- The local reduced Eisenstein `E_12` series has no zero coefficient in
degrees `1..300`. -/
theorem not_exists_le_300_coeff_eisensteinE12PSMod691_eq_zero :
    ¬ ∃ n : Nat, 1 ≤ n ∧ n ≤ 300 ∧ eisensteinE12PSMod691.coeff n = 0 := by
  rintro ⟨n, hn0, hn300, hzero⟩
  exact coeff_eisensteinE12PSMod691_ne_zero_through_300 n hn0 hn300 hzero

/-- Strict-bound form: the local reduced Eisenstein `E_12` series has no zero
coefficient in degrees `0 < n < 301`. -/
theorem not_exists_lt_301_coeff_eisensteinE12PSMod691_eq_zero :
    ¬ ∃ n : Nat, 0 < n ∧ n < 301 ∧ eisensteinE12PSMod691.coeff n = 0 := by
  rintro ⟨n, hn0, hn301, hzero⟩
  exact coeff_eisensteinE12PSMod691_ne_zero_lt_301 n hn0 hn301 hzero

/-- The reduced discriminant series has no zero coefficient in degrees
`1..300`. -/
theorem not_exists_le_300_coeff_discriminantPS_mod_691_eq_zero :
    ¬ ∃ n : Nat, 1 ≤ n ∧ n ≤ 300 ∧
      (discriminantPS (ZMod 691)).coeff n = 0 := by
  rintro ⟨n, hn0, hn300, hzero⟩
  exact coeff_discriminantPS_mod_691_ne_zero_through_300 n hn0 hn300 hzero

/-- Strict-bound form: the reduced discriminant series has no zero coefficient
in degrees `0 < n < 301`. -/
theorem not_exists_lt_301_coeff_discriminantPS_mod_691_eq_zero :
    ¬ ∃ n : Nat, 0 < n ∧ n < 301 ∧
      (discriminantPS (ZMod 691)).coeff n = 0 := by
  rintro ⟨n, hn0, hn301, hzero⟩
  exact coeff_discriminantPS_mod_691_ne_zero_lt_301 n hn0 hn301 hzero

/-- The integer discriminant series has no zero coefficient in degrees
`1..300`. -/
theorem not_exists_le_300_coeff_discriminantPS_int_eq_zero :
    ¬ ∃ n : Nat, 1 ≤ n ∧ n ≤ 300 ∧ (discriminantPS ℤ).coeff n = 0 := by
  rintro ⟨n, hn0, hn300, hzero⟩
  exact coeff_discriminantPS_int_ne_zero_through_300 n hn0 hn300 hzero

/-- Strict-bound form: the integer discriminant series has no zero coefficient
in degrees `0 < n < 301`. -/
theorem not_exists_lt_301_coeff_discriminantPS_int_eq_zero :
    ¬ ∃ n : Nat, 0 < n ∧ n < 301 ∧ (discriminantPS ℤ).coeff n = 0 := by
  rintro ⟨n, hn0, hn301, hzero⟩
  exact coeff_discriminantPS_int_ne_zero_lt_301 n hn0 hn301 hzero

end Ch20Mod691
end Pending
end QseriesFormalization
