/-
# Chapter 10 — Bridge: Chan's Eq. (10.15) in `ℚ⟦X⟧`

This file connects the machine-verified `K = HahnSeries ℤ ℚ` identity of
`Chapter10_TwoVar` to the chapter target `chan1015IdentityStatement` of
`Chapter10_TenthOrder`, stated in `ℚ⟦X⟧ = PowerSeries ℚ`.

The whole bridge is *representation transport* along the injective ring map
`ofPSK = HahnSeries.ofPowerSeries ℤ ℚ : ℚ⟦X⟧ →+* K` (sending `X ↦ Q`).  No new
mathematics: the genuine identity content lives in `Chapter10_TwoVar`
(`chan_step1_decoupling`, `chan_eq_10_15_CTxy`).

Three transported pieces:

* `ofPSK_chan1015LHSPS`         : `ofPSK (chan1015LHSPS ℚ) = ChanQuadSum`         (B-LHS)
* `ofPSK_chan1015PentagonalPS`  : `ofPSK chan1015PentagonalPS = kP10`            (B-RHS pentagonal)
* the `(q²;q²)²`-cleared `ℚ⟦X⟧` identity, obtained from the cleared `K`-identity
  `poch_q2² · ChanQuadSum = - poch_q⁵ · kP10` by `ofPSK` injectivity, then divided
  by the unit `(q²;q²)²`.

Final theorem: `chan1015 : chan1015IdentityStatement`.
-/

import QseriesFormalization.Pending.Chapter10_TwoVar
import QseriesFormalization.Pending.Chapter10_TenthOrder

open scoped Classical
open QseriesFormalization
open QseriesFormalization.Ch10TwoVar
open QseriesFormalization.Pending.Ch10TenthOrder
open QseriesFormalization.Pending.JTPFormalPSPentagonal

namespace QseriesFormalization.Pending.Ch10Bridge

/-! ## Sign helper: `negOnePowInt R k = (-1)^k` as a `zpow` -/

/-- `negOnePowInt ℚ k` (which is `(-1)^k.natAbs`, a `Nat`-power) equals the `zpow`
`(-1 : ℚ)^k`, because `-1` is its own inverse. -/
theorem negOnePowInt_rat_eq_zpow (k : ℤ) :
    JTPFormalPSPentagonal.negOnePowInt ℚ k = (-1 : ℚ) ^ k := by
  unfold JTPFormalPSPentagonal.negOnePowInt
  rcases k with n | n
  · simp [zpow_natCast]
  · rw [zpow_negSucc, Int.natAbs_negSucc]
    rcases Nat.even_or_odd (n + 1) with he | ho
    · rw [he.neg_one_pow]; norm_num
    · rw [ho.neg_one_pow]; norm_num

/-! ## `squareWindow` capture: `m² ≤ N ⟹ m ≤ squareWindow N` -/

/-- The accumulator only grows under `Nat.max`-fold: `b ≤ t.foldl Nat.max b`. -/
theorem self_le_foldl_max : ∀ (t : List ℕ) (b : ℕ), b ≤ t.foldl Nat.max b := by
  intro t
  induction t with
  | nil => intro b; simp
  | cons a t ih =>
      intro b
      calc b ≤ Nat.max b a := Nat.le_max_left _ _
        _ ≤ t.foldl Nat.max (Nat.max b a) := ih _

/-- Any element of a `Nat` list is `≤` the running `Nat.max`-fold of the list. -/
theorem le_foldl_max (l : List ℕ) (acc : ℕ) {m : ℕ} (hm : m ∈ l) :
    m ≤ l.foldl Nat.max acc := by
  induction l generalizing acc with
  | nil => simp at hm
  | cons a t ih =>
      rcases List.mem_cons.mp hm with h | h
      · subst h
        exact (Nat.le_max_right acc m).trans (self_le_foldl_max t (Nat.max acc m))
      · exact ih (Nat.max acc a) h

/-- The defining capture property of `squareWindow`: every `m` with `m² ≤ N`
satisfies `m ≤ squareWindow N`. -/
theorem le_squareWindow {N m : ℕ} (h : m * m ≤ N) : m ≤ squareWindow N := by
  unfold squareWindow
  have hmem : m ∈ (List.range (N + 1)).filter (fun x => x * x ≤ N) := by
    rw [List.mem_filter]
    refine ⟨List.mem_range.mpr ?_, by simpa using h⟩
    rcases Nat.eq_zero_or_pos m with hm0 | hm0
    · omega
    · have : m ≤ m * m := Nat.le_mul_of_pos_left m hm0
      omega
  exact le_foldl_max _ 0 hmem

/-- Integer form: `k² ≤ (N : ℤ) ⟹ -(squareWindow N : ℤ) ≤ k ≤ (squareWindow N : ℤ)`. -/
theorem mem_squareWindow_Icc {N : ℕ} {k : ℤ} (h : k ^ 2 ≤ (N : ℤ)) :
    -(squareWindow N : ℤ) ≤ k ∧ k ≤ (squareWindow N : ℤ) := by
  have hnat : k.natAbs * k.natAbs ≤ N := by
    have hcast : ((k.natAbs * k.natAbs : ℕ) : ℤ) ≤ (N : ℤ) := by
      rw [Int.natAbs_mul_self]
      have : k * k = k ^ 2 := by ring
      rw [this]; exact h
    exact_mod_cast hcast
  have hle : (k.natAbs : ℤ) ≤ (squareWindow N : ℤ) := by exact_mod_cast le_squareWindow hnat
  have h1 : -(k.natAbs : ℤ) ≤ k := by omega
  have h2 : k ≤ (k.natAbs : ℤ) := by omega
  exact ⟨by omega, by omega⟩

/-! ## B-RHS (pentagonal): `ofPSK chan1015PentagonalPS = kP10` -/

/-- `P10 n ≥ 0` for all `n : ℤ`. -/
theorem P10_nonneg (n : ℤ) : 0 ≤ P10 n := by
  have h := two_mul_P10 n
  nlinarith [h, sq_nonneg (5 * n + 3), sq_nonneg n]

/-- `pentagonal014Exp (-n) = (P10 n).toNat`, and `P10 n ≥ 0`, so `(pentagonal014Exp (-n) : ℤ) = P10 n`.
The two parametrisations of the pentagonal exponent agree under `k ↦ -n`. -/
theorem pentagonal014Exp_neg (n : ℤ) :
    ((JTPFormalPSPentagonal.pentagonal014Exp (-n) : ℕ) : ℤ) = P10 n := by
  unfold JTPFormalPSPentagonal.pentagonal014Exp
  rw [Int.toNat_of_nonneg]
  · -- (-n)(5·(-n)-3)/2 = n(5n+3)/2 = P10 n
    show (-n) * (5 * (-n) - 3) / 2 = P10 n
    unfold P10
    congr 1
    ring
  · -- (-n)(5(-n)-3)/2 ≥ 0
    have hp := P10_nonneg n
    unfold P10 at hp
    have h : (-n) * (5 * (-n) - 3) = n * (5 * n + 3) := by ring
    rw [h]; exact hp

/-- `kP10` coefficient as an `n`-finsum of indicators. -/
theorem kP10_coeff_indicator (D : ℤ) :
    kP10.coeff D = ∑ᶠ n : ℤ, (if 3 * P10 n = D then (-1 : ℚ) ^ n else 0) := by
  rw [kP10_coeff]
  apply finsum_congr
  intro n
  rw [HahnSeries.coeff_single]
  by_cases h : 3 * P10 n = D
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun hc => h hc.symm)]

/-- `kP10` coefficient reindexed to the `pentagonal014Exp` parametrisation (`n ↦ -k`). -/
theorem kP10_coeff_pent (D : ℤ) :
    kP10.coeff D
      = ∑ᶠ k : ℤ, (if 3 * (JTPFormalPSPentagonal.pentagonal014Exp k : ℤ) = D
          then JTPFormalPSPentagonal.negOnePowInt ℚ k else 0) := by
  rw [kP10_coeff_indicator]
  rw [← finsum_comp_equiv (Equiv.neg ℤ)]
  apply finsum_congr
  intro k
  simp only [Equiv.neg_apply]
  -- term at n = -k :  if 3·P10(-k)=D then (-1)^(-k) else 0
  rw [show P10 (-k) = (JTPFormalPSPentagonal.pentagonal014Exp k : ℤ) by
        have := pentagonal014Exp_neg (-k); rw [neg_neg] at this; rw [this]]
  rw [negOne_zpow_neg, negOnePowInt_rat_eq_zpow]

/-- Capture window for `pentagonal014Exp`: if `pentagonal014Exp k = j` then
`-(j+1) ≤ k ≤ j+1`. -/
theorem pentagonal014Exp_window {j : ℕ} {k : ℤ}
    (h : JTPFormalPSPentagonal.pentagonal014Exp k = j) :
    -((j : ℤ) + 1) ≤ k ∧ k ≤ (j : ℤ) + 1 := by
  have he : (JTPFormalPSPentagonal.pentagonal014Exp k : ℤ) = (j : ℤ) := by exact_mod_cast h
  have hval : k * (5 * k - 3) / 2 = (j : ℤ) := by
    rw [← he]
    unfold JTPFormalPSPentagonal.pentagonal014Exp
    rw [Int.toNat_of_nonneg (JTPFormalPSPentagonal.pentagonal014Exp_nonneg_int k)]
  -- 2j = k(5k-3) = 5k² - 3k, so k² ≤ 2j  ⟹  |k| ≤ j+1
  have h2 : k * (5 * k - 3) = 2 * (j : ℤ) := by
    have hdvd : (2 : ℤ) ∣ k * (5 * k - 3) := by
      rcases Int.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
      · exact ⟨m * (5 * k - 3), by rw [hm]; ring⟩
      · exact ⟨k * (5 * m + 1), by rw [hm]; ring⟩
    omega
  have hk2 : k ^ 2 ≤ 2 * (j : ℤ) := by nlinarith [h2, sq_nonneg (k - 1)]
  constructor <;> nlinarith [hk2, sq_nonneg (k - 1), sq_nonneg (k + 1)]

/-- **B-RHS (pentagonal):** the pentagonal power series transports to `kP10`. -/
theorem ofPSK_chan1015PentagonalPS : ofPSK chan1015PentagonalPS = kP10 := by
  apply HahnSeries.ext
  funext D
  rw [kP10_coeff_pent]
  rcases lt_or_ge D 0 with hD | hD
  · -- D < 0 : ofPSK coeff 0, and every indicator term is 0 (3·exp ≥ 0 > D).
    rw [ofPSK_coeff_neg _ D hD]
    symm
    apply finsum_eq_zero_of_forall_eq_zero
    intro k
    have : (0 : ℤ) ≤ 3 * (JTPFormalPSPentagonal.pentagonal014Exp k : ℤ) := by positivity
    rw [if_neg (by omega)]
  · -- D = (m : ℕ).
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hD
    rw [ofPSK_coeff_nat]
    unfold chan1015PentagonalPS
    rw [PowerSeries.coeff_expand]
    by_cases h3 : 3 ∣ m
    · -- m = 3 j
      obtain ⟨j, rfl⟩ := h3
      rw [if_pos ⟨j, rfl⟩, Nat.mul_div_cancel_left _ (by norm_num)]
      rw [coeff_pentagonal014SeriesPS]
      unfold JTPFormalPSPentagonal.pentagonal014Coeff
      -- finsum over k of (if 3·exp k = 3j then (-1)^k else 0)  =  Finset.Icc sum
      rw [show (∑ᶠ k : ℤ, (if 3 * (JTPFormalPSPentagonal.pentagonal014Exp k : ℤ) = (3 * j : ℕ)
              then JTPFormalPSPentagonal.negOnePowInt ℚ k else 0))
          = ∑ᶠ k : ℤ, (if JTPFormalPSPentagonal.pentagonal014Exp k = j
              then JTPFormalPSPentagonal.negOnePowInt ℚ k else 0) by
        apply finsum_congr; intro k
        have hiff : (3 * (JTPFormalPSPentagonal.pentagonal014Exp k : ℤ) = ((3 * j : ℕ) : ℤ))
            ↔ JTPFormalPSPentagonal.pentagonal014Exp k = j := by
          constructor
          · intro hc
            have : (JTPFormalPSPentagonal.pentagonal014Exp k : ℤ) = (j : ℤ) := by push_cast at hc; omega
            exact_mod_cast this
          · intro hc; rw [hc]; push_cast; ring
        by_cases hh : JTPFormalPSPentagonal.pentagonal014Exp k = j
        · rw [if_pos (hiff.mpr hh), if_pos hh]
        · rw [if_neg (fun hc => hh (hiff.mp hc)), if_neg hh]]
      -- now finsum ⟶ Finset.Icc sum via support capture
      rw [finsum_eq_finset_sum_of_support_subset _
        (s := Finset.Icc (-((j : ℤ) + 1)) ((j : ℤ) + 1))]
      intro k hk
      rw [Function.mem_support] at hk
      have hexp : JTPFormalPSPentagonal.pentagonal014Exp k = j := by
        by_contra hc; rw [if_neg hc] at hk; exact hk rfl
      rw [Finset.coe_Icc, Set.mem_Icc]
      exact pentagonal014Exp_window hexp
    · -- 3 ∤ m : both sides 0.
      rw [if_neg h3]
      symm
      apply finsum_eq_zero_of_forall_eq_zero
      intro k
      rw [if_neg]
      intro hc
      apply h3
      have : (3 : ℤ) ∣ (m : ℤ) := ⟨(JTPFormalPSPentagonal.pentagonal014Exp k : ℤ), by omega⟩
      exact_mod_cast this

/-! ## B-LHS: `ofPSK (chan1015LHSPS ℚ) = ChanQuadSum` -/

/-- The `ℚ`-cast of Chan's integer sign `ρ` agrees with `Ch10TwoVar.rho`. -/
theorem rhoInt_cast_eq_rho (r s : ℤ) : ((rhoInt r s : ℤ) : ℚ) = rho r s := by
  unfold rhoInt rho
  by_cases h1 : 0 ≤ r ∧ 0 ≤ s
  · rw [if_pos h1, if_pos h1]; norm_num
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : r < 0 ∧ s < 0
    · rw [if_pos h2, if_pos h2]; norm_num
    · rw [if_neg h2, if_neg h2]; norm_num

/-- The `ℚ`-cast of Chan's integer `δ₃` agrees with `Ch10TwoVar.delta3`. -/
theorem delta3Int_cast_eq_delta3 (k : ℤ) : ((delta3Int k : ℤ) : ℚ) = delta3 k := by
  unfold delta3Int delta3
  by_cases h : (3 : ℤ) ∣ k
  · rw [if_pos h, if_pos h]; norm_num
  · rw [if_neg h, if_neg h]; norm_num

/-- The product of factors in `chan1015CoeffTerm` equals `quadCoeff` (pure cast algebra). -/
theorem chan1015CoeffTerm_value (k l r s : ℤ) :
    ((rhoInt r s : ℤ) : ℚ) * JTPFormalPSPentagonal.negOnePowInt ℚ (k + l + r + s) *
        (((delta3Int k - delta3Int r : ℤ) : ℚ)) * (((delta3Int l - delta3Int s : ℤ) : ℚ))
      = quadCoeff k l r s := by
  unfold quadCoeff
  rw [rhoInt_cast_eq_rho, negOnePowInt_rat_eq_zpow]
  push_cast
  rw [delta3Int_cast_eq_delta3, delta3Int_cast_eq_delta3,
    delta3Int_cast_eq_delta3, delta3Int_cast_eq_delta3]

/-- `chan1015QExponent = qExp4.toNat`, so on the `qExp4 ≥ 0` regime the two exponent tests agree. -/
theorem chan1015QExponent_eq (k l r s : ℤ) :
    chan1015QExponent k l r s = (qExp4 k l r s).toNat := by
  unfold chan1015QExponent qExp4
  congr 1
  ring

/-- The chapter's `chan1015CoeffTerm` (at degree `m`) is the `qExp4 = m` indicator with value
`quadCoeff`. -/
theorem chan1015CoeffTerm_eq_indicator (m : ℕ) (k l r s : ℤ) :
    chan1015CoeffTerm ℚ m k l r s
      = if qExp4 k l r s = (m : ℤ) then quadCoeff k l r s else 0 := by
  unfold chan1015CoeffTerm
  rw [chan1015CoeffTerm_value k l r s]
  by_cases hq : 0 ≤ qExp4 k l r s
  · -- exponent tests agree on the nonneg regime.
    have hcond : (chan1015QExponent k l r s = m) ↔ (qExp4 k l r s = (m : ℤ)) := by
      rw [chan1015QExponent_eq]
      omega
    by_cases hm : qExp4 k l r s = (m : ℤ)
    · rw [if_pos (hcond.mpr hm), if_pos hm]
    · rw [if_neg (fun h => hm (hcond.mp h)), if_neg hm]
  · -- qExp4 < 0 ⟹ quadCoeff = 0, so both branches are 0.
    have hqc : quadCoeff k l r s = 0 := by
      by_contra hc; exact hq (qExp4_nonneg_of_quadCoeff hc)
    rw [hqc]
    rw [if_neg (by omega : ¬ qExp4 k l r s = (m : ℤ))]
    simp

/-- The four-fold box used by `chan1015LHSCoeff`, as one `Finset` over `(ℤ×ℤ)×(ℤ×ℤ)`. -/
def chan1015Box (N : ℕ) : Finset ((ℤ × ℤ) × (ℤ × ℤ)) :=
  (Finset.Icc (-(squareWindow N : ℤ)) (squareWindow N) ×ˢ
      Finset.Icc (-(squareWindow N : ℤ)) (squareWindow N)) ×ˢ
    (Finset.Icc (-((N : ℤ) + 2)) ((N : ℤ) + 2) ×ˢ
      Finset.Icc (-((N : ℤ) + 2)) ((N : ℤ) + 2))

/-- `chan1015LHSCoeff` as a single sum over the box `Finset`. -/
theorem chan1015LHSCoeff_eq_box_sum (m : ℕ) :
    chan1015LHSCoeff ℚ m
      = ∑ p ∈ chan1015Box m, chan1015CoeffTerm ℚ m p.1.1 p.1.2 p.2.1 p.2.2 := by
  unfold chan1015LHSCoeff chan1015Box
  rw [Finset.sum_product]
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl; rintro k _
  rw [Finset.sum_congr rfl (fun l _ => Finset.sum_product ..)]

/-- Box capture: every support point of the `qExp4 = m` indicator lies in `chan1015Box m`. -/
theorem support_subset_box (m : ℕ) :
    (Function.support fun p : (ℤ × ℤ) × (ℤ × ℤ) =>
        if qExp4 p.1.1 p.1.2 p.2.1 p.2.2 = (m : ℤ) then quadCoeff p.1.1 p.1.2 p.2.1 p.2.2 else 0)
      ⊆ (chan1015Box m : Set ((ℤ × ℤ) × (ℤ × ℤ))) := by
  rintro ⟨⟨k, l⟩, ⟨r, s⟩⟩ hp
  rw [Function.mem_support] at hp
  -- the indicator is nonzero ⟹ qExp4 = m and quadCoeff ≠ 0.
  have hqe : qExp4 k l r s = (m : ℤ) := by
    by_contra hc; rw [if_neg hc] at hp; exact hp rfl
  have hqc : quadCoeff k l r s ≠ 0 := by
    intro hc; rw [if_pos hqe, hc] at hp; exact hp rfl
  -- bounds: k² ≤ m, l² ≤ m  ⟹ |k|,|l| ≤ squareWindow m ; r²,s² ≤ m+1 ⟹ |r|,|s| ≤ m+2.
  have hrho : rho r s ≠ 0 := by
    unfold quadCoeff at hqc; intro h; apply hqc; rw [h]; ring
  have hg := g_nonneg_on_rho_support hrho
  have hqe' : k ^ 2 + l ^ 2 + (r ^ 2 + 3 * r * s + s ^ 2 + 3 * r + 3 * s + 1) = (m : ℤ) := by
    have := hqe; unfold qExp4 at this; linarith [this]
  have hk2 : k ^ 2 ≤ (m : ℤ) := by nlinarith [sq_nonneg l, hg, hqe']
  have hl2 : l ^ 2 ≤ (m : ℤ) := by nlinarith [sq_nonneg k, hg, hqe']
  have hgD : r ^ 2 + 3 * r * s + s ^ 2 + 3 * r + 3 * s + 1 ≤ (m : ℤ) := by
    nlinarith [sq_nonneg k, sq_nonneg l, hqe']
  -- r²,s² ≤ m+1 on the ρ-support.
  have hrs : r ^ 2 ≤ (m : ℤ) + 1 ∧ s ^ 2 ≤ (m : ℤ) + 1 := by
    unfold rho at hrho
    by_cases h1 : 0 ≤ r ∧ 0 ≤ s
    · obtain ⟨hr, hs⟩ := h1
      constructor <;> nlinarith [mul_nonneg hr hs, hr, hs, hgD]
    · rw [if_neg h1] at hrho
      by_cases h2 : r < 0 ∧ s < 0
      · obtain ⟨hr, hs⟩ := h2
        refine ⟨?_, ?_⟩
        · nlinarith [mul_nonneg (by omega : (0:ℤ) ≤ -1 - r) (by omega : (0:ℤ) ≤ -1 - s),
            sq_nonneg (-1 - s), hr, hs, hgD]
        · nlinarith [mul_nonneg (by omega : (0:ℤ) ≤ -1 - r) (by omega : (0:ℤ) ≤ -1 - s),
            sq_nonneg (-1 - r), hr, hs, hgD]
      · rw [if_neg h2] at hrho; exact absurd rfl hrho
  obtain ⟨hrb, hsb⟩ := hrs
  obtain ⟨hkL, hkU⟩ := mem_squareWindow_Icc hk2
  obtain ⟨hlL, hlU⟩ := mem_squareWindow_Icc hl2
  -- |r|, |s| ≤ m+2 from r²,s² ≤ m+1.
  have hrbd : -((m : ℤ) + 2) ≤ r ∧ r ≤ (m : ℤ) + 2 := by
    constructor <;> nlinarith [hrb, sq_nonneg (r - 1), sq_nonneg (r + 1)]
  have hsbd : -((m : ℤ) + 2) ≤ s ∧ s ≤ (m : ℤ) + 2 := by
    constructor <;> nlinarith [hsb, sq_nonneg (s - 1), sq_nonneg (s + 1)]
  -- assemble membership.
  simp only [chan1015Box, Finset.coe_product, Finset.coe_Icc, Set.mem_prod, Set.mem_Icc]
  exact ⟨⟨⟨hkL, hkU⟩, ⟨hlL, hlU⟩⟩, ⟨hrbd.1, hrbd.2⟩, ⟨hsbd.1, hsbd.2⟩⟩

/-- **B-LHS:** the chapter's windowed power series transports to `ChanQuadSum`. -/
theorem ofPSK_chan1015LHSPS : ofPSK (chan1015LHSPS ℚ) = ChanQuadSum := by
  apply HahnSeries.ext
  funext D
  rw [ChanQuadSum_coeff]
  -- rewrite each single-term coeff to its indicator.
  rw [show (fun p : (ℤ × ℤ) × (ℤ × ℤ) =>
        (HahnSeries.single (qExp4 p.1.1 p.1.2 p.2.1 p.2.2)
          (quadCoeff p.1.1 p.1.2 p.2.1 p.2.2)).coeff D)
      = fun p => if qExp4 p.1.1 p.1.2 p.2.1 p.2.2 = D
          then quadCoeff p.1.1 p.1.2 p.2.1 p.2.2 else 0 by
    funext p
    rw [HahnSeries.coeff_single]
    by_cases hq : qExp4 p.1.1 p.1.2 p.2.1 p.2.2 = D
    · rw [if_pos hq.symm, if_pos hq]
    · rw [if_neg (fun h => hq h.symm), if_neg hq]]
  rcases lt_or_ge D 0 with hD | hD
  · -- D < 0 : ofPSK coeff 0; each indicator is 0 (qExp4 ≥ 0 on support).
    rw [ofPSK_coeff_neg _ D hD]
    symm
    apply finsum_eq_zero_of_forall_eq_zero
    rintro ⟨⟨k, l⟩, ⟨r, s⟩⟩
    by_cases hqc : quadCoeff k l r s = 0
    · simp only; by_cases hq : qExp4 k l r s = D
      · rw [if_pos hq, hqc]
      · rw [if_neg hq]
    · have : 0 ≤ qExp4 k l r s := qExp4_nonneg_of_quadCoeff hqc
      simp only; rw [if_neg (by omega)]
  · -- D = (m : ℕ).
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hD
    rw [ofPSK_coeff_nat, coeff_chan1015LHSPS, chan1015LHSCoeff_eq_box_sum]
    rw [finsum_eq_finset_sum_of_support_subset _ (support_subset_box m)]
    apply Finset.sum_congr rfl
    rintro ⟨⟨k, l⟩, ⟨r, s⟩⟩ _
    exact chan1015CoeffTerm_eq_indicator m k l r s

/-! ## Final assembly -/

/-- The cleared `K`-identity (★): `poch_q2² · ChanQuadSum = - poch_q⁵ · kP10`.
This composes the two genuine `Chapter10_TwoVar` results. -/
theorem chanQuadSum_cleared :
    poch_q2 ^ 2 * ChanQuadSum = - poch_q ^ 5 * kP10 := by
  rw [← chan_step1_decoupling]
  exact chan_eq_10_15_CTxy

/-- `ofPSK (qPochInfAtPowerPS 3 _) = poch_q` (definitional: both are `ofPSK (expand 3 (qPochInfPS ℚ))`). -/
theorem ofPSK_qPochInfAtPowerPS_three :
    ofPSK (qPochInfAtPowerPS 3 (by decide)) = poch_q := rfl

/-- `ofPSK (qPochInfAtPowerPS 6 _) = poch_q2`. -/
theorem ofPSK_qPochInfAtPowerPS_six :
    ofPSK (qPochInfAtPowerPS 6 (by decide)) = poch_q2 := rfl

/-- `qPochInfAtPowerPS 6 _` is a unit in `ℚ⟦X⟧` (constant coefficient `1`). -/
theorem isUnit_qPochInfAtPowerPS_six :
    IsUnit (qPochInfAtPowerPS 6 (by decide : (6 : ℕ) ≠ 0)) := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  unfold qPochInfAtPowerPS
  rw [PowerSeries.constantCoeff_expand, constantCoeff_qPochInfPS_rat]
  exact isUnit_one

/-- The `(q²;q²)²`-cleared `ℚ⟦X⟧` identity, obtained from (★) by `ofPSK` injectivity. -/
theorem chan1015_cleared_PS :
    (qPochInfAtPowerPS 6 (by decide)) ^ 2 * chan1015LHSPS ℚ
      = - ((qPochInfAtPowerPS 3 (by decide)) ^ 5 * chan1015PentagonalPS) := by
  apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℚ)
  -- ofPSK is HahnSeries.ofPowerSeries ℤ ℚ; push it through products/powers/neg.
  show ofPSK _ = ofPSK _
  rw [map_mul, map_pow, ofPSK_qPochInfAtPowerPS_six, ofPSK_chan1015LHSPS,
    map_neg, map_mul, map_pow, ofPSK_qPochInfAtPowerPS_three, ofPSK_chan1015PentagonalPS]
  rw [chanQuadSum_cleared]
  ring

/-- The constant coefficient of `(qPochInfAtPowerPS 6 _)^2` is nonzero. -/
theorem constantCoeff_qPochInfAtPowerPS_six_sq_ne_zero :
    PowerSeries.constantCoeff ((qPochInfAtPowerPS 6 (by decide)) ^ 2) ≠ 0 := by
  rw [map_pow]
  unfold qPochInfAtPowerPS
  rw [PowerSeries.constantCoeff_expand, constantCoeff_qPochInfPS_rat]
  norm_num

/-- **Chan's Eq. (10.15) in `ℚ⟦X⟧`** — the chapter target. -/
theorem chan1015 : chan1015IdentityStatement := by
  rw [chan1015IdentityStatement_iff]
  -- Multiply both sides by the unit u₆² and cancel.
  apply (isUnit_qPochInfAtPowerPS_six.pow 2).mul_right_injective
  -- goal: u₆² * chan1015LHSPS = u₆² * chan1015RHSPS
  show (qPochInfAtPowerPS 6 (by decide)) ^ 2 * chan1015LHSPS ℚ
      = (qPochInfAtPowerPS 6 (by decide)) ^ 2 * chan1015RHSPS
  rw [chan1015_cleared_PS]
  -- compute u₆² · chan1015RHSPS = -(u₃⁵·pent).
  unfold chan1015RHSPS
  rw [mul_neg]
  congr 1
  -- u₆² · (u₃⁵ · (u₆²)⁻¹ · pent) = u₃⁵ · pent
  -- rearrange so u₆² · (u₆²)⁻¹ are adjacent.
  rw [show (qPochInfAtPowerPS 3 (by decide)) ^ 5 *
        ((qPochInfAtPowerPS 6 (by decide)) ^ 2)⁻¹ * chan1015PentagonalPS
      = ((qPochInfAtPowerPS 6 (by decide)) ^ 2)⁻¹ *
        ((qPochInfAtPowerPS 3 (by decide)) ^ 5 * chan1015PentagonalPS) by
    rw [mul_comm ((qPochInfAtPowerPS 3 (by decide)) ^ 5)
        ((qPochInfAtPowerPS 6 (by decide)) ^ 2)⁻¹, mul_assoc]]
  rw [← mul_assoc, PowerSeries.mul_inv_cancel _ constantCoeff_qPochInfAtPowerPS_six_sq_ne_zero,
    one_mul]

end QseriesFormalization.Pending.Ch10Bridge
