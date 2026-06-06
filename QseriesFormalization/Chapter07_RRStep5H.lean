import QseriesFormalization.Chapter07_RRStep1H
import QseriesFormalization.Chapter07_RRStep5

/-!
# Chapter 7 — Rogers-Ramanujan SECOND identity, Step 5 (Tannery limit, LHS)

H-type mirror of `Chapter07_RRStep5` (the G/first-identity LHS limit).
Takes the finite H-Schur LHS `schurSumH q N = ∑_{n} q^{n²+n}·[N-n choose n]_q`
(proved `= rrPolyH q N` in `Chapter07_RRStep1H`) to the limit `N → ∞`:

`schurSumH q N → rrJInf q q` (the `a=q` Rogers-Ramanujan series).

No analytic gap and **no bottom-index convention** is needed here — this is
the LHS half, a pure mirror of the proven G-side, dominated by the *same*
`gaussianBinom_norm_le` uniform bound (the extra `‖q‖^n` factor only helps).
-/

namespace QseriesFormalization
namespace PartII
namespace Ch07

section Complex

open Filter Topology

/-- **RR Step 5 (H), LHS pointwise limit**: the `n`-th H-Schur LHS term tends
to the `n`-th `a=q` Rogers-Ramanujan series term. Immediate from the proven
`tendsto_gaussianBinom_sub` (`[N-n choose n]_q → 1/(q;q)_n`). -/
theorem tendsto_schurTermH_rrJTerm (q : ℂ) (hq : ‖q‖ < 1) (n : ℕ) :
    Tendsto (fun N : ℕ => q ^ (n ^ 2 + n) * gaussianBinom q (N - n) n) atTop
      (𝓝 (rrJTerm q q n)) := by
  have hval : q ^ (n ^ 2 + n) * (1 / qPochhammer q n) = rrJTerm q q n := by
    rw [rrJTerm_eq, show n * n = n ^ 2 from by ring, pow_add]
    ring
  have hlim :
      Tendsto (fun N : ℕ => q ^ (n ^ 2 + n) * gaussianBinom q (N - n) n) atTop
        (𝓝 (q ^ (n ^ 2 + n) * (1 / qPochhammer q n))) :=
    tendsto_const_nhds.mul (tendsto_gaussianBinom_sub q hq n)
  rwa [hval] at hlim

/-- **RR Step 5 (H), LHS**: `schurSumH q N → rrJInf q q` as `N → ∞`, by
Tannery's theorem (dominated convergence) with the pointwise limit
`tendsto_schurTermH_rrJTerm` and the uniform bound `gaussianBinom_norm_le`
(reused verbatim from the G-side; the extra `q^n` factor only sharpens it). -/
theorem tendsto_schurSumH_rrJInf (q : ℂ) (hq : ‖q‖ < 1) :
    Tendsto (fun N : ℕ => schurSumH q N) atTop (𝓝 (rrJInf q q)) := by
  have h1q : (0 : ℝ) < 1 - ‖q‖ := by linarith
  have hqle : ‖q‖ ≤ 1 := le_of_lt hq
  set D : ℝ := 2 / (1 - ‖q‖) with hD
  set bnd : ℕ → ℝ := fun n => ‖q‖ ^ (n ^ 2) * D ^ n with hbnd
  have hsum : Summable bnd := by
    have hqtend : Tendsto (fun n : ℕ => D * ‖q‖ ^ n) atTop (𝓝 0) := by
      simpa using tendsto_const_nhds.mul
        (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg q) hq)
    obtain ⟨N₀, hN₀⟩ : ∃ N₀, ∀ n ≥ N₀, D * ‖q‖ ^ n < 1 / 2 :=
      (hqtend.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).exists_forall_of_atTop
    have hgeom : Summable fun n : ℕ => ((1 : ℝ) / 2) ^ n :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    refine hgeom.of_norm_bounded_eventually_nat ?_
    rw [Filter.eventually_atTop]
    refine ⟨N₀, fun n hn => ?_⟩
    have hb : D * ‖q‖ ^ n < 1 / 2 := hN₀ n hn
    have hnn : (0 : ℝ) ≤ ‖q‖ ^ (n ^ 2) * D ^ n := by positivity
    rw [hbnd, Real.norm_of_nonneg hnn]
    calc ‖q‖ ^ (n ^ 2) * D ^ n
        = (‖q‖ ^ n) ^ n * D ^ n := by rw [show n ^ 2 = n * n from by ring, pow_mul]
      _ = (D * ‖q‖ ^ n) ^ n := by rw [mul_pow]; ring_nf
      _ ≤ (1 / 2) ^ n := pow_le_pow_left₀ (by positivity) (le_of_lt hb) n
  have hpt : ∀ n : ℕ,
      Tendsto (fun N : ℕ => q ^ (n ^ 2 + n) * gaussianBinom q (N - n) n) atTop
        (𝓝 (rrJTerm q q n)) := fun n => tendsto_schurTermH_rrJTerm q hq n
  have hbound : ∀ᶠ N in (atTop : Filter ℕ), ∀ n : ℕ,
      ‖q ^ (n ^ 2 + n) * gaussianBinom q (N - n) n‖ ≤ bnd n := by
    rw [Filter.eventually_atTop]
    refine ⟨0, fun N _ n => ?_⟩
    rw [norm_mul, norm_pow, hbnd]
    have hqpow_le : ‖q‖ ^ (n ^ 2 + n) ≤ ‖q‖ ^ (n ^ 2) := by
      rw [pow_add]
      calc ‖q‖ ^ (n ^ 2) * ‖q‖ ^ n
          ≤ ‖q‖ ^ (n ^ 2) * 1 :=
            mul_le_mul_of_nonneg_left
              (pow_le_one₀ (norm_nonneg q) hqle) (by positivity)
        _ = ‖q‖ ^ (n ^ 2) := by ring
    by_cases hNn : 2 * n ≤ N
    · calc ‖q‖ ^ (n ^ 2 + n) * ‖gaussianBinom q (N - n) n‖
          ≤ ‖q‖ ^ (n ^ 2) * ‖gaussianBinom q (N - n) n‖ :=
            mul_le_mul_of_nonneg_right hqpow_le (norm_nonneg _)
        _ ≤ ‖q‖ ^ (n ^ 2) * (2 / (1 - ‖q‖)) ^ n :=
            mul_le_mul_of_nonneg_left (gaussianBinom_norm_le q hq n N hNn)
              (by positivity)
        _ = ‖q‖ ^ (n ^ 2) * D ^ n := by rw [hD]
    · have hz : gaussianBinom q (N - n) n = 0 :=
        PartI.Ch03.gaussianBinom_eq_zero_of_lt q (by omega)
      rw [hz, norm_zero, mul_zero]
      positivity
  have htan := tendsto_tsum_of_dominated_convergence hsum hpt hbound
  have hfun : (fun N : ℕ => ∑' n : ℕ, q ^ (n ^ 2 + n) * gaussianBinom q (N - n) n)
      = fun N : ℕ => schurSumH q N :=
    funext fun N => (schurSumH_eq_tsum q N).symm
  rw [hfun] at htan
  exact htan

/-! ### RR Step 5 (H) RHS — ℤ-Tannery (mirror of G-side, top index `N+1`)

`schurRHSH q N = Σ_j (-1)^j q^{pentExp5H j} gBz q (N+1) (schurBottomH N j)`.
The per-`j` central limit `[N+1 choose ⌊(N-5j)/2⌋]_q → 1/(q;q)_∞` is the
same `1/E` as the G-side (TOP `N+1` vs `N` gives the same limit since
`(q;q)_{N+1} → E` too). -/

private theorem tendsto_schurBottomHN_atTop (j : ℤ) :
    Tendsto (fun N : ℕ => (schurBottomH N j).toNat) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  refine ⟨2 * b + 5 * j.natAbs + 10, fun N hN => ?_⟩
  unfold schurBottomH
  have hj : j ≤ (j.natAbs : ℤ) := Int.le_natAbs
  omega

private theorem tendsto_sub_schurBottomHN_atTop (j : ℤ) :
    Tendsto (fun N : ℕ => (N + 1) - (schurBottomH N j).toNat) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  refine ⟨2 * b + 5 * j.natAbs + 10, fun N hN => ?_⟩
  unfold schurBottomH
  have hj : -(j.natAbs : ℤ) ≤ j := by
    have := Int.le_natAbs (a := j); omega
  omega

/-- **RR Step 5 (H) RHS per-`j` limit**: the central Gaussian
`[N+1 choose ⌊(N-5j)/2⌋]_q → 1/(q;q)_∞` as `N → ∞`. -/
theorem tendsto_gBz_center_schurBottomH (q : ℂ) (hq : ‖q‖ < 1) (j : ℤ) :
    Tendsto (fun N : ℕ => gBz q (N + 1) (schurBottomH N j)) atTop
      (𝓝 (1 / PartI.Ch04.eulerPentagonalInfiniteProduct q)) := by
  set E := PartI.Ch04.eulerPentagonalInfiniteProduct q with hE
  have hE_ne : E ≠ 0 := PartI.Ch04.eulerPentagonalInfiniteProduct_ne_zero q hq
  have h_target : (1 : ℂ) / E = E / (E * E) := by field_simp
  rw [h_target]
  have h_main : Tendsto (fun N : ℕ => qPochhammer q N) atTop (𝓝 E) :=
    PartI.Ch04.tendsto_eulerPentagonalProductTrunc q hq
  have h_numN1 : Tendsto (fun N : ℕ => qPochhammer q (N + 1)) atTop (𝓝 E) :=
    h_main.comp (Filter.tendsto_add_atTop_nat 1)
  have h_sb : Tendsto
      (fun N : ℕ => qPochhammer q ((schurBottomH N j).toNat)) atTop (𝓝 E) :=
    h_main.comp (tendsto_schurBottomHN_atTop j)
  have h_rest : Tendsto
      (fun N : ℕ => qPochhammer q ((N + 1) - (schurBottomH N j).toNat))
      atTop (𝓝 E) :=
    h_main.comp (tendsto_sub_schurBottomHN_atTop j)
  have h_den : Tendsto
      (fun N : ℕ => qPochhammer q ((schurBottomH N j).toNat)
        * qPochhammer q ((N + 1) - (schurBottomH N j).toNat))
      atTop (𝓝 (E * E)) := h_sb.mul h_rest
  have h_ratio : Tendsto
      (fun N : ℕ => qPochhammer q (N + 1)
        / (qPochhammer q ((schurBottomH N j).toNat)
            * qPochhammer q ((N + 1) - (schurBottomH N j).toNat)))
      atTop (𝓝 (E / (E * E))) :=
    h_numN1.div h_den (mul_ne_zero hE_ne hE_ne)
  refine h_ratio.congr' ?_
  filter_upwards [Filter.eventually_atTop.mpr
    ⟨5 * j.natAbs + 1, fun N hN => hN⟩] with N hN
  have hjle : j ≤ (j.natAbs : ℤ) := Int.le_natAbs
  have hjge : -(j.natAbs : ℤ) ≤ j := by
    have := Int.le_natAbs (a := j); omega
  have hk0 : 0 ≤ schurBottomH N j := by unfold schurBottomH; omega
  have hkle : (schurBottomH N j).toNat ≤ N + 1 := by
    unfold schurBottomH; omega
  have hkN1 : ((schurBottomH N j).toNat : ℤ) ≤ (N : ℤ) + 1 := by
    push_cast; omega
  rw [gBz_eq q (N + 1) (schurBottomH N j) hk0 (by push_cast; omega)]
  have hclosed :=
    PartI.Ch03.gaussianBinom_mul_qPochhammer_eq q (N + 1)
      ((schurBottomH N j).toNat) hkle
  have hsb_ne : qPochhammer q ((schurBottomH N j).toNat) ≠ 0 :=
    qPochhammer_ne_zero_of_norm_lt_one q hq _
  have hrest_ne : qPochhammer q ((N + 1) - (schurBottomH N j).toNat) ≠ 0 :=
    qPochhammer_ne_zero_of_norm_lt_one q hq _
  rw [div_eq_iff (mul_ne_zero hsb_ne hrest_ne)]
  linear_combination -hclosed

private theorem summable_norm_pentExp5H (q : ℂ) (hq : ‖q‖ < 1) :
    Summable (fun j : ℤ => ‖q‖ ^ pentExp5H j) := by
  have hq0 : (0 : ℝ) ≤ ‖q‖ := norm_nonneg q
  have hgeo : Summable (fun n : ℕ => ‖q‖ ^ n) :=
    summable_geometric_of_lt_one hq0 hq
  rw [summable_int_iff_summable_nat_and_neg]
  refine ⟨Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hgeo,
          Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hgeo⟩
  · have key : n ≤ pentExp5H (n : ℤ) := by
      simp only [pentExp5H]
      have hd := two_dvd_j_5j_add_three (n : ℤ)
      have hp : 2 * (n : ℤ) ≤ (n : ℤ) * (5 * (n : ℤ) + 3) := by
        nlinarith [sq_nonneg (n : ℤ), Int.natCast_nonneg n]
      omega
    exact pow_le_pow_of_le_one hq0 (le_of_lt hq) key
  · have key : n ≤ pentExp5H (-(n : ℤ)) := by
      simp only [pentExp5H]
      have hd := two_dvd_j_5j_add_three (-(n : ℤ))
      have hnn1 : (0 : ℤ) ≤ (n : ℤ) * ((n : ℤ) - 1) := by
        rcases Nat.eq_zero_or_pos n with h | h
        · simp [h]
        · have h1 : (1 : ℤ) ≤ (n : ℤ) := by exact_mod_cast h
          nlinarith [h1]
      have hp : 2 * (n : ℤ) ≤ (-(n : ℤ)) * (5 * (-(n : ℤ)) + 3) := by
        nlinarith [hnn1]
      omega
    exact pow_le_pow_of_le_one hq0 (le_of_lt hq) key

/-- **RR Step 5 (H) RHS step B**: `schurRHSH q N` as a ℤ-`tsum`. -/
theorem schurRHSH_eq_tsum (q : ℂ) (N : ℕ) :
    schurRHSH q N
      = ∑' j : ℤ,
          (-1 : ℂ) ^ j * q ^ pentExp5H j * gBz q (N + 1) (schurBottomH N j) := by
  rw [schurRHSH]
  refine (tsum_eq_sum ?_).symm
  intro j hj
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hj
  have hz : gBz q (N + 1) (schurBottomH N j) = 0 := by
    unfold schurBottomH
    rcases hj with hlt | hgt
    · exact gBz_gt q (N + 1) _ (by push_cast; omega)
    · exact gBz_neg q (N + 1) _ (by omega)
  rw [hz, mul_zero]

/-- **RR Step 5 (H) RHS step C — ℤ-Tannery**: `schurRHSH q N →
(∑'_j (-1)^j q^{j(5j+3)/2}) / (q;q)_∞` as `N → ∞`. -/
theorem tendsto_schurRHSH (q : ℂ) (hq : ‖q‖ < 1) :
    Tendsto (fun N : ℕ => schurRHSH q N) atTop
      (𝓝 ((∑' j : ℤ, (-1 : ℂ) ^ j * q ^ pentExp5H j)
            / PartI.Ch04.eulerPentagonalInfiniteProduct q)) := by
  set E := PartI.Ch04.eulerPentagonalInfiniteProduct q with hE
  have hE_ne : E ≠ 0 := PartI.Ch04.eulerPentagonalInfiniteProduct_ne_zero q hq
  obtain ⟨C, hC0, hCbnd⟩ := gaussianBinom_norm_le_uniform q hq
  set bnd : ℤ → ℝ := fun j => ‖q‖ ^ pentExp5H j * C with hbnd
  have hsum : Summable bnd := (summable_norm_pentExp5H q hq).mul_right C
  have hpt : ∀ j : ℤ,
      Tendsto (fun N : ℕ =>
          (-1 : ℂ) ^ j * q ^ pentExp5H j * gBz q (N + 1) (schurBottomH N j))
        atTop (𝓝 ((-1 : ℂ) ^ j * q ^ pentExp5H j * (1 / E))) := fun j =>
    tendsto_const_nhds.mul (tendsto_gBz_center_schurBottomH q hq j)
  have hbound : ∀ᶠ N in (atTop : Filter ℕ), ∀ j : ℤ,
      ‖(-1 : ℂ) ^ j * q ^ pentExp5H j * gBz q (N + 1) (schurBottomH N j)‖
        ≤ bnd j := by
    rw [Filter.eventually_atTop]
    refine ⟨0, fun N _ j => ?_⟩
    simp only [hbnd, norm_mul, norm_zpow, norm_pow, norm_neg, norm_one,
               one_zpow, one_mul]
    by_cases hsb : 0 ≤ schurBottomH N j ∧ schurBottomH N j ≤ (N : ℤ) + 1
    · rw [gBz_eq q (N + 1) (schurBottomH N j) hsb.1 (by push_cast; omega)]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact hCbnd (N + 1) ((schurBottomH N j).toNat) (by omega)
    · have hz : gBz q (N + 1) (schurBottomH N j) = 0 := by
        rcases not_and_or.mp hsb with h | h
        · exact gBz_neg q (N + 1) _ (by omega)
        · exact gBz_gt q (N + 1) _ (by omega)
      rw [hz, norm_zero, mul_zero]; positivity
  have htan := tendsto_tsum_of_dominated_convergence hsum hpt hbound
  have hL : (fun N : ℕ => ∑' j : ℤ,
        (-1 : ℂ) ^ j * q ^ pentExp5H j * gBz q (N + 1) (schurBottomH N j))
      = fun N : ℕ => schurRHSH q N :=
    funext fun N => (schurRHSH_eq_tsum q N).symm
  rw [hL] at htan
  have hR : (∑' j : ℤ, (-1 : ℂ) ^ j * q ^ pentExp5H j * (1 / E))
      = (∑' j : ℤ, (-1 : ℂ) ^ j * q ^ pentExp5H j) / E := by
    rw [tsum_mul_right, mul_one_div]
  rw [hR] at htan
  exact htan

/-- **Step 2 of the Rogers-Ramanujan proof (h_step2), UNCONDITIONAL**:
`rrJInf q q · (q;q)_∞ = ∑'_{j:ℤ} (-1)^j q^{j(5j+3)/2}`. -/
theorem rrJInf_q_mul_eulerPentagonal_eq (q : ℂ) (hq : ‖q‖ < 1) :
    rrJInf q q * PartI.Ch04.eulerPentagonalInfiniteProduct q
      = ∑' j : ℤ, (-1 : ℂ) ^ j * q ^ (j * (5 * j + 3) / 2) := by
  set E := PartI.Ch04.eulerPentagonalInfiniteProduct q with hE
  have hE_ne : E ≠ 0 := PartI.Ch04.eulerPentagonalInfiniteProduct_ne_zero q hq
  have heq : (fun N : ℕ => schurSumH q N) = fun N : ℕ => schurRHSH q N :=
    funext (schurSumH_eq_schurRHSH q)
  have hL := tendsto_schurSumH_rrJInf q hq
  rw [heq] at hL
  have hR := tendsto_schurRHSH q hq
  have hlim : rrJInf q q
      = (∑' j : ℤ, (-1 : ℂ) ^ j * q ^ pentExp5H j) / E :=
    tendsto_nhds_unique hL hR
  have hpe : (∑' j : ℤ, (-1 : ℂ) ^ j * q ^ pentExp5H j)
      = ∑' j : ℤ, (-1 : ℂ) ^ j * q ^ (j * (5 * j + 3) / 2) := by
    refine tsum_congr fun j => ?_
    congr 1
    simp only [pentExp5H]
    rw [← zpow_natCast, Int.toNat_of_nonneg (pentH_int_nonneg j)]
  rw [hpe] at hlim
  rw [hlim]
  exact div_mul_cancel₀ _ hE_ne

/-- **Rogers-Ramanujan SECOND identity** (unconditional, `‖q‖<1`, `q≠0`):
`H(q) · (q²;q⁵)_∞ · (q³;q⁵)_∞ = 1`. Mirror of `rogersRamanujan_first`,
discharged by the now-proven `rrJInf_q_mul_eulerPentagonal_eq` (h_step2)
together with `theta_sum_2_eq_mod5_product` and the mod-5 regroup. -/
theorem rogersRamanujan_second (q : ℂ) (hq : ‖q‖ < 1) (hq_ne : q ≠ 0) :
    rrJInf q q * (∏' n : ℕ, PartI.Ch04.rrMod5Factor q 2 n)
      * (∏' n : ℕ, PartI.Ch04.rrMod5Factor q 3 n) = 1 := by
  have h_step2 := rrJInf_q_mul_eulerPentagonal_eq q hq
  have h_theta := PartI.Ch04.theta_sum_2_eq_mod5_product q hq hq_ne
  have h_regroup := PartI.Ch04.eulerPentagonalInfiniteProduct_eq_mod5_regroup q hq
  have h_ne5 := PartI.Ch04.tprod_rrMod5Factor_ne_zero q hq 5 (by norm_num)
  have h_ne4 := PartI.Ch04.tprod_rrMod5Factor_ne_zero q hq 4 (by norm_num)
  have h_ne1 := PartI.Ch04.tprod_rrMod5Factor_ne_zero q hq 1 (by norm_num)
  have h_combined :
      rrJInf q q *
        ((∏' n, PartI.Ch04.rrMod5Factor q 1 n) *
         (∏' n, PartI.Ch04.rrMod5Factor q 2 n) *
         (∏' n, PartI.Ch04.rrMod5Factor q 3 n) *
         (∏' n, PartI.Ch04.rrMod5Factor q 4 n) *
         (∏' n, PartI.Ch04.rrMod5Factor q 5 n)) =
      (∏' n, PartI.Ch04.rrMod5Factor q 5 n) *
      (∏' n, PartI.Ch04.rrMod5Factor q 4 n) *
      (∏' n, PartI.Ch04.rrMod5Factor q 1 n) := by
    rw [show
        rrJInf q q *
          ((∏' n, PartI.Ch04.rrMod5Factor q 1 n) *
           (∏' n, PartI.Ch04.rrMod5Factor q 2 n) *
           (∏' n, PartI.Ch04.rrMod5Factor q 3 n) *
           (∏' n, PartI.Ch04.rrMod5Factor q 4 n) *
           (∏' n, PartI.Ch04.rrMod5Factor q 5 n)) =
        (rrJInf q q * PartI.Ch04.eulerPentagonalInfiniteProduct q) by
      rw [h_regroup]]
    rw [h_step2, h_theta]
  have h_factor :
      (∏' n, PartI.Ch04.rrMod5Factor q 1 n) *
      (∏' n, PartI.Ch04.rrMod5Factor q 4 n) *
      (∏' n, PartI.Ch04.rrMod5Factor q 5 n) ≠ 0 :=
    mul_ne_zero (mul_ne_zero h_ne1 h_ne4) h_ne5
  have h_simplified :
      rrJInf q q * (∏' n, PartI.Ch04.rrMod5Factor q 2 n)
        * (∏' n, PartI.Ch04.rrMod5Factor q 3 n) *
      ((∏' n, PartI.Ch04.rrMod5Factor q 1 n) *
       (∏' n, PartI.Ch04.rrMod5Factor q 4 n) *
       (∏' n, PartI.Ch04.rrMod5Factor q 5 n)) =
      (∏' n, PartI.Ch04.rrMod5Factor q 1 n) *
      (∏' n, PartI.Ch04.rrMod5Factor q 4 n) *
      (∏' n, PartI.Ch04.rrMod5Factor q 5 n) := by
    have := h_combined
    linear_combination this
  have := mul_right_cancel₀ h_factor (h_simplified.trans (one_mul _).symm)
  exact this

end Complex

end Ch07
end PartII
end QseriesFormalization
