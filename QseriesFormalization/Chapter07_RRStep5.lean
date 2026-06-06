import QseriesFormalization.Chapter07_RRStep1

/-!
# Chapter 7 — Rogers-Ramanujan Step 5 (Tannery limit, LHS)

Takes the unconditional finite Schur identity `schurSum q N = schurRHS q N`
(proved in `Chapter07_RRStep1`) to the limit `N → ∞`.

LHS pointwise limit (this file, complete, no analytic gap):
`q^(n²)·[N-n choose n]_q → rrJTerm 1 q n` as `N → ∞`, from the proven
`tendsto_gaussianBinom_sub`.

The full Tannery step (dominated convergence: `schurSum q N → rrJInf 1 q`)
needs a uniform `q`-binomial bound; that analytic core is tracked in
`docs/RR_step1_schur.md` (RR Step 5 dispatch) and added once complete.
-/

namespace QseriesFormalization
namespace PartII
namespace Ch07

section Complex

open Filter Topology

/-- **RR Step 5, LHS pointwise limit**: the `n`-th Schur LHS term tends to
the `n`-th Rogers-Ramanujan series term. Immediate from the proven
`tendsto_gaussianBinom_sub` (`[N-n choose n]_q → 1/(q;q)_n`). -/
theorem tendsto_schurTerm_rrJTerm (q : ℂ) (hq : ‖q‖ < 1) (n : ℕ) :
    Tendsto (fun N : ℕ => q ^ (n ^ 2) * gaussianBinom q (N - n) n) atTop
      (𝓝 (rrJTerm 1 q n)) := by
  have hval : q ^ (n ^ 2) * (1 / qPochhammer q n) = rrJTerm 1 q n := by
    rw [rrJTerm_eq, one_pow, one_mul, show n * n = n ^ 2 from by ring]
    ring
  have hlim :
      Tendsto (fun N : ℕ => q ^ (n ^ 2) * gaussianBinom q (N - n) n) atTop
        (𝓝 (q ^ (n ^ 2) * (1 / qPochhammer q n))) :=
    tendsto_const_nhds.mul (tendsto_gaussianBinom_sub q hq n)
  rwa [hval] at hlim

/-! ### Uniform `q`-binomial bound (ChatGPT crude-bound strategy)

`‖gaussianBinom q (N-n) n‖ ≤ (2/(1-‖q‖))^n` for `2n ≤ N`, `‖q‖<1`,
via the `q`-Pochhammer ratio identity + per-factor norm bounds. -/

/-- Lower bound: `(1-‖q‖)^n ≤ ‖(q;q)_n‖`. -/
private theorem qPochhammer_norm_lower (q : ℂ) (hq : ‖q‖ < 1) :
    ∀ n : ℕ, (1 - ‖q‖) ^ n ≤ ‖qPochhammer q n‖
  | 0 => by simp
  | n + 1 => by
      have ih := qPochhammer_norm_lower q hq n
      have h1q : (0 : ℝ) ≤ 1 - ‖q‖ := by linarith
      have hqle : ‖q‖ ≤ 1 := le_of_lt hq
      have hqpow : ‖q‖ ^ (n + 1) ≤ ‖q‖ := by
        rw [pow_succ]
        nlinarith [pow_le_one₀ (norm_nonneg q) hqle (n := n), norm_nonneg q]
      have hfac : 1 - ‖q‖ ≤ ‖1 - q ^ (n + 1)‖ := by
        have h1 : 1 - ‖q ^ (n + 1)‖ ≤ ‖1 - q ^ (n + 1)‖ := by
          have := norm_sub_norm_le (1 : ℂ) (q ^ (n + 1))
          simpa using this
        rw [norm_pow] at h1
        linarith
      calc (1 - ‖q‖) ^ (n + 1)
          = (1 - ‖q‖) ^ n * (1 - ‖q‖) := by rw [pow_succ]
        _ ≤ ‖qPochhammer q n‖ * ‖1 - q ^ (n + 1)‖ :=
            mul_le_mul ih hfac h1q (le_trans (by positivity) ih)
        _ = ‖qPochhammer q (n + 1)‖ := by rw [qPochhammer_succ, norm_mul]

/-- Extension: `‖(q;q)_{m+k}‖ ≤ ‖(q;q)_m‖ · 2^k` (each extra factor `≤ 2`). -/
private theorem qPochhammer_norm_extend (q : ℂ) (hq : ‖q‖ ≤ 1) (m : ℕ) :
    ∀ k : ℕ, ‖qPochhammer q (m + k)‖ ≤ ‖qPochhammer q m‖ * 2 ^ k
  | 0 => by simp
  | k + 1 => by
      have ih := qPochhammer_norm_extend q hq m k
      have hmk : m + (k + 1) = (m + k) + 1 := by omega
      have hb : ‖1 - q ^ ((m + k) + 1)‖ ≤ 2 := by
        calc ‖1 - q ^ ((m + k) + 1)‖
            ≤ ‖(1 : ℂ)‖ + ‖q ^ ((m + k) + 1)‖ := norm_sub_le _ _
          _ ≤ 1 + 1 := by
              have hq1 : ‖q ^ ((m + k) + 1)‖ ≤ 1 := by
                rw [norm_pow]; exact pow_le_one₀ (norm_nonneg q) hq
              simpa using hq1
          _ = 2 := by norm_num
      have hstep : ‖qPochhammer q (m + (k + 1))‖
          ≤ ‖qPochhammer q (m + k)‖ * 2 := by
        rw [hmk, qPochhammer_succ, norm_mul]
        exact mul_le_mul_of_nonneg_left hb (norm_nonneg _)
      calc ‖qPochhammer q (m + (k + 1))‖
          ≤ ‖qPochhammer q (m + k)‖ * 2 := hstep
        _ ≤ ‖qPochhammer q m‖ * 2 ^ k * 2 :=
            mul_le_mul_of_nonneg_right ih (by norm_num)
        _ = ‖qPochhammer q m‖ * 2 ^ (k + 1) := by rw [pow_succ]; ring

/-- **RR Step 5 uniform bound**: `‖[N-n choose n]_q‖ ≤ (2/(1-‖q‖))^n`
for `2n ≤ N` (the `n²`-decay of `‖q‖^{n²}` then beats this for Tannery). -/
theorem gaussianBinom_norm_le (q : ℂ) (hq : ‖q‖ < 1) (n N : ℕ)
    (hN : 2 * n ≤ N) :
    ‖gaussianBinom q (N - n) n‖ ≤ (2 / (1 - ‖q‖)) ^ n := by
  have hqle : ‖q‖ ≤ 1 := le_of_lt hq
  have h1q : (0 : ℝ) < 1 - ‖q‖ := by linarith
  have hnle : n ≤ N - n := by omega
  have hid := PartI.Ch03.gaussianBinom_mul_qPochhammer_eq q (N - n) n hnle
  have hsub : (N - n) - n = N - 2 * n := by omega
  rw [hsub] at hid
  have hpn_ne : qPochhammer q n ≠ 0 :=
    qPochhammer_ne_zero_of_norm_lt_one q hq n
  have hp2_ne : qPochhammer q (N - 2 * n) ≠ 0 :=
    qPochhammer_ne_zero_of_norm_lt_one q hq (N - 2 * n)
  have hgb : gaussianBinom q (N - n) n
      = qPochhammer q (N - n)
        / (qPochhammer q n * qPochhammer q (N - 2 * n)) := by
    rw [eq_div_iff (mul_ne_zero hpn_ne hp2_ne)]
    linear_combination hid
  have hpn_pos : 0 < ‖qPochhammer q n‖ := norm_pos_iff.mpr hpn_ne
  have hp2_pos : 0 < ‖qPochhammer q (N - 2 * n)‖ := norm_pos_iff.mpr hp2_ne
  have hNn : N - n = (N - 2 * n) + n := by omega
  have hnum : ‖qPochhammer q (N - n)‖
      ≤ ‖qPochhammer q (N - 2 * n)‖ * 2 ^ n := by
    rw [hNn]; exact qPochhammer_norm_extend q hqle (N - 2 * n) n
  have hden : (1 - ‖q‖) ^ n ≤ ‖qPochhammer q n‖ := qPochhammer_norm_lower q hq n
  have h1qn : (0 : ℝ) < (1 - ‖q‖) ^ n := by positivity
  rw [hgb, norm_div, norm_mul, div_le_iff₀ (by positivity), div_pow]
  -- ‖qPoch(N-n)‖ ≤ 2^n/(1-‖q‖)^n · (‖qPoch n‖·‖qPoch(N-2n)‖)
  have hstep1 : ‖qPochhammer q (N - n)‖
      ≤ ‖qPochhammer q (N - 2 * n)‖ * 2 ^ n := hnum
  have hstep2 : ‖qPochhammer q (N - 2 * n)‖ * 2 ^ n
      ≤ 2 ^ n / (1 - ‖q‖) ^ n
        * (‖qPochhammer q n‖ * ‖qPochhammer q (N - 2 * n)‖) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ h1qn]
    have hfac : (1 - ‖q‖) ^ n * ‖qPochhammer q (N - 2 * n)‖
        ≤ ‖qPochhammer q n‖ * ‖qPochhammer q (N - 2 * n)‖ :=
      mul_le_mul_of_nonneg_right hden (le_of_lt hp2_pos)
    nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) n, hp2_pos, hfac]
  linarith [hstep1, hstep2]

/-! ### RR Step 5 — Tannery limit (LHS) -/

/-- **RR Step 5 LHS**: `schurSum q N → rrJInf 1 q` as `N → ∞`, by Tannery's
theorem (dominated convergence) with the pointwise limit
`tendsto_schurTerm_rrJTerm` and the uniform bound `gaussianBinom_norm_le`. -/
theorem tendsto_schurSum_rrJInf (q : ℂ) (hq : ‖q‖ < 1) :
    Tendsto (fun N : ℕ => schurSum q N) atTop (𝓝 (rrJInf 1 q)) := by
  have h1q : (0 : ℝ) < 1 - ‖q‖ := by linarith
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
      Tendsto (fun N : ℕ => q ^ (n ^ 2) * gaussianBinom q (N - n) n) atTop
        (𝓝 (rrJTerm 1 q n)) := fun n => tendsto_schurTerm_rrJTerm q hq n
  have hbound : ∀ᶠ N in (atTop : Filter ℕ), ∀ n : ℕ,
      ‖q ^ (n ^ 2) * gaussianBinom q (N - n) n‖ ≤ bnd n := by
    rw [Filter.eventually_atTop]
    refine ⟨0, fun N _ n => ?_⟩
    rw [norm_mul, norm_pow, hbnd]
    by_cases hNn : 2 * n ≤ N
    · calc ‖q‖ ^ (n ^ 2) * ‖gaussianBinom q (N - n) n‖
          ≤ ‖q‖ ^ (n ^ 2) * (2 / (1 - ‖q‖)) ^ n :=
            mul_le_mul_of_nonneg_left (gaussianBinom_norm_le q hq n N hNn)
              (by positivity)
        _ = ‖q‖ ^ (n ^ 2) * D ^ n := by rw [hD]
    · have hz : gaussianBinom q (N - n) n = 0 :=
        PartI.Ch03.gaussianBinom_eq_zero_of_lt q (by omega)
      rw [hz, norm_zero, mul_zero]
      positivity
  have htan := tendsto_tsum_of_dominated_convergence hsum hpt hbound
  have hfun : (fun N : ℕ => ∑' n : ℕ, q ^ (n ^ 2) * gaussianBinom q (N - n) n)
      = fun N : ℕ => schurSum q N :=
    funext fun N => (schurSum_eq_tsum q N).symm
  rw [hfun] at htan
  exact htan

/-! ### RR Step 5 — RHS per-`j` central-Gaussian limit -/

/-- `schurBottom N j → ∞` as `N → ∞` (fixed `j`). -/
private theorem tendsto_schurBottom_atTop (j : ℤ) :
    Tendsto (fun N : ℕ => schurBottom N j) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  refine ⟨2 * b + 5 * j.natAbs + 10, fun N hN => ?_⟩
  unfold schurBottom
  have hge : ¬ ((N : ℤ) - 5 * j < 0) := by
    have hj : j ≤ (j.natAbs : ℤ) := Int.le_natAbs
    omega
  rw [if_neg hge]
  omega

/-- `N - schurBottom N j → ∞` as `N → ∞` (fixed `j`). -/
private theorem tendsto_sub_schurBottom_atTop (j : ℤ) :
    Tendsto (fun N : ℕ => N - schurBottom N j) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  refine ⟨2 * b + 5 * j.natAbs + 10, fun N hN => ?_⟩
  unfold schurBottom
  have hge : ¬ ((N : ℤ) - 5 * j < 0) := by
    have hj : -(j.natAbs : ℤ) ≤ j := by omega
    omega
  rw [if_neg hge]
  omega

/-- **RR Step 5 RHS per-`j` limit**: the central Gaussian
`[N choose ⌊(N-5j)/2⌋]_q → 1/(q;q)_∞` as `N → ∞`. -/
theorem tendsto_gaussianBinom_center_schurBottom (q : ℂ) (hq : ‖q‖ < 1)
    (j : ℤ) :
    Tendsto (fun N : ℕ => gaussianBinom q N (schurBottom N j)) atTop
      (𝓝 (1 / PartI.Ch04.eulerPentagonalInfiniteProduct q)) := by
  set E := PartI.Ch04.eulerPentagonalInfiniteProduct q with hE
  have hE_ne : E ≠ 0 := PartI.Ch04.eulerPentagonalInfiniteProduct_ne_zero q hq
  have h_target : (1 : ℂ) / E = E / (E * E) := by field_simp
  rw [h_target]
  have h_main : Tendsto (fun N : ℕ => qPochhammer q N) atTop (𝓝 E) :=
    PartI.Ch04.tendsto_eulerPentagonalProductTrunc q hq
  have h_num : Tendsto (fun N : ℕ => qPochhammer q N) atTop (𝓝 E) := h_main
  have h_sb : Tendsto (fun N : ℕ => qPochhammer q (schurBottom N j)) atTop (𝓝 E) :=
    h_main.comp (tendsto_schurBottom_atTop j)
  have h_rest :
      Tendsto (fun N : ℕ => qPochhammer q (N - schurBottom N j)) atTop (𝓝 E) :=
    h_main.comp (tendsto_sub_schurBottom_atTop j)
  have h_den :
      Tendsto (fun N : ℕ =>
        qPochhammer q (schurBottom N j) * qPochhammer q (N - schurBottom N j))
        atTop (𝓝 (E * E)) := h_sb.mul h_rest
  have h_ratio :
      Tendsto (fun N : ℕ =>
        qPochhammer q N
          / (qPochhammer q (schurBottom N j) * qPochhammer q (N - schurBottom N j)))
        atTop (𝓝 (E / (E * E))) :=
    h_num.div h_den (mul_ne_zero hE_ne hE_ne)
  refine h_ratio.congr' ?_
  filter_upwards [Filter.eventually_atTop.mpr
    ⟨5 * j.natAbs + 1, fun N hN => hN⟩] with N hN
  have hjle : j ≤ (j.natAbs : ℤ) := Int.le_natAbs
  have hjge : -(j.natAbs : ℤ) ≤ j := by omega
  have hsble : schurBottom N j ≤ N := by
    unfold schurBottom
    have hge : ¬ ((N : ℤ) - 5 * j < 0) := by omega
    rw [if_neg hge]; omega
  have hclosed :=
    PartI.Ch03.gaussianBinom_mul_qPochhammer_eq q N (schurBottom N j) hsble
  have hsb_ne : qPochhammer q (schurBottom N j) ≠ 0 :=
    qPochhammer_ne_zero_of_norm_lt_one q hq (schurBottom N j)
  have hrest_ne : qPochhammer q (N - schurBottom N j) ≠ 0 :=
    qPochhammer_ne_zero_of_norm_lt_one q hq (N - schurBottom N j)
  rw [div_eq_iff (mul_ne_zero hsb_ne hrest_ne)]
  linear_combination -hclosed

/-! ### RR Step 5 RHS — uniform q-Pochhammer norm bounds

`‖(q;q)_n‖` converges to `‖(q;q)_∞‖ ≠ 0`, hence is uniformly bounded
above and below by a positive constant (eventually-bound + finite
prefix). No infinite-product machinery needed. -/

private theorem qPochhammer_norm_uniform (q : ℂ) (hq : ‖q‖ < 1) :
    ∃ Blo Bup : ℝ, 0 < Blo ∧ ∀ n : ℕ,
      Blo ≤ ‖qPochhammer q n‖ ∧ ‖qPochhammer q n‖ ≤ Bup := by
  set E := PartI.Ch04.eulerPentagonalInfiniteProduct q with hE
  have hE_ne : E ≠ 0 := PartI.Ch04.eulerPentagonalInfiniteProduct_ne_zero q hq
  have hEpos : 0 < ‖E‖ := norm_pos_iff.mpr hE_ne
  have h_tend : Tendsto (fun n : ℕ => ‖qPochhammer q n‖) atTop (𝓝 ‖E‖) :=
    (PartI.Ch04.tendsto_eulerPentagonalProductTrunc q hq).norm
  obtain ⟨N₀, hN₀⟩ : ∃ N₀, ∀ n ≥ N₀,
      ‖E‖ / 2 < ‖qPochhammer q n‖ ∧ ‖qPochhammer q n‖ < ‖E‖ + 1 := by
    have h1 := h_tend.eventually (eventually_gt_nhds (by linarith : ‖E‖ / 2 < ‖E‖))
    have h2 := h_tend.eventually (eventually_lt_nhds (by linarith : ‖E‖ < ‖E‖ + 1))
    exact (h1.and h2).exists_forall_of_atTop
  have hpos : ∀ n : ℕ, 0 < ‖qPochhammer q n‖ := fun n =>
    norm_pos_iff.mpr (qPochhammer_ne_zero_of_norm_lt_one q hq n)
  set S := Finset.range (N₀ + 1) with hS
  have hSne : S.Nonempty := Finset.nonempty_range_succ
  set m := S.inf' hSne (fun n => ‖qPochhammer q n‖) with hm
  set M := S.sup' hSne (fun n => ‖qPochhammer q n‖) with hMdef
  have hm_pos : 0 < m := by
    rw [hm, Finset.lt_inf'_iff]
    exact fun n _ => hpos n
  refine ⟨min (‖E‖ / 2) m, max (‖E‖ + 1) M, lt_min (by linarith) hm_pos,
          fun n => ?_⟩
  by_cases hn : n ≤ N₀
  · have hnS : n ∈ S := Finset.mem_range.mpr (by omega)
    constructor
    · exact le_trans (min_le_right _ _)
        (Finset.inf'_le (fun n => ‖qPochhammer q n‖) hnS)
    · exact le_trans (Finset.le_sup' (fun n => ‖qPochhammer q n‖) hnS)
        (le_max_right _ _)
  · have hge : n ≥ N₀ := by omega
    have hb := hN₀ n hge
    constructor
    · exact le_trans (min_le_left _ _) (le_of_lt hb.1)
    · exact le_trans (le_of_lt hb.2) (le_max_left _ _)

/-- **RR Step 5 RHS uniform central bound**: `‖[N choose k]_q‖ ≤ Bup/Blo²`
uniformly in `N, k` (for `k ≤ N`), `‖q‖<1`. -/
theorem gaussianBinom_norm_le_uniform (q : ℂ) (hq : ‖q‖ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N k : ℕ, k ≤ N → ‖gaussianBinom q N k‖ ≤ C := by
  obtain ⟨Blo, Bup, hBlo, hbnd⟩ := qPochhammer_norm_uniform q hq
  have hBup : 0 ≤ Bup :=
    le_trans (le_of_lt hBlo) (le_trans (hbnd 0).1 (hbnd 0).2)
  refine ⟨Bup / (Blo * Blo), by positivity, fun N k hk => ?_⟩
  have hid := PartI.Ch03.gaussianBinom_mul_qPochhammer_eq q N k hk
  have hk_ne : qPochhammer q k ≠ 0 :=
    qPochhammer_ne_zero_of_norm_lt_one q hq k
  have hNk_ne : qPochhammer q (N - k) ≠ 0 :=
    qPochhammer_ne_zero_of_norm_lt_one q hq (N - k)
  have hgb : gaussianBinom q N k
      = qPochhammer q N / (qPochhammer q k * qPochhammer q (N - k)) := by
    rw [eq_div_iff (mul_ne_zero hk_ne hNk_ne)]
    linear_combination hid
  rw [hgb, norm_div, norm_mul]
  rw [div_le_iff₀ (by positivity)]
  have hN := (hbnd N).2
  have hk2 := (hbnd k).1
  have hNk2 := (hbnd (N - k)).1
  have hk2' := (hbnd k).2
  have hNk2' := (hbnd (N - k)).2
  have e1 : 0 < ‖qPochhammer q k‖ := lt_of_lt_of_le hBlo hk2
  have e2 : 0 < ‖qPochhammer q (N - k)‖ := lt_of_lt_of_le hBlo hNk2
  -- ‖qPoch N‖ ≤ Bup ≤ (Bup/Blo²)·(‖qPoch k‖·‖qPoch(N-k)‖) since ‖·‖≥Blo
  have hprod : Blo * Blo ≤ ‖qPochhammer q k‖ * ‖qPochhammer q (N - k)‖ :=
    mul_le_mul hk2 hNk2 (le_of_lt hBlo) (le_of_lt e1)
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  nlinarith [hN, hprod, hBup, mul_pos e1 e2, hBlo]

/-! ### RR Step 5 RHS — theta ℤ-summability (recipe step A)

`∑_{j:ℤ} ‖q‖^{pentExp5 j}` converges: `pentExp5 j = j(5j+1)/2 ≥ |j|`,
so each one-sided tail is dominated by the geometric `‖q‖^n`. -/

private theorem summable_norm_pentExp5 (q : ℂ) (hq : ‖q‖ < 1) :
    Summable (fun j : ℤ => ‖q‖ ^ pentExp5 j) := by
  have hq0 : (0 : ℝ) ≤ ‖q‖ := norm_nonneg q
  have hgeo : Summable (fun n : ℕ => ‖q‖ ^ n) :=
    summable_geometric_of_lt_one hq0 hq
  rw [summable_int_iff_summable_nat_and_neg]
  refine ⟨Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hgeo,
          Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hgeo⟩
  · have key : n ≤ pentExp5 (n : ℤ) := by
      simp only [pentExp5]
      have hd := two_dvd_j_5j_add_one (n : ℤ)
      have hp : 2 * (n : ℤ) ≤ (n : ℤ) * (5 * (n : ℤ) + 1) := by
        nlinarith [sq_nonneg (n : ℤ), Int.natCast_nonneg n]
      omega
    exact pow_le_pow_of_le_one hq0 (le_of_lt hq) key
  · have key : n ≤ pentExp5 (-(n : ℤ)) := by
      simp only [pentExp5]
      have hd := two_dvd_j_5j_add_one (-(n : ℤ))
      have hp : 2 * (n : ℤ) ≤ (-(n : ℤ)) * (5 * (-(n : ℤ)) + 1) := by
        nlinarith [sq_nonneg (n : ℤ), Int.natCast_nonneg n]
      omega
    exact pow_le_pow_of_le_one hq0 (le_of_lt hq) key

/-- **RR Step 5 RHS step B**: `schurRHS q N` as a ℤ-`tsum` (finite
support — the central Gaussian vanishes outside the `Icc`). -/
theorem schurRHS_eq_tsum (q : ℂ) (N : ℕ) :
    schurRHS q N
      = ∑' j : ℤ,
          (-1 : ℂ) ^ j * q ^ pentExp5 j * gaussianBinom q N (schurBottom N j) := by
  rw [schurRHS]
  refine (tsum_eq_sum ?_).symm
  intro j hj
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hj
  have hz : gaussianBinom q N (schurBottom N j) = 0 := by
    apply PartI.Ch03.gaussianBinom_eq_zero_of_lt q
    unfold schurBottom
    rcases hj with hlt | hgt
    · rw [if_neg (by omega : ¬ ((N : ℤ) - 5 * j < 0))]; omega
    · rw [if_pos (by omega : (N : ℤ) - 5 * j < 0)]; omega
  rw [hz, mul_zero]

/-- **RR Step 5 RHS step C — ℤ-Tannery**: `schurRHS q N → (∑'_j (-1)^j
q^{j(5j+1)/2}) / (q;q)_∞` as `N → ∞`. -/
theorem tendsto_schurRHS (q : ℂ) (hq : ‖q‖ < 1) :
    Tendsto (fun N : ℕ => schurRHS q N) atTop
      (𝓝 ((∑' j : ℤ, (-1 : ℂ) ^ j * q ^ pentExp5 j)
            / PartI.Ch04.eulerPentagonalInfiniteProduct q)) := by
  set E := PartI.Ch04.eulerPentagonalInfiniteProduct q with hE
  have hE_ne : E ≠ 0 := PartI.Ch04.eulerPentagonalInfiniteProduct_ne_zero q hq
  obtain ⟨C, _hC0, hCbnd⟩ := gaussianBinom_norm_le_uniform q hq
  set bnd : ℤ → ℝ := fun j => ‖q‖ ^ pentExp5 j * C with hbnd
  have hsum : Summable bnd := (summable_norm_pentExp5 q hq).mul_right C
  have hpt : ∀ j : ℤ,
      Tendsto (fun N : ℕ =>
          (-1 : ℂ) ^ j * q ^ pentExp5 j * gaussianBinom q N (schurBottom N j))
        atTop (𝓝 ((-1 : ℂ) ^ j * q ^ pentExp5 j * (1 / E))) := fun j =>
    tendsto_const_nhds.mul (tendsto_gaussianBinom_center_schurBottom q hq j)
  have hbound : ∀ᶠ N in (atTop : Filter ℕ), ∀ j : ℤ,
      ‖(-1 : ℂ) ^ j * q ^ pentExp5 j * gaussianBinom q N (schurBottom N j)‖
        ≤ bnd j := by
    rw [Filter.eventually_atTop]
    refine ⟨0, fun N _ j => ?_⟩
    simp only [hbnd, norm_mul, norm_zpow, norm_pow, norm_neg, norm_one,
               one_zpow, one_mul]
    by_cases hsb : schurBottom N j ≤ N
    · exact mul_le_mul_of_nonneg_left (hCbnd N (schurBottom N j) hsb)
        (by positivity)
    · have hz : gaussianBinom q N (schurBottom N j) = 0 :=
        PartI.Ch03.gaussianBinom_eq_zero_of_lt q (by omega)
      rw [hz, norm_zero, mul_zero]
      positivity
  have htan := tendsto_tsum_of_dominated_convergence hsum hpt hbound
  have hL : (fun N : ℕ => ∑' j : ℤ,
        (-1 : ℂ) ^ j * q ^ pentExp5 j * gaussianBinom q N (schurBottom N j))
      = fun N : ℕ => schurRHS q N :=
    funext fun N => (schurRHS_eq_tsum q N).symm
  rw [hL] at htan
  have hR : (∑' j : ℤ, (-1 : ℂ) ^ j * q ^ pentExp5 j * (1 / E))
      = (∑' j : ℤ, (-1 : ℂ) ^ j * q ^ pentExp5 j) / E := by
    rw [tsum_mul_right, mul_one_div]
  rw [hR] at htan
  exact htan

/-! ### RR Step 5 step D — final assembly (Rogers-Ramanujan first identity) -/

/-- **Step 1 of the Rogers-Ramanujan proof (h_step1), now UNCONDITIONAL)**:
`rrJInf 1 q · (q;q)_∞ = ∑'_{j:ℤ} (-1)^j q^{j(5j+1)/2}`. Obtained by
equating the limits of the equal sequences `schurSum = schurRHS`. -/
theorem rrJInf_one_mul_eulerPentagonal_eq (q : ℂ) (hq : ‖q‖ < 1) :
    rrJInf 1 q * PartI.Ch04.eulerPentagonalInfiniteProduct q
      = ∑' j : ℤ, (-1 : ℂ) ^ j * q ^ (j * (5 * j + 1) / 2) := by
  set E := PartI.Ch04.eulerPentagonalInfiniteProduct q with hE
  have hE_ne : E ≠ 0 := PartI.Ch04.eulerPentagonalInfiniteProduct_ne_zero q hq
  have heq : (fun N : ℕ => schurSum q N) = fun N : ℕ => schurRHS q N :=
    funext (schurSum_eq_schurRHS q)
  have hL := tendsto_schurSum_rrJInf q hq
  rw [heq] at hL
  have hR := tendsto_schurRHS q hq
  have hlim : rrJInf 1 q
      = (∑' j : ℤ, (-1 : ℂ) ^ j * q ^ pentExp5 j) / E :=
    tendsto_nhds_unique hL hR
  have hpe : (∑' j : ℤ, (-1 : ℂ) ^ j * q ^ pentExp5 j)
      = ∑' j : ℤ, (-1 : ℂ) ^ j * q ^ (j * (5 * j + 1) / 2) := by
    refine tsum_congr fun j => ?_
    congr 1
    simp only [pentExp5]
    rw [← zpow_natCast, Int.toNat_of_nonneg (pent_int_nonneg j)]
  rw [hpe] at hlim
  rw [hlim]
  exact div_mul_cancel₀ _ hE_ne

/-- **Rogers-Ramanujan first identity** (unconditional, `‖q‖<1`, `q≠0`):
`G(q) · (q;q^5)_∞ · (q^4;q^5)_∞ = 1`. Discharges the `h_step1`
hypothesis of `rogersRamanujan_first_given_step1` with the now-proven
`rrJInf_one_mul_eulerPentagonal_eq`. -/
theorem rogersRamanujan_first (q : ℂ) (hq : ‖q‖ < 1) (hq_ne : q ≠ 0) :
    rrJInf 1 q * (∏' n : ℕ, PartI.Ch04.rrMod5Factor q 1 n)
      * (∏' n : ℕ, PartI.Ch04.rrMod5Factor q 4 n) = 1 :=
  rogersRamanujan_first_given_step1 q hq hq_ne
    (rrJInf_one_mul_eulerPentagonal_eq q hq)

end Complex

end Ch07
end PartII
end QseriesFormalization
