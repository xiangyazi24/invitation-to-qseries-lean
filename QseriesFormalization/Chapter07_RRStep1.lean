import QseriesFormalization.Chapter07
import QseriesFormalization.Chapter04

/-!
# Chapter 7 — Rogers-Ramanujan Step 1 (Schur finite identity + Tannery)

Isolated module for the deepest R-R step: the Schur polynomial recurrence,
its identification with the finite Gaussian sum, and the Tannery limit
yielding `rrJInf 1 q · (q;q)_∞ = ∑'_j (-1)^j q^(j(5j+1)/2)`.

See `docs/RR_step1_schur.md`.
-/

namespace QseriesFormalization
namespace PartII
namespace Ch07

section Complex

open Filter Topology

/-- The Rogers-Ramanujan / Schur polynomial `d_N`, defined by the recurrence
`d_N = d_{N-1} + q^(N-1)·d_{N-2}`, `d_0 = d_1 = 1`. -/
noncomputable def rrPoly (q : ℂ) : ℕ → ℂ
  | 0 => 1
  | 1 => 1
  | (N + 2) => rrPoly q (N + 1) + q ^ (N + 1) * rrPoly q N

@[simp] theorem rrPoly_zero (q : ℂ) : rrPoly q 0 = 1 := rfl
@[simp] theorem rrPoly_one (q : ℂ) : rrPoly q 1 = 1 := rfl

/-- The defining recurrence (wrapper for `N + 2`). -/
theorem rrPoly_succ_succ (q : ℂ) (N : ℕ) :
    rrPoly q (N + 2) = rrPoly q (N + 1) + q ^ (N + 1) * rrPoly q N := rfl

/-- Sanity: `d_2 = 1 + q`. -/
theorem rrPoly_two (q : ℂ) : rrPoly q 2 = 1 + q := by
  rw [show (2 : ℕ) = 0 + 2 from rfl, rrPoly_succ_succ]; simp

/-- Sanity: `d_3 = 1 + q + q²`. -/
theorem rrPoly_three (q : ℂ) : rrPoly q 3 = 1 + q + q ^ 2 := by
  rw [show (3 : ℕ) = 1 + 2 from rfl, rrPoly_succ_succ, rrPoly_two]
  simp only [rrPoly_one]; ring

/-- Sanity: `d_4 = 1 + q + q² + q³ + q⁴`. -/
theorem rrPoly_four (q : ℂ) :
    rrPoly q 4 = 1 + q + q ^ 2 + q ^ 3 + q ^ 4 := by
  rw [show (4 : ℕ) = 2 + 2 from rfl, rrPoly_succ_succ, rrPoly_three, rrPoly_two]
  ring

/-- The Schur finite sum `S q N := ∑_{n=0}^{N} q^(n²)·[N-n choose n]_q`. -/
noncomputable def schurSum (q : ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range (N + 1), q ^ (n ^ 2) * gaussianBinom q (N - n) n

/-- `S q 0 = 1`. -/
@[simp] theorem schurSum_zero (q : ℂ) : schurSum q 0 = 1 := by
  simp [schurSum]

/-- `S q 1 = 1`. -/
@[simp] theorem schurSum_one (q : ℂ) : schurSum q 1 = 1 := by
  simp [schurSum, Finset.sum_range_succ, gaussianBinom]

/-- Sanity: `S q 2 = 1 + q`. -/
theorem schurSum_two (q : ℂ) : schurSum q 2 = 1 + q := by
  simp only [schurSum, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [gaussianBinom]

/-- Sanity: `S q 3 = 1 + q + q²`. -/
theorem schurSum_three (q : ℂ) : schurSum q 3 = 1 + q + q ^ 2 := by
  simp only [schurSum, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [gaussianBinom]
  ring

/-! ### Schur recurrence for `schurSum`

The crux of Step 1: `schurSum q (N+2) = schurSum q (N+1) + q^(N+1)·schurSum q N`.

Proof (verified by hand, exponent algebra):

`S q (N+2) = ∑_n q^(n²)·[N+2-n choose n]_q`. Apply gaussianBinom Pascal
(`[m+1 choose k+1]_q = [m choose k+1]_q + q^(m-k)·[m choose k]_q` with
`m=N+1-n, k=n-1`):

`[N+2-n choose n]_q = [N+1-n choose n]_q + q^(N+2-2n)·[N+1-n choose n-1]_q`

So `S q (N+2) = S q (N+1) + ∑_n q^(n²+N+2-2n)·[N+1-n choose n-1]_q`.
Reindex `n = m+1`: `q^((m+1)²+N+2-2(m+1)) = q^(m²+N+1)`, and
`[N+1-(m+1) choose m]_q = [N-m choose m]_q`. So the second sum
`= q^(N+1)·∑_m q^(m²)·[N-m choose m]_q = q^(N+1)·S q N`. ∎

The Lean formalization of this Finset reindex + Pascal split is in
`schurSum_recurrence` (below), and `rrPoly_eq_schurSum` follows by
two-step induction. -/

/-- Pointwise exponent identity for the Schur recurrence's second sum:
`q^((n+1)²+(N-n)-n)·B(N-n,n) = q^(N+1)·q^(n²)·B(N-n,n)`.
Holds for ALL n: if `2n ≤ N` the exponents match; else `B(N-n,n)=0`. -/
private theorem schur_termB_eq (q : ℂ) (N n : ℕ) :
    q ^ ((n + 1) ^ 2 + ((N - n) - n)) * gaussianBinom q (N - n) n =
      q ^ (N + 1) * (q ^ (n ^ 2) * gaussianBinom q (N - n) n) := by
  by_cases h2n : 2 * n ≤ N
  · -- exponents agree: (n+1)² + (N-n-n) = (n+1)² + (N-2n) = n²+2n+1+N-2n = N+1+n²
    have hsub : (N - n) - n = N - 2 * n := by omega
    have hexp : (n + 1) ^ 2 + ((N - n) - n) = (N + 1) + n ^ 2 := by
      rw [hsub]; ring_nf; omega
    rw [hexp, pow_add]
    ring
  · -- 2n > N ⇒ N - n < n ⇒ gaussianBinom q (N-n) n = 0
    have hlt : N - n < n := by omega
    rw [PartI.Ch03.gaussianBinom_eq_zero_of_lt q hlt]
    ring

/-- Per-term Pascal expansion of the `schurSum q (N+2)` summand (for `n+1`,
i.e. after peeling the `n=0` term). For `n ≤ N`:
`q^((n+1)²)·B(N+1-n, n+1) = q^((n+1)²)·B(N-n,n+1) + q^(N+1)·q^(n²)·B(N-n,n)`. -/
private theorem schur_pascal_term (q : ℂ) (N n : ℕ) (hn : n ≤ N) :
    q ^ ((n + 1) ^ 2) * gaussianBinom q (N + 1 - n) (n + 1) =
      q ^ ((n + 1) ^ 2) * gaussianBinom q (N - n) (n + 1) +
      q ^ (N + 1) * (q ^ (n ^ 2) * gaussianBinom q (N - n) n) := by
  have hNn : N + 1 - n = (N - n) + 1 := by omega
  rw [hNn]
  -- gaussianBinom q ((N-n)+1) (n+1) = B(N-n, n+1) + q^((N-n)-n)·B(N-n, n)  [def Pascal]
  show q ^ ((n + 1) ^ 2) *
      (gaussianBinom q (N - n) (n + 1) + q ^ ((N - n) - n) * gaussianBinom q (N - n) n) = _
  rw [mul_add]
  congr 1
  rw [← mul_assoc, ← pow_add]
  exact schur_termB_eq q N n

/-- **The Schur recurrence**: `schurSum q (N+2) = schurSum q (N+1) + q^(N+1)·schurSum q N`. -/
theorem schurSum_recurrence (q : ℂ) (N : ℕ) :
    schurSum q (N + 2) = schurSum q (N + 1) + q ^ (N + 1) * schurSum q N := by
  -- schurSum q (N+2) = ∑ n ∈ range(N+3), q^(n²)·B(N+2-n, n).
  -- Peel n=0: = B(N+2,0) + ∑ n ∈ range(N+2), q^((n+1)²)·B(N+1-n, n+1).
  rw [schurSum, Finset.sum_range_succ']
  simp only [Nat.zero_eq, pow_zero, one_mul, Nat.sub_zero, gaussianBinom_zero_right]
  -- Drop the n = N+1 term in range(N+2) (it's 0): B(N+1-(N+1), (N+1)+1) = B(0, N+2) = 0.
  rw [Finset.sum_range_succ]
  have h_last_zero :
      q ^ ((N + 1 + 1) ^ 2) * gaussianBinom q (N + 2 - (N + 1 + 1)) (N + 1 + 1) = 0 := by
    have : N + 2 - (N + 1 + 1) = 0 := by omega
    rw [this]
    rw [PartI.Ch03.gaussianBinom_eq_zero_of_lt q (by omega : (0 : ℕ) < N + 1 + 1)]
    ring
  rw [h_last_zero, add_zero]
  -- Now: 1 + ∑ n ∈ range(N+1), q^((n+1)²)·B(N+2-(n+1), n+1)
  --    = schurSum q (N+1) + q^(N+1)·schurSum q N.
  -- B(N+2-(n+1), n+1) = B(N+1-n, n+1). Apply schur_pascal_term (n ≤ N).
  have h_sum_eq :
      ∑ n ∈ Finset.range (N + 1),
          q ^ ((n + 1) ^ 2) * gaussianBinom q (N + 2 - (n + 1)) (n + 1) =
      (∑ n ∈ Finset.range (N + 1),
          q ^ ((n + 1) ^ 2) * gaussianBinom q (N - n) (n + 1)) +
      q ^ (N + 1) *
        (∑ n ∈ Finset.range (N + 1), q ^ (n ^ 2) * gaussianBinom q (N - n) n) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn' : n ≤ N := by
      simp only [Finset.mem_range] at hn; omega
    have hNn2 : N + 2 - (n + 1) = N + 1 - n := by omega
    rw [hNn2]
    rw [schur_pascal_term q N n hn']
  rw [h_sum_eq]
  -- The first sum reindexed = schurSum q (N+1) - 1; the second = schurSum q N.
  -- schurSum q (N+1) = ∑ m ∈ range(N+2), q^(m²)·B(N+1-m, m)
  --   = 1 + ∑ n ∈ range(N+1), q^((n+1)²)·B(N+1-(n+1), n+1)
  --   = 1 + ∑ n ∈ range(N+1), q^((n+1)²)·B(N-n, n+1)
  have h_sN1 :
      schurSum q (N + 1) =
        1 + ∑ n ∈ Finset.range (N + 1),
              q ^ ((n + 1) ^ 2) * gaussianBinom q (N - n) (n + 1) := by
    rw [schurSum, Finset.sum_range_succ']
    have h0 : q ^ ((0 : ℕ) ^ 2) * gaussianBinom q (N + 1 - 0) 0 = 1 := by
      simp
    rw [h0, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn' : n ≤ N := by simp only [Finset.mem_range] at hn; omega
    congr 2
    omega
  have h_sN : schurSum q N = ∑ n ∈ Finset.range (N + 1), q ^ (n ^ 2) * gaussianBinom q (N - n) n :=
    rfl
  rw [h_sN1, h_sN]
  ring

/-- **General reduction**: any `f` matching the RR recurrence + base cases
equals `rrPoly`. Reusable for both `schurSum` and `schurRHS`. -/
theorem rrPoly_eq_of_recurrence (q : ℂ) (f : ℕ → ℂ)
    (h0 : f 0 = 1) (h1 : f 1 = 1)
    (h_rec : ∀ N : ℕ, f (N + 2) = f (N + 1) + q ^ (N + 1) * f N) :
    ∀ N : ℕ, rrPoly q N = f N := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    match N with
    | 0 => simp [h0]
    | 1 => simp [h1]
    | (M + 2) =>
      rw [rrPoly_succ_succ, h_rec M, ih (M + 1) (by omega), ih M (by omega)]

/-- Once the Schur recurrence is available, `rrPoly = schurSum` follows. -/
theorem rrPoly_eq_schurSum_of_recurrence (q : ℂ)
    (h_rec : ∀ N : ℕ, schurSum q (N + 2) =
      schurSum q (N + 1) + q ^ (N + 1) * schurSum q N) :
    ∀ N : ℕ, rrPoly q N = schurSum q N :=
  rrPoly_eq_of_recurrence q (schurSum q) (schurSum_zero q) (schurSum_one q) h_rec

/-- `schurSum` as a `tsum` over all `ℕ` (tail vanishes: for `n ≥ N+1`,
`N - n = 0` and `gaussianBinom q 0 n = 0`). Needed for the Tannery LHS. -/
theorem schurSum_eq_tsum (q : ℂ) (N : ℕ) :
    schurSum q N = ∑' n : ℕ, q ^ (n ^ 2) * gaussianBinom q (N - n) n := by
  rw [schurSum]
  refine (tsum_eq_sum (s := Finset.range (N + 1)) ?_).symm
  intro n hn
  rw [Finset.mem_range, not_lt] at hn
  -- n ≥ N+1 ⇒ N - n = 0 ⇒ gaussianBinom q 0 n = 0 (n ≥ 1).
  have hNsub : N - n = 0 := by omega
  rw [hNsub]
  have hn1 : 1 ≤ n := by omega
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp [gaussianBinom]

/-- **The Schur LHS identity**: `rrPoly q N = ∑_{n} q^(n²)·[N-n choose n]_q`.
The Rogers-Ramanujan polynomial equals the Schur finite Gaussian sum. -/
theorem rrPoly_eq_schurSum (q : ℂ) (N : ℕ) : rrPoly q N = schurSum q N :=
  rrPoly_eq_schurSum_of_recurrence q (schurSum_recurrence q) N

/-! ### Tannery LHS — pointwise gaussianBinom limit -/

/-- `qPochhammer q (N - c) → (q;q)_∞` as `N → ∞` (shift by a constant). -/
private theorem tendsto_qPochhammer_sub_const (q : ℂ) (hq : ‖q‖ < 1) (c : ℕ) :
    Tendsto (fun N : ℕ => qPochhammer q (N - c)) atTop
      (𝓝 (PartI.Ch04.eulerPentagonalInfiniteProduct q)) := by
  have h_main := PartI.Ch04.tendsto_eulerPentagonalProductTrunc q hq
  have h_sub : Tendsto (fun N : ℕ => N - c) atTop atTop :=
    Filter.tendsto_atTop_atTop.mpr fun b => ⟨b + c, fun n hn => by omega⟩
  exact h_main.comp h_sub

/-- Pointwise limit: `gaussianBinom q (N-n) n → 1/qPochhammer q n` as `N → ∞`. -/
theorem tendsto_gaussianBinom_sub (q : ℂ) (hq : ‖q‖ < 1) (n : ℕ) :
    Tendsto (fun N : ℕ => gaussianBinom q (N - n) n) atTop
      (𝓝 (1 / qPochhammer q n)) := by
  -- For N ≥ 2n: gaussianBinom q (N-n) n · qPoch q n · qPoch q ((N-n)-n) = qPoch q (N-n).
  -- So gaussianBinom q (N-n) n = qPoch q (N-n) / (qPoch q n · qPoch q (N-2n)).
  set E := PartI.Ch04.eulerPentagonalInfiniteProduct q with hE
  have hE_ne : E ≠ 0 := PartI.Ch04.eulerPentagonalInfiniteProduct_ne_zero q hq
  have hpn_ne : qPochhammer q n ≠ 0 :=
    qPochhammer_ne_zero_of_norm_lt_one q hq n
  -- Target limit value: E / (qPoch q n · E) = 1/qPoch q n.
  have h_target : (1 : ℂ) / qPochhammer q n = E / (qPochhammer q n * E) := by
    field_simp
  rw [h_target]
  -- Numerator → E, denominator → qPoch q n · E (nonzero), so ratio → E/(qPoch q n · E).
  have h_num : Tendsto (fun N : ℕ => qPochhammer q (N - n)) atTop (𝓝 E) :=
    tendsto_qPochhammer_sub_const q hq n
  have h_den : Tendsto (fun N : ℕ => qPochhammer q n * qPochhammer q (N - 2 * n))
      atTop (𝓝 (qPochhammer q n * E)) :=
    tendsto_const_nhds.mul (tendsto_qPochhammer_sub_const q hq (2 * n))
  have h_den_ne : qPochhammer q n * E ≠ 0 := mul_ne_zero hpn_ne hE_ne
  have h_ratio :
      Tendsto (fun N : ℕ =>
        qPochhammer q (N - n) / (qPochhammer q n * qPochhammer q (N - 2 * n)))
        atTop (𝓝 (E / (qPochhammer q n * E))) :=
    h_num.div h_den h_den_ne
  refine h_ratio.congr' ?_
  -- Eventually (N ≥ 2n): gaussianBinom = the ratio (closed form).
  filter_upwards [Filter.eventually_atTop.mpr ⟨2 * n, fun N hN => hN⟩] with N hN
  have hle : n ≤ N - n := by omega
  have hclosed := PartI.Ch03.gaussianBinom_mul_qPochhammer_eq q (N - n) n hle
  have hsub2 : (N - n) - n = N - 2 * n := by omega
  rw [hsub2] at hclosed
  -- gaussianBinom q (N-n) n = qPoch q (N-n) / (qPoch q n · qPoch q (N-2n))
  have hpn2_ne : qPochhammer q (N - 2 * n) ≠ 0 :=
    qPochhammer_ne_zero_of_norm_lt_one q hq (N - 2 * n)
  rw [div_eq_iff (mul_ne_zero hpn_ne hpn2_ne)]
  linear_combination -hclosed

/-! ### Schur RHS — parity-split theta-Gaussian finite sum (FORM UNRESOLVED)

**Sanity-check failure (2026-05-15)**: the naively-stated Schur RHS form

`d_{2M} = ∑_{j=-M}^{M} (-1)^j q^(j(5j+1)/2) [2M choose M-j]_q`

does NOT satisfy `d_2 = 1 + q`. Direct computation at `M=1` (j ∈ {-1,0,1}):
`(-1)·q²·[2,2] + 1·q⁰·[2,1] + (-1)·q³·[2,0] = -q² + (1+q) - q³`,
which is `1+q-q²-q³ ≠ 1+q = rrPoly q 2 = schurSum q 2` (both proven above).

So a convention is off: the bottom index is likely `⌊(N-5j)/2⌋` (with `5j`,
not `2j`), OR the polynomial is the H-type `∑ q^(n²+n)[…]`, OR the exponent
differs. This requires a careful literature reference (Andrews,
*The Theory of Partitions*, Thm 7.x; or Sills, *An Invitation to the
Rogers–Ramanujan Identities*) and must NOT be guessed.

**Generalized pentagonal helper** (correct & reusable regardless of the
final bottom-index convention): -/

/-- `j(5j+1)` is even, so `j(5j+1)/2` is exact (generalized pentagonal). -/
theorem two_dvd_j_5j_add_one (j : ℤ) : (2 : ℤ) ∣ j * (5 * j + 1) := by
  rcases Int.even_or_odd j with ⟨m, hm⟩ | ⟨m, hm⟩
  · exact ⟨m * (5 * j + 1), by rw [hm]; ring⟩
  · exact ⟨j * (5 * m + 3), by rw [hm]; ring⟩

/-- Generalized pentagonal exponent `j(5j+1)/2` as a `ℕ` (always `≥ 0`). -/
noncomputable def pentExp5 (j : ℤ) : ℕ := (j * (5 * j + 1) / 2).toNat

/-- The pentagonal exponent is always nonnegative: `0 ≤ j(5j+1)/2`. -/
theorem pent_int_nonneg (j : ℤ) : 0 ≤ j * (5 * j + 1) / 2 := by
  have hdvd := two_dvd_j_5j_add_one j
  have hprod : 0 ≤ j * (5 * j + 1) := by nlinarith [sq_nonneg j, sq_nonneg (j + 1)]
  omega

/-- **Core pentagonal recurrence** (ChatGPT structure): `P_j - P_{j-1} = 5j - 2`,
i.e. `j(5j+1)/2 = (j-1)(5(j-1)+1)/2 + (5j-2)`. -/
theorem pent_int_succ (j : ℤ) :
    j * (5 * j + 1) / 2 = (j - 1) * (5 * (j - 1) + 1) / 2 + (5 * j - 2) := by
  -- Pure-ring: j(5j+1) = (j-1)(5(j-1)+1) + 2(5j-2); then divide (both even).
  have hring : j * (5 * j + 1) = (j - 1) * (5 * (j - 1) + 1) + 2 * (5 * j - 2) := by ring
  have hd1 := two_dvd_j_5j_add_one j
  have hd2 := two_dvd_j_5j_add_one (j - 1)
  omega

/-- `pentExp5` form of the core recurrence (as `ℕ`, valid since all `≥ 0`). -/
theorem pentExp5_succ (j : ℤ) (hj : 2 ≤ 5 * j) :
    (pentExp5 j : ℤ) = (pentExp5 (j - 1) : ℤ) + (5 * j - 2) := by
  simp only [pentExp5]
  rw [Int.toNat_of_nonneg (pent_int_nonneg j),
      Int.toNat_of_nonneg (pent_int_nonneg (j - 1))]
  have h := pent_int_succ j
  omega

/-- Schur bottom index `⌊(n-5j)/2⌋` as a `ℕ`. When `n-5j < 0` we return
`n+1` (out of `[0,n]`, so `gaussianBinom q n (n+1) = 0` — the term vanishes,
matching the true identity where these `j` contribute nothing). For
`n-5j ≥ 0`, `((n-5j)/2 : ℤ).toNat` is the exact floor. -/
noncomputable def schurBottom (n : ℕ) (j : ℤ) : ℕ :=
  if (n : ℤ) - 5 * j < 0 then n + 1
  else (((n : ℤ) - 5 * j) / 2).toNat

/-- Zero-extended integer-bottom Gaussian binomial (ChatGPT-recommended
wrapper for the Schur reindex): `0` when `k ∉ [0, n]`, else `[n choose k]_q`. -/
noncomputable def gBz (q : ℂ) (n : ℕ) (k : ℤ) : ℂ :=
  if 0 ≤ k ∧ k ≤ (n : ℤ) then gaussianBinom q n k.toNat else 0

/-- `gBz` vanishes for negative bottom. -/
@[simp] theorem gBz_neg (q : ℂ) (n : ℕ) (k : ℤ) (hk : k < 0) : gBz q n k = 0 := by
  simp only [gBz]; rw [if_neg]; omega

/-- `gBz` vanishes for bottom exceeding `n`. -/
@[simp] theorem gBz_gt (q : ℂ) (n : ℕ) (k : ℤ) (hk : (n : ℤ) < k) : gBz q n k = 0 := by
  simp only [gBz]; rw [if_neg]; omega

/-- `gBz` equals the ordinary Gaussian when the bottom is in range. -/
theorem gBz_eq (q : ℂ) (n : ℕ) (k : ℤ) (h0 : 0 ≤ k) (hn : k ≤ (n : ℤ)) :
    gBz q n k = gaussianBinom q n k.toNat := by
  simp only [gBz]; rw [if_pos ⟨h0, hn⟩]

/-- `gBz` with a `ℕ` bottom (coerced) is just `gaussianBinom` when `k ≤ n`,
and the codebase's `gaussianBinom_eq_zero_of_lt` covers `k > n`. -/
theorem gBz_natCast (q : ℂ) (n k : ℕ) :
    gBz q n (k : ℤ) = gaussianBinom q n k := by
  by_cases hkn : k ≤ n
  · rw [gBz_eq q n (k : ℤ) (by positivity) (by exact_mod_cast hkn)]
    simp
  · rw [gBz_gt q n (k : ℤ) (by exact_mod_cast (by omega : n < k))]
    rw [PartI.Ch03.gaussianBinom_eq_zero_of_lt q (by omega : n < k)]

/-- The Schur RHS theta-Gaussian finite sum:
`∑_{j} (-1)^j q^(j(5j+1)/2) · [n choose ⌊(n-5j)/2⌋]_q`,
summed over `j ∈ [-(n+1), n+1]` (finite support; outside, the Gaussian is 0). -/
noncomputable def schurRHS (q : ℂ) (n : ℕ) : ℂ :=
  ∑ j ∈ Finset.Icc (-(n : ℤ) - 1) ((n : ℤ) + 1),
    (-1 : ℂ) ^ j * q ^ pentExp5 j * gaussianBinom q n (schurBottom n j)

/-- `schurRHS` via the `gBz` wrapper (reindex-friendly: clean `ℤ` arithmetic). -/
noncomputable def schurRHSz (q : ℂ) (n : ℕ) : ℂ :=
  ∑ j ∈ Finset.Icc (-(n : ℤ) - 1) ((n : ℤ) + 1),
    (-1 : ℂ) ^ j * q ^ pentExp5 j * gBz q n ((schurBottom n j : ℤ))

/-- The two `schurRHS` formulations agree (per-`j`: `gBz_natCast`). -/
theorem schurRHS_eq_schurRHSz (q : ℂ) (n : ℕ) : schurRHS q n = schurRHSz q n := by
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [gBz_natCast]

/-- ℕ-level lower q-Pascal (from the defining recursion):
`[n+2 choose m]_q = [n+1 choose m]_q + q^(n+2-m)·[n+1 choose m-1]_q` for `1 ≤ m ≤ n+1`. -/
theorem gaussianBinom_lower_pascal (q : ℂ) (n m : ℕ) (hm1 : 1 ≤ m) (hmn : m ≤ n + 1) :
    gaussianBinom q (n + 2) m =
      gaussianBinom q (n + 1) m + q ^ (n + 2 - m) * gaussianBinom q (n + 1) (m - 1) := by
  obtain ⟨l, rfl⟩ : ∃ l, m = l + 1 := ⟨m - 1, by omega⟩
  have hln : l ≤ n := by omega
  -- gaussianBinom q ((n+1)+1) (l+1) = gaussianBinom q (n+1) (l+1) + q^((n+1)-l)·gaussianBinom q (n+1) l
  have hdef : gaussianBinom q ((n + 1) + 1) (l + 1) =
        gaussianBinom q (n + 1) (l + 1) + q ^ ((n + 1) - l) * gaussianBinom q (n + 1) l := rfl
  have he1 : (n + 2 - (l + 1)) = (n + 1) - l := by omega
  have he2 : (l + 1) - 1 = l := by omega
  show gaussianBinom q ((n + 1) + 1) (l + 1) =
        gaussianBinom q (n + 1) (l + 1) + q ^ (n + 2 - (l + 1)) * gaussianBinom q (n + 1) ((l+1)-1)
  rw [hdef, he1, he2]

/-- `gBz`-level lower q-Pascal for integer bottom `k`, `1 ≤ k ≤ n+1`:
`gBz q (n+2) k = gBz q (n+1) k + q^((n+2-k).toNat)·gBz q (n+1) (k-1)`. -/
theorem gBz_lower_pascal (q : ℂ) (n : ℕ) (k : ℤ) (hk1 : 1 ≤ k) (hkn : k ≤ (n : ℤ) + 1) :
    gBz q (n + 2) k =
      gBz q (n + 1) k + q ^ ((n : ℤ) + 2 - k).toNat * gBz q (n + 1) (k - 1) := by
  have hk0 : 0 ≤ k := by omega
  set m : ℕ := k.toNat with hm
  have hmk : (m : ℤ) = k := Int.toNat_of_nonneg hk0
  have hm1 : 1 ≤ m := by omega
  have hmn : m ≤ n + 1 := by omega
  -- gBz at (n+2) k = gaussianBinom q (n+2) m (since 0 ≤ k ≤ n+2)
  rw [gBz_eq q (n + 2) k hk0 (by push_cast; omega)]
  rw [gBz_eq q (n + 1) k hk0 (by push_cast; omega)]
  rw [gBz_eq q (n + 1) (k - 1) (by omega) (by push_cast; omega)]
  -- k.toNat = m, (k-1).toNat = m-1, (n+2-k).toNat = n+2-m
  have e1 : k.toNat = m := rfl
  have e2 : (k - 1).toNat = m - 1 := by omega
  have e3 : ((n : ℤ) + 2 - k).toNat = n + 2 - m := by omega
  rw [e1, e2, e3]
  exact gaussianBinom_lower_pascal q n m hm1 hmn

/-- Sanity: `schurRHS q 0 = 1`. Only `j=0`: `[0 choose 0]_q = 1`. -/
theorem schurRHS_zero (q : ℂ) : schurRHS q 0 = 1 := by
  have hset : Finset.Icc (-(((0 : ℕ) : ℤ)) - 1) (((0 : ℕ) : ℤ) + 1) =
      ({-1, 0, 1} : Finset ℤ) := by decide
  rw [schurRHS, hset]
  norm_num [Finset.sum_insert, Finset.mem_insert, pentExp5, schurBottom,
    gaussianBinom, Int.fdiv]

/-- Sanity: `schurRHS q 2 = 1 + q = rrPoly q 2`. -/
theorem schurRHS_two (q : ℂ) : schurRHS q 2 = 1 + q := by
  have hset : Finset.Icc (-(((2 : ℕ) : ℤ)) - 1) (((2 : ℕ) : ℤ) + 1) =
      ({-3, -2, -1, 0, 1, 2, 3} : Finset ℤ) := by decide
  rw [schurRHS, hset]
  norm_num [Finset.sum_insert, Finset.mem_insert, pentExp5, schurBottom,
    gaussianBinom, Int.fdiv]

/-- Sanity: `schurRHS q 3 = 1 + q + q^2 = rrPoly q 3`. -/
theorem schurRHS_three (q : ℂ) : schurRHS q 3 = 1 + q + q ^ 2 := by
  have hset : Finset.Icc (-(((3 : ℕ) : ℤ)) - 1) (((3 : ℕ) : ℤ) + 1) =
      ({-4, -3, -2, -1, 0, 1, 2, 3, 4} : Finset ℤ) := by decide
  rw [schurRHS, hset]
  norm_num [Finset.sum_insert, Finset.mem_insert, pentExp5, schurBottom,
    gaussianBinom, Int.fdiv]

/-- Sanity: `schurRHS q 1 = 1 = rrPoly q 1`. -/
theorem schurRHS_one (q : ℂ) : schurRHS q 1 = 1 := by
  have hset : Finset.Icc (-(((1 : ℕ) : ℤ)) - 1) (((1 : ℕ) : ℤ) + 1) =
      ({-2, -1, 0, 1, 2} : Finset ℤ) := by decide
  rw [schurRHS, hset]
  norm_num [Finset.sum_insert, Finset.mem_insert, pentExp5, schurBottom,
    gaussianBinom, Int.fdiv]

/-! ### Schur recurrence via carry-telescope (ChatGPT extended-pro skeleton) -/

/-- Raw integer floor bottom `⌊(n-5j)/2⌋` (no `if`, clean ℤ arithmetic). -/
private noncomputable def schurB (n : ℕ) (j : ℤ) : ℤ :=
  ((n : ℤ) - 5 * j) / 2

/-- `schurRHSz` term with the raw floor bottom. -/
private noncomputable def schurTermZ' (q : ℂ) (n : ℕ) (j : ℤ) : ℂ :=
  (-1 : ℂ) ^ j * q ^ pentExp5 j * gBz q n (schurB n j)

/-- `gBz` at `schurBottom` equals `gBz` at the raw floor `schurB`
(both `0` in the out-of-range branch). -/
private lemma gBz_schurBottom_eq_floor (q : ℂ) (n : ℕ) (j : ℤ) :
    gBz q n ((schurBottom n j : ℤ)) = gBz q n (schurB n j) := by
  unfold schurBottom schurB
  by_cases h : (n : ℤ) - 5 * j < 0
  · rw [if_pos h]
    rw [gBz_gt q n ((n + 1 : ℕ) : ℤ) (by push_cast; omega)]
    rw [gBz_neg q n _ (by omega)]
  · rw [if_neg h]
    have hnonneg : 0 ≤ ((n : ℤ) - 5 * j) / 2 := by omega
    rw [Int.toNat_of_nonneg hnonneg]

/-- `schurRHSz` rewritten with the raw-floor term. -/
private lemma schurRHSz_floor (q : ℂ) (n : ℕ) :
    schurRHSz q n =
      ∑ j ∈ Finset.Icc (-(n : ℤ) - 1) ((n : ℤ) + 1), schurTermZ' q n j := by
  unfold schurRHSz schurTermZ'
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [gBz_schurBottom_eq_floor]

/-- Common reindex range (wide enough for `N`, `N+1`, `N+2`). -/
private def bigJ (N : ℕ) : Finset ℤ :=
  Finset.Icc (-(N : ℤ) - 3) ((N : ℤ) + 3)

/-- Left out-of-range terms vanish (`schurB` exceeds `n`). -/
private lemma schurTermZ'_left_zero (q : ℂ) (n : ℕ) (j : ℤ)
    (hj : j < -(n : ℤ) - 1) :
    schurTermZ' q n j = 0 := by
  unfold schurTermZ' schurB
  rw [gBz_gt q n _ (by omega)]
  ring

/-- Right out-of-range terms vanish (`schurB` negative). -/
private lemma schurTermZ'_right_zero (q : ℂ) (n : ℕ) (j : ℤ)
    (hj : (n : ℤ) + 1 < j) :
    schurTermZ' q n j = 0 := by
  unfold schurTermZ' schurB
  rw [gBz_neg q n _ (by omega)]
  ring

/-- Normalize `schurRHSz q n` to the common `bigJ N` range, for any
`N ≤ n ≤ N+2` (out-of-range terms are zero). -/
private lemma schurRHSz_common_range (q : ℂ) (N n : ℕ)
    (hn₁ : N ≤ n) (hn₂ : n ≤ N + 2) :
    schurRHSz q n = ∑ j ∈ bigJ N, schurTermZ' q n j := by
  rw [schurRHSz_floor]
  refine Finset.sum_subset ?_ ?_
  · intro j hj
    simp only [bigJ, Finset.mem_Icc] at hj ⊢
    omega
  · intro j _ hjSmall
    simp only [Finset.mem_Icc, not_and, not_le] at hjSmall
    by_cases hlo : -(n : ℤ) - 1 ≤ j
    · exact schurTermZ'_right_zero q n j (by have := hjSmall hlo; omega)
    · exact schurTermZ'_left_zero q n j (by omega)

/-! #### Unconditional single-step q-Pascal (via gBz zero-extension) -/

/-- `gBz q n 0 = 1`. -/
private lemma gBz_zero_right (q : ℂ) (n : ℕ) : gBz q n 0 = 1 := by
  simp [gBz]

/-- Single-step **lower** q-Pascal, all integer `k`:
`gBz (n+1) k = gBz n k + q^(n+1-k) · gBz n (k-1)`. -/
private theorem gBz_lower1 (q : ℂ) (n : ℕ) (k : ℤ) :
    gBz q (n + 1) k =
      gBz q n k + q ^ ((n : ℤ) + 1 - k).toNat * gBz q n (k - 1) := by
  rcases lt_trichotomy k 0 with hk | hk | hk
  · rw [gBz_neg q (n + 1) k hk, gBz_neg q n k hk, gBz_neg q n (k - 1) (by omega)]
    ring
  · subst hk
    rw [gBz_zero_right, gBz_zero_right, gBz_neg q n ((0 : ℤ) - 1) (by norm_num)]
    ring
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = (m : ℤ) :=
      ⟨k.toNat, (Int.toNat_of_nonneg hk.le).symm⟩
    have hm : 1 ≤ m := by exact_mod_cast hk
    obtain ⟨l, rfl⟩ : ∃ l, m = l + 1 := ⟨m - 1, by omega⟩
    rw [show ((l + 1 : ℕ) : ℤ) - 1 = ((l : ℕ) : ℤ) by push_cast; ring,
        gBz_natCast, gBz_natCast, gBz_natCast]
    by_cases hln : l + 1 ≤ n
    · have hrec : gaussianBinom q (n + 1) (l + 1) =
          gaussianBinom q n (l + 1) + q ^ (n - l) * gaussianBinom q n l := rfl
      rw [hrec,
          show ((n : ℤ) + 1 - ((l + 1 : ℕ) : ℤ)).toNat = n - l by push_cast; omega]
    · by_cases hnl : n = l
      · rw [← hnl, PartI.Ch03.gaussianBinom_self, PartI.Ch03.gaussianBinom_self,
            PartI.Ch03.gaussianBinom_eq_zero_of_lt q (Nat.lt_succ_self n),
            show ((n : ℤ) + 1 - ((n + 1 : ℕ) : ℤ)).toNat = 0 by push_cast; omega]
        ring
      · rw [PartI.Ch03.gaussianBinom_eq_zero_of_lt q (show n + 1 < l + 1 by omega),
            PartI.Ch03.gaussianBinom_eq_zero_of_lt q (show n < l + 1 by omega),
            PartI.Ch03.gaussianBinom_eq_zero_of_lt q (show n < l by omega)]
        ring

/-- Single-step **upper** q-Pascal, all integer `k`:
`gBz (n+1) k = q^k · gBz n k + gBz n (k-1)`. -/
private theorem gBz_upper1 (q : ℂ) (n : ℕ) (k : ℤ) :
    gBz q (n + 1) k = q ^ k.toNat * gBz q n k + gBz q n (k - 1) := by
  rcases lt_trichotomy k 0 with hk | hk | hk
  · rw [gBz_neg q (n + 1) k hk, gBz_neg q n k hk, gBz_neg q n (k - 1) (by omega)]
    ring
  · subst hk
    rw [gBz_zero_right, gBz_zero_right, gBz_neg q n ((0 : ℤ) - 1) (by norm_num)]
    simp
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = (m : ℤ) :=
      ⟨k.toNat, (Int.toNat_of_nonneg hk.le).symm⟩
    have hm : 1 ≤ m := by exact_mod_cast hk
    obtain ⟨l, rfl⟩ : ∃ l, m = l + 1 := ⟨m - 1, by omega⟩
    rw [Int.toNat_natCast,
        show ((l + 1 : ℕ) : ℤ) - 1 = ((l : ℕ) : ℤ) by push_cast; ring,
        gBz_natCast, gBz_natCast, gBz_natCast]
    by_cases hln : l + 1 ≤ n
    · exact PartI.Ch03.gaussianBinom_pascal_alt q n l (by omega)
    · by_cases hnl : n = l
      · rw [← hnl, PartI.Ch03.gaussianBinom_self, PartI.Ch03.gaussianBinom_self,
            PartI.Ch03.gaussianBinom_eq_zero_of_lt q (Nat.lt_succ_self n)]
        ring
      · rw [PartI.Ch03.gaussianBinom_eq_zero_of_lt q (show n + 1 < l + 1 by omega),
            PartI.Ch03.gaussianBinom_eq_zero_of_lt q (show n < l + 1 by omega),
            PartI.Ch03.gaussianBinom_eq_zero_of_lt q (show n < l by omega)]
        ring

/-! #### Local q-binomial residual identities (Schur 1917 combinatorial core)

Two-Pascal-step cancellation: `gBz(N+2)(b+1)` reduced via one upper and one
lower single-step q-Pascal, with the cross term killed because either the
`toNat` exponents sum to `N+1` (when `0 ≤ b ≤ N`) or `gBz q N b = 0`. -/

/-- Even-parity residual (`B_{N+1}=B_N`). -/
theorem gBz_even_residual (q : ℂ) (N : ℕ) (b : ℤ) :
    gBz q (N + 2) (b + 1) - gBz q (N + 1) b - q ^ (N + 1) * gBz q N b
      = q ^ (b + 1).toNat * gBz q N (b + 1) := by
  have hN2 : N + 1 + 1 = N + 2 := by omega
  have hup := gBz_upper1 q (N + 1) (b + 1)
  rw [hN2, show (b + 1 : ℤ) - 1 = b from by ring] at hup
  have hlo := gBz_lower1 q N (b + 1)
  rw [show (b + 1 : ℤ) - 1 = b from by ring] at hlo
  have hkill2 :
      q ^ (b + 1).toNat * (q ^ ((N : ℤ) + 1 - (b + 1)).toNat * gBz q N b)
        = q ^ (N + 1) * gBz q N b := by
    by_cases hb : 0 ≤ b ∧ b ≤ (N : ℤ)
    · obtain ⟨hb0, hbN⟩ := hb
      have he : (b + 1).toNat + ((N : ℤ) + 1 - (b + 1)).toNat = N + 1 := by omega
      rw [← mul_assoc, ← pow_add, he]
    · have hz : gBz q N b = 0 := by
        rcases not_and_or.mp hb with h | h
        · exact gBz_neg q N b (by omega)
        · exact gBz_gt q N b (by omega)
      rw [hz]; ring
  rw [hup, hlo, mul_add, hkill2]
  ring

/-- Odd-parity residual (`B_{N+1}=B_N+1`). -/
theorem gBz_odd_residual (q : ℂ) (N : ℕ) (b : ℤ) :
    gBz q (N + 2) (b + 1) - gBz q (N + 1) (b + 1) - q ^ (N + 1) * gBz q N b
      = q ^ ((N : ℤ) + 1 - b).toNat * gBz q N (b - 1) := by
  have hN2 : N + 1 + 1 = N + 2 := by omega
  have hexp : ((N + 1 : ℕ) : ℤ) + 1 - (b + 1) = (N : ℤ) + 1 - b := by push_cast; ring
  have hlo2 := gBz_lower1 q (N + 1) (b + 1)
  rw [hN2, show (b + 1 : ℤ) - 1 = b from by ring, hexp] at hlo2
  have hup2 := gBz_upper1 q N b
  have hkill2 :
      q ^ ((N : ℤ) + 1 - b).toNat * (q ^ b.toNat * gBz q N b)
        = q ^ (N + 1) * gBz q N b := by
    by_cases hb : 0 ≤ b ∧ b ≤ (N : ℤ)
    · obtain ⟨hb0, hbN⟩ := hb
      have he : ((N : ℤ) + 1 - b).toNat + b.toNat = N + 1 := by omega
      rw [← mul_assoc, ← pow_add, he]
    · have hz : gBz q N b = 0 := by
        rcases not_and_or.mp hb with h | h
        · exact gBz_neg q N b (by omega)
        · exact gBz_gt q N b (by omega)
      rw [hz]; ring
  rw [hlo2, hup2, mul_add, hkill2]
  ring

/-- **Schur's identity** reduced to its recurrence: GIVEN that `schurRHS`
satisfies the RR recurrence, `rrPoly q N = schurRHS q N`. The hypothesis
`schurRHS_recurrence` is Schur's 1917 theorem (pentagonal reindex `j↦j±1`
in the q-Pascal split) — the remaining hard piece. -/
theorem rrPoly_eq_schurRHS_of_recurrence (q : ℂ)
    (h_rec : ∀ N : ℕ, schurRHS q (N + 2) =
      schurRHS q (N + 1) + q ^ (N + 1) * schurRHS q N) :
    ∀ N : ℕ, rrPoly q N = schurRHS q N :=
  rrPoly_eq_of_recurrence q (schurRHS q) (schurRHS_zero q) (schurRHS_one q) h_rec

/-- **Schur LHS = RHS** (conditional): given the `schurRHS` recurrence,
`schurSum q N = schurRHS q N` — i.e. the finite Rogers-Ramanujan /
Schur identity `∑_n q^(n²)[N-n choose n]_q = ∑_j (-1)^j q^(j(5j+1)/2)[N choose ⌊(N-5j)/2⌋]_q`. -/
theorem schurSum_eq_schurRHS_of_recurrence (q : ℂ)
    (h_rec : ∀ N : ℕ, schurRHS q (N + 2) =
      schurRHS q (N + 1) + q ^ (N + 1) * schurRHS q N) (N : ℕ) :
    schurSum q N = schurRHS q N := by
  rw [← rrPoly_eq_schurSum q N, rrPoly_eq_schurRHS_of_recurrence q h_rec N]

/-! #### Carry-telescope proof of the Schur recurrence (unconditional) -/

/-- Per-`j` residual of the RR recurrence (with the raw-floor term). -/
private noncomputable def schurResidual (q : ℂ) (N : ℕ) (j : ℤ) : ℂ :=
  schurTermZ' q (N + 2) j - schurTermZ' q (N + 1) j
    - q ^ (N + 1) * schurTermZ' q N j

/-- Telescoping carry: nonzero only on the even-parity residues. -/
private noncomputable def schurCarry (q : ℂ) (N : ℕ) (j : ℤ) : ℂ :=
  if ((N : ℤ) - 5 * j) % 2 = 0 then
    (-1 : ℂ) ^ j * q ^ (pentExp5 j + (schurB N j + 1).toNat)
      * gBz q N (schurB N j + 1)
  else 0

/-- **Carry certificate**: `residual j = carry j - carry (j+1)`. The even
and odd parity cases use `gBz_even_residual` / `gBz_odd_residual` together
with the pentagonal recurrence `pent_int_succ` for the exponent bookkeeping. -/
private lemma schurResidual_eq_carry_sub (q : ℂ) (N : ℕ) (j : ℤ) :
    schurResidual q N j = schurCarry q N j - schurCarry q N (j + 1) := by
  have hB2 : schurB (N + 2) j = schurB N j + 1 := by unfold schurB; omega
  by_cases hpar : ((N : ℤ) - 5 * j) % 2 = 0
  · have hB1 : schurB (N + 1) j = schurB N j := by unfold schurB; omega
    have hpar_next : ((N : ℤ) - 5 * (j + 1)) % 2 ≠ 0 := by omega
    unfold schurResidual schurTermZ' schurCarry
    rw [hB2, hB1, if_pos hpar, if_neg hpar_next,
        show q ^ (pentExp5 j + (schurB N j + 1).toNat)
          = q ^ pentExp5 j * q ^ (schurB N j + 1).toNat from pow_add q _ _]
    linear_combination ((-1 : ℂ) ^ j * q ^ pentExp5 j) *
      gBz_even_residual q N (schurB N j)
  · have hB1 : schurB (N + 1) j = schurB N j + 1 := by unfold schurB; omega
    have hpar_next : ((N : ℤ) - 5 * (j + 1)) % 2 = 0 := by omega
    have hBnext : schurB N (j + 1) + 1 = schurB N j - 1 := by unfold schurB; omega
    have hsign : (-1 : ℂ) ^ (j + 1) = -((-1 : ℂ) ^ j) := by
      rw [zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]; norm_num
    have hres := gBz_odd_residual q N (schurB N j)
    by_cases hz : gBz q N (schurB N j - 1) = 0
    · unfold schurResidual schurTermZ' schurCarry
      rw [hB2, hB1, hBnext, if_neg hpar, if_pos hpar_next]
      simp only [hz, mul_zero, zero_mul, sub_zero, zero_sub] at hres ⊢
      linear_combination ((-1 : ℂ) ^ j * q ^ pentExp5 j) * hres
    · have hb_range : 1 ≤ schurB N j ∧ schurB N j ≤ (N : ℤ) + 1 := by
        by_contra hcon
        apply hz
        rcases not_and_or.mp hcon with h | h
        · exact gBz_neg q N _ (by unfold schurB at *; omega)
        · exact gBz_gt q N _ (by unfold schurB at *; omega)
      obtain ⟨hb1, hb2⟩ := hb_range
      have hexp : pentExp5 j + ((N : ℤ) + 1 - schurB N j).toNat
                = pentExp5 (j + 1) + (schurB N j - 1).toNat := by
        have h1 := pent_int_nonneg j
        have h2 := pent_int_nonneg (j + 1)
        have h3 := pent_int_succ (j + 1)
        simp only [show ((j : ℤ) + 1) - 1 = j from by ring] at h3
        have hpar' : ((N : ℤ) - 5 * j) % 2 ≠ 0 := hpar
        simp only [pentExp5, schurB] at *
        omega
      unfold schurResidual schurTermZ' schurCarry
      rw [hB2, hB1, hBnext, if_neg hpar, if_pos hpar_next, hsign,
          show q ^ (pentExp5 (j + 1) + (schurB N j - 1).toNat)
            = q ^ pentExp5 j * q ^ ((N : ℤ) + 1 - schurB N j).toNat from by
            rw [← hexp]; exact pow_add q _ _]
      linear_combination ((-1 : ℂ) ^ j * q ^ pentExp5 j) *
        gBz_odd_residual q N (schurB N j)

/-- Finite telescoping over an integer `Icc` of width `n`. -/
lemma sumIcc_sub_telescope (F : ℤ → ℂ) (a : ℤ) (n : ℕ) :
    ∑ j ∈ Finset.Icc a (a + (n : ℤ) - 1), (F j - F (j + 1))
      = F a - F (a + (n : ℤ)) := by
  induction n with
  | zero => simp [Finset.Icc_eq_empty (by omega : ¬ a ≤ a + ((0 : ℕ) : ℤ) - 1)]
  | succ k ih =>
      have hsplit : Finset.Icc a (a + ((k + 1 : ℕ) : ℤ) - 1)
          = insert (a + (k : ℤ)) (Finset.Icc a (a + (k : ℤ) - 1)) := by
        ext x
        simp only [Finset.mem_Icc, Finset.mem_insert]
        push_cast
        omega
      rw [hsplit, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega), ih,
          show a + ((k + 1 : ℕ) : ℤ) = a + (k : ℤ) + 1 from by push_cast; ring]
      ring

/-- The carry vanishes at the left endpoint of `bigJ N`. -/
private lemma schurCarry_left_zero (q : ℂ) (N : ℕ) :
    schurCarry q N (-(N : ℤ) - 3) = 0 := by
  unfold schurCarry
  by_cases h : ((N : ℤ) - 5 * (-(N : ℤ) - 3)) % 2 = 0
  · rw [if_pos h,
        gBz_gt q N (schurB N (-(N : ℤ) - 3) + 1) (by unfold schurB; omega)]
    ring
  · rw [if_neg h]

/-- The carry vanishes past the right endpoint of `bigJ N`. -/
private lemma schurCarry_right_zero (q : ℂ) (N : ℕ) :
    schurCarry q N ((N : ℤ) + 4) = 0 := by
  unfold schurCarry
  by_cases h : ((N : ℤ) - 5 * ((N : ℤ) + 4)) % 2 = 0
  · rw [if_pos h,
        gBz_neg q N (schurB N ((N : ℤ) + 4) + 1) (by unfold schurB; omega)]
    ring
  · rw [if_neg h]

/-- The full residual sum telescopes to `0`. -/
private lemma schurResidual_sum_zero (q : ℂ) (N : ℕ) :
    ∑ j ∈ bigJ N, schurResidual q N j = 0 := by
  rw [Finset.sum_congr rfl (fun j _ => schurResidual_eq_carry_sub q N j)]
  have ha : -(↑N : ℤ) - 3 + ((2 * N + 7 : ℕ) : ℤ) - 1 = (↑N : ℤ) + 3 := by
    push_cast; ring
  have hr : -(↑N : ℤ) - 3 + ((2 * N + 7 : ℕ) : ℤ) = (↑N : ℤ) + 4 := by
    push_cast; ring
  have htel := sumIcc_sub_telescope (fun j => schurCarry q N j)
    (-(↑N : ℤ) - 3) (2 * N + 7)
  rw [ha] at htel
  rw [bigJ, htel, hr, schurCarry_left_zero, schurCarry_right_zero]
  ring

/-- **Schur's 1917 recurrence** (unconditional): `schurRHSz` satisfies the
Rogers-Ramanujan recurrence `d_{N+2} = d_{N+1} + q^{N+1} d_N`. -/
theorem schurRHSz_recurrence (q : ℂ) (N : ℕ) :
    schurRHSz q (N + 2) =
      schurRHSz q (N + 1) + q ^ (N + 1) * schurRHSz q N := by
  have h := schurResidual_sum_zero q N
  have hsum : ∑ j ∈ bigJ N, schurResidual q N j
      = (∑ j ∈ bigJ N, schurTermZ' q (N + 2) j)
        - (∑ j ∈ bigJ N, schurTermZ' q (N + 1) j)
        - q ^ (N + 1) * ∑ j ∈ bigJ N, schurTermZ' q N j := by
    simp only [schurResidual, Finset.sum_sub_distrib, Finset.mul_sum]
  rw [hsum,
      ← schurRHSz_common_range q N (N + 2) (by omega) (by omega),
      ← schurRHSz_common_range q N (N + 1) (by omega) (by omega),
      ← schurRHSz_common_range q N N (by omega) (by omega)] at h
  linear_combination h

/-- **Schur's 1917 recurrence** for `schurRHS`. -/
theorem schurRHS_recurrence (q : ℂ) (N : ℕ) :
    schurRHS q (N + 2) = schurRHS q (N + 1) + q ^ (N + 1) * schurRHS q N := by
  rw [schurRHS_eq_schurRHSz, schurRHS_eq_schurRHSz, schurRHS_eq_schurRHSz]
  exact schurRHSz_recurrence q N

/-- **Schur's identity** (unconditional): `rrPoly q N = schurRHS q N`. -/
theorem rrPoly_eq_schurRHS (q : ℂ) (N : ℕ) : rrPoly q N = schurRHS q N :=
  rrPoly_eq_schurRHS_of_recurrence q (fun N => schurRHS_recurrence q N) N

/-- **Finite Rogers-Ramanujan / Schur identity** (unconditional):
`∑_n q^(n²)·[N-n choose n]_q = ∑_j (-1)^j q^(j(5j+1)/2)·[N choose ⌊(N-5j)/2⌋]_q`. -/
theorem schurSum_eq_schurRHS (q : ℂ) (N : ℕ) : schurSum q N = schurRHS q N := by
  rw [← rrPoly_eq_schurSum q N, rrPoly_eq_schurRHS q N]

end Complex

end Ch07
end PartII
end QseriesFormalization
