import QseriesFormalization.Chapter07
import QseriesFormalization.Chapter04
import QseriesFormalization.Chapter07_RRStep1

/-!
# Chapter 7 — Rogers-Ramanujan SECOND identity, Step 1 (H-type Schur)

Parallel to `Chapter07_RRStep1` (the G/first identity) for the H/second
identity. The H-finite-LHS is `∑_n q^{n²+n}·[N-n choose n]_q` (the `a=1`
Rogers-Ramanujan polynomial, `rrJInf q q` in the limit).

The H-Schur polynomial recurrence and RHS convention are **derived and
sanity-checked** here (same methodology that caught/corrected the G-side
`5j` floor convention), not assumed.

Target: `rrJInf q q · (q;q)_∞ = ∑'_j (-1)^j q^(j(5j+3)/2)` (h_step2).
See `docs/RR_step1_schur.md`.
-/

namespace QseriesFormalization
namespace PartII
namespace Ch07

section Complex

open Filter Topology

/-- The H-type Rogers-Ramanujan / Schur polynomial `e_N`, defined by
`e_0 = e_1 = 1`, `e_{N+2} = e_{N+1} + q^{N+2}·e_N`. The exponent `N+2`
(vs `N+1` for the G-polynomial `rrPoly`) is **derived** from the
`∑ q^{n²+n}[N-n choose n]_q` sanity values `e_2 = 1+q²`, `e_3 = 1+q²+q³`. -/
noncomputable def rrPolyH (q : ℂ) : ℕ → ℂ
  | 0 => 1
  | 1 => 1
  | (N + 2) => rrPolyH q (N + 1) + q ^ (N + 2) * rrPolyH q N

@[simp] theorem rrPolyH_zero (q : ℂ) : rrPolyH q 0 = 1 := rfl
@[simp] theorem rrPolyH_one (q : ℂ) : rrPolyH q 1 = 1 := rfl

/-- The defining recurrence (wrapper for `N + 2`). -/
theorem rrPolyH_succ_succ (q : ℂ) (N : ℕ) :
    rrPolyH q (N + 2) = rrPolyH q (N + 1) + q ^ (N + 2) * rrPolyH q N := rfl

/-- Sanity: `e_2 = 1 + q²`. -/
theorem rrPolyH_two (q : ℂ) : rrPolyH q 2 = 1 + q ^ 2 := by
  rw [show (2 : ℕ) = 0 + 2 from rfl, rrPolyH_succ_succ]; simp

/-- Sanity: `e_3 = 1 + q² + q³`. -/
theorem rrPolyH_three (q : ℂ) : rrPolyH q 3 = 1 + q ^ 2 + q ^ 3 := by
  rw [show (3 : ℕ) = 1 + 2 from rfl, rrPolyH_succ_succ, rrPolyH_two]
  simp only [rrPolyH_one]; ring

/-- Sanity: `e_4 = 1 + q² + q³ + q⁴ + q⁶` (= `schurSumH q 4`; the `q⁶`
term, not `q⁵`, confirms the `q^{N+2}` recurrence exponent). -/
theorem rrPolyH_four (q : ℂ) :
    rrPolyH q 4 = 1 + q ^ 2 + q ^ 3 + q ^ 4 + q ^ 6 := by
  rw [show (4 : ℕ) = 2 + 2 from rfl, rrPolyH_succ_succ, rrPolyH_three,
      rrPolyH_two]
  ring

/-- The H-Schur finite sum `Sʜ q N := ∑_{n=0}^{N} q^(n²+n)·[N-n choose n]_q`
(the `a=1` Rogers-Ramanujan finite LHS). -/
noncomputable def schurSumH (q : ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range (N + 1), q ^ (n ^ 2 + n) * gaussianBinom q (N - n) n

/-- `Sʜ q 0 = 1`. -/
@[simp] theorem schurSumH_zero (q : ℂ) : schurSumH q 0 = 1 := by
  simp [schurSumH]

/-- `Sʜ q 1 = 1`. -/
@[simp] theorem schurSumH_one (q : ℂ) : schurSumH q 1 = 1 := by
  simp [schurSumH, Finset.sum_range_succ, gaussianBinom]

/-- Sanity: `Sʜ q 2 = 1 + q²` (matches `rrPolyH q 2`). -/
theorem schurSumH_two (q : ℂ) : schurSumH q 2 = 1 + q ^ 2 := by
  simp only [schurSumH, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [gaussianBinom]

/-- Sanity: `Sʜ q 3 = 1 + q² + q³` (matches `rrPolyH q 3`). -/
theorem schurSumH_three (q : ℂ) : schurSumH q 3 = 1 + q ^ 2 + q ^ 3 := by
  simp only [schurSumH, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [gaussianBinom]
  ring

/-! ### H-Schur recurrence (parallel to the G-side `schurSum_recurrence`) -/

/-- H-analog of `schur_termB_eq`: the exponent identity for the second
sum, `(n+1)²+(n+1)+((N-n)-n) = (N+2)+(n²+n)` when `2n ≤ N`, else `B = 0`. -/
private theorem schurH_termB_eq (q : ℂ) (N n : ℕ) :
    q ^ ((n + 1) ^ 2 + (n + 1) + ((N - n) - n)) * gaussianBinom q (N - n) n =
      q ^ (N + 2) * (q ^ (n ^ 2 + n) * gaussianBinom q (N - n) n) := by
  by_cases h2n : 2 * n ≤ N
  · have hsub : (N - n) - n = N - 2 * n := by omega
    have hexp : (n + 1) ^ 2 + (n + 1) + ((N - n) - n) = (N + 2) + (n ^ 2 + n) := by
      rw [hsub]; ring_nf; omega
    rw [hexp, pow_add]
    ring
  · have hlt : N - n < n := by omega
    rw [PartI.Ch03.gaussianBinom_eq_zero_of_lt q hlt]
    ring

/-- H-analog of `schur_pascal_term`. -/
private theorem schurH_pascal_term (q : ℂ) (N n : ℕ) (hn : n ≤ N) :
    q ^ ((n + 1) ^ 2 + (n + 1)) * gaussianBinom q (N + 1 - n) (n + 1) =
      q ^ ((n + 1) ^ 2 + (n + 1)) * gaussianBinom q (N - n) (n + 1) +
      q ^ (N + 2) * (q ^ (n ^ 2 + n) * gaussianBinom q (N - n) n) := by
  have hNn : N + 1 - n = (N - n) + 1 := by omega
  rw [hNn]
  show q ^ ((n + 1) ^ 2 + (n + 1)) *
      (gaussianBinom q (N - n) (n + 1)
        + q ^ ((N - n) - n) * gaussianBinom q (N - n) n) = _
  rw [mul_add]
  congr 1
  rw [← mul_assoc, ← pow_add]
  exact schurH_termB_eq q N n

/-- **The H-Schur recurrence**:
`schurSumH q (N+2) = schurSumH q (N+1) + q^(N+2)·schurSumH q N`. -/
theorem schurSumH_recurrence (q : ℂ) (N : ℕ) :
    schurSumH q (N + 2) = schurSumH q (N + 1) + q ^ (N + 2) * schurSumH q N := by
  rw [schurSumH, Finset.sum_range_succ']
  simp only [Nat.zero_eq, pow_zero, one_mul, Nat.sub_zero, gaussianBinom_zero_right]
  rw [Finset.sum_range_succ]
  have h_last_zero :
      q ^ ((N + 1 + 1) ^ 2 + (N + 1 + 1))
          * gaussianBinom q (N + 2 - (N + 1 + 1)) (N + 1 + 1) = 0 := by
    have : N + 2 - (N + 1 + 1) = 0 := by omega
    rw [this, PartI.Ch03.gaussianBinom_eq_zero_of_lt q (by omega : (0 : ℕ) < N + 1 + 1)]
    ring
  rw [h_last_zero, add_zero]
  have h_sum_eq :
      ∑ n ∈ Finset.range (N + 1),
          q ^ ((n + 1) ^ 2 + (n + 1)) * gaussianBinom q (N + 2 - (n + 1)) (n + 1) =
      (∑ n ∈ Finset.range (N + 1),
          q ^ ((n + 1) ^ 2 + (n + 1)) * gaussianBinom q (N - n) (n + 1)) +
      q ^ (N + 2) *
        (∑ n ∈ Finset.range (N + 1), q ^ (n ^ 2 + n) * gaussianBinom q (N - n) n) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn' : n ≤ N := by simp only [Finset.mem_range] at hn; omega
    have hNn2 : N + 2 - (n + 1) = N + 1 - n := by omega
    rw [hNn2, schurH_pascal_term q N n hn']
  rw [h_sum_eq]
  have h_sN1 :
      schurSumH q (N + 1) =
        1 + ∑ n ∈ Finset.range (N + 1),
              q ^ ((n + 1) ^ 2 + (n + 1)) * gaussianBinom q (N - n) (n + 1) := by
    rw [schurSumH, Finset.sum_range_succ']
    have h0 : q ^ ((0 : ℕ) ^ 2 + 0) * gaussianBinom q (N + 1 - 0) 0 = 1 := by simp
    rw [h0, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn' : n ≤ N := by simp only [Finset.mem_range] at hn; omega
    congr 2
    omega
  have h_sN :
      schurSumH q N
        = ∑ n ∈ Finset.range (N + 1), q ^ (n ^ 2 + n) * gaussianBinom q (N - n) n := rfl
  rw [h_sN1, h_sN]
  ring

/-- H-analog of `rrPoly_eq_of_recurrence` (recurrence weight `q^(N+2)`). -/
theorem rrPolyH_eq_of_recurrence (q : ℂ) (f : ℕ → ℂ)
    (h0 : f 0 = 1) (h1 : f 1 = 1)
    (h_rec : ∀ N : ℕ, f (N + 2) = f (N + 1) + q ^ (N + 2) * f N) :
    ∀ N : ℕ, rrPolyH q N = f N := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    match N with
    | 0 => simp [h0]
    | 1 => simp [h1]
    | (M + 2) =>
      rw [rrPolyH_succ_succ, h_rec M, ih (M + 1) (by omega), ih M (by omega)]

/-- **The H-Schur LHS identity**: `rrPolyH q N = ∑_n q^(n²+n)·[N-n choose n]_q`. -/
theorem rrPolyH_eq_schurSumH (q : ℂ) (N : ℕ) : rrPolyH q N = schurSumH q N :=
  rrPolyH_eq_of_recurrence q (schurSumH q) (schurSumH_zero q) (schurSumH_one q)
    (schurSumH_recurrence q) N

/-- `schurSumH` as a `tsum` over all `ℕ` (tail vanishes). -/
theorem schurSumH_eq_tsum (q : ℂ) (N : ℕ) :
    schurSumH q N = ∑' n : ℕ, q ^ (n ^ 2 + n) * gaussianBinom q (N - n) n := by
  rw [schurSumH]
  refine (tsum_eq_sum (s := Finset.range (N + 1)) ?_).symm
  intro n hn
  rw [Finset.mem_range, not_lt] at hn
  have hNsub : N - n = 0 := by omega
  rw [hNsub]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp [gaussianBinom]

/-! ### H-pentagonal exponent `j(5j+3)/2`

Fixed by `theta_sum_2_eq_jacobiSeries` (Ch04: `∑'_j (-1)^j q^(j(5j+3)/2)`),
not a guessed convention. Mechanical infrastructure parallel to the
G-side `pentExp5`. -/

/-- `j(5j+3)` is even, so `j(5j+3)/2` is exact. -/
theorem two_dvd_j_5j_add_three (j : ℤ) : (2 : ℤ) ∣ j * (5 * j + 3) := by
  rcases Int.even_or_odd j with ⟨m, hm⟩ | ⟨m, hm⟩
  · exact ⟨m * (5 * j + 3), by rw [hm]; ring⟩
  · exact ⟨j * (5 * m + 4), by rw [hm]; ring⟩

/-- H-generalized pentagonal exponent `j(5j+3)/2` as a `ℕ`. -/
noncomputable def pentExp5H (j : ℤ) : ℕ := (j * (5 * j + 3) / 2).toNat

/-- `0 ≤ j(5j+3)/2` for all integer `j` (no integer lies in `(-3/5, 0)`). -/
theorem pentH_int_nonneg (j : ℤ) : 0 ≤ j * (5 * j + 3) / 2 := by
  have hdvd := two_dvd_j_5j_add_three j
  have hprod : 0 ≤ j * (5 * j + 3) := by
    by_cases hj : j < 0
    · have h1 : (0 : ℤ) ≤ -j := by omega
      have h2 : (0 : ℤ) ≤ -(5 * j + 3) := by omega
      nlinarith [mul_nonneg h1 h2]
    · have hj' : (0 : ℤ) ≤ j := by omega
      exact mul_nonneg hj' (by linarith)
  omega

/-- Core H-pentagonal recurrence: `Pʜ_j - Pʜ_{j-1} = 5j - 1`,
i.e. `j(5j+3)/2 = (j-1)(5(j-1)+3)/2 + (5j-1)`. -/
theorem pentH_int_succ (j : ℤ) :
    j * (5 * j + 3) / 2 = (j - 1) * (5 * (j - 1) + 3) / 2 + (5 * j - 1) := by
  have hring :
      j * (5 * j + 3) = (j - 1) * (5 * (j - 1) + 3) + 2 * (5 * j - 1) := by ring
  have hd1 := two_dvd_j_5j_add_three j
  have hd2 := two_dvd_j_5j_add_three (j - 1)
  omega

/-- `pentExp5H` form of the core recurrence. -/
theorem pentExp5H_succ (j : ℤ) (hj : 1 ≤ 5 * j) :
    (pentExp5H j : ℤ) = (pentExp5H (j - 1) : ℤ) + (5 * j - 1) := by
  simp only [pentExp5H]
  rw [Int.toNat_of_nonneg (pentH_int_nonneg j),
      Int.toNat_of_nonneg (pentH_int_nonneg (j - 1))]
  have h := pentH_int_succ j
  omega

/-! ### H-Schur RHS (theta-Gaussian finite form) — DERIVED + VERIFIED

Derived from the proven LHS recurrence (`rrPolyH_eq_schurSumH`) and
cross-checked against the proven `rrPolyH` oracle at `N = 0..4` (the
same sanctioned methodology that caught the G-side `2j` and `q⁵→q⁶`
errors). See `docs/RR_step1_schur.md` ("RR Step 2 — UNBLOCKED").

Key structural fact: the H form uses **top index `N+1`** (not `N`),
which is exactly what reconciles the `e`-recurrence exponent `q^{N+2}`
with the natural two-`q`-Pascal-step `q^{N+1}`. With top `N+1`, the
*same* G floor `⌊(N-5j)/2⌋` and the H pentagonal `j(5j+3)/2` close it:

`e_N = Σ_j (-1)^j q^{j(5j+3)/2} · [N+1 choose ⌊(N-5j)/2⌋]_q`. -/

/-- Raw integer floor bottom `⌊(N-5j)/2⌋` (no `if` wrapper: `gBz` itself
zero-extends out-of-range, and for every in-range `j` the numerator
`N-5j ≥ 0`, so `Int./` agrees with the genuine floor). -/
noncomputable def schurBottomH (N : ℕ) (j : ℤ) : ℤ := ((N : ℤ) - 5 * j) / 2

/-- The H-Schur RHS: `Σ_j (-1)^j q^{j(5j+3)/2} · [N+1 choose ⌊(N-5j)/2⌋]_q`,
summed over `j ∈ [-(N+1), N+1]` (outside, `gBz` is `0`). Top index `N+1`. -/
noncomputable def schurRHSH (q : ℂ) (N : ℕ) : ℂ :=
  ∑ j ∈ Finset.Icc (-(N : ℤ) - 1) ((N : ℤ) + 1),
    (-1 : ℂ) ^ j * q ^ pentExp5H j * gBz q (N + 1) (schurBottomH N j)

/-- Sanity (build = oracle check vs `rrPolyH q 0 = 1`). -/
theorem schurRHSH_zero (q : ℂ) : schurRHSH q 0 = 1 := by
  have hset : Finset.Icc (-(((0 : ℕ) : ℤ)) - 1) (((0 : ℕ) : ℤ) + 1) =
      ({-1, 0, 1} : Finset ℤ) := by decide
  rw [schurRHSH, hset]
  norm_num [Finset.sum_insert, Finset.mem_insert, pentExp5H, schurBottomH,
    gBz, gaussianBinom, Int.fdiv]

/-- Sanity (= `rrPolyH q 1 = 1`). -/
theorem schurRHSH_one (q : ℂ) : schurRHSH q 1 = 1 := by
  have hset : Finset.Icc (-(((1 : ℕ) : ℤ)) - 1) (((1 : ℕ) : ℤ) + 1) =
      ({-2, -1, 0, 1, 2} : Finset ℤ) := by decide
  rw [schurRHSH, hset]
  norm_num [Finset.sum_insert, Finset.mem_insert, pentExp5H, schurBottomH,
    gBz, gaussianBinom, Int.fdiv]

/-- Sanity (= `rrPolyH q 2 = 1 + q²`): the `j=0` term `[3 choose 1]_q`
minus the `j=-1` term `q·[3 choose 3]_q` collapses to `1 + q²`. -/
theorem schurRHSH_two (q : ℂ) : schurRHSH q 2 = 1 + q ^ 2 := by
  have hset : Finset.Icc (-(((2 : ℕ) : ℤ)) - 1) (((2 : ℕ) : ℤ) + 1) =
      ({-3, -2, -1, 0, 1, 2, 3} : Finset ℤ) := by decide
  rw [schurRHSH, hset]
  norm_num [Finset.sum_insert, Finset.mem_insert, pentExp5H, schurBottomH,
    gBz, Int.fdiv]
  simp only [show Int.toNat (1 : ℤ) = 1 from rfl,
    show Int.toNat (3 : ℤ) = 3 from rfl]
  norm_num [gaussianBinom]
  ring

/-- Sanity (= `rrPolyH q 3 = 1 + q² + q³`). -/
theorem schurRHSH_three (q : ℂ) : schurRHSH q 3 = 1 + q ^ 2 + q ^ 3 := by
  have hset : Finset.Icc (-(((3 : ℕ) : ℤ)) - 1) (((3 : ℕ) : ℤ) + 1) =
      ({-4, -3, -2, -1, 0, 1, 2, 3, 4} : Finset ℤ) := by decide
  rw [schurRHSH, hset]
  norm_num [Finset.sum_insert, Finset.mem_insert, pentExp5H, schurBottomH,
    gBz, Int.fdiv]
  simp only [show Int.toNat (1 : ℤ) = 1 from rfl,
    show Int.toNat (4 : ℤ) = 4 from rfl]
  norm_num [gaussianBinom]
  ring

/-- Sanity (= `rrPolyH q 4 = 1 + q² + q³ + q⁴ + q⁶`): the deepest
cross-check — `[5 choose 2]_q − q·[5 choose 1]_q` collapses exactly. -/
theorem schurRHSH_four (q : ℂ) :
    schurRHSH q 4 = 1 + q ^ 2 + q ^ 3 + q ^ 4 + q ^ 6 := by
  have hset : Finset.Icc (-(((4 : ℕ) : ℤ)) - 1) (((4 : ℕ) : ℤ) + 1) =
      ({-5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5} : Finset ℤ) := by decide
  rw [schurRHSH, hset]
  norm_num [Finset.sum_insert, Finset.mem_insert, pentExp5H, schurBottomH,
    gBz, Int.fdiv]
  simp only [show Int.toNat (4 : ℤ) = 4 from rfl,
    show Int.toNat (2 : ℤ) = 2 from rfl]
  norm_num [gaussianBinom]
  ring

/-- The H-Schur RHS agrees with the H-Schur polynomial at the verified
base points (`N = 0..4`). The full identity `rrPolyH = schurRHSH` for
all `N` is the carry-telescope theorem (next: mirror the G-side
`gBz_even/odd_residual`, with top index shifted by `1`). -/
theorem schurRHSH_eq_rrPolyH_base (q : ℂ) :
    schurRHSH q 0 = rrPolyH q 0 ∧ schurRHSH q 1 = rrPolyH q 1 ∧
    schurRHSH q 2 = rrPolyH q 2 ∧ schurRHSH q 3 = rrPolyH q 3 ∧
    schurRHSH q 4 = rrPolyH q 4 :=
  ⟨by rw [schurRHSH_zero, rrPolyH_zero],
   by rw [schurRHSH_one, rrPolyH_one],
   by rw [schurRHSH_two, rrPolyH_two],
   by rw [schurRHSH_three, rrPolyH_three],
   by rw [schurRHSH_four, rrPolyH_four]⟩

/-- **H-Schur identity, conditional reduction** (mirror of the G-side
`rrPoly_eq_schurRHS_of_recurrence`): GIVEN that `schurRHSH` satisfies the
H Rogers-Ramanujan recurrence `e_{N+2} = e_{N+1} + q^{N+2}·e_N`, then
`rrPolyH q N = schurRHSH q N` for all `N`. The hypothesis is Schur's
second finite identity recurrence — the remaining carry-telescope piece
(mirror G `gBz_even/odd_residual` at top index `N+1`). -/
theorem rrPolyH_eq_schurRHSH_of_recurrence (q : ℂ)
    (h_rec : ∀ N : ℕ, schurRHSH q (N + 2) =
      schurRHSH q (N + 1) + q ^ (N + 2) * schurRHSH q N) :
    ∀ N : ℕ, rrPolyH q N = schurRHSH q N :=
  rrPolyH_eq_of_recurrence q (schurRHSH q) (schurRHSH_zero q) (schurRHSH_one q)
    h_rec

/-- **H-Schur LHS = RHS** (conditional): given the `schurRHSH` recurrence,
`schurSumH q N = schurRHSH q N` — the finite second Rogers-Ramanujan /
Schur identity
`∑_n q^(n²+n)·[N-n choose n]_q = ∑_j (-1)^j q^(j(5j+3)/2)·[N+1 choose ⌊(N-5j)/2⌋]_q`. -/
theorem schurSumH_eq_schurRHSH_of_recurrence (q : ℂ)
    (h_rec : ∀ N : ℕ, schurRHSH q (N + 2) =
      schurRHSH q (N + 1) + q ^ (N + 2) * schurRHSH q N) (N : ℕ) :
    schurSumH q N = schurRHSH q N := by
  rw [← rrPolyH_eq_schurSumH q N, rrPolyH_eq_schurRHSH_of_recurrence q h_rec N]

/-! ### H-Schur carry-telescope (UNCONDITIONAL recurrence)

Faithful mirror of the G-side `schurResidual_eq_carry_sub` /
`schurRHSz_recurrence` (RRStep1) with top index `N+1`, pentagonal
`j(5j+3)/2`, recurrence weight `q^{N+2}`. Reuses the de-privatized
G-side `gBz_even_residual` / `gBz_odd_residual` at `M = N+1` and
`sumIcc_sub_telescope`. See `docs/RR_step1_schur.md`. -/

/-- Per-`j` H-Schur RHS term (raw-floor bottom, **top index `N+1`**). -/
private noncomputable def schurTermHZ' (q : ℂ) (N : ℕ) (j : ℤ) : ℂ :=
  (-1 : ℂ) ^ j * q ^ pentExp5H j * gBz q (N + 1) (schurBottomH N j)

private lemma schurRHSH_eq_sumTerm (q : ℂ) (N : ℕ) :
    schurRHSH q N =
      ∑ j ∈ Finset.Icc (-(N : ℤ) - 1) ((N : ℤ) + 1), schurTermHZ' q N j := rfl

/-- Common reindex range (wide enough for `N`, `N+1`, `N+2`). -/
private def bigJH (N : ℕ) : Finset ℤ :=
  Finset.Icc (-(N : ℤ) - 3) ((N : ℤ) + 3)

private lemma schurTermHZ'_left_zero (q : ℂ) (n : ℕ) (j : ℤ)
    (hj : j < -(n : ℤ) - 1) : schurTermHZ' q n j = 0 := by
  unfold schurTermHZ' schurBottomH
  rw [gBz_gt q (n + 1) _ (by push_cast; omega)]
  ring

private lemma schurTermHZ'_right_zero (q : ℂ) (n : ℕ) (j : ℤ)
    (hj : (n : ℤ) + 1 < j) : schurTermHZ' q n j = 0 := by
  unfold schurTermHZ' schurBottomH
  rw [gBz_neg q (n + 1) _ (by omega)]
  ring

private lemma schurRHSH_common_range (q : ℂ) (N n : ℕ)
    (hn₁ : N ≤ n) (hn₂ : n ≤ N + 2) :
    schurRHSH q n = ∑ j ∈ bigJH N, schurTermHZ' q n j := by
  rw [schurRHSH_eq_sumTerm]
  refine Finset.sum_subset ?_ ?_
  · intro j hj
    simp only [bigJH, Finset.mem_Icc] at hj ⊢
    omega
  · intro j _ hjSmall
    simp only [Finset.mem_Icc, not_and, not_le] at hjSmall
    by_cases hlo : -(n : ℤ) - 1 ≤ j
    · exact schurTermHZ'_right_zero q n j (by have := hjSmall hlo; omega)
    · exact schurTermHZ'_left_zero q n j (by omega)

private noncomputable def schurResidualH (q : ℂ) (N : ℕ) (j : ℤ) : ℂ :=
  schurTermHZ' q (N + 2) j - schurTermHZ' q (N + 1) j
    - q ^ (N + 2) * schurTermHZ' q N j

private noncomputable def schurCarryH (q : ℂ) (N : ℕ) (j : ℤ) : ℂ :=
  if ((N : ℤ) - 5 * j) % 2 = 0 then
    (-1 : ℂ) ^ j * q ^ (pentExp5H j + (schurBottomH N j + 1).toNat)
      * gBz q (N + 1) (schurBottomH N j + 1)
  else 0

private lemma schurResidualH_eq_carry_sub (q : ℂ) (N : ℕ) (j : ℤ) :
    schurResidualH q N j = schurCarryH q N j - schurCarryH q N (j + 1) := by
  have hB2 : schurBottomH (N + 2) j = schurBottomH N j + 1 := by
    unfold schurBottomH; omega
  by_cases hpar : ((N : ℤ) - 5 * j) % 2 = 0
  · have hB1 : schurBottomH (N + 1) j = schurBottomH N j := by
      unfold schurBottomH; omega
    have hpar_next : ((N : ℤ) - 5 * (j + 1)) % 2 ≠ 0 := by omega
    unfold schurResidualH schurTermHZ' schurCarryH
    rw [hB2, hB1, if_pos hpar, if_neg hpar_next,
        show q ^ (pentExp5H j + (schurBottomH N j + 1).toNat)
          = q ^ pentExp5H j * q ^ (schurBottomH N j + 1).toNat
          from pow_add q _ _]
    have hres := gBz_even_residual q (N + 1) (schurBottomH N j)
    simp only [show N + 2 + 1 = N + 3 from rfl, show N + 1 + 2 = N + 3 from rfl,
      show N + 1 + 1 = N + 2 from rfl] at hres ⊢
    linear_combination ((-1 : ℂ) ^ j * q ^ pentExp5H j) * hres
  · have hB1 : schurBottomH (N + 1) j = schurBottomH N j + 1 := by
      unfold schurBottomH; omega
    have hpar_next : ((N : ℤ) - 5 * (j + 1)) % 2 = 0 := by omega
    have hBnext : schurBottomH N (j + 1) + 1 = schurBottomH N j - 1 := by
      unfold schurBottomH; omega
    have hsign : (-1 : ℂ) ^ (j + 1) = -((-1 : ℂ) ^ j) := by
      rw [zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]; norm_num
    by_cases hz : gBz q (N + 1) (schurBottomH N j - 1) = 0
    · unfold schurResidualH schurTermHZ' schurCarryH
      rw [hB2, hB1, hBnext, if_neg hpar, if_pos hpar_next]
      have hres := gBz_odd_residual q (N + 1) (schurBottomH N j)
      simp only [show N + 2 + 1 = N + 3 from rfl, show N + 1 + 2 = N + 3 from rfl,
        show N + 1 + 1 = N + 2 from rfl] at hres ⊢
      simp only [hz, mul_zero, zero_mul, sub_zero, zero_sub] at hres ⊢
      linear_combination ((-1 : ℂ) ^ j * q ^ pentExp5H j) * hres
    · have hb_range : 1 ≤ schurBottomH N j ∧ schurBottomH N j ≤ (N : ℤ) + 2 := by
        by_contra hcon
        apply hz
        rcases not_and_or.mp hcon with h | h
        · exact gBz_neg q (N + 1) _ (by unfold schurBottomH at *; omega)
        · exact gBz_gt q (N + 1) _ (by unfold schurBottomH at *; push_cast; omega)
      obtain ⟨hb1, hb2⟩ := hb_range
      have hexp : pentExp5H j + ((N : ℤ) + 2 - schurBottomH N j).toNat
                = pentExp5H (j + 1) + (schurBottomH N j - 1).toNat := by
        have h1 := pentH_int_nonneg j
        have h2 := pentH_int_nonneg (j + 1)
        have h3 := pentH_int_succ (j + 1)
        simp only [show ((j : ℤ) + 1) - 1 = j from by ring] at h3
        have hpar' : ((N : ℤ) - 5 * j) % 2 ≠ 0 := hpar
        simp only [pentExp5H, schurBottomH] at *
        omega
      unfold schurResidualH schurTermHZ' schurCarryH
      rw [hB2, hB1, hBnext, if_neg hpar, if_pos hpar_next, hsign,
          show q ^ (pentExp5H (j + 1) + (schurBottomH N j - 1).toNat)
            = q ^ pentExp5H j * q ^ ((N : ℤ) + 2 - schurBottomH N j).toNat
            from by rw [← hexp]; exact pow_add q _ _]
      have hres := gBz_odd_residual q (N + 1) (schurBottomH N j)
      rw [show ((N + 1 : ℕ) : ℤ) + 1 - schurBottomH N j
            = (N : ℤ) + 2 - schurBottomH N j from by push_cast; ring] at hres
      simp only [show N + 2 + 1 = N + 3 from rfl,
        show N + 1 + 1 = N + 2 from rfl] at hres ⊢
      linear_combination ((-1 : ℂ) ^ j * q ^ pentExp5H j) * hres

private lemma schurCarryH_left_zero (q : ℂ) (N : ℕ) :
    schurCarryH q N (-(N : ℤ) - 3) = 0 := by
  unfold schurCarryH
  by_cases h : ((N : ℤ) - 5 * (-(N : ℤ) - 3)) % 2 = 0
  · rw [if_pos h,
        gBz_gt q (N + 1) (schurBottomH N (-(N : ℤ) - 3) + 1)
          (by unfold schurBottomH; push_cast; omega)]
    ring
  · rw [if_neg h]

private lemma schurCarryH_right_zero (q : ℂ) (N : ℕ) :
    schurCarryH q N ((N : ℤ) + 4) = 0 := by
  unfold schurCarryH
  by_cases h : ((N : ℤ) - 5 * ((N : ℤ) + 4)) % 2 = 0
  · rw [if_pos h,
        gBz_neg q (N + 1) (schurBottomH N ((N : ℤ) + 4) + 1)
          (by unfold schurBottomH; omega)]
    ring
  · rw [if_neg h]

private lemma schurResidualH_sum_zero (q : ℂ) (N : ℕ) :
    ∑ j ∈ bigJH N, schurResidualH q N j = 0 := by
  rw [Finset.sum_congr rfl (fun j _ => schurResidualH_eq_carry_sub q N j)]
  have ha : -(↑N : ℤ) - 3 + ((2 * N + 7 : ℕ) : ℤ) - 1 = (↑N : ℤ) + 3 := by
    push_cast; ring
  have hr : -(↑N : ℤ) - 3 + ((2 * N + 7 : ℕ) : ℤ) = (↑N : ℤ) + 4 := by
    push_cast; ring
  have htel := sumIcc_sub_telescope (fun j => schurCarryH q N j)
    (-(↑N : ℤ) - 3) (2 * N + 7)
  rw [ha] at htel
  rw [bigJH, htel, hr, schurCarryH_left_zero, schurCarryH_right_zero]
  ring

/-- **Schur's second finite identity recurrence** (UNCONDITIONAL):
`schurRHSH` satisfies `e_{N+2} = e_{N+1} + q^{N+2}·e_N`. -/
theorem schurRHSH_recurrence (q : ℂ) (N : ℕ) :
    schurRHSH q (N + 2) =
      schurRHSH q (N + 1) + q ^ (N + 2) * schurRHSH q N := by
  have h := schurResidualH_sum_zero q N
  have hsum : ∑ j ∈ bigJH N, schurResidualH q N j
      = (∑ j ∈ bigJH N, schurTermHZ' q (N + 2) j)
        - (∑ j ∈ bigJH N, schurTermHZ' q (N + 1) j)
        - q ^ (N + 2) * ∑ j ∈ bigJH N, schurTermHZ' q N j := by
    simp only [schurResidualH, Finset.sum_sub_distrib, Finset.mul_sum]
  rw [hsum,
      ← schurRHSH_common_range q N (N + 2) (by omega) (by omega),
      ← schurRHSH_common_range q N (N + 1) (by omega) (by omega),
      ← schurRHSH_common_range q N N (by omega) (by omega)] at h
  linear_combination h

/-- **Finite second Rogers-Ramanujan / Schur identity** (unconditional):
`rrPolyH q N = schurRHSH q N`. -/
theorem rrPolyH_eq_schurRHSH (q : ℂ) (N : ℕ) :
    rrPolyH q N = schurRHSH q N :=
  rrPolyH_eq_schurRHSH_of_recurrence q (fun N => schurRHSH_recurrence q N) N

/-- **Finite second Rogers-Ramanujan / Schur identity** (LHS = RHS,
unconditional): `∑_n q^(n²+n)·[N-n choose n]_q
= ∑_j (-1)^j q^(j(5j+3)/2)·[N+1 choose ⌊(N-5j)/2⌋]_q`. -/
theorem schurSumH_eq_schurRHSH (q : ℂ) (N : ℕ) :
    schurSumH q N = schurRHSH q N := by
  rw [← rrPolyH_eq_schurSumH q N, rrPolyH_eq_schurRHSH q N]

end Complex

end Ch07
end PartII
end QseriesFormalization
