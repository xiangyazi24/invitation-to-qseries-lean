# RR Step 1 — Schur finite identity + Tannery

> **STATUS 2026-05-16: BOTH Rogers-Ramanujan identities COMPLETE,
> end-to-end, unconditional, 0 sorry / 0 axiom.**
> - First identity: `rogersRamanujan_first` (RRStep5, prior).
> - Second identity: `rogersRamanujan_second` (RRStep5H, commit
>   `9453097`) — `H(q)·(q²;q⁵)_∞·(q³;q⁵)_∞ = 1`.
> The "BLOCKED on input" sections below are HISTORICAL — the H-Schur
> RHS was DERIVED from the proven LHS recurrence (top index `N+1`)
> and verified against the `rrPolyH` oracle, WITHOUT the ChatGPT
> bridge (which timed out 5×) and WITHOUT guessing (Red Line kept).
> Chain: 4491780 (LHS Tannery) → 72446c9 (RHS derived+verified) →
> 8217251 (conditional reduction) → a5a44c2 (de-privatize) →
> e8893f2 (carry-telescope, finite Schur unconditional) →
> 68e6ed6 (h_step2 ℤ-Tannery) → 9453097 (rogersRamanujan_second).

**Source**: ChatGPT consultation 2026-05-15 (task `36418845`).

## Decision

Use **Approach (A)**: Tannery via Schur's finite forms. **NOT** Watson, **NOT** direct `tprod_mul`.

## Schur's finite identities

For each `N : ℕ`:

```
∑_{n ≤ N} q^(n²) · [N choose n]_q = ∑_j (-1)^j · q^(j(5j+1)/2) · [2N choose N-2j]_q

∑_{n ≤ N} q^(n(n+1)) · [N choose n]_q = ∑_j (-1)^j · q^(j(5j+3)/2) · [2N+1 choose N-2j]_q
```

where `[m choose k]_q` is the Gaussian binomial coefficient (q-binomial).

## Tannery limit

As `N → ∞` for `‖q‖ < 1`:
- Gaussian coefficient `[N choose n]_q → 1 / qPochhammer q n`
- RHS coefficients `[2N choose N-2j]_q → 1` (and `[2N+1 choose N-2j]_q → 1`)

Hence:
```
∑'_n q^(n²) / qPochhammer q n = rrJInf 1 q = ∑'_j (-1)^j · q^(j(5j+1)/2)
∑'_n q^(n(n+1)) / qPochhammer q n = rrJInf q q = ∑'_j (-1)^j · q^(j(5j+3)/2)
```

But the RHS is NOT yet the product form — those are the theta sums (`theta_sum_1` and `theta_sum_2` in our codebase). So Step 1 actually gives:

```
rrJInf 1 q · (q;q)_∞ = ∑'_j (-1)^j · q^(j(5j+1)/2)   ←  what's needed
rrJInf q q · (q;q)_∞ = ∑'_j (-1)^j · q^(j(5j+3)/2)
```

Wait — the issue is that Schur's identity already gives rrJInf as the LHS, but it's `∑'_n q^(n²) / (q;q)_n` directly equals `∑'_j (-1)^j q^(j(5j+1)/2)`. The `(q;q)_∞` factor doesn't appear in this version.

Looking again: the RIGHT R-R proof gives:
```
rrJInf 1 q = (∑'_j (-1)^j q^(j(5j+1)/2)) / (q;q)_∞
```

So Schur's identity gives a finite version, and Tannery passes to the limit. The `(q;q)_∞` factor appears via the [2N choose N-2j]_q coefficient limit:
- `[2N choose N-2j]_q → 1` is **WRONG** in general — it tends to `1 / (q;q)_∞` actually? Need to verify.

Actually the correct Tannery limit:
- `[N choose n]_q → q^(n(n+1)/2 - n²) / qPochhammer q n · something` — depends on convention
- The combined identity after limit gives the rrJInf product form directly.

This needs careful verification with the specific Gaussian convention used in Ch03.

## Lean implementation order

1. **Verify Schur's finite identity** in this codebase's Gaussian polynomial convention.
   Codebase: `qBinomial` or `Gaussian` (check Ch03).
2. **Tannery's theorem application**: Mathlib has `Tendsto.sum_finset_atTop` style.
3. **Finite identity → infinite limit** via `tendsto_nhds_unique`.

## CORRECTION (ChatGPT 2026-05-15, task bf31be1a)

The earlier sketch had the WRONG top index. Key corrections:

### Q1: Schur identity uses a MOVING top index

```
∑_{n=0}^{N} q^(n²) · [N-n choose n]_q
  = ∑_{j∈ℤ} (-1)^j q^(j(5j+1)/2) · [N choose ⌊(N-2j)/2⌋]_q
```

The LEFT side has `gaussianBinom q (N-n) n` — **not** `gaussianBinom q N n`.
For Lean, avoid floors: use the standard parity-split form, or match the
exact Schur polynomial three-term recurrence and use finite support indexed
by `N - 2j`.

### Q2: Tannery limits

```
gaussianBinom q (N+n) n  →  1 / qPochhammer q n   as N → ∞
```

For the RHS Schur coefficient with fixed `j`: Gaussian → **1** (NOT 1/(q;q)_∞).

So in the limit:
```
∑'_n q^(n²) / qPochhammer q n = ∑'_j (-1)^j q^(j(5j+1)/2)
```
i.e. `rrJInf 1 q = ∑'_j (-1)^j q^(j(5j+1)/2)` **directly** — wait, this means
rrJInf 1 q ≠ theta/(q;q)_∞ but rrJInf 1 q = theta?? No: the Schur LHS is
`∑ q^(n²) [N-n choose n]_q` whose Tannery limit is `∑'_n q^(n²)/(q;q)_n`
ONLY if `[N-n choose n]_q → 1/(q;q)_n`. But Q2 says `[N+n choose n]_q → 1/(q;q)_n`.
The `N-n` vs `N+n` discrepancy needs care — likely the Schur LHS Gaussian
`[N-n choose n]_q` also → `1/(q;q)_n` because as N→∞ with n fixed, N-n→∞ too.

**Net effect**: Schur + Tannery gives `rrJInf 1 q = ∑'_j (-1)^j q^(j(5j+1)/2)`.
Then combined with our Step 2/3, `rrJInf 1 q · (q;q)_∞ = theta` becomes the
identity to verify, OR rrJInf 1 q = theta directly and the product form
follows from Step 2's theta = mod-5 product divided appropriately.

NEEDS: re-derive exactly which `(q;q)_∞` factors land where, in this codebase's
convention, by carefully doing the N=0,1,2 base cases.

### Q3: Lean path

Prove finite Schur by **induction on N** using gaussianBinom's own three-term
recurrence. Do NOT derive from Ch03's q-binomial theorem (that gives
Euler/Gaussian expansions; Schur's R-R form has its own recurrence).

## Concrete next step

1. Define `schurLHS q N := ∑_{n} q^(n²) · gaussianBinom q (N-n) n` (finite, n ≤ N/2).
2. Define `schurRHS q N := ∑_{j} (-1)^j q^(j(5j+1)/2) · gaussianBinom q N (...)`.
3. Prove `schurLHS q N = schurRHS q N` by induction on N (three-term recurrence).
4. Tannery: both sides' N→∞ limits. Use Mathlib dominated convergence.
5. Identify limit with rrJInf 1 q and the theta sum.

Verify base cases N=0,1,2,3 by hand first to pin the exact index conventions.

## CRITICAL CORRECTION (2026-05-15, verified by hand)

ChatGPT's earlier Q2 answer "RHS Gaussian → 1" is **WRONG**. Correct analysis:

- Schur LHS `D_N := ∑_n q^(n²) · [N-n choose n]_q`. As N→∞ (n fixed):
  `[N-n choose n]_q = (q;q)_{N-n}/((q;q)_n·(q;q)_{N-2n}) → 1/(q;q)_n`
  (numerator/last-factor both → (q;q)_∞). Hence `D_∞ = rrJInf 1 q`.

- Schur RHS `e_N := ∑_j (-1)^j q^(j(5j+1)/2) · [N choose ⌊(N-5j)/2⌋]_q`.
  The central Gaussian `[N choose ~N/2]_q → 1/(q;q)_∞` (Euler central limit),
  NOT → 1. Hence `e_∞ = (∑'_j (-1)^j q^(j(5j+1)/2)) / (q;q)_∞`.

- Schur identity `D_N = e_N` ⟹ in the limit:
  **`rrJInf 1 q = theta_sum_1 / (q;q)_∞`**
  ⟺ **`rrJInf 1 q · (q;q)_∞ = theta_sum_1`**  ← exactly Step 4's `h_step1`. ✓

This confirms the Step 4 conditional theorem `rogersRamanujan_first_given_step1`
has the correct hypothesis shape.

## Recurrence (confirmed task 70bb2895)

`d_N = d_{N-1} + q^(N-1) · d_{N-2}`,  `d_0 = d_1 = 1`.

Verified: d_2 = d_1 + q·d_0 = 1+q; d_3 = d_2 + q²·d_1 = 1+q+q². ✓

Lean plan:
1. `rrPoly q : ℕ → ℂ` recursive (the d_N).
2. `rrPoly q N = ∑_{n} q^(n²) · gaussianBinom q (N-n) n` (induction via gaussianBinom Pascal).
3. RHS: prove the theta-Gaussian sum satisfies the same recurrence (hard reindex j↦j±1).
4. Two Tannery limits (LHS → rrJInf, RHS → theta/(q;q)_∞).
5. Conclude `rrJInf 1 q · (q;q)_∞ = theta_sum_1`, feed into `rogersRamanujan_first_given_step1`.

## STATUS 2026-05-15 — Steps 1.1, 1.2 DONE

Proved in `Chapter07_RRStep1.lean`:
- ✅ 1.1 `rrPoly` recurrence + sanity (d_0..d_4)
- ✅ 1.2 `rrPoly_eq_schurSum`: `rrPoly q N = ∑_n q^(n²)·gaussianBinom q (N-n) n`
  via `schur_termB_eq` + `schur_pascal_term` + `schurSum_recurrence`.
  **This was the crux combinatorial identity (Schur LHS).**

### Remaining gap (precise)

**1.3 Tannery LHS limit** (`lim_{N} schurSum q N = rrJInf 1 q`):
Tool available: `Ch03.gaussianBinom_mul_qPochhammer_eq`:
  `gaussianBinom q n m * qPochhammer q m * qPochhammer q (n-m) = qPochhammer q n`
So `gaussianBinom q (N-n) n = qPochhammer q (N-n) / (qPochhammer q n · qPochhammer q (N-2n))`.
As N→∞: `qPochhammer q (N-n) → (q;q)_∞`, `qPochhammer q (N-2n) → (q;q)_∞`,
ratio → `1/qPochhammer q n`. Need: dominated-convergence / Tannery's theorem
(uniform bound). `schurSum q N → ∑'_n q^(n²)/qPochhammer q n = rrJInf 1 q`.

**1.4 Schur RHS** (`rrPoly q N = schurRHS q N`): the theta-Gaussian closed form.
**SANITY-CHECK FAILURE (2026-05-15)**: the proposed parity-split form
`d_{2M} = ∑_{j=-M}^{M} (-1)^j q^(j(5j+1)/2) [2M choose M-j]_q`
computes at M=1 to `-q²+(1+q)-q³ = 1+q-q²-q³`, but
`rrPoly q 2 = schurSum q 2 = 1+q` (both proven). So this exact form is WRONG.

### CORRECT FORM FOUND & VERIFIED (2026-05-15, self-derived)

The bottom index uses **5j** (not 2j) with a floor:

```
D_n = ∑_{j∈ℤ} (-1)^j · q^(j(5j+1)/2) · [n choose ⌊(n-5j)/2⌋]_q
```

Sanity-verified against the proven `rrPoly` values:
- n=2: j=0 gives [2,1]_q=1+q, j=±1 out of range → Σ = 1+q = D_2 ✓
- n=3: j=0 gives [3,1]_q=1+q+q², j=±1 → 0 → Σ = 1+q+q² = D_3 ✓
- n=5: D_5 = 1+q+q²+q³+2q⁴+q⁵+q⁶ (from recurrence d_5=d_4+q⁴d_3);
  j=0: [5,2]_q; j=1: -q³; j=-1: -q²; Σ matches ✓

The earlier "2j" form was wrong. NO paper download needed — derived & checked.

### Lean implementation (Step 1.4)

Parity-split the floor `⌊(n-5j)/2⌋`:
- when `n-5j` even: bottom = `(n-5j)/2`
- when `n-5j` odd:  bottom = `(n-5j-1)/2`

Strategy: prove `rrPoly q n = schurRHS q n` by the SAME two-step induction
+ recurrence technique as `schurSum_recurrence`, but the q-Pascal split
needs the pentagonal reindex `j ↦ j±1` (the hard bookkeeping). Then Tannery.

Reusable correct helpers committed: `two_dvd_j_5j_add_one`, `pentExp5`
(generalized pentagonal exponent → ℕ).

## STATUS 2026-05-15 (late) — full architecture explicit

`Chapter07_RRStep1.lean` now contains the COMPLETE proof skeleton with
exactly ONE deep gap + 2 Tannery limits:

PROVEN:
- `rrPoly` recurrence + sanity (d_0..d_4)
- `schurSum` def + `schurSum_recurrence` (crux Pascal+reindex) + sanity
- `rrPoly_eq_schurSum` (Schur LHS) ✅
- `rrPoly_eq_of_recurrence` (GENERAL reduction, reusable)
- `schurRHS` def with CORRECT 5j form + sanity n=0,1,2,3 (= rrPoly)
- `tendsto_gaussianBinom_sub` (pointwise Tannery limit)
- `eulerPentagonalInfiniteProduct_ne_zero` (Ch4)
- CONDITIONAL: `rrPoly_eq_schurRHS_of_recurrence`,
  `schurSum_eq_schurRHS_of_recurrence` — given schurRHS recurrence,
  the FULL finite Schur identity holds.

REMAINING (3 lemmas, all well-specified):
1. **`schurRHS_recurrence`**: `schurRHS q (N+2) = schurRHS q (N+1) + q^(N+1)·schurRHS q N`.
   This IS Schur's 1917 theorem. Hard: integer-j sum + floor(schurBottom)
   + q-Pascal split + pentagonal reindex `j ↦ j±1`. Research-level proof,
   harder than `schurSum_recurrence`. Base cases `schurRHS_{0,1}` done.
2. **Tannery LHS** (1.3b): `schurSum q N → rrJInf 1 q` via
   `tendsto_tsum_of_dominated_convergence` + `tendsto_gaussianBinom_sub`
   + uniform bound (need dominating summable `bound n`).
3. **Tannery RHS** (1.5): `schurRHS q N → theta_sum_1 / (q;q)_∞` via
   central Gaussian `[N choose ⌊N/2⌋]_q → 1/(q;q)_∞`.

Then: `rrJInf 1 q = lim schurSum = lim schurRHS = theta/(q;q)_∞`
⟹ `rrJInf 1 q · (q;q)_∞ = theta_sum_1` ⟹ feed `rogersRamanujan_first_given_step1`.

The R-R first identity is fully reduced. The single research-level
blocker is `schurRHS_recurrence` (Schur 1917 pentagonal reindex).

## SCHUR REINDEX STRUCTURE (ChatGPT extended-pro, 2026-05-16)

The pentagonal cancellation, precise:

Let `P_j = j(5j+1)/2` (pentagonal exponent). Key recurrence on exponents:
**`P_j - P_{j-1} = 5j - 2`.**

Set `n = 5j + 2b` (so `b` is the Gaussian bottom parameter for index j).
After q-Pascal on `[n+2 choose ⌊(n+2-5j)/2⌋]_q`, the second (residual)
term reindexes via **`j ↦ j-1`** (even residual support → odd residual
support). The odd-case floor parameter: `b' = ⌊(2b+5)/2⌋ = b+2`.
Odd residual at `j'`: `R_{j'} = (-1)^{j-1} q^{P_{j-1}+n+1-(b+2)} C_n(b+1)`.
Exponent algebra: `P_{j-1}+n+1-(b+2) = P_{j-1}+5j+b-1 = P_j+b+1`, and the
Gaussian bottom matches (`b'-1 = b+1`). Hence **`R_{j'} = -R_j`** —
the residual pairs cancel, leaving exactly `schurRHS q (n+1) + q^(n+1)·schurRHS q n`.

### Lean encoding recommendation (ChatGPT)

Do NOT prove first-term / second-term identities separately, and do NOT
keep the `if … then n+1 else toNat` schurBottom throughout. Instead:
1. Define a **zero-extended integer-bottom Gaussian wrapper**
   `gBz q n (k : ℤ) := if 0 ≤ k ∧ k ≤ (n:ℤ) then gaussianBinom q n k.toNat else 0`.
2. Restate `schurRHS` via `gBz` over a unified `Finset.Icc` (ℤ).
3. Normalize all three sums (`schurRHS (n+2)`, `(n+1)`, `n`) to one large Icc.
4. Form the residual sum; split by parity of `(n:ℤ) - 5*j`.
5. `Finset.sum_bij` (or `sum_nbij'`) with `j ↦ j-1` mapping even-residual
   support to odd-residual support; the term map gives `R_{j'} = -R_j`.

This is cleaner than the if-then-else schurBottom or a global even/odd-n
floor-free rewrite. Implementation in progress.

## CRITICAL CORRECTION — final assembly approach (ChatGPT extended-pro, 2026-05-16)

**The naive termwise split is FALSE.** ChatGPT (extended-pro) explicitly warned:
the "first term after q-Pascal = schurRHS q (N+1)" identification does NOT
hold termwise — there is a parity mismatch between `⌊(N+2-5j)/2⌋` and
`⌊(N+1-5j)/2⌋`.

**Correct approach**: common Icc normalization + floor-bottom rewriting +
**residual/carry telescoping** (NOT a termwise first-term/second-term split).

The full ChatGPT skeleton was truncated (pipe cutoff + shared-bridge file
mixing with other agents' traffic — Kneser/poly answers landed in the
.md files instead). Key recovered phrase:
  "common Icc normalization, floor-bottom rewriting, and
   residual/carry telescoping—not the false termwise split."

### Building blocks PROVEN (committed, 0 sorry):
- `gBz` + `gBz_neg/gt/eq/natCast`
- `gBz_lower_pascal` (the q-Pascal step)
- `pent_int_nonneg`, `pent_int_succ` (P_j−P_{j−1}=5j−2), `pentExp5_succ`
- `schurRHSz` + `schurRHS_eq_schurRHSz`
- `schurRHS_{zero,one,two,three}` sanity = rrPoly

### Remaining (fresh-session, research-level):
1. `schurRHS_recurrence` via **residual/carry telescoping** (NOT termwise
   split). Needs the full ChatGPT skeleton re-requested in a clean session
   (ask ONE focused question, capture pipe stdout fully before bridge mixes).
2. Tannery LHS uniform bound: needs real infinite product `∏(1±‖q‖^i)`
   (A convergent, B>0) — analytic deep lemma, not in Mathlib.
3. Tannery RHS: central Gaussian `[N choose ⌊N/2⌋]_q → 1/(q;q)_∞`.

**Do NOT attempt the naive termwise split** — it is provably false (ChatGPT-confirmed).

**1.5 Tannery RHS limit**: central Gaussian `[N choose ~N/2]_q → 1/(q;q)_∞`.

Once 1.4's exact form is pinned, 1.4 proof = same recurrence technique as
`schurSum_recurrence` (Pascal + reindex j↦j±1). 1.3/1.5 are Tannery
(Mathlib dominated convergence on ℕ-sums).

### Architecture note

The crux (Schur LHS, 1.2) is done. Remaining 1.3/1.4/1.5 are well-defined
but substantial: ~2 Tannery limits + 1 reindex recurrence. The Schur RHS
exact-form lookup is the immediate blocker for 1.4. Could also bypass via
Bailey (Ch9) but that's blocked at N=8 q-Pfaff-Saalschütz.

## FULL CARRY-TELESCOPE SKELETON (ChatGPT extended-pro, 2026-05-16, new tab)

5 parts:
- P1: schurB (raw int floor (N-5j)/2), schurTermZ', gBz_schurBottom_eq_floor, schurRHSz_floor
- P2: bigJ = Icc(-N-3, N+3), schurTermZ'_{left,right}_zero, schurRHSz_common_range (N≤n≤N+2 → sum over bigJ)
- P3: schurResidual = T(N+2)-T(N+1)-q^(N+1)T(N); schurCarry (even-parity gated, exponent pentExp5 j + (B+1).toNat); schurResidual_eq_carry_sub (HEART, even/odd parity cases, needs gBz_even_residual + gBz_odd_residual)
- P4: sum_Icc_carry_telescope, schurCarry_{left,right}_zero, schurResidual_sum_zero (telescope → 0)
- P5: schurRHSz_recurrence via linear_combination hres

Two local Gaussian lemmas to self-derive from gBz_lower_pascal + upper Pascal:
  gBz_even_residual: gBz(N+2)(b+1) - gBz(N+1)b - q^(N+1)gBz N b = q^((b+1).toNat)·gBz N (b+1)
  gBz_odd_residual:  gBz(N+2)(b+1) - gBz(N+1)(b+1) - q^(N+1)gBz N b = q^(((N+1)-b).toNat)·gBz N (b-1)

## STATUS 2026-05-16 — finite Schur 1917 COMPLETE ✅ (build green, committed 744e283)

PROVEN & committed green (ba99678 = P1+P2+P3a+P3b):
- schurB/schurTermZ'/floor rewrite; bigJ common-range normalization
- gBz_zero_right; gBz_lower1/gBz_upper1 (unconditional single-step q-Pascal,
  all integer k, from gaussianBinom def recursion + gaussianBinom_pascal_alt)
- gBz_even_residual / gBz_odd_residual (Schur 1917 combinatorial core,
  two-Pascal-step cancellation; cross term killed by toNat-exponent match
  on 0<=b<=N or gBz q N b = 0)

P3c+P4+P5 (carry-telescope + unconditional identity) — build bsb53a3xq:
- schurResidual, schurCarry, schurResidual_eq_carry_sub (even branch direct;
  odd branch CASE-SPLITS on gBz q N (schurB N j - 1)=0 because the bare
  exponent identity hexp is only true in the non-vanishing regime 1<=b<=N+1,
  derived via not_and_or + gBz_neg/gBz_gt)
- sumIcc_sub_telescope (ℕ-induction, Finset.Icc insert; arg normalized so
  ring sees matching F atoms), schurCarry_left/right_zero,
  schurResidual_sum_zero, schurRHSz_recurrence, schurRHS_recurrence,
  rrPoly_eq_schurRHS, schurSum_eq_schurRHS (UNCONDITIONAL finite RR/Schur)

## NEXT (RR Step 5-7: finite -> infinite, Tannery) — multi-session

Goal: discharge `h_step1` of `rogersRamanujan_first_given_step1`
(Chapter07.lean:1433):
  rrJInf 1 q * eulerPentagonalInfiniteProduct q = ∑'_j (-1)^j q^(j(5j+1)/2)

Path: take N→∞ of `schurSum_eq_schurRHS q N`:
- LHS: schurSum q N = ∑_n q^(n²)·[N-n choose n]_q.  Tannery (dominated
  convergence) with `tendsto_gaussianBinom_sub` (RRStep1:240): per-n limit
  [N-n choose n]_q → 1/(q;q)_∞ summand; uniform ‖q‖-domination → rrJInf 1 q.
- RHS: schurRHS q N = ∑_j (-1)^j q^pent · [N choose ⌊(N-5j)/2⌋]_q.  Central
  Gaussian [N choose ⌊N/2⌋]_q → 1/(q;q)_∞; theta sum survives → ∑'_j ... .
- Combine: rrJInf 1 q · (q;q)_∞ = ∑'_j (-1)^j q^(j(5j+1)/2) = h_step1.
Tools: Mathlib `tendsto_tsum_of_dominated_convergence`
(Analysis/Normed/Group/Tannery.lean), `schurSum_eq_tsum` (RRStep1:210).
Open analytic sub-gap: uniform bound needs real infinite product
∏(1±‖q‖^i) convergence/positivity (not in Mathlib) — see earlier note.


## RR Step 5 DISPATCHED (2026-05-16)
ChatGPT extended-pro asked for `tendsto_schurSum_rrJInf` (LHS Tannery:
schurSum q N → rrJInf 1 q via tendsto_gaussianBinom_sub + dominated
convergence). Crux = uniform q-binomial bound (real ∏(1-‖q‖^i)>0).
RHS side: schurRHS q N → (∑'_j (-1)^j q^pent)·(1/(q;q)_∞) via central
Gaussian. Combine through proven schurSum_eq_schurRHS → h_step1 →
rogersRamanujan_first_given_step1 (Chapter07.lean:1433).

## RR Step 5 — ChatGPT crux insight (2026-05-16, b8vxos3z9)

CRUCIAL simplification (avoids q-Pochhammer infinite-product positivity):
use the CRUDE uniform bound
  ‖gaussianBinom q m n‖ ≤ (2 / (1 - ‖q‖))^n   (all m, ‖q‖<1)
derived from the product form
  gaussianBinom q m n = ∏_{i=1}^n (1-q^{m-n+i}) / ∏_{i=1}^n (1-q^i):
  each numerator factor ‖1-q^k‖ ≤ 1+‖q‖^k ≤ 2;
  each denominator factor ‖1-q^i‖ ≥ 1-‖q‖^i ≥ 1-‖q‖.
Then ‖q^{n²}·gaussianBinom q (N-n) n‖ ≤ ‖q‖^{n²}·(2/(1-‖q‖))^n, and
∑_n ‖q‖^{n²}·(2/(1-‖q‖))^n is summable because the n² exponent on ‖q‖
beats the geometric (2/(1-‖q‖))^n. "the factor ‖q‖^(n*n) wins immediately."
=> Tannery applies cleanly: schurSum q N → rrJInf 1 q.

DONE this session: Chapter07_RRStep5.lean with the LHS pointwise limit
`tendsto_schurTerm_rrJTerm` (no analytic gap, from tendsto_gaussianBinom_sub).
NEXT: (a) uniform-bound lemma via product form (need gaussianBinom product
identity in Ch03 — gaussianBinom_mul_qPochhammer_eq Ch03:342 or finite
product); (b) Tannery (`tendsto_tsum_of_dominated_convergence`-family in
Mathlib/Analysis/Normed/Group/Tannery.lean) → tendsto_schurSum_rrJInf;
(c) RHS central-Gaussian limit; (d) combine via schurSum_eq_schurRHS →
h_step1 → rogersRamanujan_first_given_step1.

## RR Step 5 LHS COMPLETE (2026-05-16, commit 44b0c43)

tendsto_schurSum_rrJInf : schurSum q N → rrJInf 1 q  [build green, 0 sorry]
Chain: tendsto_schurTerm_rrJTerm (9d4ca5c) + gaussianBinom_norm_le
(89d2147) + Mathlib tendsto_tsum_of_dominated_convergence.

## RR Step 5 RHS — concrete plan (infra located)

Goal: tendsto_schurRHS : schurRHS q N → (∑'_{j:ℤ} (-1)^j q^{j(5j+1)/2})
                                          / (q;q)_∞   as N→∞.
schurRHS q N = ∑_{j} (-1)^j q^pentExp5 j · gaussianBinom q N (schurBottom N j).
Central Gaussian: [N choose ⌊(N-5j)/2⌋]_q → 1/(q;q)_∞ as N→∞ (for each j).
Infra FOUND (Chapter03):
- gaussianBinom_center_add_mul_qPochhammer_eq (q) (n r) (r≤n):
    [2n choose n+r]_q · (q;q)_? = ...   (line 400)
- gaussianBinom_center_sub_mul_qPochhammer_eq                  (line 408)
- tendsto_qPoch_mul_gaussian_center_add (q) (hq) (r) :
    Tendsto (fun N => (q;q)_N · [2N choose N+r]_q) ...          (line 624)
- tendsto_qPoch_mul_gaussian_center_sub                         (line 664)
- tendsto_qPoch_mul_gaussian_center_pair                        (line 704)
RHS Tannery over ℤ (finite support per N via schurBottom range);
each term → (-1)^j q^pentExp5 j · 1/(q;q)_∞; combine →
(1/(q;q)_∞)·jacobiSeries. Then theta_sum_1_eq_jacobiSeries (Ch04:498)
connects ∑'_j to the product side.

## RR Step 6/7 — final assembly
schurSum_eq_schurRHS (744e283) + tendsto_schurSum_rrJInf (44b0c43)
+ tendsto_schurRHS  ⟹  rrJInf 1 q = jacobiSeries / (q;q)_∞
⟹ rrJInf 1 q · (q;q)_∞ = ∑'_j (-1)^j q^{j(5j+1)/2}  = h_step1
⟹ feed rogersRamanujan_first_given_step1 (Chapter07.lean:1433).

## RR Step 5 RHS per-j limit DONE (55d2480) + the real RHS gap

tendsto_gaussianBinom_center_schurBottom : [N choose ⌊(N-5j)/2⌋]_q → 1/(q;q)_∞
(build green, 0 sorry). Plus tendsto_schurBottom_atTop /
tendsto_sub_schurBottom_atTop.

REMAINING RHS ℤ-Tannery — genuine analytic gap:
schurRHS q N = ∑_{j∈Icc(-N-1)(N+1)} (-1)^j q^pentExp5 j ·[N choose ⌊(N-5j)/2⌋]_q.
Need Tannery over β=ℤ (Mathlib tendsto_tsum_of_dominated_convergence
handles general β). Bound per term: ‖q‖^pentExp5 j · C where C must be a
UNIFORM bound on ‖[N choose ⌊(N-5j)/2⌋]_q‖ independent of N,j.

THE OBSTRUCTION: for the CENTRAL Gaussian the crude per-factor bound is
(2/(1-‖q‖))^{k} with k≈N/2 → GROWS with N (not uniform). The ratio
qPoch q N/(qPoch q k·qPoch q(N-k)) needs
  ‖qPoch q m‖ ≤ ∏_{i≥1}(1+‖q‖^i) = P⁺ < ∞   (convergent infinite product)
  ‖qPoch q m‖ ≥ ∏_{i≥1}(1-‖q‖^i) = P⁻ > 0   (positive infinite product)
giving uniform ‖[N choose k]_q‖ ≤ P⁺/(P⁻)². P⁺<∞ and P⁻>0 are the
q-Pochhammer infinite-product convergence/positivity facts NOT in Mathlib
(the LHS crude-bound deliberately avoided these; the RHS center cannot).

NEXT-SESSION UNIT: develop (or locate) Lean lemmas
  Multipliable (fun i:ℕ => 1 + ‖q‖^(i+1))   [⇒ P⁺ < ∞]
  0 < ∏' i, (1 - ‖q‖^(i+1))   resp.  P⁻ > 0
(via Real.summable log / Multipliable.tprod_ne_zero / one_add_le_exp etc.),
then uniform central bound, then ℤ-Tannery → tendsto_schurRHS, then
combine with schurSum_eq_schurRHS + tendsto_schurSum_rrJInf → h_step1.

## RR Step 5 RHS gap — Mathlib API LOCATED (de-risked, 2026-05-16)

The q-Pochhammer infinite-product bounds ARE achievable with Mathlib
(file Mathlib/Analysis/SpecialFunctions/Log/Summable.lean):
- `Real.multipliable_of_summable_log (hfn : ∀ i, 0 < f i)
     (hf : Summable fun i ↦ log (f i)) : Multipliable f`
- `Real.multipliable_of_summable_log'` (eventually-positive variant)
- `Real.summable_log_one_add_of_summable (hf : Summable f) :
     Summable fun i ↦ log (1 + f i)`
- `Real.multipliable_one_add_of_summable` (⇒ P⁺ = ∏(1+‖q‖^{i+1}) < ∞)

CONCRETE next-session recipe:
1. P⁻ : 0 < ∏'_{i} (1 - ‖q‖^{i+1}).
   factors ∈ (0,1]; Summable (fun i ↦ log (1-‖q‖^{i+1})) since
   |log(1-x)| ≤ 2x for small x and ∑‖q‖^{i+1} summable (geometric).
   ⇒ Multipliable via Real.multipliable_of_summable_log; tprod > 0
   since all factors > 0 (Multipliable + pos ⇒ tprod_pos / induction on
   HasProd; or Real.tprod_pos if present).
2. Uniform lower bound: ‖qPochhammer q n‖ ≥ ∏_{i=1}^{n}(1-‖q‖^i)
   (norm_qPochhammer_ge gives the (1-‖q‖)^n form; instead bound each
   factor ‖1-q^i‖ ≥ 1-‖q‖^i and take the PARTIAL product, then
   partial ≥ ∏'_{i≥1} = P⁻ because each factor ≤ 1 ⇒
   monotone-decreasing partials ≥ infinite tail product).
   Likewise ‖qPochhammer q n‖ ≤ P⁺ uniformly.
3. Uniform central bound:
   ‖[N choose k]_q‖ = ‖qPoch N‖/(‖qPoch k‖·‖qPoch(N-k)‖) ≤ P⁺/(P⁻)².
4. ℤ-Tannery: tendsto_tsum_of_dominated_convergence with β = ℤ,
   bound j = ‖q‖^{pentExp5 j} · (P⁺/(P⁻)²), Summable over ℤ since
   pentExp5 j ~ 5j²/2 → ∞; pointwise = tendsto_gaussianBinom_center_schurBottom
   (already proven, 55d2480). ⇒ tendsto_schurRHS :
   schurRHS q N → (∑'_{j} (-1)^j q^{pentExp5 j}) / (q;q)_∞.
5. Combine: schurSum_eq_schurRHS + tendsto_schurSum_rrJInf (44b0c43)
   + tendsto_schurRHS ⇒ rrJInf 1 q · (q;q)_∞ = ∑'_j (-1)^j q^{j(5j+1)/2}
   = h_step1 ⇒ rogersRamanujan_first_given_step1 (Chapter07.lean:1433).

## RR Step 5 RHS — HARD GAP SOLVED (3dacb19). Remaining = pure assembly.

The documented hard analytic obstruction (uniform central q-binomial
bound) is SOLVED, NOT via fresh infinite-product machinery but via the
EXISTING convergence:
  qPochhammer_norm_uniform (Chapter07_RRStep5.lean): ∃ Blo>0 Bup, ∀n
    Blo ≤ ‖(q;q)_n‖ ≤ Bup   [tendsto_eulerPentagonalProductTrunc → E≠0,
    eventually-bound + finite-prefix inf'/sup']
  gaussianBinom_norm_le_uniform: ∃C≥0, ∀N k, k≤N → ‖[N choose k]_q‖ ≤ C
All RR Step 5 RHS hard pieces now proven & committed:
  tendsto_gaussianBinom_center_schurBottom (55d2480)  -- pointwise
  gaussianBinom_norm_le_uniform           (3dacb19)  -- domination

REMAINING = mechanical assembly (no hard analysis left):
A. theta ℤ-summability: Summable (fun j:ℤ => ‖q‖^(j*(5*j+1)/2)) from
   Ch02.summable_jacobiInfiniteSeries_terms (Y^5) (-Y) (‖Y^5‖<1) with
   Y²=q (IsAlgClosed.exists_pow_nat_eq gives Y), pushed through
   theta_sum_1_eq_jacobiSeries (Ch04:498). Norm version: ‖(-1)^j‖=1.
B. schurRHS as ℤ-tsum: schurRHS q N = ∑'_{j:ℤ} f N j where
   f N j = (-1)^j q^pentExp5 j · gBz q N (schurBottom N j); finite
   support = Icc(-N-1)(N+1) (gBz=0 outside) ⇒ tsum = the Finset sum
   (tsum_eq_sum / Finset.sum + zeros).
C. ℤ-Tannery: tendsto_tsum_of_dominated_convergence (β=ℤ):
   pointwise = const·tendsto_gaussianBinom_center_schurBottom,
   bound j = ‖q‖^pentExp5 j · C (by_cases schurBottom≤N: uniform else
   gBz=0), Summable from (A).  ⇒ tendsto_schurRHS :
   schurRHS q N → (∑'_j (-1)^j q^{j(5j+1)/2}) · (1/(q;q)_∞).
D. Step 6/7: schurSum_eq_schurRHS (744e283) + tendsto_schurSum_rrJInf
   (44b0c43) + tendsto_schurRHS ⇒ rrJInf 1 q = jacobiSeries/(q;q)_∞ ⇒
   rrJInf 1 q·(q;q)_∞ = ∑'_j(-1)^j q^{j(5j+1)/2} = h_step1 ⇒
   rogersRamanujan_first_given_step1 (Chapter07.lean:1433). RR Steps
   2/3/4 already done ⇒ Rogers-Ramanujan FIRST IDENTITY complete.

## ✅ ROGERS-RAMANUJAN FIRST IDENTITY — COMPLETE (2026-05-16, commit 3231a99)

UNCONDITIONAL, 0 sorry / 0 axiom across entire QseriesFormalization.
Full chain (all build-verified green, all pushed):

  RR Step 1  Schur 1917 finite identity   schurSum_eq_schurRHS   744e283
    ← q-Pascal helpers + gBz_even/odd_residual + carry-telescope  ba99678
  RR Step 5 LHS  tendsto_schurSum_rrJInf                          44b0c43
    ← pointwise tendsto_schurTerm_rrJTerm 9d4ca5c
    ← uniform crude bound gaussianBinom_norm_le 89d2147
  RR Step 5 RHS  tendsto_schurRHS                                 e0d1ebf
    ← per-j tendsto_gaussianBinom_center_schurBottom 55d2480
    ← uniform central bound gaussianBinom_norm_le_uniform 3dacb19
       (qPochhammer_norm_uniform via existing convergence — the
        documented hard analytic gap, SOLVED)
    ← theta ℤ-summability summable_norm_pentExp5 2b8e5a5
    ← schurRHS_eq_tsum 87bc7cb
  Step D  rrJInf_one_mul_eulerPentagonal_eq (= h_step1)           3231a99
       tendsto_nhds_unique of equal sequences ⇒
       rrJInf 1 q·(q;q)_∞ = ∑'_{j} (-1)^j q^{j(5j+1)/2}
  ⇒ rogersRamanujan_first :
       G(q)·(q;q^5)_∞·(q^4;q^5)_∞ = 1   (‖q‖<1, q≠0)
  (RR Steps 2/3/4 already complete from prior work; the final
   rogersRamanujan_first_given_step1 wiring closes the product form.)

THEOREM (Chapter07_RRStep5.lean):
  rogersRamanujan_first (q:ℂ) (hq:‖q‖<1) (hq_ne:q≠0) :
    rrJInf 1 q * (∏' n, rrMod5Factor q 1 n)
               * (∏' n, rrMod5Factor q 4 n) = 1

NEXT (multi-session): Rogers-Ramanujan SECOND identity (rrJInf q q,
theta_sum_2 path — symmetric, reuse this scaffold); then Chapters
5, 8-19 of Chan's book.

## RR SECOND identity — progress + H-Schur RHS finding (2026-05-16)

DONE & committed green (0 sorry/0 axiom), Chapter07_RRStep1H.lean:
- rrPolyH (e_{N+2}=e_{N+1}+q^{N+2}e_N), schurSumH = ∑ q^{n²+n}[N-n,n]_q,
  rrPolyH_eq_schurSumH (H-Schur LHS crux), schurSumH_eq_tsum  72eedba 6debdf2
- pentExp5H (j(5j+3)/2), two_dvd_j_5j_add_three, pentH_int_nonneg,
  pentH_int_succ, pentExp5H_succ                                9b16df0

H-SCHUR RHS CONVENTION — naive floor shifts FALSIFIED by hand-check
against verified rrPolyH (e_0=1, e_2=1+q², e_3=1+q²+q³):
  • bottom ⌊(N+1-5j)/2⌋ : schurRHSH 2 = 1+q  ≠ rrPolyH 2 = 1+q²  ✗
  • bottom ⌊(N-1-5j)/2⌋ : schurRHSH 0 = 0    ≠ rrPolyH 0 = 1     ✗
=> Schur's SECOND 1917 identity RHS is NOT a naive floor-shift of the
   G form (⌊(N-5j)/2⌋). Needs the actual reference form (Andrews,
   *The Theory of Partitions*, Ch.7 / Sills, *An Invitation to the
   Rogers–Ramanujan Identities*) — do NOT keep blind-guessing floors;
   two candidates already dead. Likely the H-RHS pairs differently
   (e.g. bottom involving N and a j-dependent shift not of the
   ⌊(N+c-5j)/2⌋ family, or a two-term/parity-split form).

NEXT-SESSION (with reference in hand): encode the correct schurBottomH
+ schurRHSH, verify schurRHSH_{0,2,3} = rrPolyH (build = sanity check,
same as G-side caught the 2j error), then mirror the G-side
gBz_even/odd_residual + carry-telescope + ℤ-Tannery + theta_sum_2
(Ch04:521) + a rogersRamanujan_second_given_step2 (to write, mirror
rogersRamanujan_first_given_step1 with q2·q3 products). Scaffold
(uniform/central bounds, summable_norm_pentExp5-analog, Tannery) all
reusable from RRStep5.

## RR Step 2 (second identity) — BLOCKED on input, 2026-05-16

The H-Schur RHS bottom index B_H(N,j) is required to proceed. Status:
- Naive ⌊(N±c-5j)/2⌋ floor family FALSIFIED (schurRHSH≠rrPolyH at N=0/2);
  structural analysis shows H-RHS needs multi-term j-cancellation at
  small N (no single [2 choose k]_q = 1+q²), i.e. genuinely different
  from the G form ⌊(N-5j)/2⌋ — NOT blind-guessable (Red Line: no 编故事).
- ChatGPT bridge (the sanctioned collaboration path) queried TWICE for
  the literature form (Andrews Thm 7.x / Sills): BOTH timed out
  ([BRIDGE_ERROR] response timeout @1190s, tasks bkdrxb3c2 & bpa0p5ah6).
  research-channel / extended-pro is non-responsive for this query.

NEXT-SESSION INPUT NEEDED (one of):
  (a) working ChatGPT bridge, or
  (b) the cited Schur-1917 second finite identity RHS from Andrews,
      *The Theory of Partitions*, Ch.7 (Schur polynomials) or Sills,
      *An Invitation to the Rogers–Ramanujan Identities*.
Then: encode schurBottomH/schurRHSH, build = sanity-check vs rrPolyH
(0,2,3 → 1, 1+q², 1+q²+q³), then mirror G-side gBz_even/odd_residual
+ carry-telescope + ℤ-Tannery (scaffold all reusable from RRStep5) +
theta_sum_2_eq_jacobiSeries (Ch04:521) + rogersRamanujan_second_given_step2
(write, mirror given_step1 with q2·q3 products).

All prior work (RR first identity COMPLETE; RR second identity LHS
crux rrPolyH_eq_schurSumH + H-pentagonal) committed green, 0 sorry/0
axiom: commits ba99678..c335b11, 72eedba, 6debdf2, 9b16df0.

## RR Step 2 — UNBLOCKED 2026-05-16: H-Schur RHS DERIVED + VERIFIED

The block above is resolved WITHOUT the bridge and WITHOUT guessing.
Method = the sanctioned one (derive from the proven LHS recurrence,
then cross-check against the independently-proven `rrPolyH` oracle —
same discipline that caught the G-side 2j error and the q⁵→q⁶ error).

The earlier structural note ("no single [2 choose k]_q = 1+q²") was
correct and was the key: the H form does NOT keep TOP = N. It uses
**TOP = N+1** (this is exactly what reconciles the e-recurrence's
q^{N+2} vs the natural two-q-Pascal-step q^{N+1}). With TOP = N+1 the
SAME G bottom floor and the SAME H pentagonal close it:

  e_N  =  Σ_j (-1)^j q^{j(5j+3)/2} · [ N+1 choose ⌊(N-5j)/2⌋ ]_q

(`gBz` zero-extends an out-of-range bottom; the ⌊·⌋ is the raw ℤ floor,
NOT the G-side `schurBottom` ℕ wrapper — that wrapper returns n+1 to
zero a TOP=n binomial, but here TOP=N+1 so a raw out-of-range index
must hit gBz's own 0, not [N+1 choose N+1]=1).

VERIFIED by hand against the proven rrPolyH (e_0..e_4 = 1, 1, 1+q²,
1+q²+q³, 1+q²+q³+q⁴+q⁶), all five exact:
- N=0 TOP=1: j=0 ⌊0/2⌋=0 [1,0]=1 → 1 = e_0 ✓
- N=1 TOP=2: j=0 ⌊1/2⌋=0 [2,0]=1 → 1 = e_1 ✓
- N=2 TOP=3: j=0 ⌊2/2⌋=1 [3,1]=1+q+q²; j=-1 (pent 1) ⌊7/2⌋=3
  [3,3]=1 term -q → 1+q²= e_2 ✓
- N=3 TOP=4: j=0 ⌊3/2⌋=1 [4,1]=1+q+q²+q³; j=-1 ⌊8/2⌋=4 [4,4]=1
  term -q → 1+q²+q³ = e_3 ✓
- N=4 TOP=5: j=0 ⌊4/2⌋=2 [5,2]=1+q+2q²+2q³+2q⁴+q⁵+q⁶; j=-1 ⌊9/2⌋=4
  [5,4]=[5,1]=1+q+q²+q³+q⁴ term -q·(…) → 1+q²+q³+q⁴+q⁶ = e_4 ✓

Encoding (Chapter07_RRStep1H.lean):
  schurBottomH N j := ((N:ℤ) - 5*j) / 2          -- raw ℤ floor
  schurRHSH q N := Σ_{j∈Icc(-(N)-1)(N+1)}
        (-1)^j · q^{pentExp5H j} · gBz q (N+1) (schurBottomH N j)
Build-level oracle: schurRHSH_{0,1,2,3,4} = rrPolyH_{0,1,2,3,4}.
Then mirror G carry-telescope with TOP shifted by 1 (the q^{N+2}
recurrence; gBz_upper1/lower1 reused) → schurSumH = schurRHSH, then
ℤ-Tannery (RRStep5H LHS done this session) + theta_sum_2 (Ch04) +
rogersRamanujan_second.

## RR Step 2 — carry-telescope recipe (precise, 2026-05-16)

Done so far this session (all committed+pushed, 0 sorry/0 axiom):
- 4491780  RRStep5H LHS Tannery  schurSumH → rrJInf q q
- 72446c9  schurBottomH/schurRHSH + 5 oracle-checks (DERIVED+VERIFIED)
- 8217251  rrPolyH_eq_schurRHSH_of_recurrence (conditional reduction)
- RRStep1: de-privatized gBz_even_residual, gBz_odd_residual,
  sumIcc_sub_telescope (now reusable by the H carry-telescope).

Remaining = the UNCONDITIONAL `schurRHSH_recurrence` (then
`rrPolyH_eq_schurRHSH` / `schurSumH_eq_schurRHSH` close trivially via
8217251). It is a faithful mirror of the G-side
`schurResidual_eq_carry_sub`/`schurRHSz_recurrence` (RRStep1 lines
~660–795) with these EXACT substitutions:

  schurB→schurBottomH,  schurTermZ'→schurTermHZ',
  schurRHSz→schurRHSH,  schurResidual→schurResidualH,
  schurCarry→schurCarryH,  pentExp5→pentExp5H,
  pent_int_succ→pentH_int_succ,  pent_int_nonneg→pentH_int_nonneg,
  gBz q N → gBz q (N+1)   [TOP shift],
  q^(N+1) → q^(N+2)       [recurrence weight],
  gBz_even_residual q N b → gBz_even_residual q (N+1) b,
  gBz_odd_residual  q N b → gBz_odd_residual  q (N+1) b.

Verified instantiation maths (M:=N+1):
  even: gBz_even_residual q (N+1) B gives
    gBz(N+3)(B+1) − gBz(N+2)B − q^{N+2} gBz(N+1)B = q^{(B+1)_+} gBz(N+1)(B+1)
  odd:  gBz_odd_residual q (N+1) B gives
    gBz(N+3)(B+1) − gBz(N+2)(B+1) − q^{N+2} gBz(N+1)B
      = q^{(N+2−B)_+} gBz(N+1)(B−1)
  parity flips with j→j+1 (5 odd); schurBottomH(N+2)j=B+1;
  even→schurBottomH(N+1)j=B; odd→=B+1; odd: schurBottomH N (j+1)=B−2.
  pent bookkeeping: pentH_int_succ(j+1) ⇒ pentExp5H(j+1)=pentExp5H j+5j+4.

KNOWN ALIGNMENT CAVEAT (cost the G-side a `show` rewrite): schurTermHZ'
q n j has gBz top `n+1`, so the three residual terms carry tops
`(N+2)+1, (N+1)+1, N+1` while `gBz_even_residual q (N+1)` emits
`(N+1)+2, (N+1)+1, (N+1)`. `(N+2)+1` vs `(N+1)+2` are defeq but `ring`
(inside `linear_combination`) treats them as distinct atoms — insert
`show (N+2)+1 = (N+1)+2 by omega`-style rewrites (or `simp only`
nat-normalization) BEFORE `linear_combination`, exactly as the summary
records for the G-side `F (a+↑k+1)` atom mismatch.

bigJH N := Icc (-(N:ℤ)-3) ((N:ℤ)+3); width 2N+7; endpoints
schurCarryH zero via gBz_gt / gBz_neg (public). schurRHSH_common_range:
Finset.sum_subset, out-of-range via schurTermHZ'_left/right_zero
(gBz_gt/gBz_neg + omega on the ℤ fdiv).
