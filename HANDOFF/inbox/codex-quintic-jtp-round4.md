# TASK round 4 (codex / gpt-5.5): transcribe the FULLY-WORKED η-period collapse

Round 3 pinned the exact blocker and the reparametrization. The mathematics is now **completely
worked out below** — your job this round is **Lean transcription**, not open-ended reasoning. Follow
the derivation; the coefficient/exponent arithmetic is all verified.

## Deliverable (sole)
Prove the two RHS Taylor expansions, then chain to the unconditional MBI:
```lean
HasFPowerSeriesOnBall (section83JTPProductAnalytic ζ)       (section83RhsPair14FMLS ζ) 0 1
HasFPowerSeriesOnBall (section83JTPProductAnalytic (ζ ^ 2)) (section83RhsPair23FMLS ζ) 0 1
```

## The complete worked derivation (pair14 case; z = ζ)

### Step 1 — JTP reparametrization to the triangular bilateral sum
Via `PartI.Ch02.jacobiTripleProduct` with `Y² = q`, argument `jacobiTripleProduct Y (-(ζ*Y))`
(as you found in round 3), the analytic product satisfies
```
(1 - ζ⁻¹) · section83JTPProductAnalytic ζ q  =  S(ζ, q) := ∑_{n∈ℤ} (-ζ)^n · q^{n(n+1)/2}.
```
(The scalar is `1 - ζ⁻¹ = 1 - ζ⁴`; track it carefully through the n=0 / shift bookkeeping —
this is the one place to be careful with the Ch02 convention.)

### Step 2 — residue split of S by n mod 5  (THE period collapse)
Write `n = 5m + r`, `m ∈ ℤ`, `r ∈ {0,1,2,3,4}`. Two exact facts (verified):
- **Coefficient:** `(-ζ)^{5m+r} = (-1)^{m+r} · ζ^r`  [because `(-1)^{5m}=(-1)^m`, `ζ^{5m}=1`].
- **Exponent:** `T(5m+r) = (25m² + 5m(2r+1))/2 + r(r+1)/2`  where `T(n)=n(n+1)/2`.

Match exponents to the two `q⁵`-base pentagonal APs (these ARE `section83A`, `section83B`):
- `section83A` = `pentagonal023SeriesPS` at q⁵, exponents `A(k) := (25k² − 5k)/2`  (= `5·k(5k−1)/2`).
- `q·section83B` exponents `B(k) := (25k² − 15k + 2)/2`  (= `1 + 5·k(5k−3)/2`).

Then, per residue class:
| r | exponent T(5m+r) | equals | coeff (−1)^{m+r}ζ^r |
|---|---|---|---|
| 0 | (25m²+5m)/2 | `A(−m)` | (−1)^m·1 |
| 4 | (25m²+45m+20)/2 | `A(m+1)` | (−1)^m·ζ⁴ |
| 1 | (25m²+15m+2)/2 | `B(−m)` | (−1)^{m+1}·ζ |
| 3 | (25m²+35m+12)/2 | `B(m+1)` | (−1)^{m+3}·ζ³ |
| 2 | (25m²+25m+6)/2 | (neither) | (−1)^{m}·ζ² |

**Per-exponent coefficient sums (verified):**
- For a fixed `k`, the q^{A(k)} coefficient gets r=0 (m=−k → (−1)^k) and r=4 (m=k−1 → −(−1)^kζ⁴):
  total `(−1)^k(1 − ζ⁴)`. So the A-part of S = `(1 − ζ⁴) · section83A`.
- For a fixed `k`, q^{B(k)} gets r=1 (m=−k → −(−1)^kζ) and r=3 (m=k−1 → (−1)^kζ³):
  total `(−1)^k(ζ³ − ζ)`. So the B-part of S = `(ζ³ − ζ) · q · section83B`.
- **r=2 vanishes:** its exponents pair under `m ↔ −1−m` (same exponent), and the coefficients cancel:
  `(−1)^m·ζ² + (−1)^{−1−m}·ζ² = ζ²((−1)^m + (−1)^{m+1}) = 0`. (Use `tsum_nat_add_neg_add_one` /
  the `n ↔ -n-1` pairing here — exactly the API you flagged.)

### Step 3 — collapse via the Gaussian-period algebra (already in the file)
Key identity (verify with your `quinticPeriod*` lemmas / `ring` over `ζ⁵=1`):
```
ζ³ − ζ = (1 − ζ⁴) · (ζ² + ζ³) = (1 − ζ⁴) · quinticPeriodBeta ζ.
```
Therefore `S = (1 − ζ⁴)·section83A + (1 − ζ⁴)·(quinticPeriodBeta ζ)·q·section83B
            = (1 − ζ⁴)·[ section83A + (quinticPeriodBeta ζ)·q·section83B ]`.
Combined with Step 1 (`(1−ζ⁻¹)·product = S`, and `1−ζ⁻¹ = 1−ζ⁴ ≠ 0`), cancel the scalar:
```
section83JTPProductAnalytic ζ q = section83A + (quinticPeriodBeta ζ)·q·section83B  (= section83RhsPair14).
```
That is the pointwise analytic identity; it gives the `HasFPowerSeriesOnBall ... section83RhsPair14FMLS`
(the RHS is a fixed convergent theta with the keystone's own `HasFPowerSeriesOnBall`).

### pair23 (z = ζ²)
Identical, with `ζ ↦ ζ²` (also primitive). The B-coefficient becomes
`(ζ²)²+(ζ²)³ = ζ⁴+ζ = quinticPeriodAlpha ζ`. Gives `section83RhsPair23`.

## Then chain to the unconditional MBI (do it this round if the above closes)
`section83JTPProductPS_eq_rhs_pair14/23_of_rhs_taylor` (already in the file) now fire unconditionally
→ (8.3.1)/(8.3.2); 5th-power them, apply `prod_sub_scaled_primitive_fifth_powerSeries`, multiply,
use `bookPeriod_pow_five_sum/mul`, bridge A,B to `quinticProductCore`, discharge `hfactor` in
`RamanujanQuintic.clean_quintic_of_factor_pair_product`, and state the UNCONDITIONAL
`most_beautiful_identity` (no hypotheses).

## Rules
- Edit ONLY `RamanujanQuinticJTP.lean`. NEVER `lake build`; verify
  `lake env lean QseriesFormalization/Pending/RamanujanQuinticJTP.lean`. 0 sorry/axiom/admit;
  fresh `#print axioms` clean. The math is done — if a Lean step resists, report the exact tactic
  state, do NOT abandon the approach. Reply to `HANDOFF/outbox/codex-quintic-jtp-round4-reply.md`.
