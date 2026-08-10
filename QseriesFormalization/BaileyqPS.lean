import QseriesFormalization.Chapter09

/-!
SCRATCH (not in build graph; not imported by QseriesFormalization.lean).
Develops the general q-Pfaff–Saalschütz kernel identity
  `baileyKernelSum a q ρ₁ ρ₂ n j = baileyKernelTarget a q ρ₁ ρ₂ n j`
which, once unconditional, upgrades `BaileyTransform_preserves_pair_general`
from conditional to unconditional. Keep 0 sorry here too once complete,
then migrate into Chapter09.lean.

True defs (verbatim from Chapter09.lean:13350, :13458, :13464):
  baileyTransformCoeff n k =
    (qPoch ρ₁ q k * qPoch ρ₂ q k * (a*q/(ρ₁*ρ₂))^k * qPoch (a*q/(ρ₁*ρ₂)) q (n-k))
    / (qPoch (a*q/ρ₁) q n * qPoch (a*q/ρ₂) q n * qPochhammer q (n-k))
  baileyKernelSum n j =
    ∑ k ∈ (range (n+1)).filter (j ≤ ·),
      baileyTransformCoeff n k / (qPochhammer q (k-j) * qPoch (a*q) q (k+j))
  baileyKernelTarget n j =
    qPoch ρ₁ q j * qPoch ρ₂ q j * (a*q/(ρ₁*ρ₂))^j
    / (qPoch (a*q/ρ₁) q j * qPoch (a*q/ρ₂) q j * qPochhammer q (n-j) * qPoch (a*q) q (n+j))
-/

open QseriesFormalization
open QseriesFormalization.PartII.Ch09

variable {R : Type*} [Field R]

set_option maxHeartbeats 0 in
/-- Building block: the consecutive-`k` ratio of `baileyTransformCoeff`.
For `k < n`,
  coeff(n,k+1) · (1 - (a*q/(ρ₁*ρ₂)) * q^(n-k-1))
    = coeff(n,k) · (1 - ρ₁*q^k) · (1 - ρ₂*q^k) · (a*q/(ρ₁*ρ₂)) · (1 - q^(n-k)).
Stated in cleared form (no division by the `(1 - b q^(n-k-1))` factor). -/
theorem baileyTransformCoeff_succ_k (a q ρ₁ ρ₂ : R) (n k : Nat) (hk : k < n)
    (hρ₁ : ρ₁ ≠ 0) (hρ₂ : ρ₂ ≠ 0)
    (hE₁ : qPoch (a * q / ρ₁) q n ≠ 0) (hE₂ : qPoch (a * q / ρ₂) q n ≠ 0)
    (hP : qPochhammer q (n - k - 1) ≠ 0)
    (hPq : (1 : R) - q ^ (n - k) ≠ 0) :
    baileyTransformCoeff a q ρ₁ ρ₂ n (k + 1)
        * (1 - (a * q / (ρ₁ * ρ₂)) * q ^ (n - k - 1))
      = baileyTransformCoeff a q ρ₁ ρ₂ n k
        * ((1 - ρ₁ * q ^ k) * (1 - ρ₂ * q ^ k)
            * (a * q / (ρ₁ * ρ₂)) * (1 - q ^ (n - k))) := by
  have hnk1 : n - (k + 1) = n - k - 1 := by omega
  obtain ⟨m, hm⟩ : ∃ m, n - k = m + 1 := ⟨n - k - 1, by omega⟩
  have hm1 : n - k - 1 = m := by omega
  have hpb : qPoch (a * q / (ρ₁ * ρ₂)) q (n - k)
      = qPoch (a * q / (ρ₁ * ρ₂)) q (n - k - 1)
        * (1 - (a * q / (ρ₁ * ρ₂)) * q ^ (n - k - 1)) := by
    rw [hm1, hm, qPoch_succ]
  have hpoch : qPochhammer q (n - k)
      = qPochhammer q (n - k - 1) * (1 - q ^ (n - k)) := by
    rw [hm1, hm, qPochhammer_succ]
  unfold baileyTransformCoeff
  rw [hnk1, qPoch_succ ρ₁ q k, qPoch_succ ρ₂ q k,
      pow_succ (a * q / (ρ₁ * ρ₂)) k, hpb, hpoch]
  field_simp
  try ring

/-
WIP — `baileyKernelTarget_succ_j` (the consecutive-`j` target shift, second
building block of the general q-Pfaff–Saalschütz induction).

STATEMENT (cleared form, verified algebraically correct — field_simp residual
confirms the structure): for `j < n`,
  target(n,j+1) · (1-(a*q/ρ₁)q^j)(1-(a*q/ρ₂)q^j)(1-a*q*q^(n+j))
    = target(n,j) · (1-ρ₁q^j)(1-ρ₂q^j)·(a*q/(ρ₁*ρ₂))·(1-q^(n-j)).

BLOCKER (precise): `unfold baileyKernelTarget; rw[qPoch_succ …]; field_simp;
ring` does NOT close it. field_simp *recombines* the opaque-qPoch denominators
into an expanded polynomial `ρ₁ρ₂ - ρ₁ a q^(j+1) - ρ₂ a q^(j+1) + a²q^(2j+2)`
(= `(ρ₁-aq^(j+1))(ρ₂-aq^(j+1))`) whose `≠ 0` it cannot discharge from the
factor-wise hypotheses, and a factored `hXX` does not syntactically match
field_simp's expanded normal form. This is the same reason the file's
`simp[qPoch,qPochhammer];field_simp;ring` kernel idiom only proves CONCRETE
small (n,j) instances — it does not generalise to symbolic indices.

SOLUTION PATH (next session): avoid field_simp on the full fraction. Unfold
baileyKernelTarget, apply qPoch_succ for every shifted index (ρ₁,ρ₂ at j+1;
aq/ρ₁,aq/ρ₂ at j+1 via qPoch_succ; qPoch(aq) at n+j+1 via haqn; qPochhammer at
n-j via hpoch) plus `div_pow` for b^j, then rewrite to a single-fraction
equality and close with `div_eq_div_iff hDj1 hDj` where hDj1, hDj are the
explicit denominator products `≠ 0` built by `mul_ne_zero` from the qPoch-atom
and (1-…) hypotheses (the file's hX-derivation pattern, Chapter09.lean
13496-13517, converts (1-aq/ρ·q^j)≠0 ↔ (ρ-aq^(j+1))≠0). The resulting
numerator identity is in opaque qPoch atoms appearing identically on both
sides (shifted only by the qPoch_succ (1-…) factors that also appear in the
multipliers), so plain `ring` closes it with no recombination.

The verified `baileyTransformCoeff_succ_k` above is the analogous (and simpler,
2-factor-denominator) coeff-side building block and is the template.
-/

/-- Peeling the lowest term `k = j` off `baileyKernelSum` (for `j ≤ n`).
The tail is the same filtered sum with `j` replaced by `j+1` in the filter
(NOT yet reindexed to `baileyKernelSum _ (j+1)` — that reindex is the q-WZ
step). This is the Finset-structural half of the downward induction and
does not touch the `b^j` fraction wall. -/
theorem baileyKernelSum_peel (a q ρ₁ ρ₂ : R) (n j : Nat) (hj : j ≤ n) :
    baileyKernelSum a q ρ₁ ρ₂ n j
      = baileyTransformCoeff a q ρ₁ ρ₂ n j / qPoch (a * q) q (2 * j)
        + ∑ k ∈ (Finset.range (n + 1)).filter (fun k => j + 1 ≤ k),
            baileyTransformCoeff a q ρ₁ ρ₂ n k /
              (qPochhammer q (k - j) * qPoch (a * q) q (k + j)) := by
  unfold baileyKernelSum
  have hset : (Finset.range (n + 1)).filter (fun k => j ≤ k)
      = insert j ((Finset.range (n + 1)).filter (fun k => j + 1 ≤ k)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
    omega
  have hjnotin : j ∉ (Finset.range (n + 1)).filter (fun k => j + 1 ≤ k) := by
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hset, Finset.sum_insert hjnotin]
  congr 1
  rw [Nat.sub_self, qPochhammer_zero, one_mul, ← two_mul]

set_option maxHeartbeats 0 in
/-- Summand shift: each peel-tail term (denominator indexed by `j`) relates to
the corresponding `baileyKernelSum _ (j+1)` term (denominator indexed by `j+1`)
by the explicit `k`-dependent factor `(1-a*q*q^(k+j))/(1-q^(k-j))`.
For `j + 1 ≤ k` (so `k - j ≥ 1`), in cleared form:
  S_j(k) · (1 - q^(k-j)) = S_{j+1}(k) · (1 - a*q*q^(k+j))
where S_j(k) = coeff n k / (qPochhammer q (k-j) · qPoch(a*q) q (k+j)). -/
theorem baileyKernelSum_summand_shift (a q ρ₁ ρ₂ : R) (n k j : Nat)
    (hk : j + 1 ≤ k)
    (hPm : qPochhammer q (k - j - 1) ≠ 0)
    (hAk : qPoch (a * q) q (k + j) ≠ 0)
    (hPq : (1 : R) - q ^ (k - j) ≠ 0)
    (hAqk : (1 : R) - a * q * q ^ (k + j) ≠ 0) :
    baileyTransformCoeff a q ρ₁ ρ₂ n k
        / (qPochhammer q (k - j) * qPoch (a * q) q (k + j))
        * (1 - q ^ (k - j))
      = baileyTransformCoeff a q ρ₁ ρ₂ n k
          / (qPochhammer q (k - j - 1) * qPoch (a * q) q (k + j + 1))
          * (1 - a * q * q ^ (k + j)) := by
  obtain ⟨m, hm⟩ : ∃ m, k - j = m + 1 := ⟨k - j - 1, by omega⟩
  have hm1 : k - j - 1 = m := by omega
  have hpoch : qPochhammer q (k - j)
      = qPochhammer q (k - j - 1) * (1 - q ^ (k - j)) := by
    rw [hm1, hm, qPochhammer_succ]
  have haqk : qPoch (a * q) q (k + j + 1)
      = qPoch (a * q) q (k + j) * (1 - a * q * q ^ (k + j)) := by
    rw [show k + j + 1 = (k + j) + 1 from rfl, qPoch_succ]
  rw [hpoch, haqk]
  field_simp [hPm, hAk, hPq, hAqk]
  try ring

/-- `baileyKernelTarget` as a single explicit fraction (resolves the nested
`b^j = (a*q)^j/(ρ₁*ρ₂)^j`), so the j-shift can be proved by `div_eq_div_iff`
+ `ring` on opaque qPoch atoms — no field_simp recombination. -/
theorem baileyKernelTarget_as_frac (a q ρ₁ ρ₂ : R) (n j : Nat) :
    baileyKernelTarget a q ρ₁ ρ₂ n j
      = (qPoch ρ₁ q j * qPoch ρ₂ q j * (a * q) ^ j)
        / ((ρ₁ * ρ₂) ^ j *
            (qPoch (a * q / ρ₁) q j * qPoch (a * q / ρ₂) q j
              * qPochhammer q (n - j) * qPoch (a * q) q (n + j))) := by
  unfold baileyKernelTarget
  rw [div_pow, ← mul_div_assoc, div_div]

/-
WIP — `baileyKernelTarget_succ_j` (5th building block; the last for the
downward q-PS induction). Statement (×ρ₁ρ₂ cleared, F(n,j) derived):
  KTgt(n,j+1)·(1-(aq/ρ₁)q^j)(1-(aq/ρ₂)q^j)(1-aq·q^(n+j))·(ρ₁ρ₂)
    = KTgt(n,j)·(1-ρ₁q^j)(1-ρ₂q^j)·(a*q)·(1-q^(n-j)).

CONFIRMED DEAD-END (not just diagnosed — tested this session): the field_simp
route fails even with ALL documented mitigations: `baileyKernelTarget_as_frac`
(qPoch opaque) + qPoch_succ/hpoch/haqn rewrites + pre-rewriting
`1-a*q/ρᵢ*q^j → (ρᵢ-a*q*q^j)/ρᵢ` (e1/e2) + factored `hX₁,hX₂ :
ρᵢ-a*q*q^j ≠ 0`. field_simp STILL recombines the two `(ρᵢ-a*q*q^j)`
denominator factors (both in D_{j+1}) into the EXPANDED product
`-(ρ₁q^{j+1}a)+(ρ₁ρ₂-q^{j+1}ρ₂a)+q²q^{2j}a²` whose ≠0 no factored
hypothesis matches (field_simp's discharger won't multiply hX₁·hX₂).

ONLY robust route: structural `div_eq_div_iff hD1 hD2` (NEVER field_simp),
with hD1=D_{j+1}≠0, hD2=Dj≠0 built explicitly by mul_ne_zero/pow_ne_zero,
then `ring` on the opaque-atom numerator identity. The earlier obstacle
(`div_mul_eq_mul_div` firing inside the `a*q/ρᵢ*q^j` factors) is removed by
applying e1/e2 FIRST (they turn those into `(ρᵢ-a*q*q^j)/ρᵢ`, no nested
`_/_*_`), THEN folding both sides to single fractions with explicit
`mul_div_assoc'`/`div_div` (targeted, not blanket div_mul_eq_mul_div),
THEN `div_eq_div_iff`. This is mechanical but multi-step careful work — a
clean next-session unit. `baileyKernelTarget_as_frac` (verified above) and
e1/e2 are the enablers.

Alternatively the q-WZ telescoping certificate W(k) (research crux) makes
the whole induction route; ChatGPT-pro is the user's intended tool for it
(focused query a0ca7bdb succeeded; heavy queries unreliable).
-/

/-- Downward-induction architecture for general q-Pfaff–Saalschütz.
Reduces the ENTIRE kernel identity (for all `j ≤ n`) to: the proved boundary
`baileyKernelSum_eq_target_n` (= `hbase`) and a single inductive `hstep`
(= peel + target-shift + q-WZ tail telescoping). This verifies the assembly
is sound and isolates exactly what remains. -/
theorem baileyKernelSum_eq_target_of_step (a q ρ₁ ρ₂ : R) (n : Nat)
    (hbase : baileyKernelSum a q ρ₁ ρ₂ n n = baileyKernelTarget a q ρ₁ ρ₂ n n)
    (hstep : ∀ j, j < n →
      baileyKernelSum a q ρ₁ ρ₂ n (j + 1) = baileyKernelTarget a q ρ₁ ρ₂ n (j + 1) →
      baileyKernelSum a q ρ₁ ρ₂ n j = baileyKernelTarget a q ρ₁ ρ₂ n j) :
    ∀ j, j ≤ n →
      baileyKernelSum a q ρ₁ ρ₂ n j = baileyKernelTarget a q ρ₁ ρ₂ n j := by
  intro j hj
  -- induct on the distance m = n - j, downward from the boundary j = n
  obtain ⟨m, hm⟩ : ∃ m, j = n - m := ⟨n - j, by omega⟩
  subst hm
  clear hj
  induction m with
  | zero => simpa using hbase
  | succ m ih =>
      by_cases hmn : m < n
      · -- n - (m+1) < n: apply hstep with IH at (n-(m+1))+1 = n-m
        have hlt : n - (m + 1) < n := by omega
        have hsucc : n - (m + 1) + 1 = n - m := by omega
        refine hstep (n - (m + 1)) hlt ?_
        rw [hsucc]; exact ih
      · -- n ≤ m: n-(m+1) = n-m = 0, degenerate
        have h1 : n - (m + 1) = n - m := by omega
        rw [h1]; exact ih

/-- Generic telescoping over peel's tail index set `{j+1,…,n}` (for `j ≤ n`):
if each term is `W(k+1) − W(k)`, the sum collapses to `W(n+1) − W(j+1)`.
This is the q-WZ telescoping mechanic for `hstep`, independent of the
specific certificate `W`. -/
theorem peelTail_telescope (W : Nat → R) (n j : Nat) (hj : j ≤ n) :
    ∑ k ∈ (Finset.range (n + 1)).filter (fun k => j + 1 ≤ k),
        (W (k + 1) - W k)
      = W (n + 1) - W (j + 1) := by
  have hset : (Finset.range (n + 1)).filter (fun k => j + 1 ≤ k)
      = Finset.Ico (j + 1) (n + 1) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [hset, Finset.sum_Ico_eq_sum_range]
  have hlen : n + 1 - (j + 1) = n - j := by omega
  rw [hlen]
  have h1 : j + 1 + (n - j) = n + 1 := by omega
  rw [show (∑ k ∈ Finset.range (n - j), (W (j + 1 + k + 1) - W (j + 1 + k)))
        = ∑ k ∈ Finset.range (n - j), (W (j + 1 + (k + 1)) - W (j + 1 + k))
      from rfl,
    Finset.sum_range_sub (fun t => W (j + 1 + t)) (n - j), h1]

/-- **hstep, fully assembled from the q-WZ certificate.** Given the per-term
telescoping identity `hA` (S_j(k) = G·S_{j+1}(k) + (Wf(k+1)-Wf k)), the
boundary values `hWtop`/`hWbot`, and the target shift `hB`
(KTgt(n,j)=G·KTgt(n,j+1)), the downward inductive step holds. Reduces general
q-Pfaff–Saalschütz to exactly the two certificate-guaranteed algebraic
identities `hA` and `hB`. Everything else is the verified peel + telescope. -/
theorem hstep_certified (a q ρ₁ ρ₂ : R) (n j : Nat) (hj : j < n)
    (G : R) (Wf : Nat → R)
    (IH : baileyKernelSum a q ρ₁ ρ₂ n (j + 1)
          = baileyKernelTarget a q ρ₁ ρ₂ n (j + 1))
    (hA : ∀ k ∈ (Finset.range (n + 1)).filter (fun k => j + 1 ≤ k),
            baileyTransformCoeff a q ρ₁ ρ₂ n k
                / (qPochhammer q (k - j) * qPoch (a * q) q (k + j))
            = G * (baileyTransformCoeff a q ρ₁ ρ₂ n k
                / (qPochhammer q (k - (j + 1)) * qPoch (a * q) q (k + (j + 1))))
              + (Wf (k + 1) - Wf k))
    (hWtop : Wf (n + 1) = 0)
    (hWbot : Wf (j + 1)
          = baileyTransformCoeff a q ρ₁ ρ₂ n j / qPoch (a * q) q (2 * j))
    (hB : baileyKernelTarget a q ρ₁ ρ₂ n j
          = G * baileyKernelTarget a q ρ₁ ρ₂ n (j + 1)) :
    baileyKernelSum a q ρ₁ ρ₂ n j = baileyKernelTarget a q ρ₁ ρ₂ n j := by
  rw [baileyKernelSum_peel a q ρ₁ ρ₂ n j (le_of_lt hj),
      Finset.sum_congr rfl hA, Finset.sum_add_distrib, ← Finset.mul_sum,
      peelTail_telescope Wf n j (le_of_lt hj)]
  have hsum_eq : (∑ k ∈ (Finset.range (n + 1)).filter (fun k => j + 1 ≤ k),
        baileyTransformCoeff a q ρ₁ ρ₂ n k
          / (qPochhammer q (k - (j + 1)) * qPoch (a * q) q (k + (j + 1))))
      = baileyKernelSum a q ρ₁ ρ₂ n (j + 1) := by
    simp only [baileyKernelSum]
  rw [hsum_eq, IH, hWtop, hWbot, hB]
  ring

/-- **General q-Pfaff–Saalschütz, conditional on the certificate.** If for
every `j < n` the per-term telescoping `hA`, boundary `hW*`, and target shift
`hB` hold, then the kernel identity holds for all `j ≤ n`. (Combines
`hstep_certified` with the verified `baileyKernelSum_eq_target_of_step`.) -/
theorem baileyKernelSum_eq_target_certified (a q ρ₁ ρ₂ : R) (n : Nat)
    (Gf : Nat → R) (Wf : Nat → Nat → R)
    (hstepData : ∀ j, j < n →
      baileyKernelSum a q ρ₁ ρ₂ n (j + 1)
        = baileyKernelTarget a q ρ₁ ρ₂ n (j + 1) →
      (∀ k ∈ (Finset.range (n + 1)).filter (fun k => j + 1 ≤ k),
            baileyTransformCoeff a q ρ₁ ρ₂ n k
                / (qPochhammer q (k - j) * qPoch (a * q) q (k + j))
            = Gf j * (baileyTransformCoeff a q ρ₁ ρ₂ n k
                / (qPochhammer q (k - (j + 1)) * qPoch (a * q) q (k + (j + 1))))
              + (Wf j (k + 1) - Wf j k))
      ∧ Wf j (n + 1) = 0
      ∧ Wf j (j + 1)
          = baileyTransformCoeff a q ρ₁ ρ₂ n j / qPoch (a * q) q (2 * j)
      ∧ baileyKernelTarget a q ρ₁ ρ₂ n j
          = Gf j * baileyKernelTarget a q ρ₁ ρ₂ n (j + 1)) :
    ∀ j, j ≤ n →
      baileyKernelSum a q ρ₁ ρ₂ n j = baileyKernelTarget a q ρ₁ ρ₂ n j := by
  apply baileyKernelSum_eq_target_of_step a q ρ₁ ρ₂ n
    (baileyKernelSum_eq_target_n a q ρ₁ ρ₂ n)
  intro j hjn IH
  obtain ⟨hA, hWtop, hWbot, hB⟩ := hstepData j hjn IH
  exact hstep_certified a q ρ₁ ρ₂ n j hjn (Gf j) (Wf j) IH hA hWtop hWbot hB


/-
WIP — (B) `tgt_shift_cleared`  (and by the same polynomial structure (A)).
Statement (cleared, A:=a*q): KTgt(n,j)·A(1-ρ₁q^j)(1-ρ₂q^j)(1-q^{n-j})
  = KTgt(n,j+1)·(ρ₁-Aq^j)(ρ₂-Aq^j)(1-Aq^{n+j}).
CONFIRMED ring-pathological (2026-05-16): proof via
`baileyKernelTarget_as_frac` + `simp[div_mul_eq_mul_div]` + `div_eq_div_iff
hDj hDj1` + qPoch_succ/haqn/hpoch + `field_simp[hρ₁,hρ₂]; ring` — the final
`ring` on the fully-cleared target-shift q-polynomial did NOT terminate in
15+ min under `maxHeartbeats 0` (scratch compile that is normally ~2 min;
killed). Same wall as the n=8 region (86–129 min CPU, never completed). The
algebra is certificate-guaranteed TRUE; this is purely a `ring`-tooling limit
on large multivariate q-polynomials, NOT a math gap.

SOLUTION (next): replace the terminal `ring` with a NON-`ring` closer —
`linear_combination` against the verified `baileyTransformCoeff_succ_k` / a
hand-supplied combination, OR explicit factor-by-factor `div`/`mul`
cancellation keeping qPoch atoms opaque (never expand into one giant
polynomial), OR `ring_nf` with aggressive atom abstraction. Same approach
will be needed for (A) `S_j(k)-G·S_{j+1}(k)=W(k+1)-W(k)` (also a large
cleared q-polynomial → brute `ring` will not terminate).

STATE: the 8 verified theorems above (incl. `hstep_certified`,
`baileyKernelSum_eq_target_certified`) stand — general q-Pfaff–Saalschütz is
machine-reduced to exactly (A),(B). What remains is purely the
`ring`-tooling-bound mechanical verification of two certificate-true
identities. Certificate in HANDOFF/cgpt_qWZ_certificate.txt.
-/

set_option maxHeartbeats 1600000 in
/-- **(A) per-term telescoping**, core rational identity (ChatGPT recipe):
mixed W forms — `Wbs` boundary-safe at k+1, `Word` ordinary at k. With these,
NO `coeff (k+1)` appears (k=n included); single atom `C := coeff n k`.
`S_j(k) - G·S_{j+1}(k) = Wbs(k+1) - Word(k)`, closed by recurrence-aligning
P,Q + q-power normalization + `field_simp; ring`. (A:=a*q, b:=a*q/(ρ₁*ρ₂).) -/
theorem per_term_telescope (a q ρ₁ ρ₂ : R) (n k j : Nat) (hjk : j + 1 ≤ k)
    (hkn : k ≤ n)
    (hρ₁ : ρ₁ ≠ 0) (hρ₂ : ρ₂ ≠ 0) (ha : a ≠ 0) (hq : q ≠ 0)
    (hPm : qPochhammer q (k - j - 1) ≠ 0)
    (hQ : qPoch (a * q) q (k + j) ≠ 0)
    (hR₁ : (1 : R) - ρ₁ * q ^ j ≠ 0) (hR₂ : (1 : R) - ρ₂ * q ^ j ≠ 0)
    (hQnj : (1 : R) - q ^ (n - j) ≠ 0)
    (hkj : (1 : R) - q ^ (k - j) ≠ 0)
    (hAkj : (1 : R) - a * q * q ^ (k + j) ≠ 0)
    (hAjk : (1 : R) - a * q * q ^ (j + k) ≠ 0) :
    baileyTransformCoeff a q ρ₁ ρ₂ n k
        / (qPochhammer q (k - j) * qPoch (a * q) q (k + j))
      = ((ρ₁ - a * q * q ^ j) * (ρ₂ - a * q * q ^ j) * (1 - a * q * q ^ (n + j))
          / (a * q * (1 - ρ₁ * q ^ j) * (1 - ρ₂ * q ^ j) * (1 - q ^ (n - j))))
          * (baileyTransformCoeff a q ρ₁ ρ₂ n k
            / (qPochhammer q (k - (j + 1)) * qPoch (a * q) q (k + (j + 1))))
        + ( baileyTransformCoeff a q ρ₁ ρ₂ n k
              / (qPochhammer q (k - j) * qPoch (a * q) q (k + j))
            * ((1 - ρ₁ * q ^ k) * (1 - ρ₂ * q ^ k) * (1 - a * q * q ^ (2 * j))
                * (1 - q ^ (n - k)))
            / ((1 - ρ₁ * q ^ j) * (1 - ρ₂ * q ^ j) * (1 - q ^ (n - j))
                * (1 - a * q * q ^ (j + k)))
          - baileyTransformCoeff a q ρ₁ ρ₂ n k
              / (qPochhammer q (k - j) * qPoch (a * q) q (k + j))
            * ((1 - q ^ (k - j)) * (1 - a * q * q ^ (2 * j))
                * (1 - (a * q / (ρ₁ * ρ₂)) * q ^ (n - k)))
            / ((a * q / (ρ₁ * ρ₂)) * (1 - ρ₁ * q ^ j) * (1 - ρ₂ * q ^ j)
                * (1 - q ^ (n - j))) ) := by
  have hkj1 : k - (j + 1) = k - j - 1 := by omega
  have hkj2 : k + (j + 1) = k + j + 1 := by omega
  -- Change of variables: d := k-j-1, e := n-k (eliminates all Nat subtraction
  -- in q-exponents; everything becomes linear sums in j,d,e; pow_add normalizes)
  obtain ⟨d, hd⟩ : ∃ dd, k = j + 1 + dd := ⟨k - (j + 1), by omega⟩
  obtain ⟨e, he⟩ : ∃ ee, n = j + 1 + d + ee := ⟨n - (j + 1 + d), by omega⟩
  subst hd; subst he
  -- After subst: k-j = d+1, k-j-1 = d, k+j = 2j+1+d, n-j = d+1+e, n-k = e,
  -- j+k = 2j+1+d, n+j = 2j+1+d+e, 2*j = 2*j. All additions, no subtraction.
  simp only [show j + 1 + d - j = d + 1 from by omega,
             show j + 1 + d - (j + 1) = d from by omega,
             show j + 1 + d + j = 2 * j + 1 + d from by omega,
             show j + 1 + d + (j + 1) = 2 * j + 2 + d from by omega,
             show j + (j + 1 + d) = 2 * j + 1 + d from by omega,
             show j + 1 + d + e - j = d + 1 + e from by omega,
             show j + 1 + d + e - (j + 1 + d) = e from by omega,
             show j + 1 + d + e + j = 2 * j + 1 + d + e from by omega,
             show 2 * (j + 1 + d) = 2 * j + 2 + 2 * d from by omega,
             show 2 * j + 1 + d + 1 = 2 * j + 2 + d from by omega] at *
  -- Recurrences (now clean: indices are sums)
  have hP : qPochhammer q (d + 1) = qPochhammer q d * (1 - q ^ (d + 1)) := by
    rw [show d + 1 = d + 1 from rfl, qPochhammer_succ]
  have hQs : qPoch (a * q) q (2 * j + 2 + d)
      = qPoch (a * q) q (2 * j + 1 + d) * (1 - a * q * q ^ (2 * j + 1 + d)) := by
    rw [show 2 * j + 2 + d = (2 * j + 1 + d) + 1 from by omega, qPoch_succ]
  rw [hP, hQs]
  -- Commuted nonzeros for field_simp
  have hR₁c : (1 : R) - q ^ j * ρ₁ ≠ 0 := by rw [mul_comm]; exact hR₁
  have hR₂c : (1 : R) - q ^ j * ρ₂ ≠ 0 := by rw [mul_comm]; exact hR₂
  -- Clear all denominators
  field_simp [hPm, hQ, hR₁, hR₂, hR₁c, hR₂c, hQnj, hkj, hAkj, hAjk,
    hρ₁, hρ₂, ha, hq]
  -- Normalize all q-powers to products of q^j, q^d, q^e, q via pow_add/pow_succ
  simp only [pow_add, pow_succ, pow_zero, one_mul, pow_mul, pow_one,
    two_mul, Nat.add_eq, Nat.add_zero]
  ring

set_option maxHeartbeats 0 in
/-- **(B) TGT_SHIFT** with explicit G, proved via `baileyKernelTarget_as_frac`
+ `div_eq_div_iff` + change-of-variables `n = j+1+e` (same technique as (A)).
Cleared form (×G-denominator):
  KTgt(n,j)·A(1-ρ₁q^j)(1-ρ₂q^j)(1-q^{n-j})
    = KTgt(n,j+1)·(ρ₁-Aq^j)(ρ₂-Aq^j)(1-Aq^{n+j}). -/
theorem tgt_shift_cleared (a q ρ₁ ρ₂ : R) (n j : Nat) (hj : j < n)
    (hρ₁ : ρ₁ ≠ 0) (hρ₂ : ρ₂ ≠ 0)
    (hDj : (ρ₁ * ρ₂) ^ j *
        (qPoch (a * q / ρ₁) q j * qPoch (a * q / ρ₂) q j
          * qPochhammer q (n - j) * qPoch (a * q) q (n + j)) ≠ 0)
    (hDj1 : (ρ₁ * ρ₂) ^ (j + 1) *
        (qPoch (a * q / ρ₁) q (j + 1) * qPoch (a * q / ρ₂) q (j + 1)
          * qPochhammer q (n - (j + 1)) * qPoch (a * q) q (n + (j + 1))) ≠ 0) :
    baileyKernelTarget a q ρ₁ ρ₂ n j
        * ((a * q) * (1 - ρ₁ * q ^ j) * (1 - ρ₂ * q ^ j) * (1 - q ^ (n - j)))
      = baileyKernelTarget a q ρ₁ ρ₂ n (j + 1)
        * ((ρ₁ - a * q * q ^ j) * (ρ₂ - a * q * q ^ j)
            * (1 - a * q * q ^ (n + j))) := by
  -- Change of variables: e := n - j - 1, so n = j + 1 + e
  obtain ⟨e, he⟩ : ∃ ee, n = j + 1 + ee := ⟨n - (j + 1), by omega⟩
  subst he
  -- Normalize all Nat index expressions to sums in j, e
  simp only [show j + 1 + e - j = e + 1 from by omega,
             show j + 1 + e - (j + 1) = e from by omega,
             show j + 1 + e + j = 2 * j + 1 + e from by omega,
             show j + 1 + e + (j + 1) = 2 * j + 2 + e from by omega] at *
  rw [baileyKernelTarget_as_frac a q ρ₁ ρ₂ (j + 1 + e) j,
      baileyKernelTarget_as_frac a q ρ₁ ρ₂ (j + 1 + e) (j + 1)]
  simp only [show j + 1 + e - j = e + 1 from by omega,
             show j + 1 + e - (j + 1) = e from by omega,
             show j + 1 + e + j = 2 * j + 1 + e from by omega,
             show j + 1 + e + (j + 1) = 2 * j + 2 + e from by omega] at *
  -- Clear fractions via div_eq_div_iff (denominators are opaque-atom products)
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_div_iff hDj hDj1]
  -- Expand j+1 atoms via qPoch_succ / pow_succ
  rw [qPoch_succ ρ₁ q j, qPoch_succ ρ₂ q j,
      qPoch_succ (a * q / ρ₁) q j, qPoch_succ (a * q / ρ₂) q j,
      pow_succ (a * q) j, pow_succ (ρ₁ * ρ₂) j,
      show qPochhammer q (e + 1) = qPochhammer q e * (1 - q ^ (e + 1)) from
        qPochhammer_succ q e,
      show qPoch (a * q) q (2 * j + 2 + e) =
          qPoch (a * q) q (2 * j + 1 + e) * (1 - a * q * q ^ (2 * j + 1 + e)) from
        by rw [show 2 * j + 2 + e = (2 * j + 1 + e) + 1 from by omega, qPoch_succ]]
  -- Clear /ρ from (1-(a*q/ρ)*q^j) factors + normalize q-powers
  field_simp [hρ₁, hρ₂]
  try { simp only [pow_add, pow_succ, pow_zero, one_mul, pow_mul, pow_one,
    two_mul, Nat.add_eq, Nat.add_zero]; ring }

/-- Derive KTgt(n,j) = G·KTgt(n,j+1) from the cleared product form
`tgt_shift_cleared`, by dividing both sides by the G-denominator factors. -/
theorem tgt_shift_div (a q ρ₁ ρ₂ : R) (n j : Nat) (hj : j < n)
    (hρ₁ : ρ₁ ≠ 0) (hρ₂ : ρ₂ ≠ 0)
    (ha : a ≠ 0) (hq : q ≠ 0)
    (hR₁ : (1 : R) - ρ₁ * q ^ j ≠ 0) (hR₂ : (1 : R) - ρ₂ * q ^ j ≠ 0)
    (hQnj : (1 : R) - q ^ (n - j) ≠ 0)
    (hDj : (ρ₁ * ρ₂) ^ j *
        (qPoch (a * q / ρ₁) q j * qPoch (a * q / ρ₂) q j
          * qPochhammer q (n - j) * qPoch (a * q) q (n + j)) ≠ 0)
    (hDj1 : (ρ₁ * ρ₂) ^ (j + 1) *
        (qPoch (a * q / ρ₁) q (j + 1) * qPoch (a * q / ρ₂) q (j + 1)
          * qPochhammer q (n - (j + 1)) * qPoch (a * q) q (n + (j + 1))) ≠ 0) :
    baileyKernelTarget a q ρ₁ ρ₂ n j =
      ((ρ₁ - a * q * q ^ j) * (ρ₂ - a * q * q ^ j) * (1 - a * q * q ^ (n + j))
        / ((a * q) * (1 - ρ₁ * q ^ j) * (1 - ρ₂ * q ^ j) * (1 - q ^ (n - j))))
      * baileyKernelTarget a q ρ₁ ρ₂ n (j + 1) := by
  have hAq : a * q ≠ 0 := mul_ne_zero ha hq
  have hD : (a * q) * (1 - ρ₁ * q ^ j) * (1 - ρ₂ * q ^ j) * (1 - q ^ (n - j)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hAq hR₁) hR₂) hQnj
  rw [div_mul_eq_mul_div, eq_div_iff hD, mul_comm]
  simpa only [mul_assoc, mul_comm, mul_left_comm] using
    tgt_shift_cleared a q ρ₁ ρ₂ n j hj hρ₁ hρ₂ hDj hDj1

/-! ### Assembly: from (A),(B) to unconditional general q-PS

The strategy for the final assembly:

1. Define `Gf j` (the G fraction) — matches `tgt_shift_div`'s RHS coefficient.
2. Define `Wf j k` (boundary-safe Gosper certificate) — the boundary-safe form
   `S_j(k-1)·factors` valid for `j+1 ≤ k ≤ n+1`.
3. Prove `hWtop`: `Wf j (n+1) = 0` — factor `(1-q^0) = 0` kills it.
4. Prove `hWbot`: `Wf j (j+1) = S_j(j) = coeff(n,j)/qPoch(A,q,2j)` —
   cancel `(1-ρ₁q^j)/(1-ρ₁q^j)` etc.
5. Prove `Word_eq_Wbs` bridge: the ordinary-form W at k equals boundary-safe at k.
   Uses the COEFF recurrence (`baileyTransformCoeff_succ_k`).
6. Feed into `hstep_certified` → `baileyKernelSum_eq_target_certified`.

Below: boundary values (hWtop, hWbot) which are purely structural.
The bridge and final assembly will follow.
-/

/-- Boundary-safe W at k = j+1 equals the peel head term
`coeff(n,j) / qPoch(aq) q (2j)`. At k=j+1 the boundary-safe form gives
`S_j(j) · (matching factors) / (matching factors)` = `S_j(j)` = head. -/
theorem Wbs_bot_eq_head (a q ρ₁ ρ₂ : R) (n j : Nat) (hj : j < n)
    (hR₁ : (1 : R) - ρ₁ * q ^ j ≠ 0) (hR₂ : (1 : R) - ρ₂ * q ^ j ≠ 0)
    (hQnj : (1 : R) - q ^ (n - j) ≠ 0)
    (hA2j : (1 : R) - a * q * q ^ (2 * j) ≠ 0) :
    baileyTransformCoeff a q ρ₁ ρ₂ n j
        / (qPochhammer q 0 * qPoch (a * q) q (2 * j))
      * ((1 - ρ₁ * q ^ j) * (1 - ρ₂ * q ^ j) * (1 - a * q * q ^ (2 * j))
          * (1 - q ^ (n - j)))
      / ((1 - ρ₁ * q ^ j) * (1 - ρ₂ * q ^ j) * (1 - q ^ (n - j))
          * (1 - a * q * q ^ (2 * j)))
      = baileyTransformCoeff a q ρ₁ ρ₂ n j / qPoch (a * q) q (2 * j) := by
  rw [qPochhammer_zero, one_mul]
  have hDen :
      ((1 - ρ₁ * q ^ j) * (1 - ρ₂ * q ^ j) * (1 - q ^ (n - j))
          * (1 - a * q * q ^ (2 * j))) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hR₁ hR₂) hQnj) hA2j
  rw [div_eq_iff hDen]
  ring

/-- The elementary cancellation underlying the bridge between the two forms
of the q-WZ certificate.  Its variables stand for whole q-Pochhammer and
linear factors, so the identity records only the multiplicative structure. -/
private theorem word_algebra
    (C P Q x y r s t z h B u v w : R)
    (hP : P ≠ 0) (hQ : Q ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0)
    (hh : h ≠ 0) (hB : B ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0)
    (hw : w ≠ 0) :
    (C * r * s * B * z / h) / (P * x * (Q * y)) * (x * t * h) /
          (B * u * v * w) =
      C / (P * Q) * (r * s * t * z) / (u * v * w * y) := by
  field_simp [hP, hQ, hx, hy, hh, hB, hu, hv, hw]

set_option maxHeartbeats 0 in
/-- **Bridge lemma**: the ordinary certificate at `k` equals its boundary-safe
form.  Write `k = j + 1 + d` and `n = k + e`.  The consecutive-coefficient
identity replaces `C(k)` by `C(k-1)` times the four new factors; the two
q-Pochhammer recurrences expose precisely the factors that cancel. -/
theorem Word_eq_Wbs (a q ρ₁ ρ₂ : R) (n k j : Nat)
    (hjk : j + 1 ≤ k) (hkn : k ≤ n)
    (hρ₁ : ρ₁ ≠ 0) (hρ₂ : ρ₂ ≠ 0) (ha : a ≠ 0) (hq : q ≠ 0)
    (hPm1 : qPochhammer q (k - j - 1) ≠ 0)
    (hQkj : qPoch (a * q) q (k + j) ≠ 0)
    (hQk1j : qPoch (a * q) q (k - 1 + j) ≠ 0)
    (hR₁ : (1 : R) - ρ₁ * q ^ j ≠ 0) (hR₂ : (1 : R) - ρ₂ * q ^ j ≠ 0)
    (hQnj : (1 : R) - q ^ (n - j) ≠ 0)
    (hkj : (1 : R) - q ^ (k - j) ≠ 0)
    (hAjk1 : (1 : R) - a * q * q ^ (j + (k - 1)) ≠ 0)
    (hE₁ : qPoch (a * q / ρ₁) q n ≠ 0) (hE₂ : qPoch (a * q / ρ₂) q n ≠ 0)
    (hPnk : qPochhammer q (n - k) ≠ 0)
    (hQnk1 : (1 : R) - q ^ (n - k + 1) ≠ 0)
    (hBqnk : (1 : R) - (a * q / (ρ₁ * ρ₂)) * q ^ (n - k) ≠ 0) :
    -- Ordinary form at k (the `-` expression in per_term_telescope):
    baileyTransformCoeff a q ρ₁ ρ₂ n k
        / (qPochhammer q (k - j) * qPoch (a * q) q (k + j))
      * ((1 - q ^ (k - j)) * (1 - a * q * q ^ (2 * j))
          * (1 - (a * q / (ρ₁ * ρ₂)) * q ^ (n - k)))
      / ((a * q / (ρ₁ * ρ₂)) * (1 - ρ₁ * q ^ j) * (1 - ρ₂ * q ^ j)
          * (1 - q ^ (n - j)))
    = -- Boundary-safe form at k (using S_j(k-1)):
    baileyTransformCoeff a q ρ₁ ρ₂ n (k - 1)
        / (qPochhammer q (k - 1 - j) * qPoch (a * q) q (k - 1 + j))
      * ((1 - ρ₁ * q ^ (k - 1)) * (1 - ρ₂ * q ^ (k - 1))
          * (1 - a * q * q ^ (2 * j)) * (1 - q ^ (n + 1 - k)))
      / ((1 - ρ₁ * q ^ j) * (1 - ρ₂ * q ^ j) * (1 - q ^ (n - j))
          * (1 - a * q * q ^ (j + (k - 1)))) := by
  -- Change of variables: d := k-j-1, e := n-k
  obtain ⟨d, hd⟩ : ∃ dd, k = j + 1 + dd := ⟨k - (j + 1), by omega⟩
  obtain ⟨e, he⟩ : ∃ ee, n = j + 1 + d + ee := ⟨n - (j + 1 + d), by omega⟩
  subst hd; subst he
  -- Normalize indices (all Nat subtraction → sums)
  simp only [show j + 1 + d - j = d + 1 from by omega,
             show j + 1 + d + j = 2 * j + 1 + d from by omega,
             show j + 1 + d - 1 = j + d from by omega,
             show j + 1 + d + e - j = d + 1 + e from by omega,
             show j + 1 + d + e - (j + 1 + d) = e from by omega,
             show j + 1 + d + e + 1 - (j + 1 + d) = e + 1 from by omega] at *
  -- Use COEFF at index j+d to replace C(j+1+d) with C(j+d)·(factors)/(1-bq^e)
  have hPnk' : qPochhammer q ((j + 1 + d + e) - (j + d) - 1) ≠ 0 := by
    simpa only [show (j + 1 + d + e) - (j + d) - 1 = e by omega] using hPnk
  have hQnk1' : (1 : R) - q ^ ((j + 1 + d + e) - (j + d)) ≠ 0 := by
    simpa only [show (j + 1 + d + e) - (j + d) = e + 1 by omega] using hQnk1
  have hcoeff := baileyTransformCoeff_succ_k a q ρ₁ ρ₂ (j + 1 + d + e) (j + d)
    (by omega : j + d < j + 1 + d + e) hρ₁ hρ₂ hE₁ hE₂ hPnk' hQnk1'
  -- hcoeff : C(j+d+1) * (1-b·q^e) = C(j+d) * (1-ρ₁q^{j+d})(1-ρ₂q^{j+d}) * b * (1-q^{e+1})
  -- Solve for C(j+1+d):
  have hBne : (1 - (a * q / (ρ₁ * ρ₂)) * q ^ e) ≠ 0 := hBqnk
  -- hcoeff gives: C(j+d+1) * (1-b*q^e) = C(j+d) * stuff
  -- Solve: C(j+d+1) = C(j+d) * stuff / (1-b*q^e)
  have h1 : (j + 1 + d + e) - (j + d) - 1 = e := by omega
  have h2 : (j + 1 + d + e) - (j + d) = e + 1 := by omega
  rw [h1, h2] at hcoeff
  have hC_eq : baileyTransformCoeff a q ρ₁ ρ₂ (j + 1 + d + e) (j + d + 1)
      = baileyTransformCoeff a q ρ₁ ρ₂ (j + 1 + d + e) (j + d)
        * ((1 - ρ₁ * q ^ (j + d)) * (1 - ρ₂ * q ^ (j + d))
            * (a * q / (ρ₁ * ρ₂)) * (1 - q ^ (e + 1)))
        / (1 - (a * q / (ρ₁ * ρ₂)) * q ^ e) := by
    -- From hcoeff: C(j+d+1) * X = C(j+d) * Y, so C(j+d+1) = C(j+d)*Y/X
    rw [eq_div_iff hBne]
    linear_combination hcoeff
  have hC_eq' : baileyTransformCoeff a q ρ₁ ρ₂ (j + d + 1 + e) (j + d + 1)
      = baileyTransformCoeff a q ρ₁ ρ₂ (j + d + 1 + e) (j + d)
        * ((1 - ρ₁ * q ^ (j + d)) * (1 - ρ₂ * q ^ (j + d))
            * (a * q / (ρ₁ * ρ₂)) * (1 - q ^ (e + 1)))
        / (1 - (a * q / (ρ₁ * ρ₂)) * q ^ e) := by
    simpa only [show j + 1 + d + e = j + d + 1 + e by omega] using hC_eq
  rw [show j + 1 + d = j + d + 1 from by omega, hC_eq']
  -- Recurrences to align P/Q indices
  have hP : qPochhammer q (d + 1) = qPochhammer q d * (1 - q ^ (d + 1)) := by
    rw [show d + 1 = d + 1 from rfl, qPochhammer_succ]
  have hQ : qPoch (a * q) q (2 * j + 1 + d)
      = qPoch (a * q) q (2 * j + d) * (1 - a * q * q ^ (2 * j + d)) := by
    rw [show 2 * j + 1 + d = (2 * j + d) + 1 from by omega, qPoch_succ]
  rw [hP, hQ]
  have hPm1' : qPochhammer q d ≠ 0 := by
    simpa only using hPm1
  have hQk1j' : qPoch (a * q) q (2 * j + d) ≠ 0 := by
    simpa only [show j + d + j = 2 * j + d by omega] using hQk1j
  have hAjk1' : (1 : R) - a * q * q ^ (2 * j + d) ≠ 0 := by
    simpa only [show j + (j + d) = 2 * j + d by omega] using hAjk1
  have hB : a * q / (ρ₁ * ρ₂) ≠ 0 :=
    div_ne_zero (mul_ne_zero ha hq) (mul_ne_zero hρ₁ hρ₂)
  -- Regard each q-Pochhammer and linear factor as one atom.  The bridge is
  -- then exactly the cancellation pattern isolated in `word_algebra`.
  simpa only [show j + d - j = d by omega,
      show j + d + j = 2 * j + d by omega,
      show j + (j + d) = 2 * j + d by omega,
      mul_assoc, mul_comm, mul_left_comm] using
    (word_algebra
      (C := baileyTransformCoeff a q ρ₁ ρ₂ (j + d + 1 + e) (j + d))
      (P := qPochhammer q d) (Q := qPoch (a * q) q (2 * j + d))
      (x := 1 - q ^ (d + 1)) (y := 1 - a * q * q ^ (2 * j + d))
      (r := 1 - ρ₁ * q ^ (j + d)) (s := 1 - ρ₂ * q ^ (j + d))
      (t := 1 - a * q * q ^ (2 * j)) (z := 1 - q ^ (e + 1))
      (h := 1 - (a * q / (ρ₁ * ρ₂)) * q ^ e)
      (B := a * q / (ρ₁ * ρ₂))
      (u := 1 - ρ₁ * q ^ j) (v := 1 - ρ₂ * q ^ j)
      (w := 1 - q ^ (d + 1 + e))
      hPm1' hQk1j' hkj hAjk1' hBne hB hR₁ hR₂ hQnj)

/-! ### Final assembly: unconditional general q-Pfaff–Saalschütz

Define concrete Gf, Wf and instantiate `baileyKernelSum_eq_target_certified`.
The Wf uses the boundary-safe form (using S_j(k-1)). Boundary values are
proved by `Wbs_bot_eq_head` (bottom) and direct factor evaluation (top).
The per-term identity hA combines `per_term_telescope` with `Word_eq_Wbs`.
The target shift hB is `tgt_shift_div`.
-/

/-- **Unconditional general q-Pfaff–Saalschütz** (structural assembly).
Combines per_term_telescope (A), tgt_shift_div (B), Word_eq_Wbs bridge,
and boundary values to instantiate baileyKernelSum_eq_target_certified.
All conditions are discharged by the 14 verified building blocks above.

This is the FINAL theorem: `baileyKernelSum = baileyKernelTarget` for all j ≤ n,
under generic nonvanishing hypotheses. -/
theorem baileyKernelSum_eq_target_general (a q ρ₁ ρ₂ : R) (n : Nat)
    (hρ₁ : ρ₁ ≠ 0) (hρ₂ : ρ₂ ≠ 0) (ha : a ≠ 0) (hq : q ≠ 0)
    (hE₁ : qPoch (a * q / ρ₁) q n ≠ 0) (hE₂ : qPoch (a * q / ρ₂) q n ≠ 0)
    (hR₁ : ∀ j, j < n → (1 : R) - ρ₁ * q ^ j ≠ 0)
    (hR₂ : ∀ j, j < n → (1 : R) - ρ₂ * q ^ j ≠ 0)
    (hQm : ∀ m, 1 ≤ m → m ≤ n → (1 : R) - q ^ m ≠ 0)
    (hAQ : ∀ m, m ≤ 2 * n → (1 : R) - a * q * q ^ m ≠ 0)
    (hPoch : ∀ m, m ≤ n → qPochhammer q m ≠ 0)
    (hAQP : ∀ m, m ≤ 2 * n → qPoch (a * q) q m ≠ 0)
    (hBq : ∀ m, m ≤ n → (1 : R) - (a * q / (ρ₁ * ρ₂)) * q ^ m ≠ 0)
    (hDj : ∀ j, j ≤ n → (ρ₁ * ρ₂) ^ j *
        (qPoch (a * q / ρ₁) q j * qPoch (a * q / ρ₂) q j
          * qPochhammer q (n - j) * qPoch (a * q) q (n + j)) ≠ 0) :
    ∀ j, j ≤ n →
      baileyKernelSum a q ρ₁ ρ₂ n j = baileyKernelTarget a q ρ₁ ρ₂ n j := by
  apply baileyKernelSum_eq_target_certified a q ρ₁ ρ₂ n
    (fun j => (ρ₁ - a * q * q ^ j) * (ρ₂ - a * q * q ^ j) * (1 - a * q * q ^ (n + j))
      / ((a * q) * (1 - ρ₁ * q ^ j) * (1 - ρ₂ * q ^ j) * (1 - q ^ (n - j))))
    (fun j k => baileyTransformCoeff a q ρ₁ ρ₂ n (k - 1)
      / (qPochhammer q (k - 1 - j) * qPoch (a * q) q (k - 1 + j))
      * ((1 - ρ₁ * q ^ (k - 1)) * (1 - ρ₂ * q ^ (k - 1))
          * (1 - a * q * q ^ (2 * j)) * (1 - q ^ (n + 1 - k)))
      / ((1 - ρ₁ * q ^ j) * (1 - ρ₂ * q ^ j) * (1 - q ^ (n - j))
          * (1 - a * q * q ^ (j + (k - 1)))))
  intro j hj IH
  refine ⟨?hA, ?hWtop, ?hWbot, ?hB⟩
  -- (1) hA: per-term telescoping + bridge
  case hA =>
    intro k hk
    have hjk : j + 1 ≤ k := by
      simp only [Finset.mem_filter] at hk; exact hk.2
    have hkn : k ≤ n := by
      simp only [Finset.mem_filter, Finset.mem_range] at hk; omega
    -- Goal now has beta-reduced Gf/Wf (inline lambdas)
    -- Apply per_term_telescope: S_j(k) = G·S_{j+1}(k) + (Wbs(k+1) - Word(k))
    have hpt := per_term_telescope a q ρ₁ ρ₂ n k j hjk hkn
      hρ₁ hρ₂ ha hq
      (hPoch (k - j - 1) (by omega))
      (hAQP (k + j) (by omega))
      (hR₁ j hj) (hR₂ j hj)
      (hQm (n - j) (by omega) (by omega))
      (hQm (k - j) (by omega) (by omega))
      (hAQ (k + j) (by omega))
      (hAQ (j + k) (by omega))
    -- Apply bridge: Word(k) = Wbs(k) = Wf j k
    have hbridge := Word_eq_Wbs a q ρ₁ ρ₂ n k j hjk hkn
      hρ₁ hρ₂ ha hq
      (hPoch (k - j - 1) (by omega))
      (hAQP (k + j) (by omega))
      (hAQP (k - 1 + j) (by omega))
      (hR₁ j hj) (hR₂ j hj)
      (hQm (n - j) (by omega) (by omega))
      (hQm (k - j) (by omega) (by omega))
      (hAQ (j + (k - 1)) (by omega))
      hE₁ hE₂
      (hPoch (n - k) (by omega))
      (hQm (n - k + 1) (by omega) (by omega))
      (hBq (n - k) (by omega))
    -- Rewrite Word(k) → Wbs(k) in hpt, then exact
    rw [hbridge] at hpt
    simpa only [Nat.add_sub_cancel, Nat.add_sub_cancel_left,
      Nat.add_sub_cancel_right,
      show n + 1 - (k + 1) = n - k by omega] using hpt
  -- (2) hWtop: Wf j (n+1) = 0 (factor 1-q^0 = 0)
  case hWtop =>
    simp [Nat.sub_self, sub_self, mul_zero, zero_mul, zero_div]
  -- (3) hWbot: Wf(j,j+1) = coeff/qPoch (factors cancel), from Wbs_bot_eq_head
  case hWbot =>
    simpa only [show j + 1 - 1 = j from by omega,
        Nat.sub_self, show n + 1 - (j + 1) = n - j from by omega,
        two_mul] using
      Wbs_bot_eq_head a q ρ₁ ρ₂ n j hj
        (hR₁ j hj) (hR₂ j hj) (hQm (n - j) (by omega) (by omega))
        (hAQ (2 * j) (by omega))
  -- (4) hB: KTgt(n,j) = Gf(j) · KTgt(n,j+1), from tgt_shift_div
  case hB =>
    exact tgt_shift_div a q ρ₁ ρ₂ n j hj hρ₁ hρ₂ ha hq
      (hR₁ j hj) (hR₂ j hj) (hQm (n - j) (by omega) (by omega))
      (hDj j (le_of_lt hj)) (hDj (j + 1) (by omega))

/-- **Unconditional finite Bailey lemma.** The Bailey transform sends Bailey
pairs to Bailey pairs at every level `n`, under generic nonvanishing hypotheses.
Combines `BaileyTransform_preserves_pair_general` (structural) with
`baileyKernelSum_eq_target_general` (the q-Pfaff–Saalschütz kernel identity). -/
theorem BaileyTransform_preserves_pair_unconditional
    (a q ρ₁ ρ₂ : R) {α β : Nat → R} (n : Nat)
    (hpair : IsBaileyPairUpTo a q α β n)
    (hρ₁ : ρ₁ ≠ 0) (hρ₂ : ρ₂ ≠ 0) (ha : a ≠ 0) (hq : q ≠ 0)
    (hE₁ : qPoch (a * q / ρ₁) q n ≠ 0) (hE₂ : qPoch (a * q / ρ₂) q n ≠ 0)
    (hR₁ : ∀ j, j < n → (1 : R) - ρ₁ * q ^ j ≠ 0)
    (hR₂ : ∀ j, j < n → (1 : R) - ρ₂ * q ^ j ≠ 0)
    (hQm : ∀ m, 1 ≤ m → m ≤ n → (1 : R) - q ^ m ≠ 0)
    (hAQ : ∀ m, m ≤ 2 * n → (1 : R) - a * q * q ^ m ≠ 0)
    (hPoch : ∀ m, m ≤ n → qPochhammer q m ≠ 0)
    (hAQP : ∀ m, m ≤ 2 * n → qPoch (a * q) q m ≠ 0)
    (hBq : ∀ m, m ≤ n → (1 : R) - (a * q / (ρ₁ * ρ₂)) * q ^ m ≠ 0)
    (hDj : ∀ j, j ≤ n → (ρ₁ * ρ₂) ^ j *
        (qPoch (a * q / ρ₁) q j * qPoch (a * q / ρ₂) q j
          * qPochhammer q (n - j) * qPoch (a * q) q (n + j)) ≠ 0) :
    BaileyTransformBeta a q ρ₁ ρ₂ β n =
      BaileyBeta a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) n := by
  apply BaileyTransform_preserves_pair_general a q ρ₁ ρ₂ n hpair
  intro j hj
  rw [Finset.mem_range] at hj
  exact baileyKernelSum_eq_target_general a q ρ₁ ρ₂ n
    hρ₁ hρ₂ ha hq hE₁ hE₂ hR₁ hR₂ hQm hAQ hPoch hAQP hBq hDj
    j (Nat.lt_succ_iff.mp hj)
