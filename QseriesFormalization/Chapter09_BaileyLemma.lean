import QseriesFormalization.Chapter09
import QseriesFormalization.Chapter03

/-!
# Chapter 9 — Bailey lemma operator form

This file isolates the operator statement of Bailey's lemma from the larger
Chapter 9 development.  The underlying finite Bailey-transform identity is
already proved in `Chapter09` modulo the q-Pfaff--Saalschutz kernel evaluation;
here we package it as Chan's matrix equation `LM = MD` and its two immediate
consequences.
-/

namespace QseriesFormalization
namespace PartII
namespace Ch09

section Field

variable {R : Type*} [Field R]

/-- Chan's matrix `L(x)`, Eq. (9.6):
`L_{n,k} = x^k q^{k^2} / (q;q)_{n-k}` for `k ≤ n`. -/
noncomputable def L (x q : R) (β : Nat → R) (n : Nat) : R :=
  ∑ k ∈ Finset.range (n + 1),
    x ^ k * q ^ (k * k) / qPochhammer q (n - k) * β k

/-- Chan's Bailey matrix `M(x)`, Eq. (9.7):
`M_{n,k} = 1 / ((q;q)_{n-k} (xq;q)_{n+k})` for `k ≤ n`. -/
noncomputable def M (x q : R) (α : Nat → R) (n : Nat) : R :=
  BaileyBeta x q α n

/-- Chan's diagonal matrix `D(x)`, Eq. (9.8):
`D_{n,n} = x^n q^{n^2}`. -/
noncomputable def D (x q : R) (α : Nat → R) (n : Nat) : R :=
  x ^ n * q ^ (n * n) * α n

/-- The finite full-Bailey-lemma β-side transform from FYI 9.1. -/
noncomputable def BaileyTransformL (a q ρ₁ ρ₂ : R) (β : Nat → R) (n : Nat) : R :=
  BaileyTransformBeta a q ρ₁ ρ₂ β n

/-- The finite full-Bailey-lemma α-side transform from FYI 9.1. -/
noncomputable def BaileyTransformD (a q ρ₁ ρ₂ : R) (α : Nat → R) (n : Nat) : R :=
  BaileyTransformAlpha a q ρ₁ ρ₂ α n

/-- Bailey pairs, stated in the operator language `b = M a`. -/
def IsBaileyPairByM (a q : R) (α β : Nat → R) : Prop :=
  ∀ n : Nat, β n = M a q α n

/-- Pointwise q-Pfaff--Saalschutz kernel hypothesis needed by the structural
finite Bailey lemma already proved in `Chapter09`. -/
def BaileyKernelIdentity (a q ρ₁ ρ₂ : R) : Prop :=
  ∀ n : Nat, ∀ j ∈ Finset.range (n + 1),
    baileyKernelSum a q ρ₁ ρ₂ n j = baileyKernelTarget a q ρ₁ ρ₂ n j

theorem isBaileyPairByM_iff_isBaileyPair (a q : R) (α β : Nat → R) :
    IsBaileyPairByM a q α β ↔ IsBaileyPair a q α β := by
  rfl

/-- The second iterate of Chan's `L(x)`. -/
noncomputable def L2 (x q : R) (β : Nat → R) (n : Nat) : R :=
  L x q (L x q β) n

/-- The second iterate of Chan's `D(x)`. -/
noncomputable def D2 (x q : R) (α : Nat → R) (n : Nat) : R :=
  D x q (D x q α) n

theorem L_one_eq_MBeta (q : R) (β : Nat → R) (n : Nat) :
    L 1 q β n = MBeta q β n := by
  unfold L MBeta
  apply Finset.sum_congr rfl
  intro k _hk
  simp only [one_pow]
  rw [div_mul_eq_mul_div]
  ring

theorem D_one_eq_MAlpha (q : R) (α : Nat → R) (n : Nat) :
    D 1 q α n = MAlpha q α n := by
  simp [D, MAlpha]

theorem D_one_eq_MAlpha_fun (q : R) (α : Nat → R) :
    D 1 q α = MAlpha q α := by
  funext n
  exact D_one_eq_MAlpha q α n

theorem D2_one_eq_MAlpha_MAlpha (q : R) (α : Nat → R) (n : Nat) :
    D2 1 q α n = MAlpha q (MAlpha q α) n := by
  simp [D2, D, MAlpha]

/-- Lemma 9.1, Eq. (9.10), in the shifted variables `j = m + k` and
`N = n - m`.  This is the coefficient identity behind `LM = MD`; the
nonzero hypotheses are needed because the PDF uses reciprocal Pochhammer
factors while Lean's field division is total. -/
theorem lemma91_matrix_entry_shifted (x q : R) (m N : Nat)
    (hxq : ∀ k, k < N + 2 * m → (1 : R) - x * q ^ (k + 1) ≠ 0)
    (hQ : ∀ k, k ≤ N → qPochhammer q k ≠ 0) :
    (∑ k ∈ Finset.range (N + 1),
      x ^ (m + k) * q ^ ((m + k) * (m + k)) /
        (qPochhammer q (N - k) * qPochhammer q k * qPoch (x * q) q (k + 2 * m))) =
      x ^ m * q ^ (m * m) /
        (qPochhammer q N * qPoch (x * q) q (N + 2 * m)) := by
  have hbase := lemma91BaseM_eq x q (2 * m) N hxq
  unfold lemma91BaseM lemma91TargetM at hbase
  have hN : qPochhammer q N ≠ 0 := hQ N le_rfl
  calc
    (∑ k ∈ Finset.range (N + 1),
      x ^ (m + k) * q ^ ((m + k) * (m + k)) /
        (qPochhammer q (N - k) * qPochhammer q k * qPoch (x * q) q (k + 2 * m)))
        = x ^ m * q ^ (m * m) / qPochhammer q N *
            (∑ k ∈ Finset.range (N + 1),
              x ^ k * q ^ (k * (k + 2 * m)) * gaussianBinom q N k /
                qPoch (x * q) q (k + 2 * m)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          have hkN : k ≤ N := by
            simpa [Finset.mem_range, Nat.lt_succ_iff] using hk
          have hNk : N - k ≤ N := Nat.sub_le N k
          have hQk : qPochhammer q k ≠ 0 := hQ k hkN
          have hQNk : qPochhammer q (N - k) ≠ 0 := hQ (N - k) hNk
          have hgb :=
            QseriesFormalization.PartI.Ch03.gaussianBinom_mul_qPochhammer_eq
              (R := R) q N k hkN
          have hxpow : x ^ (m + k) = x ^ m * x ^ k := by
            rw [pow_add]
          have hexp : (m + k) * (m + k) = m * m + k * (k + 2 * m) := by
            ring
          rw [hxpow, hexp, pow_add]
          by_cases hP : qPoch (x * q) q (k + 2 * m) = 0
          · simp [hP]
          · field_simp [hN, hQk, hQNk, hP]
            have hgb' :
                qPochhammer q N =
                  qPochhammer q (N - k) * qPochhammer q k * gaussianBinom q N k := by
              rw [← hgb]
              ring
            rw [hgb']
            ring
    _ = x ^ m * q ^ (m * m) / qPochhammer q N *
          (1 / qPoch (x * q) q (N + 2 * m)) := by
          rw [hbase]
    _ = x ^ m * q ^ (m * m) /
          (qPochhammer q N * qPoch (x * q) q (N + 2 * m)) := by
          ring

open Finset in
/-- Expansion and triangular Fubini step for the operator product `L (M α)`. -/
private theorem L_comp_M_double_sum (x q : R) (α : Nat → R) (n : Nat) :
    L x q (M x q α) n =
      ∑ j ∈ range (n + 1),
        α j * ∑ k ∈ (range (n + 1)).filter (fun k => j ≤ k),
          x ^ k * q ^ (k * k) /
            (qPochhammer q (n - k) * qPochhammer q (k - j) *
              qPoch (x * q) q (k + j)) := by
  unfold L M
  rw [show (∑ k ∈ range (n + 1),
              x ^ k * q ^ (k * k) / qPochhammer q (n - k) * BaileyBeta x q α k) =
            ∑ k ∈ range (n + 1),
              x ^ k * q ^ (k * k) / qPochhammer q (n - k) *
                ∑ j ∈ range (k + 1), BaileyTerm x q α k j from by
        refine Finset.sum_congr rfl fun k _ => ?_
        congr 1
        rw [BaileyBeta_eq_sum]]
  set F : Nat → Nat → R := fun k j =>
    x ^ k * q ^ (k * k) / qPochhammer q (n - k) *
      (α j / (qPochhammer q (k - j) * qPoch (x * q) q (k + j))) with hF
  have step1 :
      ∀ k ∈ range (n + 1),
        x ^ k * q ^ (k * k) / qPochhammer q (n - k) *
            ∑ j ∈ range (k + 1), BaileyTerm x q α k j =
          ∑ j ∈ range (k + 1), F k j := by
    intro k _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [BaileyTerm, hF]
  rw [Finset.sum_congr rfl step1]
  have step2 :
      ∀ k ∈ range (n + 1),
        ∑ j ∈ range (k + 1), F k j =
          ∑ j ∈ (range (n + 1)).filter (fun j => j ≤ k), F k j := by
    intro k hk
    have hkn : k ≤ n := by simpa [Finset.mem_range, Nat.lt_succ_iff] using hk
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext j
    simp [Finset.mem_range, Finset.mem_filter]
    omega
  rw [Finset.sum_congr rfl step2]
  rw [show (∑ k ∈ range (n + 1),
              ∑ j ∈ (range (n + 1)).filter (fun j => j ≤ k), F k j) =
          ∑ j ∈ range (n + 1),
              ∑ k ∈ (range (n + 1)).filter (fun k => j ≤ k), F k j from by
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [hF]
  ring

open Finset in
/-- The inner triangular sum after fixing the lower index `j`. -/
private theorem lemma91_operator_inner_sum (x q : R) (n j : Nat)
    (hj : j ∈ range (n + 1))
    (hxq : ∀ k, k < 2 * n → (1 : R) - x * q ^ (k + 1) ≠ 0)
    (hQ : ∀ k, k ≤ n → qPochhammer q k ≠ 0) :
    (∑ k ∈ (range (n + 1)).filter (fun k => j ≤ k),
      x ^ k * q ^ (k * k) /
        (qPochhammer q (n - k) * qPochhammer q (k - j) *
          qPoch (x * q) q (k + j))) =
      x ^ j * q ^ (j * j) /
        (qPochhammer q (n - j) * qPoch (x * q) q (n + j)) := by
  have hjn : j ≤ n := by simpa [Finset.mem_range, Nat.lt_succ_iff] using hj
  let e : Nat ↪ Nat := ⟨fun t => j + t, by intro a b h; exact Nat.add_left_cancel h⟩
  have hfilter_eq :
      (range (n + 1)).filter (fun k => j ≤ k) =
        (range (n - j + 1)).map e := by
    ext k
    simp [e, Finset.mem_filter, Finset.mem_range]
    constructor
    · intro h
      refine ⟨k - j, ?_, ?_⟩
      · omega
      · omega
    · intro h
      rcases h with ⟨t, ht, rfl⟩
      omega
  rw [hfilter_eq, Finset.sum_map]
  have hshift := lemma91_matrix_entry_shifted x q j (n - j)
    (fun k hk => hxq k (by omega))
    (fun k hk => hQ k (by omega))
  calc
    (∑ t ∈ range (n - j + 1),
      x ^ (j + t) * q ^ ((j + t) * (j + t)) /
        (qPochhammer q (n - (j + t)) * qPochhammer q (j + t - j) *
          qPoch (x * q) q (j + t + j)))
        = (∑ t ∈ range (n - j + 1),
            x ^ (j + t) * q ^ ((j + t) * (j + t)) /
              (qPochhammer q (n - j - t) * qPochhammer q t *
                qPoch (x * q) q (t + 2 * j))) := by
          refine Finset.sum_congr rfl fun t ht => ?_
          have htle : t ≤ n - j := by simpa [Finset.mem_range, Nat.lt_succ_iff] using ht
          have h1 : n - (j + t) = n - j - t := by omega
          have h2 : j + t - j = t := by omega
          have h3 : j + t + j = t + 2 * j := by omega
          rw [h1, h2, h3]
    _ = x ^ j * q ^ (j * j) /
        (qPochhammer q (n - j) * qPoch (x * q) q ((n - j) + 2 * j)) := hshift
    _ = x ^ j * q ^ (j * j) /
        (qPochhammer q (n - j) * qPoch (x * q) q (n + j)) := by
          have hidx : (n - j) + 2 * j = n + j := by omega
          rw [hidx]

set_option maxHeartbeats 1200000 in
/-- Component form of Lemma 9.1: `L(x) (M(x) α) = M(x) (D(x) α)`. -/
theorem lemma91_operator_at (x q : R) (α : Nat → R) (n : Nat)
    (hxq : ∀ k, k < 2 * n → (1 : R) - x * q ^ (k + 1) ≠ 0)
    (hQ : ∀ k, k ≤ n → qPochhammer q k ≠ 0) :
    L x q (M x q α) n = M x q (D x q α) n := by
  calc
    L x q (M x q α) n =
        ∑ j ∈ Finset.range (n + 1),
          α j * ∑ k ∈ (Finset.range (n + 1)).filter (fun k => j ≤ k),
            x ^ k * q ^ (k * k) /
              (qPochhammer q (n - k) * qPochhammer q (k - j) *
                qPoch (x * q) q (k + j)) :=
      L_comp_M_double_sum x q α n
    _ = ∑ j ∈ Finset.range (n + 1),
          α j * (x ^ j * q ^ (j * j) /
            (qPochhammer q (n - j) * qPoch (x * q) q (n + j))) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [lemma91_operator_inner_sum x q n j hj hxq hQ]
    _ = M x q (D x q α) n := by
      unfold M D
      rw [BaileyBeta_eq_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [BaileyTerm]
      ring

/-- Lemma 9.1 in operator form: `L(x) ∘ M(x) = M(x) ∘ D(x)`.

The hypotheses are only the nonzero denominator conditions needed by
`lemma91_matrix_entry_shifted`; no Bailey kernel identity is used. -/
theorem lemma91_operator (x q : R) (α : Nat → R)
    (hxq : ∀ k, (1 : R) - x * q ^ (k + 1) ≠ 0)
    (hQ : ∀ k, qPochhammer q k ≠ 0) :
    ∀ n : Nat, L x q (M x q α) n = M x q (D x q α) n := by
  intro n
  exact lemma91_operator_at x q α n (fun k _ => hxq k) (fun k _ => hQ k)

/-- Chan Theorem 9.1: if `β = M(x) α`, then `L(x) β = M(x) (D(x) α)`. -/
theorem theorem91 (x q : R) {α β : Nat → R}
    (hxq : ∀ k, (1 : R) - x * q ^ (k + 1) ≠ 0)
    (hQ : ∀ k, qPochhammer q k ≠ 0)
    (hpair : IsBaileyPairByM x q α β) :
    ∀ n : Nat, L x q β n = M x q (D x q α) n := by
  intro n
  calc
    L x q β n = L x q (M x q α) n := by
      unfold L
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hpair k]
    _ = M x q (D x q α) n := lemma91_operator x q α hxq hQ n

/-- Chan Theorem 9.2: the two-step operator identity `L(x)^2 β = M(x) D(x)^2 α`. -/
theorem theorem92 (x q : R) {α β : Nat → R}
    (hxq : ∀ k, (1 : R) - x * q ^ (k + 1) ≠ 0)
    (hQ : ∀ k, qPochhammer q k ≠ 0)
    (hpair : IsBaileyPairByM x q α β) :
    ∀ n : Nat, L2 x q β n = M x q (D2 x q α) n := by
  have hpair₁ : IsBaileyPairByM x q (D x q α) (L x q β) := by
    intro n
    exact theorem91 x q hxq hQ hpair n
  intro n
  simpa [L2, D2] using
    theorem91 x q (α := D x q α) (β := L x q β) hxq hQ hpair₁ n

/-- Chan Theorem 9.1 at `x = 1`, component `n = 0`. -/
theorem theorem91_x_one_zero (q : R) {α β : Nat → R}
    (hpair : IsBaileyPairByM 1 q α β) :
    L 1 q β 0 = M 1 q (D 1 q α) 0 := by
  rw [L_one_eq_MBeta]
  change MBeta q β 0 = BaileyBeta 1 q (D 1 q α) 0
  rw [D_one_eq_MAlpha_fun]
  exact M_preserves_BaileyPair_zero q α β (hpair 0)

/-- Chan Theorem 9.1 at `x = 1`, component `n = 1`. -/
theorem theorem91_x_one_one (q : R) {α β : Nat → R}
    (hpair : IsBaileyPairByM 1 q α β)
    (hq1 : (1 : R) - q ≠ 0) (hq2 : (1 : R) - q ^ 2 ≠ 0) :
    L 1 q β 1 = M 1 q (D 1 q α) 1 := by
  rw [L_one_eq_MBeta]
  change MBeta q β 1 = BaileyBeta 1 q (D 1 q α) 1
  rw [D_one_eq_MAlpha_fun]
  exact M_preserves_BaileyPair_one q α β (hpair 0) (hpair 1) hq1 hq2

/-- Chan Theorem 9.1 at `x = 1`, component `n = 2`. -/
theorem theorem91_x_one_two (q : R) {α β : Nat → R}
    (hpair : IsBaileyPairByM 1 q α β)
    (hq1 : (1 : R) - q ≠ 0) (hq2 : (1 : R) - q ^ 2 ≠ 0)
    (hq3 : (1 : R) - q ^ 3 ≠ 0) (hq4 : (1 : R) - q ^ 4 ≠ 0) :
    L 1 q β 2 = M 1 q (D 1 q α) 2 := by
  rw [L_one_eq_MBeta]
  change MBeta q β 2 = BaileyBeta 1 q (D 1 q α) 2
  rw [D_one_eq_MAlpha_fun]
  exact M_preserves_BaileyPair_two q α β
    (hpair 0) (hpair 1) (hpair 2) hq1 hq2 hq3 hq4

/-- Chan Theorem 9.1 at `x = 1`, bundled through `n = 2`. -/
theorem theorem91_x_one_upTo_two (q : R) {α β : Nat → R}
    (hpair : IsBaileyPairByM 1 q α β)
    (hq1 : (1 : R) - q ≠ 0) (hq2 : (1 : R) - q ^ 2 ≠ 0)
    (hq3 : (1 : R) - q ^ 3 ≠ 0) (hq4 : (1 : R) - q ^ 4 ≠ 0) :
    IsBaileyPairUpTo 1 q (D 1 q α) (L 1 q β) 2 := by
  apply IsBaileyPairUpTo.of_two
  · exact theorem91_x_one_zero q hpair
  · exact theorem91_x_one_one q hpair hq1 hq2
  · exact theorem91_x_one_two q hpair hq1 hq2 hq3 hq4

/-- Lemma 9.1 (`LM = MD`) at `x = 1`, component `n = 0`. -/
theorem lemma91_x_one_zero (q : R) (α : Nat → R) :
    L 1 q (M 1 q α) 0 = M 1 q (D 1 q α) 0 := by
  exact theorem91_x_one_zero q (α := α) (β := M 1 q α) (by intro n; rfl)

/-- Lemma 9.1 (`LM = MD`) at `x = 1`, component `n = 1`. -/
theorem lemma91_x_one_one (q : R) (α : Nat → R)
    (hq1 : (1 : R) - q ≠ 0) (hq2 : (1 : R) - q ^ 2 ≠ 0) :
    L 1 q (M 1 q α) 1 = M 1 q (D 1 q α) 1 := by
  exact theorem91_x_one_one q (α := α) (β := M 1 q α)
    (by intro n; rfl) hq1 hq2

/-- Lemma 9.1 (`LM = MD`) at `x = 1`, component `n = 2`. -/
theorem lemma91_x_one_two (q : R) (α : Nat → R)
    (hq1 : (1 : R) - q ≠ 0) (hq2 : (1 : R) - q ^ 2 ≠ 0)
    (hq3 : (1 : R) - q ^ 3 ≠ 0) (hq4 : (1 : R) - q ^ 4 ≠ 0) :
    L 1 q (M 1 q α) 2 = M 1 q (D 1 q α) 2 := by
  exact theorem91_x_one_two q (α := α) (β := M 1 q α)
    (by intro n; rfl) hq1 hq2 hq3 hq4

/-- Lemma 9.1 (`LM = MD`) at `x = 1`, bundled through `n = 2`. -/
theorem lemma91_x_one_upTo_two (q : R) (α : Nat → R)
    (hq1 : (1 : R) - q ≠ 0) (hq2 : (1 : R) - q ^ 2 ≠ 0)
    (hq3 : (1 : R) - q ^ 3 ≠ 0) (hq4 : (1 : R) - q ^ 4 ≠ 0) :
    IsBaileyPairUpTo 1 q (D 1 q α) (L 1 q (M 1 q α)) 2 := by
  exact theorem91_x_one_upTo_two q (α := α) (β := M 1 q α)
    (by intro n; rfl) hq1 hq2 hq3 hq4

/-- Chan Theorem 9.2 at `x = 1`, component `n = 0`. -/
theorem theorem92_x_one_zero (q : R) {α β : Nat → R}
    (hpair : IsBaileyPairByM 1 q α β) :
    L2 1 q β 0 = M 1 q (D2 1 q α) 0 := by
  have hpair₁0 : L 1 q β 0 = M 1 q (D 1 q α) 0 :=
    theorem91_x_one_zero q hpair
  change L 1 q (L 1 q β) 0 = M 1 q (D 1 q (D 1 q α)) 0
  rw [L_one_eq_MBeta]
  change MBeta q (L 1 q β) 0 = BaileyBeta 1 q (D 1 q (D 1 q α)) 0
  rw [D_one_eq_MAlpha_fun]
  exact M_preserves_BaileyPair_zero q (D 1 q α) (L 1 q β) hpair₁0

/-- Chan Theorem 9.2 at `x = 1`, component `n = 1`. -/
theorem theorem92_x_one_one (q : R) {α β : Nat → R}
    (hpair : IsBaileyPairByM 1 q α β)
    (hq1 : (1 : R) - q ≠ 0) (hq2 : (1 : R) - q ^ 2 ≠ 0) :
    L2 1 q β 1 = M 1 q (D2 1 q α) 1 := by
  have hpair₁0 : L 1 q β 0 = M 1 q (D 1 q α) 0 :=
    theorem91_x_one_zero q hpair
  have hpair₁1 : L 1 q β 1 = M 1 q (D 1 q α) 1 :=
    theorem91_x_one_one q hpair hq1 hq2
  change L 1 q (L 1 q β) 1 = M 1 q (D 1 q (D 1 q α)) 1
  rw [L_one_eq_MBeta]
  change MBeta q (L 1 q β) 1 = BaileyBeta 1 q (D 1 q (D 1 q α)) 1
  rw [D_one_eq_MAlpha_fun]
  exact M_preserves_BaileyPair_one q (D 1 q α) (L 1 q β)
    hpair₁0 hpair₁1 hq1 hq2

/-- Chan Theorem 9.2 at `x = 1`, component `n = 2`. -/
theorem theorem92_x_one_two (q : R) {α β : Nat → R}
    (hpair : IsBaileyPairByM 1 q α β)
    (hq1 : (1 : R) - q ≠ 0) (hq2 : (1 : R) - q ^ 2 ≠ 0)
    (hq3 : (1 : R) - q ^ 3 ≠ 0) (hq4 : (1 : R) - q ^ 4 ≠ 0) :
    L2 1 q β 2 = M 1 q (D2 1 q α) 2 := by
  have hpair₁0 : L 1 q β 0 = M 1 q (D 1 q α) 0 :=
    theorem91_x_one_zero q hpair
  have hpair₁1 : L 1 q β 1 = M 1 q (D 1 q α) 1 :=
    theorem91_x_one_one q hpair hq1 hq2
  have hpair₁2 : L 1 q β 2 = M 1 q (D 1 q α) 2 :=
    theorem91_x_one_two q hpair hq1 hq2 hq3 hq4
  change L 1 q (L 1 q β) 2 = M 1 q (D 1 q (D 1 q α)) 2
  rw [L_one_eq_MBeta]
  change MBeta q (L 1 q β) 2 = BaileyBeta 1 q (D 1 q (D 1 q α)) 2
  rw [D_one_eq_MAlpha_fun]
  exact M_preserves_BaileyPair_two q (D 1 q α) (L 1 q β)
    hpair₁0 hpair₁1 hpair₁2 hq1 hq2 hq3 hq4

/-- Chan Theorem 9.2 at `x = 1`, bundled through `n = 2`. -/
theorem theorem92_x_one_upTo_two (q : R) {α β : Nat → R}
    (hpair : IsBaileyPairByM 1 q α β)
    (hq1 : (1 : R) - q ≠ 0) (hq2 : (1 : R) - q ^ 2 ≠ 0)
    (hq3 : (1 : R) - q ^ 3 ≠ 0) (hq4 : (1 : R) - q ^ 4 ≠ 0) :
    IsBaileyPairUpTo 1 q (D2 1 q α) (L2 1 q β) 2 := by
  apply IsBaileyPairUpTo.of_two
  · exact theorem92_x_one_zero q hpair
  · exact theorem92_x_one_one q hpair hq1 hq2
  · exact theorem92_x_one_two q hpair hq1 hq2 hq3 hq4

/-- Lemma 9.1 in operator form: `L ∘ M = M ∘ D`.

The only non-structural input is the q-Pfaff--Saalschutz kernel identity,
kept explicit as a hypothesis. -/
theorem fullBaileyTransform_L_comp_M_eq_M_comp_D (a q ρ₁ ρ₂ : R)
    (hkernel : BaileyKernelIdentity a q ρ₁ ρ₂) (α : Nat → R) :
    ∀ n : Nat,
      BaileyTransformL a q ρ₁ ρ₂ (M a q α) n =
        M a q (BaileyTransformD a q ρ₁ ρ₂ α) n := by
  intro n
  have hpair : IsBaileyPairUpTo a q α (M a q α) n := by
    intro k _hk
    rfl
  simpa [BaileyTransformL, M, BaileyTransformD] using
    BaileyTransform_preserves_pair_general a q ρ₁ ρ₂ n hpair (hkernel n)

/-- Full finite Bailey transform: if `(α, β)` is a Bailey pair, then the
FYI 9.1 transformed pair is again a Bailey pair. -/
theorem fullBaileyTransform_theorem91 (a q ρ₁ ρ₂ : R) {α β : Nat → R}
    (hkernel : BaileyKernelIdentity a q ρ₁ ρ₂)
    (hpair : IsBaileyPairByM a q α β) :
    ∀ n : Nat,
      BaileyTransformL a q ρ₁ ρ₂ β n =
        M a q (BaileyTransformD a q ρ₁ ρ₂ α) n := by
  intro n
  have hpairUp : IsBaileyPairUpTo a q α β n := by
    intro k _hk
    exact hpair k
  simpa [BaileyTransformL, M, BaileyTransformD] using
    BaileyTransform_preserves_pair_general a q ρ₁ ρ₂ n hpairUp (hkernel n)

/-- Full finite Bailey transform, packaged as preservation of the pair relation. -/
theorem fullBaileyTransform_preserves_pair (a q ρ₁ ρ₂ : R) {α β : Nat → R}
    (hkernel : BaileyKernelIdentity a q ρ₁ ρ₂)
    (hpair : IsBaileyPairByM a q α β) :
    IsBaileyPairByM a q
      (BaileyTransformD a q ρ₁ ρ₂ α) (BaileyTransformL a q ρ₁ ρ₂ β) := by
  intro n
  exact fullBaileyTransform_theorem91 a q ρ₁ ρ₂ hkernel hpair n

/-- The second iterate of the full β-side transform. -/
noncomputable def BaileyTransformL2 (a q ρ₁ ρ₂ : R) (β : Nat → R) (n : Nat) : R :=
  BaileyTransformL a q ρ₁ ρ₂ (BaileyTransformL a q ρ₁ ρ₂ β) n

/-- The second iterate of the full α-side transform. -/
noncomputable def BaileyTransformD2 (a q ρ₁ ρ₂ : R) (α : Nat → R) (n : Nat) : R :=
  BaileyTransformD a q ρ₁ ρ₂ (BaileyTransformD a q ρ₁ ρ₂ α) n

/-- Iterating the full finite Bailey transform gives the two-step identity. -/
theorem fullBaileyTransform_theorem92 (a q ρ₁ ρ₂ : R) {α β : Nat → R}
    (hkernel : BaileyKernelIdentity a q ρ₁ ρ₂)
    (hpair : IsBaileyPairByM a q α β) :
    ∀ n : Nat,
      BaileyTransformL2 a q ρ₁ ρ₂ β n =
        M a q (BaileyTransformD2 a q ρ₁ ρ₂ α) n := by
  intro n
  have hpair₁ :
      IsBaileyPairByM a q
        (BaileyTransformD a q ρ₁ ρ₂ α) (BaileyTransformL a q ρ₁ ρ₂ β) :=
    fullBaileyTransform_preserves_pair a q ρ₁ ρ₂ hkernel hpair
  simpa [BaileyTransformL2, BaileyTransformD2] using
    fullBaileyTransform_theorem91 a q ρ₁ ρ₂ hkernel hpair₁ n

/-- The full finite Bailey transform, packaged as two-step preservation. -/
theorem fullBaileyTransform_preserves_pair_two_steps (a q ρ₁ ρ₂ : R) {α β : Nat → R}
    (hkernel : BaileyKernelIdentity a q ρ₁ ρ₂)
    (hpair : IsBaileyPairByM a q α β) :
    IsBaileyPairByM a q
      (BaileyTransformD2 a q ρ₁ ρ₂ α) (BaileyTransformL2 a q ρ₁ ρ₂ β) := by
  intro n
  exact fullBaileyTransform_theorem92 a q ρ₁ ρ₂ hkernel hpair n

end Field

end Ch09
end PartII
end QseriesFormalization
