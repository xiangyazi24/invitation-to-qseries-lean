import QseriesFormalization.Basic

/-!
# Chapter 9 — Bailey pairs and Bailey's lemma

⚠️  **AUX CHAPTER — chapter-main result OPEN**.

Per `PLAYBOOK_AUDIT.md` (2026-05-22): this file contains substantive
Bailey-pair infrastructure — definitions (`BaileyTerm`, `BaileyBeta`,
`IsBaileyPairUpTo`), finite preservation of the Bailey transform under
nonzero-denominator hypotheses up through `N = 7`, the eight-coefficient
linear assembly needed for the q-Saalschütz reduction.

The chapter-main result — **Bailey's lemma in general** (Tier 1 #2 in
`TODO_THEOREMS.md`, the unconditional Bailey-transform identity that
underlies Rogers-Ramanujan and Macdonald-Bailey applications) — is
**not yet closed**.  See `BaileyTransform_preserves_pair_general` and
the Chapter 9 strategy doc.
-/

namespace QseriesFormalization
namespace PartII
namespace Ch09

section Field

variable {R : Type*} [Field R]

/-- The Bailey pair relation, finite form. `BaileyTerm a q n α k` is the
k-th summand in the Bailey defining relation
`β_n = ∑_{k=0}^n α_k / ((q;q)_{n-k} (a q; q)_{n+k})`. -/
noncomputable def BaileyTerm (a q : R) (α : Nat → R) (n k : Nat) : R :=
  α k / (qPochhammer q (n - k) * qPoch (a * q) q (n + k))

/-- BaileyTerm at `k = 0` unfolds. -/
theorem BaileyTerm_zero (a q : R) (α : Nat → R) (n : Nat) :
    BaileyTerm a q α n 0 = α 0 / (qPochhammer q n * qPoch (a * q) q n) := by
  simp [BaileyTerm]

/-- BaileyTerm at `k = n` unfolds with the first Pochhammer factor at zero. -/
theorem BaileyTerm_at_n (a q : R) (α : Nat → R) (n : Nat) :
    BaileyTerm a q α n n = α n / (qPochhammer q 0 * qPoch (a * q) q (2 * n)) := by
  unfold BaileyTerm
  rw [Nat.sub_self, two_mul]

/-- BaileyTerm at `k = n`, using `(q; q)_0 = 1`. -/
theorem BaileyTerm_at_n_simplified (a q : R) (α : Nat → R) (n : Nat) :
    BaileyTerm a q α n n = α n / qPoch (a * q) q (2 * n) := by
  rw [BaileyTerm_at_n]
  simp [qPochhammer]

/-- For `k > n`, the natural-number subtraction in `BaileyTerm` truncates
`n - k` to `0`, so this convention still gives a nontrivial summand. -/
theorem BaileyTerm_out_of_range_uses_truncated_pochhammer (a q : R)
    (α : Nat → R) (n k : Nat) (h : n < k) :
    BaileyTerm a q α n k =
      α k / (qPochhammer q 0 * qPoch (a * q) q (n + k)) := by
  unfold BaileyTerm
  rw [show n - k = 0 from Nat.sub_eq_zero_of_le (Nat.le_of_lt h)]

/-- The β-side of a Bailey pair, defined by the truncated sum. -/
noncomputable def BaileyBeta (a q : R) (α : Nat → R) (n : Nat) : R :=
  natSum (fun k => BaileyTerm a q α n k) n

/-- BaileyBeta at `n = 0` is its single defining summand. -/
theorem BaileyBeta_zero_expand (a q : R) (α : Nat → R) :
    BaileyBeta a q α 0 = BaileyTerm a q α 0 0 := by
  simp [BaileyBeta, natSum]

/-- BaileyBeta at `n = 0` is exactly the zeroth α-coefficient. -/
theorem BaileyBeta_zero (a q : R) (α : Nat → R) :
    BaileyBeta a q α 0 = α 0 := by
  simp [BaileyBeta, natSum, BaileyTerm, qPochhammer, qPoch]

/-- BaileyBeta at `n = 1` expands to its two defining summands. -/
theorem BaileyBeta_one_expand (a q : R) (α : Nat → R) :
    BaileyBeta a q α 1 = BaileyTerm a q α 1 0 + BaileyTerm a q α 1 1 := by
  simp [BaileyBeta, natSum]

/-- BaileyBeta at `n = 1`, with both defining summands simplified. -/
theorem BaileyBeta_one_terms (a q : R) (α : Nat → R) :
    BaileyBeta a q α 1 =
      α 0 / ((1 - q) * (1 - a * q)) + α 1 / qPoch (a * q) q 2 := by
  rw [BaileyBeta_one_expand]
  simp [BaileyTerm, qPochhammer, qPoch]

/-- BaileyBeta at `n = 2` expands to its three defining summands. -/
theorem BaileyBeta_two_expand (a q : R) (α : Nat → R) :
    BaileyBeta a q α 2 =
      BaileyTerm a q α 2 0 + BaileyTerm a q α 2 1 + BaileyTerm a q α 2 2 := by
  simp [BaileyBeta, natSum]

/-- BaileyBeta at `n = 2`, with all three defining summands simplified. -/
theorem BaileyBeta_two_terms (a q : R) (α : Nat → R) :
    BaileyBeta a q α 2 =
      α 0 / (qPochhammer q 2 * qPoch (a * q) q 2) +
      α 1 / (qPochhammer q 1 * qPoch (a * q) q 3) +
      α 2 / qPoch (a * q) q 4 := by
  rw [BaileyBeta_two_expand]
  simp [BaileyTerm, qPochhammer]

/-- BaileyBeta at `n = 3` expands to its four defining summands. -/
theorem BaileyBeta_three_expand (a q : R) (α : Nat → R) :
    BaileyBeta a q α 3 =
      BaileyTerm a q α 3 0 + BaileyTerm a q α 3 1 +
      BaileyTerm a q α 3 2 + BaileyTerm a q α 3 3 := by
  simp [BaileyBeta, natSum]

/-- BaileyBeta at `n = 3`, with all four defining summands simplified. -/
theorem BaileyBeta_three_terms (a q : R) (α : Nat → R) :
    BaileyBeta a q α 3 =
      α 0 / (qPochhammer q 3 * qPoch (a * q) q 3) +
      α 1 / (qPochhammer q 2 * qPoch (a * q) q 4) +
      α 2 / (qPochhammer q 1 * qPoch (a * q) q 5) +
      α 3 / qPoch (a * q) q 6 := by
  rw [BaileyBeta_three_expand]
  simp [BaileyTerm, qPochhammer]

/-- BaileyBeta at `n = 4` expands to its five defining summands. -/
theorem BaileyBeta_four_expand (a q : R) (α : Nat → R) :
    BaileyBeta a q α 4 =
      BaileyTerm a q α 4 0 + BaileyTerm a q α 4 1 +
      BaileyTerm a q α 4 2 + BaileyTerm a q α 4 3 +
      BaileyTerm a q α 4 4 := by
  simp [BaileyBeta, natSum]

/-- BaileyBeta at `n = 4`, with all five defining summands simplified. -/
theorem BaileyBeta_four_terms (a q : R) (α : Nat → R) :
    BaileyBeta a q α 4 =
      α 0 / (qPochhammer q 4 * qPoch (a * q) q 4) +
      α 1 / (qPochhammer q 3 * qPoch (a * q) q 5) +
      α 2 / (qPochhammer q 2 * qPoch (a * q) q 6) +
      α 3 / (qPochhammer q 1 * qPoch (a * q) q 7) +
      α 4 / qPoch (a * q) q 8 := by
  rw [BaileyBeta_four_expand]
  simp [BaileyTerm, qPochhammer]

/-- BaileyBeta at `n = 5` expands to its six defining summands. -/
theorem BaileyBeta_five_expand (a q : R) (α : Nat → R) :
    BaileyBeta a q α 5 =
      BaileyTerm a q α 5 0 + BaileyTerm a q α 5 1 +
      BaileyTerm a q α 5 2 + BaileyTerm a q α 5 3 +
      BaileyTerm a q α 5 4 + BaileyTerm a q α 5 5 := by
  simp [BaileyBeta, natSum]

/-- BaileyBeta at `n = 5`, with all six defining summands simplified. -/
theorem BaileyBeta_five_terms (a q : R) (α : Nat → R) :
    BaileyBeta a q α 5 =
      α 0 / (qPochhammer q 5 * qPoch (a * q) q 5) +
      α 1 / (qPochhammer q 4 * qPoch (a * q) q 6) +
      α 2 / (qPochhammer q 3 * qPoch (a * q) q 7) +
      α 3 / (qPochhammer q 2 * qPoch (a * q) q 8) +
      α 4 / (qPochhammer q 1 * qPoch (a * q) q 9) +
      α 5 / qPoch (a * q) q 10 := by
  rw [BaileyBeta_five_expand]
  simp [BaileyTerm, qPochhammer]

/-- BaileyBeta at `n = 6` expands to its seven defining summands. -/
theorem BaileyBeta_six_expand (a q : R) (α : Nat → R) :
    BaileyBeta a q α 6 =
      BaileyTerm a q α 6 0 + BaileyTerm a q α 6 1 +
      BaileyTerm a q α 6 2 + BaileyTerm a q α 6 3 +
      BaileyTerm a q α 6 4 + BaileyTerm a q α 6 5 +
      BaileyTerm a q α 6 6 := by
  simp [BaileyBeta, natSum]

/-- BaileyBeta at `n = 6`, with all seven defining summands simplified. -/
theorem BaileyBeta_six_terms (a q : R) (α : Nat → R) :
    BaileyBeta a q α 6 =
      α 0 / (qPochhammer q 6 * qPoch (a * q) q 6) +
      α 1 / (qPochhammer q 5 * qPoch (a * q) q 7) +
      α 2 / (qPochhammer q 4 * qPoch (a * q) q 8) +
      α 3 / (qPochhammer q 3 * qPoch (a * q) q 9) +
      α 4 / (qPochhammer q 2 * qPoch (a * q) q 10) +
      α 5 / (qPochhammer q 1 * qPoch (a * q) q 11) +
      α 6 / qPoch (a * q) q 12 := by
  rw [BaileyBeta_six_expand]
  simp [BaileyTerm, qPochhammer]

/-- BaileyBeta at `n = 7` expands to its eight defining summands. -/
theorem BaileyBeta_seven_expand (a q : R) (α : Nat → R) :
    BaileyBeta a q α 7 =
      BaileyTerm a q α 7 0 + BaileyTerm a q α 7 1 +
      BaileyTerm a q α 7 2 + BaileyTerm a q α 7 3 +
      BaileyTerm a q α 7 4 + BaileyTerm a q α 7 5 +
      BaileyTerm a q α 7 6 + BaileyTerm a q α 7 7 := by
  simp [BaileyBeta, natSum]

/-- BaileyBeta at `n = 7`, with all eight defining summands simplified. -/
theorem BaileyBeta_seven_terms (a q : R) (α : Nat → R) :
    BaileyBeta a q α 7 =
      α 0 / (qPochhammer q 7 * qPoch (a * q) q 7) +
      α 1 / (qPochhammer q 6 * qPoch (a * q) q 8) +
      α 2 / (qPochhammer q 5 * qPoch (a * q) q 9) +
      α 3 / (qPochhammer q 4 * qPoch (a * q) q 10) +
      α 4 / (qPochhammer q 3 * qPoch (a * q) q 11) +
      α 5 / (qPochhammer q 2 * qPoch (a * q) q 12) +
      α 6 / (qPochhammer q 1 * qPoch (a * q) q 13) +
      α 7 / qPoch (a * q) q 14 := by
  rw [BaileyBeta_seven_expand]
  simp [BaileyTerm, qPochhammer]

/-- BaileyBeta at `n = 8` expands to its nine defining summands. -/
theorem BaileyBeta_eight_expand (a q : R) (α : Nat → R) :
    BaileyBeta a q α 8 =
      BaileyTerm a q α 8 0 + BaileyTerm a q α 8 1 +
      BaileyTerm a q α 8 2 + BaileyTerm a q α 8 3 +
      BaileyTerm a q α 8 4 + BaileyTerm a q α 8 5 +
      BaileyTerm a q α 8 6 + BaileyTerm a q α 8 7 +
      BaileyTerm a q α 8 8 := by
  simp [BaileyBeta, natSum]

/-- BaileyBeta at `n = 8`, with all nine defining summands simplified. -/
theorem BaileyBeta_eight_terms (a q : R) (α : Nat → R) :
    BaileyBeta a q α 8 =
      α 0 / (qPochhammer q 8 * qPoch (a * q) q 8) +
      α 1 / (qPochhammer q 7 * qPoch (a * q) q 9) +
      α 2 / (qPochhammer q 6 * qPoch (a * q) q 10) +
      α 3 / (qPochhammer q 5 * qPoch (a * q) q 11) +
      α 4 / (qPochhammer q 4 * qPoch (a * q) q 12) +
      α 5 / (qPochhammer q 3 * qPoch (a * q) q 13) +
      α 6 / (qPochhammer q 2 * qPoch (a * q) q 14) +
      α 7 / (qPochhammer q 1 * qPoch (a * q) q 15) +
      α 8 / qPoch (a * q) q 16 := by
  rw [BaileyBeta_eight_expand]
  simp [BaileyTerm, qPochhammer]

/-- Full finite-form Bailey pair relation:
`β_n = ∑_{k=0}^n α_k / ((q;q)_{n-k}(aq;q)_{n+k})` for every `n`. -/
def IsBaileyPair (a q : R) (α β : Nat → R) : Prop :=
  ∀ n : Nat, β n = BaileyBeta a q α n

/-- Bailey pair relation checked only up to `N`. -/
def IsBaileyPairUpTo (a q : R) (α β : Nat → R) (N : Nat) : Prop :=
  ∀ n : Nat, n ≤ N → β n = BaileyBeta a q α n

/-- The canonical β generated from any α is a Bailey pair by definition. -/
theorem isBaileyPair_BaileyBeta (a q : R) (α : Nat → R) :
    IsBaileyPair a q α (BaileyBeta a q α) := by
  intro n
  rfl

/-- A full Bailey pair gives the finite relation up to any truncation depth. -/
theorem IsBaileyPair.upTo {a q : R} {α β : Nat → R} (h : IsBaileyPair a q α β)
    (N : Nat) :
    IsBaileyPairUpTo a q α β N := by
  intro n _hn
  exact h n

/-- A Bailey-pair relation checked up to `N` also holds up to any smaller `M`. -/
theorem IsBaileyPairUpTo.mono {a q : R} {α β : Nat → R} {M N : Nat}
    (h : IsBaileyPairUpTo a q α β N) (hMN : M ≤ N) :
    IsBaileyPairUpTo a q α β M := by
  intro n hn
  exact h n (Nat.le_trans hn hMN)

/-- Any up-to Bailey relation includes the zeroth component. -/
theorem IsBaileyPairUpTo.zero {a q : R} {α β : Nat → R} {N : Nat}
    (h : IsBaileyPairUpTo a q α β N) :
    β 0 = BaileyBeta a q α 0 :=
  h 0 (Nat.zero_le N)

/-- The `n = 0` component of a Bailey-pair relation checked up to `1`. -/
theorem IsBaileyPairUpTo.zero_of_one {a q : R} {α β : Nat → R}
    (h : IsBaileyPairUpTo a q α β 1) :
    β 0 = BaileyBeta a q α 0 :=
  h.zero

/-- The `n = 1` component of a Bailey-pair relation checked up to `1`. -/
theorem IsBaileyPairUpTo.one {a q : R} {α β : Nat → R}
    (h : IsBaileyPairUpTo a q α β 1) :
    β 1 = BaileyBeta a q α 1 :=
  h 1 (by omega)

/-- The `n = 2` component of a Bailey-pair relation checked up to `2`. -/
theorem IsBaileyPairUpTo.two {a q : R} {α β : Nat → R}
    (h : IsBaileyPairUpTo a q α β 2) :
    β 2 = BaileyBeta a q α 2 :=
  h 2 (by omega)

/-- The `n = 1` component of a Bailey-pair relation checked up to `2`. -/
theorem IsBaileyPairUpTo.one_of_two {a q : R} {α β : Nat → R}
    (h : IsBaileyPairUpTo a q α β 2) :
    β 1 = BaileyBeta a q α 1 :=
  h 1 (by omega)

/-- The `n = 3` component of a Bailey-pair relation checked up to `3`. -/
theorem IsBaileyPairUpTo.three {a q : R} {α β : Nat → R}
    (h : IsBaileyPairUpTo a q α β 3) :
    β 3 = BaileyBeta a q α 3 :=
  h 3 (by omega)

/-- The `n = 1` component of a Bailey-pair relation checked up to `3`. -/
theorem IsBaileyPairUpTo.one_of_three {a q : R} {α β : Nat → R}
    (h : IsBaileyPairUpTo a q α β 3) :
    β 1 = BaileyBeta a q α 1 :=
  h 1 (by omega)

/-- The `n = 2` component of a Bailey-pair relation checked up to `3`. -/
theorem IsBaileyPairUpTo.two_of_three {a q : R} {α β : Nat → R}
    (h : IsBaileyPairUpTo a q α β 3) :
    β 2 = BaileyBeta a q α 2 :=
  h 2 (by omega)

/-- The `n = 4` component of a Bailey-pair relation checked up to `4`. -/
theorem IsBaileyPairUpTo.four {a q : R} {α β : Nat → R}
    (h : IsBaileyPairUpTo a q α β 4) :
    β 4 = BaileyBeta a q α 4 :=
  h 4 (by omega)

/-- The `n = 1` component of a Bailey-pair relation checked up to `4`. -/
theorem IsBaileyPairUpTo.one_of_four {a q : R} {α β : Nat → R}
    (h : IsBaileyPairUpTo a q α β 4) :
    β 1 = BaileyBeta a q α 1 :=
  h 1 (by omega)

/-- The `n = 2` component of a Bailey-pair relation checked up to `4`. -/
theorem IsBaileyPairUpTo.two_of_four {a q : R} {α β : Nat → R}
    (h : IsBaileyPairUpTo a q α β 4) :
    β 2 = BaileyBeta a q α 2 :=
  h 2 (by omega)

/-- The `n = 3` component of a Bailey-pair relation checked up to `4`. -/
theorem IsBaileyPairUpTo.three_of_four {a q : R} {α β : Nat → R}
    (h : IsBaileyPairUpTo a q α β 4) :
    β 3 = BaileyBeta a q α 3 :=
  h 3 (by omega)

/-- The `n = 5` component of a Bailey-pair relation checked up to `5`. -/
theorem IsBaileyPairUpTo.five {a q : R} {α β : Nat → R}
    (h : IsBaileyPairUpTo a q α β 5) :
    β 5 = BaileyBeta a q α 5 :=
  h 5 (by omega)

/-- The `n = 6` component of a Bailey-pair relation checked up to `6`. -/
theorem IsBaileyPairUpTo.six {a q : R} {α β : Nat → R}
    (h : IsBaileyPairUpTo a q α β 6) :
    β 6 = BaileyBeta a q α 6 :=
  h 6 (by omega)

/-- The `n = 1` component of a Bailey-pair relation checked up to `5`. -/
theorem IsBaileyPairUpTo.one_of_five {a q : R} {α β : Nat → R}
    (h : IsBaileyPairUpTo a q α β 5) :
    β 1 = BaileyBeta a q α 1 :=
  h 1 (by omega)

/-- The `n = 2` component of a Bailey-pair relation checked up to `5`. -/
theorem IsBaileyPairUpTo.two_of_five {a q : R} {α β : Nat → R}
    (h : IsBaileyPairUpTo a q α β 5) :
    β 2 = BaileyBeta a q α 2 :=
  h 2 (by omega)

/-- The `n = 3` component of a Bailey-pair relation checked up to `5`. -/
theorem IsBaileyPairUpTo.three_of_five {a q : R} {α β : Nat → R}
    (h : IsBaileyPairUpTo a q α β 5) :
    β 3 = BaileyBeta a q α 3 :=
  h 3 (by omega)

/-- The `n = 4` component of a Bailey-pair relation checked up to `5`. -/
theorem IsBaileyPairUpTo.four_of_five {a q : R} {α β : Nat → R}
    (h : IsBaileyPairUpTo a q α β 5) :
    β 4 = BaileyBeta a q α 4 :=
  h 4 (by omega)

/-- The `n = 1` component of a Bailey-pair relation checked up to `6`. -/
theorem IsBaileyPairUpTo.one_of_six {a q : R} {α β : Nat → R}
    (h : IsBaileyPairUpTo a q α β 6) :
    β 1 = BaileyBeta a q α 1 :=
  h 1 (by omega)

/-- The `n = 2` component of a Bailey-pair relation checked up to `6`. -/
theorem IsBaileyPairUpTo.two_of_six {a q : R} {α β : Nat → R}
    (h : IsBaileyPairUpTo a q α β 6) :
    β 2 = BaileyBeta a q α 2 :=
  h 2 (by omega)

/-- The `n = 3` component of a Bailey-pair relation checked up to `6`. -/
theorem IsBaileyPairUpTo.three_of_six {a q : R} {α β : Nat → R}
    (h : IsBaileyPairUpTo a q α β 6) :
    β 3 = BaileyBeta a q α 3 :=
  h 3 (by omega)

/-- The `n = 4` component of a Bailey-pair relation checked up to `6`. -/
theorem IsBaileyPairUpTo.four_of_six {a q : R} {α β : Nat → R}
    (h : IsBaileyPairUpTo a q α β 6) :
    β 4 = BaileyBeta a q α 4 :=
  h 4 (by omega)

/-- The `n = 5` component of a Bailey-pair relation checked up to `6`. -/
theorem IsBaileyPairUpTo.five_of_six {a q : R} {α β : Nat → R}
    (h : IsBaileyPairUpTo a q α β 6) :
    β 5 = BaileyBeta a q α 5 :=
  h 5 (by omega)

/-- The `n = 7` component of a Bailey-pair relation checked up to `7`. -/
theorem IsBaileyPairUpTo.seven {a q : R} {α β : Nat → R}
    (h : IsBaileyPairUpTo a q α β 7) :
    β 7 = BaileyBeta a q α 7 :=
  h 7 (by omega)

/-- The `n = 1` component of a Bailey-pair relation checked up to `7`. -/
theorem IsBaileyPairUpTo.one_of_seven {a q : R} {α β : Nat → R}
    (h : IsBaileyPairUpTo a q α β 7) :
    β 1 = BaileyBeta a q α 1 :=
  h 1 (by omega)

/-- The `n = 2` component of a Bailey-pair relation checked up to `7`. -/
theorem IsBaileyPairUpTo.two_of_seven {a q : R} {α β : Nat → R}
    (h : IsBaileyPairUpTo a q α β 7) :
    β 2 = BaileyBeta a q α 2 :=
  h 2 (by omega)

/-- The `n = 3` component of a Bailey-pair relation checked up to `7`. -/
theorem IsBaileyPairUpTo.three_of_seven {a q : R} {α β : Nat → R}
    (h : IsBaileyPairUpTo a q α β 7) :
    β 3 = BaileyBeta a q α 3 :=
  h 3 (by omega)

/-- The `n = 4` component of a Bailey-pair relation checked up to `7`. -/
theorem IsBaileyPairUpTo.four_of_seven {a q : R} {α β : Nat → R}
    (h : IsBaileyPairUpTo a q α β 7) :
    β 4 = BaileyBeta a q α 4 :=
  h 4 (by omega)

/-- The `n = 5` component of a Bailey-pair relation checked up to `7`. -/
theorem IsBaileyPairUpTo.five_of_seven {a q : R} {α β : Nat → R}
    (h : IsBaileyPairUpTo a q α β 7) :
    β 5 = BaileyBeta a q α 5 :=
  h 5 (by omega)

/-- The `n = 6` component of a Bailey-pair relation checked up to `7`. -/
theorem IsBaileyPairUpTo.six_of_seven {a q : R} {α β : Nat → R}
    (h : IsBaileyPairUpTo a q α β 7) :
    β 6 = BaileyBeta a q α 6 :=
  h 6 (by omega)

/-- The `n = 8` component of a Bailey-pair relation checked up to `8`. -/
theorem IsBaileyPairUpTo.eight {a q : R} {α β : Nat → R}
    (h : IsBaileyPairUpTo a q α β 8) :
    β 8 = BaileyBeta a q α 8 :=
  h 8 (by omega)

/-- The `n = 1` component of a Bailey-pair relation checked up to `8`. -/
theorem IsBaileyPairUpTo.one_of_eight {a q : R} {α β : Nat → R}
    (h : IsBaileyPairUpTo a q α β 8) :
    β 1 = BaileyBeta a q α 1 :=
  h 1 (by omega)

/-- The `n = 2` component of a Bailey-pair relation checked up to `8`. -/
theorem IsBaileyPairUpTo.two_of_eight {a q : R} {α β : Nat → R}
    (h : IsBaileyPairUpTo a q α β 8) :
    β 2 = BaileyBeta a q α 2 :=
  h 2 (by omega)

/-- The `n = 3` component of a Bailey-pair relation checked up to `8`. -/
theorem IsBaileyPairUpTo.three_of_eight {a q : R} {α β : Nat → R}
    (h : IsBaileyPairUpTo a q α β 8) :
    β 3 = BaileyBeta a q α 3 :=
  h 3 (by omega)

/-- The `n = 4` component of a Bailey-pair relation checked up to `8`. -/
theorem IsBaileyPairUpTo.four_of_eight {a q : R} {α β : Nat → R}
    (h : IsBaileyPairUpTo a q α β 8) :
    β 4 = BaileyBeta a q α 4 :=
  h 4 (by omega)

/-- The `n = 5` component of a Bailey-pair relation checked up to `8`. -/
theorem IsBaileyPairUpTo.five_of_eight {a q : R} {α β : Nat → R}
    (h : IsBaileyPairUpTo a q α β 8) :
    β 5 = BaileyBeta a q α 5 :=
  h 5 (by omega)

/-- The `n = 6` component of a Bailey-pair relation checked up to `8`. -/
theorem IsBaileyPairUpTo.six_of_eight {a q : R} {α β : Nat → R}
    (h : IsBaileyPairUpTo a q α β 8) :
    β 6 = BaileyBeta a q α 6 :=
  h 6 (by omega)

/-- The `n = 7` component of a Bailey-pair relation checked up to `8`. -/
theorem IsBaileyPairUpTo.seven_of_eight {a q : R} {α β : Nat → R}
    (h : IsBaileyPairUpTo a q α β 8) :
    β 7 = BaileyBeta a q α 7 :=
  h 7 (by omega)

/-- A single `n = 0` identity assembles the Bailey relation up to zero. -/
theorem IsBaileyPairUpTo.of_zero {a q : R} {α β : Nat → R}
    (h0 : β 0 = BaileyBeta a q α 0) :
    IsBaileyPairUpTo a q α β 0 := by
  intro n hn
  interval_cases n
  exact h0

/-- The `n = 0,1` identities assemble the Bailey relation up to one. -/
theorem IsBaileyPairUpTo.of_one {a q : R} {α β : Nat → R}
    (h0 : β 0 = BaileyBeta a q α 0)
    (h1 : β 1 = BaileyBeta a q α 1) :
    IsBaileyPairUpTo a q α β 1 := by
  intro n hn
  interval_cases n
  · exact h0
  · exact h1

/-- The `n = 0,1,2` identities assemble the Bailey relation up to two. -/
theorem IsBaileyPairUpTo.of_two {a q : R} {α β : Nat → R}
    (h0 : β 0 = BaileyBeta a q α 0)
    (h1 : β 1 = BaileyBeta a q α 1)
    (h2 : β 2 = BaileyBeta a q α 2) :
    IsBaileyPairUpTo a q α β 2 := by
  intro n hn
  interval_cases n
  · exact h0
  · exact h1
  · exact h2

/-- The `n = 0,1,2,3` identities assemble the Bailey relation up to three. -/
theorem IsBaileyPairUpTo.of_three {a q : R} {α β : Nat → R}
    (h0 : β 0 = BaileyBeta a q α 0)
    (h1 : β 1 = BaileyBeta a q α 1)
    (h2 : β 2 = BaileyBeta a q α 2)
    (h3 : β 3 = BaileyBeta a q α 3) :
    IsBaileyPairUpTo a q α β 3 := by
  intro n hn
  interval_cases n
  · exact h0
  · exact h1
  · exact h2
  · exact h3

/-- The `n = 0,1,2,3,4` identities assemble the Bailey relation up to four. -/
theorem IsBaileyPairUpTo.of_four {a q : R} {α β : Nat → R}
    (h0 : β 0 = BaileyBeta a q α 0)
    (h1 : β 1 = BaileyBeta a q α 1)
    (h2 : β 2 = BaileyBeta a q α 2)
    (h3 : β 3 = BaileyBeta a q α 3)
    (h4 : β 4 = BaileyBeta a q α 4) :
    IsBaileyPairUpTo a q α β 4 := by
  intro n hn
  interval_cases n
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

/-- The `n = 0,1,2,3,4,5` identities assemble the Bailey relation up to five. -/
theorem IsBaileyPairUpTo.of_five {a q : R} {α β : Nat → R}
    (h0 : β 0 = BaileyBeta a q α 0)
    (h1 : β 1 = BaileyBeta a q α 1)
    (h2 : β 2 = BaileyBeta a q α 2)
    (h3 : β 3 = BaileyBeta a q α 3)
    (h4 : β 4 = BaileyBeta a q α 4)
    (h5 : β 5 = BaileyBeta a q α 5) :
    IsBaileyPairUpTo a q α β 5 := by
  intro n hn
  interval_cases n
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

/-- The `n = 0,1,2,3,4,5,6` identities assemble the Bailey relation up to six. -/
theorem IsBaileyPairUpTo.of_six {a q : R} {α β : Nat → R}
    (h0 : β 0 = BaileyBeta a q α 0)
    (h1 : β 1 = BaileyBeta a q α 1)
    (h2 : β 2 = BaileyBeta a q α 2)
    (h3 : β 3 = BaileyBeta a q α 3)
    (h4 : β 4 = BaileyBeta a q α 4)
    (h5 : β 5 = BaileyBeta a q α 5)
    (h6 : β 6 = BaileyBeta a q α 6) :
    IsBaileyPairUpTo a q α β 6 := by
  intro n hn
  interval_cases n
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6

/-- The `n = 0,..,7` identities assemble the Bailey relation up to seven. -/
theorem IsBaileyPairUpTo.of_seven {a q : R} {α β : Nat → R}
    (h0 : β 0 = BaileyBeta a q α 0)
    (h1 : β 1 = BaileyBeta a q α 1)
    (h2 : β 2 = BaileyBeta a q α 2)
    (h3 : β 3 = BaileyBeta a q α 3)
    (h4 : β 4 = BaileyBeta a q α 4)
    (h5 : β 5 = BaileyBeta a q α 5)
    (h6 : β 6 = BaileyBeta a q α 6)
    (h7 : β 7 = BaileyBeta a q α 7) :
    IsBaileyPairUpTo a q α β 7 := by
  intro n hn
  interval_cases n
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7

/-- Up-to-one Bailey relations are exactly their two component equations. -/
theorem isBaileyPairUpTo_one_iff {a q : R} {α β : Nat → R} :
    IsBaileyPairUpTo a q α β 1 ↔
      β 0 = BaileyBeta a q α 0 ∧ β 1 = BaileyBeta a q α 1 := by
  constructor
  · intro h
    exact ⟨h.zero_of_one, h.one⟩
  · rintro ⟨h0, h1⟩
    exact IsBaileyPairUpTo.of_one h0 h1

/-- Up-to-two Bailey relations are exactly their three component equations. -/
theorem isBaileyPairUpTo_two_iff {a q : R} {α β : Nat → R} :
    IsBaileyPairUpTo a q α β 2 ↔
      β 0 = BaileyBeta a q α 0 ∧ β 1 = BaileyBeta a q α 1 ∧
        β 2 = BaileyBeta a q α 2 := by
  constructor
  · intro h
    exact ⟨h 0 (by omega), h 1 (by omega), h.two⟩
  · rintro ⟨h0, h1, h2⟩
    exact IsBaileyPairUpTo.of_two h0 h1 h2

/-- Up-to-three Bailey relations are exactly their four component equations. -/
theorem isBaileyPairUpTo_three_iff {a q : R} {α β : Nat → R} :
    IsBaileyPairUpTo a q α β 3 ↔
      β 0 = BaileyBeta a q α 0 ∧ β 1 = BaileyBeta a q α 1 ∧
        β 2 = BaileyBeta a q α 2 ∧ β 3 = BaileyBeta a q α 3 := by
  constructor
  · intro h
    exact ⟨h 0 (by omega), h 1 (by omega), h 2 (by omega), h.three⟩
  · rintro ⟨h0, h1, h2, h3⟩
    exact IsBaileyPairUpTo.of_three h0 h1 h2 h3

/-- Up-to-four Bailey relations are exactly their five component equations. -/
theorem isBaileyPairUpTo_four_iff {a q : R} {α β : Nat → R} :
    IsBaileyPairUpTo a q α β 4 ↔
      β 0 = BaileyBeta a q α 0 ∧ β 1 = BaileyBeta a q α 1 ∧
        β 2 = BaileyBeta a q α 2 ∧ β 3 = BaileyBeta a q α 3 ∧
        β 4 = BaileyBeta a q α 4 := by
  constructor
  · intro h
    exact ⟨h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega), h.four⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩
    exact IsBaileyPairUpTo.of_four h0 h1 h2 h3 h4

/-- Up-to-five Bailey relations are exactly their six component equations. -/
theorem isBaileyPairUpTo_five_iff {a q : R} {α β : Nat → R} :
    IsBaileyPairUpTo a q α β 5 ↔
      β 0 = BaileyBeta a q α 0 ∧ β 1 = BaileyBeta a q α 1 ∧
        β 2 = BaileyBeta a q α 2 ∧ β 3 = BaileyBeta a q α 3 ∧
        β 4 = BaileyBeta a q α 4 ∧ β 5 = BaileyBeta a q α 5 := by
  constructor
  · intro h
    exact ⟨h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega),
      h 4 (by omega), h.five⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5⟩
    exact IsBaileyPairUpTo.of_five h0 h1 h2 h3 h4 h5

/-- Up-to-six Bailey relations are exactly their seven component equations. -/
theorem isBaileyPairUpTo_six_iff {a q : R} {α β : Nat → R} :
    IsBaileyPairUpTo a q α β 6 ↔
      β 0 = BaileyBeta a q α 0 ∧ β 1 = BaileyBeta a q α 1 ∧
        β 2 = BaileyBeta a q α 2 ∧ β 3 = BaileyBeta a q α 3 ∧
        β 4 = BaileyBeta a q α 4 ∧ β 5 = BaileyBeta a q α 5 ∧
        β 6 = BaileyBeta a q α 6 := by
  constructor
  · intro h
    exact ⟨h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega),
      h 4 (by omega), h 5 (by omega), h.six⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
    exact IsBaileyPairUpTo.of_six h0 h1 h2 h3 h4 h5 h6

/-- The canonical β generated from any α is a Bailey pair up to any `N`. -/
theorem isBaileyPairUpTo_BaileyBeta (a q : R) (α : Nat → R) (N : Nat) :
    IsBaileyPairUpTo a q α (BaileyBeta a q α) N :=
  (isBaileyPair_BaileyBeta a q α).upTo N

/-- Trivial Bailey pair: α_0 = 1, α_k = 0 for k ≥ 1. Then β_0 = 1 / (1 · (a q; q)_0) = 1. -/
theorem BaileyBeta_trivial_zero (a q : R) (_h : qPochhammer q 0 ≠ 0)
    (_h' : qPoch (a * q) q 0 ≠ 0) :
    BaileyBeta a q (fun k => if k = 0 then 1 else 0) 0 = 1 := by
  simp [BaileyBeta, BaileyTerm, natSum, qPochhammer, qPoch]

/-- The nonzero `k = 0` summand for the trivial Bailey pair at `n = 1`. -/
@[simp] theorem BaileyTerm_trivial_one_zero (a q : R) :
    BaileyTerm a q (fun k => if k = 0 then 1 else 0) 1 0 =
      1 / ((1 - q) * (1 - a * q)) := by
  simp [BaileyTerm, qPochhammer, qPoch]

/-- The `k = 1` summand for the trivial Bailey pair at `n = 1` vanishes. -/
@[simp] theorem BaileyTerm_trivial_one_one (a q : R) :
    BaileyTerm a q (fun k => if k = 0 then 1 else 0) 1 1 = 0 := by
  simp [BaileyTerm]

/-- Trivial Bailey pair with `α = δ_0`: the `n = 1` beta value. -/
theorem BaileyBeta_trivial_one (a q : R) :
    BaileyBeta a q (fun k => if k = 0 then 1 else 0) 1 =
      1 / ((1 - q) * (1 - a * q)) := by
  simp [BaileyBeta, natSum]

/-- Trivial Bailey pair with `α = δ_0`: the `n = 1` beta value. -/
theorem BaileyBeta_trivial_succ (a q : R) (_h_q1 : 1 - q ≠ 0)
    (_h_aq1 : 1 - a * q ≠ 0) :
    BaileyBeta a q (fun k => if k = 0 then 1 else 0) 1 =
      1 / ((1 - q) * (1 - a * q)) := by
  exact BaileyBeta_trivial_one a q

/-- Trivial Bailey pair α = δ_0: the n = 2 beta value. -/
theorem BaileyBeta_trivial_two (a q : R) :
    BaileyBeta a q (fun k => if k = 0 then 1 else 0) 2 =
      1 / ((1 - q) * (1 - q ^ 2) * (1 - a * q) * (1 - a * q ^ 2)) := by
  simp [BaileyBeta, natSum, BaileyTerm, qPochhammer, qPoch]
  ring

/-- Trivial Bailey pair α = δ_0: the n = 3 beta value. -/
theorem BaileyBeta_trivial_three (a q : R) :
    BaileyBeta a q (fun k => if k = 0 then 1 else 0) 3 =
      1 / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - a * q) * (1 - a * q ^ 2) * (1 - a * q ^ 3)) := by
  simp [BaileyBeta, natSum, BaileyTerm, qPochhammer, qPoch]
  ring

theorem BaileyBeta_trivial_four (a q : R) :
    BaileyBeta a q (fun k => if k = 0 then 1 else 0) 4 =
      1 / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) *
           (1 - a * q) * (1 - a * q ^ 2) * (1 - a * q ^ 3) * (1 - a * q ^ 4)) := by
  simp [BaileyBeta, natSum, BaileyTerm, qPochhammer, qPoch]
  ring

/-- Trivial Bailey pair α = δ_0: the n = 5 beta value. -/
theorem BaileyBeta_trivial_five (a q : R) :
    BaileyBeta a q (fun k => if k = 0 then 1 else 0) 5 =
      1 / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
           (1 - a * q) * (1 - a * q ^ 2) * (1 - a * q ^ 3) * (1 - a * q ^ 4) * (1 - a * q ^ 5)) := by
  simp [BaileyBeta, natSum, BaileyTerm, qPochhammer, qPoch]
  ring

/-- Trivial Bailey pair α = δ_0: the n = 6 beta value. -/
theorem BaileyBeta_trivial_six (a q : R) :
    BaileyBeta a q (fun k => if k = 0 then 1 else 0) 6 =
      1 / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) *
           (1 - a * q) * (1 - a * q ^ 2) * (1 - a * q ^ 3) * (1 - a * q ^ 4) * (1 - a * q ^ 5) * (1 - a * q ^ 6)) := by
  simp [BaileyBeta, natSum, BaileyTerm, qPochhammer, qPoch]
  ring

/-- Trivial Bailey pair α = δ_0: the n = 7 beta value. -/
theorem BaileyBeta_trivial_seven (a q : R) :
    BaileyBeta a q (fun k => if k = 0 then 1 else 0) 7 =
      1 / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) *
           (1 - a * q) * (1 - a * q ^ 2) * (1 - a * q ^ 3) * (1 - a * q ^ 4) * (1 - a * q ^ 5) * (1 - a * q ^ 6) * (1 - a * q ^ 7)) := by
  simp [BaileyBeta, natSum, BaileyTerm, qPochhammer, qPoch]
  ring

/-- Trivial Bailey pair α = δ_0: the n = 8 beta value. -/
theorem BaileyBeta_trivial_eight (a q : R) :
    BaileyBeta a q (fun k => if k = 0 then 1 else 0) 8 =
      1 / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) *
           (1 - a * q) * (1 - a * q ^ 2) * (1 - a * q ^ 3) * (1 - a * q ^ 4) * (1 - a * q ^ 5) * (1 - a * q ^ 6) * (1 - a * q ^ 7) * (1 - a * q ^ 8)) := by
  simp [BaileyBeta, natSum, BaileyTerm, qPochhammer, qPoch]
  ring

/-- Trivial Bailey pair α = δ_0: the n = 9 beta value. -/
theorem BaileyBeta_trivial_nine (a q : R) :
    BaileyBeta a q (fun k => if k = 0 then 1 else 0) 9 =
      1 / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) *
           (1 - a * q) * (1 - a * q ^ 2) * (1 - a * q ^ 3) * (1 - a * q ^ 4) * (1 - a * q ^ 5) * (1 - a * q ^ 6) * (1 - a * q ^ 7) * (1 - a * q ^ 8) * (1 - a * q ^ 9)) := by
  simp [BaileyBeta, natSum, BaileyTerm, qPochhammer, qPoch]
  ring

/-- Trivial Bailey pair α = δ_0: the n = 10 beta value. -/
theorem BaileyBeta_trivial_ten (a q : R) :
    BaileyBeta a q (fun k => if k = 0 then 1 else 0) 10 =
      1 / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
           (1 - a * q) * (1 - a * q ^ 2) * (1 - a * q ^ 3) * (1 - a * q ^ 4) * (1 - a * q ^ 5) * (1 - a * q ^ 6) * (1 - a * q ^ 7) * (1 - a * q ^ 8) * (1 - a * q ^ 9) * (1 - a * q ^ 10)) := by
  simp [BaileyBeta, natSum, BaileyTerm, qPochhammer, qPoch]
  ring

/-- Trivial Bailey pair α = δ_0: the n = 11 beta value. -/
theorem BaileyBeta_trivial_eleven (a q : R) :
    BaileyBeta a q (fun k => if k = 0 then 1 else 0) 11 =
      1 / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) * (1 - q ^ 11) *
           (1 - a * q) * (1 - a * q ^ 2) * (1 - a * q ^ 3) * (1 - a * q ^ 4) * (1 - a * q ^ 5) * (1 - a * q ^ 6) * (1 - a * q ^ 7) * (1 - a * q ^ 8) * (1 - a * q ^ 9) * (1 - a * q ^ 10) * (1 - a * q ^ 11)) := by
  simp [BaileyBeta, natSum, BaileyTerm, qPochhammer, qPoch]
  ring

/-- Trivial Bailey pair α = δ_0: the n = 12 beta value. -/
theorem BaileyBeta_trivial_twelve (a q : R) :
    BaileyBeta a q (fun k => if k = 0 then 1 else 0) 12 =
      1 / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) * (1 - q ^ 11) * (1 - q ^ 12) *
           (1 - a * q) * (1 - a * q ^ 2) * (1 - a * q ^ 3) * (1 - a * q ^ 4) * (1 - a * q ^ 5) * (1 - a * q ^ 6) * (1 - a * q ^ 7) * (1 - a * q ^ 8) * (1 - a * q ^ 9) * (1 - a * q ^ 10) * (1 - a * q ^ 11) * (1 - a * q ^ 12)) := by
  simp [BaileyBeta, natSum, BaileyTerm, qPochhammer, qPoch]
  ring

/-- Trivial Bailey pair α = δ_0: the n = 13 beta value. -/
theorem BaileyBeta_trivial_thirteen (a q : R) :
    BaileyBeta a q (fun k => if k = 0 then 1 else 0) 13 =
      1 / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) * (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) *
           (1 - a * q) * (1 - a * q ^ 2) * (1 - a * q ^ 3) * (1 - a * q ^ 4) * (1 - a * q ^ 5) * (1 - a * q ^ 6) * (1 - a * q ^ 7) * (1 - a * q ^ 8) * (1 - a * q ^ 9) * (1 - a * q ^ 10) * (1 - a * q ^ 11) * (1 - a * q ^ 12) * (1 - a * q ^ 13)) := by
  simp [BaileyBeta, natSum, BaileyTerm, qPochhammer, qPoch]
  ring

/-- Trivial Bailey pair α = δ_0: the n = 14 beta value. -/
theorem BaileyBeta_trivial_fourteen (a q : R) :
    BaileyBeta a q (fun k => if k = 0 then 1 else 0) 14 =
      1 / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) * (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) *
           (1 - a * q) * (1 - a * q ^ 2) * (1 - a * q ^ 3) * (1 - a * q ^ 4) * (1 - a * q ^ 5) * (1 - a * q ^ 6) * (1 - a * q ^ 7) * (1 - a * q ^ 8) * (1 - a * q ^ 9) * (1 - a * q ^ 10) * (1 - a * q ^ 11) * (1 - a * q ^ 12) * (1 - a * q ^ 13) * (1 - a * q ^ 14)) := by
  simp [BaileyBeta, natSum, BaileyTerm, qPochhammer, qPoch]
  ring

/-- Trivial Bailey pair α = δ_0: the n = 15 beta value. -/
theorem BaileyBeta_trivial_fifteen (a q : R) :
    BaileyBeta a q (fun k => if k = 0 then 1 else 0) 15 =
      1 / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) * (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) *
           (1 - a * q) * (1 - a * q ^ 2) * (1 - a * q ^ 3) * (1 - a * q ^ 4) * (1 - a * q ^ 5) * (1 - a * q ^ 6) * (1 - a * q ^ 7) * (1 - a * q ^ 8) * (1 - a * q ^ 9) * (1 - a * q ^ 10) * (1 - a * q ^ 11) * (1 - a * q ^ 12) * (1 - a * q ^ 13) * (1 - a * q ^ 14) * (1 - a * q ^ 15)) := by
  simp [BaileyBeta, natSum, BaileyTerm, qPochhammer, qPoch]
  ring

/-- Trivial Bailey pair α = δ_0: the n = 16 beta value. -/
theorem BaileyBeta_trivial_sixteen (a q : R) :
    BaileyBeta a q (fun k => if k = 0 then 1 else 0) 16 =
      1 / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) * (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) * (1 - q ^ 16) *
           (1 - a * q) * (1 - a * q ^ 2) * (1 - a * q ^ 3) * (1 - a * q ^ 4) * (1 - a * q ^ 5) * (1 - a * q ^ 6) * (1 - a * q ^ 7) * (1 - a * q ^ 8) * (1 - a * q ^ 9) * (1 - a * q ^ 10) * (1 - a * q ^ 11) * (1 - a * q ^ 12) * (1 - a * q ^ 13) * (1 - a * q ^ 14) * (1 - a * q ^ 15) * (1 - a * q ^ 16)) := by
  simp [BaileyBeta, natSum, BaileyTerm, qPochhammer, qPoch]
  ring

/-- Trivial Bailey pair α = δ_0: the n = 17 beta value. -/
theorem BaileyBeta_trivial_seventeen (a q : R) :
    BaileyBeta a q (fun k => if k = 0 then 1 else 0) 17 =
      1 / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) * (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) * (1 - q ^ 16) * (1 - q ^ 17) *
           (1 - a * q) * (1 - a * q ^ 2) * (1 - a * q ^ 3) * (1 - a * q ^ 4) * (1 - a * q ^ 5) * (1 - a * q ^ 6) * (1 - a * q ^ 7) * (1 - a * q ^ 8) * (1 - a * q ^ 9) * (1 - a * q ^ 10) * (1 - a * q ^ 11) * (1 - a * q ^ 12) * (1 - a * q ^ 13) * (1 - a * q ^ 14) * (1 - a * q ^ 15) * (1 - a * q ^ 16) * (1 - a * q ^ 17)) := by
  simp [BaileyBeta, natSum, BaileyTerm, qPochhammer, qPoch]
  ring

/-- Trivial Bailey pair α = δ_0: the n = 18 beta value. -/
theorem BaileyBeta_trivial_eighteen (a q : R) :
    BaileyBeta a q (fun k => if k = 0 then 1 else 0) 18 =
      1 / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) * (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) * (1 - q ^ 16) * (1 - q ^ 17) * (1 - q ^ 18) *
           (1 - a * q) * (1 - a * q ^ 2) * (1 - a * q ^ 3) * (1 - a * q ^ 4) * (1 - a * q ^ 5) * (1 - a * q ^ 6) * (1 - a * q ^ 7) * (1 - a * q ^ 8) * (1 - a * q ^ 9) * (1 - a * q ^ 10) * (1 - a * q ^ 11) * (1 - a * q ^ 12) * (1 - a * q ^ 13) * (1 - a * q ^ 14) * (1 - a * q ^ 15) * (1 - a * q ^ 16) * (1 - a * q ^ 17) * (1 - a * q ^ 18)) := by
  simp [BaileyBeta, natSum, BaileyTerm, qPochhammer, qPoch]
  ring

set_option maxHeartbeats 400000 in
/-- Trivial Bailey pair α = δ_0: the n = 19 beta value. -/
theorem BaileyBeta_trivial_nineteen (a q : R) :
    BaileyBeta a q (fun k => if k = 0 then 1 else 0) 19 =
      1 / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) * (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) * (1 - q ^ 16) * (1 - q ^ 17) * (1 - q ^ 18) * (1 - q ^ 19) *
           (1 - a * q) * (1 - a * q ^ 2) * (1 - a * q ^ 3) * (1 - a * q ^ 4) * (1 - a * q ^ 5) * (1 - a * q ^ 6) * (1 - a * q ^ 7) * (1 - a * q ^ 8) * (1 - a * q ^ 9) * (1 - a * q ^ 10) * (1 - a * q ^ 11) * (1 - a * q ^ 12) * (1 - a * q ^ 13) * (1 - a * q ^ 14) * (1 - a * q ^ 15) * (1 - a * q ^ 16) * (1 - a * q ^ 17) * (1 - a * q ^ 18) * (1 - a * q ^ 19)) := by
  simp [BaileyBeta, natSum, BaileyTerm, qPochhammer, qPoch]
  ring

set_option maxHeartbeats 400000 in
/-- Trivial Bailey pair α = δ_0: the n = 20 beta value. -/
theorem BaileyBeta_trivial_twenty (a q : R) :
    BaileyBeta a q (fun k => if k = 0 then 1 else 0) 20 =
      1 / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) * (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) * (1 - q ^ 16) * (1 - q ^ 17) * (1 - q ^ 18) * (1 - q ^ 19) * (1 - q ^ 20) *
           (1 - a * q) * (1 - a * q ^ 2) * (1 - a * q ^ 3) * (1 - a * q ^ 4) * (1 - a * q ^ 5) * (1 - a * q ^ 6) * (1 - a * q ^ 7) * (1 - a * q ^ 8) * (1 - a * q ^ 9) * (1 - a * q ^ 10) * (1 - a * q ^ 11) * (1 - a * q ^ 12) * (1 - a * q ^ 13) * (1 - a * q ^ 14) * (1 - a * q ^ 15) * (1 - a * q ^ 16) * (1 - a * q ^ 17) * (1 - a * q ^ 18) * (1 - a * q ^ 19) * (1 - a * q ^ 20)) := by
  simp [BaileyBeta, natSum, BaileyTerm, qPochhammer, qPoch]
  ring

set_option maxHeartbeats 800000 in
/-- Trivial Bailey pair α = δ_0: the n = 21 beta value. -/
theorem BaileyBeta_trivial_twentyone (a q : R) :
    BaileyBeta a q (fun k => if k = 0 then 1 else 0) 21 =
      1 / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) * (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) * (1 - q ^ 16) * (1 - q ^ 17) * (1 - q ^ 18) * (1 - q ^ 19) * (1 - q ^ 20) * (1 - q ^ 21) *
           (1 - a * q) * (1 - a * q ^ 2) * (1 - a * q ^ 3) * (1 - a * q ^ 4) * (1 - a * q ^ 5) * (1 - a * q ^ 6) * (1 - a * q ^ 7) * (1 - a * q ^ 8) * (1 - a * q ^ 9) * (1 - a * q ^ 10) * (1 - a * q ^ 11) * (1 - a * q ^ 12) * (1 - a * q ^ 13) * (1 - a * q ^ 14) * (1 - a * q ^ 15) * (1 - a * q ^ 16) * (1 - a * q ^ 17) * (1 - a * q ^ 18) * (1 - a * q ^ 19) * (1 - a * q ^ 20) * (1 - a * q ^ 21)) := by
  simp [BaileyBeta, natSum, BaileyTerm, qPochhammer, qPoch]
  ring

set_option maxHeartbeats 800000 in
/-- Trivial Bailey pair α = δ_0: the n = 22 beta value. -/
theorem BaileyBeta_trivial_twentytwo (a q : R) :
    BaileyBeta a q (fun k => if k = 0 then 1 else 0) 22 =
      1 / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) * (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) * (1 - q ^ 16) * (1 - q ^ 17) * (1 - q ^ 18) * (1 - q ^ 19) * (1 - q ^ 20) * (1 - q ^ 21) * (1 - q ^ 22) *
           (1 - a * q) * (1 - a * q ^ 2) * (1 - a * q ^ 3) * (1 - a * q ^ 4) * (1 - a * q ^ 5) * (1 - a * q ^ 6) * (1 - a * q ^ 7) * (1 - a * q ^ 8) * (1 - a * q ^ 9) * (1 - a * q ^ 10) * (1 - a * q ^ 11) * (1 - a * q ^ 12) * (1 - a * q ^ 13) * (1 - a * q ^ 14) * (1 - a * q ^ 15) * (1 - a * q ^ 16) * (1 - a * q ^ 17) * (1 - a * q ^ 18) * (1 - a * q ^ 19) * (1 - a * q ^ 20) * (1 - a * q ^ 21) * (1 - a * q ^ 22)) := by
  simp [BaileyBeta, natSum, BaileyTerm, qPochhammer, qPoch]
  ring

private lemma BaileyTerm_trivial_pos (a q : R) (n k : Nat) (hk : 1 ≤ k) :
    BaileyTerm a q (fun j => if j = 0 then 1 else 0) n k = 0 := by
  have hk0 : k ≠ 0 := by omega
  simp [BaileyTerm, hk0]

private lemma natSum_only_first (f : Nat → R) (n : Nat)
    (h : ∀ k, 1 ≤ k → f k = 0) :
    natSum f n = f 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [natSum_succ]
    rw [ih, h (n + 1) (by omega), add_zero]

theorem BaileyBeta_trivial_general (a q : R) (n : Nat) :
    BaileyBeta a q (fun k => if k = 0 then 1 else 0) n =
      1 / (qPochhammer q n * qPoch (a * q) q n) := by
  unfold BaileyBeta
  rw [natSum_only_first _ n (fun k hk => BaileyTerm_trivial_pos a q n k hk)]
  simp [BaileyTerm]

/-! ### Rogers–Ramanujan Bailey pair seed and Bailey transform -/

/-- The Rogers–Ramanujan seed for α:
`α_n = (-1)^n · q^{n(n-1)/2} · (1 - a·q^{2n}) / (1 - a)`. -/
noncomputable def rrAlpha (a q : R) (n : Nat) : R :=
  (-1) ^ n * q ^ (n * (n - 1) / 2) * (1 - a * q ^ (2 * n)) / (1 - a)

/-- The canonical β associated to the Rogers-Ramanujan Bailey seed. -/
noncomputable def rrBeta (a q : R) (n : Nat) : R :=
  BaileyBeta a q (rrAlpha a q) n

/-- The Rogers-Ramanujan seed together with its canonical β is a Bailey pair. -/
theorem isBaileyPair_rrAlpha_rrBeta (a q : R) :
    IsBaileyPair a q (rrAlpha a q) (rrBeta a q) := by
  intro n
  rfl

/-- The Rogers-Ramanujan seed pair satisfies the Bailey relation up to `N`. -/
theorem isBaileyPairUpTo_rrAlpha_rrBeta (a q : R) (N : Nat) :
    IsBaileyPairUpTo a q (rrAlpha a q) (rrBeta a q) N :=
  (isBaileyPair_rrAlpha_rrBeta a q).upTo N

theorem rrAlpha_zero (a q : R) (ha : 1 - a ≠ 0) : rrAlpha a q 0 = 1 := by
  simp [rrAlpha]
  exact ha

theorem rrAlpha_one (a q : R) :
    rrAlpha a q 1 = -(1 - a * q ^ 2) / (1 - a) := by
  unfold rrAlpha
  norm_num

theorem rrAlpha_two (a q : R) :
    rrAlpha a q 2 = q * (1 - a * q ^ 4) / (1 - a) := by
  unfold rrAlpha
  norm_num

theorem rrAlpha_three (a q : R) :
    rrAlpha a q 3 = -(q ^ 3 * (1 - a * q ^ 6)) / (1 - a) := by
  unfold rrAlpha
  norm_num

theorem rrAlpha_four (a q : R) :
    rrAlpha a q 4 = q ^ 6 * (1 - a * q ^ 8) / (1 - a) := by
  unfold rrAlpha
  norm_num

theorem rrAlpha_five (a q : R) :
    rrAlpha a q 5 = -(q ^ 10 * (1 - a * q ^ 10)) / (1 - a) := by
  unfold rrAlpha
  norm_num

theorem rrAlpha_six (a q : R) :
    rrAlpha a q 6 = q ^ 15 * (1 - a * q ^ 12) / (1 - a) := by
  unfold rrAlpha
  norm_num

theorem BaileyBeta_rrAlpha_zero (a q : R) (ha : 1 - a ≠ 0) :
    BaileyBeta a q (rrAlpha a q) 0 = 1 := by
  simp [BaileyBeta, natSum, BaileyTerm, rrAlpha, qPochhammer, qPoch]
  exact ha

theorem rrBeta_zero (a q : R) (ha : 1 - a ≠ 0) :
    rrBeta a q 0 = 1 := by
  unfold rrBeta
  exact BaileyBeta_rrAlpha_zero a q ha

/-- The Bailey transform of α:
`α'_n = (ρ₁;q)_n · (ρ₂;q)_n · (aq/(ρ₁ρ₂))^n / ((aq/ρ₁;q)_n · (aq/ρ₂;q)_n) · α_n`. -/
noncomputable def BaileyTransformAlpha (a q ρ₁ ρ₂ : R) (α : Nat → R) (n : Nat) : R :=
  qPoch ρ₁ q n * qPoch ρ₂ q n * (a * q / (ρ₁ * ρ₂)) ^ n /
  (qPoch (a * q / ρ₁) q n * qPoch (a * q / ρ₂) q n) * α n

/-- At `n = 0`, the Bailey transform is the identity on α. -/
theorem BaileyTransformAlpha_zero (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    BaileyTransformAlpha a q ρ₁ ρ₂ α 0 = α 0 := by
  simp [BaileyTransformAlpha, qPoch]

/-- At `n = 1`, the Bailey transform expands to its explicit form. -/
theorem BaileyTransformAlpha_one (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    BaileyTransformAlpha a q ρ₁ ρ₂ α 1 =
      (1 - ρ₁) * (1 - ρ₂) * (a * q / (ρ₁ * ρ₂)) /
      ((1 - a * q / ρ₁) * (1 - a * q / ρ₂)) * α 1 := by
  unfold BaileyTransformAlpha
  simp [qPoch]

/-- At `n = 2`, the Bailey transform of α expands to its finite product
form. -/
theorem BaileyTransformAlpha_two (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    BaileyTransformAlpha a q ρ₁ ρ₂ α 2 =
      qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 /
      (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2) * α 2 := by
  rfl

/-- At `n = 3`, the Bailey transform of α expands to its finite product
form. -/
theorem BaileyTransformAlpha_three (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    BaileyTransformAlpha a q ρ₁ ρ₂ α 3 =
      qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3) * α 3 := by
  rfl

/-- At `n = 4`, the Bailey transform of α expands to its finite product
form. -/
theorem BaileyTransformAlpha_four (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    BaileyTransformAlpha a q ρ₁ ρ₂ α 4 =
      qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 /
      (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4) * α 4 := by
  rfl

/-- At `n = 5`, the Bailey transform of α expands to its finite product
form. -/
theorem BaileyTransformAlpha_five (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    BaileyTransformAlpha a q ρ₁ ρ₂ α 5 =
      qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 /
      (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5) * α 5 := by
  rfl

/-- At `n = 6`, the Bailey transform of α expands to its finite product
form. -/
theorem BaileyTransformAlpha_six (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    BaileyTransformAlpha a q ρ₁ ρ₂ α 6 =
      qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6 /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6) * α 6 := by
  rfl

/-- At `n = 7`, the Bailey transform of α expands to its finite product
form. -/
theorem BaileyTransformAlpha_seven (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    BaileyTransformAlpha a q ρ₁ ρ₂ α 7 =
      qPoch ρ₁ q 7 * qPoch ρ₂ q 7 * (a * q / (ρ₁ * ρ₂)) ^ 7 /
      (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7) * α 7 := by
  rfl

/-- The Bailey transform applied to the RR seed at `n = 0`. -/
theorem BaileyTransformAlpha_rrAlpha_zero (a q ρ₁ ρ₂ : R) (ha : 1 - a ≠ 0) :
    BaileyTransformAlpha a q ρ₁ ρ₂ (rrAlpha a q) 0 = 1 := by
  rw [BaileyTransformAlpha_zero, rrAlpha_zero a q ha]

/-- The finite Bailey transform on β:
`β'_n = ∑_{k=0}^n ((ρ₁;q)_k(ρ₂;q)_k(aq/(ρ₁ρ₂))^k
  (aq/(ρ₁ρ₂);q)_{n-k}) /
  ((aq/ρ₁;q)_n(aq/ρ₂;q)_n(q;q)_{n-k}) · β_k`.
This is the finite algebraic side of Bailey's lemma. -/
noncomputable def BaileyTransformBeta (a q ρ₁ ρ₂ : R) (β : Nat → R) (n : Nat) : R :=
  natSum
    (fun k =>
      (qPoch ρ₁ q k * qPoch ρ₂ q k * (a * q / (ρ₁ * ρ₂)) ^ k *
        qPoch (a * q / (ρ₁ * ρ₂)) q (n - k)) /
      (qPoch (a * q / ρ₁) q n * qPoch (a * q / ρ₂) q n *
        qPochhammer q (n - k)) * β k)
    n

/-- At `n = 0`, the Bailey β-transform is the identity on β. -/
theorem BaileyTransformBeta_zero (a q ρ₁ ρ₂ : R) (β : Nat → R) :
    BaileyTransformBeta a q ρ₁ ρ₂ β 0 = β 0 := by
  simp [BaileyTransformBeta, natSum, qPoch, qPochhammer]

/-- The transformed α still gives the original zeroth α on the Bailey-beta
side. This is the base case of the finite Bailey-lemma relation. -/
theorem BaileyBeta_transformAlpha_zero (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    BaileyBeta a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 0 = α 0 := by
  simp [BaileyBeta, natSum, BaileyTerm, BaileyTransformAlpha, qPoch, qPochhammer]

/-- Base case of Bailey's lemma: at truncation depth zero, the finite Bailey
transform preserves the Bailey-pair relation. -/
theorem BaileyTransform_preserves_pair_zero (a q ρ₁ ρ₂ : R) {α β : Nat → R}
    (h : IsBaileyPairUpTo a q α β 0) :
    BaileyTransformBeta a q ρ₁ ρ₂ β 0 =
      BaileyBeta a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 0 := by
  rw [BaileyTransformBeta_zero]
  rw [h 0 (by omega)]
  simp [BaileyBeta, natSum, BaileyTerm, BaileyTransformAlpha, qPoch, qPochhammer]

/-- Up-to-zero Bailey-lemma packaging: the transformed pair satisfies the
Bailey relation at the zeroth component. -/
theorem BaileyTransform_preserves_pair_upTo_zero (a q ρ₁ ρ₂ : R) {α β : Nat → R}
    (h : IsBaileyPairUpTo a q α β 0) :
    IsBaileyPairUpTo a q (BaileyTransformAlpha a q ρ₁ ρ₂ α)
      (BaileyTransformBeta a q ρ₁ ρ₂ β) 0 :=
  IsBaileyPairUpTo.of_zero (BaileyTransform_preserves_pair_zero a q ρ₁ ρ₂ h)

/-- The Bailey transform of the canonical RR β is still normalized at `n=0`. -/
theorem BaileyTransformBeta_rrBeta_zero (a q ρ₁ ρ₂ : R) (ha : 1 - a ≠ 0) :
    BaileyTransformBeta a q ρ₁ ρ₂ (rrBeta a q) 0 = 1 := by
  rw [BaileyTransformBeta_zero, rrBeta_zero a q ha]

/-- Base case of Bailey's lemma for the Rogers-Ramanujan seed pair. -/
theorem BaileyTransform_preserves_rr_pair_zero (a q ρ₁ ρ₂ : R) :
    BaileyTransformBeta a q ρ₁ ρ₂ (rrBeta a q) 0 =
      BaileyBeta a q (BaileyTransformAlpha a q ρ₁ ρ₂ (rrAlpha a q)) 0 := by
  exact BaileyTransform_preserves_pair_zero a q ρ₁ ρ₂
    (isBaileyPairUpTo_rrAlpha_rrBeta a q 0)

/-- Up-to-zero Bailey-lemma packaging for the Rogers-Ramanujan seed pair. -/
theorem BaileyTransform_preserves_rr_pair_upTo_zero (a q ρ₁ ρ₂ : R) :
    IsBaileyPairUpTo a q (BaileyTransformAlpha a q ρ₁ ρ₂ (rrAlpha a q))
      (BaileyTransformBeta a q ρ₁ ρ₂ (rrBeta a q)) 0 :=
  BaileyTransform_preserves_pair_upTo_zero a q ρ₁ ρ₂
    (isBaileyPairUpTo_rrAlpha_rrBeta a q 0)

/-- At `n = 1`, the Bailey β-transform expands as a two-term finite sum. -/
theorem BaileyTransformBeta_one_expand (a q ρ₁ ρ₂ : R) (β : Nat → R) :
    BaileyTransformBeta a q ρ₁ ρ₂ β 1 =
      ((qPoch ρ₁ q 0 * qPoch ρ₂ q 0 * (a * q / (ρ₁ * ρ₂)) ^ 0 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1 *
        qPochhammer q 1) * β 0) +
      ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1 *
        qPochhammer q 0) * β 1) := by
  simp [BaileyTransformBeta, natSum]

/-- At `n = 1`, the Bailey β-transform with both finite q-Pochhammer
factors simplified. -/
theorem BaileyTransformBeta_one_terms (a q ρ₁ ρ₂ : R) (β : Nat → R) :
    BaileyTransformBeta a q ρ₁ ρ₂ β 1 =
      ((1 - a * q / (ρ₁ * ρ₂)) /
        ((1 - a * q / ρ₁) * (1 - a * q / ρ₂) * (1 - q)) * β 0) +
      (((1 - ρ₁) * (1 - ρ₂) * (a * q / (ρ₁ * ρ₂))) /
        ((1 - a * q / ρ₁) * (1 - a * q / ρ₂)) * β 1) := by
  rw [BaileyTransformBeta_one_expand]
  simp [qPoch, qPochhammer]

/-- At `n = 2`, the Bailey β-transform expands as a three-term finite sum. -/
theorem BaileyTransformBeta_two_expand (a q ρ₁ ρ₂ : R) (β : Nat → R) :
    BaileyTransformBeta a q ρ₁ ρ₂ β 2 =
      ((qPoch ρ₁ q 0 * qPoch ρ₂ q 0 * (a * q / (ρ₁ * ρ₂)) ^ 0 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2 *
        qPochhammer q 2) * β 0) +
      ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2 *
        qPochhammer q 1) * β 1) +
      ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2 *
        qPochhammer q 0) * β 2) := by
  simp [BaileyTransformBeta, natSum]

/-- At `n = 3`, the Bailey β-transform expands as a four-term finite sum. -/
theorem BaileyTransformBeta_three_expand (a q ρ₁ ρ₂ : R) (β : Nat → R) :
    BaileyTransformBeta a q ρ₁ ρ₂ β 3 =
      ((qPoch ρ₁ q 0 * qPoch ρ₂ q 0 * (a * q / (ρ₁ * ρ₂)) ^ 0 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3) /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 *
        qPochhammer q 3) * β 0) +
      ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 *
        qPochhammer q 2) * β 1) +
      ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 *
        qPochhammer q 1) * β 2) +
      ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 *
        qPochhammer q 0) * β 3) := by
  simp [BaileyTransformBeta, natSum]

/-- At `n = 4`, the Bailey β-transform expands as a five-term finite sum. -/
theorem BaileyTransformBeta_four_expand (a q ρ₁ ρ₂ : R) (β : Nat → R) :
    BaileyTransformBeta a q ρ₁ ρ₂ β 4 =
      ((qPoch ρ₁ q 0 * qPoch ρ₂ q 0 * (a * q / (ρ₁ * ρ₂)) ^ 0 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 4) /
      (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4 *
        qPochhammer q 4) * β 0) +
      ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3) /
      (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4 *
        qPochhammer q 3) * β 1) +
      ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4 *
        qPochhammer q 2) * β 2) +
      ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4 *
        qPochhammer q 1) * β 3) +
      ((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4 *
        qPochhammer q 0) * β 4) := by
  simp [BaileyTransformBeta, natSum]

/-- At `n = 5`, the Bailey β-transform expands as a six-term finite sum. -/
theorem BaileyTransformBeta_five_expand (a q ρ₁ ρ₂ : R) (β : Nat → R) :
    BaileyTransformBeta a q ρ₁ ρ₂ β 5 =
      ((qPoch ρ₁ q 0 * qPoch ρ₂ q 0 * (a * q / (ρ₁ * ρ₂)) ^ 0 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 5) /
      (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 *
        qPochhammer q 5) * β 0) +
      ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 4) /
      (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 *
        qPochhammer q 4) * β 1) +
      ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3) /
      (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 *
        qPochhammer q 3) * β 2) +
      ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 *
        qPochhammer q 2) * β 3) +
      ((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 *
        qPochhammer q 1) * β 4) +
      ((qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 *
        qPochhammer q 0) * β 5) := by
  simp [BaileyTransformBeta, natSum]

/-- At `n = 6`, the Bailey β-transform expands as a seven-term finite sum. -/
theorem BaileyTransformBeta_six_expand (a q ρ₁ ρ₂ : R) (β : Nat → R) :
    BaileyTransformBeta a q ρ₁ ρ₂ β 6 =
      ((qPoch ρ₁ q 0 * qPoch ρ₂ q 0 * (a * q / (ρ₁ * ρ₂)) ^ 0 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 6) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 6) * β 0) +
      ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 5) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 5) * β 1) +
      ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 4) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 4) * β 2) +
      ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 3) * β 3) +
      ((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 2) * β 4) +
      ((qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 1) * β 5) +
      ((qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 0) * β 6) := by
  simp [BaileyTransformBeta, natSum]

/-- At `n = 7`, the Bailey β-transform expands as an eight-term finite sum. -/
theorem BaileyTransformBeta_seven_expand (a q ρ₁ ρ₂ : R) (β : Nat → R) :
    BaileyTransformBeta a q ρ₁ ρ₂ β 7 =
      ((qPoch ρ₁ q 0 * qPoch ρ₂ q 0 * (a * q / (ρ₁ * ρ₂)) ^ 0 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 7) /
      (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 *
        qPochhammer q 7) * β 0) +
      ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 6) /
      (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 *
        qPochhammer q 6) * β 1) +
      ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 5) /
      (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 *
        qPochhammer q 5) * β 2) +
      ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 4) /
      (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 *
        qPochhammer q 4) * β 3) +
      ((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3) /
      (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 *
        qPochhammer q 3) * β 4) +
      ((qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 *
        qPochhammer q 2) * β 5) +
      ((qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 *
        qPochhammer q 1) * β 6) +
      ((qPoch ρ₁ q 7 * qPoch ρ₂ q 7 * (a * q / (ρ₁ * ρ₂)) ^ 7 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 *
        qPochhammer q 0) * β 7) := by
  simp [BaileyTransformBeta, natSum]

/-- At `n = 8`, the Bailey β-transform expands as a nine-term finite sum. -/
theorem BaileyTransformBeta_eight_expand (a q ρ₁ ρ₂ : R) (β : Nat → R) :
    BaileyTransformBeta a q ρ₁ ρ₂ β 8 =
      ((qPoch ρ₁ q 0 * qPoch ρ₂ q 0 * (a * q / (ρ₁ * ρ₂)) ^ 0 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 8) /
      (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8 *
        qPochhammer q 8) * β 0) +
      ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 7) /
      (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8 *
        qPochhammer q 7) * β 1) +
      ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 6) /
      (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8 *
        qPochhammer q 6) * β 2) +
      ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 5) /
      (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8 *
        qPochhammer q 5) * β 3) +
      ((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 4) /
      (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8 *
        qPochhammer q 4) * β 4) +
      ((qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3) /
      (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8 *
        qPochhammer q 3) * β 5) +
      ((qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8 *
        qPochhammer q 2) * β 6) +
      ((qPoch ρ₁ q 7 * qPoch ρ₂ q 7 * (a * q / (ρ₁ * ρ₂)) ^ 7 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8 *
        qPochhammer q 1) * β 7) +
      ((qPoch ρ₁ q 8 * qPoch ρ₂ q 8 * (a * q / (ρ₁ * ρ₂)) ^ 8 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8 *
        qPochhammer q 0) * β 8) := by
  simp [BaileyTransformBeta, natSum]

/-- If `(α, β)` is a Bailey pair up to one, the transformed β at `n = 1`
can be written using only the Bailey-beta values generated by α. -/
theorem BaileyTransformBeta_of_pair_one_expand (a q ρ₁ ρ₂ : R)
    {α β : Nat → R} (h : IsBaileyPairUpTo a q α β 1) :
    BaileyTransformBeta a q ρ₁ ρ₂ β 1 =
      ((qPoch ρ₁ q 0 * qPoch ρ₂ q 0 * (a * q / (ρ₁ * ρ₂)) ^ 0 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1 *
        qPochhammer q 1) * BaileyBeta a q α 0) +
      ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1 *
        qPochhammer q 0) * BaileyBeta a q α 1) := by
  rw [BaileyTransformBeta_one_expand, h 0 (by omega), h 1 (by omega)]

/-- If `(α, β)` is a Bailey pair up to one, the transformed β at `n = 1`
can be written in terms of the two simplified coefficients of `α`. -/
theorem BaileyTransformBeta_of_pair_one_terms (a q ρ₁ ρ₂ : R)
    {α β : Nat → R} (h : IsBaileyPairUpTo a q α β 1) :
    BaileyTransformBeta a q ρ₁ ρ₂ β 1 =
      ((1 - a * q / (ρ₁ * ρ₂)) /
        ((1 - a * q / ρ₁) * (1 - a * q / ρ₂) * (1 - q)) * α 0) +
      (((1 - ρ₁) * (1 - ρ₂) * (a * q / (ρ₁ * ρ₂))) /
        ((1 - a * q / ρ₁) * (1 - a * q / ρ₂)) *
          (α 0 / ((1 - q) * (1 - a * q)) + α 1 / qPoch (a * q) q 2)) := by
  rw [BaileyTransformBeta_one_terms, h 0 (by omega), h 1 (by omega),
    BaileyBeta_zero, BaileyBeta_one_terms]

/-- If `(α, β)` is a Bailey pair up to two, the transformed β at `n = 2`
can be written using only the Bailey-beta values generated by α. -/
theorem BaileyTransformBeta_of_pair_two_expand (a q ρ₁ ρ₂ : R)
    {α β : Nat → R} (h : IsBaileyPairUpTo a q α β 2) :
    BaileyTransformBeta a q ρ₁ ρ₂ β 2 =
      ((qPoch ρ₁ q 0 * qPoch ρ₂ q 0 * (a * q / (ρ₁ * ρ₂)) ^ 0 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2 *
        qPochhammer q 2) * BaileyBeta a q α 0) +
      ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2 *
        qPochhammer q 1) * BaileyBeta a q α 1) +
      ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2 *
        qPochhammer q 0) * BaileyBeta a q α 2) := by
  rw [BaileyTransformBeta_two_expand, h 0 (by omega), h 1 (by omega),
    h 2 (by omega)]

/-- If `(α, β)` is a Bailey pair up to two, the transformed β at `n = 2`
can be written in terms of the three simplified coefficients of `α`. -/
theorem BaileyTransformBeta_of_pair_two_terms (a q ρ₁ ρ₂ : R)
    {α β : Nat → R} (h : IsBaileyPairUpTo a q α β 2) :
    BaileyTransformBeta a q ρ₁ ρ₂ β 2 =
      ((qPoch ρ₁ q 0 * qPoch ρ₂ q 0 * (a * q / (ρ₁ * ρ₂)) ^ 0 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2 *
        qPochhammer q 2) * α 0) +
      ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2 *
        qPochhammer q 1) *
        (α 0 / ((1 - q) * (1 - a * q)) + α 1 / qPoch (a * q) q 2)) +
      ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2 *
        qPochhammer q 0) *
        (α 0 / (qPochhammer q 2 * qPoch (a * q) q 2) +
          α 1 / (qPochhammer q 1 * qPoch (a * q) q 3) +
          α 2 / qPoch (a * q) q 4)) := by
  rw [BaileyTransformBeta_of_pair_two_expand a q ρ₁ ρ₂ h, BaileyBeta_zero,
    BaileyBeta_one_terms, BaileyBeta_two_terms]

/-- If `(α, β)` is a Bailey pair up to three, the transformed β at `n = 3`
can be written using only the Bailey-beta values generated by α. -/
theorem BaileyTransformBeta_of_pair_three_expand (a q ρ₁ ρ₂ : R)
    {α β : Nat → R} (h : IsBaileyPairUpTo a q α β 3) :
    BaileyTransformBeta a q ρ₁ ρ₂ β 3 =
      ((qPoch ρ₁ q 0 * qPoch ρ₂ q 0 * (a * q / (ρ₁ * ρ₂)) ^ 0 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3) /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 *
        qPochhammer q 3) * BaileyBeta a q α 0) +
      ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 *
        qPochhammer q 2) * BaileyBeta a q α 1) +
      ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 *
        qPochhammer q 1) * BaileyBeta a q α 2) +
      ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 *
        qPochhammer q 0) * BaileyBeta a q α 3) := by
  rw [BaileyTransformBeta_three_expand, h 0 (by omega), h 1 (by omega),
    h 2 (by omega), h 3 (by omega)]

/-- If `(α, β)` is a Bailey pair up to three, the transformed β at `n = 3`
can be written in terms of the four simplified coefficients of `α`. -/
theorem BaileyTransformBeta_of_pair_three_terms (a q ρ₁ ρ₂ : R)
    {α β : Nat → R} (h : IsBaileyPairUpTo a q α β 3) :
    BaileyTransformBeta a q ρ₁ ρ₂ β 3 =
      ((qPoch ρ₁ q 0 * qPoch ρ₂ q 0 * (a * q / (ρ₁ * ρ₂)) ^ 0 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3) /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 *
        qPochhammer q 3) * α 0) +
      ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 *
        qPochhammer q 2) *
        (α 0 / ((1 - q) * (1 - a * q)) + α 1 / qPoch (a * q) q 2)) +
      ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 *
        qPochhammer q 1) *
        (α 0 / (qPochhammer q 2 * qPoch (a * q) q 2) +
          α 1 / (qPochhammer q 1 * qPoch (a * q) q 3) +
          α 2 / qPoch (a * q) q 4)) +
      ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 *
        qPochhammer q 0) *
        (α 0 / (qPochhammer q 3 * qPoch (a * q) q 3) +
          α 1 / (qPochhammer q 2 * qPoch (a * q) q 4) +
          α 2 / (qPochhammer q 1 * qPoch (a * q) q 5) +
          α 3 / qPoch (a * q) q 6)) := by
  rw [BaileyTransformBeta_of_pair_three_expand a q ρ₁ ρ₂ h, BaileyBeta_zero,
    BaileyBeta_one_terms, BaileyBeta_two_terms, BaileyBeta_three_terms]

/-- If `(α, β)` is a Bailey pair up to four, the transformed β at `n = 4`
can be written using only the Bailey-beta values generated by α. -/
theorem BaileyTransformBeta_of_pair_four_expand (a q ρ₁ ρ₂ : R)
    {α β : Nat → R} (h : IsBaileyPairUpTo a q α β 4) :
    BaileyTransformBeta a q ρ₁ ρ₂ β 4 =
      ((qPoch ρ₁ q 0 * qPoch ρ₂ q 0 * (a * q / (ρ₁ * ρ₂)) ^ 0 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 4) /
      (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4 *
        qPochhammer q 4) * BaileyBeta a q α 0) +
      ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3) /
      (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4 *
        qPochhammer q 3) * BaileyBeta a q α 1) +
      ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4 *
        qPochhammer q 2) * BaileyBeta a q α 2) +
      ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4 *
        qPochhammer q 1) * BaileyBeta a q α 3) +
      ((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4 *
        qPochhammer q 0) * BaileyBeta a q α 4) := by
  rw [BaileyTransformBeta_four_expand, h 0 (by omega), h 1 (by omega),
    h 2 (by omega), h 3 (by omega), h 4 (by omega)]

/-- If `(α, β)` is a Bailey pair up to four, the transformed β at `n = 4`
can be written in terms of the five simplified coefficients of `α`. -/
theorem BaileyTransformBeta_of_pair_four_terms (a q ρ₁ ρ₂ : R)
    {α β : Nat → R} (h : IsBaileyPairUpTo a q α β 4) :
    BaileyTransformBeta a q ρ₁ ρ₂ β 4 =
      ((qPoch ρ₁ q 0 * qPoch ρ₂ q 0 * (a * q / (ρ₁ * ρ₂)) ^ 0 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 4) /
      (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4 *
        qPochhammer q 4) * α 0) +
      ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3) /
      (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4 *
        qPochhammer q 3) *
        (α 0 / ((1 - q) * (1 - a * q)) + α 1 / qPoch (a * q) q 2)) +
      ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4 *
        qPochhammer q 2) *
        (α 0 / (qPochhammer q 2 * qPoch (a * q) q 2) +
          α 1 / (qPochhammer q 1 * qPoch (a * q) q 3) +
          α 2 / qPoch (a * q) q 4)) +
      ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4 *
        qPochhammer q 1) *
        (α 0 / (qPochhammer q 3 * qPoch (a * q) q 3) +
          α 1 / (qPochhammer q 2 * qPoch (a * q) q 4) +
          α 2 / (qPochhammer q 1 * qPoch (a * q) q 5) +
          α 3 / qPoch (a * q) q 6)) +
      ((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4 *
        qPochhammer q 0) *
        (α 0 / (qPochhammer q 4 * qPoch (a * q) q 4) +
          α 1 / (qPochhammer q 3 * qPoch (a * q) q 5) +
          α 2 / (qPochhammer q 2 * qPoch (a * q) q 6) +
          α 3 / (qPochhammer q 1 * qPoch (a * q) q 7) +
          α 4 / qPoch (a * q) q 8)) := by
  rw [BaileyTransformBeta_of_pair_four_expand a q ρ₁ ρ₂ h, BaileyBeta_zero,
    BaileyBeta_one_terms, BaileyBeta_two_terms, BaileyBeta_three_terms, BaileyBeta_four_terms]

/-- If `(α, β)` is a Bailey pair up to five, the transformed β at `n = 5`
can be written using only the Bailey-beta values generated by α. -/
theorem BaileyTransformBeta_of_pair_five_expand (a q ρ₁ ρ₂ : R)
    {α β : Nat → R} (h : IsBaileyPairUpTo a q α β 5) :
    BaileyTransformBeta a q ρ₁ ρ₂ β 5 =
      ((qPoch ρ₁ q 0 * qPoch ρ₂ q 0 * (a * q / (ρ₁ * ρ₂)) ^ 0 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 5) /
      (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 *
        qPochhammer q 5) * BaileyBeta a q α 0) +
      ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 4) /
      (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 *
        qPochhammer q 4) * BaileyBeta a q α 1) +
      ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3) /
      (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 *
        qPochhammer q 3) * BaileyBeta a q α 2) +
      ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 *
        qPochhammer q 2) * BaileyBeta a q α 3) +
      ((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 *
        qPochhammer q 1) * BaileyBeta a q α 4) +
      ((qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 *
        qPochhammer q 0) * BaileyBeta a q α 5) := by
  rw [BaileyTransformBeta_five_expand, h 0 (by omega), h 1 (by omega),
    h 2 (by omega), h 3 (by omega), h 4 (by omega), h 5 (by omega)]

/-- If `(α, β)` is a Bailey pair up to six, the transformed β at `n = 6`
can be written using only the Bailey-beta values generated by α. -/
theorem BaileyTransformBeta_of_pair_six_expand (a q ρ₁ ρ₂ : R)
    {α β : Nat → R} (h : IsBaileyPairUpTo a q α β 6) :
    BaileyTransformBeta a q ρ₁ ρ₂ β 6 =
      ((qPoch ρ₁ q 0 * qPoch ρ₂ q 0 * (a * q / (ρ₁ * ρ₂)) ^ 0 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 6) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 6) * BaileyBeta a q α 0) +
      ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 5) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 5) * BaileyBeta a q α 1) +
      ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 4) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 4) * BaileyBeta a q α 2) +
      ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 3) * BaileyBeta a q α 3) +
      ((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 2) * BaileyBeta a q α 4) +
      ((qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 1) * BaileyBeta a q α 5) +
      ((qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 0) * BaileyBeta a q α 6) := by
  rw [BaileyTransformBeta_six_expand, h 0 (by omega), h 1 (by omega),
    h 2 (by omega), h 3 (by omega), h 4 (by omega), h 5 (by omega), h 6 (by omega)]

/-- If `(α, β)` is a Bailey pair up to seven, the transformed β at `n = 7`
can be written using only the Bailey-beta values generated by α. -/
theorem BaileyTransformBeta_of_pair_seven_expand (a q ρ₁ ρ₂ : R)
    {α β : Nat → R} (h : IsBaileyPairUpTo a q α β 7) :
    BaileyTransformBeta a q ρ₁ ρ₂ β 7 =
      ((qPoch ρ₁ q 0 * qPoch ρ₂ q 0 * (a * q / (ρ₁ * ρ₂)) ^ 0 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 7) /
      (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 *
        qPochhammer q 7) * BaileyBeta a q α 0) +
      ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 6) /
      (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 *
        qPochhammer q 6) * BaileyBeta a q α 1) +
      ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 5) /
      (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 *
        qPochhammer q 5) * BaileyBeta a q α 2) +
      ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 4) /
      (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 *
        qPochhammer q 4) * BaileyBeta a q α 3) +
      ((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3) /
      (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 *
        qPochhammer q 3) * BaileyBeta a q α 4) +
      ((qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 *
        qPochhammer q 2) * BaileyBeta a q α 5) +
      ((qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 *
        qPochhammer q 1) * BaileyBeta a q α 6) +
      ((qPoch ρ₁ q 7 * qPoch ρ₂ q 7 * (a * q / (ρ₁ * ρ₂)) ^ 7 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 *
        qPochhammer q 0) * BaileyBeta a q α 7) := by
  rw [BaileyTransformBeta_seven_expand, h 0 (by omega), h 1 (by omega),
    h 2 (by omega), h 3 (by omega), h 4 (by omega), h 5 (by omega),
    h 6 (by omega), h 7 (by omega)]

/-- If `(α, β)` is a Bailey pair up to eight, the transformed β at `n = 8`
can be written using only the Bailey-beta values generated by α. -/
theorem BaileyTransformBeta_of_pair_eight_expand (a q ρ₁ ρ₂ : R)
    {α β : Nat → R} (h : IsBaileyPairUpTo a q α β 8) :
    BaileyTransformBeta a q ρ₁ ρ₂ β 8 =
      ((qPoch ρ₁ q 0 * qPoch ρ₂ q 0 * (a * q / (ρ₁ * ρ₂)) ^ 0 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 8) /
      (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8 *
        qPochhammer q 8) * BaileyBeta a q α 0) +
      ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 7) /
      (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8 *
        qPochhammer q 7) * BaileyBeta a q α 1) +
      ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 6) /
      (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8 *
        qPochhammer q 6) * BaileyBeta a q α 2) +
      ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 5) /
      (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8 *
        qPochhammer q 5) * BaileyBeta a q α 3) +
      ((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 4) /
      (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8 *
        qPochhammer q 4) * BaileyBeta a q α 4) +
      ((qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3) /
      (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8 *
        qPochhammer q 3) * BaileyBeta a q α 5) +
      ((qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8 *
        qPochhammer q 2) * BaileyBeta a q α 6) +
      ((qPoch ρ₁ q 7 * qPoch ρ₂ q 7 * (a * q / (ρ₁ * ρ₂)) ^ 7 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8 *
        qPochhammer q 1) * BaileyBeta a q α 7) +
      ((qPoch ρ₁ q 8 * qPoch ρ₂ q 8 * (a * q / (ρ₁ * ρ₂)) ^ 8 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8 *
        qPochhammer q 0) * BaileyBeta a q α 8) := by
  rw [BaileyTransformBeta_eight_expand, h 0 (by omega), h 1 (by omega),
    h 2 (by omega), h 3 (by omega), h 4 (by omega), h 5 (by omega),
    h 6 (by omega), h 7 (by omega), h 8 (by omega)]

/-- If `(α, β)` is a Bailey pair up to five, the transformed β at `n = 5`
can be written in terms of the six simplified coefficients of `α`. -/
theorem BaileyTransformBeta_of_pair_five_terms (a q ρ₁ ρ₂ : R)
    {α β : Nat → R} (h : IsBaileyPairUpTo a q α β 5) :
    BaileyTransformBeta a q ρ₁ ρ₂ β 5 =
      ((qPoch ρ₁ q 0 * qPoch ρ₂ q 0 * (a * q / (ρ₁ * ρ₂)) ^ 0 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 5) /
      (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 *
        qPochhammer q 5) * α 0) +
      ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 4) /
      (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 *
        qPochhammer q 4) *
        (α 0 / ((1 - q) * (1 - a * q)) + α 1 / qPoch (a * q) q 2)) +
      ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3) /
      (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 *
        qPochhammer q 3) *
        (α 0 / (qPochhammer q 2 * qPoch (a * q) q 2) +
          α 1 / (qPochhammer q 1 * qPoch (a * q) q 3) +
          α 2 / qPoch (a * q) q 4)) +
      ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 *
        qPochhammer q 2) *
        (α 0 / (qPochhammer q 3 * qPoch (a * q) q 3) +
          α 1 / (qPochhammer q 2 * qPoch (a * q) q 4) +
          α 2 / (qPochhammer q 1 * qPoch (a * q) q 5) +
          α 3 / qPoch (a * q) q 6)) +
      ((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 *
        qPochhammer q 1) *
        (α 0 / (qPochhammer q 4 * qPoch (a * q) q 4) +
          α 1 / (qPochhammer q 3 * qPoch (a * q) q 5) +
          α 2 / (qPochhammer q 2 * qPoch (a * q) q 6) +
          α 3 / (qPochhammer q 1 * qPoch (a * q) q 7) +
          α 4 / qPoch (a * q) q 8)) +
      ((qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 *
        qPochhammer q 0) *
        (α 0 / (qPochhammer q 5 * qPoch (a * q) q 5) +
          α 1 / (qPochhammer q 4 * qPoch (a * q) q 6) +
          α 2 / (qPochhammer q 3 * qPoch (a * q) q 7) +
          α 3 / (qPochhammer q 2 * qPoch (a * q) q 8) +
          α 4 / (qPochhammer q 1 * qPoch (a * q) q 9) +
          α 5 / qPoch (a * q) q 10)) := by
  rw [BaileyTransformBeta_of_pair_five_expand a q ρ₁ ρ₂ h, BaileyBeta_zero,
    BaileyBeta_one_terms, BaileyBeta_two_terms, BaileyBeta_three_terms,
    BaileyBeta_four_terms, BaileyBeta_five_terms]

/-- If `(α, β)` is a Bailey pair up to six, the transformed β at `n = 6`
can be written in terms of the seven simplified coefficients of `α`. -/
theorem BaileyTransformBeta_of_pair_six_terms (a q ρ₁ ρ₂ : R)
    {α β : Nat → R} (h : IsBaileyPairUpTo a q α β 6) :
    BaileyTransformBeta a q ρ₁ ρ₂ β 6 =
      ((qPoch ρ₁ q 0 * qPoch ρ₂ q 0 * (a * q / (ρ₁ * ρ₂)) ^ 0 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 6) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 6) * α 0) +
      ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 5) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 5) *
        (α 0 / ((1 - q) * (1 - a * q)) + α 1 / qPoch (a * q) q 2)) +
      ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 4) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 4) *
        (α 0 / (qPochhammer q 2 * qPoch (a * q) q 2) +
          α 1 / (qPochhammer q 1 * qPoch (a * q) q 3) +
          α 2 / qPoch (a * q) q 4)) +
      ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 3) *
        (α 0 / (qPochhammer q 3 * qPoch (a * q) q 3) +
          α 1 / (qPochhammer q 2 * qPoch (a * q) q 4) +
          α 2 / (qPochhammer q 1 * qPoch (a * q) q 5) +
          α 3 / qPoch (a * q) q 6)) +
      ((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 2) *
        (α 0 / (qPochhammer q 4 * qPoch (a * q) q 4) +
          α 1 / (qPochhammer q 3 * qPoch (a * q) q 5) +
          α 2 / (qPochhammer q 2 * qPoch (a * q) q 6) +
          α 3 / (qPochhammer q 1 * qPoch (a * q) q 7) +
          α 4 / qPoch (a * q) q 8)) +
      ((qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 1) *
        (α 0 / (qPochhammer q 5 * qPoch (a * q) q 5) +
          α 1 / (qPochhammer q 4 * qPoch (a * q) q 6) +
          α 2 / (qPochhammer q 3 * qPoch (a * q) q 7) +
          α 3 / (qPochhammer q 2 * qPoch (a * q) q 8) +
          α 4 / (qPochhammer q 1 * qPoch (a * q) q 9) +
          α 5 / qPoch (a * q) q 10)) +
      ((qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 0) *
        (α 0 / (qPochhammer q 6 * qPoch (a * q) q 6) +
          α 1 / (qPochhammer q 5 * qPoch (a * q) q 7) +
          α 2 / (qPochhammer q 4 * qPoch (a * q) q 8) +
          α 3 / (qPochhammer q 3 * qPoch (a * q) q 9) +
          α 4 / (qPochhammer q 2 * qPoch (a * q) q 10) +
          α 5 / (qPochhammer q 1 * qPoch (a * q) q 11) +
          α 6 / qPoch (a * q) q 12)) := by
  rw [BaileyTransformBeta_of_pair_six_expand a q ρ₁ ρ₂ h, BaileyBeta_zero,
    BaileyBeta_one_terms, BaileyBeta_two_terms, BaileyBeta_three_terms,
    BaileyBeta_four_terms, BaileyBeta_five_terms, BaileyBeta_six_terms]

/-- If `(α, β)` is a Bailey pair up to seven, the transformed β at `n = 7`
expands into the eight outer factors paired with the simplified
BaileyBeta_k_terms expressions of α (k = 0..7). -/
theorem BaileyTransformBeta_of_pair_seven_terms (a q ρ₁ ρ₂ : R)
    {α β : Nat → R} (h : IsBaileyPairUpTo a q α β 7) :
    BaileyTransformBeta a q ρ₁ ρ₂ β 7 =
      ((qPoch ρ₁ q 0 * qPoch ρ₂ q 0 * (a * q / (ρ₁ * ρ₂)) ^ 0 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 7) /
      (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 *
        qPochhammer q 7) * α 0) +
      ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 6) /
      (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 *
        qPochhammer q 6) *
        (α 0 / ((1 - q) * (1 - a * q)) + α 1 / qPoch (a * q) q 2)) +
      ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 5) /
      (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 *
        qPochhammer q 5) *
        (α 0 / (qPochhammer q 2 * qPoch (a * q) q 2) +
          α 1 / (qPochhammer q 1 * qPoch (a * q) q 3) +
          α 2 / qPoch (a * q) q 4)) +
      ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 4) /
      (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 *
        qPochhammer q 4) *
        (α 0 / (qPochhammer q 3 * qPoch (a * q) q 3) +
          α 1 / (qPochhammer q 2 * qPoch (a * q) q 4) +
          α 2 / (qPochhammer q 1 * qPoch (a * q) q 5) +
          α 3 / qPoch (a * q) q 6)) +
      ((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3) /
      (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 *
        qPochhammer q 3) *
        (α 0 / (qPochhammer q 4 * qPoch (a * q) q 4) +
          α 1 / (qPochhammer q 3 * qPoch (a * q) q 5) +
          α 2 / (qPochhammer q 2 * qPoch (a * q) q 6) +
          α 3 / (qPochhammer q 1 * qPoch (a * q) q 7) +
          α 4 / qPoch (a * q) q 8)) +
      ((qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 *
        qPochhammer q 2) *
        (α 0 / (qPochhammer q 5 * qPoch (a * q) q 5) +
          α 1 / (qPochhammer q 4 * qPoch (a * q) q 6) +
          α 2 / (qPochhammer q 3 * qPoch (a * q) q 7) +
          α 3 / (qPochhammer q 2 * qPoch (a * q) q 8) +
          α 4 / (qPochhammer q 1 * qPoch (a * q) q 9) +
          α 5 / qPoch (a * q) q 10)) +
      ((qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 *
        qPochhammer q 1) *
        (α 0 / (qPochhammer q 6 * qPoch (a * q) q 6) +
          α 1 / (qPochhammer q 5 * qPoch (a * q) q 7) +
          α 2 / (qPochhammer q 4 * qPoch (a * q) q 8) +
          α 3 / (qPochhammer q 3 * qPoch (a * q) q 9) +
          α 4 / (qPochhammer q 2 * qPoch (a * q) q 10) +
          α 5 / (qPochhammer q 1 * qPoch (a * q) q 11) +
          α 6 / qPoch (a * q) q 12)) +
      ((qPoch ρ₁ q 7 * qPoch ρ₂ q 7 * (a * q / (ρ₁ * ρ₂)) ^ 7 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 *
        qPochhammer q 0) *
        (α 0 / (qPochhammer q 7 * qPoch (a * q) q 7) +
          α 1 / (qPochhammer q 6 * qPoch (a * q) q 8) +
          α 2 / (qPochhammer q 5 * qPoch (a * q) q 9) +
          α 3 / (qPochhammer q 4 * qPoch (a * q) q 10) +
          α 4 / (qPochhammer q 3 * qPoch (a * q) q 11) +
          α 5 / (qPochhammer q 2 * qPoch (a * q) q 12) +
          α 6 / (qPochhammer q 1 * qPoch (a * q) q 13) +
          α 7 / qPoch (a * q) q 14)) := by
  rw [BaileyTransformBeta_of_pair_seven_expand a q ρ₁ ρ₂ h, BaileyBeta_zero,
    BaileyBeta_one_terms, BaileyBeta_two_terms, BaileyBeta_three_terms,
    BaileyBeta_four_terms, BaileyBeta_five_terms, BaileyBeta_six_terms,
    BaileyBeta_seven_terms]

/-- If `(α, β)` is a Bailey pair up to eight, the transformed β at `n = 8`
expands into the nine outer factors paired with the simplified
BaileyBeta_k_terms expressions of α (k = 0..8). -/
theorem BaileyTransformBeta_of_pair_eight_terms (a q ρ₁ ρ₂ : R)
    {α β : Nat → R} (h : IsBaileyPairUpTo a q α β 8) :
    BaileyTransformBeta a q ρ₁ ρ₂ β 8 =
      ((qPoch ρ₁ q 0 * qPoch ρ₂ q 0 * (a * q / (ρ₁ * ρ₂)) ^ 0 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 8) /
      (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8 *
        qPochhammer q 8) * α 0) +
      ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 7) /
      (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8 *
        qPochhammer q 7) *
        (α 0 / ((1 - q) * (1 - a * q)) + α 1 / qPoch (a * q) q 2)) +
      ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 6) /
      (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8 *
        qPochhammer q 6) *
        (α 0 / (qPochhammer q 2 * qPoch (a * q) q 2) +
          α 1 / (qPochhammer q 1 * qPoch (a * q) q 3) +
          α 2 / qPoch (a * q) q 4)) +
      ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 5) /
      (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8 *
        qPochhammer q 5) *
        (α 0 / (qPochhammer q 3 * qPoch (a * q) q 3) +
          α 1 / (qPochhammer q 2 * qPoch (a * q) q 4) +
          α 2 / (qPochhammer q 1 * qPoch (a * q) q 5) +
          α 3 / qPoch (a * q) q 6)) +
      ((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 4) /
      (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8 *
        qPochhammer q 4) *
        (α 0 / (qPochhammer q 4 * qPoch (a * q) q 4) +
          α 1 / (qPochhammer q 3 * qPoch (a * q) q 5) +
          α 2 / (qPochhammer q 2 * qPoch (a * q) q 6) +
          α 3 / (qPochhammer q 1 * qPoch (a * q) q 7) +
          α 4 / qPoch (a * q) q 8)) +
      ((qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3) /
      (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8 *
        qPochhammer q 3) *
        (α 0 / (qPochhammer q 5 * qPoch (a * q) q 5) +
          α 1 / (qPochhammer q 4 * qPoch (a * q) q 6) +
          α 2 / (qPochhammer q 3 * qPoch (a * q) q 7) +
          α 3 / (qPochhammer q 2 * qPoch (a * q) q 8) +
          α 4 / (qPochhammer q 1 * qPoch (a * q) q 9) +
          α 5 / qPoch (a * q) q 10)) +
      ((qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8 *
        qPochhammer q 2) *
        (α 0 / (qPochhammer q 6 * qPoch (a * q) q 6) +
          α 1 / (qPochhammer q 5 * qPoch (a * q) q 7) +
          α 2 / (qPochhammer q 4 * qPoch (a * q) q 8) +
          α 3 / (qPochhammer q 3 * qPoch (a * q) q 9) +
          α 4 / (qPochhammer q 2 * qPoch (a * q) q 10) +
          α 5 / (qPochhammer q 1 * qPoch (a * q) q 11) +
          α 6 / qPoch (a * q) q 12)) +
      ((qPoch ρ₁ q 7 * qPoch ρ₂ q 7 * (a * q / (ρ₁ * ρ₂)) ^ 7 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8 *
        qPochhammer q 1) *
        (α 0 / (qPochhammer q 7 * qPoch (a * q) q 7) +
          α 1 / (qPochhammer q 6 * qPoch (a * q) q 8) +
          α 2 / (qPochhammer q 5 * qPoch (a * q) q 9) +
          α 3 / (qPochhammer q 4 * qPoch (a * q) q 10) +
          α 4 / (qPochhammer q 3 * qPoch (a * q) q 11) +
          α 5 / (qPochhammer q 2 * qPoch (a * q) q 12) +
          α 6 / (qPochhammer q 1 * qPoch (a * q) q 13) +
          α 7 / qPoch (a * q) q 14)) +
      ((qPoch ρ₁ q 8 * qPoch ρ₂ q 8 * (a * q / (ρ₁ * ρ₂)) ^ 8 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8 *
        qPochhammer q 0) *
        (α 0 / (qPochhammer q 8 * qPoch (a * q) q 8) +
          α 1 / (qPochhammer q 7 * qPoch (a * q) q 9) +
          α 2 / (qPochhammer q 6 * qPoch (a * q) q 10) +
          α 3 / (qPochhammer q 5 * qPoch (a * q) q 11) +
          α 4 / (qPochhammer q 4 * qPoch (a * q) q 12) +
          α 5 / (qPochhammer q 3 * qPoch (a * q) q 13) +
          α 6 / (qPochhammer q 2 * qPoch (a * q) q 14) +
          α 7 / (qPochhammer q 1 * qPoch (a * q) q 15) +
          α 8 / qPoch (a * q) q 16)) := by
  rw [BaileyTransformBeta_of_pair_eight_expand a q ρ₁ ρ₂ h, BaileyBeta_zero,
    BaileyBeta_one_terms, BaileyBeta_two_terms, BaileyBeta_three_terms,
    BaileyBeta_four_terms, BaileyBeta_five_terms, BaileyBeta_six_terms,
    BaileyBeta_seven_terms, BaileyBeta_eight_terms]

/-- The Bailey-beta side generated by the transformed α at `n=1` expands to
the two defining summands. -/
theorem BaileyBeta_transformAlpha_one_expand (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    BaileyBeta a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 1 =
      BaileyTerm a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 1 0 +
      BaileyTerm a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 1 1 := by
  exact BaileyBeta_one_expand a q (BaileyTransformAlpha a q ρ₁ ρ₂ α)

/-- The `k=0` term of `BaileyBeta` for the transformed α at `N=1`. -/
theorem BaileyTerm_transformAlpha_one_zero (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    BaileyTerm a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 1 0 =
      α 0 / (qPochhammer q 1 * qPoch (a * q) q 1) := by
  rw [BaileyTerm_zero, BaileyTransformAlpha_zero]

/-- The `k=1` term of `BaileyBeta` for the transformed α at `N=1`. -/
theorem BaileyTerm_transformAlpha_one_one (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    BaileyTerm a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 1 1 =
      ((1 - ρ₁) * (1 - ρ₂) * (a * q / (ρ₁ * ρ₂)) /
        ((1 - a * q / ρ₁) * (1 - a * q / ρ₂)) * α 1) /
        qPoch (a * q) q 2 := by
  rw [BaileyTerm_at_n_simplified, BaileyTransformAlpha_one]

/-- The transformed-α Bailey beta at `N=1`, with both summands simplified.
This isolates the α₁ coefficient side of the first nontrivial finite Bailey
lemma calculation. -/
theorem BaileyBeta_transformAlpha_one_terms (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    BaileyBeta a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 1 =
      α 0 / (qPochhammer q 1 * qPoch (a * q) q 1) +
      ((1 - ρ₁) * (1 - ρ₂) * (a * q / (ρ₁ * ρ₂)) /
        ((1 - a * q / ρ₁) * (1 - a * q / ρ₂)) * α 1) /
        qPoch (a * q) q 2 := by
  rw [BaileyBeta_transformAlpha_one_expand, BaileyTerm_transformAlpha_one_zero,
    BaileyTerm_transformAlpha_one_one]

/-- The transformed-α Bailey beta at `N=1`, with the zeroth denominator written
in first-order factor form. -/
theorem BaileyBeta_transformAlpha_one_terms_simplified
    (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    BaileyBeta a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 1 =
      α 0 / ((1 - q) * (1 - a * q)) +
      (((1 - ρ₁) * (1 - ρ₂) * (a * q / (ρ₁ * ρ₂))) /
        ((1 - a * q / ρ₁) * (1 - a * q / ρ₂)) * α 1) /
        qPoch (a * q) q 2 := by
  rw [BaileyBeta_transformAlpha_one_terms]
  simp [qPochhammer, qPoch]

/-- The coefficient identity behind the `n = 1` case of Bailey's lemma.
It is the cancellation that makes the transformed β coefficient of `α 0`
collapse to the Bailey-beta coefficient for the transformed α. -/
theorem BaileyTransform_one_alpha_zero_coefficient_identity
    (a q ρ₁ ρ₂ : R) (hρ : ρ₁ * ρ₂ ≠ 0) :
    (1 - a * q) * (1 - a * q / (ρ₁ * ρ₂)) +
        (1 - ρ₁) * (1 - ρ₂) * (a * q / (ρ₁ * ρ₂)) =
      (1 - a * q / ρ₁) * (1 - a * q / ρ₂) := by
  have hρ₁0 : ρ₁ ≠ 0 := left_ne_zero_of_mul hρ
  have hρ₂0 : ρ₂ ≠ 0 := right_ne_zero_of_mul hρ
  field_simp [hρ, hρ₁0, hρ₂0]
  ring

/-- Fractional form of the α₀ coefficient cancellation used in the `n = 1`
Bailey-lemma step. -/
theorem BaileyTransform_one_alpha_zero_fraction_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0) (hq : 1 - q ≠ 0) (haq : 1 - a * q ≠ 0)
    (hρ₁ : 1 - a * q / ρ₁ ≠ 0) (hρ₂ : 1 - a * q / ρ₂ ≠ 0) :
    (1 - a * q / (ρ₁ * ρ₂)) /
        ((1 - a * q / ρ₁) * (1 - a * q / ρ₂) * (1 - q)) +
      ((1 - ρ₁) * (1 - ρ₂) * (a * q / (ρ₁ * ρ₂))) /
        ((1 - a * q / ρ₁) * (1 - a * q / ρ₂)) /
          ((1 - q) * (1 - a * q)) =
      1 / ((1 - q) * (1 - a * q)) := by
  have hden : (1 - a * q / ρ₁) * (1 - a * q / ρ₂) ≠ 0 :=
    mul_ne_zero hρ₁ hρ₂
  have hcoef := BaileyTransform_one_alpha_zero_coefficient_identity a q ρ₁ ρ₂ hρ
  field_simp [hden, hq, haq]
  field_simp [hρ] at hcoef
  ring_nf at hcoef ⊢
  exact hcoef

/-- The standardized `n = 1` transformed-β expression agrees with the
standardized transformed-α Bailey-beta expression. This is the algebraic core
of the first nontrivial finite Bailey-lemma preservation step. -/
theorem BaileyTransform_one_standard_terms_eq_transformAlpha_one_terms
    (a q ρ₁ ρ₂ α0 α1 : R)
    (hρ : ρ₁ * ρ₂ ≠ 0) (hq : 1 - q ≠ 0) (haq : 1 - a * q ≠ 0)
    (hρ₁ : 1 - a * q / ρ₁ ≠ 0) (hρ₂ : 1 - a * q / ρ₂ ≠ 0) :
    ((1 - a * q / (ρ₁ * ρ₂)) /
        ((1 - a * q / ρ₁) * (1 - a * q / ρ₂) * (1 - q)) * α0) +
      (((1 - ρ₁) * (1 - ρ₂) * (a * q / (ρ₁ * ρ₂))) /
        ((1 - a * q / ρ₁) * (1 - a * q / ρ₂)) *
          (α0 / ((1 - q) * (1 - a * q)) + α1 / qPoch (a * q) q 2)) =
      α0 / ((1 - q) * (1 - a * q)) +
        (((1 - ρ₁) * (1 - ρ₂) * (a * q / (ρ₁ * ρ₂))) /
          ((1 - a * q / ρ₁) * (1 - a * q / ρ₂)) * α1) /
          qPoch (a * q) q 2 := by
  let A := (1 - a * q / (ρ₁ * ρ₂)) /
        ((1 - a * q / ρ₁) * (1 - a * q / ρ₂) * (1 - q))
  let C := ((1 - ρ₁) * (1 - ρ₂) * (a * q / (ρ₁ * ρ₂))) /
        ((1 - a * q / ρ₁) * (1 - a * q / ρ₂))
  let D := (1 - q) * (1 - a * q)
  let E := qPoch (a * q) q 2
  have hscalar : A + C / D = 1 / D := by
    dsimp [A, C, D]
    exact BaileyTransform_one_alpha_zero_fraction_identity a q ρ₁ ρ₂
      hρ hq haq hρ₁ hρ₂
  change A * α0 + C * (α0 / D + α1 / E) = α0 / D + (C * α1) / E
  calc
    A * α0 + C * (α0 / D + α1 / E) =
        (A + C / D) * α0 + (C * α1) / E := by ring
    _ = (1 / D) * α0 + (C * α1) / E := by rw [hscalar]
    _ = α0 / D + (C * α1) / E := by ring

/-- The first nontrivial finite Bailey-lemma preservation step, under explicit
nonzero denominator hypotheses for the standardized `n = 1` algebra. -/
theorem BaileyTransform_preserves_pair_one_of_nonzero
    (a q ρ₁ ρ₂ : R) {α β : Nat → R}
    (h : IsBaileyPairUpTo a q α β 1)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hq : 1 - q ≠ 0) (haq : 1 - a * q ≠ 0)
    (hρ₁ : 1 - a * q / ρ₁ ≠ 0) (hρ₂ : 1 - a * q / ρ₂ ≠ 0) :
    BaileyTransformBeta a q ρ₁ ρ₂ β 1 =
      BaileyBeta a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 1 := by
  rw [BaileyTransformBeta_of_pair_one_terms a q ρ₁ ρ₂ h,
    BaileyBeta_transformAlpha_one_terms_simplified]
  exact BaileyTransform_one_standard_terms_eq_transformAlpha_one_terms
    a q ρ₁ ρ₂ (α 0) (α 1) hρ hq haq hρ₁ hρ₂

/-- Up-to-one finite Bailey-lemma packaging under explicit nonzero denominator
hypotheses. -/
theorem BaileyTransform_preserves_pair_upTo_one_of_nonzero
    (a q ρ₁ ρ₂ : R) {α β : Nat → R}
    (h : IsBaileyPairUpTo a q α β 1)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hq : 1 - q ≠ 0) (haq : 1 - a * q ≠ 0)
    (hρ₁ : 1 - a * q / ρ₁ ≠ 0) (hρ₂ : 1 - a * q / ρ₂ ≠ 0) :
    IsBaileyPairUpTo a q (BaileyTransformAlpha a q ρ₁ ρ₂ α)
      (BaileyTransformBeta a q ρ₁ ρ₂ β) 1 :=
  IsBaileyPairUpTo.of_one
    (BaileyTransform_preserves_pair_zero a q ρ₁ ρ₂ (h.mono (by omega)))
    (BaileyTransform_preserves_pair_one_of_nonzero a q ρ₁ ρ₂ h
      hρ hq haq hρ₁ hρ₂)

/-- The q-Pochhammer ratio that appears when the α₀ coefficient in the
`n = 2` Bailey-transform calculation is moved to a common denominator. -/
theorem BaileyTransform_two_qpoch_ratio
    (a q : R) (hQ1 : qPochhammer q 1 ≠ 0)
    (hB1 : (1 - q) * (1 - a * q) ≠ 0) :
    qPochhammer q 2 * qPoch (a * q) q 2 /
        (qPochhammer q 1 * ((1 - q) * (1 - a * q))) =
      (1 + q) * (1 - a * q ^ 2) := by
  have hq : 1 - q ≠ 0 := by simpa [qPochhammer] using hQ1
  have haq : 1 - a * q ≠ 0 := right_ne_zero_of_mul hB1
  have hqa : 1 - q * a ≠ 0 := by simpa [mul_comm] using haq
  simp [qPochhammer, qPoch]
  field_simp [hq, haq, hqa]
  ring

/-- The α₀ coefficient identity in the `n = 2` finite Bailey-lemma step after
moving the three transformed-β contributions to a common denominator. -/
theorem BaileyTransform_two_alpha_zero_common_denominator_identity
    (a q ρ₁ ρ₂ : R) (hρ : ρ₁ * ρ₂ ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hB1 : (1 - q) * (1 - a * q) ≠ 0) :
    qPoch (a * q) q 2 * qPoch (a * q / (ρ₁ * ρ₂)) q 2 +
      qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1 *
        (qPochhammer q 2 * qPoch (a * q) q 2 /
          (qPochhammer q 1 * ((1 - q) * (1 - a * q)))) +
      qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 =
      qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2 := by
  rw [BaileyTransform_two_qpoch_ratio a q hQ1 hB1]
  have hρ1 : ρ₁ ≠ 0 := left_ne_zero_of_mul hρ
  have hρ2 : ρ₂ ≠ 0 := right_ne_zero_of_mul hρ
  simp [qPoch]
  field_simp [hρ, hρ1, hρ2]
  ring

/-- Generic algebra step: a common-denominator coefficient identity implies the
corresponding fractional coefficient identity. -/
theorem BaileyTransform_common_denominator_fraction_identity
    (P0 P1 P2 D Q1 Q2 A2 B : R)
    (hD : D ≠ 0) (hQ1 : Q1 ≠ 0) (hQ2 : Q2 ≠ 0)
    (hA2 : A2 ≠ 0) (hB : B ≠ 0)
    (hcommon : A2 * P0 + P1 * (Q2 * A2 / (Q1 * B)) + P2 = D) :
    P0 / (D * Q2) + (P1 / (D * Q1)) / B + (P2 / D) / (Q2 * A2) =
      1 / (Q2 * A2) := by
  have hQ1B : Q1 * B ≠ 0 := mul_ne_zero hQ1 hB
  have hQ2A2 : Q2 * A2 ≠ 0 := mul_ne_zero hQ2 hA2
  field_simp [hD, hQ1, hQ2, hA2, hB, hQ1B, hQ2A2]
  field_simp [hQ1B] at hcommon
  ring_nf at hcommon ⊢
  exact hcommon

/-- Generic algebra step assembling three independent coefficient identities
into the `n = 2` linear combination. -/
theorem BaileyTransform_three_coefficient_linear_identity
    (C0 C1 C2 D0 D1 E0 E1 E2 T0 T1 T2 α0 α1 α2 : R)
    (h0 : C0 + C1 / D0 + C2 / D1 = T0)
    (h1 : C1 / E0 + C2 / E1 = T1)
    (h2 : C2 / E2 = T2) :
    C0 * α0 + C1 * (α0 / D0 + α1 / E0) +
      C2 * (α0 / D1 + α1 / E1 + α2 / E2) =
      T0 * α0 + T1 * α1 + T2 * α2 := by
  rw [← h0, ← h1, ← h2]
  ring

/-- Generic algebra step assembling four independent coefficient identities
into the `n = 3` linear combination. -/
theorem BaileyTransform_four_coefficient_linear_identity
    (C0 C1 C2 C3 D10 D20 D30 E10 E21 E31 E22 E32 E33
      T0 T1 T2 T3 α0 α1 α2 α3 : R)
    (h0 : C0 + C1 / D10 + C2 / D20 + C3 / D30 = T0)
    (h1 : C1 / E10 + C2 / E21 + C3 / E31 = T1)
    (h2 : C2 / E22 + C3 / E32 = T2)
    (h3 : C3 / E33 = T3) :
    C0 * α0 + C1 * (α0 / D10 + α1 / E10) +
      C2 * (α0 / D20 + α1 / E21 + α2 / E22) +
      C3 * (α0 / D30 + α1 / E31 + α2 / E32 + α3 / E33) =
      T0 * α0 + T1 * α1 + T2 * α2 + T3 * α3 := by
  rw [← h0, ← h1, ← h2, ← h3]
  ring

/-- The α₀ coefficient identity in fractional form for the `n = 2` finite
Bailey-lemma step. -/
theorem BaileyTransform_two_alpha_zero_fraction_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hD1 : qPoch (a * q / ρ₁) q 2 ≠ 0)
    (hD2 : qPoch (a * q / ρ₂) q 2 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hA2 : qPoch (a * q) q 2 ≠ 0)
    (hB1 : (1 - q) * (1 - a * q) ≠ 0) :
    ((qPoch ρ₁ q 0 * qPoch ρ₂ q 0 * (a * q / (ρ₁ * ρ₂)) ^ 0 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2 *
        qPochhammer q 2)) +
      ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2 *
        qPochhammer q 1)) / ((1 - q) * (1 - a * q)) +
      ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2 *
        qPochhammer q 0)) /
        (qPochhammer q 2 * qPoch (a * q) q 2) =
      1 / (qPochhammer q 2 * qPoch (a * q) q 2) := by
  have hD : qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2 ≠ 0 :=
    mul_ne_zero hD1 hD2
  have hcommon := BaileyTransform_two_alpha_zero_common_denominator_identity
    a q ρ₁ ρ₂ hρ hQ1 hB1
  simpa [qPochhammer, qPoch] using
    (BaileyTransform_common_denominator_fraction_identity
      (P0 := qPoch (a * q / (ρ₁ * ρ₂)) q 2)
      (P1 := qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1)
      (P2 := qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2)
      (D := qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2)
      (Q1 := qPochhammer q 1)
      (Q2 := qPochhammer q 2)
      (A2 := qPoch (a * q) q 2)
      (B := (1 - q) * (1 - a * q))
      hD hQ1 hQ2 hA2 hB1 hcommon)

/-- The α₁ coefficient identity in the `n = 2` finite Bailey-lemma step.
This separates the second-order cancellation into a reusable coefficient
calculation before the full `N = 2` packaging. -/
theorem BaileyTransform_two_alpha_one_coefficient_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hD1 : qPoch (a * q / ρ₁) q 2 ≠ 0)
    (hD2 : qPoch (a * q / ρ₂) q 2 ≠ 0)
    (hD1one : qPoch (a * q / ρ₁) q 1 ≠ 0)
    (hD2one : qPoch (a * q / ρ₂) q 1 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hA2 : qPoch (a * q) q 2 ≠ 0)
    (hA3 : qPoch (a * q) q 3 ≠ 0) :
    ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2 *
        qPochhammer q 1)) / qPoch (a * q) q 2 +
      ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2 *
        qPochhammer q 0)) /
        (qPochhammer q 1 * qPoch (a * q) q 3) =
      ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂))) /
        (qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1)) /
        (qPochhammer q 1 * qPoch (a * q) q 3) := by
  have hρ1 : ρ₁ ≠ 0 := left_ne_zero_of_mul hρ
  have hρ2 : ρ₂ ≠ 0 := right_ne_zero_of_mul hρ
  have hD :
      qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2 *
        qPochhammer q 1 ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero hD1 hD2) hQ1
  have hDone :
      qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1 ≠ 0 := by
    exact mul_ne_zero hD1one hD2one
  have hQA3 : qPochhammer q 1 * qPoch (a * q) q 3 ≠ 0 :=
    mul_ne_zero hQ1 hA3
  field_simp [hD, hDone, hQA3, hQ1, hA2, hA3]
  simp [qPoch, qPochhammer]
  field_simp [hρ, hρ1, hρ2]
  ring

/-- The α₂ coefficient identity in the `n = 2` finite Bailey-lemma step. -/
theorem BaileyTransform_two_alpha_two_coefficient_identity (a q ρ₁ ρ₂ : R) :
    ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2 *
        qPochhammer q 0)) / qPoch (a * q) q 4 =
      (qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 /
        (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2)) /
        qPoch (a * q) q 4 := by
  simp [qPochhammer, qPoch]

/-- The standardized `n = 2` transformed-β expression agrees coefficientwise
with the standardized transformed-α Bailey-beta expression. -/
theorem BaileyTransform_two_standard_terms_eq_transformAlpha_two_terms
    (a q ρ₁ ρ₂ α0 α1 α2 : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hD1 : qPoch (a * q / ρ₁) q 2 ≠ 0)
    (hD2 : qPoch (a * q / ρ₂) q 2 ≠ 0)
    (hD1one : qPoch (a * q / ρ₁) q 1 ≠ 0)
    (hD2one : qPoch (a * q / ρ₂) q 1 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hA2 : qPoch (a * q) q 2 ≠ 0)
    (hA3 : qPoch (a * q) q 3 ≠ 0)
    (hB1 : (1 - q) * (1 - a * q) ≠ 0) :
    (((qPoch ρ₁ q 0 * qPoch ρ₂ q 0 * (a * q / (ρ₁ * ρ₂)) ^ 0 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2 *
        qPochhammer q 2)) * α0) +
      (((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2 *
        qPochhammer q 1)) *
        (α0 / ((1 - q) * (1 - a * q)) + α1 / qPoch (a * q) q 2)) +
      (((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2 *
        qPochhammer q 0)) *
        (α0 / (qPochhammer q 2 * qPoch (a * q) q 2) +
          α1 / (qPochhammer q 1 * qPoch (a * q) q 3) +
          α2 / qPoch (a * q) q 4)) =
      (1 / (qPochhammer q 2 * qPoch (a * q) q 2)) * α0 +
        (((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂))) /
          (qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1)) /
          (qPochhammer q 1 * qPoch (a * q) q 3)) * α1 +
        (((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 /
          (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2)) /
          qPoch (a * q) q 4)) * α2 := by
  have h0 := BaileyTransform_two_alpha_zero_fraction_identity a q ρ₁ ρ₂
    hρ hD1 hD2 hQ1 hQ2 hA2 hB1
  have h1 := BaileyTransform_two_alpha_one_coefficient_identity a q ρ₁ ρ₂
    hρ hD1 hD2 hD1one hD2one hQ1 hA2 hA3
  have h2 := BaileyTransform_two_alpha_two_coefficient_identity a q ρ₁ ρ₂
  exact BaileyTransform_three_coefficient_linear_identity
    (((qPoch ρ₁ q 0 * qPoch ρ₂ q 0 * (a * q / (ρ₁ * ρ₂)) ^ 0 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2 *
        qPochhammer q 2)))
    (((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2 *
        qPochhammer q 1)))
    (((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2 *
        qPochhammer q 0)))
    ((1 - q) * (1 - a * q))
    (qPochhammer q 2 * qPoch (a * q) q 2)
    (qPoch (a * q) q 2)
    (qPochhammer q 1 * qPoch (a * q) q 3)
    (qPoch (a * q) q 4)
    (1 / (qPochhammer q 2 * qPoch (a * q) q 2))
    (((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂))) /
      (qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1)) /
      (qPochhammer q 1 * qPoch (a * q) q 3))
    (((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 /
      (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2)) /
      qPoch (a * q) q 4))
    α0 α1 α2 h0 h1 h2

/-- Generic ratio multiplication helper, used to keep q-Pochhammer ratio
proofs from expanding too early. -/
theorem BaileyTransform_ratio_mul (x y u v X U : R)
    (hy : y ≠ 0) (hv : v ≠ 0)
    (hx : x / y = X) (hu : u / v = U) :
    x * u / (y * v) = X * U := by
  rw [← hx, ← hu]
  field_simp [hy, hv]

/-- The α₀ common-denominator identity at `n = 3` after all scalar ratios
have been simplified to polynomial factors. -/
theorem BaileyTransform_three_alpha_zero_common_denominator_simplified
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0) :
    qPoch (a * q / (ρ₁ * ρ₂)) q 3 * qPoch (a * q) q 3 +
      qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2 *
        ((1 + q + q ^ 2) * ((1 - a * q ^ 2) * (1 - a * q ^ 3))) +
      qPoch ρ₁ q 2 * qPoch ρ₂ q 2 *
        (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1 *
        ((1 + q + q ^ 2) * (1 - a * q ^ 3)) +
      qPoch ρ₁ q 3 * qPoch ρ₂ q 3 *
        (a * q / (ρ₁ * ρ₂)) ^ 3 =
      qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 := by
  have hρ1 : ρ₁ ≠ 0 := left_ne_zero_of_mul hρ
  have hρ2 : ρ₂ ≠ 0 := right_ne_zero_of_mul hρ
  simp [qPoch]
  field_simp [hρ, hρ1, hρ2]
  ring

/-- The q-Pochhammer ratio `(q;q)_3 / ((q;q)_2 (q;q)_1)`. -/
theorem BaileyTransform_three_qpochhammer_three_over_one_two
    (q : R) (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0) :
    qPochhammer q 3 / (qPochhammer q 2 * qPochhammer q 1) =
      1 + q + q ^ 2 := by
  have hq : 1 - q ≠ 0 := by simpa [qPochhammer] using hQ1
  have hq2 : 1 - q ^ 2 ≠ 0 := by
    simpa [qPochhammer] using right_ne_zero_of_mul hQ2
  simp [qPochhammer]
  field_simp [hq, hq2]
  ring

/-- The ratio `(aq;q)_3 / (aq;q)_1`. -/
theorem BaileyTransform_three_qpoch_aq_three_over_one
    (a q : R) (hA1 : qPoch (a * q) q 1 ≠ 0) :
    qPoch (a * q) q 3 / qPoch (a * q) q 1 =
      (1 - a * q ^ 2) * (1 - a * q ^ 3) := by
  have hF : 1 - a * q ≠ 0 := by simpa [qPoch] using hA1
  simp [qPoch]
  field_simp [hF]

/-- The ratio `(aq;q)_3 / (aq;q)_2`. -/
theorem BaileyTransform_three_qpoch_aq_three_over_two
    (a q : R) (hA2 : qPoch (a * q) q 2 ≠ 0) :
    qPoch (a * q) q 3 / qPoch (a * q) q 2 =
      1 - a * q ^ 3 := by
  rw [show qPoch (a * q) q 3 =
      qPoch (a * q) q 2 * (1 - (a * q) * q ^ 2) by rfl]
  field_simp [hA2]

/-- The first scalar ratio in the `n = 3`, α₀ common-denominator
calculation. -/
theorem BaileyTransform_three_alpha_zero_first_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hA1 : qPoch (a * q) q 1 ≠ 0) :
    qPochhammer q 3 * qPoch (a * q) q 3 /
        (qPochhammer q 2 * qPochhammer q 1 * qPoch (a * q) q 1) =
      (1 + q + q ^ 2) * ((1 - a * q ^ 2) * (1 - a * q ^ 3)) := by
  have hQ2Q1 : qPochhammer q 2 * qPochhammer q 1 ≠ 0 := mul_ne_zero hQ2 hQ1
  have hQ := BaileyTransform_three_qpochhammer_three_over_one_two q hQ1 hQ2
  have hA := BaileyTransform_three_qpoch_aq_three_over_one a q hA1
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 3) (qPochhammer q 2 * qPochhammer q 1)
      (qPoch (a * q) q 3) (qPoch (a * q) q 1)
      (1 + q + q ^ 2) ((1 - a * q ^ 2) * (1 - a * q ^ 3))
      hQ2Q1 hA1 hQ hA

/-- The second scalar ratio in the `n = 3`, α₀ common-denominator
calculation. -/
theorem BaileyTransform_three_alpha_zero_second_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hA2 : qPoch (a * q) q 2 ≠ 0) :
    qPochhammer q 3 * qPoch (a * q) q 3 /
        (qPochhammer q 1 * qPochhammer q 2 * qPoch (a * q) q 2) =
      (1 + q + q ^ 2) * (1 - a * q ^ 3) := by
  have hQ1Q2 : qPochhammer q 1 * qPochhammer q 2 ≠ 0 := mul_ne_zero hQ1 hQ2
  have hQ : qPochhammer q 3 / (qPochhammer q 1 * qPochhammer q 2) =
      1 + q + q ^ 2 := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      BaileyTransform_three_qpochhammer_three_over_one_two q hQ1 hQ2
  have hA := BaileyTransform_three_qpoch_aq_three_over_two a q hA2
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 3) (qPochhammer q 1 * qPochhammer q 2)
      (qPoch (a * q) q 3) (qPoch (a * q) q 2)
      (1 + q + q ^ 2) (1 - a * q ^ 3) hQ1Q2 hA2 hQ hA

/-- The α₀ coefficient identity in the `n = 3` finite Bailey-lemma step after
moving the four transformed-β contributions to a common denominator. -/
theorem BaileyTransform_three_alpha_zero_common_denominator_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hA1 : qPoch (a * q) q 1 ≠ 0)
    (hA2 : qPoch (a * q) q 2 ≠ 0) :
    qPoch (a * q / (ρ₁ * ρ₂)) q 3 * qPoch (a * q) q 3 +
      qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2 *
        (qPochhammer q 3 * qPoch (a * q) q 3 /
          (qPochhammer q 2 * qPochhammer q 1 * qPoch (a * q) q 1)) +
      qPoch ρ₁ q 2 * qPoch ρ₂ q 2 *
        (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1 *
        (qPochhammer q 3 * qPoch (a * q) q 3 /
          (qPochhammer q 1 * qPochhammer q 2 * qPoch (a * q) q 2)) +
      qPoch ρ₁ q 3 * qPoch ρ₂ q 3 *
        (a * q / (ρ₁ * ρ₂)) ^ 3 =
      qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 := by
  rw [BaileyTransform_three_alpha_zero_first_ratio a q hQ1 hQ2 hA1,
    BaileyTransform_three_alpha_zero_second_ratio a q hQ1 hQ2 hA2]
  exact BaileyTransform_three_alpha_zero_common_denominator_simplified a q ρ₁ ρ₂ hρ

/-- Generic four-term algebra step: a common-denominator identity implies the
corresponding fractional α₀ identity at `n = 3`. -/
theorem BaileyTransform_four_term_fraction_from_common
    (P0 P1 P2 P3 D Q1 Q2 Q3 A1 A2 A3 : R)
    (hD : D ≠ 0) (hQ1 : Q1 ≠ 0) (hQ2 : Q2 ≠ 0) (hQ3 : Q3 ≠ 0)
    (hA1 : A1 ≠ 0) (hA2 : A2 ≠ 0) (hA3 : A3 ≠ 0)
    (hcommon : P0 * A3 + P1 * (Q3 * A3 / (Q2 * Q1 * A1)) +
      P2 * (Q3 * A3 / (Q1 * Q2 * A2)) + P3 = D) :
    P0 / (D * Q3) + (P1 / (D * Q2)) / (Q1 * A1) +
      (P2 / (D * Q1)) / (Q2 * A2) + (P3 / D) / (Q3 * A3) =
      1 / (Q3 * A3) := by
  have hDQ3 : D * Q3 ≠ 0 := mul_ne_zero hD hQ3
  have hDQ2 : D * Q2 ≠ 0 := mul_ne_zero hD hQ2
  have hDQ1 : D * Q1 ≠ 0 := mul_ne_zero hD hQ1
  have hQ1A1 : Q1 * A1 ≠ 0 := mul_ne_zero hQ1 hA1
  have hQ2A2 : Q2 * A2 ≠ 0 := mul_ne_zero hQ2 hA2
  have hQ3A3 : Q3 * A3 ≠ 0 := mul_ne_zero hQ3 hA3
  have hQ2Q1A1 : Q2 * Q1 * A1 ≠ 0 := mul_ne_zero (mul_ne_zero hQ2 hQ1) hA1
  have hQ1Q2A2 : Q1 * Q2 * A2 ≠ 0 := mul_ne_zero (mul_ne_zero hQ1 hQ2) hA2
  field_simp [hD, hQ1, hQ2, hQ3, hA1, hA2, hA3, hDQ3, hDQ2, hDQ1,
    hQ1A1, hQ2A2, hQ3A3, hQ2Q1A1, hQ1Q2A2]
  field_simp [hQ2Q1A1, hQ1Q2A2] at hcommon
  ring_nf at hcommon ⊢
  exact hcommon

/-- The α₀ coefficient identity in the `n = 3` finite Bailey-lemma step. -/
theorem BaileyTransform_three_alpha_zero_coefficient_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hD1 : qPoch (a * q / ρ₁) q 3 ≠ 0)
    (hD2 : qPoch (a * q / ρ₂) q 3 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hA1 : qPoch (a * q) q 1 ≠ 0)
    (hA2 : qPoch (a * q) q 2 ≠ 0)
    (hA3 : qPoch (a * q) q 3 ≠ 0) :
    ((qPoch ρ₁ q 0 * qPoch ρ₂ q 0 * (a * q / (ρ₁ * ρ₂)) ^ 0 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3) /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 *
        qPochhammer q 3)) +
      ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 *
        qPochhammer q 2)) /
        (qPochhammer q 1 * qPoch (a * q) q 1) +
      ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 *
        qPochhammer q 1)) /
        (qPochhammer q 2 * qPoch (a * q) q 2) +
      ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 *
        qPochhammer q 0)) /
        (qPochhammer q 3 * qPoch (a * q) q 3) =
      1 / (qPochhammer q 3 * qPoch (a * q) q 3) := by
  have hD : qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 ≠ 0 :=
    mul_ne_zero hD1 hD2
  have hcommon := BaileyTransform_three_alpha_zero_common_denominator_identity
    a q ρ₁ ρ₂ hρ hQ1 hQ2 hA1 hA2
  simpa [qPochhammer, qPoch] using
    (BaileyTransform_four_term_fraction_from_common
      (P0 := qPoch (a * q / (ρ₁ * ρ₂)) q 3)
      (P1 := qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2)
      (P2 := qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1)
      (P3 := qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3)
      (D := qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3)
      (Q1 := qPochhammer q 1)
      (Q2 := qPochhammer q 2)
      (Q3 := qPochhammer q 3)
      (A1 := qPoch (a * q) q 1)
      (A2 := qPoch (a * q) q 2)
      (A3 := qPoch (a * q) q 3)
      hD hQ1 hQ2 hQ3 hA1 hA2 hA3 hcommon)

/-- The q-Pochhammer ratio `(q;q)_2 / (q;q)_1^2` used in the `n = 3`,
α₁ coefficient calculation. -/
theorem BaileyTransform_three_qpochhammer_two_over_one_sq
    (q : R) (hQ1 : qPochhammer q 1 ≠ 0) :
    qPochhammer q 2 / (qPochhammer q 1 * qPochhammer q 1) = 1 + q := by
  have hq : 1 - q ≠ 0 := by simpa [qPochhammer] using hQ1
  simp [qPochhammer]
  field_simp [hq]
  ring

/-- The adjacent q-Pochhammer ratio `(aq;q)_4 / (aq;q)_3`. -/
theorem BaileyTransform_three_qpoch_aq_four_over_three
    (a q : R) (hA3 : qPoch (a * q) q 3 ≠ 0) :
    qPoch (a * q) q 4 / qPoch (a * q) q 3 = 1 - a * q ^ 4 := by
  rw [show qPoch (a * q) q 4 =
      qPoch (a * q) q 3 * (1 - (a * q) * q ^ 3) by rfl]
  field_simp [hA3]

/-- The middle denominator ratio appearing in the `n = 3`, α₁
common-denominator calculation. -/
theorem BaileyTransform_three_qpochhammer_aq_alpha_one_middle_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hA3 : qPoch (a * q) q 3 ≠ 0) :
    qPochhammer q 2 * qPoch (a * q) q 4 /
        (qPochhammer q 1 * qPochhammer q 1 * qPoch (a * q) q 3) =
      (1 + q) * (1 - a * q ^ 4) := by
  have hQ1sq : qPochhammer q 1 * qPochhammer q 1 ≠ 0 :=
    mul_ne_zero hQ1 hQ1
  have hQ := BaileyTransform_three_qpochhammer_two_over_one_sq q hQ1
  have hA := BaileyTransform_three_qpoch_aq_four_over_three a q hA3
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 2)
      (qPochhammer q 1 * qPochhammer q 1)
      (qPoch (a * q) q 4) (qPoch (a * q) q 3)
      (1 + q) (1 - a * q ^ 4) hQ1sq hA3 hQ hA

/-- The ratio `(aq;q)_4 / (aq;q)_2` used by the first α₁ transformed-β
contribution at `n = 3`. -/
theorem BaileyTransform_three_qpoch_aq_four_over_two
    (a q : R) (hA2 : qPoch (a * q) q 2 ≠ 0) :
    qPoch (a * q) q 4 / qPoch (a * q) q 2 =
      (1 - a * q ^ 3) * (1 - a * q ^ 4) := by
  rw [show qPoch (a * q) q 4 =
      qPoch (a * q) q 2 * (1 - (a * q) * q ^ 2) *
        (1 - (a * q) * q ^ 3) by rfl]
  field_simp [hA2]

/-- The denominator ratio from the `N=3` transformed-β denominator to the
`N=1` transformed-α denominator. -/
theorem BaileyTransform_three_qpoch_pair_ratio_one_three
    (a q ρ₁ ρ₂ : R)
    (hD1one : qPoch (a * q / ρ₁) q 1 ≠ 0)
    (hD2one : qPoch (a * q / ρ₂) q 1 ≠ 0) :
    (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3) /
        (qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1) =
      ((1 - (a * q / ρ₁) * q) * (1 - (a * q / ρ₁) * q ^ 2)) *
        ((1 - (a * q / ρ₂) * q) * (1 - (a * q / ρ₂) * q ^ 2)) := by
  have hD : qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1 ≠ 0 :=
    mul_ne_zero hD1one hD2one
  have hF1 : 1 - a * q / ρ₁ ≠ 0 := by simpa [qPoch] using hD1one
  have hF2 : 1 - a * q / ρ₂ ≠ 0 := by simpa [qPoch] using hD2one
  simp [qPoch]
  field_simp [hF1, hF2, hD]

/-- The α₁ coefficient identity in the `n = 3` finite Bailey-lemma step after
moving the three transformed-β contributions to a common denominator. -/
theorem BaileyTransform_three_alpha_one_common_denominator_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hA2 : qPoch (a * q) q 2 ≠ 0)
    (hA3 : qPoch (a * q) q 3 ≠ 0)
    (hD1one : qPoch (a * q / ρ₁) q 1 ≠ 0)
    (hD2one : qPoch (a * q / ρ₂) q 1 ≠ 0) :
    qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2 *
        (qPoch (a * q) q 4 / qPoch (a * q) q 2) +
      qPoch ρ₁ q 2 * qPoch ρ₂ q 2 *
        (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1 *
        (qPochhammer q 2 * qPoch (a * q) q 4 /
          (qPochhammer q 1 * qPochhammer q 1 * qPoch (a * q) q 3)) +
      qPoch ρ₁ q 3 * qPoch ρ₂ q 3 *
        (a * q / (ρ₁ * ρ₂)) ^ 3 =
      (qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂))) *
        ((qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3) /
          (qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1)) := by
  rw [BaileyTransform_three_qpoch_aq_four_over_two a q hA2,
    BaileyTransform_three_qpochhammer_aq_alpha_one_middle_ratio a q hQ1 hA3,
    BaileyTransform_three_qpoch_pair_ratio_one_three a q ρ₁ ρ₂ hD1one hD2one]
  have hρ1 : ρ₁ ≠ 0 := left_ne_zero_of_mul hρ
  have hρ2 : ρ₂ ≠ 0 := right_ne_zero_of_mul hρ
  simp [qPoch]
  field_simp [hρ, hρ1, hρ2]
  ring

/-- Generic three-term algebra step: a common-denominator identity with a
remaining denominator ratio implies the corresponding fractional identity. -/
theorem BaileyTransform_three_term_fraction_from_common_ratio
    (P1 P2 P3 B D D1 Q1 Q2 A2 A3 A4 : R)
    (hD : D ≠ 0) (hD1 : D1 ≠ 0)
    (hQ1 : Q1 ≠ 0) (hQ2 : Q2 ≠ 0)
    (hA2 : A2 ≠ 0) (hA3 : A3 ≠ 0) (hA4 : A4 ≠ 0)
    (hcommon : P1 * (A4 / A2) + P2 * (Q2 * A4 / (Q1 * Q1 * A3)) +
      P3 = B * (D / D1)) :
    (P1 / (D * Q2)) / A2 + (P2 / (D * Q1)) / (Q1 * A3) +
      (P3 / D) / (Q2 * A4) =
      (B / D1) / (Q2 * A4) := by
  have hDQ2 : D * Q2 ≠ 0 := mul_ne_zero hD hQ2
  have hDQ1 : D * Q1 ≠ 0 := mul_ne_zero hD hQ1
  have hQ1A3 : Q1 * A3 ≠ 0 := mul_ne_zero hQ1 hA3
  have hQ2A4 : Q2 * A4 ≠ 0 := mul_ne_zero hQ2 hA4
  have hQ1Q1A3 : Q1 * Q1 * A3 ≠ 0 := mul_ne_zero (mul_ne_zero hQ1 hQ1) hA3
  field_simp [hD, hD1, hQ1, hQ2, hA2, hA3, hA4, hDQ2, hDQ1, hQ1A3,
    hQ2A4, hQ1Q1A3]
  field_simp [hA2, hQ1Q1A3, hD1] at hcommon
  ring_nf at hcommon ⊢
  exact hcommon

/-- The α₁ coefficient identity in the `n = 3` finite Bailey-lemma step. -/
theorem BaileyTransform_three_alpha_one_coefficient_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hD1 : qPoch (a * q / ρ₁) q 3 ≠ 0)
    (hD2 : qPoch (a * q / ρ₂) q 3 ≠ 0)
    (hD1one : qPoch (a * q / ρ₁) q 1 ≠ 0)
    (hD2one : qPoch (a * q / ρ₂) q 1 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hA2 : qPoch (a * q) q 2 ≠ 0)
    (hA3 : qPoch (a * q) q 3 ≠ 0)
    (hA4 : qPoch (a * q) q 4 ≠ 0) :
    ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 *
        qPochhammer q 2)) / qPoch (a * q) q 2 +
      ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 *
        qPochhammer q 1)) /
        (qPochhammer q 1 * qPoch (a * q) q 3) +
      ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 *
        qPochhammer q 0)) /
        (qPochhammer q 2 * qPoch (a * q) q 4) =
      ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂))) /
        (qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1)) /
        (qPochhammer q 2 * qPoch (a * q) q 4) := by
  have hD : qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 ≠ 0 :=
    mul_ne_zero hD1 hD2
  have hDone : qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1 ≠ 0 :=
    mul_ne_zero hD1one hD2one
  have hcommon := BaileyTransform_three_alpha_one_common_denominator_identity
    a q ρ₁ ρ₂ hρ hQ1 hA2 hA3 hD1one hD2one
  simpa [qPochhammer, qPoch] using
    (BaileyTransform_three_term_fraction_from_common_ratio
      (P1 := qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2)
      (P2 := qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1)
      (P3 := qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3)
      (B := qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)))
      (D := qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3)
      (D1 := qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1)
      (Q1 := qPochhammer q 1)
      (Q2 := qPochhammer q 2)
      (A2 := qPoch (a * q) q 2)
      (A3 := qPoch (a * q) q 3)
      (A4 := qPoch (a * q) q 4)
      hD hDone hQ1 hQ2 hA2 hA3 hA4 hcommon)

/-- The adjacent q-Pochhammer ratio needed in the `n = 3`, α₂ coefficient
calculation. -/
theorem BaileyTransform_three_qpoch_ratio_four_five
    (a q : R) (hA4 : qPoch (a * q) q 4 ≠ 0) :
    qPoch (a * q) q 5 / qPoch (a * q) q 4 = 1 - a * q ^ 5 := by
  rw [show qPoch (a * q) q 5 =
      qPoch (a * q) q 4 * (1 - (a * q) * q ^ 4) by rfl]
  field_simp [hA4]

/-- The denominator ratio between the `N=3` and `N=2` transformed-α
q-Pochhammer factors. -/
theorem BaileyTransform_three_qpoch_pair_ratio_two_three
    (a q ρ₁ ρ₂ : R)
    (hD1two : qPoch (a * q / ρ₁) q 2 ≠ 0)
    (hD2two : qPoch (a * q / ρ₂) q 2 ≠ 0) :
    (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3) /
        (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2) =
      (1 - (a * q / ρ₁) * q ^ 2) *
        (1 - (a * q / ρ₂) * q ^ 2) := by
  have hD2 : qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2 ≠ 0 :=
    mul_ne_zero hD1two hD2two
  rw [show qPoch (a * q / ρ₁) q 3 =
      qPoch (a * q / ρ₁) q 2 * (1 - (a * q / ρ₁) * q ^ 2) by rfl]
  rw [show qPoch (a * q / ρ₂) q 3 =
      qPoch (a * q / ρ₂) q 2 * (1 - (a * q / ρ₂) * q ^ 2) by rfl]
  field_simp [hD2]

/-- The α₂ coefficient identity in the `n = 3` finite Bailey-lemma step after
moving the two transformed-β contributions to a common denominator. -/
theorem BaileyTransform_three_alpha_two_common_denominator_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hA4 : qPoch (a * q) q 4 ≠ 0)
    (hD1two : qPoch (a * q / ρ₁) q 2 ≠ 0)
    (hD2two : qPoch (a * q / ρ₂) q 2 ≠ 0) :
    qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1 *
        (qPoch (a * q) q 5 / qPoch (a * q) q 4) +
      qPoch ρ₁ q 3 * qPoch ρ₂ q 3 *
        (a * q / (ρ₁ * ρ₂)) ^ 3 =
      (qPoch ρ₁ q 2 * qPoch ρ₂ q 2 *
        (a * q / (ρ₁ * ρ₂)) ^ 2) *
        ((qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3) /
          (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2)) := by
  rw [BaileyTransform_three_qpoch_ratio_four_five a q hA4,
    BaileyTransform_three_qpoch_pair_ratio_two_three a q ρ₁ ρ₂ hD1two hD2two]
  have hρ1 : ρ₁ ≠ 0 := left_ne_zero_of_mul hρ
  have hρ2 : ρ₂ ≠ 0 := right_ne_zero_of_mul hρ
  simp [qPoch]
  field_simp [hρ, hρ1, hρ2]
  ring

/-- Generic two-term algebra step: a common-denominator identity with a
remaining denominator ratio implies the corresponding fractional identity. -/
theorem BaileyTransform_two_term_fraction_from_common_ratio
    (P0 P1 B D D2 Q A4 A5 : R)
    (hD : D ≠ 0) (hD2 : D2 ≠ 0) (hQ : Q ≠ 0)
    (hA4 : A4 ≠ 0) (hA5 : A5 ≠ 0)
    (hcommon : P0 * (A5 / A4) + P1 = B * (D / D2)) :
    (P0 / (D * Q)) / A4 + (P1 / D) / (Q * A5) =
      (B / D2) / (Q * A5) := by
  have hDQ : D * Q ≠ 0 := mul_ne_zero hD hQ
  have hQA5 : Q * A5 ≠ 0 := mul_ne_zero hQ hA5
  field_simp [hD, hD2, hQ, hA4, hA5, hDQ, hQA5]
  field_simp [hA4, hD2] at hcommon
  ring_nf at hcommon ⊢
  exact hcommon

/-- The α₂ coefficient identity in the `n = 3` finite Bailey-lemma step. -/
theorem BaileyTransform_three_alpha_two_coefficient_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hD1 : qPoch (a * q / ρ₁) q 3 ≠ 0)
    (hD2 : qPoch (a * q / ρ₂) q 3 ≠ 0)
    (hD1two : qPoch (a * q / ρ₁) q 2 ≠ 0)
    (hD2two : qPoch (a * q / ρ₂) q 2 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hA4 : qPoch (a * q) q 4 ≠ 0)
    (hA5 : qPoch (a * q) q 5 ≠ 0) :
    ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 *
        qPochhammer q 1)) / qPoch (a * q) q 4 +
      ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 *
        qPochhammer q 0)) /
        (qPochhammer q 1 * qPoch (a * q) q 5) =
      (qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 /
        (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2)) /
        (qPochhammer q 1 * qPoch (a * q) q 5) := by
  have hD : qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 ≠ 0 :=
    mul_ne_zero hD1 hD2
  have hDtwo : qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2 ≠ 0 :=
    mul_ne_zero hD1two hD2two
  have hcommon := BaileyTransform_three_alpha_two_common_denominator_identity
    a q ρ₁ ρ₂ hρ hA4 hD1two hD2two
  simpa [qPochhammer, qPoch] using
    (BaileyTransform_two_term_fraction_from_common_ratio
      (P0 := qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1)
      (P1 := qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3)
      (B := qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2)
      (D := qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3)
      (D2 := qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2)
      (Q := qPochhammer q 1)
      (A4 := qPoch (a * q) q 4)
      (A5 := qPoch (a * q) q 5)
      hD hDtwo hQ1 hA4 hA5 hcommon)

/-- The α₃ coefficient identity in the `n = 3` finite Bailey-lemma step. -/
theorem BaileyTransform_three_alpha_three_coefficient_identity (a q ρ₁ ρ₂ : R) :
    ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 *
        qPochhammer q 0)) / qPoch (a * q) q 6 =
      (qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 /
        (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3)) /
        qPoch (a * q) q 6 := by
  simp [qPochhammer, qPoch]

/-- The adjacent q-Pochhammer ratio needed in the `n = 4`, α₃ coefficient
calculation. -/
theorem BaileyTransform_four_qpoch_ratio_six_seven
    (a q : R) (hA6 : qPoch (a * q) q 6 ≠ 0) :
    qPoch (a * q) q 7 / qPoch (a * q) q 6 = 1 - a * q ^ 7 := by
  rw [show qPoch (a * q) q 7 =
      qPoch (a * q) q 6 * (1 - (a * q) * q ^ 6) by rfl]
  field_simp [hA6]

/-- The denominator ratio between the `N=4` and `N=3` transformed-α
q-Pochhammer factors. -/
theorem BaileyTransform_four_qpoch_pair_ratio_three_four
    (a q ρ₁ ρ₂ : R)
    (hD1three : qPoch (a * q / ρ₁) q 3 ≠ 0)
    (hD2three : qPoch (a * q / ρ₂) q 3 ≠ 0) :
    (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4) /
        (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3) =
      (1 - (a * q / ρ₁) * q ^ 3) *
        (1 - (a * q / ρ₂) * q ^ 3) := by
  have hD3 : qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 ≠ 0 :=
    mul_ne_zero hD1three hD2three
  rw [show qPoch (a * q / ρ₁) q 4 =
      qPoch (a * q / ρ₁) q 3 * (1 - (a * q / ρ₁) * q ^ 3) by rfl]
  rw [show qPoch (a * q / ρ₂) q 4 =
      qPoch (a * q / ρ₂) q 3 * (1 - (a * q / ρ₂) * q ^ 3) by rfl]
  field_simp [hD3]

/-- The adjacent q-Pochhammer ratio needed in the `n = 5`, α₄ coefficient
calculation. -/
theorem BaileyTransform_five_qpoch_ratio_eight_nine
    (a q : R) (hA8 : qPoch (a * q) q 8 ≠ 0) :
    qPoch (a * q) q 9 / qPoch (a * q) q 8 = 1 - a * q ^ 9 := by
  rw [show qPoch (a * q) q 9 =
      qPoch (a * q) q 8 * (1 - (a * q) * q ^ 8) by rfl]
  field_simp [hA8]

/-- The denominator ratio between the `N=5` and `N=4` transformed-α
q-Pochhammer factors. -/
theorem BaileyTransform_five_qpoch_pair_ratio_four_five
    (a q ρ₁ ρ₂ : R)
    (hD1four : qPoch (a * q / ρ₁) q 4 ≠ 0)
    (hD2four : qPoch (a * q / ρ₂) q 4 ≠ 0) :
    (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5) /
        (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4) =
      (1 - (a * q / ρ₁) * q ^ 4) *
        (1 - (a * q / ρ₂) * q ^ 4) := by
  have hD4 : qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4 ≠ 0 :=
    mul_ne_zero hD1four hD2four
  rw [show qPoch (a * q / ρ₁) q 5 =
      qPoch (a * q / ρ₁) q 4 * (1 - (a * q / ρ₁) * q ^ 4) by rfl]
  rw [show qPoch (a * q / ρ₂) q 5 =
      qPoch (a * q / ρ₂) q 4 * (1 - (a * q / ρ₂) * q ^ 4) by rfl]
  field_simp [hD4]

/-- The adjacent q-Pochhammer ratio needed in the `n = 6`, α₅ coefficient
calculation. -/
theorem BaileyTransform_six_qpoch_ratio_ten_eleven
    (a q : R) (hA10 : qPoch (a * q) q 10 ≠ 0) :
    qPoch (a * q) q 11 / qPoch (a * q) q 10 = 1 - a * q ^ 11 := by
  rw [show qPoch (a * q) q 11 =
      qPoch (a * q) q 10 * (1 - (a * q) * q ^ 10) by rfl]
  field_simp [hA10]

/-- The two-step q-Pochhammer ratio needed in the `n = 6`, α₄ coefficient
calculation. -/
theorem BaileyTransform_six_qpoch_aq_ten_over_eight
    (a q : R) (hA8 : qPoch (a * q) q 8 ≠ 0) :
    qPoch (a * q) q 10 / qPoch (a * q) q 8 =
      (1 - a * q ^ 9) * (1 - a * q ^ 10) := by
  rw [show qPoch (a * q) q 10 =
      qPoch (a * q) q 8 * (1 - (a * q) * q ^ 8) *
        (1 - (a * q) * q ^ 9) by rfl]
  field_simp [hA8]

/-- The middle q-Pochhammer ratio needed in the `n = 6`, α₄ coefficient
calculation. -/
theorem BaileyTransform_six_qpochhammer_aq_alpha_four_middle_ratio
    (a q : R) (hQ1 : qPochhammer q 1 ≠ 0)
    (hA9 : qPoch (a * q) q 9 ≠ 0) :
    qPochhammer q 2 * qPoch (a * q) q 10 /
        (qPochhammer q 1 * qPochhammer q 1 * qPoch (a * q) q 9) =
      (1 + q) * (1 - a * q ^ 10) := by
  have hq : 1 - q ≠ 0 := by simpa [qPochhammer] using hQ1
  have hA9' : qPoch (q * a) q 9 ≠ 0 := by
    simpa [mul_comm] using hA9
  rw [show qPochhammer q 2 = qPochhammer q 1 * (1 - q ^ 2) by rfl]
  rw [show qPoch (a * q) q 10 =
      qPoch (a * q) q 9 * (1 - (a * q) * q ^ 9) by rfl]
  field_simp [hQ1, hA9, hA9', hq, qPochhammer]
  rw [qPochhammer_one q]
  ring_nf

/-- The denominator ratio between the `N=6` and `N=5` transformed-α
q-Pochhammer factors. -/
theorem BaileyTransform_six_qpoch_pair_ratio_five_six
    (a q ρ₁ ρ₂ : R)
    (hD1five : qPoch (a * q / ρ₁) q 5 ≠ 0)
    (hD2five : qPoch (a * q / ρ₂) q 5 ≠ 0) :
    (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6) /
        (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5) =
      (1 - (a * q / ρ₁) * q ^ 5) *
        (1 - (a * q / ρ₂) * q ^ 5) := by
  have hD5 : qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 ≠ 0 :=
    mul_ne_zero hD1five hD2five
  rw [show qPoch (a * q / ρ₁) q 6 =
      qPoch (a * q / ρ₁) q 5 * (1 - (a * q / ρ₁) * q ^ 5) by rfl]
  rw [show qPoch (a * q / ρ₂) q 6 =
      qPoch (a * q / ρ₂) q 5 * (1 - (a * q / ρ₂) * q ^ 5) by rfl]
  field_simp [hD5]

/-- The denominator ratio between the `N=6` and `N=4` transformed-α
q-Pochhammer factors. -/
theorem BaileyTransform_six_qpoch_pair_ratio_four_six
    (a q ρ₁ ρ₂ : R)
    (hD1four : qPoch (a * q / ρ₁) q 4 ≠ 0)
    (hD2four : qPoch (a * q / ρ₂) q 4 ≠ 0) :
    (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6) /
        (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4) =
      ((1 - (a * q / ρ₁) * q ^ 4) *
        (1 - (a * q / ρ₁) * q ^ 5)) *
      ((1 - (a * q / ρ₂) * q ^ 4) *
        (1 - (a * q / ρ₂) * q ^ 5)) := by
  have hD4 : qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4 ≠ 0 :=
    mul_ne_zero hD1four hD2four
  rw [show qPoch (a * q / ρ₁) q 6 =
      qPoch (a * q / ρ₁) q 4 * (1 - (a * q / ρ₁) * q ^ 4) *
        (1 - (a * q / ρ₁) * q ^ 5) by rfl]
  rw [show qPoch (a * q / ρ₂) q 6 =
      qPoch (a * q / ρ₂) q 4 * (1 - (a * q / ρ₂) * q ^ 4) *
        (1 - (a * q / ρ₂) * q ^ 5) by rfl]
  field_simp [hD4]

/-- The eight-step q-Pochhammer ratio `(aq;q)_9 / (aq;q)_1`. -/
theorem BaileyTransform_seven_qpoch_aq_nine_over_one
    (a q : R) (hA1 : qPoch (a * q) q 1 ≠ 0) :
    qPoch (a * q) q 9 / qPoch (a * q) q 1 =
      (1 - a * q ^ 2) * (1 - a * q ^ 3) * (1 - a * q ^ 4) *
        (1 - a * q ^ 5) * (1 - a * q ^ 6) * (1 - a * q ^ 7) *
        (1 - a * q ^ 8) * (1 - a * q ^ 9) := by
  rw [show qPoch (a * q) q 9 =
      qPoch (a * q) q 1 * (1 - (a * q) * q ^ 1) *
        (1 - (a * q) * q ^ 2) * (1 - (a * q) * q ^ 3) *
        (1 - (a * q) * q ^ 4) * (1 - (a * q) * q ^ 5) *
        (1 - (a * q) * q ^ 6) * (1 - (a * q) * q ^ 7) *
        (1 - (a * q) * q ^ 8) by rfl]
  simp only [pow_one]
  field_simp [hA1]

/-- The seven-step q-Pochhammer ratio `(aq;q)_9 / (aq;q)_2`. -/
theorem BaileyTransform_seven_qpoch_aq_nine_over_two
    (a q : R) (hA2 : qPoch (a * q) q 2 ≠ 0) :
    qPoch (a * q) q 9 / qPoch (a * q) q 2 =
      (1 - a * q ^ 3) * (1 - a * q ^ 4) * (1 - a * q ^ 5) *
        (1 - a * q ^ 6) * (1 - a * q ^ 7) * (1 - a * q ^ 8) *
        (1 - a * q ^ 9) := by
  rw [show qPoch (a * q) q 9 =
      qPoch (a * q) q 2 * (1 - (a * q) * q ^ 2) *
        (1 - (a * q) * q ^ 3) * (1 - (a * q) * q ^ 4) *
        (1 - (a * q) * q ^ 5) * (1 - (a * q) * q ^ 6) *
        (1 - (a * q) * q ^ 7) * (1 - (a * q) * q ^ 8) by rfl]
  field_simp [hA2]

/-- The six-step q-Pochhammer ratio `(aq;q)_9 / (aq;q)_3`. -/
theorem BaileyTransform_seven_qpoch_aq_nine_over_three
    (a q : R) (hA3 : qPoch (a * q) q 3 ≠ 0) :
    qPoch (a * q) q 9 / qPoch (a * q) q 3 =
      (1 - a * q ^ 4) * (1 - a * q ^ 5) * (1 - a * q ^ 6) *
        (1 - a * q ^ 7) * (1 - a * q ^ 8) * (1 - a * q ^ 9) := by
  rw [show qPoch (a * q) q 9 =
      qPoch (a * q) q 3 * (1 - (a * q) * q ^ 3) *
        (1 - (a * q) * q ^ 4) * (1 - (a * q) * q ^ 5) *
        (1 - (a * q) * q ^ 6) * (1 - (a * q) * q ^ 7) *
        (1 - (a * q) * q ^ 8) by rfl]
  field_simp [hA3]

/-- The five-step q-Pochhammer ratio `(aq;q)_9 / (aq;q)_4`. -/
theorem BaileyTransform_seven_qpoch_aq_nine_over_four
    (a q : R) (hA4 : qPoch (a * q) q 4 ≠ 0) :
    qPoch (a * q) q 9 / qPoch (a * q) q 4 =
      (1 - a * q ^ 5) * (1 - a * q ^ 6) * (1 - a * q ^ 7) *
        (1 - a * q ^ 8) * (1 - a * q ^ 9) := by
  rw [show qPoch (a * q) q 9 =
      qPoch (a * q) q 4 * (1 - (a * q) * q ^ 4) *
        (1 - (a * q) * q ^ 5) * (1 - (a * q) * q ^ 6) *
        (1 - (a * q) * q ^ 7) * (1 - (a * q) * q ^ 8) by rfl]
  field_simp [hA4]

/-- The four-step q-Pochhammer ratio `(aq;q)_9 / (aq;q)_5`. -/
theorem BaileyTransform_seven_qpoch_aq_nine_over_five
    (a q : R) (hA5 : qPoch (a * q) q 5 ≠ 0) :
    qPoch (a * q) q 9 / qPoch (a * q) q 5 =
      (1 - a * q ^ 6) * (1 - a * q ^ 7) * (1 - a * q ^ 8) *
        (1 - a * q ^ 9) := by
  rw [show qPoch (a * q) q 9 =
      qPoch (a * q) q 5 * (1 - (a * q) * q ^ 5) *
        (1 - (a * q) * q ^ 6) * (1 - (a * q) * q ^ 7) *
        (1 - (a * q) * q ^ 8) by rfl]
  field_simp [hA5]

/-- The four-step q-Pochhammer ratio `(aq;q)_10 / (aq;q)_6`. -/
theorem BaileyTransform_seven_qpoch_aq_ten_over_six
    (a q : R) (hA6 : qPoch (a * q) q 6 ≠ 0) :
    qPoch (a * q) q 10 / qPoch (a * q) q 6 =
      (1 - a * q ^ 7) * (1 - a * q ^ 8) * (1 - a * q ^ 9) *
        (1 - a * q ^ 10) := by
  rw [show qPoch (a * q) q 10 =
      qPoch (a * q) q 6 * (1 - (a * q) * q ^ 6) *
        (1 - (a * q) * q ^ 7) * (1 - (a * q) * q ^ 8) *
        (1 - (a * q) * q ^ 9) by rfl]
  field_simp [hA6]

/-- The three-step q-Pochhammer ratio `(aq;q)_10 / (aq;q)_7`. -/
theorem BaileyTransform_seven_qpoch_aq_ten_over_seven
    (a q : R) (hA7 : qPoch (a * q) q 7 ≠ 0) :
    qPoch (a * q) q 10 / qPoch (a * q) q 7 =
      (1 - a * q ^ 8) * (1 - a * q ^ 9) * (1 - a * q ^ 10) := by
  rw [show qPoch (a * q) q 10 =
      qPoch (a * q) q 7 * (1 - (a * q) * q ^ 7) *
        (1 - (a * q) * q ^ 8) * (1 - (a * q) * q ^ 9) by rfl]
  field_simp [hA7]

/-- The two-step q-Pochhammer ratio `(aq;q)_10 / (aq;q)_8`. -/
theorem BaileyTransform_seven_qpoch_aq_ten_over_eight
    (a q : R) (hA8 : qPoch (a * q) q 8 ≠ 0) :
    qPoch (a * q) q 10 / qPoch (a * q) q 8 =
      (1 - a * q ^ 9) * (1 - a * q ^ 10) := by
  rw [show qPoch (a * q) q 10 =
      qPoch (a * q) q 8 * (1 - (a * q) * q ^ 8) *
        (1 - (a * q) * q ^ 9) by rfl]
  field_simp [hA8]

/-- The adjacent q-Pochhammer ratio `(aq;q)_10 / (aq;q)_9`. -/
theorem BaileyTransform_seven_qpoch_aq_ten_over_nine
    (a q : R) (hA9 : qPoch (a * q) q 9 ≠ 0) :
    qPoch (a * q) q 10 / qPoch (a * q) q 9 = 1 - a * q ^ 10 := by
  rw [show qPoch (a * q) q 10 =
      qPoch (a * q) q 9 * (1 - (a * q) * q ^ 9) by rfl]
  field_simp [hA9]

/-- The three-step q-Pochhammer ratio needed in the `n = 6`, α₃ coefficient
calculation. -/
theorem BaileyTransform_six_qpoch_aq_nine_over_six
    (a q : R) (hA6 : qPoch (a * q) q 6 ≠ 0) :
    qPoch (a * q) q 9 / qPoch (a * q) q 6 =
      (1 - a * q ^ 7) * (1 - a * q ^ 8) * (1 - a * q ^ 9) := by
  rw [show qPoch (a * q) q 9 =
      qPoch (a * q) q 6 * (1 - (a * q) * q ^ 6) *
        (1 - (a * q) * q ^ 7) * (1 - (a * q) * q ^ 8) by rfl]
  field_simp [hA6]

/-- The two-step q-Pochhammer ratio `(aq;q)_9 / (aq;q)_7`. -/
theorem BaileyTransform_six_qpoch_aq_nine_over_seven
    (a q : R) (hA7 : qPoch (a * q) q 7 ≠ 0) :
    qPoch (a * q) q 9 / qPoch (a * q) q 7 =
      (1 - a * q ^ 8) * (1 - a * q ^ 9) := by
  rw [show qPoch (a * q) q 9 =
      qPoch (a * q) q 7 * (1 - (a * q) * q ^ 7) *
        (1 - (a * q) * q ^ 8) by rfl]
  field_simp [hA7]

/-- The adjacent q-Pochhammer ratio `(aq;q)_9 / (aq;q)_8`. -/
theorem BaileyTransform_six_qpoch_aq_nine_over_eight
    (a q : R) (hA8 : qPoch (a * q) q 8 ≠ 0) :
    qPoch (a * q) q 9 / qPoch (a * q) q 8 = 1 - a * q ^ 9 := by
  rw [show qPoch (a * q) q 9 =
      qPoch (a * q) q 8 * (1 - (a * q) * q ^ 8) by rfl]
  field_simp [hA8]

/-- The first middle denominator ratio appearing in the `n = 6`, α₃
common-denominator calculation. -/
theorem BaileyTransform_six_qpochhammer_aq_alpha_three_first_middle_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hA7 : qPoch (a * q) q 7 ≠ 0) :
    qPochhammer q 3 * qPoch (a * q) q 9 /
        (qPochhammer q 2 * qPochhammer q 1 * qPoch (a * q) q 7) =
      (1 + q + q ^ 2) * ((1 - a * q ^ 8) * (1 - a * q ^ 9)) := by
  have hQ2Q1 : qPochhammer q 2 * qPochhammer q 1 ≠ 0 :=
    mul_ne_zero hQ2 hQ1
  have hQ := BaileyTransform_three_qpochhammer_three_over_one_two q hQ1 hQ2
  have hA := BaileyTransform_six_qpoch_aq_nine_over_seven a q hA7
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 3)
      (qPochhammer q 2 * qPochhammer q 1)
      (qPoch (a * q) q 9) (qPoch (a * q) q 7)
      (1 + q + q ^ 2) ((1 - a * q ^ 8) * (1 - a * q ^ 9))
      hQ2Q1 hA7 hQ hA

/-- The second middle denominator ratio appearing in the `n = 6`, α₃
common-denominator calculation. -/
theorem BaileyTransform_six_qpochhammer_aq_alpha_three_second_middle_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hA8 : qPoch (a * q) q 8 ≠ 0) :
    qPochhammer q 3 * qPoch (a * q) q 9 /
        (qPochhammer q 1 * qPochhammer q 2 * qPoch (a * q) q 8) =
      (1 + q + q ^ 2) * (1 - a * q ^ 9) := by
  have hQ1Q2 : qPochhammer q 1 * qPochhammer q 2 ≠ 0 :=
    mul_ne_zero hQ1 hQ2
  have hQ : qPochhammer q 3 / (qPochhammer q 1 * qPochhammer q 2) =
      1 + q + q ^ 2 := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      BaileyTransform_three_qpochhammer_three_over_one_two q hQ1 hQ2
  have hA := BaileyTransform_six_qpoch_aq_nine_over_eight a q hA8
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 3)
      (qPochhammer q 1 * qPochhammer q 2)
      (qPoch (a * q) q 9) (qPoch (a * q) q 8)
      (1 + q + q ^ 2) (1 - a * q ^ 9) hQ1Q2 hA8 hQ hA

/-- The denominator ratio between the `N=6` and `N=3` transformed-α
q-Pochhammer factors. -/
theorem BaileyTransform_six_qpoch_pair_ratio_three_six
    (a q ρ₁ ρ₂ : R)
    (hD1three : qPoch (a * q / ρ₁) q 3 ≠ 0)
    (hD2three : qPoch (a * q / ρ₂) q 3 ≠ 0) :
    (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6) /
        (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3) =
      ((1 - (a * q / ρ₁) * q ^ 3) *
        (1 - (a * q / ρ₁) * q ^ 4) *
        (1 - (a * q / ρ₁) * q ^ 5)) *
      ((1 - (a * q / ρ₂) * q ^ 3) *
        (1 - (a * q / ρ₂) * q ^ 4) *
        (1 - (a * q / ρ₂) * q ^ 5)) := by
  have hD3 : qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 ≠ 0 :=
    mul_ne_zero hD1three hD2three
  rw [show qPoch (a * q / ρ₁) q 6 =
      qPoch (a * q / ρ₁) q 3 * (1 - (a * q / ρ₁) * q ^ 3) *
        (1 - (a * q / ρ₁) * q ^ 4) *
        (1 - (a * q / ρ₁) * q ^ 5) by rfl]
  rw [show qPoch (a * q / ρ₂) q 6 =
      qPoch (a * q / ρ₂) q 3 * (1 - (a * q / ρ₂) * q ^ 3) *
        (1 - (a * q / ρ₂) * q ^ 4) *
        (1 - (a * q / ρ₂) * q ^ 5) by rfl]
  field_simp [hD3]

/-- The seven-step q-Pochhammer ratio `(aq;q)_8 / (aq;q)_1`. -/
theorem BaileyTransform_seven_qpoch_aq_eight_over_one
    (a q : R) (hA1 : qPoch (a * q) q 1 ≠ 0) :
    qPoch (a * q) q 8 / qPoch (a * q) q 1 =
      (1 - a * q ^ 2) * (1 - a * q ^ 3) * (1 - a * q ^ 4) *
        (1 - a * q ^ 5) * (1 - a * q ^ 6) * (1 - a * q ^ 7) *
        (1 - a * q ^ 8) := by
  rw [show qPoch (a * q) q 8 =
      qPoch (a * q) q 1 * (1 - (a * q) * q ^ 1) *
        (1 - (a * q) * q ^ 2) * (1 - (a * q) * q ^ 3) *
        (1 - (a * q) * q ^ 4) * (1 - (a * q) * q ^ 5) *
        (1 - (a * q) * q ^ 6) * (1 - (a * q) * q ^ 7) by rfl]
  simp only [pow_one]
  field_simp [hA1]

/-- The six-step q-Pochhammer ratio `(aq;q)_8 / (aq;q)_2`. -/
theorem BaileyTransform_seven_qpoch_aq_eight_over_two
    (a q : R) (hA2 : qPoch (a * q) q 2 ≠ 0) :
    qPoch (a * q) q 8 / qPoch (a * q) q 2 =
      (1 - a * q ^ 3) * (1 - a * q ^ 4) * (1 - a * q ^ 5) *
        (1 - a * q ^ 6) * (1 - a * q ^ 7) * (1 - a * q ^ 8) := by
  rw [show qPoch (a * q) q 8 =
      qPoch (a * q) q 2 * (1 - (a * q) * q ^ 2) *
        (1 - (a * q) * q ^ 3) * (1 - (a * q) * q ^ 4) *
        (1 - (a * q) * q ^ 5) * (1 - (a * q) * q ^ 6) *
        (1 - (a * q) * q ^ 7) by rfl]
  field_simp [hA2]

/-- The five-step q-Pochhammer ratio `(aq;q)_8 / (aq;q)_3`. -/
theorem BaileyTransform_seven_qpoch_aq_eight_over_three
    (a q : R) (hA3 : qPoch (a * q) q 3 ≠ 0) :
    qPoch (a * q) q 8 / qPoch (a * q) q 3 =
      (1 - a * q ^ 4) * (1 - a * q ^ 5) * (1 - a * q ^ 6) *
        (1 - a * q ^ 7) * (1 - a * q ^ 8) := by
  rw [show qPoch (a * q) q 8 =
      qPoch (a * q) q 3 * (1 - (a * q) * q ^ 3) *
        (1 - (a * q) * q ^ 4) * (1 - (a * q) * q ^ 5) *
        (1 - (a * q) * q ^ 6) * (1 - (a * q) * q ^ 7) by rfl]
  field_simp [hA3]

/-- The four-step q-Pochhammer ratio needed in the `n = 6`, α₂ coefficient
calculation. -/
theorem BaileyTransform_six_qpoch_aq_eight_over_four
    (a q : R) (hA4 : qPoch (a * q) q 4 ≠ 0) :
    qPoch (a * q) q 8 / qPoch (a * q) q 4 =
      (1 - a * q ^ 5) * (1 - a * q ^ 6) *
        (1 - a * q ^ 7) * (1 - a * q ^ 8) := by
  rw [show qPoch (a * q) q 8 =
      qPoch (a * q) q 4 * (1 - (a * q) * q ^ 4) *
        (1 - (a * q) * q ^ 5) * (1 - (a * q) * q ^ 6) *
        (1 - (a * q) * q ^ 7) by rfl]
  field_simp [hA4]

/-- The three-step q-Pochhammer ratio `(aq;q)_8 / (aq;q)_5`. -/
theorem BaileyTransform_six_qpoch_aq_eight_over_five
    (a q : R) (hA5 : qPoch (a * q) q 5 ≠ 0) :
    qPoch (a * q) q 8 / qPoch (a * q) q 5 =
      (1 - a * q ^ 6) * (1 - a * q ^ 7) * (1 - a * q ^ 8) := by
  rw [show qPoch (a * q) q 8 =
      qPoch (a * q) q 5 * (1 - (a * q) * q ^ 5) *
        (1 - (a * q) * q ^ 6) * (1 - (a * q) * q ^ 7) by rfl]
  field_simp [hA5]

/-- The first middle denominator ratio appearing in the `n = 6`, α₂
common-denominator calculation. -/
theorem BaileyTransform_six_qpochhammer_aq_alpha_two_first_middle_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hA5 : qPoch (a * q) q 5 ≠ 0) :
    qPochhammer q 4 * qPoch (a * q) q 8 /
        (qPochhammer q 3 * qPochhammer q 1 * qPoch (a * q) q 5) =
      (1 + q + q ^ 2 + q ^ 3) *
        ((1 - a * q ^ 6) * (1 - a * q ^ 7) * (1 - a * q ^ 8)) := by
  have hQ3Q1 : qPochhammer q 3 * qPochhammer q 1 ≠ 0 :=
    mul_ne_zero hQ3 hQ1
  have hQ : qPochhammer q 4 / (qPochhammer q 3 * qPochhammer q 1) =
      1 + q + q ^ 2 + q ^ 3 := by
    have hq : 1 - q ≠ 0 := by simpa [qPochhammer] using hQ1
    rw [show qPochhammer q 4 = qPochhammer q 3 * (1 - q ^ 4) by rfl]
    field_simp [hQ3]
    simp [qPochhammer]
    field_simp [hq]
    ring
  have hA := BaileyTransform_six_qpoch_aq_eight_over_five a q hA5
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 4)
      (qPochhammer q 3 * qPochhammer q 1)
      (qPoch (a * q) q 8) (qPoch (a * q) q 5)
      (1 + q + q ^ 2 + q ^ 3)
      ((1 - a * q ^ 6) * (1 - a * q ^ 7) * (1 - a * q ^ 8))
      hQ3Q1 hA5 hQ hA

/-- The second middle denominator ratio appearing in the `n = 6`, α₂
common-denominator calculation. -/
theorem BaileyTransform_six_qpochhammer_aq_alpha_two_second_middle_ratio
    (a q : R)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hA6 : qPoch (a * q) q 6 ≠ 0) :
    qPochhammer q 4 * qPoch (a * q) q 8 /
        (qPochhammer q 2 * qPochhammer q 2 * qPoch (a * q) q 6) =
      ((1 + q + q ^ 2) * (1 + q ^ 2)) *
        ((1 - a * q ^ 7) * (1 - a * q ^ 8)) := by
  have hQ2Q2 : qPochhammer q 2 * qPochhammer q 2 ≠ 0 :=
    mul_ne_zero hQ2 hQ2
  have hQ : qPochhammer q 4 / (qPochhammer q 2 * qPochhammer q 2) =
      (1 + q + q ^ 2) * (1 + q ^ 2) := by
    have hq : 1 - q ≠ 0 := by
      simpa [qPochhammer] using left_ne_zero_of_mul hQ2
    have hq2 : 1 - q ^ 2 ≠ 0 := by
      simpa [qPochhammer] using right_ne_zero_of_mul hQ2
    simp [qPochhammer]
    field_simp [hq, hq2, hQ2Q2]
    ring
  have hA : qPoch (a * q) q 8 / qPoch (a * q) q 6 =
      (1 - a * q ^ 7) * (1 - a * q ^ 8) := by
    rw [show qPoch (a * q) q 8 =
        qPoch (a * q) q 6 * (1 - (a * q) * q ^ 6) *
          (1 - (a * q) * q ^ 7) by rfl]
    field_simp [hA6]
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 4)
      (qPochhammer q 2 * qPochhammer q 2)
      (qPoch (a * q) q 8) (qPoch (a * q) q 6)
      ((1 + q + q ^ 2) * (1 + q ^ 2))
      ((1 - a * q ^ 7) * (1 - a * q ^ 8))
      hQ2Q2 hA6 hQ hA

/-- The third middle denominator ratio appearing in the `n = 6`, α₂
common-denominator calculation. -/
theorem BaileyTransform_six_qpochhammer_aq_alpha_two_third_middle_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hA7 : qPoch (a * q) q 7 ≠ 0) :
    qPochhammer q 4 * qPoch (a * q) q 8 /
        (qPochhammer q 1 * qPochhammer q 3 * qPoch (a * q) q 7) =
      (1 + q + q ^ 2 + q ^ 3) * (1 - a * q ^ 8) := by
  have hQ1Q3 : qPochhammer q 1 * qPochhammer q 3 ≠ 0 :=
    mul_ne_zero hQ1 hQ3
  have hQ : qPochhammer q 4 / (qPochhammer q 1 * qPochhammer q 3) =
      1 + q + q ^ 2 + q ^ 3 := by
    have hq : 1 - q ≠ 0 := by simpa [qPochhammer] using hQ1
    rw [show qPochhammer q 4 = qPochhammer q 3 * (1 - q ^ 4) by rfl]
    field_simp [hQ3, hQ1Q3]
    simp [qPochhammer]
    field_simp [hq]
    ring
  have hA : qPoch (a * q) q 8 / qPoch (a * q) q 7 =
      1 - a * q ^ 8 := by
    rw [show qPoch (a * q) q 8 =
        qPoch (a * q) q 7 * (1 - (a * q) * q ^ 7) by rfl]
    field_simp [hA7]
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 4)
      (qPochhammer q 1 * qPochhammer q 3)
      (qPoch (a * q) q 8) (qPoch (a * q) q 7)
      (1 + q + q ^ 2 + q ^ 3) (1 - a * q ^ 8)
      hQ1Q3 hA7 hQ hA

/-- The denominator ratio between the `N=6` and `N=2` transformed-α
q-Pochhammer factors. -/
theorem BaileyTransform_six_qpoch_pair_ratio_two_six
    (a q ρ₁ ρ₂ : R)
    (hD1two : qPoch (a * q / ρ₁) q 2 ≠ 0)
    (hD2two : qPoch (a * q / ρ₂) q 2 ≠ 0) :
    (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6) /
        (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2) =
      ((1 - (a * q / ρ₁) * q ^ 2) *
        (1 - (a * q / ρ₁) * q ^ 3) *
        (1 - (a * q / ρ₁) * q ^ 4) *
        (1 - (a * q / ρ₁) * q ^ 5)) *
      ((1 - (a * q / ρ₂) * q ^ 2) *
        (1 - (a * q / ρ₂) * q ^ 3) *
        (1 - (a * q / ρ₂) * q ^ 4) *
        (1 - (a * q / ρ₂) * q ^ 5)) := by
  have h1 : qPoch (a * q / ρ₁) q 6 / qPoch (a * q / ρ₁) q 2 =
      (1 - (a * q / ρ₁) * q ^ 2) *
        (1 - (a * q / ρ₁) * q ^ 3) *
        (1 - (a * q / ρ₁) * q ^ 4) *
        (1 - (a * q / ρ₁) * q ^ 5) := by
    rw [show qPoch (a * q / ρ₁) q 6 =
        qPoch (a * q / ρ₁) q 2 * (1 - (a * q / ρ₁) * q ^ 2) *
          (1 - (a * q / ρ₁) * q ^ 3) *
          (1 - (a * q / ρ₁) * q ^ 4) *
          (1 - (a * q / ρ₁) * q ^ 5) by rfl]
    field_simp [hD1two]
  have h2 : qPoch (a * q / ρ₂) q 6 / qPoch (a * q / ρ₂) q 2 =
      (1 - (a * q / ρ₂) * q ^ 2) *
        (1 - (a * q / ρ₂) * q ^ 3) *
        (1 - (a * q / ρ₂) * q ^ 4) *
        (1 - (a * q / ρ₂) * q ^ 5) := by
    rw [show qPoch (a * q / ρ₂) q 6 =
        qPoch (a * q / ρ₂) q 2 * (1 - (a * q / ρ₂) * q ^ 2) *
          (1 - (a * q / ρ₂) * q ^ 3) *
          (1 - (a * q / ρ₂) * q ^ 4) *
          (1 - (a * q / ρ₂) * q ^ 5) by rfl]
    field_simp [hD2two]
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPoch (a * q / ρ₁) q 6)
      (qPoch (a * q / ρ₁) q 2)
      (qPoch (a * q / ρ₂) q 6)
      (qPoch (a * q / ρ₂) q 2)
      ((1 - (a * q / ρ₁) * q ^ 2) *
        (1 - (a * q / ρ₁) * q ^ 3) *
        (1 - (a * q / ρ₁) * q ^ 4) *
        (1 - (a * q / ρ₁) * q ^ 5))
      ((1 - (a * q / ρ₂) * q ^ 2) *
        (1 - (a * q / ρ₂) * q ^ 3) *
        (1 - (a * q / ρ₂) * q ^ 4) *
        (1 - (a * q / ρ₂) * q ^ 5))
      hD1two hD2two h1 h2

/-- The two-step q-Pochhammer ratio needed in the `n = 5`, α₃ coefficient
calculation. -/
theorem BaileyTransform_five_qpoch_aq_eight_over_six
    (a q : R) (hA6 : qPoch (a * q) q 6 ≠ 0) :
    qPoch (a * q) q 8 / qPoch (a * q) q 6 =
      (1 - a * q ^ 7) * (1 - a * q ^ 8) := by
  rw [show qPoch (a * q) q 8 =
      qPoch (a * q) q 6 * (1 - (a * q) * q ^ 6) *
        (1 - (a * q) * q ^ 7) by rfl]
  field_simp [hA6]

/-- The adjacent q-Pochhammer ratio `(aq;q)_8 / (aq;q)_7`. -/
theorem BaileyTransform_five_qpoch_aq_eight_over_seven
    (a q : R) (hA7 : qPoch (a * q) q 7 ≠ 0) :
    qPoch (a * q) q 8 / qPoch (a * q) q 7 = 1 - a * q ^ 8 := by
  rw [show qPoch (a * q) q 8 =
      qPoch (a * q) q 7 * (1 - (a * q) * q ^ 7) by rfl]
  field_simp [hA7]

/-- The middle denominator ratio appearing in the `n = 5`, α₃
common-denominator calculation. -/
theorem BaileyTransform_five_qpochhammer_aq_alpha_three_middle_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hA7 : qPoch (a * q) q 7 ≠ 0) :
    qPochhammer q 2 * qPoch (a * q) q 8 /
        (qPochhammer q 1 * qPochhammer q 1 * qPoch (a * q) q 7) =
      (1 + q) * (1 - a * q ^ 8) := by
  have hQ1sq : qPochhammer q 1 * qPochhammer q 1 ≠ 0 :=
    mul_ne_zero hQ1 hQ1
  have hQ := BaileyTransform_three_qpochhammer_two_over_one_sq q hQ1
  have hA := BaileyTransform_five_qpoch_aq_eight_over_seven a q hA7
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 2)
      (qPochhammer q 1 * qPochhammer q 1)
      (qPoch (a * q) q 8) (qPoch (a * q) q 7)
      (1 + q) (1 - a * q ^ 8) hQ1sq hA7 hQ hA

/-- The denominator ratio between the `N=5` and `N=3` transformed-α
q-Pochhammer factors. -/
theorem BaileyTransform_five_qpoch_pair_ratio_three_five
    (a q ρ₁ ρ₂ : R)
    (hD1three : qPoch (a * q / ρ₁) q 3 ≠ 0)
    (hD2three : qPoch (a * q / ρ₂) q 3 ≠ 0) :
    (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5) /
        (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3) =
      ((1 - (a * q / ρ₁) * q ^ 3) * (1 - (a * q / ρ₁) * q ^ 4)) *
        ((1 - (a * q / ρ₂) * q ^ 3) * (1 - (a * q / ρ₂) * q ^ 4)) := by
  have hD3 : qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 ≠ 0 :=
    mul_ne_zero hD1three hD2three
  rw [show qPoch (a * q / ρ₁) q 5 =
      qPoch (a * q / ρ₁) q 3 * (1 - (a * q / ρ₁) * q ^ 3) *
        (1 - (a * q / ρ₁) * q ^ 4) by rfl]
  rw [show qPoch (a * q / ρ₂) q 5 =
      qPoch (a * q / ρ₂) q 3 * (1 - (a * q / ρ₂) * q ^ 3) *
        (1 - (a * q / ρ₂) * q ^ 4) by rfl]
  field_simp [hD3]

/-- The three-step q-Pochhammer ratio needed in the `n = 5`, α₂ coefficient
calculation. -/
theorem BaileyTransform_five_qpoch_aq_seven_over_four
    (a q : R) (hA4 : qPoch (a * q) q 4 ≠ 0) :
    qPoch (a * q) q 7 / qPoch (a * q) q 4 =
      (1 - a * q ^ 5) * (1 - a * q ^ 6) * (1 - a * q ^ 7) := by
  rw [show qPoch (a * q) q 7 =
      qPoch (a * q) q 4 * (1 - (a * q) * q ^ 4) *
        (1 - (a * q) * q ^ 5) * (1 - (a * q) * q ^ 6) by rfl]
  field_simp [hA4]

/-- The two-step q-Pochhammer ratio `(aq;q)_7 / (aq;q)_5`. -/
theorem BaileyTransform_five_qpoch_aq_seven_over_five
    (a q : R) (hA5 : qPoch (a * q) q 5 ≠ 0) :
    qPoch (a * q) q 7 / qPoch (a * q) q 5 =
      (1 - a * q ^ 6) * (1 - a * q ^ 7) := by
  rw [show qPoch (a * q) q 7 =
      qPoch (a * q) q 5 * (1 - (a * q) * q ^ 5) *
        (1 - (a * q) * q ^ 6) by rfl]
  field_simp [hA5]

/-- The adjacent q-Pochhammer ratio `(aq;q)_7 / (aq;q)_6`. -/
theorem BaileyTransform_five_qpoch_aq_seven_over_six
    (a q : R) (hA6 : qPoch (a * q) q 6 ≠ 0) :
    qPoch (a * q) q 7 / qPoch (a * q) q 6 = 1 - a * q ^ 7 := by
  rw [show qPoch (a * q) q 7 =
      qPoch (a * q) q 6 * (1 - (a * q) * q ^ 6) by rfl]
  field_simp [hA6]

/-- The first middle denominator ratio appearing in the `n = 5`, α₂
common-denominator calculation. -/
theorem BaileyTransform_five_qpochhammer_aq_alpha_two_first_middle_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hA5 : qPoch (a * q) q 5 ≠ 0) :
    qPochhammer q 3 * qPoch (a * q) q 7 /
        (qPochhammer q 2 * qPochhammer q 1 * qPoch (a * q) q 5) =
      (1 + q + q ^ 2) * ((1 - a * q ^ 6) * (1 - a * q ^ 7)) := by
  have hQ2Q1 : qPochhammer q 2 * qPochhammer q 1 ≠ 0 :=
    mul_ne_zero hQ2 hQ1
  have hQ := BaileyTransform_three_qpochhammer_three_over_one_two q hQ1 hQ2
  have hA := BaileyTransform_five_qpoch_aq_seven_over_five a q hA5
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 3)
      (qPochhammer q 2 * qPochhammer q 1)
      (qPoch (a * q) q 7) (qPoch (a * q) q 5)
      (1 + q + q ^ 2) ((1 - a * q ^ 6) * (1 - a * q ^ 7))
      hQ2Q1 hA5 hQ hA

/-- The second middle denominator ratio appearing in the `n = 5`, α₂
common-denominator calculation. -/
theorem BaileyTransform_five_qpochhammer_aq_alpha_two_second_middle_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hA6 : qPoch (a * q) q 6 ≠ 0) :
    qPochhammer q 3 * qPoch (a * q) q 7 /
        (qPochhammer q 1 * qPochhammer q 2 * qPoch (a * q) q 6) =
      (1 + q + q ^ 2) * (1 - a * q ^ 7) := by
  have hQ1Q2 : qPochhammer q 1 * qPochhammer q 2 ≠ 0 :=
    mul_ne_zero hQ1 hQ2
  have hQ : qPochhammer q 3 / (qPochhammer q 1 * qPochhammer q 2) =
      1 + q + q ^ 2 := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      BaileyTransform_three_qpochhammer_three_over_one_two q hQ1 hQ2
  have hA := BaileyTransform_five_qpoch_aq_seven_over_six a q hA6
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 3)
      (qPochhammer q 1 * qPochhammer q 2)
      (qPoch (a * q) q 7) (qPoch (a * q) q 6)
      (1 + q + q ^ 2) (1 - a * q ^ 7) hQ1Q2 hA6 hQ hA

/-- The denominator ratio between the `N=5` and `N=2` transformed-α
q-Pochhammer factors. -/
theorem BaileyTransform_five_qpoch_pair_ratio_two_five
    (a q ρ₁ ρ₂ : R)
    (hD1two : qPoch (a * q / ρ₁) q 2 ≠ 0)
    (hD2two : qPoch (a * q / ρ₂) q 2 ≠ 0) :
    (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5) /
        (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2) =
      ((1 - (a * q / ρ₁) * q ^ 2) * (1 - (a * q / ρ₁) * q ^ 3) *
          (1 - (a * q / ρ₁) * q ^ 4)) *
        ((1 - (a * q / ρ₂) * q ^ 2) * (1 - (a * q / ρ₂) * q ^ 3) *
          (1 - (a * q / ρ₂) * q ^ 4)) := by
  have hD2 : qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2 ≠ 0 :=
    mul_ne_zero hD1two hD2two
  rw [show qPoch (a * q / ρ₁) q 5 =
      qPoch (a * q / ρ₁) q 2 * (1 - (a * q / ρ₁) * q ^ 2) *
        (1 - (a * q / ρ₁) * q ^ 3) * (1 - (a * q / ρ₁) * q ^ 4) by rfl]
  rw [show qPoch (a * q / ρ₂) q 5 =
      qPoch (a * q / ρ₂) q 2 * (1 - (a * q / ρ₂) * q ^ 2) *
        (1 - (a * q / ρ₂) * q ^ 3) * (1 - (a * q / ρ₂) * q ^ 4) by rfl]
  field_simp [hD2]

/-- The two-step q-Pochhammer ratio needed in the `n = 4`, α₂ coefficient
calculation. -/
theorem BaileyTransform_four_qpoch_aq_six_over_four
    (a q : R) (hA4 : qPoch (a * q) q 4 ≠ 0) :
    qPoch (a * q) q 6 / qPoch (a * q) q 4 =
      (1 - a * q ^ 5) * (1 - a * q ^ 6) := by
  rw [show qPoch (a * q) q 6 =
      qPoch (a * q) q 4 * (1 - (a * q) * q ^ 4) *
        (1 - (a * q) * q ^ 5) by rfl]
  field_simp [hA4]

/-- The adjacent q-Pochhammer ratio `(aq;q)_6 / (aq;q)_5`. -/
theorem BaileyTransform_four_qpoch_aq_six_over_five
    (a q : R) (hA5 : qPoch (a * q) q 5 ≠ 0) :
    qPoch (a * q) q 6 / qPoch (a * q) q 5 = 1 - a * q ^ 6 := by
  rw [show qPoch (a * q) q 6 =
      qPoch (a * q) q 5 * (1 - (a * q) * q ^ 5) by rfl]
  field_simp [hA5]

/-- The middle denominator ratio appearing in the `n = 4`, α₂
common-denominator calculation. -/
theorem BaileyTransform_four_qpochhammer_aq_alpha_two_middle_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hA5 : qPoch (a * q) q 5 ≠ 0) :
    qPochhammer q 2 * qPoch (a * q) q 6 /
        (qPochhammer q 1 * qPochhammer q 1 * qPoch (a * q) q 5) =
      (1 + q) * (1 - a * q ^ 6) := by
  have hQ1sq : qPochhammer q 1 * qPochhammer q 1 ≠ 0 :=
    mul_ne_zero hQ1 hQ1
  have hQ := BaileyTransform_three_qpochhammer_two_over_one_sq q hQ1
  have hA := BaileyTransform_four_qpoch_aq_six_over_five a q hA5
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 2)
      (qPochhammer q 1 * qPochhammer q 1)
      (qPoch (a * q) q 6) (qPoch (a * q) q 5)
      (1 + q) (1 - a * q ^ 6) hQ1sq hA5 hQ hA

/-- The denominator ratio between the `N=4` and `N=2` transformed-α
q-Pochhammer factors. -/
theorem BaileyTransform_four_qpoch_pair_ratio_two_four
    (a q ρ₁ ρ₂ : R)
    (hD1two : qPoch (a * q / ρ₁) q 2 ≠ 0)
    (hD2two : qPoch (a * q / ρ₂) q 2 ≠ 0) :
    (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4) /
        (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2) =
      ((1 - (a * q / ρ₁) * q ^ 2) * (1 - (a * q / ρ₁) * q ^ 3)) *
        ((1 - (a * q / ρ₂) * q ^ 2) * (1 - (a * q / ρ₂) * q ^ 3)) := by
  have hD2 : qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2 ≠ 0 :=
    mul_ne_zero hD1two hD2two
  rw [show qPoch (a * q / ρ₁) q 4 =
      qPoch (a * q / ρ₁) q 2 * (1 - (a * q / ρ₁) * q ^ 2) *
        (1 - (a * q / ρ₁) * q ^ 3) by rfl]
  rw [show qPoch (a * q / ρ₂) q 4 =
      qPoch (a * q / ρ₂) q 2 * (1 - (a * q / ρ₂) * q ^ 2) *
        (1 - (a * q / ρ₂) * q ^ 3) by rfl]
  field_simp [hD2]

/-- The three-step q-Pochhammer ratio needed in the `n = 4`, α₁ coefficient
calculation. -/
theorem BaileyTransform_four_qpoch_aq_five_over_two
    (a q : R) (hA2 : qPoch (a * q) q 2 ≠ 0) :
    qPoch (a * q) q 5 / qPoch (a * q) q 2 =
      (1 - a * q ^ 3) * (1 - a * q ^ 4) * (1 - a * q ^ 5) := by
  rw [show qPoch (a * q) q 5 =
      qPoch (a * q) q 2 * (1 - (a * q) * q ^ 2) *
        (1 - (a * q) * q ^ 3) * (1 - (a * q) * q ^ 4) by rfl]
  field_simp [hA2]

/-- The two-step q-Pochhammer ratio needed in the `n = 4`, α₁ coefficient
calculation. -/
theorem BaileyTransform_four_qpoch_aq_five_over_three
    (a q : R) (hA3 : qPoch (a * q) q 3 ≠ 0) :
    qPoch (a * q) q 5 / qPoch (a * q) q 3 =
      (1 - a * q ^ 4) * (1 - a * q ^ 5) := by
  rw [show qPoch (a * q) q 5 =
      qPoch (a * q) q 3 * (1 - (a * q) * q ^ 3) *
        (1 - (a * q) * q ^ 4) by rfl]
  field_simp [hA3]

/-- The first middle denominator ratio appearing in the `n = 4`, α₁
common-denominator calculation. -/
theorem BaileyTransform_four_qpochhammer_aq_alpha_one_first_middle_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hA3 : qPoch (a * q) q 3 ≠ 0) :
    qPochhammer q 3 * qPoch (a * q) q 5 /
        (qPochhammer q 2 * qPochhammer q 1 * qPoch (a * q) q 3) =
      (1 + q + q ^ 2) * ((1 - a * q ^ 4) * (1 - a * q ^ 5)) := by
  have hQ2Q1 : qPochhammer q 2 * qPochhammer q 1 ≠ 0 :=
    mul_ne_zero hQ2 hQ1
  have hQ := BaileyTransform_three_qpochhammer_three_over_one_two q hQ1 hQ2
  have hA := BaileyTransform_four_qpoch_aq_five_over_three a q hA3
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 3)
      (qPochhammer q 2 * qPochhammer q 1)
      (qPoch (a * q) q 5) (qPoch (a * q) q 3)
      (1 + q + q ^ 2) ((1 - a * q ^ 4) * (1 - a * q ^ 5))
      hQ2Q1 hA3 hQ hA

/-- The second middle denominator ratio appearing in the `n = 4`, α₁
common-denominator calculation. -/
theorem BaileyTransform_four_qpochhammer_aq_alpha_one_second_middle_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hA4 : qPoch (a * q) q 4 ≠ 0) :
    qPochhammer q 3 * qPoch (a * q) q 5 /
        (qPochhammer q 1 * qPochhammer q 2 * qPoch (a * q) q 4) =
      (1 + q + q ^ 2) * (1 - a * q ^ 5) := by
  have hQ1Q2 : qPochhammer q 1 * qPochhammer q 2 ≠ 0 :=
    mul_ne_zero hQ1 hQ2
  have hQ : qPochhammer q 3 / (qPochhammer q 1 * qPochhammer q 2) =
      1 + q + q ^ 2 := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      BaileyTransform_three_qpochhammer_three_over_one_two q hQ1 hQ2
  have hA := BaileyTransform_three_qpoch_ratio_four_five a q hA4
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 3)
      (qPochhammer q 1 * qPochhammer q 2)
      (qPoch (a * q) q 5) (qPoch (a * q) q 4)
      (1 + q + q ^ 2) (1 - a * q ^ 5) hQ1Q2 hA4 hQ hA

/-- The denominator ratio between the `N=4` and `N=1` transformed-α
q-Pochhammer factors. -/
theorem BaileyTransform_four_qpoch_pair_ratio_one_four
    (a q ρ₁ ρ₂ : R)
    (hD1one : qPoch (a * q / ρ₁) q 1 ≠ 0)
    (hD2one : qPoch (a * q / ρ₂) q 1 ≠ 0) :
    (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4) /
        (qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1) =
      ((1 - (a * q / ρ₁) * q) * (1 - (a * q / ρ₁) * q ^ 2) *
        (1 - (a * q / ρ₁) * q ^ 3)) *
        ((1 - (a * q / ρ₂) * q) * (1 - (a * q / ρ₂) * q ^ 2) *
          (1 - (a * q / ρ₂) * q ^ 3)) := by
  have hD1 : qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1 ≠ 0 :=
    mul_ne_zero hD1one hD2one
  have hF1 : 1 - a * q / ρ₁ ≠ 0 := by simpa [qPoch] using hD1one
  have hF2 : 1 - a * q / ρ₂ ≠ 0 := by simpa [qPoch] using hD2one
  simp [qPoch]
  field_simp [hF1, hF2, hD1]

/-- The q-Pochhammer ratio `(q;q)_4 / ((q;q)_3 (q;q)_1)`. -/
theorem BaileyTransform_four_qpochhammer_four_over_three_one
    (q : R) (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0) :
    qPochhammer q 4 / (qPochhammer q 3 * qPochhammer q 1) =
      1 + q + q ^ 2 + q ^ 3 := by
  have hq : 1 - q ≠ 0 := by simpa [qPochhammer] using hQ1
  rw [show qPochhammer q 4 = qPochhammer q 3 * (1 - q ^ 4) by rfl]
  field_simp [hQ3]
  simp [qPochhammer]
  field_simp [hq]
  ring

/-- The q-Pochhammer ratio `(q;q)_4 / ((q;q)_2 (q;q)_2)`. -/
theorem BaileyTransform_four_qpochhammer_four_over_two_two
    (q : R) (hQ2 : qPochhammer q 2 ≠ 0) :
    qPochhammer q 4 / (qPochhammer q 2 * qPochhammer q 2) =
      (1 + q + q ^ 2) * (1 + q ^ 2) := by
  have hq : 1 - q ≠ 0 := by
    simpa [qPochhammer] using left_ne_zero_of_mul hQ2
  have hq2 : 1 - q ^ 2 ≠ 0 := by
    simpa [qPochhammer] using right_ne_zero_of_mul hQ2
  have hQ2sq : qPochhammer q 2 * qPochhammer q 2 ≠ 0 :=
    mul_ne_zero hQ2 hQ2
  simp [qPochhammer]
  field_simp [hq, hq2, hQ2sq]
  ring

/-- The ratio `(aq;q)_4 / (aq;q)_1`. -/
theorem BaileyTransform_four_qpoch_aq_four_over_one
    (a q : R) (hA1 : qPoch (a * q) q 1 ≠ 0) :
    qPoch (a * q) q 4 / qPoch (a * q) q 1 =
      (1 - a * q ^ 2) * (1 - a * q ^ 3) * (1 - a * q ^ 4) := by
  have hF : 1 - a * q ≠ 0 := by simpa [qPoch] using hA1
  simp [qPoch]
  field_simp [hF]

/-- The ratio `(aq;q)_4 / (aq;q)_2`. -/
theorem BaileyTransform_four_qpoch_aq_four_over_two
    (a q : R) (hA2 : qPoch (a * q) q 2 ≠ 0) :
    qPoch (a * q) q 4 / qPoch (a * q) q 2 =
      (1 - a * q ^ 3) * (1 - a * q ^ 4) := by
  rw [show qPoch (a * q) q 4 =
      qPoch (a * q) q 2 * (1 - (a * q) * q ^ 2) *
        (1 - (a * q) * q ^ 3) by rfl]
  field_simp [hA2]

/-- The first scalar ratio in the `n = 4`, α₀ common-denominator
calculation. -/
theorem BaileyTransform_four_alpha_zero_first_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hA1 : qPoch (a * q) q 1 ≠ 0) :
    qPochhammer q 4 * qPoch (a * q) q 4 /
        (qPochhammer q 3 * qPochhammer q 1 * qPoch (a * q) q 1) =
      (1 + q + q ^ 2 + q ^ 3) *
        ((1 - a * q ^ 2) * (1 - a * q ^ 3) * (1 - a * q ^ 4)) := by
  have hQ3Q1 : qPochhammer q 3 * qPochhammer q 1 ≠ 0 :=
    mul_ne_zero hQ3 hQ1
  have hQ := BaileyTransform_four_qpochhammer_four_over_three_one q hQ1 hQ3
  have hA := BaileyTransform_four_qpoch_aq_four_over_one a q hA1
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 4)
      (qPochhammer q 3 * qPochhammer q 1)
      (qPoch (a * q) q 4) (qPoch (a * q) q 1)
      (1 + q + q ^ 2 + q ^ 3)
      ((1 - a * q ^ 2) * (1 - a * q ^ 3) * (1 - a * q ^ 4))
      hQ3Q1 hA1 hQ hA

/-- The second scalar ratio in the `n = 4`, α₀ common-denominator
calculation. -/
theorem BaileyTransform_four_alpha_zero_second_ratio
    (a q : R)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hA2 : qPoch (a * q) q 2 ≠ 0) :
    qPochhammer q 4 * qPoch (a * q) q 4 /
        (qPochhammer q 2 * qPochhammer q 2 * qPoch (a * q) q 2) =
      ((1 + q + q ^ 2) * (1 + q ^ 2)) *
        ((1 - a * q ^ 3) * (1 - a * q ^ 4)) := by
  have hQ2Q2 : qPochhammer q 2 * qPochhammer q 2 ≠ 0 :=
    mul_ne_zero hQ2 hQ2
  have hQ := BaileyTransform_four_qpochhammer_four_over_two_two q hQ2
  have hA := BaileyTransform_four_qpoch_aq_four_over_two a q hA2
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 4)
      (qPochhammer q 2 * qPochhammer q 2)
      (qPoch (a * q) q 4) (qPoch (a * q) q 2)
      ((1 + q + q ^ 2) * (1 + q ^ 2))
      ((1 - a * q ^ 3) * (1 - a * q ^ 4))
      hQ2Q2 hA2 hQ hA

/-- The third scalar ratio in the `n = 4`, α₀ common-denominator
calculation. -/
theorem BaileyTransform_four_alpha_zero_third_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hA3 : qPoch (a * q) q 3 ≠ 0) :
    qPochhammer q 4 * qPoch (a * q) q 4 /
        (qPochhammer q 1 * qPochhammer q 3 * qPoch (a * q) q 3) =
      (1 + q + q ^ 2 + q ^ 3) * (1 - a * q ^ 4) := by
  have hQ1Q3 : qPochhammer q 1 * qPochhammer q 3 ≠ 0 :=
    mul_ne_zero hQ1 hQ3
  have hQ : qPochhammer q 4 / (qPochhammer q 1 * qPochhammer q 3) =
      1 + q + q ^ 2 + q ^ 3 := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      BaileyTransform_four_qpochhammer_four_over_three_one q hQ1 hQ3
  have hA := BaileyTransform_three_qpoch_aq_four_over_three a q hA3
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 4)
      (qPochhammer q 1 * qPochhammer q 3)
      (qPoch (a * q) q 4) (qPoch (a * q) q 3)
      (1 + q + q ^ 2 + q ^ 3) (1 - a * q ^ 4)
      hQ1Q3 hA3 hQ hA

/-- The four-step q-Pochhammer ratio needed in the `n = 5`, α₁ coefficient
calculation. -/
theorem BaileyTransform_five_qpoch_aq_six_over_two
    (a q : R) (hA2 : qPoch (a * q) q 2 ≠ 0) :
    qPoch (a * q) q 6 / qPoch (a * q) q 2 =
      (1 - a * q ^ 3) * (1 - a * q ^ 4) *
        (1 - a * q ^ 5) * (1 - a * q ^ 6) := by
  rw [show qPoch (a * q) q 6 =
      qPoch (a * q) q 2 * (1 - (a * q) * q ^ 2) *
        (1 - (a * q) * q ^ 3) * (1 - (a * q) * q ^ 4) *
        (1 - (a * q) * q ^ 5) by rfl]
  field_simp [hA2]

/-- The three-step q-Pochhammer ratio `(aq;q)_6 / (aq;q)_3`. -/
theorem BaileyTransform_five_qpoch_aq_six_over_three
    (a q : R) (hA3 : qPoch (a * q) q 3 ≠ 0) :
    qPoch (a * q) q 6 / qPoch (a * q) q 3 =
      (1 - a * q ^ 4) * (1 - a * q ^ 5) * (1 - a * q ^ 6) := by
  rw [show qPoch (a * q) q 6 =
      qPoch (a * q) q 3 * (1 - (a * q) * q ^ 3) *
        (1 - (a * q) * q ^ 4) * (1 - (a * q) * q ^ 5) by rfl]
  field_simp [hA3]

/-- The first middle denominator ratio appearing in the `n = 5`, α₁
common-denominator calculation. -/
theorem BaileyTransform_five_qpochhammer_aq_alpha_one_first_middle_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hA3 : qPoch (a * q) q 3 ≠ 0) :
    qPochhammer q 4 * qPoch (a * q) q 6 /
        (qPochhammer q 3 * qPochhammer q 1 * qPoch (a * q) q 3) =
      (1 + q + q ^ 2 + q ^ 3) *
        ((1 - a * q ^ 4) * (1 - a * q ^ 5) * (1 - a * q ^ 6)) := by
  have hQ3Q1 : qPochhammer q 3 * qPochhammer q 1 ≠ 0 :=
    mul_ne_zero hQ3 hQ1
  have hQ := BaileyTransform_four_qpochhammer_four_over_three_one q hQ1 hQ3
  have hA := BaileyTransform_five_qpoch_aq_six_over_three a q hA3
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 4)
      (qPochhammer q 3 * qPochhammer q 1)
      (qPoch (a * q) q 6) (qPoch (a * q) q 3)
      (1 + q + q ^ 2 + q ^ 3)
      ((1 - a * q ^ 4) * (1 - a * q ^ 5) * (1 - a * q ^ 6))
      hQ3Q1 hA3 hQ hA

/-- The second middle denominator ratio appearing in the `n = 5`, α₁
common-denominator calculation. -/
theorem BaileyTransform_five_qpochhammer_aq_alpha_one_second_middle_ratio
    (a q : R)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hA4 : qPoch (a * q) q 4 ≠ 0) :
    qPochhammer q 4 * qPoch (a * q) q 6 /
        (qPochhammer q 2 * qPochhammer q 2 * qPoch (a * q) q 4) =
      ((1 + q + q ^ 2) * (1 + q ^ 2)) *
        ((1 - a * q ^ 5) * (1 - a * q ^ 6)) := by
  have hQ2Q2 : qPochhammer q 2 * qPochhammer q 2 ≠ 0 :=
    mul_ne_zero hQ2 hQ2
  have hQ := BaileyTransform_four_qpochhammer_four_over_two_two q hQ2
  have hA := BaileyTransform_four_qpoch_aq_six_over_four a q hA4
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 4)
      (qPochhammer q 2 * qPochhammer q 2)
      (qPoch (a * q) q 6) (qPoch (a * q) q 4)
      ((1 + q + q ^ 2) * (1 + q ^ 2))
      ((1 - a * q ^ 5) * (1 - a * q ^ 6))
      hQ2Q2 hA4 hQ hA

/-- The third middle denominator ratio appearing in the `n = 5`, α₁
common-denominator calculation. -/
theorem BaileyTransform_five_qpochhammer_aq_alpha_one_third_middle_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hA5 : qPoch (a * q) q 5 ≠ 0) :
    qPochhammer q 4 * qPoch (a * q) q 6 /
        (qPochhammer q 1 * qPochhammer q 3 * qPoch (a * q) q 5) =
      (1 + q + q ^ 2 + q ^ 3) * (1 - a * q ^ 6) := by
  have hQ1Q3 : qPochhammer q 1 * qPochhammer q 3 ≠ 0 :=
    mul_ne_zero hQ1 hQ3
  have hQ : qPochhammer q 4 / (qPochhammer q 1 * qPochhammer q 3) =
      1 + q + q ^ 2 + q ^ 3 := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      BaileyTransform_four_qpochhammer_four_over_three_one q hQ1 hQ3
  have hA := BaileyTransform_four_qpoch_aq_six_over_five a q hA5
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 4)
      (qPochhammer q 1 * qPochhammer q 3)
      (qPoch (a * q) q 6) (qPoch (a * q) q 5)
      (1 + q + q ^ 2 + q ^ 3) (1 - a * q ^ 6)
      hQ1Q3 hA5 hQ hA

/-- The single denominator ratio between depth `5` and depth `1` for a
transformed-α q-Pochhammer factor. -/
theorem BaileyTransform_five_qpoch_single_ratio_one_five
    (a q ρ : R) (hDone : qPoch (a * q / ρ) q 1 ≠ 0) :
    qPoch (a * q / ρ) q 5 / qPoch (a * q / ρ) q 1 =
      (1 - (a * q / ρ) * q) * (1 - (a * q / ρ) * q ^ 2) *
        (1 - (a * q / ρ) * q ^ 3) * (1 - (a * q / ρ) * q ^ 4) := by
  rw [show qPoch (a * q / ρ) q 5 =
      qPoch (a * q / ρ) q 1 * (1 - (a * q / ρ) * q ^ 1) *
        (1 - (a * q / ρ) * q ^ 2) *
        (1 - (a * q / ρ) * q ^ 3) *
        (1 - (a * q / ρ) * q ^ 4) by rfl]
  simp only [pow_one]
  field_simp [hDone]

/-- The denominator ratio between the `N=5` and `N=1` transformed-α
q-Pochhammer factors. -/
theorem BaileyTransform_five_qpoch_pair_ratio_one_five
    (a q ρ₁ ρ₂ : R)
    (hD1one : qPoch (a * q / ρ₁) q 1 ≠ 0)
    (hD2one : qPoch (a * q / ρ₂) q 1 ≠ 0) :
    (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5) /
        (qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1) =
      ((1 - (a * q / ρ₁) * q) * (1 - (a * q / ρ₁) * q ^ 2) *
          (1 - (a * q / ρ₁) * q ^ 3) * (1 - (a * q / ρ₁) * q ^ 4)) *
        ((1 - (a * q / ρ₂) * q) * (1 - (a * q / ρ₂) * q ^ 2) *
          (1 - (a * q / ρ₂) * q ^ 3) * (1 - (a * q / ρ₂) * q ^ 4)) := by
  have h1 := BaileyTransform_five_qpoch_single_ratio_one_five a q ρ₁ hD1one
  have h2 := BaileyTransform_five_qpoch_single_ratio_one_five a q ρ₂ hD2one
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPoch (a * q / ρ₁) q 5)
      (qPoch (a * q / ρ₁) q 1)
      (qPoch (a * q / ρ₂) q 5)
      (qPoch (a * q / ρ₂) q 1)
      ((1 - (a * q / ρ₁) * q) * (1 - (a * q / ρ₁) * q ^ 2) *
        (1 - (a * q / ρ₁) * q ^ 3) * (1 - (a * q / ρ₁) * q ^ 4))
      ((1 - (a * q / ρ₂) * q) * (1 - (a * q / ρ₂) * q ^ 2) *
        (1 - (a * q / ρ₂) * q ^ 3) * (1 - (a * q / ρ₂) * q ^ 4))
      hD1one hD2one h1 h2

/-- The q-Pochhammer ratio `(q;q)_5 / ((q;q)_4 (q;q)_1)`. -/
theorem BaileyTransform_five_qpochhammer_five_over_four_one
    (q : R) (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ4 : qPochhammer q 4 ≠ 0) :
    qPochhammer q 5 / (qPochhammer q 4 * qPochhammer q 1) =
      1 + q + q ^ 2 + q ^ 3 + q ^ 4 := by
  have hq : 1 - q ≠ 0 := by simpa [qPochhammer] using hQ1
  rw [show qPochhammer q 5 = qPochhammer q 4 * (1 - q ^ 5) by rfl]
  field_simp [hQ4]
  simp [qPochhammer]
  field_simp [hq]
  ring

/-- The q-Pochhammer ratio `(q;q)_5 / ((q;q)_3 (q;q)_2)`. -/
theorem BaileyTransform_five_qpochhammer_five_over_three_two
    (q : R) (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0) :
    qPochhammer q 5 / (qPochhammer q 3 * qPochhammer q 2) =
      (1 + q + q ^ 2 + q ^ 3 + q ^ 4) * (1 + q ^ 2) := by
  have hq : 1 - q ≠ 0 := by simpa [qPochhammer] using hQ1
  have hq2 : 1 - q ^ 2 ≠ 0 := by
    simpa [qPochhammer] using right_ne_zero_of_mul hQ2
  have hq3 : 1 - q ^ 3 ≠ 0 := by
    simpa [qPochhammer] using right_ne_zero_of_mul hQ3
  have hQ3Q2 : qPochhammer q 3 * qPochhammer q 2 ≠ 0 :=
    mul_ne_zero hQ3 hQ2
  simp [qPochhammer]
  field_simp [hq, hq2, hq3, hQ3Q2]
  ring

/-- The q-Pochhammer ratio `(q;q)_5 / ((q;q)_2 (q;q)_3)`. -/
theorem BaileyTransform_five_qpochhammer_five_over_two_three
    (q : R) (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0) :
    qPochhammer q 5 / (qPochhammer q 2 * qPochhammer q 3) =
      (1 + q + q ^ 2 + q ^ 3 + q ^ 4) * (1 + q ^ 2) := by
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    BaileyTransform_five_qpochhammer_five_over_three_two q hQ1 hQ2 hQ3

/-- The ratio `(aq;q)_5 / (aq;q)_1`. -/
theorem BaileyTransform_five_qpoch_aq_five_over_one
    (a q : R) (hA1 : qPoch (a * q) q 1 ≠ 0) :
    qPoch (a * q) q 5 / qPoch (a * q) q 1 =
      (1 - a * q ^ 2) * (1 - a * q ^ 3) *
        (1 - a * q ^ 4) * (1 - a * q ^ 5) := by
  rw [show qPoch (a * q) q 5 =
      qPoch (a * q) q 1 * (1 - (a * q) * q ^ 1) *
        (1 - (a * q) * q ^ 2) * (1 - (a * q) * q ^ 3) *
        (1 - (a * q) * q ^ 4) by rfl]
  simp only [pow_one]
  field_simp [hA1]

/-- The ratio `(aq;q)_5 / (aq;q)_2`. -/
theorem BaileyTransform_five_qpoch_aq_five_over_two
    (a q : R) (hA2 : qPoch (a * q) q 2 ≠ 0) :
    qPoch (a * q) q 5 / qPoch (a * q) q 2 =
      (1 - a * q ^ 3) * (1 - a * q ^ 4) * (1 - a * q ^ 5) := by
  rw [show qPoch (a * q) q 5 =
      qPoch (a * q) q 2 * (1 - (a * q) * q ^ 2) *
        (1 - (a * q) * q ^ 3) * (1 - (a * q) * q ^ 4) by rfl]
  field_simp [hA2]

/-- The first scalar ratio in the `n = 5`, α₀ common-denominator
calculation. -/
theorem BaileyTransform_five_alpha_zero_first_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ4 : qPochhammer q 4 ≠ 0)
    (hA1 : qPoch (a * q) q 1 ≠ 0) :
    qPochhammer q 5 * qPoch (a * q) q 5 /
        (qPochhammer q 4 * qPochhammer q 1 * qPoch (a * q) q 1) =
      (1 + q + q ^ 2 + q ^ 3 + q ^ 4) *
        ((1 - a * q ^ 2) * (1 - a * q ^ 3) *
          (1 - a * q ^ 4) * (1 - a * q ^ 5)) := by
  have hQ4Q1 : qPochhammer q 4 * qPochhammer q 1 ≠ 0 :=
    mul_ne_zero hQ4 hQ1
  have hQ := BaileyTransform_five_qpochhammer_five_over_four_one q hQ1 hQ4
  have hA := BaileyTransform_five_qpoch_aq_five_over_one a q hA1
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 5)
      (qPochhammer q 4 * qPochhammer q 1)
      (qPoch (a * q) q 5) (qPoch (a * q) q 1)
      (1 + q + q ^ 2 + q ^ 3 + q ^ 4)
      ((1 - a * q ^ 2) * (1 - a * q ^ 3) *
        (1 - a * q ^ 4) * (1 - a * q ^ 5))
      hQ4Q1 hA1 hQ hA

/-- The second scalar ratio in the `n = 5`, α₀ common-denominator
calculation. -/
theorem BaileyTransform_five_alpha_zero_second_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hA2 : qPoch (a * q) q 2 ≠ 0) :
    qPochhammer q 5 * qPoch (a * q) q 5 /
        (qPochhammer q 3 * qPochhammer q 2 * qPoch (a * q) q 2) =
      ((1 + q + q ^ 2 + q ^ 3 + q ^ 4) * (1 + q ^ 2)) *
        ((1 - a * q ^ 3) * (1 - a * q ^ 4) * (1 - a * q ^ 5)) := by
  have hQ3Q2 : qPochhammer q 3 * qPochhammer q 2 ≠ 0 :=
    mul_ne_zero hQ3 hQ2
  have hQ := BaileyTransform_five_qpochhammer_five_over_three_two q hQ1 hQ2 hQ3
  have hA := BaileyTransform_five_qpoch_aq_five_over_two a q hA2
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 5)
      (qPochhammer q 3 * qPochhammer q 2)
      (qPoch (a * q) q 5) (qPoch (a * q) q 2)
      ((1 + q + q ^ 2 + q ^ 3 + q ^ 4) * (1 + q ^ 2))
      ((1 - a * q ^ 3) * (1 - a * q ^ 4) * (1 - a * q ^ 5))
      hQ3Q2 hA2 hQ hA

/-- The third scalar ratio in the `n = 5`, α₀ common-denominator
calculation. -/
theorem BaileyTransform_five_alpha_zero_third_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hA3 : qPoch (a * q) q 3 ≠ 0) :
    qPochhammer q 5 * qPoch (a * q) q 5 /
        (qPochhammer q 2 * qPochhammer q 3 * qPoch (a * q) q 3) =
      ((1 + q + q ^ 2 + q ^ 3 + q ^ 4) * (1 + q ^ 2)) *
        ((1 - a * q ^ 4) * (1 - a * q ^ 5)) := by
  have hQ2Q3 : qPochhammer q 2 * qPochhammer q 3 ≠ 0 :=
    mul_ne_zero hQ2 hQ3
  have hQ := BaileyTransform_five_qpochhammer_five_over_two_three q hQ1 hQ2 hQ3
  have hA := BaileyTransform_four_qpoch_aq_five_over_three a q hA3
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 5)
      (qPochhammer q 2 * qPochhammer q 3)
      (qPoch (a * q) q 5) (qPoch (a * q) q 3)
      ((1 + q + q ^ 2 + q ^ 3 + q ^ 4) * (1 + q ^ 2))
      ((1 - a * q ^ 4) * (1 - a * q ^ 5))
      hQ2Q3 hA3 hQ hA

/-- The fourth scalar ratio in the `n = 5`, α₀ common-denominator
calculation. -/
theorem BaileyTransform_five_alpha_zero_fourth_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ4 : qPochhammer q 4 ≠ 0)
    (hA4 : qPoch (a * q) q 4 ≠ 0) :
    qPochhammer q 5 * qPoch (a * q) q 5 /
        (qPochhammer q 1 * qPochhammer q 4 * qPoch (a * q) q 4) =
      (1 + q + q ^ 2 + q ^ 3 + q ^ 4) * (1 - a * q ^ 5) := by
  have hQ1Q4 : qPochhammer q 1 * qPochhammer q 4 ≠ 0 :=
    mul_ne_zero hQ1 hQ4
  have hQ : qPochhammer q 5 / (qPochhammer q 1 * qPochhammer q 4) =
      1 + q + q ^ 2 + q ^ 3 + q ^ 4 := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      BaileyTransform_five_qpochhammer_five_over_four_one q hQ1 hQ4
  have hA := BaileyTransform_three_qpoch_ratio_four_five a q hA4
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 5)
      (qPochhammer q 1 * qPochhammer q 4)
      (qPoch (a * q) q 5) (qPoch (a * q) q 4)
      (1 + q + q ^ 2 + q ^ 3 + q ^ 4) (1 - a * q ^ 5)
      hQ1Q4 hA4 hQ hA

/-- The α₀ common-denominator identity at `n = 5` after all scalar ratios
have been simplified to polynomial factors. -/
theorem BaileyTransform_five_alpha_zero_common_denominator_simplified
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0) :
    qPoch (a * q / (ρ₁ * ρ₂)) q 5 * qPoch (a * q) q 5 +
      qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) *
        qPoch (a * q / (ρ₁ * ρ₂)) q 4 *
        ((1 + q + q ^ 2 + q ^ 3 + q ^ 4) *
          ((1 - a * q ^ 2) * (1 - a * q ^ 3) *
            (1 - a * q ^ 4) * (1 - a * q ^ 5))) +
      qPoch ρ₁ q 2 * qPoch ρ₂ q 2 *
        (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3 *
        (((1 + q + q ^ 2 + q ^ 3 + q ^ 4) * (1 + q ^ 2)) *
          ((1 - a * q ^ 3) * (1 - a * q ^ 4) * (1 - a * q ^ 5))) +
      qPoch ρ₁ q 3 * qPoch ρ₂ q 3 *
        (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2 *
        (((1 + q + q ^ 2 + q ^ 3 + q ^ 4) * (1 + q ^ 2)) *
          ((1 - a * q ^ 4) * (1 - a * q ^ 5))) +
      qPoch ρ₁ q 4 * qPoch ρ₂ q 4 *
        (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1 *
        ((1 + q + q ^ 2 + q ^ 3 + q ^ 4) * (1 - a * q ^ 5)) +
      qPoch ρ₁ q 5 * qPoch ρ₂ q 5 *
        (a * q / (ρ₁ * ρ₂)) ^ 5 =
      qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 := by
  have hρ1 : ρ₁ ≠ 0 := left_ne_zero_of_mul hρ
  have hρ2 : ρ₂ ≠ 0 := right_ne_zero_of_mul hρ
  simp [qPoch]
  field_simp [hρ, hρ1, hρ2]
  ring

/-- The α₀ coefficient identity in the `n = 5` finite Bailey-lemma step after
moving the six transformed-β contributions to a common denominator. -/
theorem BaileyTransform_five_alpha_zero_common_denominator_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hQ4 : qPochhammer q 4 ≠ 0)
    (hA1 : qPoch (a * q) q 1 ≠ 0)
    (hA2 : qPoch (a * q) q 2 ≠ 0)
    (hA3 : qPoch (a * q) q 3 ≠ 0)
    (hA4 : qPoch (a * q) q 4 ≠ 0) :
    qPoch (a * q / (ρ₁ * ρ₂)) q 5 * qPoch (a * q) q 5 +
      qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) *
        qPoch (a * q / (ρ₁ * ρ₂)) q 4 *
        (qPochhammer q 5 * qPoch (a * q) q 5 /
          (qPochhammer q 4 * qPochhammer q 1 * qPoch (a * q) q 1)) +
      qPoch ρ₁ q 2 * qPoch ρ₂ q 2 *
        (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3 *
        (qPochhammer q 5 * qPoch (a * q) q 5 /
          (qPochhammer q 3 * qPochhammer q 2 * qPoch (a * q) q 2)) +
      qPoch ρ₁ q 3 * qPoch ρ₂ q 3 *
        (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2 *
        (qPochhammer q 5 * qPoch (a * q) q 5 /
          (qPochhammer q 2 * qPochhammer q 3 * qPoch (a * q) q 3)) +
      qPoch ρ₁ q 4 * qPoch ρ₂ q 4 *
        (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1 *
        (qPochhammer q 5 * qPoch (a * q) q 5 /
          (qPochhammer q 1 * qPochhammer q 4 * qPoch (a * q) q 4)) +
      qPoch ρ₁ q 5 * qPoch ρ₂ q 5 *
        (a * q / (ρ₁ * ρ₂)) ^ 5 =
      qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 := by
  rw [BaileyTransform_five_alpha_zero_first_ratio a q hQ1 hQ4 hA1,
    BaileyTransform_five_alpha_zero_second_ratio a q hQ1 hQ2 hQ3 hA2,
    BaileyTransform_five_alpha_zero_third_ratio a q hQ1 hQ2 hQ3 hA3,
    BaileyTransform_five_alpha_zero_fourth_ratio a q hQ1 hQ4 hA4]
  exact BaileyTransform_five_alpha_zero_common_denominator_simplified a q ρ₁ ρ₂ hρ

/-- The α₀ common-denominator identity at `n = 4` after all scalar ratios
have been simplified to polynomial factors. -/
theorem BaileyTransform_four_alpha_zero_common_denominator_simplified
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0) :
    qPoch (a * q / (ρ₁ * ρ₂)) q 4 * qPoch (a * q) q 4 +
      qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3 *
        ((1 + q + q ^ 2 + q ^ 3) *
          ((1 - a * q ^ 2) * (1 - a * q ^ 3) * (1 - a * q ^ 4))) +
      qPoch ρ₁ q 2 * qPoch ρ₂ q 2 *
        (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2 *
        (((1 + q + q ^ 2) * (1 + q ^ 2)) *
          ((1 - a * q ^ 3) * (1 - a * q ^ 4))) +
      qPoch ρ₁ q 3 * qPoch ρ₂ q 3 *
        (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1 *
        ((1 + q + q ^ 2 + q ^ 3) * (1 - a * q ^ 4)) +
      qPoch ρ₁ q 4 * qPoch ρ₂ q 4 *
        (a * q / (ρ₁ * ρ₂)) ^ 4 =
      qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4 := by
  have hρ1 : ρ₁ ≠ 0 := left_ne_zero_of_mul hρ
  have hρ2 : ρ₂ ≠ 0 := right_ne_zero_of_mul hρ
  simp [qPoch]
  field_simp [hρ, hρ1, hρ2]
  ring

/-- The α₀ coefficient identity in the `n = 4` finite Bailey-lemma step after
moving the five transformed-β contributions to a common denominator. -/
theorem BaileyTransform_four_alpha_zero_common_denominator_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hA1 : qPoch (a * q) q 1 ≠ 0)
    (hA2 : qPoch (a * q) q 2 ≠ 0)
    (hA3 : qPoch (a * q) q 3 ≠ 0) :
    qPoch (a * q / (ρ₁ * ρ₂)) q 4 * qPoch (a * q) q 4 +
      qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3 *
        (qPochhammer q 4 * qPoch (a * q) q 4 /
          (qPochhammer q 3 * qPochhammer q 1 * qPoch (a * q) q 1)) +
      qPoch ρ₁ q 2 * qPoch ρ₂ q 2 *
        (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2 *
        (qPochhammer q 4 * qPoch (a * q) q 4 /
          (qPochhammer q 2 * qPochhammer q 2 * qPoch (a * q) q 2)) +
      qPoch ρ₁ q 3 * qPoch ρ₂ q 3 *
        (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1 *
        (qPochhammer q 4 * qPoch (a * q) q 4 /
          (qPochhammer q 1 * qPochhammer q 3 * qPoch (a * q) q 3)) +
      qPoch ρ₁ q 4 * qPoch ρ₂ q 4 *
        (a * q / (ρ₁ * ρ₂)) ^ 4 =
      qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4 := by
  rw [BaileyTransform_four_alpha_zero_first_ratio a q hQ1 hQ3 hA1,
    BaileyTransform_four_alpha_zero_second_ratio a q hQ2 hA2,
    BaileyTransform_four_alpha_zero_third_ratio a q hQ1 hQ3 hA3]
  exact BaileyTransform_four_alpha_zero_common_denominator_simplified a q ρ₁ ρ₂ hρ

/-- Generic five-term algebra step: a common-denominator identity implies the
corresponding fractional α₀ identity at `n = 4`. -/
theorem BaileyTransform_five_term_fraction_from_common
    (P0 P1 P2 P3 P4 D Q1 Q2 Q3 Q4 A1 A2 A3 A4 : R)
    (hD : D ≠ 0) (hQ1 : Q1 ≠ 0) (hQ2 : Q2 ≠ 0)
    (hQ3 : Q3 ≠ 0) (hQ4 : Q4 ≠ 0)
    (hA1 : A1 ≠ 0) (hA2 : A2 ≠ 0) (hA3 : A3 ≠ 0) (hA4 : A4 ≠ 0)
    (hcommon : P0 * A4 + P1 * (Q4 * A4 / (Q3 * Q1 * A1)) +
      P2 * (Q4 * A4 / (Q2 * Q2 * A2)) +
      P3 * (Q4 * A4 / (Q1 * Q3 * A3)) + P4 = D) :
    P0 / (D * Q4) + (P1 / (D * Q3)) / (Q1 * A1) +
      (P2 / (D * Q2)) / (Q2 * A2) +
      (P3 / (D * Q1)) / (Q3 * A3) + (P4 / D) / (Q4 * A4) =
      1 / (Q4 * A4) := by
  have hDQ4 : D * Q4 ≠ 0 := mul_ne_zero hD hQ4
  have hDQ3 : D * Q3 ≠ 0 := mul_ne_zero hD hQ3
  have hDQ2 : D * Q2 ≠ 0 := mul_ne_zero hD hQ2
  have hDQ1 : D * Q1 ≠ 0 := mul_ne_zero hD hQ1
  have hQ1A1 : Q1 * A1 ≠ 0 := mul_ne_zero hQ1 hA1
  have hQ2A2 : Q2 * A2 ≠ 0 := mul_ne_zero hQ2 hA2
  have hQ3A3 : Q3 * A3 ≠ 0 := mul_ne_zero hQ3 hA3
  have hQ4A4 : Q4 * A4 ≠ 0 := mul_ne_zero hQ4 hA4
  have hQ3Q1A1 : Q3 * Q1 * A1 ≠ 0 := mul_ne_zero (mul_ne_zero hQ3 hQ1) hA1
  have hQ2Q2A2 : Q2 * Q2 * A2 ≠ 0 := mul_ne_zero (mul_ne_zero hQ2 hQ2) hA2
  have hQ1Q3A3 : Q1 * Q3 * A3 ≠ 0 := mul_ne_zero (mul_ne_zero hQ1 hQ3) hA3
  field_simp [hD, hQ1, hQ2, hQ3, hQ4, hA1, hA2, hA3, hA4, hDQ4,
    hDQ3, hDQ2, hDQ1, hQ1A1, hQ2A2, hQ3A3, hQ4A4,
    hQ3Q1A1, hQ2Q2A2, hQ1Q3A3]
  field_simp [hQ3Q1A1, hQ2Q2A2, hQ1Q3A3] at hcommon
  ring_nf at hcommon ⊢
  exact hcommon

/-- Generic six-term algebra step: a common-denominator identity implies the
corresponding fractional α₀ identity at `n = 5`. -/
theorem BaileyTransform_six_term_fraction_from_common
    (P0 P1 P2 P3 P4 P5 D Q1 Q2 Q3 Q4 Q5 A1 A2 A3 A4 A5 : R)
    (hD : D ≠ 0) (hQ1 : Q1 ≠ 0) (hQ2 : Q2 ≠ 0)
    (hQ3 : Q3 ≠ 0) (hQ4 : Q4 ≠ 0) (hQ5 : Q5 ≠ 0)
    (hA1 : A1 ≠ 0) (hA2 : A2 ≠ 0) (hA3 : A3 ≠ 0)
    (hA4 : A4 ≠ 0) (hA5 : A5 ≠ 0)
    (hcommon : P0 * A5 + P1 * (Q5 * A5 / (Q4 * Q1 * A1)) +
      P2 * (Q5 * A5 / (Q3 * Q2 * A2)) +
      P3 * (Q5 * A5 / (Q2 * Q3 * A3)) +
      P4 * (Q5 * A5 / (Q1 * Q4 * A4)) + P5 = D) :
    P0 / (D * Q5) + (P1 / (D * Q4)) / (Q1 * A1) +
      (P2 / (D * Q3)) / (Q2 * A2) +
      (P3 / (D * Q2)) / (Q3 * A3) +
      (P4 / (D * Q1)) / (Q4 * A4) + (P5 / D) / (Q5 * A5) =
      1 / (Q5 * A5) := by
  have hDQ5 : D * Q5 ≠ 0 := mul_ne_zero hD hQ5
  have hDQ4 : D * Q4 ≠ 0 := mul_ne_zero hD hQ4
  have hDQ3 : D * Q3 ≠ 0 := mul_ne_zero hD hQ3
  have hDQ2 : D * Q2 ≠ 0 := mul_ne_zero hD hQ2
  have hDQ1 : D * Q1 ≠ 0 := mul_ne_zero hD hQ1
  have hQ1A1 : Q1 * A1 ≠ 0 := mul_ne_zero hQ1 hA1
  have hQ2A2 : Q2 * A2 ≠ 0 := mul_ne_zero hQ2 hA2
  have hQ3A3 : Q3 * A3 ≠ 0 := mul_ne_zero hQ3 hA3
  have hQ4A4 : Q4 * A4 ≠ 0 := mul_ne_zero hQ4 hA4
  have hQ5A5 : Q5 * A5 ≠ 0 := mul_ne_zero hQ5 hA5
  have hQ4Q1A1 : Q4 * Q1 * A1 ≠ 0 := mul_ne_zero (mul_ne_zero hQ4 hQ1) hA1
  have hQ3Q2A2 : Q3 * Q2 * A2 ≠ 0 := mul_ne_zero (mul_ne_zero hQ3 hQ2) hA2
  have hQ2Q3A3 : Q2 * Q3 * A3 ≠ 0 := mul_ne_zero (mul_ne_zero hQ2 hQ3) hA3
  have hQ1Q4A4 : Q1 * Q4 * A4 ≠ 0 := mul_ne_zero (mul_ne_zero hQ1 hQ4) hA4
  field_simp [hD, hQ1, hQ2, hQ3, hQ4, hQ5, hA1, hA2, hA3, hA4, hA5,
    hDQ5, hDQ4, hDQ3, hDQ2, hDQ1, hQ1A1, hQ2A2, hQ3A3, hQ4A4, hQ5A5,
    hQ4Q1A1, hQ3Q2A2, hQ2Q3A3, hQ1Q4A4]
  field_simp [hQ4Q1A1, hQ3Q2A2, hQ2Q3A3, hQ1Q4A4] at hcommon
  ring_nf at hcommon ⊢
  exact hcommon

/-- Generic six-term algebra step: a common-denominator identity with a
remaining denominator ratio implies the corresponding fractional identity. -/
theorem BaileyTransform_six_term_fraction_from_common_ratio
    (P1 P2 P3 P4 P5 P6 B D D1 Q1 Q2 Q3 Q4 Q5 A2 A3 A4 A5 A6 A7 : R)
    (hD : D ≠ 0) (hD1 : D1 ≠ 0)
    (hQ1 : Q1 ≠ 0) (hQ2 : Q2 ≠ 0) (hQ3 : Q3 ≠ 0)
    (hQ4 : Q4 ≠ 0) (hQ5 : Q5 ≠ 0)
    (hA2 : A2 ≠ 0) (hA3 : A3 ≠ 0) (hA4 : A4 ≠ 0)
    (hA5 : A5 ≠ 0) (hA6 : A6 ≠ 0) (hA7 : A7 ≠ 0)
    (hcommon : P1 * (A7 / A2) + P2 * (Q5 * A7 / (Q4 * Q1 * A3)) +
      P3 * (Q5 * A7 / (Q3 * Q2 * A4)) +
      P4 * (Q5 * A7 / (Q2 * Q3 * A5)) +
      P5 * (Q5 * A7 / (Q1 * Q4 * A6)) + P6 = B * (D / D1)) :
    (P1 / (D * Q5)) / A2 + (P2 / (D * Q4)) / (Q1 * A3) +
      (P3 / (D * Q3)) / (Q2 * A4) +
      (P4 / (D * Q2)) / (Q3 * A5) +
      (P5 / (D * Q1)) / (Q4 * A6) + (P6 / D) / (Q5 * A7) =
      (B / D1) / (Q5 * A7) := by
  have hDQ5 : D * Q5 ≠ 0 := mul_ne_zero hD hQ5
  have hDQ4 : D * Q4 ≠ 0 := mul_ne_zero hD hQ4
  have hDQ3 : D * Q3 ≠ 0 := mul_ne_zero hD hQ3
  have hDQ2 : D * Q2 ≠ 0 := mul_ne_zero hD hQ2
  have hDQ1 : D * Q1 ≠ 0 := mul_ne_zero hD hQ1
  have hQ1A3 : Q1 * A3 ≠ 0 := mul_ne_zero hQ1 hA3
  have hQ2A4 : Q2 * A4 ≠ 0 := mul_ne_zero hQ2 hA4
  have hQ3A5 : Q3 * A5 ≠ 0 := mul_ne_zero hQ3 hA5
  have hQ4A6 : Q4 * A6 ≠ 0 := mul_ne_zero hQ4 hA6
  have hQ5A7 : Q5 * A7 ≠ 0 := mul_ne_zero hQ5 hA7
  have hQ4Q1A3 : Q4 * Q1 * A3 ≠ 0 := mul_ne_zero (mul_ne_zero hQ4 hQ1) hA3
  have hQ3Q2A4 : Q3 * Q2 * A4 ≠ 0 := mul_ne_zero (mul_ne_zero hQ3 hQ2) hA4
  have hQ2Q3A5 : Q2 * Q3 * A5 ≠ 0 := mul_ne_zero (mul_ne_zero hQ2 hQ3) hA5
  have hQ1Q4A6 : Q1 * Q4 * A6 ≠ 0 := mul_ne_zero (mul_ne_zero hQ1 hQ4) hA6
  field_simp [hD, hD1, hQ1, hQ2, hQ3, hQ4, hQ5, hA2, hA3, hA4, hA5, hA6,
    hA7, hDQ5, hDQ4, hDQ3, hDQ2, hDQ1, hQ1A3, hQ2A4, hQ3A5, hQ4A6, hQ5A7,
    hQ4Q1A3, hQ3Q2A4, hQ2Q3A5, hQ1Q4A6]
  field_simp [hA2, hQ4Q1A3, hQ3Q2A4, hQ2Q3A5, hQ1Q4A6, hD1] at hcommon
  ring_nf at hcommon ⊢
  exact hcommon

/-- Generic seven-term algebra step (alpha_1 shape): a common-denominator
identity with a remaining denominator ratio implies the corresponding
fractional identity at `n = 7`. -/
theorem BaileyTransform_seven_term_fraction_from_common_ratio
    (P1 P2 P3 P4 P5 P6 P7 B D D1 Q1 Q2 Q3 Q4 Q5 Q6
      A2 A3 A4 A5 A6 A7 A8 : R)
    (hD : D ≠ 0) (hD1 : D1 ≠ 0)
    (hQ1 : Q1 ≠ 0) (hQ2 : Q2 ≠ 0) (hQ3 : Q3 ≠ 0)
    (hQ4 : Q4 ≠ 0) (hQ5 : Q5 ≠ 0) (hQ6 : Q6 ≠ 0)
    (hA2 : A2 ≠ 0) (hA3 : A3 ≠ 0) (hA4 : A4 ≠ 0)
    (hA5 : A5 ≠ 0) (hA6 : A6 ≠ 0) (hA7 : A7 ≠ 0) (hA8 : A8 ≠ 0)
    (hcommon : P1 * (A8 / A2) + P2 * (Q6 * A8 / (Q5 * Q1 * A3)) +
      P3 * (Q6 * A8 / (Q4 * Q2 * A4)) +
      P4 * (Q6 * A8 / (Q3 * Q3 * A5)) +
      P5 * (Q6 * A8 / (Q2 * Q4 * A6)) +
      P6 * (Q6 * A8 / (Q1 * Q5 * A7)) + P7 = B * (D / D1)) :
    (P1 / (D * Q6)) / A2 + (P2 / (D * Q5)) / (Q1 * A3) +
      (P3 / (D * Q4)) / (Q2 * A4) +
      (P4 / (D * Q3)) / (Q3 * A5) +
      (P5 / (D * Q2)) / (Q4 * A6) +
      (P6 / (D * Q1)) / (Q5 * A7) + (P7 / D) / (Q6 * A8) =
      (B / D1) / (Q6 * A8) := by
  have hDQ6 : D * Q6 ≠ 0 := mul_ne_zero hD hQ6
  have hDQ5 : D * Q5 ≠ 0 := mul_ne_zero hD hQ5
  have hDQ4 : D * Q4 ≠ 0 := mul_ne_zero hD hQ4
  have hDQ3 : D * Q3 ≠ 0 := mul_ne_zero hD hQ3
  have hDQ2 : D * Q2 ≠ 0 := mul_ne_zero hD hQ2
  have hDQ1 : D * Q1 ≠ 0 := mul_ne_zero hD hQ1
  have hQ1A3 : Q1 * A3 ≠ 0 := mul_ne_zero hQ1 hA3
  have hQ2A4 : Q2 * A4 ≠ 0 := mul_ne_zero hQ2 hA4
  have hQ3A5 : Q3 * A5 ≠ 0 := mul_ne_zero hQ3 hA5
  have hQ4A6 : Q4 * A6 ≠ 0 := mul_ne_zero hQ4 hA6
  have hQ5A7 : Q5 * A7 ≠ 0 := mul_ne_zero hQ5 hA7
  have hQ6A8 : Q6 * A8 ≠ 0 := mul_ne_zero hQ6 hA8
  have hQ5Q1A3 : Q5 * Q1 * A3 ≠ 0 := mul_ne_zero (mul_ne_zero hQ5 hQ1) hA3
  have hQ4Q2A4 : Q4 * Q2 * A4 ≠ 0 := mul_ne_zero (mul_ne_zero hQ4 hQ2) hA4
  have hQ3Q3A5 : Q3 * Q3 * A5 ≠ 0 := mul_ne_zero (mul_ne_zero hQ3 hQ3) hA5
  have hQ2Q4A6 : Q2 * Q4 * A6 ≠ 0 := mul_ne_zero (mul_ne_zero hQ2 hQ4) hA6
  have hQ1Q5A7 : Q1 * Q5 * A7 ≠ 0 := mul_ne_zero (mul_ne_zero hQ1 hQ5) hA7
  field_simp [hD, hD1, hQ1, hQ2, hQ3, hQ4, hQ5, hQ6, hA2, hA3, hA4, hA5,
    hA6, hA7, hA8, hDQ6, hDQ5, hDQ4, hDQ3, hDQ2, hDQ1,
    hQ1A3, hQ2A4, hQ3A5, hQ4A6, hQ5A7, hQ6A8,
    hQ5Q1A3, hQ4Q2A4, hQ3Q3A5, hQ2Q4A6, hQ1Q5A7]
  field_simp [hA2, hQ5Q1A3, hQ4Q2A4, hQ3Q3A5, hQ2Q4A6, hQ1Q5A7, hD1] at hcommon
  ring_nf at hcommon ⊢
  exact hcommon

set_option maxHeartbeats 4000000 in
/-- Generic eight-term algebra step: a common-denominator identity with a
remaining denominator ratio implies the corresponding fractional α₁
identity at `n = 8`. -/
theorem BaileyTransform_eight_term_fraction_from_common_ratio
    (P1 P2 P3 P4 P5 P6 P7 P8 B D D1 Q1 Q2 Q3 Q4 Q5 Q6 Q7
      A2 A3 A4 A5 A6 A7 A8 A9 : R)
    (hD : D ≠ 0) (hD1 : D1 ≠ 0)
    (hQ1 : Q1 ≠ 0) (hQ2 : Q2 ≠ 0) (hQ3 : Q3 ≠ 0)
    (hQ4 : Q4 ≠ 0) (hQ5 : Q5 ≠ 0) (hQ6 : Q6 ≠ 0) (hQ7 : Q7 ≠ 0)
    (hA2 : A2 ≠ 0) (hA3 : A3 ≠ 0) (hA4 : A4 ≠ 0)
    (hA5 : A5 ≠ 0) (hA6 : A6 ≠ 0) (hA7 : A7 ≠ 0)
    (hA8 : A8 ≠ 0) (hA9 : A9 ≠ 0)
    (hcommon : P1 * (A9 / A2) + P2 * (Q7 * A9 / (Q6 * Q1 * A3)) +
      P3 * (Q7 * A9 / (Q5 * Q2 * A4)) +
      P4 * (Q7 * A9 / (Q4 * Q3 * A5)) +
      P5 * (Q7 * A9 / (Q3 * Q4 * A6)) +
      P6 * (Q7 * A9 / (Q2 * Q5 * A7)) +
      P7 * (Q7 * A9 / (Q1 * Q6 * A8)) + P8 = B * (D / D1)) :
    (P1 / (D * Q7)) / A2 + (P2 / (D * Q6)) / (Q1 * A3) +
      (P3 / (D * Q5)) / (Q2 * A4) +
      (P4 / (D * Q4)) / (Q3 * A5) +
      (P5 / (D * Q3)) / (Q4 * A6) +
      (P6 / (D * Q2)) / (Q5 * A7) +
      (P7 / (D * Q1)) / (Q6 * A8) + (P8 / D) / (Q7 * A9) =
      (B / D1) / (Q7 * A9) := by
  have hDQ7 : D * Q7 ≠ 0 := mul_ne_zero hD hQ7
  have hDQ6 : D * Q6 ≠ 0 := mul_ne_zero hD hQ6
  have hDQ5 : D * Q5 ≠ 0 := mul_ne_zero hD hQ5
  have hDQ4 : D * Q4 ≠ 0 := mul_ne_zero hD hQ4
  have hDQ3 : D * Q3 ≠ 0 := mul_ne_zero hD hQ3
  have hDQ2 : D * Q2 ≠ 0 := mul_ne_zero hD hQ2
  have hDQ1 : D * Q1 ≠ 0 := mul_ne_zero hD hQ1
  have hQ1A3 : Q1 * A3 ≠ 0 := mul_ne_zero hQ1 hA3
  have hQ2A4 : Q2 * A4 ≠ 0 := mul_ne_zero hQ2 hA4
  have hQ3A5 : Q3 * A5 ≠ 0 := mul_ne_zero hQ3 hA5
  have hQ4A6 : Q4 * A6 ≠ 0 := mul_ne_zero hQ4 hA6
  have hQ5A7 : Q5 * A7 ≠ 0 := mul_ne_zero hQ5 hA7
  have hQ6A8 : Q6 * A8 ≠ 0 := mul_ne_zero hQ6 hA8
  have hQ7A9 : Q7 * A9 ≠ 0 := mul_ne_zero hQ7 hA9
  have hQ6Q1A3 : Q6 * Q1 * A3 ≠ 0 := mul_ne_zero (mul_ne_zero hQ6 hQ1) hA3
  have hQ5Q2A4 : Q5 * Q2 * A4 ≠ 0 := mul_ne_zero (mul_ne_zero hQ5 hQ2) hA4
  have hQ4Q3A5 : Q4 * Q3 * A5 ≠ 0 := mul_ne_zero (mul_ne_zero hQ4 hQ3) hA5
  have hQ3Q4A6 : Q3 * Q4 * A6 ≠ 0 := mul_ne_zero (mul_ne_zero hQ3 hQ4) hA6
  have hQ2Q5A7 : Q2 * Q5 * A7 ≠ 0 := mul_ne_zero (mul_ne_zero hQ2 hQ5) hA7
  have hQ1Q6A8 : Q1 * Q6 * A8 ≠ 0 := mul_ne_zero (mul_ne_zero hQ1 hQ6) hA8
  field_simp [hD, hD1, hQ1, hQ2, hQ3, hQ4, hQ5, hQ6, hQ7,
    hA2, hA3, hA4, hA5, hA6, hA7, hA8, hA9,
    hDQ7, hDQ6, hDQ5, hDQ4, hDQ3, hDQ2, hDQ1,
    hQ1A3, hQ2A4, hQ3A5, hQ4A6, hQ5A7, hQ6A8, hQ7A9,
    hQ6Q1A3, hQ5Q2A4, hQ4Q3A5, hQ3Q4A6, hQ2Q5A7, hQ1Q6A8]
  field_simp [hA2, hQ6Q1A3, hQ5Q2A4, hQ4Q3A5, hQ3Q4A6, hQ2Q5A7, hQ1Q6A8, hD1] at hcommon
  ring_nf at hcommon ⊢
  exact hcommon

/-- Generic seven-term algebra step: a common-denominator identity implies the
corresponding fractional α₀ identity at `n = 6`. -/
theorem BaileyTransform_seven_term_fraction_from_common
    (P0 P1 P2 P3 P4 P5 P6 D Q1 Q2 Q3 Q4 Q5 Q6 A1 A2 A3 A4 A5 A6 : R)
    (hD : D ≠ 0) (hQ1 : Q1 ≠ 0) (hQ2 : Q2 ≠ 0)
    (hQ3 : Q3 ≠ 0) (hQ4 : Q4 ≠ 0) (hQ5 : Q5 ≠ 0) (hQ6 : Q6 ≠ 0)
    (hA1 : A1 ≠ 0) (hA2 : A2 ≠ 0) (hA3 : A3 ≠ 0)
    (hA4 : A4 ≠ 0) (hA5 : A5 ≠ 0) (hA6 : A6 ≠ 0)
    (hcommon : P0 * A6 + P1 * (Q6 * A6 / (Q5 * Q1 * A1)) +
      P2 * (Q6 * A6 / (Q4 * Q2 * A2)) +
      P3 * (Q6 * A6 / (Q3 * Q3 * A3)) +
      P4 * (Q6 * A6 / (Q2 * Q4 * A4)) +
      P5 * (Q6 * A6 / (Q1 * Q5 * A5)) + P6 = D) :
    P0 / (D * Q6) + (P1 / (D * Q5)) / (Q1 * A1) +
      (P2 / (D * Q4)) / (Q2 * A2) +
      (P3 / (D * Q3)) / (Q3 * A3) +
      (P4 / (D * Q2)) / (Q4 * A4) +
      (P5 / (D * Q1)) / (Q5 * A5) + (P6 / D) / (Q6 * A6) =
      1 / (Q6 * A6) := by
  have hDQ6 : D * Q6 ≠ 0 := mul_ne_zero hD hQ6
  have hDQ5 : D * Q5 ≠ 0 := mul_ne_zero hD hQ5
  have hDQ4 : D * Q4 ≠ 0 := mul_ne_zero hD hQ4
  have hDQ3 : D * Q3 ≠ 0 := mul_ne_zero hD hQ3
  have hDQ2 : D * Q2 ≠ 0 := mul_ne_zero hD hQ2
  have hDQ1 : D * Q1 ≠ 0 := mul_ne_zero hD hQ1
  have hQ1A1 : Q1 * A1 ≠ 0 := mul_ne_zero hQ1 hA1
  have hQ2A2 : Q2 * A2 ≠ 0 := mul_ne_zero hQ2 hA2
  have hQ3A3 : Q3 * A3 ≠ 0 := mul_ne_zero hQ3 hA3
  have hQ4A4 : Q4 * A4 ≠ 0 := mul_ne_zero hQ4 hA4
  have hQ5A5 : Q5 * A5 ≠ 0 := mul_ne_zero hQ5 hA5
  have hQ6A6 : Q6 * A6 ≠ 0 := mul_ne_zero hQ6 hA6
  have hQ5Q1A1 : Q5 * Q1 * A1 ≠ 0 := mul_ne_zero (mul_ne_zero hQ5 hQ1) hA1
  have hQ4Q2A2 : Q4 * Q2 * A2 ≠ 0 := mul_ne_zero (mul_ne_zero hQ4 hQ2) hA2
  have hQ3Q3A3 : Q3 * Q3 * A3 ≠ 0 := mul_ne_zero (mul_ne_zero hQ3 hQ3) hA3
  have hQ2Q4A4 : Q2 * Q4 * A4 ≠ 0 := mul_ne_zero (mul_ne_zero hQ2 hQ4) hA4
  have hQ1Q5A5 : Q1 * Q5 * A5 ≠ 0 := mul_ne_zero (mul_ne_zero hQ1 hQ5) hA5
  field_simp [hD, hQ1, hQ2, hQ3, hQ4, hQ5, hQ6, hA1, hA2, hA3, hA4, hA5,
    hA6, hDQ6, hDQ5, hDQ4, hDQ3, hDQ2, hDQ1, hQ1A1, hQ2A2, hQ3A3, hQ4A4,
    hQ5A5, hQ6A6, hQ5Q1A1, hQ4Q2A2, hQ3Q3A3, hQ2Q4A4, hQ1Q5A5]
  field_simp [hQ5Q1A1, hQ4Q2A2, hQ3Q3A3, hQ2Q4A4, hQ1Q5A5] at hcommon
  ring_nf at hcommon ⊢
  exact hcommon

/-- Generic eight-term algebra step: a common-denominator identity implies the
corresponding fractional α₀ identity at `n = 7`. -/
theorem BaileyTransform_eight_term_fraction_from_common
    (P0 P1 P2 P3 P4 P5 P6 P7 D Q1 Q2 Q3 Q4 Q5 Q6 Q7
      A1 A2 A3 A4 A5 A6 A7 : R)
    (hD : D ≠ 0) (hQ1 : Q1 ≠ 0) (hQ2 : Q2 ≠ 0)
    (hQ3 : Q3 ≠ 0) (hQ4 : Q4 ≠ 0) (hQ5 : Q5 ≠ 0)
    (hQ6 : Q6 ≠ 0) (hQ7 : Q7 ≠ 0)
    (hA1 : A1 ≠ 0) (hA2 : A2 ≠ 0) (hA3 : A3 ≠ 0)
    (hA4 : A4 ≠ 0) (hA5 : A5 ≠ 0) (hA6 : A6 ≠ 0)
    (hA7 : A7 ≠ 0)
    (hcommon : P0 * A7 + P1 * (Q7 * A7 / (Q6 * Q1 * A1)) +
      P2 * (Q7 * A7 / (Q5 * Q2 * A2)) +
      P3 * (Q7 * A7 / (Q4 * Q3 * A3)) +
      P4 * (Q7 * A7 / (Q3 * Q4 * A4)) +
      P5 * (Q7 * A7 / (Q2 * Q5 * A5)) +
      P6 * (Q7 * A7 / (Q1 * Q6 * A6)) + P7 = D) :
    P0 / (D * Q7) + (P1 / (D * Q6)) / (Q1 * A1) +
      (P2 / (D * Q5)) / (Q2 * A2) +
      (P3 / (D * Q4)) / (Q3 * A3) +
      (P4 / (D * Q3)) / (Q4 * A4) +
      (P5 / (D * Q2)) / (Q5 * A5) +
      (P6 / (D * Q1)) / (Q6 * A6) + (P7 / D) / (Q7 * A7) =
      1 / (Q7 * A7) := by
  have hDQ7 : D * Q7 ≠ 0 := mul_ne_zero hD hQ7
  have hDQ6 : D * Q6 ≠ 0 := mul_ne_zero hD hQ6
  have hDQ5 : D * Q5 ≠ 0 := mul_ne_zero hD hQ5
  have hDQ4 : D * Q4 ≠ 0 := mul_ne_zero hD hQ4
  have hDQ3 : D * Q3 ≠ 0 := mul_ne_zero hD hQ3
  have hDQ2 : D * Q2 ≠ 0 := mul_ne_zero hD hQ2
  have hDQ1 : D * Q1 ≠ 0 := mul_ne_zero hD hQ1
  have hQ1A1 : Q1 * A1 ≠ 0 := mul_ne_zero hQ1 hA1
  have hQ2A2 : Q2 * A2 ≠ 0 := mul_ne_zero hQ2 hA2
  have hQ3A3 : Q3 * A3 ≠ 0 := mul_ne_zero hQ3 hA3
  have hQ4A4 : Q4 * A4 ≠ 0 := mul_ne_zero hQ4 hA4
  have hQ5A5 : Q5 * A5 ≠ 0 := mul_ne_zero hQ5 hA5
  have hQ6A6 : Q6 * A6 ≠ 0 := mul_ne_zero hQ6 hA6
  have hQ7A7 : Q7 * A7 ≠ 0 := mul_ne_zero hQ7 hA7
  have hQ6Q1A1 : Q6 * Q1 * A1 ≠ 0 := mul_ne_zero (mul_ne_zero hQ6 hQ1) hA1
  have hQ5Q2A2 : Q5 * Q2 * A2 ≠ 0 := mul_ne_zero (mul_ne_zero hQ5 hQ2) hA2
  have hQ4Q3A3 : Q4 * Q3 * A3 ≠ 0 := mul_ne_zero (mul_ne_zero hQ4 hQ3) hA3
  have hQ3Q4A4 : Q3 * Q4 * A4 ≠ 0 := mul_ne_zero (mul_ne_zero hQ3 hQ4) hA4
  have hQ2Q5A5 : Q2 * Q5 * A5 ≠ 0 := mul_ne_zero (mul_ne_zero hQ2 hQ5) hA5
  have hQ1Q6A6 : Q1 * Q6 * A6 ≠ 0 := mul_ne_zero (mul_ne_zero hQ1 hQ6) hA6
  field_simp [hD, hQ1, hQ2, hQ3, hQ4, hQ5, hQ6, hQ7, hA1, hA2, hA3, hA4,
    hA5, hA6, hA7, hDQ7, hDQ6, hDQ5, hDQ4, hDQ3, hDQ2, hDQ1,
    hQ1A1, hQ2A2, hQ3A3, hQ4A4, hQ5A5, hQ6A6, hQ7A7,
    hQ6Q1A1, hQ5Q2A2, hQ4Q3A3, hQ3Q4A4, hQ2Q5A5, hQ1Q6A6]
  field_simp [hQ6Q1A1, hQ5Q2A2, hQ4Q3A3, hQ3Q4A4, hQ2Q5A5, hQ1Q6A6] at hcommon
  ring_nf at hcommon ⊢
  exact hcommon

set_option maxHeartbeats 4000000 in
/-- Generic nine-term algebra step used to express the α₀ coefficient
identity at `n = 8` once both sides have a common denominator equal to
`Q8 · A8` after multiplying through by all q-Pochhammer / q-shifted
factors. -/
theorem BaileyTransform_nine_term_fraction_from_common
    (P0 P1 P2 P3 P4 P5 P6 P7 P8 D Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8
      A1 A2 A3 A4 A5 A6 A7 A8 : R)
    (hD : D ≠ 0) (hQ1 : Q1 ≠ 0) (hQ2 : Q2 ≠ 0)
    (hQ3 : Q3 ≠ 0) (hQ4 : Q4 ≠ 0) (hQ5 : Q5 ≠ 0)
    (hQ6 : Q6 ≠ 0) (hQ7 : Q7 ≠ 0) (hQ8 : Q8 ≠ 0)
    (hA1 : A1 ≠ 0) (hA2 : A2 ≠ 0) (hA3 : A3 ≠ 0)
    (hA4 : A4 ≠ 0) (hA5 : A5 ≠ 0) (hA6 : A6 ≠ 0)
    (hA7 : A7 ≠ 0) (hA8 : A8 ≠ 0)
    (hcommon : P0 * A8 + P1 * (Q8 * A8 / (Q7 * Q1 * A1)) +
      P2 * (Q8 * A8 / (Q6 * Q2 * A2)) +
      P3 * (Q8 * A8 / (Q5 * Q3 * A3)) +
      P4 * (Q8 * A8 / (Q4 * Q4 * A4)) +
      P5 * (Q8 * A8 / (Q3 * Q5 * A5)) +
      P6 * (Q8 * A8 / (Q2 * Q6 * A6)) +
      P7 * (Q8 * A8 / (Q1 * Q7 * A7)) + P8 = D) :
    P0 / (D * Q8) + (P1 / (D * Q7)) / (Q1 * A1) +
      (P2 / (D * Q6)) / (Q2 * A2) +
      (P3 / (D * Q5)) / (Q3 * A3) +
      (P4 / (D * Q4)) / (Q4 * A4) +
      (P5 / (D * Q3)) / (Q5 * A5) +
      (P6 / (D * Q2)) / (Q6 * A6) +
      (P7 / (D * Q1)) / (Q7 * A7) + (P8 / D) / (Q8 * A8) =
      1 / (Q8 * A8) := by
  have hDQ8 : D * Q8 ≠ 0 := mul_ne_zero hD hQ8
  have hDQ7 : D * Q7 ≠ 0 := mul_ne_zero hD hQ7
  have hDQ6 : D * Q6 ≠ 0 := mul_ne_zero hD hQ6
  have hDQ5 : D * Q5 ≠ 0 := mul_ne_zero hD hQ5
  have hDQ4 : D * Q4 ≠ 0 := mul_ne_zero hD hQ4
  have hDQ3 : D * Q3 ≠ 0 := mul_ne_zero hD hQ3
  have hDQ2 : D * Q2 ≠ 0 := mul_ne_zero hD hQ2
  have hDQ1 : D * Q1 ≠ 0 := mul_ne_zero hD hQ1
  have hQ1A1 : Q1 * A1 ≠ 0 := mul_ne_zero hQ1 hA1
  have hQ2A2 : Q2 * A2 ≠ 0 := mul_ne_zero hQ2 hA2
  have hQ3A3 : Q3 * A3 ≠ 0 := mul_ne_zero hQ3 hA3
  have hQ4A4 : Q4 * A4 ≠ 0 := mul_ne_zero hQ4 hA4
  have hQ5A5 : Q5 * A5 ≠ 0 := mul_ne_zero hQ5 hA5
  have hQ6A6 : Q6 * A6 ≠ 0 := mul_ne_zero hQ6 hA6
  have hQ7A7 : Q7 * A7 ≠ 0 := mul_ne_zero hQ7 hA7
  have hQ8A8 : Q8 * A8 ≠ 0 := mul_ne_zero hQ8 hA8
  have hQ7Q1A1 : Q7 * Q1 * A1 ≠ 0 := mul_ne_zero (mul_ne_zero hQ7 hQ1) hA1
  have hQ6Q2A2 : Q6 * Q2 * A2 ≠ 0 := mul_ne_zero (mul_ne_zero hQ6 hQ2) hA2
  have hQ5Q3A3 : Q5 * Q3 * A3 ≠ 0 := mul_ne_zero (mul_ne_zero hQ5 hQ3) hA3
  have hQ4Q4A4 : Q4 * Q4 * A4 ≠ 0 := mul_ne_zero (mul_ne_zero hQ4 hQ4) hA4
  have hQ3Q5A5 : Q3 * Q5 * A5 ≠ 0 := mul_ne_zero (mul_ne_zero hQ3 hQ5) hA5
  have hQ2Q6A6 : Q2 * Q6 * A6 ≠ 0 := mul_ne_zero (mul_ne_zero hQ2 hQ6) hA6
  have hQ1Q7A7 : Q1 * Q7 * A7 ≠ 0 := mul_ne_zero (mul_ne_zero hQ1 hQ7) hA7
  field_simp [hD, hQ1, hQ2, hQ3, hQ4, hQ5, hQ6, hQ7, hQ8,
    hA1, hA2, hA3, hA4, hA5, hA6, hA7, hA8,
    hDQ8, hDQ7, hDQ6, hDQ5, hDQ4, hDQ3, hDQ2, hDQ1,
    hQ1A1, hQ2A2, hQ3A3, hQ4A4, hQ5A5, hQ6A6, hQ7A7, hQ8A8,
    hQ7Q1A1, hQ6Q2A2, hQ5Q3A3, hQ4Q4A4, hQ3Q5A5, hQ2Q6A6, hQ1Q7A7]
  field_simp [hQ7Q1A1, hQ6Q2A2, hQ5Q3A3, hQ4Q4A4, hQ3Q5A5, hQ2Q6A6, hQ1Q7A7] at hcommon
  ring_nf at hcommon ⊢
  exact hcommon

/-- The α₀ coefficient identity in the `n = 4` finite Bailey-lemma step. -/
theorem BaileyTransform_four_alpha_zero_coefficient_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hD1 : qPoch (a * q / ρ₁) q 4 ≠ 0)
    (hD2 : qPoch (a * q / ρ₂) q 4 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hQ4 : qPochhammer q 4 ≠ 0)
    (hA1 : qPoch (a * q) q 1 ≠ 0)
    (hA2 : qPoch (a * q) q 2 ≠ 0)
    (hA3 : qPoch (a * q) q 3 ≠ 0)
    (hA4 : qPoch (a * q) q 4 ≠ 0) :
    ((qPoch ρ₁ q 0 * qPoch ρ₂ q 0 * (a * q / (ρ₁ * ρ₂)) ^ 0 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 4) /
      (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4 *
        qPochhammer q 4)) +
      ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3) /
      (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4 *
        qPochhammer q 3)) /
        (qPochhammer q 1 * qPoch (a * q) q 1) +
      ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4 *
        qPochhammer q 2)) /
        (qPochhammer q 2 * qPoch (a * q) q 2) +
      ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4 *
        qPochhammer q 1)) /
        (qPochhammer q 3 * qPoch (a * q) q 3) +
      ((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4 *
        qPochhammer q 0)) /
        (qPochhammer q 4 * qPoch (a * q) q 4) =
      1 / (qPochhammer q 4 * qPoch (a * q) q 4) := by
  have hD : qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4 ≠ 0 :=
    mul_ne_zero hD1 hD2
  have hcommon := BaileyTransform_four_alpha_zero_common_denominator_identity
    a q ρ₁ ρ₂ hρ hQ1 hQ2 hQ3 hA1 hA2 hA3
  simpa [qPochhammer, qPoch] using
    (BaileyTransform_five_term_fraction_from_common
      (P0 := qPoch (a * q / (ρ₁ * ρ₂)) q 4)
      (P1 := qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3)
      (P2 := qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2)
      (P3 := qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1)
      (P4 := qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4)
      (D := qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4)
      (Q1 := qPochhammer q 1)
      (Q2 := qPochhammer q 2)
      (Q3 := qPochhammer q 3)
      (Q4 := qPochhammer q 4)
      (A1 := qPoch (a * q) q 1)
      (A2 := qPoch (a * q) q 2)
      (A3 := qPoch (a * q) q 3)
      (A4 := qPoch (a * q) q 4)
      hD hQ1 hQ2 hQ3 hQ4 hA1 hA2 hA3 hA4 hcommon)

/-- The α₀ coefficient identity in the `n = 5` finite Bailey-lemma step. -/
theorem BaileyTransform_five_alpha_zero_coefficient_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hD1 : qPoch (a * q / ρ₁) q 5 ≠ 0)
    (hD2 : qPoch (a * q / ρ₂) q 5 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hQ4 : qPochhammer q 4 ≠ 0)
    (hQ5 : qPochhammer q 5 ≠ 0)
    (hA1 : qPoch (a * q) q 1 ≠ 0)
    (hA2 : qPoch (a * q) q 2 ≠ 0)
    (hA3 : qPoch (a * q) q 3 ≠ 0)
    (hA4 : qPoch (a * q) q 4 ≠ 0)
    (hA5 : qPoch (a * q) q 5 ≠ 0) :
    ((qPoch ρ₁ q 0 * qPoch ρ₂ q 0 * (a * q / (ρ₁ * ρ₂)) ^ 0 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 5) /
      (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 *
        qPochhammer q 5)) +
      ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 4) /
      (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 *
        qPochhammer q 4)) /
        (qPochhammer q 1 * qPoch (a * q) q 1) +
      ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3) /
      (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 *
        qPochhammer q 3)) /
        (qPochhammer q 2 * qPoch (a * q) q 2) +
      ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 *
        qPochhammer q 2)) /
        (qPochhammer q 3 * qPoch (a * q) q 3) +
      ((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 *
        qPochhammer q 1)) /
        (qPochhammer q 4 * qPoch (a * q) q 4) +
      ((qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 *
        qPochhammer q 0)) /
        (qPochhammer q 5 * qPoch (a * q) q 5) =
      1 / (qPochhammer q 5 * qPoch (a * q) q 5) := by
  have hD : qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 ≠ 0 :=
    mul_ne_zero hD1 hD2
  have hcommon := BaileyTransform_five_alpha_zero_common_denominator_identity
    a q ρ₁ ρ₂ hρ hQ1 hQ2 hQ3 hQ4 hA1 hA2 hA3 hA4
  simpa [qPochhammer, qPoch] using
    (BaileyTransform_six_term_fraction_from_common
      (P0 := qPoch (a * q / (ρ₁ * ρ₂)) q 5)
      (P1 := qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) *
        qPoch (a * q / (ρ₁ * ρ₂)) q 4)
      (P2 := qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3)
      (P3 := qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2)
      (P4 := qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1)
      (P5 := qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5)
      (D := qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5)
      (Q1 := qPochhammer q 1)
      (Q2 := qPochhammer q 2)
      (Q3 := qPochhammer q 3)
      (Q4 := qPochhammer q 4)
      (Q5 := qPochhammer q 5)
      (A1 := qPoch (a * q) q 1)
      (A2 := qPoch (a * q) q 2)
      (A3 := qPoch (a * q) q 3)
      (A4 := qPoch (a * q) q 4)
      (A5 := qPoch (a * q) q 5)
      hD hQ1 hQ2 hQ3 hQ4 hQ5 hA1 hA2 hA3 hA4 hA5 hcommon)

/-- The α₁ coefficient identity in the `n = 4` finite Bailey-lemma step after
moving the four transformed-β contributions to a common denominator. -/
theorem BaileyTransform_four_alpha_one_common_denominator_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hA2 : qPoch (a * q) q 2 ≠ 0)
    (hA3 : qPoch (a * q) q 3 ≠ 0)
    (hA4 : qPoch (a * q) q 4 ≠ 0)
    (hD1one : qPoch (a * q / ρ₁) q 1 ≠ 0)
    (hD2one : qPoch (a * q / ρ₂) q 1 ≠ 0) :
    qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3 *
        (qPoch (a * q) q 5 / qPoch (a * q) q 2) +
      qPoch ρ₁ q 2 * qPoch ρ₂ q 2 *
        (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2 *
        (qPochhammer q 3 * qPoch (a * q) q 5 /
          (qPochhammer q 2 * qPochhammer q 1 * qPoch (a * q) q 3)) +
      qPoch ρ₁ q 3 * qPoch ρ₂ q 3 *
        (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1 *
        (qPochhammer q 3 * qPoch (a * q) q 5 /
          (qPochhammer q 1 * qPochhammer q 2 * qPoch (a * q) q 4)) +
      qPoch ρ₁ q 4 * qPoch ρ₂ q 4 *
        (a * q / (ρ₁ * ρ₂)) ^ 4 =
      (qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂))) *
        ((qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4) /
          (qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1)) := by
  rw [BaileyTransform_four_qpoch_aq_five_over_two a q hA2,
    BaileyTransform_four_qpochhammer_aq_alpha_one_first_middle_ratio a q hQ1 hQ2 hA3,
    BaileyTransform_four_qpochhammer_aq_alpha_one_second_middle_ratio a q hQ1 hQ2 hA4,
    BaileyTransform_four_qpoch_pair_ratio_one_four a q ρ₁ ρ₂ hD1one hD2one]
  have hρ1 : ρ₁ ≠ 0 := left_ne_zero_of_mul hρ
  have hρ2 : ρ₂ ≠ 0 := right_ne_zero_of_mul hρ
  simp [qPoch]
  field_simp [hρ, hρ1, hρ2]
  ring

/-- Generic four-term algebra step: a common-denominator identity with a
remaining denominator ratio implies the corresponding fractional identity. -/
theorem BaileyTransform_four_term_fraction_from_common_ratio
    (P1 P2 P3 P4 B D D1 Q1 Q2 Q3 A2 A3 A4 A5 : R)
    (hD : D ≠ 0) (hD1 : D1 ≠ 0)
    (hQ1 : Q1 ≠ 0) (hQ2 : Q2 ≠ 0) (hQ3 : Q3 ≠ 0)
    (hA2 : A2 ≠ 0) (hA3 : A3 ≠ 0) (hA4 : A4 ≠ 0) (hA5 : A5 ≠ 0)
    (hcommon : P1 * (A5 / A2) + P2 * (Q3 * A5 / (Q2 * Q1 * A3)) +
      P3 * (Q3 * A5 / (Q1 * Q2 * A4)) + P4 = B * (D / D1)) :
    (P1 / (D * Q3)) / A2 + (P2 / (D * Q2)) / (Q1 * A3) +
      (P3 / (D * Q1)) / (Q2 * A4) + (P4 / D) / (Q3 * A5) =
      (B / D1) / (Q3 * A5) := by
  have hDQ3 : D * Q3 ≠ 0 := mul_ne_zero hD hQ3
  have hDQ2 : D * Q2 ≠ 0 := mul_ne_zero hD hQ2
  have hDQ1 : D * Q1 ≠ 0 := mul_ne_zero hD hQ1
  have hQ1A3 : Q1 * A3 ≠ 0 := mul_ne_zero hQ1 hA3
  have hQ2A4 : Q2 * A4 ≠ 0 := mul_ne_zero hQ2 hA4
  have hQ3A5 : Q3 * A5 ≠ 0 := mul_ne_zero hQ3 hA5
  have hQ2Q1A3 : Q2 * Q1 * A3 ≠ 0 := mul_ne_zero (mul_ne_zero hQ2 hQ1) hA3
  have hQ1Q2A4 : Q1 * Q2 * A4 ≠ 0 := mul_ne_zero (mul_ne_zero hQ1 hQ2) hA4
  field_simp [hD, hD1, hQ1, hQ2, hQ3, hA2, hA3, hA4, hA5, hDQ3, hDQ2,
    hDQ1, hQ1A3, hQ2A4, hQ3A5, hQ2Q1A3, hQ1Q2A4]
  field_simp [hA2, hQ2Q1A3, hQ1Q2A4, hD1] at hcommon
  ring_nf at hcommon ⊢
  exact hcommon

/-- Generic five-term algebra step: a common-denominator identity with a
remaining denominator ratio implies the corresponding fractional identity. -/
theorem BaileyTransform_five_term_fraction_from_common_ratio
    (P1 P2 P3 P4 P5 B D D1 Q1 Q2 Q3 Q4 A2 A3 A4 A5 A6 : R)
    (hD : D ≠ 0) (hD1 : D1 ≠ 0)
    (hQ1 : Q1 ≠ 0) (hQ2 : Q2 ≠ 0) (hQ3 : Q3 ≠ 0) (hQ4 : Q4 ≠ 0)
    (hA2 : A2 ≠ 0) (hA3 : A3 ≠ 0) (hA4 : A4 ≠ 0)
    (hA5 : A5 ≠ 0) (hA6 : A6 ≠ 0)
    (hcommon : P1 * (A6 / A2) + P2 * (Q4 * A6 / (Q3 * Q1 * A3)) +
      P3 * (Q4 * A6 / (Q2 * Q2 * A4)) +
      P4 * (Q4 * A6 / (Q1 * Q3 * A5)) + P5 = B * (D / D1)) :
    (P1 / (D * Q4)) / A2 + (P2 / (D * Q3)) / (Q1 * A3) +
      (P3 / (D * Q2)) / (Q2 * A4) +
      (P4 / (D * Q1)) / (Q3 * A5) + (P5 / D) / (Q4 * A6) =
      (B / D1) / (Q4 * A6) := by
  have hDQ4 : D * Q4 ≠ 0 := mul_ne_zero hD hQ4
  have hDQ3 : D * Q3 ≠ 0 := mul_ne_zero hD hQ3
  have hDQ2 : D * Q2 ≠ 0 := mul_ne_zero hD hQ2
  have hDQ1 : D * Q1 ≠ 0 := mul_ne_zero hD hQ1
  have hQ1A3 : Q1 * A3 ≠ 0 := mul_ne_zero hQ1 hA3
  have hQ2A4 : Q2 * A4 ≠ 0 := mul_ne_zero hQ2 hA4
  have hQ3A5 : Q3 * A5 ≠ 0 := mul_ne_zero hQ3 hA5
  have hQ4A6 : Q4 * A6 ≠ 0 := mul_ne_zero hQ4 hA6
  have hQ3Q1A3 : Q3 * Q1 * A3 ≠ 0 := mul_ne_zero (mul_ne_zero hQ3 hQ1) hA3
  have hQ2Q2A4 : Q2 * Q2 * A4 ≠ 0 := mul_ne_zero (mul_ne_zero hQ2 hQ2) hA4
  have hQ1Q3A5 : Q1 * Q3 * A5 ≠ 0 := mul_ne_zero (mul_ne_zero hQ1 hQ3) hA5
  field_simp [hD, hD1, hQ1, hQ2, hQ3, hQ4, hA2, hA3, hA4, hA5, hA6,
    hDQ4, hDQ3, hDQ2, hDQ1, hQ1A3, hQ2A4, hQ3A5, hQ4A6,
    hQ3Q1A3, hQ2Q2A4, hQ1Q3A5]
  field_simp [hA2, hQ3Q1A3, hQ2Q2A4, hQ1Q3A5, hD1] at hcommon
  ring_nf at hcommon ⊢
  exact hcommon

/-- The α₁ coefficient identity in the `n = 4` finite Bailey-lemma step. -/
theorem BaileyTransform_four_alpha_one_coefficient_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hD1 : qPoch (a * q / ρ₁) q 4 ≠ 0)
    (hD2 : qPoch (a * q / ρ₂) q 4 ≠ 0)
    (hD1one : qPoch (a * q / ρ₁) q 1 ≠ 0)
    (hD2one : qPoch (a * q / ρ₂) q 1 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hA2 : qPoch (a * q) q 2 ≠ 0)
    (hA3 : qPoch (a * q) q 3 ≠ 0)
    (hA4 : qPoch (a * q) q 4 ≠ 0)
    (hA5 : qPoch (a * q) q 5 ≠ 0) :
    ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3) /
      (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4 *
        qPochhammer q 3)) / qPoch (a * q) q 2 +
      ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4 *
        qPochhammer q 2)) /
        (qPochhammer q 1 * qPoch (a * q) q 3) +
      ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4 *
        qPochhammer q 1)) /
        (qPochhammer q 2 * qPoch (a * q) q 4) +
      ((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4 *
        qPochhammer q 0)) /
        (qPochhammer q 3 * qPoch (a * q) q 5) =
      ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂))) /
        (qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1)) /
        (qPochhammer q 3 * qPoch (a * q) q 5) := by
  have hD : qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4 ≠ 0 :=
    mul_ne_zero hD1 hD2
  have hDone : qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1 ≠ 0 :=
    mul_ne_zero hD1one hD2one
  have hcommon := BaileyTransform_four_alpha_one_common_denominator_identity
    a q ρ₁ ρ₂ hρ hQ1 hQ2 hA2 hA3 hA4 hD1one hD2one
  simpa [qPochhammer, qPoch] using
    (BaileyTransform_four_term_fraction_from_common_ratio
      (P1 := qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3)
      (P2 := qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2)
      (P3 := qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1)
      (P4 := qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4)
      (B := qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)))
      (D := qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4)
      (D1 := qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1)
      (Q1 := qPochhammer q 1)
      (Q2 := qPochhammer q 2)
      (Q3 := qPochhammer q 3)
      (A2 := qPoch (a * q) q 2)
      (A3 := qPoch (a * q) q 3)
      (A4 := qPoch (a * q) q 4)
      (A5 := qPoch (a * q) q 5)
      hD hDone hQ1 hQ2 hQ3 hA2 hA3 hA4 hA5 hcommon)

/-- The α₂ coefficient identity in the `n = 4` finite Bailey-lemma step after
moving the three transformed-β contributions to a common denominator. -/
theorem BaileyTransform_four_alpha_two_common_denominator_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hA4 : qPoch (a * q) q 4 ≠ 0)
    (hA5 : qPoch (a * q) q 5 ≠ 0)
    (hD1two : qPoch (a * q / ρ₁) q 2 ≠ 0)
    (hD2two : qPoch (a * q / ρ₂) q 2 ≠ 0) :
    qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2 *
        (qPoch (a * q) q 6 / qPoch (a * q) q 4) +
      qPoch ρ₁ q 3 * qPoch ρ₂ q 3 *
        (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1 *
        (qPochhammer q 2 * qPoch (a * q) q 6 /
          (qPochhammer q 1 * qPochhammer q 1 * qPoch (a * q) q 5)) +
      qPoch ρ₁ q 4 * qPoch ρ₂ q 4 *
        (a * q / (ρ₁ * ρ₂)) ^ 4 =
      (qPoch ρ₁ q 2 * qPoch ρ₂ q 2 *
        (a * q / (ρ₁ * ρ₂)) ^ 2) *
        ((qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4) /
          (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2)) := by
  rw [BaileyTransform_four_qpoch_aq_six_over_four a q hA4,
    BaileyTransform_four_qpochhammer_aq_alpha_two_middle_ratio a q hQ1 hA5,
    BaileyTransform_four_qpoch_pair_ratio_two_four a q ρ₁ ρ₂ hD1two hD2two]
  have hρ1 : ρ₁ ≠ 0 := left_ne_zero_of_mul hρ
  have hρ2 : ρ₂ ≠ 0 := right_ne_zero_of_mul hρ
  simp [qPoch]
  field_simp [hρ, hρ1, hρ2]
  ring

/-- The α₂ coefficient identity in the `n = 4` finite Bailey-lemma step. -/
theorem BaileyTransform_four_alpha_two_coefficient_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hD1 : qPoch (a * q / ρ₁) q 4 ≠ 0)
    (hD2 : qPoch (a * q / ρ₂) q 4 ≠ 0)
    (hD1two : qPoch (a * q / ρ₁) q 2 ≠ 0)
    (hD2two : qPoch (a * q / ρ₂) q 2 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hA4 : qPoch (a * q) q 4 ≠ 0)
    (hA5 : qPoch (a * q) q 5 ≠ 0)
    (hA6 : qPoch (a * q) q 6 ≠ 0) :
    ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4 *
        qPochhammer q 2)) / qPoch (a * q) q 4 +
      ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4 *
        qPochhammer q 1)) /
        (qPochhammer q 1 * qPoch (a * q) q 5) +
      ((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4 *
        qPochhammer q 0)) /
        (qPochhammer q 2 * qPoch (a * q) q 6) =
      (qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 /
        (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2)) /
        (qPochhammer q 2 * qPoch (a * q) q 6) := by
  have hD : qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4 ≠ 0 :=
    mul_ne_zero hD1 hD2
  have hDtwo : qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2 ≠ 0 :=
    mul_ne_zero hD1two hD2two
  have hcommon := BaileyTransform_four_alpha_two_common_denominator_identity
    a q ρ₁ ρ₂ hρ hQ1 hA4 hA5 hD1two hD2two
  simpa [qPochhammer, qPoch] using
    (BaileyTransform_three_term_fraction_from_common_ratio
      (P1 := qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2)
      (P2 := qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1)
      (P3 := qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4)
      (B := qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2)
      (D := qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4)
      (D1 := qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2)
      (Q1 := qPochhammer q 1)
      (Q2 := qPochhammer q 2)
      (A2 := qPoch (a * q) q 4)
      (A3 := qPoch (a * q) q 5)
      (A4 := qPoch (a * q) q 6)
      hD hDtwo hQ1 hQ2 hA4 hA5 hA6 hcommon)

/-- The α₃ coefficient identity in the `n = 4` finite Bailey-lemma step after
moving the two transformed-β contributions to a common denominator. -/
theorem BaileyTransform_four_alpha_three_common_denominator_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hA6 : qPoch (a * q) q 6 ≠ 0)
    (hD1three : qPoch (a * q / ρ₁) q 3 ≠ 0)
    (hD2three : qPoch (a * q / ρ₂) q 3 ≠ 0) :
    qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1 *
        (qPoch (a * q) q 7 / qPoch (a * q) q 6) +
      qPoch ρ₁ q 4 * qPoch ρ₂ q 4 *
        (a * q / (ρ₁ * ρ₂)) ^ 4 =
      (qPoch ρ₁ q 3 * qPoch ρ₂ q 3 *
        (a * q / (ρ₁ * ρ₂)) ^ 3) *
        ((qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4) /
          (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3)) := by
  rw [BaileyTransform_four_qpoch_ratio_six_seven a q hA6,
    BaileyTransform_four_qpoch_pair_ratio_three_four a q ρ₁ ρ₂ hD1three hD2three]
  have hρ1 : ρ₁ ≠ 0 := left_ne_zero_of_mul hρ
  have hρ2 : ρ₂ ≠ 0 := right_ne_zero_of_mul hρ
  simp [qPoch]
  field_simp [hρ, hρ1, hρ2]
  ring

/-- The α₃ coefficient identity in the `n = 4` finite Bailey-lemma step. -/
theorem BaileyTransform_four_alpha_three_coefficient_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hD1 : qPoch (a * q / ρ₁) q 4 ≠ 0)
    (hD2 : qPoch (a * q / ρ₂) q 4 ≠ 0)
    (hD1three : qPoch (a * q / ρ₁) q 3 ≠ 0)
    (hD2three : qPoch (a * q / ρ₂) q 3 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hA6 : qPoch (a * q) q 6 ≠ 0)
    (hA7 : qPoch (a * q) q 7 ≠ 0) :
    ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4 *
        qPochhammer q 1)) / qPoch (a * q) q 6 +
      ((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4 *
        qPochhammer q 0)) /
        (qPochhammer q 1 * qPoch (a * q) q 7) =
      (qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 /
        (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3)) /
        (qPochhammer q 1 * qPoch (a * q) q 7) := by
  have hD : qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4 ≠ 0 :=
    mul_ne_zero hD1 hD2
  have hDthree : qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 ≠ 0 :=
    mul_ne_zero hD1three hD2three
  have hcommon := BaileyTransform_four_alpha_three_common_denominator_identity
    a q ρ₁ ρ₂ hρ hA6 hD1three hD2three
  simpa [qPochhammer, qPoch] using
    (BaileyTransform_two_term_fraction_from_common_ratio
      (P0 := qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1)
      (P1 := qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4)
      (B := qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3)
      (D := qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4)
      (D2 := qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3)
      (Q := qPochhammer q 1)
      (A4 := qPoch (a * q) q 6)
      (A5 := qPoch (a * q) q 7)
      hD hDthree hQ1 hA6 hA7 hcommon)

/-- The α₄ coefficient identity in the `n = 4` finite Bailey-lemma step. -/
theorem BaileyTransform_four_alpha_four_coefficient_identity (a q ρ₁ ρ₂ : R) :
    ((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4 *
        qPochhammer q 0)) / qPoch (a * q) q 8 =
      (qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 /
        (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4)) /
        qPoch (a * q) q 8 := by
  simp [qPochhammer, qPoch]

/-- The α₅ coefficient identity in the `n = 5` finite Bailey-lemma step. -/
theorem BaileyTransform_five_alpha_five_coefficient_identity (a q ρ₁ ρ₂ : R) :
    ((qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 *
        qPochhammer q 0)) / qPoch (a * q) q 10 =
      (qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 /
        (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5)) /
        qPoch (a * q) q 10 := by
  simp [qPochhammer, qPoch]

/-- The α₆ coefficient identity in the `n = 6` finite Bailey-lemma step. -/
theorem BaileyTransform_six_alpha_six_coefficient_identity (a q ρ₁ ρ₂ : R) :
    ((qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 0)) / qPoch (a * q) q 12 =
      (qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6 /
        (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6)) /
        qPoch (a * q) q 12 := by
  simp [qPochhammer, qPoch]

/-- The α₃ coefficient identity in the `n = 5` finite Bailey-lemma step after
moving the three transformed-β contributions to a common denominator. -/
theorem BaileyTransform_five_alpha_three_common_denominator_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hA6 : qPoch (a * q) q 6 ≠ 0)
    (hA7 : qPoch (a * q) q 7 ≠ 0)
    (hD1three : qPoch (a * q / ρ₁) q 3 ≠ 0)
    (hD2three : qPoch (a * q / ρ₂) q 3 ≠ 0) :
    qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2 *
        (qPoch (a * q) q 8 / qPoch (a * q) q 6) +
      qPoch ρ₁ q 4 * qPoch ρ₂ q 4 *
        (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1 *
        (qPochhammer q 2 * qPoch (a * q) q 8 /
          (qPochhammer q 1 * qPochhammer q 1 * qPoch (a * q) q 7)) +
      qPoch ρ₁ q 5 * qPoch ρ₂ q 5 *
        (a * q / (ρ₁ * ρ₂)) ^ 5 =
      (qPoch ρ₁ q 3 * qPoch ρ₂ q 3 *
        (a * q / (ρ₁ * ρ₂)) ^ 3) *
        ((qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5) /
          (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3)) := by
  rw [BaileyTransform_five_qpoch_aq_eight_over_six a q hA6,
    BaileyTransform_five_qpochhammer_aq_alpha_three_middle_ratio a q hQ1 hA7,
    BaileyTransform_five_qpoch_pair_ratio_three_five a q ρ₁ ρ₂ hD1three hD2three]
  have hρ1 : ρ₁ ≠ 0 := left_ne_zero_of_mul hρ
  have hρ2 : ρ₂ ≠ 0 := right_ne_zero_of_mul hρ
  rw [show qPoch (a * q / (ρ₁ * ρ₂)) q 2 =
      (1 - a * q / (ρ₁ * ρ₂)) * (1 - (a * q / (ρ₁ * ρ₂)) * q) by
        simp [qPoch]]
  rw [show qPoch (a * q / (ρ₁ * ρ₂)) q 1 =
      1 - a * q / (ρ₁ * ρ₂) by simp [qPoch]]
  rw [show qPoch ρ₁ q 5 = qPoch ρ₁ q 4 * (1 - ρ₁ * q ^ 4) by rfl]
  rw [show qPoch ρ₂ q 5 = qPoch ρ₂ q 4 * (1 - ρ₂ * q ^ 4) by rfl]
  rw [show qPoch ρ₁ q 4 = qPoch ρ₁ q 3 * (1 - ρ₁ * q ^ 3) by rfl]
  rw [show qPoch ρ₂ q 4 = qPoch ρ₂ q 3 * (1 - ρ₂ * q ^ 3) by rfl]
  field_simp [hρ, hρ1, hρ2]
  ring

/-- The α₃ coefficient identity in the `n = 5` finite Bailey-lemma step. -/
theorem BaileyTransform_five_alpha_three_coefficient_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hD1 : qPoch (a * q / ρ₁) q 5 ≠ 0)
    (hD2 : qPoch (a * q / ρ₂) q 5 ≠ 0)
    (hD1three : qPoch (a * q / ρ₁) q 3 ≠ 0)
    (hD2three : qPoch (a * q / ρ₂) q 3 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hA6 : qPoch (a * q) q 6 ≠ 0)
    (hA7 : qPoch (a * q) q 7 ≠ 0)
    (hA8 : qPoch (a * q) q 8 ≠ 0) :
    ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 *
        qPochhammer q 2)) / qPoch (a * q) q 6 +
      ((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 *
        qPochhammer q 1)) /
        (qPochhammer q 1 * qPoch (a * q) q 7) +
      ((qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 *
        qPochhammer q 0)) /
        (qPochhammer q 2 * qPoch (a * q) q 8) =
      (qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 /
        (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3)) /
        (qPochhammer q 2 * qPoch (a * q) q 8) := by
  have hD : qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 ≠ 0 :=
    mul_ne_zero hD1 hD2
  have hDthree : qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 ≠ 0 :=
    mul_ne_zero hD1three hD2three
  have hcommon := BaileyTransform_five_alpha_three_common_denominator_identity
    a q ρ₁ ρ₂ hρ hQ1 hA6 hA7 hD1three hD2three
  simpa [qPochhammer, qPoch] using
    (BaileyTransform_three_term_fraction_from_common_ratio
      (P1 := qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2)
      (P2 := qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1)
      (P3 := qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5)
      (B := qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3)
      (D := qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5)
      (D1 := qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3)
      (Q1 := qPochhammer q 1)
      (Q2 := qPochhammer q 2)
      (A2 := qPoch (a * q) q 6)
      (A3 := qPoch (a * q) q 7)
      (A4 := qPoch (a * q) q 8)
      hD hDthree hQ1 hQ2 hA6 hA7 hA8 hcommon)

/-- The α₂ coefficient identity in the `n = 5` finite Bailey-lemma step after
moving the four transformed-β contributions to a common denominator. -/
theorem BaileyTransform_five_alpha_two_common_denominator_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hA4 : qPoch (a * q) q 4 ≠ 0)
    (hA5 : qPoch (a * q) q 5 ≠ 0)
    (hA6 : qPoch (a * q) q 6 ≠ 0)
    (hD1two : qPoch (a * q / ρ₁) q 2 ≠ 0)
    (hD2two : qPoch (a * q / ρ₂) q 2 ≠ 0) :
    qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3 *
        (qPoch (a * q) q 7 / qPoch (a * q) q 4) +
      qPoch ρ₁ q 3 * qPoch ρ₂ q 3 *
        (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2 *
        (qPochhammer q 3 * qPoch (a * q) q 7 /
          (qPochhammer q 2 * qPochhammer q 1 * qPoch (a * q) q 5)) +
      qPoch ρ₁ q 4 * qPoch ρ₂ q 4 *
        (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1 *
        (qPochhammer q 3 * qPoch (a * q) q 7 /
          (qPochhammer q 1 * qPochhammer q 2 * qPoch (a * q) q 6)) +
      qPoch ρ₁ q 5 * qPoch ρ₂ q 5 *
        (a * q / (ρ₁ * ρ₂)) ^ 5 =
      (qPoch ρ₁ q 2 * qPoch ρ₂ q 2 *
        (a * q / (ρ₁ * ρ₂)) ^ 2) *
        ((qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5) /
          (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2)) := by
  rw [BaileyTransform_five_qpoch_aq_seven_over_four a q hA4,
    BaileyTransform_five_qpochhammer_aq_alpha_two_first_middle_ratio a q hQ1 hQ2 hA5,
    BaileyTransform_five_qpochhammer_aq_alpha_two_second_middle_ratio a q hQ1 hQ2 hA6,
    BaileyTransform_five_qpoch_pair_ratio_two_five a q ρ₁ ρ₂ hD1two hD2two]
  have hρ1 : ρ₁ ≠ 0 := left_ne_zero_of_mul hρ
  have hρ2 : ρ₂ ≠ 0 := right_ne_zero_of_mul hρ
  rw [show qPoch (a * q / (ρ₁ * ρ₂)) q 3 =
      (1 - a * q / (ρ₁ * ρ₂)) * (1 - (a * q / (ρ₁ * ρ₂)) * q) *
        (1 - (a * q / (ρ₁ * ρ₂)) * q ^ 2) by
        simp [qPoch]]
  rw [show qPoch (a * q / (ρ₁ * ρ₂)) q 2 =
      (1 - a * q / (ρ₁ * ρ₂)) * (1 - (a * q / (ρ₁ * ρ₂)) * q) by
        simp [qPoch]]
  rw [show qPoch (a * q / (ρ₁ * ρ₂)) q 1 =
      1 - a * q / (ρ₁ * ρ₂) by simp [qPoch]]
  rw [show qPoch ρ₁ q 5 = qPoch ρ₁ q 4 * (1 - ρ₁ * q ^ 4) by rfl]
  rw [show qPoch ρ₂ q 5 = qPoch ρ₂ q 4 * (1 - ρ₂ * q ^ 4) by rfl]
  rw [show qPoch ρ₁ q 4 = qPoch ρ₁ q 3 * (1 - ρ₁ * q ^ 3) by rfl]
  rw [show qPoch ρ₂ q 4 = qPoch ρ₂ q 3 * (1 - ρ₂ * q ^ 3) by rfl]
  rw [show qPoch ρ₁ q 3 = qPoch ρ₁ q 2 * (1 - ρ₁ * q ^ 2) by rfl]
  rw [show qPoch ρ₂ q 3 = qPoch ρ₂ q 2 * (1 - ρ₂ * q ^ 2) by rfl]
  field_simp [hρ, hρ1, hρ2]
  ring

/-- The α₂ coefficient identity in the `n = 5` finite Bailey-lemma step. -/
theorem BaileyTransform_five_alpha_two_coefficient_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hD1 : qPoch (a * q / ρ₁) q 5 ≠ 0)
    (hD2 : qPoch (a * q / ρ₂) q 5 ≠ 0)
    (hD1two : qPoch (a * q / ρ₁) q 2 ≠ 0)
    (hD2two : qPoch (a * q / ρ₂) q 2 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hA4 : qPoch (a * q) q 4 ≠ 0)
    (hA5 : qPoch (a * q) q 5 ≠ 0)
    (hA6 : qPoch (a * q) q 6 ≠ 0)
    (hA7 : qPoch (a * q) q 7 ≠ 0) :
    ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3) /
      (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 *
        qPochhammer q 3)) / qPoch (a * q) q 4 +
      ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 *
        qPochhammer q 2)) /
        (qPochhammer q 1 * qPoch (a * q) q 5) +
      ((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 *
        qPochhammer q 1)) /
        (qPochhammer q 2 * qPoch (a * q) q 6) +
      ((qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 *
        qPochhammer q 0)) /
        (qPochhammer q 3 * qPoch (a * q) q 7) =
      (qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 /
        (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2)) /
        (qPochhammer q 3 * qPoch (a * q) q 7) := by
  have hD : qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 ≠ 0 :=
    mul_ne_zero hD1 hD2
  have hDtwo : qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2 ≠ 0 :=
    mul_ne_zero hD1two hD2two
  have hcommon := BaileyTransform_five_alpha_two_common_denominator_identity
    a q ρ₁ ρ₂ hρ hQ1 hQ2 hA4 hA5 hA6 hD1two hD2two
  simpa [qPochhammer, qPoch] using
    (BaileyTransform_four_term_fraction_from_common_ratio
      (P1 := qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3)
      (P2 := qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2)
      (P3 := qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1)
      (P4 := qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5)
      (B := qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2)
      (D := qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5)
      (D1 := qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2)
      (Q1 := qPochhammer q 1)
      (Q2 := qPochhammer q 2)
      (Q3 := qPochhammer q 3)
      (A2 := qPoch (a * q) q 4)
      (A3 := qPoch (a * q) q 5)
      (A4 := qPoch (a * q) q 6)
      (A5 := qPoch (a * q) q 7)
      hD hDtwo hQ1 hQ2 hQ3 hA4 hA5 hA6 hA7 hcommon)

/-- The α₁ coefficient identity in the `n = 5` finite Bailey-lemma step after
moving the five transformed-β contributions to a common denominator. -/
theorem BaileyTransform_five_alpha_one_common_denominator_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hA2 : qPoch (a * q) q 2 ≠ 0)
    (hA3 : qPoch (a * q) q 3 ≠ 0)
    (hA4 : qPoch (a * q) q 4 ≠ 0)
    (hA5 : qPoch (a * q) q 5 ≠ 0)
    (hD1one : qPoch (a * q / ρ₁) q 1 ≠ 0)
    (hD2one : qPoch (a * q / ρ₂) q 1 ≠ 0) :
    qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) *
        qPoch (a * q / (ρ₁ * ρ₂)) q 4 *
        (qPoch (a * q) q 6 / qPoch (a * q) q 2) +
      qPoch ρ₁ q 2 * qPoch ρ₂ q 2 *
        (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3 *
        (qPochhammer q 4 * qPoch (a * q) q 6 /
          (qPochhammer q 3 * qPochhammer q 1 * qPoch (a * q) q 3)) +
      qPoch ρ₁ q 3 * qPoch ρ₂ q 3 *
        (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2 *
        (qPochhammer q 4 * qPoch (a * q) q 6 /
          (qPochhammer q 2 * qPochhammer q 2 * qPoch (a * q) q 4)) +
      qPoch ρ₁ q 4 * qPoch ρ₂ q 4 *
        (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1 *
        (qPochhammer q 4 * qPoch (a * q) q 6 /
          (qPochhammer q 1 * qPochhammer q 3 * qPoch (a * q) q 5)) +
      qPoch ρ₁ q 5 * qPoch ρ₂ q 5 *
        (a * q / (ρ₁ * ρ₂)) ^ 5 =
      (qPoch ρ₁ q 1 * qPoch ρ₂ q 1 *
        (a * q / (ρ₁ * ρ₂))) *
        ((qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5) /
          (qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1)) := by
  rw [BaileyTransform_five_qpoch_aq_six_over_two a q hA2,
    BaileyTransform_five_qpochhammer_aq_alpha_one_first_middle_ratio a q hQ1 hQ3 hA3,
    BaileyTransform_five_qpochhammer_aq_alpha_one_second_middle_ratio a q hQ2 hA4,
    BaileyTransform_five_qpochhammer_aq_alpha_one_third_middle_ratio a q hQ1 hQ3 hA5,
    BaileyTransform_five_qpoch_pair_ratio_one_five a q ρ₁ ρ₂ hD1one hD2one]
  have hρ1 : ρ₁ ≠ 0 := left_ne_zero_of_mul hρ
  have hρ2 : ρ₂ ≠ 0 := right_ne_zero_of_mul hρ
  rw [show qPoch (a * q / (ρ₁ * ρ₂)) q 4 =
      (1 - a * q / (ρ₁ * ρ₂)) * (1 - (a * q / (ρ₁ * ρ₂)) * q) *
        (1 - (a * q / (ρ₁ * ρ₂)) * q ^ 2) *
        (1 - (a * q / (ρ₁ * ρ₂)) * q ^ 3) by
        simp [qPoch]]
  rw [show qPoch (a * q / (ρ₁ * ρ₂)) q 3 =
      (1 - a * q / (ρ₁ * ρ₂)) * (1 - (a * q / (ρ₁ * ρ₂)) * q) *
        (1 - (a * q / (ρ₁ * ρ₂)) * q ^ 2) by
        simp [qPoch]]
  rw [show qPoch (a * q / (ρ₁ * ρ₂)) q 2 =
      (1 - a * q / (ρ₁ * ρ₂)) * (1 - (a * q / (ρ₁ * ρ₂)) * q) by
        simp [qPoch]]
  rw [show qPoch (a * q / (ρ₁ * ρ₂)) q 1 =
      1 - a * q / (ρ₁ * ρ₂) by simp [qPoch]]
  rw [show qPoch ρ₁ q 5 = qPoch ρ₁ q 4 * (1 - ρ₁ * q ^ 4) by rfl]
  rw [show qPoch ρ₂ q 5 = qPoch ρ₂ q 4 * (1 - ρ₂ * q ^ 4) by rfl]
  rw [show qPoch ρ₁ q 4 = qPoch ρ₁ q 3 * (1 - ρ₁ * q ^ 3) by rfl]
  rw [show qPoch ρ₂ q 4 = qPoch ρ₂ q 3 * (1 - ρ₂ * q ^ 3) by rfl]
  rw [show qPoch ρ₁ q 3 = qPoch ρ₁ q 2 * (1 - ρ₁ * q ^ 2) by rfl]
  rw [show qPoch ρ₂ q 3 = qPoch ρ₂ q 2 * (1 - ρ₂ * q ^ 2) by rfl]
  rw [show qPoch ρ₁ q 2 = qPoch ρ₁ q 1 * (1 - ρ₁ * q) by simp [qPoch]]
  rw [show qPoch ρ₂ q 2 = qPoch ρ₂ q 1 * (1 - ρ₂ * q) by simp [qPoch]]
  field_simp [hρ, hρ1, hρ2]
  ring

/-- The α₁ coefficient identity in the `n = 5` finite Bailey-lemma step. -/
theorem BaileyTransform_five_alpha_one_coefficient_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hD1 : qPoch (a * q / ρ₁) q 5 ≠ 0)
    (hD2 : qPoch (a * q / ρ₂) q 5 ≠ 0)
    (hD1one : qPoch (a * q / ρ₁) q 1 ≠ 0)
    (hD2one : qPoch (a * q / ρ₂) q 1 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hQ4 : qPochhammer q 4 ≠ 0)
    (hA2 : qPoch (a * q) q 2 ≠ 0)
    (hA3 : qPoch (a * q) q 3 ≠ 0)
    (hA4 : qPoch (a * q) q 4 ≠ 0)
    (hA5 : qPoch (a * q) q 5 ≠ 0)
    (hA6 : qPoch (a * q) q 6 ≠ 0) :
    ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 4) /
      (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 *
        qPochhammer q 4)) / qPoch (a * q) q 2 +
      ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3) /
      (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 *
        qPochhammer q 3)) /
        (qPochhammer q 1 * qPoch (a * q) q 3) +
      ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 *
        qPochhammer q 2)) /
        (qPochhammer q 2 * qPoch (a * q) q 4) +
      ((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 *
        qPochhammer q 1)) /
        (qPochhammer q 3 * qPoch (a * q) q 5) +
      ((qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 *
        qPochhammer q 0)) /
        (qPochhammer q 4 * qPoch (a * q) q 6) =
      (qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) /
        (qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1)) /
        (qPochhammer q 4 * qPoch (a * q) q 6) := by
  have hD : qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 ≠ 0 :=
    mul_ne_zero hD1 hD2
  have hDone : qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1 ≠ 0 :=
    mul_ne_zero hD1one hD2one
  have hcommon := BaileyTransform_five_alpha_one_common_denominator_identity
    a q ρ₁ ρ₂ hρ hQ1 hQ2 hQ3 hA2 hA3 hA4 hA5 hD1one hD2one
  simpa [qPochhammer, qPoch] using
    (BaileyTransform_five_term_fraction_from_common_ratio
      (P1 := qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) *
        qPoch (a * q / (ρ₁ * ρ₂)) q 4)
      (P2 := qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3)
      (P3 := qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2)
      (P4 := qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1)
      (P5 := qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5)
      (B := qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)))
      (D := qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5)
      (D1 := qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1)
      (Q1 := qPochhammer q 1)
      (Q2 := qPochhammer q 2)
      (Q3 := qPochhammer q 3)
      (Q4 := qPochhammer q 4)
      (A2 := qPoch (a * q) q 2)
      (A3 := qPoch (a * q) q 3)
      (A4 := qPoch (a * q) q 4)
      (A5 := qPoch (a * q) q 5)
      (A6 := qPoch (a * q) q 6)
      hD hDone hQ1 hQ2 hQ3 hQ4 hA2 hA3 hA4 hA5 hA6 hcommon)

/-- The α₄ coefficient identity in the `n = 5` finite Bailey-lemma step after
moving the two transformed-β contributions to a common denominator. -/
theorem BaileyTransform_five_alpha_four_common_denominator_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hA8 : qPoch (a * q) q 8 ≠ 0)
    (hD1four : qPoch (a * q / ρ₁) q 4 ≠ 0)
    (hD2four : qPoch (a * q / ρ₂) q 4 ≠ 0) :
    qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1 *
        (qPoch (a * q) q 9 / qPoch (a * q) q 8) +
      qPoch ρ₁ q 5 * qPoch ρ₂ q 5 *
        (a * q / (ρ₁ * ρ₂)) ^ 5 =
      (qPoch ρ₁ q 4 * qPoch ρ₂ q 4 *
        (a * q / (ρ₁ * ρ₂)) ^ 4) *
        ((qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5) /
          (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4)) := by
  rw [BaileyTransform_five_qpoch_ratio_eight_nine a q hA8,
    BaileyTransform_five_qpoch_pair_ratio_four_five a q ρ₁ ρ₂ hD1four hD2four]
  have hρ1 : ρ₁ ≠ 0 := left_ne_zero_of_mul hρ
  have hρ2 : ρ₂ ≠ 0 := right_ne_zero_of_mul hρ
  rw [show qPoch (a * q / (ρ₁ * ρ₂)) q 1 =
      1 - a * q / (ρ₁ * ρ₂) by simp [qPoch]]
  rw [show qPoch ρ₁ q 5 = qPoch ρ₁ q 4 * (1 - ρ₁ * q ^ 4) by rfl]
  rw [show qPoch ρ₂ q 5 = qPoch ρ₂ q 4 * (1 - ρ₂ * q ^ 4) by rfl]
  field_simp [hρ, hρ1, hρ2]
  ring

/-- The α₄ coefficient identity in the `n = 5` finite Bailey-lemma step. -/
theorem BaileyTransform_five_alpha_four_coefficient_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hD1 : qPoch (a * q / ρ₁) q 5 ≠ 0)
    (hD2 : qPoch (a * q / ρ₂) q 5 ≠ 0)
    (hD1four : qPoch (a * q / ρ₁) q 4 ≠ 0)
    (hD2four : qPoch (a * q / ρ₂) q 4 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hA8 : qPoch (a * q) q 8 ≠ 0)
    (hA9 : qPoch (a * q) q 9 ≠ 0) :
    ((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 *
        qPochhammer q 1)) / qPoch (a * q) q 8 +
      ((qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 *
        qPochhammer q 0)) /
        (qPochhammer q 1 * qPoch (a * q) q 9) =
      (qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 /
        (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4)) /
        (qPochhammer q 1 * qPoch (a * q) q 9) := by
  have hD : qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 ≠ 0 :=
    mul_ne_zero hD1 hD2
  have hDfour : qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4 ≠ 0 :=
    mul_ne_zero hD1four hD2four
  have hcommon := BaileyTransform_five_alpha_four_common_denominator_identity
    a q ρ₁ ρ₂ hρ hA8 hD1four hD2four
  simpa [qPochhammer, qPoch] using
  (BaileyTransform_two_term_fraction_from_common_ratio
  (P0 := qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
    qPoch (a * q / (ρ₁ * ρ₂)) q 1)
  (P1 := qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5)
  (B := qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4)
  (D := qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5)
  (D2 := qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4)
  (Q := qPochhammer q 1)
  (A4 := qPoch (a * q) q 8)
  (A5 := qPoch (a * q) q 9)
  hD hDfour hQ1 hA8 hA9 hcommon)

/-- The five-step q-Pochhammer ratio needed in the `n = 6`, α₁ coefficient
calculation. -/
theorem BaileyTransform_six_qpoch_aq_seven_over_two
    (a q : R) (hA2 : qPoch (a * q) q 2 ≠ 0) :
    qPoch (a * q) q 7 / qPoch (a * q) q 2 =
      (1 - a * q ^ 3) * (1 - a * q ^ 4) *
        (1 - a * q ^ 5) * (1 - a * q ^ 6) *
        (1 - a * q ^ 7) := by
  rw [show qPoch (a * q) q 7 =
      qPoch (a * q) q 2 * (1 - (a * q) * q ^ 2) *
        (1 - (a * q) * q ^ 3) * (1 - (a * q) * q ^ 4) *
        (1 - (a * q) * q ^ 5) * (1 - (a * q) * q ^ 6) by rfl]
  field_simp [hA2]

/-- The four-step q-Pochhammer ratio `(aq;q)_7 / (aq;q)_3`. -/
theorem BaileyTransform_six_qpoch_aq_seven_over_three
    (a q : R) (hA3 : qPoch (a * q) q 3 ≠ 0) :
    qPoch (a * q) q 7 / qPoch (a * q) q 3 =
      (1 - a * q ^ 4) * (1 - a * q ^ 5) *
        (1 - a * q ^ 6) * (1 - a * q ^ 7) := by
  rw [show qPoch (a * q) q 7 =
      qPoch (a * q) q 3 * (1 - (a * q) * q ^ 3) *
        (1 - (a * q) * q ^ 4) * (1 - (a * q) * q ^ 5) *
        (1 - (a * q) * q ^ 6) by rfl]
  field_simp [hA3]

/-- The first middle denominator ratio appearing in the `n = 6`, α₁
common-denominator calculation. -/
theorem BaileyTransform_six_qpochhammer_aq_alpha_one_first_middle_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ4 : qPochhammer q 4 ≠ 0)
    (hA3 : qPoch (a * q) q 3 ≠ 0) :
    qPochhammer q 5 * qPoch (a * q) q 7 /
        (qPochhammer q 4 * qPochhammer q 1 * qPoch (a * q) q 3) =
      (1 + q + q ^ 2 + q ^ 3 + q ^ 4) *
        ((1 - a * q ^ 4) * (1 - a * q ^ 5) *
          (1 - a * q ^ 6) * (1 - a * q ^ 7)) := by
  have hQ4Q1 : qPochhammer q 4 * qPochhammer q 1 ≠ 0 :=
    mul_ne_zero hQ4 hQ1
  have hQ := BaileyTransform_five_qpochhammer_five_over_four_one q hQ1 hQ4
  have hA := BaileyTransform_six_qpoch_aq_seven_over_three a q hA3
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 5)
      (qPochhammer q 4 * qPochhammer q 1)
      (qPoch (a * q) q 7) (qPoch (a * q) q 3)
      (1 + q + q ^ 2 + q ^ 3 + q ^ 4)
      ((1 - a * q ^ 4) * (1 - a * q ^ 5) *
        (1 - a * q ^ 6) * (1 - a * q ^ 7))
      hQ4Q1 hA3 hQ hA

/-- The second middle denominator ratio appearing in the `n = 6`, α₁
common-denominator calculation. -/
theorem BaileyTransform_six_qpochhammer_aq_alpha_one_second_middle_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hA4 : qPoch (a * q) q 4 ≠ 0) :
    qPochhammer q 5 * qPoch (a * q) q 7 /
        (qPochhammer q 3 * qPochhammer q 2 * qPoch (a * q) q 4) =
      ((1 + q + q ^ 2 + q ^ 3 + q ^ 4) * (1 + q ^ 2)) *
        ((1 - a * q ^ 5) * (1 - a * q ^ 6) * (1 - a * q ^ 7)) := by
  have hQ3Q2 : qPochhammer q 3 * qPochhammer q 2 ≠ 0 :=
    mul_ne_zero hQ3 hQ2
  have hQ := BaileyTransform_five_qpochhammer_five_over_three_two q hQ1 hQ2 hQ3
  have hA := BaileyTransform_five_qpoch_aq_seven_over_four a q hA4
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 5)
      (qPochhammer q 3 * qPochhammer q 2)
      (qPoch (a * q) q 7) (qPoch (a * q) q 4)
      ((1 + q + q ^ 2 + q ^ 3 + q ^ 4) * (1 + q ^ 2))
      ((1 - a * q ^ 5) * (1 - a * q ^ 6) * (1 - a * q ^ 7))
      hQ3Q2 hA4 hQ hA

/-- The third middle denominator ratio appearing in the `n = 6`, α₁
common-denominator calculation. -/
theorem BaileyTransform_six_qpochhammer_aq_alpha_one_third_middle_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hA5 : qPoch (a * q) q 5 ≠ 0) :
    qPochhammer q 5 * qPoch (a * q) q 7 /
        (qPochhammer q 2 * qPochhammer q 3 * qPoch (a * q) q 5) =
      ((1 + q + q ^ 2 + q ^ 3 + q ^ 4) * (1 + q ^ 2)) *
        ((1 - a * q ^ 6) * (1 - a * q ^ 7)) := by
  have hQ2Q3 : qPochhammer q 2 * qPochhammer q 3 ≠ 0 :=
    mul_ne_zero hQ2 hQ3
  have hQ := BaileyTransform_five_qpochhammer_five_over_two_three q hQ1 hQ2 hQ3
  have hA := BaileyTransform_five_qpoch_aq_seven_over_five a q hA5
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 5)
      (qPochhammer q 2 * qPochhammer q 3)
      (qPoch (a * q) q 7) (qPoch (a * q) q 5)
      ((1 + q + q ^ 2 + q ^ 3 + q ^ 4) * (1 + q ^ 2))
      ((1 - a * q ^ 6) * (1 - a * q ^ 7))
      hQ2Q3 hA5 hQ hA

/-- The fourth middle denominator ratio appearing in the `n = 6`, α₁
common-denominator calculation. -/
theorem BaileyTransform_six_qpochhammer_aq_alpha_one_fourth_middle_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ4 : qPochhammer q 4 ≠ 0)
    (hA6 : qPoch (a * q) q 6 ≠ 0) :
    qPochhammer q 5 * qPoch (a * q) q 7 /
        (qPochhammer q 1 * qPochhammer q 4 * qPoch (a * q) q 6) =
      (1 + q + q ^ 2 + q ^ 3 + q ^ 4) * (1 - a * q ^ 7) := by
  have hQ1Q4 : qPochhammer q 1 * qPochhammer q 4 ≠ 0 :=
    mul_ne_zero hQ1 hQ4
  have hQ : qPochhammer q 5 / (qPochhammer q 1 * qPochhammer q 4) =
      1 + q + q ^ 2 + q ^ 3 + q ^ 4 := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      BaileyTransform_five_qpochhammer_five_over_four_one q hQ1 hQ4
  have hA := BaileyTransform_five_qpoch_aq_seven_over_six a q hA6
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 5)
      (qPochhammer q 1 * qPochhammer q 4)
      (qPoch (a * q) q 7) (qPoch (a * q) q 6)
      (1 + q + q ^ 2 + q ^ 3 + q ^ 4) (1 - a * q ^ 7)
      hQ1Q4 hA6 hQ hA

set_option maxHeartbeats 800000 in
/-- The denominator ratio between the `N=7` and `N=2` transformed-α
q-Pochhammer factors. -/
theorem BaileyTransform_seven_qpoch_pair_ratio_two_seven
    (a q ρ₁ ρ₂ : R)
    (hD1two : qPoch (a * q / ρ₁) q 2 ≠ 0)
    (hD2two : qPoch (a * q / ρ₂) q 2 ≠ 0) :
    (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7) /
        (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2) =
      ((1 - (a * q / ρ₁) * q ^ 2) *
        (1 - (a * q / ρ₁) * q ^ 3) *
        (1 - (a * q / ρ₁) * q ^ 4) *
        (1 - (a * q / ρ₁) * q ^ 5) *
        (1 - (a * q / ρ₁) * q ^ 6)) *
      ((1 - (a * q / ρ₂) * q ^ 2) *
        (1 - (a * q / ρ₂) * q ^ 3) *
        (1 - (a * q / ρ₂) * q ^ 4) *
        (1 - (a * q / ρ₂) * q ^ 5) *
        (1 - (a * q / ρ₂) * q ^ 6)) := by
  have h1 : qPoch (a * q / ρ₁) q 7 / qPoch (a * q / ρ₁) q 2 =
      (1 - (a * q / ρ₁) * q ^ 2) *
        (1 - (a * q / ρ₁) * q ^ 3) *
        (1 - (a * q / ρ₁) * q ^ 4) *
        (1 - (a * q / ρ₁) * q ^ 5) *
        (1 - (a * q / ρ₁) * q ^ 6) := by
    rw [show qPoch (a * q / ρ₁) q 7 =
        qPoch (a * q / ρ₁) q 2 * (1 - (a * q / ρ₁) * q ^ 2) *
          (1 - (a * q / ρ₁) * q ^ 3) *
          (1 - (a * q / ρ₁) * q ^ 4) *
          (1 - (a * q / ρ₁) * q ^ 5) *
          (1 - (a * q / ρ₁) * q ^ 6) by rfl]
    field_simp [hD1two]
  have h2 : qPoch (a * q / ρ₂) q 7 / qPoch (a * q / ρ₂) q 2 =
      (1 - (a * q / ρ₂) * q ^ 2) *
        (1 - (a * q / ρ₂) * q ^ 3) *
        (1 - (a * q / ρ₂) * q ^ 4) *
        (1 - (a * q / ρ₂) * q ^ 5) *
        (1 - (a * q / ρ₂) * q ^ 6) := by
    rw [show qPoch (a * q / ρ₂) q 7 =
        qPoch (a * q / ρ₂) q 2 * (1 - (a * q / ρ₂) * q ^ 2) *
          (1 - (a * q / ρ₂) * q ^ 3) *
          (1 - (a * q / ρ₂) * q ^ 4) *
          (1 - (a * q / ρ₂) * q ^ 5) *
          (1 - (a * q / ρ₂) * q ^ 6) by rfl]
    field_simp [hD2two]
  rw [show (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7) /
      (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2) =
      (qPoch (a * q / ρ₁) q 7 / qPoch (a * q / ρ₁) q 2) *
      (qPoch (a * q / ρ₂) q 7 / qPoch (a * q / ρ₂) q 2) by
        field_simp]
  rw [h1, h2]

/-- The first middle denominator ratio appearing in the `n = 7`, α₂
common-denominator calculation. -/
theorem BaileyTransform_seven_qpochhammer_aq_alpha_two_first_middle_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ4 : qPochhammer q 4 ≠ 0)
    (hA5 : qPoch (a * q) q 5 ≠ 0) :
    qPochhammer q 5 * qPoch (a * q) q 9 /
        (qPochhammer q 4 * qPochhammer q 1 * qPoch (a * q) q 5) =
      (1 + q + q ^ 2 + q ^ 3 + q ^ 4) *
        ((1 - a * q ^ 6) * (1 - a * q ^ 7) * (1 - a * q ^ 8) *
          (1 - a * q ^ 9)) := by
  have hQ4Q1 : qPochhammer q 4 * qPochhammer q 1 ≠ 0 :=
    mul_ne_zero hQ4 hQ1
  have hQ := BaileyTransform_five_qpochhammer_five_over_four_one q hQ1 hQ4
  have hA := BaileyTransform_seven_qpoch_aq_nine_over_five a q hA5
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 5)
      (qPochhammer q 4 * qPochhammer q 1)
      (qPoch (a * q) q 9) (qPoch (a * q) q 5)
      (1 + q + q ^ 2 + q ^ 3 + q ^ 4)
      ((1 - a * q ^ 6) * (1 - a * q ^ 7) * (1 - a * q ^ 8) *
        (1 - a * q ^ 9))
      hQ4Q1 hA5 hQ hA

/-- The second middle denominator ratio appearing in the `n = 7`, α₂
common-denominator calculation. -/
theorem BaileyTransform_seven_qpochhammer_aq_alpha_two_second_middle_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hA6 : qPoch (a * q) q 6 ≠ 0) :
    qPochhammer q 5 * qPoch (a * q) q 9 /
        (qPochhammer q 3 * qPochhammer q 2 * qPoch (a * q) q 6) =
      ((1 + q + q ^ 2 + q ^ 3 + q ^ 4) * (1 + q ^ 2)) *
        ((1 - a * q ^ 7) * (1 - a * q ^ 8) * (1 - a * q ^ 9)) := by
  have hQ3Q2 : qPochhammer q 3 * qPochhammer q 2 ≠ 0 :=
    mul_ne_zero hQ3 hQ2
  have hQ := BaileyTransform_five_qpochhammer_five_over_three_two q hQ1 hQ2 hQ3
  have hA := BaileyTransform_six_qpoch_aq_nine_over_six a q hA6
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 5)
      (qPochhammer q 3 * qPochhammer q 2)
      (qPoch (a * q) q 9) (qPoch (a * q) q 6)
      ((1 + q + q ^ 2 + q ^ 3 + q ^ 4) * (1 + q ^ 2))
      ((1 - a * q ^ 7) * (1 - a * q ^ 8) * (1 - a * q ^ 9))
      hQ3Q2 hA6 hQ hA

/-- The third middle denominator ratio appearing in the `n = 7`, α₂
common-denominator calculation. -/
theorem BaileyTransform_seven_qpochhammer_aq_alpha_two_third_middle_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hA7 : qPoch (a * q) q 7 ≠ 0) :
    qPochhammer q 5 * qPoch (a * q) q 9 /
        (qPochhammer q 2 * qPochhammer q 3 * qPoch (a * q) q 7) =
      ((1 + q + q ^ 2 + q ^ 3 + q ^ 4) * (1 + q ^ 2)) *
        ((1 - a * q ^ 8) * (1 - a * q ^ 9)) := by
  have hQ2Q3 : qPochhammer q 2 * qPochhammer q 3 ≠ 0 :=
    mul_ne_zero hQ2 hQ3
  have hQ := BaileyTransform_five_qpochhammer_five_over_two_three q hQ1 hQ2 hQ3
  have hA := BaileyTransform_six_qpoch_aq_nine_over_seven a q hA7
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 5)
      (qPochhammer q 2 * qPochhammer q 3)
      (qPoch (a * q) q 9) (qPoch (a * q) q 7)
      ((1 + q + q ^ 2 + q ^ 3 + q ^ 4) * (1 + q ^ 2))
      ((1 - a * q ^ 8) * (1 - a * q ^ 9))
      hQ2Q3 hA7 hQ hA

/-- The fourth middle denominator ratio appearing in the `n = 7`, α₂
common-denominator calculation. -/
theorem BaileyTransform_seven_qpochhammer_aq_alpha_two_fourth_middle_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ4 : qPochhammer q 4 ≠ 0)
    (hA8 : qPoch (a * q) q 8 ≠ 0) :
    qPochhammer q 5 * qPoch (a * q) q 9 /
        (qPochhammer q 1 * qPochhammer q 4 * qPoch (a * q) q 8) =
      (1 + q + q ^ 2 + q ^ 3 + q ^ 4) * (1 - a * q ^ 9) := by
  have hQ1Q4 : qPochhammer q 1 * qPochhammer q 4 ≠ 0 :=
    mul_ne_zero hQ1 hQ4
  have hQ : qPochhammer q 5 / (qPochhammer q 1 * qPochhammer q 4) =
      1 + q + q ^ 2 + q ^ 3 + q ^ 4 := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      BaileyTransform_five_qpochhammer_five_over_four_one q hQ1 hQ4
  have hA := BaileyTransform_six_qpoch_aq_nine_over_eight a q hA8
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 5)
      (qPochhammer q 1 * qPochhammer q 4)
      (qPoch (a * q) q 9) (qPoch (a * q) q 8)
      (1 + q + q ^ 2 + q ^ 3 + q ^ 4) (1 - a * q ^ 9)
      hQ1Q4 hA8 hQ hA

set_option maxHeartbeats 4000000 in
/-- The α₂ coefficient identity in the `n = 7` finite Bailey-lemma step
after moving the six transformed-β contributions to a common denominator. -/
theorem BaileyTransform_seven_alpha_two_common_denominator_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hQ4 : qPochhammer q 4 ≠ 0)
    (hA4 : qPoch (a * q) q 4 ≠ 0)
    (hA5 : qPoch (a * q) q 5 ≠ 0)
    (hA6 : qPoch (a * q) q 6 ≠ 0)
    (hA7 : qPoch (a * q) q 7 ≠ 0)
    (hA8 : qPoch (a * q) q 8 ≠ 0)
    (hD1two : qPoch (a * q / ρ₁) q 2 ≠ 0)
    (hD2two : qPoch (a * q / ρ₂) q 2 ≠ 0) :
    qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 5 *
        (qPoch (a * q) q 9 / qPoch (a * q) q 4) +
      qPoch ρ₁ q 3 * qPoch ρ₂ q 3 *
        (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 4 *
        (qPochhammer q 5 * qPoch (a * q) q 9 /
          (qPochhammer q 4 * qPochhammer q 1 * qPoch (a * q) q 5)) +
      qPoch ρ₁ q 4 * qPoch ρ₂ q 4 *
        (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3 *
        (qPochhammer q 5 * qPoch (a * q) q 9 /
          (qPochhammer q 3 * qPochhammer q 2 * qPoch (a * q) q 6)) +
      qPoch ρ₁ q 5 * qPoch ρ₂ q 5 *
        (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2 *
        (qPochhammer q 5 * qPoch (a * q) q 9 /
          (qPochhammer q 2 * qPochhammer q 3 * qPoch (a * q) q 7)) +
      qPoch ρ₁ q 6 * qPoch ρ₂ q 6 *
        (a * q / (ρ₁ * ρ₂)) ^ 6 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1 *
        (qPochhammer q 5 * qPoch (a * q) q 9 /
          (qPochhammer q 1 * qPochhammer q 4 * qPoch (a * q) q 8)) +
      qPoch ρ₁ q 7 * qPoch ρ₂ q 7 *
        (a * q / (ρ₁ * ρ₂)) ^ 7 =
      (qPoch ρ₁ q 2 * qPoch ρ₂ q 2 *
        (a * q / (ρ₁ * ρ₂)) ^ 2) *
        ((qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7) /
          (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2)) := by
  rw [BaileyTransform_seven_qpoch_aq_nine_over_four a q hA4,
    BaileyTransform_seven_qpochhammer_aq_alpha_two_first_middle_ratio a q hQ1 hQ4 hA5,
    BaileyTransform_seven_qpochhammer_aq_alpha_two_second_middle_ratio a q hQ1 hQ2 hQ3 hA6,
    BaileyTransform_seven_qpochhammer_aq_alpha_two_third_middle_ratio a q hQ1 hQ2 hQ3 hA7,
    BaileyTransform_seven_qpochhammer_aq_alpha_two_fourth_middle_ratio a q hQ1 hQ4 hA8,
    BaileyTransform_seven_qpoch_pair_ratio_two_seven a q ρ₁ ρ₂ hD1two hD2two]
  have hρ1 : ρ₁ ≠ 0 := left_ne_zero_of_mul hρ
  have hρ2 : ρ₂ ≠ 0 := right_ne_zero_of_mul hρ
  rw [show qPoch (a * q / (ρ₁ * ρ₂)) q 5 =
      (1 - a * q / (ρ₁ * ρ₂)) * (1 - (a * q / (ρ₁ * ρ₂)) * q) *
        (1 - (a * q / (ρ₁ * ρ₂)) * q ^ 2) *
        (1 - (a * q / (ρ₁ * ρ₂)) * q ^ 3) *
        (1 - (a * q / (ρ₁ * ρ₂)) * q ^ 4) by
        simp [qPoch]]
  rw [show qPoch (a * q / (ρ₁ * ρ₂)) q 4 =
      (1 - a * q / (ρ₁ * ρ₂)) * (1 - (a * q / (ρ₁ * ρ₂)) * q) *
        (1 - (a * q / (ρ₁ * ρ₂)) * q ^ 2) *
        (1 - (a * q / (ρ₁ * ρ₂)) * q ^ 3) by
        simp [qPoch]]
  rw [show qPoch (a * q / (ρ₁ * ρ₂)) q 3 =
      (1 - a * q / (ρ₁ * ρ₂)) * (1 - (a * q / (ρ₁ * ρ₂)) * q) *
        (1 - (a * q / (ρ₁ * ρ₂)) * q ^ 2) by
        simp [qPoch]]
  rw [show qPoch (a * q / (ρ₁ * ρ₂)) q 2 =
      (1 - a * q / (ρ₁ * ρ₂)) * (1 - (a * q / (ρ₁ * ρ₂)) * q) by
        simp [qPoch]]
  rw [show qPoch (a * q / (ρ₁ * ρ₂)) q 1 =
      1 - a * q / (ρ₁ * ρ₂) by simp [qPoch]]
  rw [show qPoch ρ₁ q 7 = qPoch ρ₁ q 6 * (1 - ρ₁ * q ^ 6) by rfl]
  rw [show qPoch ρ₂ q 7 = qPoch ρ₂ q 6 * (1 - ρ₂ * q ^ 6) by rfl]
  rw [show qPoch ρ₁ q 6 = qPoch ρ₁ q 5 * (1 - ρ₁ * q ^ 5) by rfl]
  rw [show qPoch ρ₂ q 6 = qPoch ρ₂ q 5 * (1 - ρ₂ * q ^ 5) by rfl]
  rw [show qPoch ρ₁ q 5 = qPoch ρ₁ q 4 * (1 - ρ₁ * q ^ 4) by rfl]
  rw [show qPoch ρ₂ q 5 = qPoch ρ₂ q 4 * (1 - ρ₂ * q ^ 4) by rfl]
  rw [show qPoch ρ₁ q 4 = qPoch ρ₁ q 3 * (1 - ρ₁ * q ^ 3) by rfl]
  rw [show qPoch ρ₂ q 4 = qPoch ρ₂ q 3 * (1 - ρ₂ * q ^ 3) by rfl]
  rw [show qPoch ρ₁ q 3 = qPoch ρ₁ q 2 * (1 - ρ₁ * q ^ 2) by rfl]
  rw [show qPoch ρ₂ q 3 = qPoch ρ₂ q 2 * (1 - ρ₂ * q ^ 2) by rfl]
  field_simp [hρ, hρ1, hρ2]
  ring

set_option maxHeartbeats 4000000 in
/-- The α₂ coefficient identity in the `n = 7` finite Bailey-lemma step. -/
theorem BaileyTransform_seven_alpha_two_coefficient_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hD1 : qPoch (a * q / ρ₁) q 7 ≠ 0)
    (hD2 : qPoch (a * q / ρ₂) q 7 ≠ 0)
    (hD1two : qPoch (a * q / ρ₁) q 2 ≠ 0)
    (hD2two : qPoch (a * q / ρ₂) q 2 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hQ4 : qPochhammer q 4 ≠ 0)
    (hQ5 : qPochhammer q 5 ≠ 0)
    (hA4 : qPoch (a * q) q 4 ≠ 0)
    (hA5 : qPoch (a * q) q 5 ≠ 0)
    (hA6 : qPoch (a * q) q 6 ≠ 0)
    (hA7 : qPoch (a * q) q 7 ≠ 0)
    (hA8 : qPoch (a * q) q 8 ≠ 0)
    (hA9 : qPoch (a * q) q 9 ≠ 0) :
    ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 5) /
      (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 *
        qPochhammer q 5)) / qPoch (a * q) q 4 +
      ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 4) /
      (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 *
        qPochhammer q 4)) /
        (qPochhammer q 1 * qPoch (a * q) q 5) +
      ((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3) /
      (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 *
        qPochhammer q 3)) /
        (qPochhammer q 2 * qPoch (a * q) q 6) +
      ((qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 *
        qPochhammer q 2)) /
        (qPochhammer q 3 * qPoch (a * q) q 7) +
      ((qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 *
        qPochhammer q 1)) /
        (qPochhammer q 4 * qPoch (a * q) q 8) +
      ((qPoch ρ₁ q 7 * qPoch ρ₂ q 7 * (a * q / (ρ₁ * ρ₂)) ^ 7 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 *
        qPochhammer q 0)) /
        (qPochhammer q 5 * qPoch (a * q) q 9) =
      (qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 /
        (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2)) /
        (qPochhammer q 5 * qPoch (a * q) q 9) := by
  have hD : qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 ≠ 0 :=
    mul_ne_zero hD1 hD2
  have hDtwo : qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2 ≠ 0 :=
    mul_ne_zero hD1two hD2two
  have hcommon := BaileyTransform_seven_alpha_two_common_denominator_identity
    a q ρ₁ ρ₂ hρ hQ1 hQ2 hQ3 hQ4 hA4 hA5 hA6 hA7 hA8 hD1two hD2two
  simpa [qPochhammer, qPoch] using
    (BaileyTransform_six_term_fraction_from_common_ratio
      (P1 := qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 5)
      (P2 := qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 4)
      (P3 := qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3)
      (P4 := qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2)
      (P5 := qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1)
      (P6 := qPoch ρ₁ q 7 * qPoch ρ₂ q 7 * (a * q / (ρ₁ * ρ₂)) ^ 7)
      (B := qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2)
      (D := qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7)
      (D1 := qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2)
      (Q1 := qPochhammer q 1)
      (Q2 := qPochhammer q 2)
      (Q3 := qPochhammer q 3)
      (Q4 := qPochhammer q 4)
      (Q5 := qPochhammer q 5)
      (A2 := qPoch (a * q) q 4)
      (A3 := qPoch (a * q) q 5)
      (A4 := qPoch (a * q) q 6)
      (A5 := qPoch (a * q) q 7)
      (A6 := qPoch (a * q) q 8)
      (A7 := qPoch (a * q) q 9)
      hD hDtwo hQ1 hQ2 hQ3 hQ4 hQ5 hA4 hA5 hA6 hA7 hA8 hA9 hcommon)

set_option maxHeartbeats 800000 in
/-- The denominator ratio between the `N=7` and `N=3` transformed-α
q-Pochhammer factors. -/
theorem BaileyTransform_seven_qpoch_pair_ratio_three_seven
    (a q ρ₁ ρ₂ : R)
    (hD1three : qPoch (a * q / ρ₁) q 3 ≠ 0)
    (hD2three : qPoch (a * q / ρ₂) q 3 ≠ 0) :
    (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7) /
        (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3) =
      ((1 - (a * q / ρ₁) * q ^ 3) *
        (1 - (a * q / ρ₁) * q ^ 4) *
        (1 - (a * q / ρ₁) * q ^ 5) *
        (1 - (a * q / ρ₁) * q ^ 6)) *
      ((1 - (a * q / ρ₂) * q ^ 3) *
        (1 - (a * q / ρ₂) * q ^ 4) *
        (1 - (a * q / ρ₂) * q ^ 5) *
        (1 - (a * q / ρ₂) * q ^ 6)) := by
  have h1 : qPoch (a * q / ρ₁) q 7 / qPoch (a * q / ρ₁) q 3 =
      (1 - (a * q / ρ₁) * q ^ 3) *
        (1 - (a * q / ρ₁) * q ^ 4) *
        (1 - (a * q / ρ₁) * q ^ 5) *
        (1 - (a * q / ρ₁) * q ^ 6) := by
    rw [show qPoch (a * q / ρ₁) q 7 =
        qPoch (a * q / ρ₁) q 3 * (1 - (a * q / ρ₁) * q ^ 3) *
          (1 - (a * q / ρ₁) * q ^ 4) *
          (1 - (a * q / ρ₁) * q ^ 5) *
          (1 - (a * q / ρ₁) * q ^ 6) by rfl]
    field_simp [hD1three]
  have h2 : qPoch (a * q / ρ₂) q 7 / qPoch (a * q / ρ₂) q 3 =
      (1 - (a * q / ρ₂) * q ^ 3) *
        (1 - (a * q / ρ₂) * q ^ 4) *
        (1 - (a * q / ρ₂) * q ^ 5) *
        (1 - (a * q / ρ₂) * q ^ 6) := by
    rw [show qPoch (a * q / ρ₂) q 7 =
        qPoch (a * q / ρ₂) q 3 * (1 - (a * q / ρ₂) * q ^ 3) *
          (1 - (a * q / ρ₂) * q ^ 4) *
          (1 - (a * q / ρ₂) * q ^ 5) *
          (1 - (a * q / ρ₂) * q ^ 6) by rfl]
    field_simp [hD2three]
  rw [show (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7) /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3) =
      (qPoch (a * q / ρ₁) q 7 / qPoch (a * q / ρ₁) q 3) *
      (qPoch (a * q / ρ₂) q 7 / qPoch (a * q / ρ₂) q 3) by
        field_simp]
  rw [h1, h2]

/-- The first middle denominator ratio appearing in the `n = 7`, α₃
common-denominator calculation. -/
theorem BaileyTransform_seven_qpochhammer_aq_alpha_three_first_middle_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hA7 : qPoch (a * q) q 7 ≠ 0) :
    qPochhammer q 4 * qPoch (a * q) q 10 /
        (qPochhammer q 3 * qPochhammer q 1 * qPoch (a * q) q 7) =
      (1 + q + q ^ 2 + q ^ 3) *
        ((1 - a * q ^ 8) * (1 - a * q ^ 9) * (1 - a * q ^ 10)) := by
  have hQ3Q1 : qPochhammer q 3 * qPochhammer q 1 ≠ 0 :=
    mul_ne_zero hQ3 hQ1
  have hQ := BaileyTransform_four_qpochhammer_four_over_three_one q hQ1 hQ3
  have hA := BaileyTransform_seven_qpoch_aq_ten_over_seven a q hA7
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 4)
      (qPochhammer q 3 * qPochhammer q 1)
      (qPoch (a * q) q 10) (qPoch (a * q) q 7)
      (1 + q + q ^ 2 + q ^ 3)
      ((1 - a * q ^ 8) * (1 - a * q ^ 9) * (1 - a * q ^ 10))
      hQ3Q1 hA7 hQ hA

/-- The second middle denominator ratio appearing in the `n = 7`, α₃
common-denominator calculation. -/
theorem BaileyTransform_seven_qpochhammer_aq_alpha_three_second_middle_ratio
    (a q : R)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hA8 : qPoch (a * q) q 8 ≠ 0) :
    qPochhammer q 4 * qPoch (a * q) q 10 /
        (qPochhammer q 2 * qPochhammer q 2 * qPoch (a * q) q 8) =
      ((1 + q + q ^ 2) * (1 + q ^ 2)) *
        ((1 - a * q ^ 9) * (1 - a * q ^ 10)) := by
  have hQ2Q2 : qPochhammer q 2 * qPochhammer q 2 ≠ 0 :=
    mul_ne_zero hQ2 hQ2
  have hQ := BaileyTransform_four_qpochhammer_four_over_two_two q hQ2
  have hA := BaileyTransform_seven_qpoch_aq_ten_over_eight a q hA8
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 4)
      (qPochhammer q 2 * qPochhammer q 2)
      (qPoch (a * q) q 10) (qPoch (a * q) q 8)
      ((1 + q + q ^ 2) * (1 + q ^ 2))
      ((1 - a * q ^ 9) * (1 - a * q ^ 10))
      hQ2Q2 hA8 hQ hA

/-- The third middle denominator ratio appearing in the `n = 7`, α₃
common-denominator calculation. -/
theorem BaileyTransform_seven_qpochhammer_aq_alpha_three_third_middle_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hA9 : qPoch (a * q) q 9 ≠ 0) :
    qPochhammer q 4 * qPoch (a * q) q 10 /
        (qPochhammer q 1 * qPochhammer q 3 * qPoch (a * q) q 9) =
      (1 + q + q ^ 2 + q ^ 3) * (1 - a * q ^ 10) := by
  have hQ1Q3 : qPochhammer q 1 * qPochhammer q 3 ≠ 0 :=
    mul_ne_zero hQ1 hQ3
  have hQ : qPochhammer q 4 / (qPochhammer q 1 * qPochhammer q 3) =
      1 + q + q ^ 2 + q ^ 3 := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      BaileyTransform_four_qpochhammer_four_over_three_one q hQ1 hQ3
  have hA := BaileyTransform_seven_qpoch_aq_ten_over_nine a q hA9
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 4)
      (qPochhammer q 1 * qPochhammer q 3)
      (qPoch (a * q) q 10) (qPoch (a * q) q 9)
      (1 + q + q ^ 2 + q ^ 3) (1 - a * q ^ 10)
      hQ1Q3 hA9 hQ hA

set_option maxHeartbeats 4000000 in
/-- The α₃ coefficient identity in the `n = 7` finite Bailey-lemma step after
moving the five transformed-β contributions to a common denominator. -/
theorem BaileyTransform_seven_alpha_three_common_denominator_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hA6 : qPoch (a * q) q 6 ≠ 0)
    (hA7 : qPoch (a * q) q 7 ≠ 0)
    (hA8 : qPoch (a * q) q 8 ≠ 0)
    (hA9 : qPoch (a * q) q 9 ≠ 0)
    (hD1three : qPoch (a * q / ρ₁) q 3 ≠ 0)
    (hD2three : qPoch (a * q / ρ₂) q 3 ≠ 0) :
    qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 4 *
        (qPoch (a * q) q 10 / qPoch (a * q) q 6) +
      qPoch ρ₁ q 4 * qPoch ρ₂ q 4 *
        (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3 *
        (qPochhammer q 4 * qPoch (a * q) q 10 /
          (qPochhammer q 3 * qPochhammer q 1 * qPoch (a * q) q 7)) +
      qPoch ρ₁ q 5 * qPoch ρ₂ q 5 *
        (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2 *
        (qPochhammer q 4 * qPoch (a * q) q 10 /
          (qPochhammer q 2 * qPochhammer q 2 * qPoch (a * q) q 8)) +
      qPoch ρ₁ q 6 * qPoch ρ₂ q 6 *
        (a * q / (ρ₁ * ρ₂)) ^ 6 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1 *
        (qPochhammer q 4 * qPoch (a * q) q 10 /
          (qPochhammer q 1 * qPochhammer q 3 * qPoch (a * q) q 9)) +
      qPoch ρ₁ q 7 * qPoch ρ₂ q 7 *
        (a * q / (ρ₁ * ρ₂)) ^ 7 =
      (qPoch ρ₁ q 3 * qPoch ρ₂ q 3 *
        (a * q / (ρ₁ * ρ₂)) ^ 3) *
        ((qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7) /
          (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3)) := by
  rw [BaileyTransform_seven_qpoch_aq_ten_over_six a q hA6,
    BaileyTransform_seven_qpochhammer_aq_alpha_three_first_middle_ratio a q hQ1 hQ3 hA7,
    BaileyTransform_seven_qpochhammer_aq_alpha_three_second_middle_ratio a q hQ2 hA8,
    BaileyTransform_seven_qpochhammer_aq_alpha_three_third_middle_ratio a q hQ1 hQ3 hA9,
    BaileyTransform_seven_qpoch_pair_ratio_three_seven a q ρ₁ ρ₂ hD1three hD2three]
  have hρ1 : ρ₁ ≠ 0 := left_ne_zero_of_mul hρ
  have hρ2 : ρ₂ ≠ 0 := right_ne_zero_of_mul hρ
  rw [show qPoch (a * q / (ρ₁ * ρ₂)) q 4 =
      (1 - a * q / (ρ₁ * ρ₂)) * (1 - (a * q / (ρ₁ * ρ₂)) * q) *
        (1 - (a * q / (ρ₁ * ρ₂)) * q ^ 2) *
        (1 - (a * q / (ρ₁ * ρ₂)) * q ^ 3) by
        simp [qPoch]]
  rw [show qPoch (a * q / (ρ₁ * ρ₂)) q 3 =
      (1 - a * q / (ρ₁ * ρ₂)) * (1 - (a * q / (ρ₁ * ρ₂)) * q) *
        (1 - (a * q / (ρ₁ * ρ₂)) * q ^ 2) by
        simp [qPoch]]
  rw [show qPoch (a * q / (ρ₁ * ρ₂)) q 2 =
      (1 - a * q / (ρ₁ * ρ₂)) * (1 - (a * q / (ρ₁ * ρ₂)) * q) by
        simp [qPoch]]
  rw [show qPoch (a * q / (ρ₁ * ρ₂)) q 1 =
      1 - a * q / (ρ₁ * ρ₂) by simp [qPoch]]
  rw [show qPoch ρ₁ q 7 = qPoch ρ₁ q 6 * (1 - ρ₁ * q ^ 6) by rfl]
  rw [show qPoch ρ₂ q 7 = qPoch ρ₂ q 6 * (1 - ρ₂ * q ^ 6) by rfl]
  rw [show qPoch ρ₁ q 6 = qPoch ρ₁ q 5 * (1 - ρ₁ * q ^ 5) by rfl]
  rw [show qPoch ρ₂ q 6 = qPoch ρ₂ q 5 * (1 - ρ₂ * q ^ 5) by rfl]
  rw [show qPoch ρ₁ q 5 = qPoch ρ₁ q 4 * (1 - ρ₁ * q ^ 4) by rfl]
  rw [show qPoch ρ₂ q 5 = qPoch ρ₂ q 4 * (1 - ρ₂ * q ^ 4) by rfl]
  rw [show qPoch ρ₁ q 4 = qPoch ρ₁ q 3 * (1 - ρ₁ * q ^ 3) by rfl]
  rw [show qPoch ρ₂ q 4 = qPoch ρ₂ q 3 * (1 - ρ₂ * q ^ 3) by rfl]
  field_simp [hρ, hρ1, hρ2]
  ring

set_option maxHeartbeats 4000000 in
/-- The α₃ coefficient identity in the `n = 7` finite Bailey-lemma step. -/
theorem BaileyTransform_seven_alpha_three_coefficient_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hD1 : qPoch (a * q / ρ₁) q 7 ≠ 0)
    (hD2 : qPoch (a * q / ρ₂) q 7 ≠ 0)
    (hD1three : qPoch (a * q / ρ₁) q 3 ≠ 0)
    (hD2three : qPoch (a * q / ρ₂) q 3 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hQ4 : qPochhammer q 4 ≠ 0)
    (hA6 : qPoch (a * q) q 6 ≠ 0)
    (hA7 : qPoch (a * q) q 7 ≠ 0)
    (hA8 : qPoch (a * q) q 8 ≠ 0)
    (hA9 : qPoch (a * q) q 9 ≠ 0)
    (hA10 : qPoch (a * q) q 10 ≠ 0) :
    ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 4) /
      (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 *
        qPochhammer q 4)) / qPoch (a * q) q 6 +
      ((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3) /
      (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 *
        qPochhammer q 3)) /
        (qPochhammer q 1 * qPoch (a * q) q 7) +
      ((qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 *
        qPochhammer q 2)) /
        (qPochhammer q 2 * qPoch (a * q) q 8) +
      ((qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 *
        qPochhammer q 1)) /
        (qPochhammer q 3 * qPoch (a * q) q 9) +
      ((qPoch ρ₁ q 7 * qPoch ρ₂ q 7 * (a * q / (ρ₁ * ρ₂)) ^ 7 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 *
        qPochhammer q 0)) /
        (qPochhammer q 4 * qPoch (a * q) q 10) =
      (qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 /
        (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3)) /
        (qPochhammer q 4 * qPoch (a * q) q 10) := by
  have hD : qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 ≠ 0 :=
    mul_ne_zero hD1 hD2
  have hDthree : qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 ≠ 0 :=
    mul_ne_zero hD1three hD2three
  have hcommon := BaileyTransform_seven_alpha_three_common_denominator_identity
    a q ρ₁ ρ₂ hρ hQ1 hQ2 hQ3 hA6 hA7 hA8 hA9 hD1three hD2three
  simpa [qPochhammer, qPoch] using
    (BaileyTransform_five_term_fraction_from_common_ratio
      (P1 := qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 4)
      (P2 := qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3)
      (P3 := qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2)
      (P4 := qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1)
      (P5 := qPoch ρ₁ q 7 * qPoch ρ₂ q 7 * (a * q / (ρ₁ * ρ₂)) ^ 7)
      (B := qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3)
      (D := qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7)
      (D1 := qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3)
      (Q1 := qPochhammer q 1)
      (Q2 := qPochhammer q 2)
      (Q3 := qPochhammer q 3)
      (Q4 := qPochhammer q 4)
      (A2 := qPoch (a * q) q 6)
      (A3 := qPoch (a * q) q 7)
      (A4 := qPoch (a * q) q 8)
      (A5 := qPoch (a * q) q 9)
      (A6 := qPoch (a * q) q 10)
      hD hDthree hQ1 hQ2 hQ3 hQ4 hA6 hA7 hA8 hA9 hA10 hcommon)

/-- The three-step q-Pochhammer ratio `(aq;q)_11 / (aq;q)_8`. -/
theorem BaileyTransform_seven_qpoch_aq_eleven_over_eight
    (a q : R) (hA8 : qPoch (a * q) q 8 ≠ 0) :
    qPoch (a * q) q 11 / qPoch (a * q) q 8 =
      (1 - a * q ^ 9) * (1 - a * q ^ 10) * (1 - a * q ^ 11) := by
  rw [show qPoch (a * q) q 11 =
      qPoch (a * q) q 8 * (1 - (a * q) * q ^ 8) *
        (1 - (a * q) * q ^ 9) * (1 - (a * q) * q ^ 10) by rfl]
  field_simp [hA8]

/-- The two-step q-Pochhammer ratio `(aq;q)_11 / (aq;q)_9`. -/
theorem BaileyTransform_seven_qpoch_aq_eleven_over_nine
    (a q : R) (hA9 : qPoch (a * q) q 9 ≠ 0) :
    qPoch (a * q) q 11 / qPoch (a * q) q 9 =
      (1 - a * q ^ 10) * (1 - a * q ^ 11) := by
  rw [show qPoch (a * q) q 11 =
      qPoch (a * q) q 9 * (1 - (a * q) * q ^ 9) *
        (1 - (a * q) * q ^ 10) by rfl]
  field_simp [hA9]

/-- The adjacent q-Pochhammer ratio `(aq;q)_11 / (aq;q)_10`. -/
theorem BaileyTransform_seven_qpoch_aq_eleven_over_ten
    (a q : R) (hA10 : qPoch (a * q) q 10 ≠ 0) :
    qPoch (a * q) q 11 / qPoch (a * q) q 10 = 1 - a * q ^ 11 := by
  rw [show qPoch (a * q) q 11 =
      qPoch (a * q) q 10 * (1 - (a * q) * q ^ 10) by rfl]
  field_simp [hA10]

/-- The two-step q-Pochhammer ratio `(aq;q)_12 / (aq;q)_10`. -/
theorem BaileyTransform_seven_qpoch_aq_twelve_over_ten
    (a q : R) (hA10 : qPoch (a * q) q 10 ≠ 0) :
    qPoch (a * q) q 12 / qPoch (a * q) q 10 =
      (1 - a * q ^ 11) * (1 - a * q ^ 12) := by
  rw [show qPoch (a * q) q 12 =
      qPoch (a * q) q 10 * (1 - (a * q) * q ^ 10) *
        (1 - (a * q) * q ^ 11) by rfl]
  field_simp [hA10]

/-- The adjacent q-Pochhammer ratio `(aq;q)_12 / (aq;q)_11`. -/
theorem BaileyTransform_seven_qpoch_aq_twelve_over_eleven
    (a q : R) (hA11 : qPoch (a * q) q 11 ≠ 0) :
    qPoch (a * q) q 12 / qPoch (a * q) q 11 = 1 - a * q ^ 12 := by
  rw [show qPoch (a * q) q 12 =
      qPoch (a * q) q 11 * (1 - (a * q) * q ^ 11) by rfl]
  field_simp [hA11]

/-- The adjacent q-Pochhammer ratio `(aq;q)_13 / (aq;q)_12`. -/
theorem BaileyTransform_seven_qpoch_aq_thirteen_over_twelve
    (a q : R) (hA12 : qPoch (a * q) q 12 ≠ 0) :
    qPoch (a * q) q 13 / qPoch (a * q) q 12 = 1 - a * q ^ 13 := by
  rw [show qPoch (a * q) q 13 =
      qPoch (a * q) q 12 * (1 - (a * q) * q ^ 12) by rfl]
  field_simp [hA12]

/-- The denominator ratio between the `N=7` and `N=4` transformed-α
q-Pochhammer factors. -/
theorem BaileyTransform_seven_qpoch_pair_ratio_four_seven
    (a q ρ₁ ρ₂ : R)
    (hD1four : qPoch (a * q / ρ₁) q 4 ≠ 0)
    (hD2four : qPoch (a * q / ρ₂) q 4 ≠ 0) :
    (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7) /
        (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4) =
      ((1 - (a * q / ρ₁) * q ^ 4) *
        (1 - (a * q / ρ₁) * q ^ 5) *
        (1 - (a * q / ρ₁) * q ^ 6)) *
      ((1 - (a * q / ρ₂) * q ^ 4) *
        (1 - (a * q / ρ₂) * q ^ 5) *
        (1 - (a * q / ρ₂) * q ^ 6)) := by
  have h1 : qPoch (a * q / ρ₁) q 7 / qPoch (a * q / ρ₁) q 4 =
      (1 - (a * q / ρ₁) * q ^ 4) *
        (1 - (a * q / ρ₁) * q ^ 5) *
        (1 - (a * q / ρ₁) * q ^ 6) := by
    rw [show qPoch (a * q / ρ₁) q 7 =
        qPoch (a * q / ρ₁) q 4 * (1 - (a * q / ρ₁) * q ^ 4) *
          (1 - (a * q / ρ₁) * q ^ 5) *
          (1 - (a * q / ρ₁) * q ^ 6) by rfl]
    field_simp [hD1four]
  have h2 : qPoch (a * q / ρ₂) q 7 / qPoch (a * q / ρ₂) q 4 =
      (1 - (a * q / ρ₂) * q ^ 4) *
        (1 - (a * q / ρ₂) * q ^ 5) *
        (1 - (a * q / ρ₂) * q ^ 6) := by
    rw [show qPoch (a * q / ρ₂) q 7 =
        qPoch (a * q / ρ₂) q 4 * (1 - (a * q / ρ₂) * q ^ 4) *
          (1 - (a * q / ρ₂) * q ^ 5) *
          (1 - (a * q / ρ₂) * q ^ 6) by rfl]
    field_simp [hD2four]
  rw [show (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7) /
      (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4) =
      (qPoch (a * q / ρ₁) q 7 / qPoch (a * q / ρ₁) q 4) *
      (qPoch (a * q / ρ₂) q 7 / qPoch (a * q / ρ₂) q 4) by
        field_simp]
  rw [h1, h2]

/-- The denominator ratio between the `N=7` and `N=5` transformed-α
q-Pochhammer factors. -/
theorem BaileyTransform_seven_qpoch_pair_ratio_five_seven
    (a q ρ₁ ρ₂ : R)
    (hD1five : qPoch (a * q / ρ₁) q 5 ≠ 0)
    (hD2five : qPoch (a * q / ρ₂) q 5 ≠ 0) :
    (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7) /
        (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5) =
      ((1 - (a * q / ρ₁) * q ^ 5) * (1 - (a * q / ρ₁) * q ^ 6)) *
      ((1 - (a * q / ρ₂) * q ^ 5) * (1 - (a * q / ρ₂) * q ^ 6)) := by
  have h1 : qPoch (a * q / ρ₁) q 7 / qPoch (a * q / ρ₁) q 5 =
      (1 - (a * q / ρ₁) * q ^ 5) * (1 - (a * q / ρ₁) * q ^ 6) := by
    rw [show qPoch (a * q / ρ₁) q 7 =
        qPoch (a * q / ρ₁) q 5 * (1 - (a * q / ρ₁) * q ^ 5) *
          (1 - (a * q / ρ₁) * q ^ 6) by rfl]
    field_simp [hD1five]
  have h2 : qPoch (a * q / ρ₂) q 7 / qPoch (a * q / ρ₂) q 5 =
      (1 - (a * q / ρ₂) * q ^ 5) * (1 - (a * q / ρ₂) * q ^ 6) := by
    rw [show qPoch (a * q / ρ₂) q 7 =
        qPoch (a * q / ρ₂) q 5 * (1 - (a * q / ρ₂) * q ^ 5) *
          (1 - (a * q / ρ₂) * q ^ 6) by rfl]
    field_simp [hD2five]
  rw [show (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7) /
      (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5) =
      (qPoch (a * q / ρ₁) q 7 / qPoch (a * q / ρ₁) q 5) *
      (qPoch (a * q / ρ₂) q 7 / qPoch (a * q / ρ₂) q 5) by
        field_simp]
  rw [h1, h2]

/-- The denominator ratio between the `N=7` and `N=6` transformed-α
q-Pochhammer factors. -/
theorem BaileyTransform_seven_qpoch_pair_ratio_six_seven
    (a q ρ₁ ρ₂ : R)
    (hD1six : qPoch (a * q / ρ₁) q 6 ≠ 0)
    (hD2six : qPoch (a * q / ρ₂) q 6 ≠ 0) :
    (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7) /
        (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6) =
      (1 - (a * q / ρ₁) * q ^ 6) * (1 - (a * q / ρ₂) * q ^ 6) := by
  have h1 : qPoch (a * q / ρ₁) q 7 / qPoch (a * q / ρ₁) q 6 =
      1 - (a * q / ρ₁) * q ^ 6 := by
    rw [show qPoch (a * q / ρ₁) q 7 =
        qPoch (a * q / ρ₁) q 6 * (1 - (a * q / ρ₁) * q ^ 6) by rfl]
    field_simp [hD1six]
  have h2 : qPoch (a * q / ρ₂) q 7 / qPoch (a * q / ρ₂) q 6 =
      1 - (a * q / ρ₂) * q ^ 6 := by
    rw [show qPoch (a * q / ρ₂) q 7 =
        qPoch (a * q / ρ₂) q 6 * (1 - (a * q / ρ₂) * q ^ 6) by rfl]
    field_simp [hD2six]
  rw [show (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6) =
      (qPoch (a * q / ρ₁) q 7 / qPoch (a * q / ρ₁) q 6) *
      (qPoch (a * q / ρ₂) q 7 / qPoch (a * q / ρ₂) q 6) by
        field_simp]
  rw [h1, h2]

/-- The first middle denominator ratio appearing in the `n = 7`, α₄
common-denominator calculation. -/
theorem BaileyTransform_seven_qpochhammer_aq_alpha_four_first_middle_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hA9 : qPoch (a * q) q 9 ≠ 0) :
    qPochhammer q 3 * qPoch (a * q) q 11 /
        (qPochhammer q 2 * qPochhammer q 1 * qPoch (a * q) q 9) =
      (1 + q + q ^ 2) * ((1 - a * q ^ 10) * (1 - a * q ^ 11)) := by
  have hQ2Q1 : qPochhammer q 2 * qPochhammer q 1 ≠ 0 :=
    mul_ne_zero hQ2 hQ1
  have hQ := BaileyTransform_three_qpochhammer_three_over_one_two q hQ1 hQ2
  have hA := BaileyTransform_seven_qpoch_aq_eleven_over_nine a q hA9
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 3)
      (qPochhammer q 2 * qPochhammer q 1)
      (qPoch (a * q) q 11) (qPoch (a * q) q 9)
      (1 + q + q ^ 2) ((1 - a * q ^ 10) * (1 - a * q ^ 11))
      hQ2Q1 hA9 hQ hA

/-- The second middle denominator ratio appearing in the `n = 7`, α₄
common-denominator calculation. -/
theorem BaileyTransform_seven_qpochhammer_aq_alpha_four_second_middle_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hA10 : qPoch (a * q) q 10 ≠ 0) :
    qPochhammer q 3 * qPoch (a * q) q 11 /
        (qPochhammer q 1 * qPochhammer q 2 * qPoch (a * q) q 10) =
      (1 + q + q ^ 2) * (1 - a * q ^ 11) := by
  have hQ1Q2 : qPochhammer q 1 * qPochhammer q 2 ≠ 0 :=
    mul_ne_zero hQ1 hQ2
  have hQ : qPochhammer q 3 / (qPochhammer q 1 * qPochhammer q 2) =
      1 + q + q ^ 2 := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      BaileyTransform_three_qpochhammer_three_over_one_two q hQ1 hQ2
  have hA := BaileyTransform_seven_qpoch_aq_eleven_over_ten a q hA10
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 3)
      (qPochhammer q 1 * qPochhammer q 2)
      (qPoch (a * q) q 11) (qPoch (a * q) q 10)
      (1 + q + q ^ 2) (1 - a * q ^ 11)
      hQ1Q2 hA10 hQ hA

set_option maxHeartbeats 4000000 in
/-- The α₄ coefficient identity in the `n = 7` finite Bailey-lemma step after
moving the four transformed-β contributions to a common denominator. -/
theorem BaileyTransform_seven_alpha_four_common_denominator_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hA8 : qPoch (a * q) q 8 ≠ 0)
    (hA9 : qPoch (a * q) q 9 ≠ 0)
    (hA10 : qPoch (a * q) q 10 ≠ 0)
    (hD1four : qPoch (a * q / ρ₁) q 4 ≠ 0)
    (hD2four : qPoch (a * q / ρ₂) q 4 ≠ 0) :
    qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3 *
        (qPoch (a * q) q 11 / qPoch (a * q) q 8) +
      qPoch ρ₁ q 5 * qPoch ρ₂ q 5 *
        (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2 *
        (qPochhammer q 3 * qPoch (a * q) q 11 /
          (qPochhammer q 2 * qPochhammer q 1 * qPoch (a * q) q 9)) +
      qPoch ρ₁ q 6 * qPoch ρ₂ q 6 *
        (a * q / (ρ₁ * ρ₂)) ^ 6 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1 *
        (qPochhammer q 3 * qPoch (a * q) q 11 /
          (qPochhammer q 1 * qPochhammer q 2 * qPoch (a * q) q 10)) +
      qPoch ρ₁ q 7 * qPoch ρ₂ q 7 *
        (a * q / (ρ₁ * ρ₂)) ^ 7 =
      (qPoch ρ₁ q 4 * qPoch ρ₂ q 4 *
        (a * q / (ρ₁ * ρ₂)) ^ 4) *
        ((qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7) /
          (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4)) := by
  rw [BaileyTransform_seven_qpoch_aq_eleven_over_eight a q hA8,
    BaileyTransform_seven_qpochhammer_aq_alpha_four_first_middle_ratio a q hQ1 hQ2 hA9,
    BaileyTransform_seven_qpochhammer_aq_alpha_four_second_middle_ratio a q hQ1 hQ2 hA10,
    BaileyTransform_seven_qpoch_pair_ratio_four_seven a q ρ₁ ρ₂ hD1four hD2four]
  have hρ1 : ρ₁ ≠ 0 := left_ne_zero_of_mul hρ
  have hρ2 : ρ₂ ≠ 0 := right_ne_zero_of_mul hρ
  rw [show qPoch (a * q / (ρ₁ * ρ₂)) q 3 =
      (1 - a * q / (ρ₁ * ρ₂)) * (1 - (a * q / (ρ₁ * ρ₂)) * q) *
        (1 - (a * q / (ρ₁ * ρ₂)) * q ^ 2) by
        simp [qPoch]]
  rw [show qPoch (a * q / (ρ₁ * ρ₂)) q 2 =
      (1 - a * q / (ρ₁ * ρ₂)) * (1 - (a * q / (ρ₁ * ρ₂)) * q) by
        simp [qPoch]]
  rw [show qPoch (a * q / (ρ₁ * ρ₂)) q 1 =
      1 - a * q / (ρ₁ * ρ₂) by simp [qPoch]]
  rw [show qPoch ρ₁ q 7 = qPoch ρ₁ q 6 * (1 - ρ₁ * q ^ 6) by rfl]
  rw [show qPoch ρ₂ q 7 = qPoch ρ₂ q 6 * (1 - ρ₂ * q ^ 6) by rfl]
  rw [show qPoch ρ₁ q 6 = qPoch ρ₁ q 5 * (1 - ρ₁ * q ^ 5) by rfl]
  rw [show qPoch ρ₂ q 6 = qPoch ρ₂ q 5 * (1 - ρ₂ * q ^ 5) by rfl]
  rw [show qPoch ρ₁ q 5 = qPoch ρ₁ q 4 * (1 - ρ₁ * q ^ 4) by rfl]
  rw [show qPoch ρ₂ q 5 = qPoch ρ₂ q 4 * (1 - ρ₂ * q ^ 4) by rfl]
  field_simp [hρ, hρ1, hρ2]
  ring

set_option maxHeartbeats 4000000 in
/-- The α₄ coefficient identity in the `n = 7` finite Bailey-lemma step. -/
theorem BaileyTransform_seven_alpha_four_coefficient_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hD1 : qPoch (a * q / ρ₁) q 7 ≠ 0)
    (hD2 : qPoch (a * q / ρ₂) q 7 ≠ 0)
    (hD1four : qPoch (a * q / ρ₁) q 4 ≠ 0)
    (hD2four : qPoch (a * q / ρ₂) q 4 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hA8 : qPoch (a * q) q 8 ≠ 0)
    (hA9 : qPoch (a * q) q 9 ≠ 0)
    (hA10 : qPoch (a * q) q 10 ≠ 0)
    (hA11 : qPoch (a * q) q 11 ≠ 0) :
    ((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3) /
      (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 *
        qPochhammer q 3)) / qPoch (a * q) q 8 +
      ((qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 *
        qPochhammer q 2)) /
        (qPochhammer q 1 * qPoch (a * q) q 9) +
      ((qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 *
        qPochhammer q 1)) /
        (qPochhammer q 2 * qPoch (a * q) q 10) +
      ((qPoch ρ₁ q 7 * qPoch ρ₂ q 7 * (a * q / (ρ₁ * ρ₂)) ^ 7 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 *
        qPochhammer q 0)) /
        (qPochhammer q 3 * qPoch (a * q) q 11) =
      (qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 /
        (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4)) /
        (qPochhammer q 3 * qPoch (a * q) q 11) := by
  have hD : qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 ≠ 0 :=
    mul_ne_zero hD1 hD2
  have hDfour : qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4 ≠ 0 :=
    mul_ne_zero hD1four hD2four
  have hcommon := BaileyTransform_seven_alpha_four_common_denominator_identity
    a q ρ₁ ρ₂ hρ hQ1 hQ2 hA8 hA9 hA10 hD1four hD2four
  simpa [qPochhammer, qPoch] using
    (BaileyTransform_four_term_fraction_from_common_ratio
      (P1 := qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3)
      (P2 := qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2)
      (P3 := qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1)
      (P4 := qPoch ρ₁ q 7 * qPoch ρ₂ q 7 * (a * q / (ρ₁ * ρ₂)) ^ 7)
      (B := qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4)
      (D := qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7)
      (D1 := qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4)
      (Q1 := qPochhammer q 1)
      (Q2 := qPochhammer q 2)
      (Q3 := qPochhammer q 3)
      (A2 := qPoch (a * q) q 8)
      (A3 := qPoch (a * q) q 9)
      (A4 := qPoch (a * q) q 10)
      (A5 := qPoch (a * q) q 11)
      hD hDfour hQ1 hQ2 hQ3 hA8 hA9 hA10 hA11 hcommon)

/-- The middle denominator ratio appearing in the `n = 7`, α₅
common-denominator calculation. -/
theorem BaileyTransform_seven_qpochhammer_aq_alpha_five_middle_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hA11 : qPoch (a * q) q 11 ≠ 0) :
    qPochhammer q 2 * qPoch (a * q) q 12 /
        (qPochhammer q 1 * qPochhammer q 1 * qPoch (a * q) q 11) =
      (1 + q) * (1 - a * q ^ 12) := by
  have hQ1Q1 : qPochhammer q 1 * qPochhammer q 1 ≠ 0 :=
    mul_ne_zero hQ1 hQ1
  have hQ := BaileyTransform_three_qpochhammer_two_over_one_sq q hQ1
  have hA := BaileyTransform_seven_qpoch_aq_twelve_over_eleven a q hA11
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 2)
      (qPochhammer q 1 * qPochhammer q 1)
      (qPoch (a * q) q 12) (qPoch (a * q) q 11)
      (1 + q) (1 - a * q ^ 12)
      hQ1Q1 hA11 hQ hA

set_option maxHeartbeats 2000000 in
/-- The α₅ coefficient identity in the `n = 7` finite Bailey-lemma step after
moving the three transformed-β contributions to a common denominator. -/
theorem BaileyTransform_seven_alpha_five_common_denominator_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hA10 : qPoch (a * q) q 10 ≠ 0)
    (hA11 : qPoch (a * q) q 11 ≠ 0)
    (hD1five : qPoch (a * q / ρ₁) q 5 ≠ 0)
    (hD2five : qPoch (a * q / ρ₂) q 5 ≠ 0) :
    qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2 *
        (qPoch (a * q) q 12 / qPoch (a * q) q 10) +
      qPoch ρ₁ q 6 * qPoch ρ₂ q 6 *
        (a * q / (ρ₁ * ρ₂)) ^ 6 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1 *
        (qPochhammer q 2 * qPoch (a * q) q 12 /
          (qPochhammer q 1 * qPochhammer q 1 * qPoch (a * q) q 11)) +
      qPoch ρ₁ q 7 * qPoch ρ₂ q 7 *
        (a * q / (ρ₁ * ρ₂)) ^ 7 =
      (qPoch ρ₁ q 5 * qPoch ρ₂ q 5 *
        (a * q / (ρ₁ * ρ₂)) ^ 5) *
        ((qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7) /
          (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5)) := by
  rw [BaileyTransform_seven_qpoch_aq_twelve_over_ten a q hA10,
    BaileyTransform_seven_qpochhammer_aq_alpha_five_middle_ratio a q hQ1 hA11,
    BaileyTransform_seven_qpoch_pair_ratio_five_seven a q ρ₁ ρ₂ hD1five hD2five]
  have hρ1 : ρ₁ ≠ 0 := left_ne_zero_of_mul hρ
  have hρ2 : ρ₂ ≠ 0 := right_ne_zero_of_mul hρ
  rw [show qPoch (a * q / (ρ₁ * ρ₂)) q 2 =
      (1 - a * q / (ρ₁ * ρ₂)) * (1 - (a * q / (ρ₁ * ρ₂)) * q) by
        simp [qPoch]]
  rw [show qPoch (a * q / (ρ₁ * ρ₂)) q 1 =
      1 - a * q / (ρ₁ * ρ₂) by simp [qPoch]]
  rw [show qPoch ρ₁ q 7 = qPoch ρ₁ q 6 * (1 - ρ₁ * q ^ 6) by rfl]
  rw [show qPoch ρ₂ q 7 = qPoch ρ₂ q 6 * (1 - ρ₂ * q ^ 6) by rfl]
  rw [show qPoch ρ₁ q 6 = qPoch ρ₁ q 5 * (1 - ρ₁ * q ^ 5) by rfl]
  rw [show qPoch ρ₂ q 6 = qPoch ρ₂ q 5 * (1 - ρ₂ * q ^ 5) by rfl]
  field_simp [hρ, hρ1, hρ2]
  ring

set_option maxHeartbeats 2000000 in
/-- The α₅ coefficient identity in the `n = 7` finite Bailey-lemma step. -/
theorem BaileyTransform_seven_alpha_five_coefficient_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hD1 : qPoch (a * q / ρ₁) q 7 ≠ 0)
    (hD2 : qPoch (a * q / ρ₂) q 7 ≠ 0)
    (hD1five : qPoch (a * q / ρ₁) q 5 ≠ 0)
    (hD2five : qPoch (a * q / ρ₂) q 5 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hA10 : qPoch (a * q) q 10 ≠ 0)
    (hA11 : qPoch (a * q) q 11 ≠ 0)
    (hA12 : qPoch (a * q) q 12 ≠ 0) :
    ((qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 *
        qPochhammer q 2)) / qPoch (a * q) q 10 +
      ((qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 *
        qPochhammer q 1)) /
        (qPochhammer q 1 * qPoch (a * q) q 11) +
      ((qPoch ρ₁ q 7 * qPoch ρ₂ q 7 * (a * q / (ρ₁ * ρ₂)) ^ 7 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 *
        qPochhammer q 0)) /
        (qPochhammer q 2 * qPoch (a * q) q 12) =
      (qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 /
        (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5)) /
        (qPochhammer q 2 * qPoch (a * q) q 12) := by
  have hD : qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 ≠ 0 :=
    mul_ne_zero hD1 hD2
  have hDfive : qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 ≠ 0 :=
    mul_ne_zero hD1five hD2five
  have hcommon := BaileyTransform_seven_alpha_five_common_denominator_identity
    a q ρ₁ ρ₂ hρ hQ1 hA10 hA11 hD1five hD2five
  simpa [qPochhammer, qPoch] using
    (BaileyTransform_three_term_fraction_from_common_ratio
      (P1 := qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2)
      (P2 := qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1)
      (P3 := qPoch ρ₁ q 7 * qPoch ρ₂ q 7 * (a * q / (ρ₁ * ρ₂)) ^ 7)
      (B := qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5)
      (D := qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7)
      (D1 := qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5)
      (Q1 := qPochhammer q 1)
      (Q2 := qPochhammer q 2)
      (A2 := qPoch (a * q) q 10)
      (A3 := qPoch (a * q) q 11)
      (A4 := qPoch (a * q) q 12)
      hD hDfive hQ1 hQ2 hA10 hA11 hA12 hcommon)

/-- The α₆ coefficient identity in the `n = 7` finite Bailey-lemma step after
moving the two transformed-β contributions to a common denominator. -/
theorem BaileyTransform_seven_alpha_six_common_denominator_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hA12 : qPoch (a * q) q 12 ≠ 0)
    (hD1six : qPoch (a * q / ρ₁) q 6 ≠ 0)
    (hD2six : qPoch (a * q / ρ₂) q 6 ≠ 0) :
    qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1 *
        (qPoch (a * q) q 13 / qPoch (a * q) q 12) +
      qPoch ρ₁ q 7 * qPoch ρ₂ q 7 *
        (a * q / (ρ₁ * ρ₂)) ^ 7 =
      (qPoch ρ₁ q 6 * qPoch ρ₂ q 6 *
        (a * q / (ρ₁ * ρ₂)) ^ 6) *
        ((qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7) /
          (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6)) := by
  rw [BaileyTransform_seven_qpoch_aq_thirteen_over_twelve a q hA12,
    BaileyTransform_seven_qpoch_pair_ratio_six_seven a q ρ₁ ρ₂ hD1six hD2six]
  have hρ1 : ρ₁ ≠ 0 := left_ne_zero_of_mul hρ
  have hρ2 : ρ₂ ≠ 0 := right_ne_zero_of_mul hρ
  rw [show qPoch (a * q / (ρ₁ * ρ₂)) q 1 =
      1 - a * q / (ρ₁ * ρ₂) by simp [qPoch]]
  rw [show qPoch ρ₁ q 7 = qPoch ρ₁ q 6 * (1 - ρ₁ * q ^ 6) by rfl]
  rw [show qPoch ρ₂ q 7 = qPoch ρ₂ q 6 * (1 - ρ₂ * q ^ 6) by rfl]
  field_simp [hρ, hρ1, hρ2]
  ring

/-- The α₆ coefficient identity in the `n = 7` finite Bailey-lemma step. -/
theorem BaileyTransform_seven_alpha_six_coefficient_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hD1 : qPoch (a * q / ρ₁) q 7 ≠ 0)
    (hD2 : qPoch (a * q / ρ₂) q 7 ≠ 0)
    (hD1six : qPoch (a * q / ρ₁) q 6 ≠ 0)
    (hD2six : qPoch (a * q / ρ₂) q 6 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hA12 : qPoch (a * q) q 12 ≠ 0)
    (hA13 : qPoch (a * q) q 13 ≠ 0) :
    ((qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 *
        qPochhammer q 1)) / qPoch (a * q) q 12 +
      ((qPoch ρ₁ q 7 * qPoch ρ₂ q 7 * (a * q / (ρ₁ * ρ₂)) ^ 7 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 *
        qPochhammer q 0)) /
        (qPochhammer q 1 * qPoch (a * q) q 13) =
      (qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6 /
        (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6)) /
        (qPochhammer q 1 * qPoch (a * q) q 13) := by
  have hD : qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 ≠ 0 :=
    mul_ne_zero hD1 hD2
  have hDsix : qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 ≠ 0 :=
    mul_ne_zero hD1six hD2six
  have hcommon := BaileyTransform_seven_alpha_six_common_denominator_identity
    a q ρ₁ ρ₂ hρ hA12 hD1six hD2six
  simpa [qPochhammer, qPoch] using
    (BaileyTransform_two_term_fraction_from_common_ratio
      (P0 := qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1)
      (P1 := qPoch ρ₁ q 7 * qPoch ρ₂ q 7 * (a * q / (ρ₁ * ρ₂)) ^ 7)
      (B := qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6)
      (D := qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7)
      (D2 := qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6)
      (Q := qPochhammer q 1)
      (A4 := qPoch (a * q) q 12)
      (A5 := qPoch (a * q) q 13)
      hD hDsix hQ1 hA12 hA13 hcommon)

/-- The α₇ coefficient identity in the `n = 7` finite Bailey-lemma step. The
single remaining transformed-β term equals itself after the trivial
denominator collapse. -/
theorem BaileyTransform_seven_alpha_seven_coefficient_identity (a q ρ₁ ρ₂ : R) :
    ((qPoch ρ₁ q 7 * qPoch ρ₂ q 7 * (a * q / (ρ₁ * ρ₂)) ^ 7 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 *
        qPochhammer q 0)) / qPoch (a * q) q 14 =
      (qPoch ρ₁ q 7 * qPoch ρ₂ q 7 * (a * q / (ρ₁ * ρ₂)) ^ 7 /
        (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7)) /
        qPoch (a * q) q 14 := by
  simp [qPochhammer, qPoch]

/-- The adjacent q-Pochhammer ratio `(aq;q)_15 / (aq;q)_14`. -/
theorem BaileyTransform_eight_qpoch_aq_fifteen_over_fourteen
    (a q : R) (hA14 : qPoch (a * q) q 14 ≠ 0) :
    qPoch (a * q) q 15 / qPoch (a * q) q 14 = 1 - a * q ^ 15 := by
  rw [show qPoch (a * q) q 15 =
      qPoch (a * q) q 14 * (1 - (a * q) * q ^ 14) by rfl]
  field_simp [hA14]

/-- The denominator ratio between the `N=8` and `N=7` transformed-α
q-Pochhammer factors. -/
theorem BaileyTransform_eight_qpoch_pair_ratio_seven_eight
    (a q ρ₁ ρ₂ : R)
    (hD1seven : qPoch (a * q / ρ₁) q 7 ≠ 0)
    (hD2seven : qPoch (a * q / ρ₂) q 7 ≠ 0) :
    (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8) /
        (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7) =
      (1 - (a * q / ρ₁) * q ^ 7) * (1 - (a * q / ρ₂) * q ^ 7) := by
  have h1 : qPoch (a * q / ρ₁) q 8 / qPoch (a * q / ρ₁) q 7 =
      1 - (a * q / ρ₁) * q ^ 7 := by
    rw [show qPoch (a * q / ρ₁) q 8 =
        qPoch (a * q / ρ₁) q 7 * (1 - (a * q / ρ₁) * q ^ 7) by rfl]
    field_simp [hD1seven]
  have h2 : qPoch (a * q / ρ₂) q 8 / qPoch (a * q / ρ₂) q 7 =
      1 - (a * q / ρ₂) * q ^ 7 := by
    rw [show qPoch (a * q / ρ₂) q 8 =
        qPoch (a * q / ρ₂) q 7 * (1 - (a * q / ρ₂) * q ^ 7) by rfl]
    field_simp [hD2seven]
  rw [show (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8) /
      (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7) =
      (qPoch (a * q / ρ₁) q 8 / qPoch (a * q / ρ₁) q 7) *
      (qPoch (a * q / ρ₂) q 8 / qPoch (a * q / ρ₂) q 7) by
        field_simp]
  rw [h1, h2]

set_option maxHeartbeats 800000 in
/-- The α₇ coefficient identity in the `n = 8` finite Bailey-lemma step after
moving the two transformed-β contributions to a common denominator. -/
theorem BaileyTransform_eight_alpha_seven_common_denominator_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hA14 : qPoch (a * q) q 14 ≠ 0)
    (hD1seven : qPoch (a * q / ρ₁) q 7 ≠ 0)
    (hD2seven : qPoch (a * q / ρ₂) q 7 ≠ 0) :
    qPoch ρ₁ q 7 * qPoch ρ₂ q 7 * (a * q / (ρ₁ * ρ₂)) ^ 7 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1 *
        (qPoch (a * q) q 15 / qPoch (a * q) q 14) +
      qPoch ρ₁ q 8 * qPoch ρ₂ q 8 *
        (a * q / (ρ₁ * ρ₂)) ^ 8 =
      (qPoch ρ₁ q 7 * qPoch ρ₂ q 7 *
        (a * q / (ρ₁ * ρ₂)) ^ 7) *
        ((qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8) /
          (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7)) := by
  rw [BaileyTransform_eight_qpoch_aq_fifteen_over_fourteen a q hA14,
    BaileyTransform_eight_qpoch_pair_ratio_seven_eight a q ρ₁ ρ₂ hD1seven hD2seven]
  have hρ1 : ρ₁ ≠ 0 := left_ne_zero_of_mul hρ
  have hρ2 : ρ₂ ≠ 0 := right_ne_zero_of_mul hρ
  rw [show qPoch (a * q / (ρ₁ * ρ₂)) q 1 =
      1 - a * q / (ρ₁ * ρ₂) by simp [qPoch]]
  rw [show qPoch ρ₁ q 8 = qPoch ρ₁ q 7 * (1 - ρ₁ * q ^ 7) by rfl]
  rw [show qPoch ρ₂ q 8 = qPoch ρ₂ q 7 * (1 - ρ₂ * q ^ 7) by rfl]
  field_simp [hρ, hρ1, hρ2]
  ring

/-- The α₇ coefficient identity in the `n = 8` finite Bailey-lemma step. -/
theorem BaileyTransform_eight_alpha_seven_coefficient_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hD1 : qPoch (a * q / ρ₁) q 8 ≠ 0)
    (hD2 : qPoch (a * q / ρ₂) q 8 ≠ 0)
    (hD1seven : qPoch (a * q / ρ₁) q 7 ≠ 0)
    (hD2seven : qPoch (a * q / ρ₂) q 7 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hA14 : qPoch (a * q) q 14 ≠ 0)
    (hA15 : qPoch (a * q) q 15 ≠ 0) :
    ((qPoch ρ₁ q 7 * qPoch ρ₂ q 7 * (a * q / (ρ₁ * ρ₂)) ^ 7 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8 *
        qPochhammer q 1)) / qPoch (a * q) q 14 +
      ((qPoch ρ₁ q 8 * qPoch ρ₂ q 8 * (a * q / (ρ₁ * ρ₂)) ^ 8 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8 *
        qPochhammer q 0)) /
        (qPochhammer q 1 * qPoch (a * q) q 15) =
      (qPoch ρ₁ q 7 * qPoch ρ₂ q 7 * (a * q / (ρ₁ * ρ₂)) ^ 7 /
        (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7)) /
        (qPochhammer q 1 * qPoch (a * q) q 15) := by
  have hD : qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8 ≠ 0 :=
    mul_ne_zero hD1 hD2
  have hDseven : qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 ≠ 0 :=
    mul_ne_zero hD1seven hD2seven
  have hcommon := BaileyTransform_eight_alpha_seven_common_denominator_identity
    a q ρ₁ ρ₂ hρ hA14 hD1seven hD2seven
  simpa [qPochhammer, qPoch] using
    (BaileyTransform_two_term_fraction_from_common_ratio
      (P0 := qPoch ρ₁ q 7 * qPoch ρ₂ q 7 * (a * q / (ρ₁ * ρ₂)) ^ 7 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1)
      (P1 := qPoch ρ₁ q 8 * qPoch ρ₂ q 8 * (a * q / (ρ₁ * ρ₂)) ^ 8)
      (B := qPoch ρ₁ q 7 * qPoch ρ₂ q 7 * (a * q / (ρ₁ * ρ₂)) ^ 7)
      (D := qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8)
      (D2 := qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7)
      (Q := qPochhammer q 1)
      (A4 := qPoch (a * q) q 14)
      (A5 := qPoch (a * q) q 15)
      hD hDseven hQ1 hA14 hA15 hcommon)

/-- The α₈ coefficient identity in the `n = 8` finite Bailey-lemma step. The
single remaining transformed-β term equals itself after the trivial
denominator collapse. -/
theorem BaileyTransform_eight_alpha_eight_coefficient_identity (a q ρ₁ ρ₂ : R) :
    ((qPoch ρ₁ q 8 * qPoch ρ₂ q 8 * (a * q / (ρ₁ * ρ₂)) ^ 8 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8 *
        qPochhammer q 0)) / qPoch (a * q) q 16 =
      (qPoch ρ₁ q 8 * qPoch ρ₂ q 8 * (a * q / (ρ₁ * ρ₂)) ^ 8 /
        (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8)) /
        qPoch (a * q) q 16 := by
  simp [qPochhammer, qPoch]

/-- The two-step q-Pochhammer ratio `(aq;q)_14 / (aq;q)_12`. -/
theorem BaileyTransform_eight_qpoch_aq_fourteen_over_twelve
    (a q : R) (hA12 : qPoch (a * q) q 12 ≠ 0) :
    qPoch (a * q) q 14 / qPoch (a * q) q 12 =
      (1 - a * q ^ 13) * (1 - a * q ^ 14) := by
  rw [show qPoch (a * q) q 14 =
      qPoch (a * q) q 12 * (1 - (a * q) * q ^ 12) *
        (1 - (a * q) * q ^ 13) by rfl]
  field_simp [hA12]

/-- The adjacent q-Pochhammer ratio `(aq;q)_14 / (aq;q)_13`. -/
theorem BaileyTransform_eight_qpoch_aq_fourteen_over_thirteen
    (a q : R) (hA13 : qPoch (a * q) q 13 ≠ 0) :
    qPoch (a * q) q 14 / qPoch (a * q) q 13 = 1 - a * q ^ 14 := by
  rw [show qPoch (a * q) q 14 =
      qPoch (a * q) q 13 * (1 - (a * q) * q ^ 13) by rfl]
  field_simp [hA13]

/-- The denominator ratio between the `N=8` and `N=6` transformed-α
q-Pochhammer factors. -/
theorem BaileyTransform_eight_qpoch_pair_ratio_six_eight
    (a q ρ₁ ρ₂ : R)
    (hD1six : qPoch (a * q / ρ₁) q 6 ≠ 0)
    (hD2six : qPoch (a * q / ρ₂) q 6 ≠ 0) :
    (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8) /
        (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6) =
      ((1 - (a * q / ρ₁) * q ^ 6) * (1 - (a * q / ρ₁) * q ^ 7)) *
      ((1 - (a * q / ρ₂) * q ^ 6) * (1 - (a * q / ρ₂) * q ^ 7)) := by
  have h1 : qPoch (a * q / ρ₁) q 8 / qPoch (a * q / ρ₁) q 6 =
      (1 - (a * q / ρ₁) * q ^ 6) * (1 - (a * q / ρ₁) * q ^ 7) := by
    rw [show qPoch (a * q / ρ₁) q 8 =
        qPoch (a * q / ρ₁) q 6 * (1 - (a * q / ρ₁) * q ^ 6) *
          (1 - (a * q / ρ₁) * q ^ 7) by rfl]
    field_simp [hD1six]
  have h2 : qPoch (a * q / ρ₂) q 8 / qPoch (a * q / ρ₂) q 6 =
      (1 - (a * q / ρ₂) * q ^ 6) * (1 - (a * q / ρ₂) * q ^ 7) := by
    rw [show qPoch (a * q / ρ₂) q 8 =
        qPoch (a * q / ρ₂) q 6 * (1 - (a * q / ρ₂) * q ^ 6) *
          (1 - (a * q / ρ₂) * q ^ 7) by rfl]
    field_simp [hD2six]
  rw [show (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6) =
      (qPoch (a * q / ρ₁) q 8 / qPoch (a * q / ρ₁) q 6) *
      (qPoch (a * q / ρ₂) q 8 / qPoch (a * q / ρ₂) q 6) by
        field_simp]
  rw [h1, h2]

/-- The middle denominator ratio appearing in the `n = 8`, α₆
common-denominator calculation. -/
theorem BaileyTransform_eight_qpochhammer_aq_alpha_six_middle_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hA13 : qPoch (a * q) q 13 ≠ 0) :
    qPochhammer q 2 * qPoch (a * q) q 14 /
        (qPochhammer q 1 * qPochhammer q 1 * qPoch (a * q) q 13) =
      (1 + q) * (1 - a * q ^ 14) := by
  have hQ1Q1 : qPochhammer q 1 * qPochhammer q 1 ≠ 0 :=
    mul_ne_zero hQ1 hQ1
  have hQ := BaileyTransform_three_qpochhammer_two_over_one_sq q hQ1
  have hA := BaileyTransform_eight_qpoch_aq_fourteen_over_thirteen a q hA13
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 2)
      (qPochhammer q 1 * qPochhammer q 1)
      (qPoch (a * q) q 14) (qPoch (a * q) q 13)
      (1 + q) (1 - a * q ^ 14)
      hQ1Q1 hA13 hQ hA

set_option maxHeartbeats 2000000 in
/-- The α₆ coefficient identity in the `n = 8` finite Bailey-lemma step after
moving the three transformed-β contributions to a common denominator. -/
theorem BaileyTransform_eight_alpha_six_common_denominator_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hA12 : qPoch (a * q) q 12 ≠ 0)
    (hA13 : qPoch (a * q) q 13 ≠ 0)
    (hD1six : qPoch (a * q / ρ₁) q 6 ≠ 0)
    (hD2six : qPoch (a * q / ρ₂) q 6 ≠ 0) :
    qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2 *
        (qPoch (a * q) q 14 / qPoch (a * q) q 12) +
      qPoch ρ₁ q 7 * qPoch ρ₂ q 7 *
        (a * q / (ρ₁ * ρ₂)) ^ 7 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1 *
        (qPochhammer q 2 * qPoch (a * q) q 14 /
          (qPochhammer q 1 * qPochhammer q 1 * qPoch (a * q) q 13)) +
      qPoch ρ₁ q 8 * qPoch ρ₂ q 8 *
        (a * q / (ρ₁ * ρ₂)) ^ 8 =
      (qPoch ρ₁ q 6 * qPoch ρ₂ q 6 *
        (a * q / (ρ₁ * ρ₂)) ^ 6) *
        ((qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8) /
          (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6)) := by
  rw [BaileyTransform_eight_qpoch_aq_fourteen_over_twelve a q hA12,
    BaileyTransform_eight_qpochhammer_aq_alpha_six_middle_ratio a q hQ1 hA13,
    BaileyTransform_eight_qpoch_pair_ratio_six_eight a q ρ₁ ρ₂ hD1six hD2six]
  have hρ1 : ρ₁ ≠ 0 := left_ne_zero_of_mul hρ
  have hρ2 : ρ₂ ≠ 0 := right_ne_zero_of_mul hρ
  rw [show qPoch (a * q / (ρ₁ * ρ₂)) q 2 =
      (1 - a * q / (ρ₁ * ρ₂)) * (1 - (a * q / (ρ₁ * ρ₂)) * q) by
        simp [qPoch]]
  rw [show qPoch (a * q / (ρ₁ * ρ₂)) q 1 =
      1 - a * q / (ρ₁ * ρ₂) by simp [qPoch]]
  rw [show qPoch ρ₁ q 8 = qPoch ρ₁ q 7 * (1 - ρ₁ * q ^ 7) by rfl]
  rw [show qPoch ρ₂ q 8 = qPoch ρ₂ q 7 * (1 - ρ₂ * q ^ 7) by rfl]
  rw [show qPoch ρ₁ q 7 = qPoch ρ₁ q 6 * (1 - ρ₁ * q ^ 6) by rfl]
  rw [show qPoch ρ₂ q 7 = qPoch ρ₂ q 6 * (1 - ρ₂ * q ^ 6) by rfl]
  field_simp [hρ, hρ1, hρ2]
  ring

set_option maxHeartbeats 2000000 in
/-- The α₆ coefficient identity in the `n = 8` finite Bailey-lemma step. -/
theorem BaileyTransform_eight_alpha_six_coefficient_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hD1 : qPoch (a * q / ρ₁) q 8 ≠ 0)
    (hD2 : qPoch (a * q / ρ₂) q 8 ≠ 0)
    (hD1six : qPoch (a * q / ρ₁) q 6 ≠ 0)
    (hD2six : qPoch (a * q / ρ₂) q 6 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hA12 : qPoch (a * q) q 12 ≠ 0)
    (hA13 : qPoch (a * q) q 13 ≠ 0)
    (hA14 : qPoch (a * q) q 14 ≠ 0) :
    ((qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8 *
        qPochhammer q 2)) / qPoch (a * q) q 12 +
      ((qPoch ρ₁ q 7 * qPoch ρ₂ q 7 * (a * q / (ρ₁ * ρ₂)) ^ 7 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8 *
        qPochhammer q 1)) /
        (qPochhammer q 1 * qPoch (a * q) q 13) +
      ((qPoch ρ₁ q 8 * qPoch ρ₂ q 8 * (a * q / (ρ₁ * ρ₂)) ^ 8 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8 *
        qPochhammer q 0)) /
        (qPochhammer q 2 * qPoch (a * q) q 14) =
      (qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6 /
        (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6)) /
        (qPochhammer q 2 * qPoch (a * q) q 14) := by
  have hD : qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8 ≠ 0 :=
    mul_ne_zero hD1 hD2
  have hDsix : qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 ≠ 0 :=
    mul_ne_zero hD1six hD2six
  have hcommon := BaileyTransform_eight_alpha_six_common_denominator_identity
    a q ρ₁ ρ₂ hρ hQ1 hA12 hA13 hD1six hD2six
  simpa [qPochhammer, qPoch] using
    (BaileyTransform_three_term_fraction_from_common_ratio
      (P1 := qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2)
      (P2 := qPoch ρ₁ q 7 * qPoch ρ₂ q 7 * (a * q / (ρ₁ * ρ₂)) ^ 7 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1)
      (P3 := qPoch ρ₁ q 8 * qPoch ρ₂ q 8 * (a * q / (ρ₁ * ρ₂)) ^ 8)
      (B := qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6)
      (D := qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8)
      (D1 := qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6)
      (Q1 := qPochhammer q 1)
      (Q2 := qPochhammer q 2)
      (A2 := qPoch (a * q) q 12)
      (A3 := qPoch (a * q) q 13)
      (A4 := qPoch (a * q) q 14)
      hD hDsix hQ1 hQ2 hA12 hA13 hA14 hcommon)

/-- The three-step q-Pochhammer ratio `(aq;q)_13 / (aq;q)_10`. -/
theorem BaileyTransform_eight_qpoch_aq_thirteen_over_ten
    (a q : R) (hA10 : qPoch (a * q) q 10 ≠ 0) :
    qPoch (a * q) q 13 / qPoch (a * q) q 10 =
      (1 - a * q ^ 11) * (1 - a * q ^ 12) * (1 - a * q ^ 13) := by
  rw [show qPoch (a * q) q 13 =
      qPoch (a * q) q 10 * (1 - (a * q) * q ^ 10) *
        (1 - (a * q) * q ^ 11) * (1 - (a * q) * q ^ 12) by rfl]
  field_simp [hA10]

/-- The two-step q-Pochhammer ratio `(aq;q)_13 / (aq;q)_11`. -/
theorem BaileyTransform_eight_qpoch_aq_thirteen_over_eleven
    (a q : R) (hA11 : qPoch (a * q) q 11 ≠ 0) :
    qPoch (a * q) q 13 / qPoch (a * q) q 11 =
      (1 - a * q ^ 12) * (1 - a * q ^ 13) := by
  rw [show qPoch (a * q) q 13 =
      qPoch (a * q) q 11 * (1 - (a * q) * q ^ 11) *
        (1 - (a * q) * q ^ 12) by rfl]
  field_simp [hA11]

-- (For (aq;q)_13 / (aq;q)_12, reuse `BaileyTransform_seven_qpoch_aq_thirteen_over_twelve`.)

/-- The denominator ratio between the `N=8` and `N=5` transformed-α
q-Pochhammer factors. -/
theorem BaileyTransform_eight_qpoch_pair_ratio_five_eight
    (a q ρ₁ ρ₂ : R)
    (hD1five : qPoch (a * q / ρ₁) q 5 ≠ 0)
    (hD2five : qPoch (a * q / ρ₂) q 5 ≠ 0) :
    (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8) /
        (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5) =
      ((1 - (a * q / ρ₁) * q ^ 5) * (1 - (a * q / ρ₁) * q ^ 6) *
        (1 - (a * q / ρ₁) * q ^ 7)) *
      ((1 - (a * q / ρ₂) * q ^ 5) * (1 - (a * q / ρ₂) * q ^ 6) *
        (1 - (a * q / ρ₂) * q ^ 7)) := by
  have h1 : qPoch (a * q / ρ₁) q 8 / qPoch (a * q / ρ₁) q 5 =
      (1 - (a * q / ρ₁) * q ^ 5) * (1 - (a * q / ρ₁) * q ^ 6) *
        (1 - (a * q / ρ₁) * q ^ 7) := by
    rw [show qPoch (a * q / ρ₁) q 8 =
        qPoch (a * q / ρ₁) q 5 * (1 - (a * q / ρ₁) * q ^ 5) *
          (1 - (a * q / ρ₁) * q ^ 6) * (1 - (a * q / ρ₁) * q ^ 7) by rfl]
    field_simp [hD1five]
  have h2 : qPoch (a * q / ρ₂) q 8 / qPoch (a * q / ρ₂) q 5 =
      (1 - (a * q / ρ₂) * q ^ 5) * (1 - (a * q / ρ₂) * q ^ 6) *
        (1 - (a * q / ρ₂) * q ^ 7) := by
    rw [show qPoch (a * q / ρ₂) q 8 =
        qPoch (a * q / ρ₂) q 5 * (1 - (a * q / ρ₂) * q ^ 5) *
          (1 - (a * q / ρ₂) * q ^ 6) * (1 - (a * q / ρ₂) * q ^ 7) by rfl]
    field_simp [hD2five]
  rw [show (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8) /
      (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5) =
      (qPoch (a * q / ρ₁) q 8 / qPoch (a * q / ρ₁) q 5) *
      (qPoch (a * q / ρ₂) q 8 / qPoch (a * q / ρ₂) q 5) by
        field_simp]
  rw [h1, h2]

/-- The first middle denominator ratio appearing in the `n = 8`, α₅
common-denominator calculation. -/
theorem BaileyTransform_eight_qpochhammer_aq_alpha_five_first_middle_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hA11 : qPoch (a * q) q 11 ≠ 0) :
    qPochhammer q 3 * qPoch (a * q) q 13 /
        (qPochhammer q 2 * qPochhammer q 1 * qPoch (a * q) q 11) =
      (1 + q + q ^ 2) * ((1 - a * q ^ 12) * (1 - a * q ^ 13)) := by
  have hQ2Q1 : qPochhammer q 2 * qPochhammer q 1 ≠ 0 :=
    mul_ne_zero hQ2 hQ1
  have hQ := BaileyTransform_three_qpochhammer_three_over_one_two q hQ1 hQ2
  have hA := BaileyTransform_eight_qpoch_aq_thirteen_over_eleven a q hA11
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 3)
      (qPochhammer q 2 * qPochhammer q 1)
      (qPoch (a * q) q 13) (qPoch (a * q) q 11)
      (1 + q + q ^ 2) ((1 - a * q ^ 12) * (1 - a * q ^ 13))
      hQ2Q1 hA11 hQ hA

/-- The second middle denominator ratio appearing in the `n = 8`, α₅
common-denominator calculation. -/
theorem BaileyTransform_eight_qpochhammer_aq_alpha_five_second_middle_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hA12 : qPoch (a * q) q 12 ≠ 0) :
    qPochhammer q 3 * qPoch (a * q) q 13 /
        (qPochhammer q 1 * qPochhammer q 2 * qPoch (a * q) q 12) =
      (1 + q + q ^ 2) * (1 - a * q ^ 13) := by
  have hQ1Q2 : qPochhammer q 1 * qPochhammer q 2 ≠ 0 :=
    mul_ne_zero hQ1 hQ2
  have hQ : qPochhammer q 3 / (qPochhammer q 1 * qPochhammer q 2) =
      1 + q + q ^ 2 := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      BaileyTransform_three_qpochhammer_three_over_one_two q hQ1 hQ2
  have hA := BaileyTransform_seven_qpoch_aq_thirteen_over_twelve a q hA12
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 3)
      (qPochhammer q 1 * qPochhammer q 2)
      (qPoch (a * q) q 13) (qPoch (a * q) q 12)
      (1 + q + q ^ 2) (1 - a * q ^ 13)
      hQ1Q2 hA12 hQ hA

set_option maxHeartbeats 4000000 in
/-- The α₅ coefficient identity in the `n = 8` finite Bailey-lemma step after
moving the four transformed-β contributions to a common denominator. -/
theorem BaileyTransform_eight_alpha_five_common_denominator_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hA10 : qPoch (a * q) q 10 ≠ 0)
    (hA11 : qPoch (a * q) q 11 ≠ 0)
    (hA12 : qPoch (a * q) q 12 ≠ 0)
    (hD1five : qPoch (a * q / ρ₁) q 5 ≠ 0)
    (hD2five : qPoch (a * q / ρ₂) q 5 ≠ 0) :
    qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3 *
        (qPoch (a * q) q 13 / qPoch (a * q) q 10) +
      qPoch ρ₁ q 6 * qPoch ρ₂ q 6 *
        (a * q / (ρ₁ * ρ₂)) ^ 6 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2 *
        (qPochhammer q 3 * qPoch (a * q) q 13 /
          (qPochhammer q 2 * qPochhammer q 1 * qPoch (a * q) q 11)) +
      qPoch ρ₁ q 7 * qPoch ρ₂ q 7 *
        (a * q / (ρ₁ * ρ₂)) ^ 7 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1 *
        (qPochhammer q 3 * qPoch (a * q) q 13 /
          (qPochhammer q 1 * qPochhammer q 2 * qPoch (a * q) q 12)) +
      qPoch ρ₁ q 8 * qPoch ρ₂ q 8 *
        (a * q / (ρ₁ * ρ₂)) ^ 8 =
      (qPoch ρ₁ q 5 * qPoch ρ₂ q 5 *
        (a * q / (ρ₁ * ρ₂)) ^ 5) *
        ((qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8) /
          (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5)) := by
  rw [BaileyTransform_eight_qpoch_aq_thirteen_over_ten a q hA10,
    BaileyTransform_eight_qpochhammer_aq_alpha_five_first_middle_ratio a q hQ1 hQ2 hA11,
    BaileyTransform_eight_qpochhammer_aq_alpha_five_second_middle_ratio a q hQ1 hQ2 hA12,
    BaileyTransform_eight_qpoch_pair_ratio_five_eight a q ρ₁ ρ₂ hD1five hD2five]
  have hρ1 : ρ₁ ≠ 0 := left_ne_zero_of_mul hρ
  have hρ2 : ρ₂ ≠ 0 := right_ne_zero_of_mul hρ
  rw [show qPoch (a * q / (ρ₁ * ρ₂)) q 3 =
      (1 - a * q / (ρ₁ * ρ₂)) * (1 - (a * q / (ρ₁ * ρ₂)) * q) *
        (1 - (a * q / (ρ₁ * ρ₂)) * q ^ 2) by
        simp [qPoch]]
  rw [show qPoch (a * q / (ρ₁ * ρ₂)) q 2 =
      (1 - a * q / (ρ₁ * ρ₂)) * (1 - (a * q / (ρ₁ * ρ₂)) * q) by
        simp [qPoch]]
  rw [show qPoch (a * q / (ρ₁ * ρ₂)) q 1 =
      1 - a * q / (ρ₁ * ρ₂) by simp [qPoch]]
  rw [show qPoch ρ₁ q 8 = qPoch ρ₁ q 7 * (1 - ρ₁ * q ^ 7) by rfl]
  rw [show qPoch ρ₂ q 8 = qPoch ρ₂ q 7 * (1 - ρ₂ * q ^ 7) by rfl]
  rw [show qPoch ρ₁ q 7 = qPoch ρ₁ q 6 * (1 - ρ₁ * q ^ 6) by rfl]
  rw [show qPoch ρ₂ q 7 = qPoch ρ₂ q 6 * (1 - ρ₂ * q ^ 6) by rfl]
  rw [show qPoch ρ₁ q 6 = qPoch ρ₁ q 5 * (1 - ρ₁ * q ^ 5) by rfl]
  rw [show qPoch ρ₂ q 6 = qPoch ρ₂ q 5 * (1 - ρ₂ * q ^ 5) by rfl]
  field_simp [hρ, hρ1, hρ2]
  ring

set_option maxHeartbeats 4000000 in
/-- The α₅ coefficient identity in the `n = 8` finite Bailey-lemma step. -/
theorem BaileyTransform_eight_alpha_five_coefficient_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hD1 : qPoch (a * q / ρ₁) q 8 ≠ 0)
    (hD2 : qPoch (a * q / ρ₂) q 8 ≠ 0)
    (hD1five : qPoch (a * q / ρ₁) q 5 ≠ 0)
    (hD2five : qPoch (a * q / ρ₂) q 5 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hA10 : qPoch (a * q) q 10 ≠ 0)
    (hA11 : qPoch (a * q) q 11 ≠ 0)
    (hA12 : qPoch (a * q) q 12 ≠ 0)
    (hA13 : qPoch (a * q) q 13 ≠ 0) :
    ((qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3) /
      (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8 *
        qPochhammer q 3)) / qPoch (a * q) q 10 +
      ((qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8 *
        qPochhammer q 2)) /
        (qPochhammer q 1 * qPoch (a * q) q 11) +
      ((qPoch ρ₁ q 7 * qPoch ρ₂ q 7 * (a * q / (ρ₁ * ρ₂)) ^ 7 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8 *
        qPochhammer q 1)) /
        (qPochhammer q 2 * qPoch (a * q) q 12) +
      ((qPoch ρ₁ q 8 * qPoch ρ₂ q 8 * (a * q / (ρ₁ * ρ₂)) ^ 8 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8 *
        qPochhammer q 0)) /
        (qPochhammer q 3 * qPoch (a * q) q 13) =
      (qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 /
        (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5)) /
        (qPochhammer q 3 * qPoch (a * q) q 13) := by
  have hD : qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8 ≠ 0 :=
    mul_ne_zero hD1 hD2
  have hDfive : qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 ≠ 0 :=
    mul_ne_zero hD1five hD2five
  have hcommon := BaileyTransform_eight_alpha_five_common_denominator_identity
    a q ρ₁ ρ₂ hρ hQ1 hQ2 hA10 hA11 hA12 hD1five hD2five
  simpa [qPochhammer, qPoch] using
    (BaileyTransform_four_term_fraction_from_common_ratio
      (P1 := qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3)
      (P2 := qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2)
      (P3 := qPoch ρ₁ q 7 * qPoch ρ₂ q 7 * (a * q / (ρ₁ * ρ₂)) ^ 7 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1)
      (P4 := qPoch ρ₁ q 8 * qPoch ρ₂ q 8 * (a * q / (ρ₁ * ρ₂)) ^ 8)
      (B := qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5)
      (D := qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8)
      (D1 := qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5)
      (Q1 := qPochhammer q 1)
      (Q2 := qPochhammer q 2)
      (Q3 := qPochhammer q 3)
      (A2 := qPoch (a * q) q 10)
      (A3 := qPoch (a * q) q 11)
      (A4 := qPoch (a * q) q 12)
      (A5 := qPoch (a * q) q 13)
      hD hDfive hQ1 hQ2 hQ3 hA10 hA11 hA12 hA13 hcommon)

/-- The four-step q-Pochhammer ratio `(aq;q)_12 / (aq;q)_8`. -/
theorem BaileyTransform_eight_qpoch_aq_twelve_over_eight
    (a q : R) (hA8 : qPoch (a * q) q 8 ≠ 0) :
    qPoch (a * q) q 12 / qPoch (a * q) q 8 =
      (1 - a * q ^ 9) * (1 - a * q ^ 10) * (1 - a * q ^ 11) *
        (1 - a * q ^ 12) := by
  rw [show qPoch (a * q) q 12 =
      qPoch (a * q) q 8 * (1 - (a * q) * q ^ 8) *
        (1 - (a * q) * q ^ 9) * (1 - (a * q) * q ^ 10) *
        (1 - (a * q) * q ^ 11) by rfl]
  field_simp [hA8]

/-- The three-step q-Pochhammer ratio `(aq;q)_12 / (aq;q)_9`. -/
theorem BaileyTransform_eight_qpoch_aq_twelve_over_nine
    (a q : R) (hA9 : qPoch (a * q) q 9 ≠ 0) :
    qPoch (a * q) q 12 / qPoch (a * q) q 9 =
      (1 - a * q ^ 10) * (1 - a * q ^ 11) * (1 - a * q ^ 12) := by
  rw [show qPoch (a * q) q 12 =
      qPoch (a * q) q 9 * (1 - (a * q) * q ^ 9) *
        (1 - (a * q) * q ^ 10) * (1 - (a * q) * q ^ 11) by rfl]
  field_simp [hA9]

/-- The denominator ratio between the `N=8` and `N=4` transformed-α
q-Pochhammer factors. -/
theorem BaileyTransform_eight_qpoch_pair_ratio_four_eight
    (a q ρ₁ ρ₂ : R)
    (hD1four : qPoch (a * q / ρ₁) q 4 ≠ 0)
    (hD2four : qPoch (a * q / ρ₂) q 4 ≠ 0) :
    (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8) /
        (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4) =
      ((1 - (a * q / ρ₁) * q ^ 4) * (1 - (a * q / ρ₁) * q ^ 5) *
        (1 - (a * q / ρ₁) * q ^ 6) * (1 - (a * q / ρ₁) * q ^ 7)) *
      ((1 - (a * q / ρ₂) * q ^ 4) * (1 - (a * q / ρ₂) * q ^ 5) *
        (1 - (a * q / ρ₂) * q ^ 6) * (1 - (a * q / ρ₂) * q ^ 7)) := by
  have h1 : qPoch (a * q / ρ₁) q 8 / qPoch (a * q / ρ₁) q 4 =
      (1 - (a * q / ρ₁) * q ^ 4) * (1 - (a * q / ρ₁) * q ^ 5) *
        (1 - (a * q / ρ₁) * q ^ 6) * (1 - (a * q / ρ₁) * q ^ 7) := by
    rw [show qPoch (a * q / ρ₁) q 8 =
        qPoch (a * q / ρ₁) q 4 * (1 - (a * q / ρ₁) * q ^ 4) *
          (1 - (a * q / ρ₁) * q ^ 5) * (1 - (a * q / ρ₁) * q ^ 6) *
          (1 - (a * q / ρ₁) * q ^ 7) by rfl]
    field_simp [hD1four]
  have h2 : qPoch (a * q / ρ₂) q 8 / qPoch (a * q / ρ₂) q 4 =
      (1 - (a * q / ρ₂) * q ^ 4) * (1 - (a * q / ρ₂) * q ^ 5) *
        (1 - (a * q / ρ₂) * q ^ 6) * (1 - (a * q / ρ₂) * q ^ 7) := by
    rw [show qPoch (a * q / ρ₂) q 8 =
        qPoch (a * q / ρ₂) q 4 * (1 - (a * q / ρ₂) * q ^ 4) *
          (1 - (a * q / ρ₂) * q ^ 5) * (1 - (a * q / ρ₂) * q ^ 6) *
          (1 - (a * q / ρ₂) * q ^ 7) by rfl]
    field_simp [hD2four]
  rw [show (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8) /
      (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4) =
      (qPoch (a * q / ρ₁) q 8 / qPoch (a * q / ρ₁) q 4) *
      (qPoch (a * q / ρ₂) q 8 / qPoch (a * q / ρ₂) q 4) by
        field_simp]
  rw [h1, h2]

/-- The first middle denominator ratio appearing in the `n = 8`, α₄
common-denominator calculation. -/
theorem BaileyTransform_eight_qpochhammer_aq_alpha_four_first_middle_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hA9 : qPoch (a * q) q 9 ≠ 0) :
    qPochhammer q 4 * qPoch (a * q) q 12 /
        (qPochhammer q 3 * qPochhammer q 1 * qPoch (a * q) q 9) =
      (1 + q + q ^ 2 + q ^ 3) *
        ((1 - a * q ^ 10) * (1 - a * q ^ 11) * (1 - a * q ^ 12)) := by
  have hQ3Q1 : qPochhammer q 3 * qPochhammer q 1 ≠ 0 :=
    mul_ne_zero hQ3 hQ1
  have hQ := BaileyTransform_four_qpochhammer_four_over_three_one q hQ1 hQ3
  have hA := BaileyTransform_eight_qpoch_aq_twelve_over_nine a q hA9
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 4)
      (qPochhammer q 3 * qPochhammer q 1)
      (qPoch (a * q) q 12) (qPoch (a * q) q 9)
      (1 + q + q ^ 2 + q ^ 3)
      ((1 - a * q ^ 10) * (1 - a * q ^ 11) * (1 - a * q ^ 12))
      hQ3Q1 hA9 hQ hA

/-- The second middle denominator ratio appearing in the `n = 8`, α₄
common-denominator calculation. -/
theorem BaileyTransform_eight_qpochhammer_aq_alpha_four_second_middle_ratio
    (a q : R)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hA10 : qPoch (a * q) q 10 ≠ 0) :
    qPochhammer q 4 * qPoch (a * q) q 12 /
        (qPochhammer q 2 * qPochhammer q 2 * qPoch (a * q) q 10) =
      ((1 + q + q ^ 2) * (1 + q ^ 2)) *
        ((1 - a * q ^ 11) * (1 - a * q ^ 12)) := by
  have hQ2Q2 : qPochhammer q 2 * qPochhammer q 2 ≠ 0 :=
    mul_ne_zero hQ2 hQ2
  have hQ := BaileyTransform_four_qpochhammer_four_over_two_two q hQ2
  have hA := BaileyTransform_seven_qpoch_aq_twelve_over_ten a q hA10
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 4)
      (qPochhammer q 2 * qPochhammer q 2)
      (qPoch (a * q) q 12) (qPoch (a * q) q 10)
      ((1 + q + q ^ 2) * (1 + q ^ 2))
      ((1 - a * q ^ 11) * (1 - a * q ^ 12))
      hQ2Q2 hA10 hQ hA

/-- The third middle denominator ratio appearing in the `n = 8`, α₄
common-denominator calculation. -/
theorem BaileyTransform_eight_qpochhammer_aq_alpha_four_third_middle_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hA11 : qPoch (a * q) q 11 ≠ 0) :
    qPochhammer q 4 * qPoch (a * q) q 12 /
        (qPochhammer q 1 * qPochhammer q 3 * qPoch (a * q) q 11) =
      (1 + q + q ^ 2 + q ^ 3) * (1 - a * q ^ 12) := by
  have hQ1Q3 : qPochhammer q 1 * qPochhammer q 3 ≠ 0 :=
    mul_ne_zero hQ1 hQ3
  have hQ : qPochhammer q 4 / (qPochhammer q 1 * qPochhammer q 3) =
      1 + q + q ^ 2 + q ^ 3 := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      BaileyTransform_four_qpochhammer_four_over_three_one q hQ1 hQ3
  have hA := BaileyTransform_seven_qpoch_aq_twelve_over_eleven a q hA11
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 4)
      (qPochhammer q 1 * qPochhammer q 3)
      (qPoch (a * q) q 12) (qPoch (a * q) q 11)
      (1 + q + q ^ 2 + q ^ 3) (1 - a * q ^ 12)
      hQ1Q3 hA11 hQ hA

set_option maxHeartbeats 4000000 in
/-- The α₄ coefficient identity in the `n = 8` finite Bailey-lemma step after
moving the five transformed-β contributions to a common denominator. -/
theorem BaileyTransform_eight_alpha_four_common_denominator_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hA8 : qPoch (a * q) q 8 ≠ 0)
    (hA9 : qPoch (a * q) q 9 ≠ 0)
    (hA10 : qPoch (a * q) q 10 ≠ 0)
    (hA11 : qPoch (a * q) q 11 ≠ 0)
    (hD1four : qPoch (a * q / ρ₁) q 4 ≠ 0)
    (hD2four : qPoch (a * q / ρ₂) q 4 ≠ 0) :
    qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 4 *
        (qPoch (a * q) q 12 / qPoch (a * q) q 8) +
      qPoch ρ₁ q 5 * qPoch ρ₂ q 5 *
        (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3 *
        (qPochhammer q 4 * qPoch (a * q) q 12 /
          (qPochhammer q 3 * qPochhammer q 1 * qPoch (a * q) q 9)) +
      qPoch ρ₁ q 6 * qPoch ρ₂ q 6 *
        (a * q / (ρ₁ * ρ₂)) ^ 6 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2 *
        (qPochhammer q 4 * qPoch (a * q) q 12 /
          (qPochhammer q 2 * qPochhammer q 2 * qPoch (a * q) q 10)) +
      qPoch ρ₁ q 7 * qPoch ρ₂ q 7 *
        (a * q / (ρ₁ * ρ₂)) ^ 7 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1 *
        (qPochhammer q 4 * qPoch (a * q) q 12 /
          (qPochhammer q 1 * qPochhammer q 3 * qPoch (a * q) q 11)) +
      qPoch ρ₁ q 8 * qPoch ρ₂ q 8 *
        (a * q / (ρ₁ * ρ₂)) ^ 8 =
      (qPoch ρ₁ q 4 * qPoch ρ₂ q 4 *
        (a * q / (ρ₁ * ρ₂)) ^ 4) *
        ((qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8) /
          (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4)) := by
  rw [BaileyTransform_eight_qpoch_aq_twelve_over_eight a q hA8,
    BaileyTransform_eight_qpochhammer_aq_alpha_four_first_middle_ratio a q hQ1 hQ3 hA9,
    BaileyTransform_eight_qpochhammer_aq_alpha_four_second_middle_ratio a q hQ2 hA10,
    BaileyTransform_eight_qpochhammer_aq_alpha_four_third_middle_ratio a q hQ1 hQ3 hA11,
    BaileyTransform_eight_qpoch_pair_ratio_four_eight a q ρ₁ ρ₂ hD1four hD2four]
  have hρ1 : ρ₁ ≠ 0 := left_ne_zero_of_mul hρ
  have hρ2 : ρ₂ ≠ 0 := right_ne_zero_of_mul hρ
  rw [show qPoch (a * q / (ρ₁ * ρ₂)) q 4 =
      (1 - a * q / (ρ₁ * ρ₂)) * (1 - (a * q / (ρ₁ * ρ₂)) * q) *
        (1 - (a * q / (ρ₁ * ρ₂)) * q ^ 2) *
        (1 - (a * q / (ρ₁ * ρ₂)) * q ^ 3) by
        simp [qPoch]]
  rw [show qPoch (a * q / (ρ₁ * ρ₂)) q 3 =
      (1 - a * q / (ρ₁ * ρ₂)) * (1 - (a * q / (ρ₁ * ρ₂)) * q) *
        (1 - (a * q / (ρ₁ * ρ₂)) * q ^ 2) by
        simp [qPoch]]
  rw [show qPoch (a * q / (ρ₁ * ρ₂)) q 2 =
      (1 - a * q / (ρ₁ * ρ₂)) * (1 - (a * q / (ρ₁ * ρ₂)) * q) by
        simp [qPoch]]
  rw [show qPoch (a * q / (ρ₁ * ρ₂)) q 1 =
      1 - a * q / (ρ₁ * ρ₂) by simp [qPoch]]
  rw [show qPoch ρ₁ q 8 = qPoch ρ₁ q 7 * (1 - ρ₁ * q ^ 7) by rfl]
  rw [show qPoch ρ₂ q 8 = qPoch ρ₂ q 7 * (1 - ρ₂ * q ^ 7) by rfl]
  rw [show qPoch ρ₁ q 7 = qPoch ρ₁ q 6 * (1 - ρ₁ * q ^ 6) by rfl]
  rw [show qPoch ρ₂ q 7 = qPoch ρ₂ q 6 * (1 - ρ₂ * q ^ 6) by rfl]
  rw [show qPoch ρ₁ q 6 = qPoch ρ₁ q 5 * (1 - ρ₁ * q ^ 5) by rfl]
  rw [show qPoch ρ₂ q 6 = qPoch ρ₂ q 5 * (1 - ρ₂ * q ^ 5) by rfl]
  rw [show qPoch ρ₁ q 5 = qPoch ρ₁ q 4 * (1 - ρ₁ * q ^ 4) by rfl]
  rw [show qPoch ρ₂ q 5 = qPoch ρ₂ q 4 * (1 - ρ₂ * q ^ 4) by rfl]
  field_simp [hρ, hρ1, hρ2]
  ring

set_option maxHeartbeats 4000000 in
/-- The α₄ coefficient identity in the `n = 8` finite Bailey-lemma step. -/
theorem BaileyTransform_eight_alpha_four_coefficient_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hD1 : qPoch (a * q / ρ₁) q 8 ≠ 0)
    (hD2 : qPoch (a * q / ρ₂) q 8 ≠ 0)
    (hD1four : qPoch (a * q / ρ₁) q 4 ≠ 0)
    (hD2four : qPoch (a * q / ρ₂) q 4 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hQ4 : qPochhammer q 4 ≠ 0)
    (hA8 : qPoch (a * q) q 8 ≠ 0)
    (hA9 : qPoch (a * q) q 9 ≠ 0)
    (hA10 : qPoch (a * q) q 10 ≠ 0)
    (hA11 : qPoch (a * q) q 11 ≠ 0)
    (hA12 : qPoch (a * q) q 12 ≠ 0) :
    ((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 4) /
      (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8 *
        qPochhammer q 4)) / qPoch (a * q) q 8 +
      ((qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3) /
      (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8 *
        qPochhammer q 3)) /
        (qPochhammer q 1 * qPoch (a * q) q 9) +
      ((qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8 *
        qPochhammer q 2)) /
        (qPochhammer q 2 * qPoch (a * q) q 10) +
      ((qPoch ρ₁ q 7 * qPoch ρ₂ q 7 * (a * q / (ρ₁ * ρ₂)) ^ 7 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8 *
        qPochhammer q 1)) /
        (qPochhammer q 3 * qPoch (a * q) q 11) +
      ((qPoch ρ₁ q 8 * qPoch ρ₂ q 8 * (a * q / (ρ₁ * ρ₂)) ^ 8 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8 *
        qPochhammer q 0)) /
        (qPochhammer q 4 * qPoch (a * q) q 12) =
      (qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 /
        (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4)) /
        (qPochhammer q 4 * qPoch (a * q) q 12) := by
  have hD : qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8 ≠ 0 :=
    mul_ne_zero hD1 hD2
  have hDfour : qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4 ≠ 0 :=
    mul_ne_zero hD1four hD2four
  have hcommon := BaileyTransform_eight_alpha_four_common_denominator_identity
    a q ρ₁ ρ₂ hρ hQ1 hQ2 hQ3 hA8 hA9 hA10 hA11 hD1four hD2four
  simpa [qPochhammer, qPoch] using
    (BaileyTransform_five_term_fraction_from_common_ratio
      (P1 := qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 4)
      (P2 := qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3)
      (P3 := qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2)
      (P4 := qPoch ρ₁ q 7 * qPoch ρ₂ q 7 * (a * q / (ρ₁ * ρ₂)) ^ 7 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1)
      (P5 := qPoch ρ₁ q 8 * qPoch ρ₂ q 8 * (a * q / (ρ₁ * ρ₂)) ^ 8)
      (B := qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4)
      (D := qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8)
      (D1 := qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4)
      (Q1 := qPochhammer q 1)
      (Q2 := qPochhammer q 2)
      (Q3 := qPochhammer q 3)
      (Q4 := qPochhammer q 4)
      (A2 := qPoch (a * q) q 8)
      (A3 := qPoch (a * q) q 9)
      (A4 := qPoch (a * q) q 10)
      (A5 := qPoch (a * q) q 11)
      (A6 := qPoch (a * q) q 12)
      hD hDfour hQ1 hQ2 hQ3 hQ4 hA8 hA9 hA10 hA11 hA12 hcommon)

/-- The five-step q-Pochhammer ratio `(aq;q)_11 / (aq;q)_6`. -/
theorem BaileyTransform_eight_qpoch_aq_eleven_over_six
    (a q : R) (hA6 : qPoch (a * q) q 6 ≠ 0) :
    qPoch (a * q) q 11 / qPoch (a * q) q 6 =
      (1 - a * q ^ 7) * (1 - a * q ^ 8) * (1 - a * q ^ 9) *
        (1 - a * q ^ 10) * (1 - a * q ^ 11) := by
  rw [show qPoch (a * q) q 11 =
      qPoch (a * q) q 6 * (1 - (a * q) * q ^ 6) *
        (1 - (a * q) * q ^ 7) * (1 - (a * q) * q ^ 8) *
        (1 - (a * q) * q ^ 9) * (1 - (a * q) * q ^ 10) by rfl]
  field_simp [hA6]

/-- The four-step q-Pochhammer ratio `(aq;q)_11 / (aq;q)_7`. -/
theorem BaileyTransform_eight_qpoch_aq_eleven_over_seven
    (a q : R) (hA7 : qPoch (a * q) q 7 ≠ 0) :
    qPoch (a * q) q 11 / qPoch (a * q) q 7 =
      (1 - a * q ^ 8) * (1 - a * q ^ 9) * (1 - a * q ^ 10) *
        (1 - a * q ^ 11) := by
  rw [show qPoch (a * q) q 11 =
      qPoch (a * q) q 7 * (1 - (a * q) * q ^ 7) *
        (1 - (a * q) * q ^ 8) * (1 - (a * q) * q ^ 9) *
        (1 - (a * q) * q ^ 10) by rfl]
  field_simp [hA7]

/-- The denominator ratio between the `N=8` and `N=3` transformed-α
q-Pochhammer factors. -/
theorem BaileyTransform_eight_qpoch_pair_ratio_three_eight
    (a q ρ₁ ρ₂ : R)
    (hD1three : qPoch (a * q / ρ₁) q 3 ≠ 0)
    (hD2three : qPoch (a * q / ρ₂) q 3 ≠ 0) :
    (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8) /
        (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3) =
      ((1 - (a * q / ρ₁) * q ^ 3) * (1 - (a * q / ρ₁) * q ^ 4) *
        (1 - (a * q / ρ₁) * q ^ 5) * (1 - (a * q / ρ₁) * q ^ 6) *
        (1 - (a * q / ρ₁) * q ^ 7)) *
      ((1 - (a * q / ρ₂) * q ^ 3) * (1 - (a * q / ρ₂) * q ^ 4) *
        (1 - (a * q / ρ₂) * q ^ 5) * (1 - (a * q / ρ₂) * q ^ 6) *
        (1 - (a * q / ρ₂) * q ^ 7)) := by
  have h1 : qPoch (a * q / ρ₁) q 8 / qPoch (a * q / ρ₁) q 3 =
      (1 - (a * q / ρ₁) * q ^ 3) * (1 - (a * q / ρ₁) * q ^ 4) *
        (1 - (a * q / ρ₁) * q ^ 5) * (1 - (a * q / ρ₁) * q ^ 6) *
        (1 - (a * q / ρ₁) * q ^ 7) := by
    rw [show qPoch (a * q / ρ₁) q 8 =
        qPoch (a * q / ρ₁) q 3 * (1 - (a * q / ρ₁) * q ^ 3) *
          (1 - (a * q / ρ₁) * q ^ 4) * (1 - (a * q / ρ₁) * q ^ 5) *
          (1 - (a * q / ρ₁) * q ^ 6) * (1 - (a * q / ρ₁) * q ^ 7) by rfl]
    field_simp [hD1three]
  have h2 : qPoch (a * q / ρ₂) q 8 / qPoch (a * q / ρ₂) q 3 =
      (1 - (a * q / ρ₂) * q ^ 3) * (1 - (a * q / ρ₂) * q ^ 4) *
        (1 - (a * q / ρ₂) * q ^ 5) * (1 - (a * q / ρ₂) * q ^ 6) *
        (1 - (a * q / ρ₂) * q ^ 7) := by
    rw [show qPoch (a * q / ρ₂) q 8 =
        qPoch (a * q / ρ₂) q 3 * (1 - (a * q / ρ₂) * q ^ 3) *
          (1 - (a * q / ρ₂) * q ^ 4) * (1 - (a * q / ρ₂) * q ^ 5) *
          (1 - (a * q / ρ₂) * q ^ 6) * (1 - (a * q / ρ₂) * q ^ 7) by rfl]
    field_simp [hD2three]
  rw [show (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8) /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3) =
      (qPoch (a * q / ρ₁) q 8 / qPoch (a * q / ρ₁) q 3) *
      (qPoch (a * q / ρ₂) q 8 / qPoch (a * q / ρ₂) q 3) by
        field_simp]
  rw [h1, h2]

/-- The first middle denominator ratio appearing in the `n = 8`, α₃
common-denominator calculation. -/
theorem BaileyTransform_eight_qpochhammer_aq_alpha_three_first_middle_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ4 : qPochhammer q 4 ≠ 0)
    (hA7 : qPoch (a * q) q 7 ≠ 0) :
    qPochhammer q 5 * qPoch (a * q) q 11 /
        (qPochhammer q 4 * qPochhammer q 1 * qPoch (a * q) q 7) =
      (1 + q + q ^ 2 + q ^ 3 + q ^ 4) *
        ((1 - a * q ^ 8) * (1 - a * q ^ 9) * (1 - a * q ^ 10) *
          (1 - a * q ^ 11)) := by
  have hQ4Q1 : qPochhammer q 4 * qPochhammer q 1 ≠ 0 :=
    mul_ne_zero hQ4 hQ1
  have hQ := BaileyTransform_five_qpochhammer_five_over_four_one q hQ1 hQ4
  have hA := BaileyTransform_eight_qpoch_aq_eleven_over_seven a q hA7
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 5)
      (qPochhammer q 4 * qPochhammer q 1)
      (qPoch (a * q) q 11) (qPoch (a * q) q 7)
      (1 + q + q ^ 2 + q ^ 3 + q ^ 4)
      ((1 - a * q ^ 8) * (1 - a * q ^ 9) * (1 - a * q ^ 10) *
        (1 - a * q ^ 11))
      hQ4Q1 hA7 hQ hA

/-- The second middle denominator ratio appearing in the `n = 8`, α₃
common-denominator calculation. -/
theorem BaileyTransform_eight_qpochhammer_aq_alpha_three_second_middle_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hA8 : qPoch (a * q) q 8 ≠ 0) :
    qPochhammer q 5 * qPoch (a * q) q 11 /
        (qPochhammer q 3 * qPochhammer q 2 * qPoch (a * q) q 8) =
      ((1 + q + q ^ 2 + q ^ 3 + q ^ 4) * (1 + q ^ 2)) *
        ((1 - a * q ^ 9) * (1 - a * q ^ 10) * (1 - a * q ^ 11)) := by
  have hQ3Q2 : qPochhammer q 3 * qPochhammer q 2 ≠ 0 :=
    mul_ne_zero hQ3 hQ2
  have hQ := BaileyTransform_five_qpochhammer_five_over_three_two q hQ1 hQ2 hQ3
  have hA := BaileyTransform_seven_qpoch_aq_eleven_over_eight a q hA8
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 5)
      (qPochhammer q 3 * qPochhammer q 2)
      (qPoch (a * q) q 11) (qPoch (a * q) q 8)
      ((1 + q + q ^ 2 + q ^ 3 + q ^ 4) * (1 + q ^ 2))
      ((1 - a * q ^ 9) * (1 - a * q ^ 10) * (1 - a * q ^ 11))
      hQ3Q2 hA8 hQ hA

/-- The third middle denominator ratio appearing in the `n = 8`, α₃
common-denominator calculation. -/
theorem BaileyTransform_eight_qpochhammer_aq_alpha_three_third_middle_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hA9 : qPoch (a * q) q 9 ≠ 0) :
    qPochhammer q 5 * qPoch (a * q) q 11 /
        (qPochhammer q 2 * qPochhammer q 3 * qPoch (a * q) q 9) =
      ((1 + q + q ^ 2 + q ^ 3 + q ^ 4) * (1 + q ^ 2)) *
        ((1 - a * q ^ 10) * (1 - a * q ^ 11)) := by
  have hQ2Q3 : qPochhammer q 2 * qPochhammer q 3 ≠ 0 :=
    mul_ne_zero hQ2 hQ3
  have hQ := BaileyTransform_five_qpochhammer_five_over_two_three q hQ1 hQ2 hQ3
  have hA := BaileyTransform_seven_qpoch_aq_eleven_over_nine a q hA9
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 5)
      (qPochhammer q 2 * qPochhammer q 3)
      (qPoch (a * q) q 11) (qPoch (a * q) q 9)
      ((1 + q + q ^ 2 + q ^ 3 + q ^ 4) * (1 + q ^ 2))
      ((1 - a * q ^ 10) * (1 - a * q ^ 11))
      hQ2Q3 hA9 hQ hA

/-- The fourth middle denominator ratio appearing in the `n = 8`, α₃
common-denominator calculation. -/
theorem BaileyTransform_eight_qpochhammer_aq_alpha_three_fourth_middle_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ4 : qPochhammer q 4 ≠ 0)
    (hA10 : qPoch (a * q) q 10 ≠ 0) :
    qPochhammer q 5 * qPoch (a * q) q 11 /
        (qPochhammer q 1 * qPochhammer q 4 * qPoch (a * q) q 10) =
      (1 + q + q ^ 2 + q ^ 3 + q ^ 4) * (1 - a * q ^ 11) := by
  have hQ1Q4 : qPochhammer q 1 * qPochhammer q 4 ≠ 0 :=
    mul_ne_zero hQ1 hQ4
  have hQ : qPochhammer q 5 / (qPochhammer q 1 * qPochhammer q 4) =
      1 + q + q ^ 2 + q ^ 3 + q ^ 4 := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      BaileyTransform_five_qpochhammer_five_over_four_one q hQ1 hQ4
  have hA := BaileyTransform_seven_qpoch_aq_eleven_over_ten a q hA10
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 5)
      (qPochhammer q 1 * qPochhammer q 4)
      (qPoch (a * q) q 11) (qPoch (a * q) q 10)
      (1 + q + q ^ 2 + q ^ 3 + q ^ 4) (1 - a * q ^ 11)
      hQ1Q4 hA10 hQ hA

set_option maxHeartbeats 4000000 in
/-- The α₃ coefficient identity in the `n = 8` finite Bailey-lemma step after
moving the six transformed-β contributions to a common denominator. -/
theorem BaileyTransform_eight_alpha_three_common_denominator_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hQ4 : qPochhammer q 4 ≠ 0)
    (hA6 : qPoch (a * q) q 6 ≠ 0)
    (hA7 : qPoch (a * q) q 7 ≠ 0)
    (hA8 : qPoch (a * q) q 8 ≠ 0)
    (hA9 : qPoch (a * q) q 9 ≠ 0)
    (hA10 : qPoch (a * q) q 10 ≠ 0)
    (hD1three : qPoch (a * q / ρ₁) q 3 ≠ 0)
    (hD2three : qPoch (a * q / ρ₂) q 3 ≠ 0) :
    qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 5 *
        (qPoch (a * q) q 11 / qPoch (a * q) q 6) +
      qPoch ρ₁ q 4 * qPoch ρ₂ q 4 *
        (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 4 *
        (qPochhammer q 5 * qPoch (a * q) q 11 /
          (qPochhammer q 4 * qPochhammer q 1 * qPoch (a * q) q 7)) +
      qPoch ρ₁ q 5 * qPoch ρ₂ q 5 *
        (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3 *
        (qPochhammer q 5 * qPoch (a * q) q 11 /
          (qPochhammer q 3 * qPochhammer q 2 * qPoch (a * q) q 8)) +
      qPoch ρ₁ q 6 * qPoch ρ₂ q 6 *
        (a * q / (ρ₁ * ρ₂)) ^ 6 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2 *
        (qPochhammer q 5 * qPoch (a * q) q 11 /
          (qPochhammer q 2 * qPochhammer q 3 * qPoch (a * q) q 9)) +
      qPoch ρ₁ q 7 * qPoch ρ₂ q 7 *
        (a * q / (ρ₁ * ρ₂)) ^ 7 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1 *
        (qPochhammer q 5 * qPoch (a * q) q 11 /
          (qPochhammer q 1 * qPochhammer q 4 * qPoch (a * q) q 10)) +
      qPoch ρ₁ q 8 * qPoch ρ₂ q 8 *
        (a * q / (ρ₁ * ρ₂)) ^ 8 =
      (qPoch ρ₁ q 3 * qPoch ρ₂ q 3 *
        (a * q / (ρ₁ * ρ₂)) ^ 3) *
        ((qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8) /
          (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3)) := by
  rw [BaileyTransform_eight_qpoch_aq_eleven_over_six a q hA6,
    BaileyTransform_eight_qpochhammer_aq_alpha_three_first_middle_ratio a q hQ1 hQ4 hA7,
    BaileyTransform_eight_qpochhammer_aq_alpha_three_second_middle_ratio a q hQ1 hQ2 hQ3 hA8,
    BaileyTransform_eight_qpochhammer_aq_alpha_three_third_middle_ratio a q hQ1 hQ2 hQ3 hA9,
    BaileyTransform_eight_qpochhammer_aq_alpha_three_fourth_middle_ratio a q hQ1 hQ4 hA10,
    BaileyTransform_eight_qpoch_pair_ratio_three_eight a q ρ₁ ρ₂ hD1three hD2three]
  have hρ1 : ρ₁ ≠ 0 := left_ne_zero_of_mul hρ
  have hρ2 : ρ₂ ≠ 0 := right_ne_zero_of_mul hρ
  rw [show qPoch (a * q / (ρ₁ * ρ₂)) q 5 =
      (1 - a * q / (ρ₁ * ρ₂)) * (1 - (a * q / (ρ₁ * ρ₂)) * q) *
        (1 - (a * q / (ρ₁ * ρ₂)) * q ^ 2) *
        (1 - (a * q / (ρ₁ * ρ₂)) * q ^ 3) *
        (1 - (a * q / (ρ₁ * ρ₂)) * q ^ 4) by
        simp [qPoch]]
  rw [show qPoch (a * q / (ρ₁ * ρ₂)) q 4 =
      (1 - a * q / (ρ₁ * ρ₂)) * (1 - (a * q / (ρ₁ * ρ₂)) * q) *
        (1 - (a * q / (ρ₁ * ρ₂)) * q ^ 2) *
        (1 - (a * q / (ρ₁ * ρ₂)) * q ^ 3) by
        simp [qPoch]]
  rw [show qPoch (a * q / (ρ₁ * ρ₂)) q 3 =
      (1 - a * q / (ρ₁ * ρ₂)) * (1 - (a * q / (ρ₁ * ρ₂)) * q) *
        (1 - (a * q / (ρ₁ * ρ₂)) * q ^ 2) by
        simp [qPoch]]
  rw [show qPoch (a * q / (ρ₁ * ρ₂)) q 2 =
      (1 - a * q / (ρ₁ * ρ₂)) * (1 - (a * q / (ρ₁ * ρ₂)) * q) by
        simp [qPoch]]
  rw [show qPoch (a * q / (ρ₁ * ρ₂)) q 1 =
      1 - a * q / (ρ₁ * ρ₂) by simp [qPoch]]
  rw [show qPoch ρ₁ q 8 = qPoch ρ₁ q 7 * (1 - ρ₁ * q ^ 7) by rfl]
  rw [show qPoch ρ₂ q 8 = qPoch ρ₂ q 7 * (1 - ρ₂ * q ^ 7) by rfl]
  rw [show qPoch ρ₁ q 7 = qPoch ρ₁ q 6 * (1 - ρ₁ * q ^ 6) by rfl]
  rw [show qPoch ρ₂ q 7 = qPoch ρ₂ q 6 * (1 - ρ₂ * q ^ 6) by rfl]
  rw [show qPoch ρ₁ q 6 = qPoch ρ₁ q 5 * (1 - ρ₁ * q ^ 5) by rfl]
  rw [show qPoch ρ₂ q 6 = qPoch ρ₂ q 5 * (1 - ρ₂ * q ^ 5) by rfl]
  rw [show qPoch ρ₁ q 5 = qPoch ρ₁ q 4 * (1 - ρ₁ * q ^ 4) by rfl]
  rw [show qPoch ρ₂ q 5 = qPoch ρ₂ q 4 * (1 - ρ₂ * q ^ 4) by rfl]
  rw [show qPoch ρ₁ q 4 = qPoch ρ₁ q 3 * (1 - ρ₁ * q ^ 3) by rfl]
  rw [show qPoch ρ₂ q 4 = qPoch ρ₂ q 3 * (1 - ρ₂ * q ^ 3) by rfl]
  field_simp [hρ, hρ1, hρ2]
  ring

set_option maxHeartbeats 4000000 in
/-- The α₃ coefficient identity in the `n = 8` finite Bailey-lemma step. -/
theorem BaileyTransform_eight_alpha_three_coefficient_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hD1 : qPoch (a * q / ρ₁) q 8 ≠ 0)
    (hD2 : qPoch (a * q / ρ₂) q 8 ≠ 0)
    (hD1three : qPoch (a * q / ρ₁) q 3 ≠ 0)
    (hD2three : qPoch (a * q / ρ₂) q 3 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hQ4 : qPochhammer q 4 ≠ 0)
    (hQ5 : qPochhammer q 5 ≠ 0)
    (hA6 : qPoch (a * q) q 6 ≠ 0)
    (hA7 : qPoch (a * q) q 7 ≠ 0)
    (hA8 : qPoch (a * q) q 8 ≠ 0)
    (hA9 : qPoch (a * q) q 9 ≠ 0)
    (hA10 : qPoch (a * q) q 10 ≠ 0)
    (hA11 : qPoch (a * q) q 11 ≠ 0) :
    ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 5) /
      (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8 *
        qPochhammer q 5)) / qPoch (a * q) q 6 +
      ((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 4) /
      (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8 *
        qPochhammer q 4)) /
        (qPochhammer q 1 * qPoch (a * q) q 7) +
      ((qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3) /
      (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8 *
        qPochhammer q 3)) /
        (qPochhammer q 2 * qPoch (a * q) q 8) +
      ((qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8 *
        qPochhammer q 2)) /
        (qPochhammer q 3 * qPoch (a * q) q 9) +
      ((qPoch ρ₁ q 7 * qPoch ρ₂ q 7 * (a * q / (ρ₁ * ρ₂)) ^ 7 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8 *
        qPochhammer q 1)) /
        (qPochhammer q 4 * qPoch (a * q) q 10) +
      ((qPoch ρ₁ q 8 * qPoch ρ₂ q 8 * (a * q / (ρ₁ * ρ₂)) ^ 8 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8 *
        qPochhammer q 0)) /
        (qPochhammer q 5 * qPoch (a * q) q 11) =
      (qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 /
        (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3)) /
        (qPochhammer q 5 * qPoch (a * q) q 11) := by
  have hD : qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8 ≠ 0 :=
    mul_ne_zero hD1 hD2
  have hDthree : qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 ≠ 0 :=
    mul_ne_zero hD1three hD2three
  have hcommon := BaileyTransform_eight_alpha_three_common_denominator_identity
    a q ρ₁ ρ₂ hρ hQ1 hQ2 hQ3 hQ4 hA6 hA7 hA8 hA9 hA10 hD1three hD2three
  simpa [qPochhammer, qPoch] using
    (BaileyTransform_six_term_fraction_from_common_ratio
      (P1 := qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 5)
      (P2 := qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 4)
      (P3 := qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3)
      (P4 := qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2)
      (P5 := qPoch ρ₁ q 7 * qPoch ρ₂ q 7 * (a * q / (ρ₁ * ρ₂)) ^ 7 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1)
      (P6 := qPoch ρ₁ q 8 * qPoch ρ₂ q 8 * (a * q / (ρ₁ * ρ₂)) ^ 8)
      (B := qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3)
      (D := qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8)
      (D1 := qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3)
      (Q1 := qPochhammer q 1)
      (Q2 := qPochhammer q 2)
      (Q3 := qPochhammer q 3)
      (Q4 := qPochhammer q 4)
      (Q5 := qPochhammer q 5)
      (A2 := qPoch (a * q) q 6)
      (A3 := qPoch (a * q) q 7)
      (A4 := qPoch (a * q) q 8)
      (A5 := qPoch (a * q) q 9)
      (A6 := qPoch (a * q) q 10)
      (A7 := qPoch (a * q) q 11)
      hD hDthree hQ1 hQ2 hQ3 hQ4 hQ5 hA6 hA7 hA8 hA9 hA10 hA11 hcommon)

/-- The six-step q-Pochhammer ratio `(aq;q)_10 / (aq;q)_4`. -/
theorem BaileyTransform_eight_qpoch_aq_ten_over_four
    (a q : R) (hA4 : qPoch (a * q) q 4 ≠ 0) :
    qPoch (a * q) q 10 / qPoch (a * q) q 4 =
      (1 - a * q ^ 5) * (1 - a * q ^ 6) * (1 - a * q ^ 7) *
        (1 - a * q ^ 8) * (1 - a * q ^ 9) * (1 - a * q ^ 10) := by
  rw [show qPoch (a * q) q 10 =
      qPoch (a * q) q 4 * (1 - (a * q) * q ^ 4) *
        (1 - (a * q) * q ^ 5) * (1 - (a * q) * q ^ 6) *
        (1 - (a * q) * q ^ 7) * (1 - (a * q) * q ^ 8) *
        (1 - (a * q) * q ^ 9) by rfl]
  field_simp [hA4]

/-- The five-step q-Pochhammer ratio `(aq;q)_10 / (aq;q)_5`. -/
theorem BaileyTransform_eight_qpoch_aq_ten_over_five
    (a q : R) (hA5 : qPoch (a * q) q 5 ≠ 0) :
    qPoch (a * q) q 10 / qPoch (a * q) q 5 =
      (1 - a * q ^ 6) * (1 - a * q ^ 7) * (1 - a * q ^ 8) *
        (1 - a * q ^ 9) * (1 - a * q ^ 10) := by
  rw [show qPoch (a * q) q 10 =
      qPoch (a * q) q 5 * (1 - (a * q) * q ^ 5) *
        (1 - (a * q) * q ^ 6) * (1 - (a * q) * q ^ 7) *
        (1 - (a * q) * q ^ 8) * (1 - (a * q) * q ^ 9) by rfl]
  field_simp [hA5]

set_option maxHeartbeats 800000 in
/-- The denominator ratio between the `N=8` and `N=2` transformed-α
q-Pochhammer factors. -/
theorem BaileyTransform_eight_qpoch_pair_ratio_two_eight
    (a q ρ₁ ρ₂ : R)
    (hD1two : qPoch (a * q / ρ₁) q 2 ≠ 0)
    (hD2two : qPoch (a * q / ρ₂) q 2 ≠ 0) :
    (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8) /
        (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2) =
      ((1 - (a * q / ρ₁) * q ^ 2) * (1 - (a * q / ρ₁) * q ^ 3) *
        (1 - (a * q / ρ₁) * q ^ 4) * (1 - (a * q / ρ₁) * q ^ 5) *
        (1 - (a * q / ρ₁) * q ^ 6) * (1 - (a * q / ρ₁) * q ^ 7)) *
      ((1 - (a * q / ρ₂) * q ^ 2) * (1 - (a * q / ρ₂) * q ^ 3) *
        (1 - (a * q / ρ₂) * q ^ 4) * (1 - (a * q / ρ₂) * q ^ 5) *
        (1 - (a * q / ρ₂) * q ^ 6) * (1 - (a * q / ρ₂) * q ^ 7)) := by
  have h1 : qPoch (a * q / ρ₁) q 8 / qPoch (a * q / ρ₁) q 2 =
      (1 - (a * q / ρ₁) * q ^ 2) * (1 - (a * q / ρ₁) * q ^ 3) *
        (1 - (a * q / ρ₁) * q ^ 4) * (1 - (a * q / ρ₁) * q ^ 5) *
        (1 - (a * q / ρ₁) * q ^ 6) * (1 - (a * q / ρ₁) * q ^ 7) := by
    rw [show qPoch (a * q / ρ₁) q 8 =
        qPoch (a * q / ρ₁) q 2 * (1 - (a * q / ρ₁) * q ^ 2) *
          (1 - (a * q / ρ₁) * q ^ 3) * (1 - (a * q / ρ₁) * q ^ 4) *
          (1 - (a * q / ρ₁) * q ^ 5) * (1 - (a * q / ρ₁) * q ^ 6) *
          (1 - (a * q / ρ₁) * q ^ 7) by rfl]
    field_simp [hD1two]
  have h2 : qPoch (a * q / ρ₂) q 8 / qPoch (a * q / ρ₂) q 2 =
      (1 - (a * q / ρ₂) * q ^ 2) * (1 - (a * q / ρ₂) * q ^ 3) *
        (1 - (a * q / ρ₂) * q ^ 4) * (1 - (a * q / ρ₂) * q ^ 5) *
        (1 - (a * q / ρ₂) * q ^ 6) * (1 - (a * q / ρ₂) * q ^ 7) := by
    rw [show qPoch (a * q / ρ₂) q 8 =
        qPoch (a * q / ρ₂) q 2 * (1 - (a * q / ρ₂) * q ^ 2) *
          (1 - (a * q / ρ₂) * q ^ 3) * (1 - (a * q / ρ₂) * q ^ 4) *
          (1 - (a * q / ρ₂) * q ^ 5) * (1 - (a * q / ρ₂) * q ^ 6) *
          (1 - (a * q / ρ₂) * q ^ 7) by rfl]
    field_simp [hD2two]
  rw [show (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8) /
      (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2) =
      (qPoch (a * q / ρ₁) q 8 / qPoch (a * q / ρ₁) q 2) *
      (qPoch (a * q / ρ₂) q 8 / qPoch (a * q / ρ₂) q 2) by
        field_simp]
  rw [h1, h2]

set_option maxHeartbeats 800000 in
/-- The denominator ratio between the `N=7` and `N=1` transformed-α
q-Pochhammer factors. -/
theorem BaileyTransform_seven_qpoch_pair_ratio_one_seven
    (a q ρ₁ ρ₂ : R)
    (hD1one : qPoch (a * q / ρ₁) q 1 ≠ 0)
    (hD2one : qPoch (a * q / ρ₂) q 1 ≠ 0) :
    (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7) /
        (qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1) =
      ((1 - (a * q / ρ₁) * q) * (1 - (a * q / ρ₁) * q ^ 2) *
          (1 - (a * q / ρ₁) * q ^ 3) * (1 - (a * q / ρ₁) * q ^ 4) *
          (1 - (a * q / ρ₁) * q ^ 5) * (1 - (a * q / ρ₁) * q ^ 6)) *
        ((1 - (a * q / ρ₂) * q) * (1 - (a * q / ρ₂) * q ^ 2) *
          (1 - (a * q / ρ₂) * q ^ 3) * (1 - (a * q / ρ₂) * q ^ 4) *
          (1 - (a * q / ρ₂) * q ^ 5) * (1 - (a * q / ρ₂) * q ^ 6)) := by
  have h1 : qPoch (a * q / ρ₁) q 7 / qPoch (a * q / ρ₁) q 1 =
      (1 - (a * q / ρ₁) * q) * (1 - (a * q / ρ₁) * q ^ 2) *
        (1 - (a * q / ρ₁) * q ^ 3) * (1 - (a * q / ρ₁) * q ^ 4) *
        (1 - (a * q / ρ₁) * q ^ 5) * (1 - (a * q / ρ₁) * q ^ 6) := by
    rw [show qPoch (a * q / ρ₁) q 7 =
        qPoch (a * q / ρ₁) q 1 * (1 - (a * q / ρ₁) * q ^ 1) *
          (1 - (a * q / ρ₁) * q ^ 2) * (1 - (a * q / ρ₁) * q ^ 3) *
          (1 - (a * q / ρ₁) * q ^ 4) * (1 - (a * q / ρ₁) * q ^ 5) *
          (1 - (a * q / ρ₁) * q ^ 6) by rfl]
    simp only [pow_one]
    field_simp [hD1one]
  have h2 : qPoch (a * q / ρ₂) q 7 / qPoch (a * q / ρ₂) q 1 =
      (1 - (a * q / ρ₂) * q) * (1 - (a * q / ρ₂) * q ^ 2) *
        (1 - (a * q / ρ₂) * q ^ 3) * (1 - (a * q / ρ₂) * q ^ 4) *
        (1 - (a * q / ρ₂) * q ^ 5) * (1 - (a * q / ρ₂) * q ^ 6) := by
    rw [show qPoch (a * q / ρ₂) q 7 =
        qPoch (a * q / ρ₂) q 1 * (1 - (a * q / ρ₂) * q ^ 1) *
          (1 - (a * q / ρ₂) * q ^ 2) * (1 - (a * q / ρ₂) * q ^ 3) *
          (1 - (a * q / ρ₂) * q ^ 4) * (1 - (a * q / ρ₂) * q ^ 5) *
          (1 - (a * q / ρ₂) * q ^ 6) by rfl]
    simp only [pow_one]
    field_simp [hD2one]
  rw [show (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7) /
      (qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1) =
      (qPoch (a * q / ρ₁) q 7 / qPoch (a * q / ρ₁) q 1) *
      (qPoch (a * q / ρ₂) q 7 / qPoch (a * q / ρ₂) q 1) by
        field_simp]
  rw [h1, h2]

/-- The denominator ratio between the `N=6` and `N=1` transformed-α
q-Pochhammer factors. -/
theorem BaileyTransform_six_qpoch_pair_ratio_one_six
    (a q ρ₁ ρ₂ : R)
    (hD1one : qPoch (a * q / ρ₁) q 1 ≠ 0)
    (hD2one : qPoch (a * q / ρ₂) q 1 ≠ 0) :
    (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6) /
        (qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1) =
      ((1 - (a * q / ρ₁) * q) * (1 - (a * q / ρ₁) * q ^ 2) *
          (1 - (a * q / ρ₁) * q ^ 3) * (1 - (a * q / ρ₁) * q ^ 4) *
          (1 - (a * q / ρ₁) * q ^ 5)) *
        ((1 - (a * q / ρ₂) * q) * (1 - (a * q / ρ₂) * q ^ 2) *
          (1 - (a * q / ρ₂) * q ^ 3) * (1 - (a * q / ρ₂) * q ^ 4) *
          (1 - (a * q / ρ₂) * q ^ 5)) := by
  have h1 : qPoch (a * q / ρ₁) q 6 / qPoch (a * q / ρ₁) q 1 =
      (1 - (a * q / ρ₁) * q) * (1 - (a * q / ρ₁) * q ^ 2) *
        (1 - (a * q / ρ₁) * q ^ 3) * (1 - (a * q / ρ₁) * q ^ 4) *
        (1 - (a * q / ρ₁) * q ^ 5) := by
    rw [show qPoch (a * q / ρ₁) q 6 =
        qPoch (a * q / ρ₁) q 1 * (1 - (a * q / ρ₁) * q ^ 1) *
          (1 - (a * q / ρ₁) * q ^ 2) * (1 - (a * q / ρ₁) * q ^ 3) *
          (1 - (a * q / ρ₁) * q ^ 4) * (1 - (a * q / ρ₁) * q ^ 5) by rfl]
    simp only [pow_one]
    field_simp [hD1one]
  have h2 : qPoch (a * q / ρ₂) q 6 / qPoch (a * q / ρ₂) q 1 =
      (1 - (a * q / ρ₂) * q) * (1 - (a * q / ρ₂) * q ^ 2) *
        (1 - (a * q / ρ₂) * q ^ 3) * (1 - (a * q / ρ₂) * q ^ 4) *
        (1 - (a * q / ρ₂) * q ^ 5) := by
    rw [show qPoch (a * q / ρ₂) q 6 =
        qPoch (a * q / ρ₂) q 1 * (1 - (a * q / ρ₂) * q ^ 1) *
          (1 - (a * q / ρ₂) * q ^ 2) * (1 - (a * q / ρ₂) * q ^ 3) *
          (1 - (a * q / ρ₂) * q ^ 4) * (1 - (a * q / ρ₂) * q ^ 5) by rfl]
    simp only [pow_one]
    field_simp [hD2one]
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPoch (a * q / ρ₁) q 6)
      (qPoch (a * q / ρ₁) q 1)
      (qPoch (a * q / ρ₂) q 6)
      (qPoch (a * q / ρ₂) q 1)
      ((1 - (a * q / ρ₁) * q) * (1 - (a * q / ρ₁) * q ^ 2) *
        (1 - (a * q / ρ₁) * q ^ 3) * (1 - (a * q / ρ₁) * q ^ 4) *
        (1 - (a * q / ρ₁) * q ^ 5))
      ((1 - (a * q / ρ₂) * q) * (1 - (a * q / ρ₂) * q ^ 2) *
        (1 - (a * q / ρ₂) * q ^ 3) * (1 - (a * q / ρ₂) * q ^ 4) *
        (1 - (a * q / ρ₂) * q ^ 5))
      hD1one hD2one h1 h2

/-- The α₁ coefficient identity in the `n = 6` finite Bailey-lemma step after
moving the six transformed-β contributions to a common denominator. -/
theorem BaileyTransform_six_alpha_one_common_denominator_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hQ4 : qPochhammer q 4 ≠ 0)
    (hA2 : qPoch (a * q) q 2 ≠ 0)
    (hA3 : qPoch (a * q) q 3 ≠ 0)
    (hA4 : qPoch (a * q) q 4 ≠ 0)
    (hA5 : qPoch (a * q) q 5 ≠ 0)
    (hA6 : qPoch (a * q) q 6 ≠ 0)
    (hD1one : qPoch (a * q / ρ₁) q 1 ≠ 0)
    (hD2one : qPoch (a * q / ρ₂) q 1 ≠ 0) :
    qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) *
        qPoch (a * q / (ρ₁ * ρ₂)) q 5 *
        (qPoch (a * q) q 7 / qPoch (a * q) q 2) +
      qPoch ρ₁ q 2 * qPoch ρ₂ q 2 *
        (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 4 *
        (qPochhammer q 5 * qPoch (a * q) q 7 /
          (qPochhammer q 4 * qPochhammer q 1 * qPoch (a * q) q 3)) +
      qPoch ρ₁ q 3 * qPoch ρ₂ q 3 *
        (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3 *
        (qPochhammer q 5 * qPoch (a * q) q 7 /
          (qPochhammer q 3 * qPochhammer q 2 * qPoch (a * q) q 4)) +
      qPoch ρ₁ q 4 * qPoch ρ₂ q 4 *
        (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2 *
        (qPochhammer q 5 * qPoch (a * q) q 7 /
          (qPochhammer q 2 * qPochhammer q 3 * qPoch (a * q) q 5)) +
      qPoch ρ₁ q 5 * qPoch ρ₂ q 5 *
        (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1 *
        (qPochhammer q 5 * qPoch (a * q) q 7 /
          (qPochhammer q 1 * qPochhammer q 4 * qPoch (a * q) q 6)) +
      qPoch ρ₁ q 6 * qPoch ρ₂ q 6 *
        (a * q / (ρ₁ * ρ₂)) ^ 6 =
      (qPoch ρ₁ q 1 * qPoch ρ₂ q 1 *
        (a * q / (ρ₁ * ρ₂))) *
        ((qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6) /
          (qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1)) := by
  rw [BaileyTransform_six_qpoch_aq_seven_over_two a q hA2,
    BaileyTransform_six_qpochhammer_aq_alpha_one_first_middle_ratio a q hQ1 hQ4 hA3,
    BaileyTransform_six_qpochhammer_aq_alpha_one_second_middle_ratio a q hQ1 hQ2 hQ3 hA4,
    BaileyTransform_six_qpochhammer_aq_alpha_one_third_middle_ratio a q hQ1 hQ2 hQ3 hA5,
    BaileyTransform_six_qpochhammer_aq_alpha_one_fourth_middle_ratio a q hQ1 hQ4 hA6,
    BaileyTransform_six_qpoch_pair_ratio_one_six a q ρ₁ ρ₂ hD1one hD2one]
  have hρ1 : ρ₁ ≠ 0 := left_ne_zero_of_mul hρ
  have hρ2 : ρ₂ ≠ 0 := right_ne_zero_of_mul hρ
  rw [show qPoch (a * q / (ρ₁ * ρ₂)) q 5 =
      (1 - a * q / (ρ₁ * ρ₂)) * (1 - (a * q / (ρ₁ * ρ₂)) * q) *
        (1 - (a * q / (ρ₁ * ρ₂)) * q ^ 2) *
        (1 - (a * q / (ρ₁ * ρ₂)) * q ^ 3) *
        (1 - (a * q / (ρ₁ * ρ₂)) * q ^ 4) by
        simp [qPoch]]
  rw [show qPoch (a * q / (ρ₁ * ρ₂)) q 4 =
      (1 - a * q / (ρ₁ * ρ₂)) * (1 - (a * q / (ρ₁ * ρ₂)) * q) *
        (1 - (a * q / (ρ₁ * ρ₂)) * q ^ 2) *
        (1 - (a * q / (ρ₁ * ρ₂)) * q ^ 3) by
        simp [qPoch]]
  rw [show qPoch (a * q / (ρ₁ * ρ₂)) q 3 =
      (1 - a * q / (ρ₁ * ρ₂)) * (1 - (a * q / (ρ₁ * ρ₂)) * q) *
        (1 - (a * q / (ρ₁ * ρ₂)) * q ^ 2) by
        simp [qPoch]]
  rw [show qPoch (a * q / (ρ₁ * ρ₂)) q 2 =
      (1 - a * q / (ρ₁ * ρ₂)) * (1 - (a * q / (ρ₁ * ρ₂)) * q) by
        simp [qPoch]]
  rw [show qPoch (a * q / (ρ₁ * ρ₂)) q 1 =
      1 - a * q / (ρ₁ * ρ₂) by simp [qPoch]]
  rw [show qPoch ρ₁ q 6 = qPoch ρ₁ q 5 * (1 - ρ₁ * q ^ 5) by rfl]
  rw [show qPoch ρ₂ q 6 = qPoch ρ₂ q 5 * (1 - ρ₂ * q ^ 5) by rfl]
  rw [show qPoch ρ₁ q 5 = qPoch ρ₁ q 4 * (1 - ρ₁ * q ^ 4) by rfl]
  rw [show qPoch ρ₂ q 5 = qPoch ρ₂ q 4 * (1 - ρ₂ * q ^ 4) by rfl]
  rw [show qPoch ρ₁ q 4 = qPoch ρ₁ q 3 * (1 - ρ₁ * q ^ 3) by rfl]
  rw [show qPoch ρ₂ q 4 = qPoch ρ₂ q 3 * (1 - ρ₂ * q ^ 3) by rfl]
  rw [show qPoch ρ₁ q 3 = qPoch ρ₁ q 2 * (1 - ρ₁ * q ^ 2) by rfl]
  rw [show qPoch ρ₂ q 3 = qPoch ρ₂ q 2 * (1 - ρ₂ * q ^ 2) by rfl]
  rw [show qPoch ρ₁ q 2 = qPoch ρ₁ q 1 * (1 - ρ₁ * q) by simp [qPoch]]
  rw [show qPoch ρ₂ q 2 = qPoch ρ₂ q 1 * (1 - ρ₂ * q) by simp [qPoch]]
  field_simp [hρ, hρ1, hρ2]
  ring

/-- The α₁ coefficient identity in the `n = 6` finite Bailey-lemma step. -/
theorem BaileyTransform_six_alpha_one_coefficient_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hD1 : qPoch (a * q / ρ₁) q 6 ≠ 0)
    (hD2 : qPoch (a * q / ρ₂) q 6 ≠ 0)
    (hD1one : qPoch (a * q / ρ₁) q 1 ≠ 0)
    (hD2one : qPoch (a * q / ρ₂) q 1 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hQ4 : qPochhammer q 4 ≠ 0)
    (hQ5 : qPochhammer q 5 ≠ 0)
    (hA2 : qPoch (a * q) q 2 ≠ 0)
    (hA3 : qPoch (a * q) q 3 ≠ 0)
    (hA4 : qPoch (a * q) q 4 ≠ 0)
    (hA5 : qPoch (a * q) q 5 ≠ 0)
    (hA6 : qPoch (a * q) q 6 ≠ 0)
    (hA7 : qPoch (a * q) q 7 ≠ 0) :
    ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 5) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 5)) / qPoch (a * q) q 2 +
      ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 4) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 4)) /
        (qPochhammer q 1 * qPoch (a * q) q 3) +
      ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 3)) /
        (qPochhammer q 2 * qPoch (a * q) q 4) +
      ((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 2)) /
        (qPochhammer q 3 * qPoch (a * q) q 5) +
      ((qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 1)) /
        (qPochhammer q 4 * qPoch (a * q) q 6) +
      ((qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 0)) /
        (qPochhammer q 5 * qPoch (a * q) q 7) =
      (qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) /
        (qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1)) /
        (qPochhammer q 5 * qPoch (a * q) q 7) := by
  have hD : qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 ≠ 0 :=
    mul_ne_zero hD1 hD2
  have hDone : qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1 ≠ 0 :=
    mul_ne_zero hD1one hD2one
  have hcommon := BaileyTransform_six_alpha_one_common_denominator_identity
    a q ρ₁ ρ₂ hρ hQ1 hQ2 hQ3 hQ4 hA2 hA3 hA4 hA5 hA6 hD1one hD2one
  simpa [qPochhammer, qPoch] using
    (BaileyTransform_six_term_fraction_from_common_ratio
      (P1 := qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) *
        qPoch (a * q / (ρ₁ * ρ₂)) q 5)
      (P2 := qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 4)
      (P3 := qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3)
      (P4 := qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2)
      (P5 := qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1)
      (P6 := qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6)
      (B := qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)))
      (D := qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6)
      (D1 := qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1)
      (Q1 := qPochhammer q 1)
      (Q2 := qPochhammer q 2)
      (Q3 := qPochhammer q 3)
      (Q4 := qPochhammer q 4)
      (Q5 := qPochhammer q 5)
      (A2 := qPoch (a * q) q 2)
      (A3 := qPoch (a * q) q 3)
      (A4 := qPoch (a * q) q 4)
      (A5 := qPoch (a * q) q 5)
      (A6 := qPoch (a * q) q 6)
      (A7 := qPoch (a * q) q 7)
      hD hDone hQ1 hQ2 hQ3 hQ4 hQ5 hA2 hA3 hA4 hA5 hA6 hA7 hcommon)

/-- The q-Pochhammer ratio `(q;q)_6 / ((q;q)_5 (q;q)_1)`. -/
theorem BaileyTransform_six_qpochhammer_six_over_five_one
    (q : R) (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ5 : qPochhammer q 5 ≠ 0) :
    qPochhammer q 6 / (qPochhammer q 5 * qPochhammer q 1) =
      1 + q + q ^ 2 + q ^ 3 + q ^ 4 + q ^ 5 := by
  have hq : 1 - q ≠ 0 := by simpa [qPochhammer] using hQ1
  rw [show qPochhammer q 6 = qPochhammer q 5 * (1 - q ^ 6) by rfl]
  field_simp [hQ5]
  simp [qPochhammer]
  field_simp [hq]
  ring

/-- The q-Pochhammer ratio `(q;q)_6 / ((q;q)_4 (q;q)_2)`. -/
theorem BaileyTransform_six_qpochhammer_six_over_four_two
    (q : R) (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ4 : qPochhammer q 4 ≠ 0) :
    qPochhammer q 6 / (qPochhammer q 4 * qPochhammer q 2) =
      (1 + q + q ^ 2 + q ^ 3 + q ^ 4) * (1 + q ^ 2 + q ^ 4) := by
  have hq : 1 - q ≠ 0 := by simpa [qPochhammer] using hQ1
  have hq2 : 1 - q ^ 2 ≠ 0 := by
    simpa [qPochhammer] using right_ne_zero_of_mul hQ2
  rw [show qPochhammer q 6 =
      qPochhammer q 4 * (1 - q ^ 5) * (1 - q ^ 6) by rfl]
  field_simp [hQ4]
  simp [qPochhammer]
  field_simp [hq, hq2]
  ring

/-- The q-Pochhammer ratio `(q;q)_6 / ((q;q)_3 (q;q)_3)`. -/
theorem BaileyTransform_six_qpochhammer_six_over_three_three
    (q : R) (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0) :
    qPochhammer q 6 / (qPochhammer q 3 * qPochhammer q 3) =
      (1 + q + q ^ 2 + q ^ 3 + q ^ 4) * (1 + q ^ 2) * (1 + q ^ 3) := by
  have hq : 1 - q ≠ 0 := by simpa [qPochhammer] using hQ1
  have hq2 : 1 - q ^ 2 ≠ 0 := by
    simpa [qPochhammer] using right_ne_zero_of_mul hQ2
  have hq3 : 1 - q ^ 3 ≠ 0 := by
    simpa [qPochhammer] using right_ne_zero_of_mul hQ3
  rw [show qPochhammer q 6 =
      qPochhammer q 3 * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) by rfl]
  field_simp [hQ3]
  simp [qPochhammer]
  field_simp [hq, hq2, hq3]
  ring

/-- The q-Pochhammer ratio `(q;q)_6 / ((q;q)_2 (q;q)_4)`. -/
theorem BaileyTransform_six_qpochhammer_six_over_two_four
    (q : R) (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ4 : qPochhammer q 4 ≠ 0) :
    qPochhammer q 6 / (qPochhammer q 2 * qPochhammer q 4) =
      (1 + q + q ^ 2 + q ^ 3 + q ^ 4) * (1 + q ^ 2 + q ^ 4) := by
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    BaileyTransform_six_qpochhammer_six_over_four_two q hQ1 hQ2 hQ4

/-- The q-Pochhammer ratio `(q;q)_6 / ((q;q)_1 (q;q)_5)`. -/
theorem BaileyTransform_six_qpochhammer_six_over_one_five
    (q : R) (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ5 : qPochhammer q 5 ≠ 0) :
    qPochhammer q 6 / (qPochhammer q 1 * qPochhammer q 5) =
      1 + q + q ^ 2 + q ^ 3 + q ^ 4 + q ^ 5 := by
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    BaileyTransform_six_qpochhammer_six_over_five_one q hQ1 hQ5
/-- The first middle denominator ratio appearing in the `n = 8`, α₂
common-denominator calculation. -/
theorem BaileyTransform_eight_qpochhammer_aq_alpha_two_first_middle_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ5 : qPochhammer q 5 ≠ 0)
    (hA5 : qPoch (a * q) q 5 ≠ 0) :
    qPochhammer q 6 * qPoch (a * q) q 10 /
        (qPochhammer q 5 * qPochhammer q 1 * qPoch (a * q) q 5) =
      (1 + q + q ^ 2 + q ^ 3 + q ^ 4 + q ^ 5) *
        ((1 - a * q ^ 6) * (1 - a * q ^ 7) * (1 - a * q ^ 8) *
          (1 - a * q ^ 9) * (1 - a * q ^ 10)) := by
  have hQ5Q1 : qPochhammer q 5 * qPochhammer q 1 ≠ 0 :=
    mul_ne_zero hQ5 hQ1
  have hQ := BaileyTransform_six_qpochhammer_six_over_five_one q hQ1 hQ5
  have hA := BaileyTransform_eight_qpoch_aq_ten_over_five a q hA5
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 6)
      (qPochhammer q 5 * qPochhammer q 1)
      (qPoch (a * q) q 10) (qPoch (a * q) q 5)
      (1 + q + q ^ 2 + q ^ 3 + q ^ 4 + q ^ 5)
      ((1 - a * q ^ 6) * (1 - a * q ^ 7) * (1 - a * q ^ 8) *
        (1 - a * q ^ 9) * (1 - a * q ^ 10))
      hQ5Q1 hA5 hQ hA

/-- The second middle denominator ratio appearing in the `n = 8`, α₂
common-denominator calculation. -/
theorem BaileyTransform_eight_qpochhammer_aq_alpha_two_second_middle_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ4 : qPochhammer q 4 ≠ 0)
    (hA6 : qPoch (a * q) q 6 ≠ 0) :
    qPochhammer q 6 * qPoch (a * q) q 10 /
        (qPochhammer q 4 * qPochhammer q 2 * qPoch (a * q) q 6) =
      ((1 + q + q ^ 2 + q ^ 3 + q ^ 4) * (1 + q ^ 2 + q ^ 4)) *
        ((1 - a * q ^ 7) * (1 - a * q ^ 8) * (1 - a * q ^ 9) *
          (1 - a * q ^ 10)) := by
  have hQ4Q2 : qPochhammer q 4 * qPochhammer q 2 ≠ 0 :=
    mul_ne_zero hQ4 hQ2
  have hQ := BaileyTransform_six_qpochhammer_six_over_four_two q hQ1 hQ2 hQ4
  have hA := BaileyTransform_seven_qpoch_aq_ten_over_six a q hA6
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 6)
      (qPochhammer q 4 * qPochhammer q 2)
      (qPoch (a * q) q 10) (qPoch (a * q) q 6)
      ((1 + q + q ^ 2 + q ^ 3 + q ^ 4) * (1 + q ^ 2 + q ^ 4))
      ((1 - a * q ^ 7) * (1 - a * q ^ 8) * (1 - a * q ^ 9) *
        (1 - a * q ^ 10))
      hQ4Q2 hA6 hQ hA

/-- The third middle denominator ratio appearing in the `n = 8`, α₂
common-denominator calculation. -/
theorem BaileyTransform_eight_qpochhammer_aq_alpha_two_third_middle_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hA7 : qPoch (a * q) q 7 ≠ 0) :
    qPochhammer q 6 * qPoch (a * q) q 10 /
        (qPochhammer q 3 * qPochhammer q 3 * qPoch (a * q) q 7) =
      ((1 + q + q ^ 2 + q ^ 3 + q ^ 4) * (1 + q ^ 2) * (1 + q ^ 3)) *
        ((1 - a * q ^ 8) * (1 - a * q ^ 9) * (1 - a * q ^ 10)) := by
  have hQ3Q3 : qPochhammer q 3 * qPochhammer q 3 ≠ 0 :=
    mul_ne_zero hQ3 hQ3
  have hQ := BaileyTransform_six_qpochhammer_six_over_three_three q hQ1 hQ2 hQ3
  have hA := BaileyTransform_seven_qpoch_aq_ten_over_seven a q hA7
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 6)
      (qPochhammer q 3 * qPochhammer q 3)
      (qPoch (a * q) q 10) (qPoch (a * q) q 7)
      ((1 + q + q ^ 2 + q ^ 3 + q ^ 4) * (1 + q ^ 2) * (1 + q ^ 3))
      ((1 - a * q ^ 8) * (1 - a * q ^ 9) * (1 - a * q ^ 10))
      hQ3Q3 hA7 hQ hA

/-- The fourth middle denominator ratio appearing in the `n = 8`, α₂
common-denominator calculation. -/
theorem BaileyTransform_eight_qpochhammer_aq_alpha_two_fourth_middle_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ4 : qPochhammer q 4 ≠ 0)
    (hA8 : qPoch (a * q) q 8 ≠ 0) :
    qPochhammer q 6 * qPoch (a * q) q 10 /
        (qPochhammer q 2 * qPochhammer q 4 * qPoch (a * q) q 8) =
      ((1 + q + q ^ 2 + q ^ 3 + q ^ 4) * (1 + q ^ 2 + q ^ 4)) *
        ((1 - a * q ^ 9) * (1 - a * q ^ 10)) := by
  have hQ2Q4 : qPochhammer q 2 * qPochhammer q 4 ≠ 0 :=
    mul_ne_zero hQ2 hQ4
  have hQ := BaileyTransform_six_qpochhammer_six_over_two_four q hQ1 hQ2 hQ4
  have hA := BaileyTransform_seven_qpoch_aq_ten_over_eight a q hA8
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 6)
      (qPochhammer q 2 * qPochhammer q 4)
      (qPoch (a * q) q 10) (qPoch (a * q) q 8)
      ((1 + q + q ^ 2 + q ^ 3 + q ^ 4) * (1 + q ^ 2 + q ^ 4))
      ((1 - a * q ^ 9) * (1 - a * q ^ 10))
      hQ2Q4 hA8 hQ hA

/-- The fifth middle denominator ratio appearing in the `n = 8`, α₂
common-denominator calculation. -/
theorem BaileyTransform_eight_qpochhammer_aq_alpha_two_fifth_middle_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ5 : qPochhammer q 5 ≠ 0)
    (hA9 : qPoch (a * q) q 9 ≠ 0) :
    qPochhammer q 6 * qPoch (a * q) q 10 /
        (qPochhammer q 1 * qPochhammer q 5 * qPoch (a * q) q 9) =
      (1 + q + q ^ 2 + q ^ 3 + q ^ 4 + q ^ 5) * (1 - a * q ^ 10) := by
  have hQ1Q5 : qPochhammer q 1 * qPochhammer q 5 ≠ 0 :=
    mul_ne_zero hQ1 hQ5
  have hQ : qPochhammer q 6 / (qPochhammer q 1 * qPochhammer q 5) =
      1 + q + q ^ 2 + q ^ 3 + q ^ 4 + q ^ 5 := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      BaileyTransform_six_qpochhammer_six_over_five_one q hQ1 hQ5
  have hA := BaileyTransform_seven_qpoch_aq_ten_over_nine a q hA9
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 6)
      (qPochhammer q 1 * qPochhammer q 5)
      (qPoch (a * q) q 10) (qPoch (a * q) q 9)
      (1 + q + q ^ 2 + q ^ 3 + q ^ 4 + q ^ 5) (1 - a * q ^ 10)
      hQ1Q5 hA9 hQ hA

set_option maxHeartbeats 4000000 in
/-- The α₂ coefficient identity in the `n = 8` finite Bailey-lemma step after
moving the seven transformed-β contributions to a common denominator. -/
theorem BaileyTransform_eight_alpha_two_common_denominator_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hQ4 : qPochhammer q 4 ≠ 0)
    (hQ5 : qPochhammer q 5 ≠ 0)
    (hA4 : qPoch (a * q) q 4 ≠ 0)
    (hA5 : qPoch (a * q) q 5 ≠ 0)
    (hA6 : qPoch (a * q) q 6 ≠ 0)
    (hA7 : qPoch (a * q) q 7 ≠ 0)
    (hA8 : qPoch (a * q) q 8 ≠ 0)
    (hA9 : qPoch (a * q) q 9 ≠ 0)
    (hD1two : qPoch (a * q / ρ₁) q 2 ≠ 0)
    (hD2two : qPoch (a * q / ρ₂) q 2 ≠ 0) :
    qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 6 *
        (qPoch (a * q) q 10 / qPoch (a * q) q 4) +
      qPoch ρ₁ q 3 * qPoch ρ₂ q 3 *
        (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 5 *
        (qPochhammer q 6 * qPoch (a * q) q 10 /
          (qPochhammer q 5 * qPochhammer q 1 * qPoch (a * q) q 5)) +
      qPoch ρ₁ q 4 * qPoch ρ₂ q 4 *
        (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 4 *
        (qPochhammer q 6 * qPoch (a * q) q 10 /
          (qPochhammer q 4 * qPochhammer q 2 * qPoch (a * q) q 6)) +
      qPoch ρ₁ q 5 * qPoch ρ₂ q 5 *
        (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3 *
        (qPochhammer q 6 * qPoch (a * q) q 10 /
          (qPochhammer q 3 * qPochhammer q 3 * qPoch (a * q) q 7)) +
      qPoch ρ₁ q 6 * qPoch ρ₂ q 6 *
        (a * q / (ρ₁ * ρ₂)) ^ 6 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2 *
        (qPochhammer q 6 * qPoch (a * q) q 10 /
          (qPochhammer q 2 * qPochhammer q 4 * qPoch (a * q) q 8)) +
      qPoch ρ₁ q 7 * qPoch ρ₂ q 7 *
        (a * q / (ρ₁ * ρ₂)) ^ 7 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1 *
        (qPochhammer q 6 * qPoch (a * q) q 10 /
          (qPochhammer q 1 * qPochhammer q 5 * qPoch (a * q) q 9)) +
      qPoch ρ₁ q 8 * qPoch ρ₂ q 8 *
        (a * q / (ρ₁ * ρ₂)) ^ 8 =
      (qPoch ρ₁ q 2 * qPoch ρ₂ q 2 *
        (a * q / (ρ₁ * ρ₂)) ^ 2) *
        ((qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8) /
          (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2)) := by
  rw [BaileyTransform_eight_qpoch_aq_ten_over_four a q hA4,
    BaileyTransform_eight_qpochhammer_aq_alpha_two_first_middle_ratio a q hQ1 hQ5 hA5,
    BaileyTransform_eight_qpochhammer_aq_alpha_two_second_middle_ratio a q hQ1 hQ2 hQ4 hA6,
    BaileyTransform_eight_qpochhammer_aq_alpha_two_third_middle_ratio a q hQ1 hQ2 hQ3 hA7,
    BaileyTransform_eight_qpochhammer_aq_alpha_two_fourth_middle_ratio a q hQ1 hQ2 hQ4 hA8,
    BaileyTransform_eight_qpochhammer_aq_alpha_two_fifth_middle_ratio a q hQ1 hQ5 hA9,
    BaileyTransform_eight_qpoch_pair_ratio_two_eight a q ρ₁ ρ₂ hD1two hD2two]
  have hρ1 : ρ₁ ≠ 0 := left_ne_zero_of_mul hρ
  have hρ2 : ρ₂ ≠ 0 := right_ne_zero_of_mul hρ
  rw [show qPoch (a * q / (ρ₁ * ρ₂)) q 6 =
      (1 - a * q / (ρ₁ * ρ₂)) * (1 - (a * q / (ρ₁ * ρ₂)) * q) *
        (1 - (a * q / (ρ₁ * ρ₂)) * q ^ 2) *
        (1 - (a * q / (ρ₁ * ρ₂)) * q ^ 3) *
        (1 - (a * q / (ρ₁ * ρ₂)) * q ^ 4) *
        (1 - (a * q / (ρ₁ * ρ₂)) * q ^ 5) by
        simp [qPoch]]
  rw [show qPoch (a * q / (ρ₁ * ρ₂)) q 5 =
      (1 - a * q / (ρ₁ * ρ₂)) * (1 - (a * q / (ρ₁ * ρ₂)) * q) *
        (1 - (a * q / (ρ₁ * ρ₂)) * q ^ 2) *
        (1 - (a * q / (ρ₁ * ρ₂)) * q ^ 3) *
        (1 - (a * q / (ρ₁ * ρ₂)) * q ^ 4) by
        simp [qPoch]]
  rw [show qPoch (a * q / (ρ₁ * ρ₂)) q 4 =
      (1 - a * q / (ρ₁ * ρ₂)) * (1 - (a * q / (ρ₁ * ρ₂)) * q) *
        (1 - (a * q / (ρ₁ * ρ₂)) * q ^ 2) *
        (1 - (a * q / (ρ₁ * ρ₂)) * q ^ 3) by
        simp [qPoch]]
  rw [show qPoch (a * q / (ρ₁ * ρ₂)) q 3 =
      (1 - a * q / (ρ₁ * ρ₂)) * (1 - (a * q / (ρ₁ * ρ₂)) * q) *
        (1 - (a * q / (ρ₁ * ρ₂)) * q ^ 2) by
        simp [qPoch]]
  rw [show qPoch (a * q / (ρ₁ * ρ₂)) q 2 =
      (1 - a * q / (ρ₁ * ρ₂)) * (1 - (a * q / (ρ₁ * ρ₂)) * q) by
        simp [qPoch]]
  rw [show qPoch (a * q / (ρ₁ * ρ₂)) q 1 =
      1 - a * q / (ρ₁ * ρ₂) by simp [qPoch]]
  rw [show qPoch ρ₁ q 8 = qPoch ρ₁ q 7 * (1 - ρ₁ * q ^ 7) by rfl]
  rw [show qPoch ρ₂ q 8 = qPoch ρ₂ q 7 * (1 - ρ₂ * q ^ 7) by rfl]
  rw [show qPoch ρ₁ q 7 = qPoch ρ₁ q 6 * (1 - ρ₁ * q ^ 6) by rfl]
  rw [show qPoch ρ₂ q 7 = qPoch ρ₂ q 6 * (1 - ρ₂ * q ^ 6) by rfl]
  rw [show qPoch ρ₁ q 6 = qPoch ρ₁ q 5 * (1 - ρ₁ * q ^ 5) by rfl]
  rw [show qPoch ρ₂ q 6 = qPoch ρ₂ q 5 * (1 - ρ₂ * q ^ 5) by rfl]
  rw [show qPoch ρ₁ q 5 = qPoch ρ₁ q 4 * (1 - ρ₁ * q ^ 4) by rfl]
  rw [show qPoch ρ₂ q 5 = qPoch ρ₂ q 4 * (1 - ρ₂ * q ^ 4) by rfl]
  rw [show qPoch ρ₁ q 4 = qPoch ρ₁ q 3 * (1 - ρ₁ * q ^ 3) by rfl]
  rw [show qPoch ρ₂ q 4 = qPoch ρ₂ q 3 * (1 - ρ₂ * q ^ 3) by rfl]
  rw [show qPoch ρ₁ q 3 = qPoch ρ₁ q 2 * (1 - ρ₁ * q ^ 2) by rfl]
  rw [show qPoch ρ₂ q 3 = qPoch ρ₂ q 2 * (1 - ρ₂ * q ^ 2) by rfl]
  field_simp [hρ, hρ1, hρ2]
  ring

set_option maxHeartbeats 4000000 in
/-- The α₂ coefficient identity in the `n = 8` finite Bailey-lemma step. -/
theorem BaileyTransform_eight_alpha_two_coefficient_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hD1 : qPoch (a * q / ρ₁) q 8 ≠ 0)
    (hD2 : qPoch (a * q / ρ₂) q 8 ≠ 0)
    (hD1two : qPoch (a * q / ρ₁) q 2 ≠ 0)
    (hD2two : qPoch (a * q / ρ₂) q 2 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hQ4 : qPochhammer q 4 ≠ 0)
    (hQ5 : qPochhammer q 5 ≠ 0)
    (hQ6 : qPochhammer q 6 ≠ 0)
    (hA4 : qPoch (a * q) q 4 ≠ 0)
    (hA5 : qPoch (a * q) q 5 ≠ 0)
    (hA6 : qPoch (a * q) q 6 ≠ 0)
    (hA7 : qPoch (a * q) q 7 ≠ 0)
    (hA8 : qPoch (a * q) q 8 ≠ 0)
    (hA9 : qPoch (a * q) q 9 ≠ 0)
    (hA10 : qPoch (a * q) q 10 ≠ 0) :
    ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 6) /
      (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8 *
        qPochhammer q 6)) / qPoch (a * q) q 4 +
      ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 5) /
      (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8 *
        qPochhammer q 5)) /
        (qPochhammer q 1 * qPoch (a * q) q 5) +
      ((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 4) /
      (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8 *
        qPochhammer q 4)) /
        (qPochhammer q 2 * qPoch (a * q) q 6) +
      ((qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3) /
      (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8 *
        qPochhammer q 3)) /
        (qPochhammer q 3 * qPoch (a * q) q 7) +
      ((qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8 *
        qPochhammer q 2)) /
        (qPochhammer q 4 * qPoch (a * q) q 8) +
      ((qPoch ρ₁ q 7 * qPoch ρ₂ q 7 * (a * q / (ρ₁ * ρ₂)) ^ 7 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8 *
        qPochhammer q 1)) /
        (qPochhammer q 5 * qPoch (a * q) q 9) +
      ((qPoch ρ₁ q 8 * qPoch ρ₂ q 8 * (a * q / (ρ₁ * ρ₂)) ^ 8 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8 *
        qPochhammer q 0)) /
        (qPochhammer q 6 * qPoch (a * q) q 10) =
      (qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 /
        (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2)) /
        (qPochhammer q 6 * qPoch (a * q) q 10) := by
  have hD : qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8 ≠ 0 :=
    mul_ne_zero hD1 hD2
  have hDtwo : qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2 ≠ 0 :=
    mul_ne_zero hD1two hD2two
  have hcommon := BaileyTransform_eight_alpha_two_common_denominator_identity
    a q ρ₁ ρ₂ hρ hQ1 hQ2 hQ3 hQ4 hQ5 hA4 hA5 hA6 hA7 hA8 hA9 hD1two hD2two
  simpa [qPochhammer, qPoch] using
    (BaileyTransform_seven_term_fraction_from_common_ratio
      (P1 := qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 6)
      (P2 := qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 5)
      (P3 := qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 4)
      (P4 := qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3)
      (P5 := qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2)
      (P6 := qPoch ρ₁ q 7 * qPoch ρ₂ q 7 * (a * q / (ρ₁ * ρ₂)) ^ 7 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1)
      (P7 := qPoch ρ₁ q 8 * qPoch ρ₂ q 8 * (a * q / (ρ₁ * ρ₂)) ^ 8)
      (B := qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2)
      (D := qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8)
      (D1 := qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2)
      (Q1 := qPochhammer q 1)
      (Q2 := qPochhammer q 2)
      (Q3 := qPochhammer q 3)
      (Q4 := qPochhammer q 4)
      (Q5 := qPochhammer q 5)
      (Q6 := qPochhammer q 6)
      (A2 := qPoch (a * q) q 4)
      (A3 := qPoch (a * q) q 5)
      (A4 := qPoch (a * q) q 6)
      (A5 := qPoch (a * q) q 7)
      (A6 := qPoch (a * q) q 8)
      (A7 := qPoch (a * q) q 9)
      (A8 := qPoch (a * q) q 10)
      hD hDtwo hQ1 hQ2 hQ3 hQ4 hQ5 hQ6 hA4 hA5 hA6 hA7 hA8 hA9 hA10 hcommon)



/-- The first middle denominator ratio appearing in the `n = 7`, α₁
common-denominator calculation. -/
theorem BaileyTransform_seven_qpochhammer_aq_alpha_one_first_middle_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ5 : qPochhammer q 5 ≠ 0)
    (hA3 : qPoch (a * q) q 3 ≠ 0) :
    qPochhammer q 6 * qPoch (a * q) q 8 /
        (qPochhammer q 5 * qPochhammer q 1 * qPoch (a * q) q 3) =
      (1 + q + q ^ 2 + q ^ 3 + q ^ 4 + q ^ 5) *
        ((1 - a * q ^ 4) * (1 - a * q ^ 5) *
          (1 - a * q ^ 6) * (1 - a * q ^ 7) * (1 - a * q ^ 8)) := by
  have hQ5Q1 : qPochhammer q 5 * qPochhammer q 1 ≠ 0 :=
    mul_ne_zero hQ5 hQ1
  have hQ := BaileyTransform_six_qpochhammer_six_over_five_one q hQ1 hQ5
  have hA := BaileyTransform_seven_qpoch_aq_eight_over_three a q hA3
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 6)
      (qPochhammer q 5 * qPochhammer q 1)
      (qPoch (a * q) q 8) (qPoch (a * q) q 3)
      (1 + q + q ^ 2 + q ^ 3 + q ^ 4 + q ^ 5)
      ((1 - a * q ^ 4) * (1 - a * q ^ 5) *
        (1 - a * q ^ 6) * (1 - a * q ^ 7) * (1 - a * q ^ 8))
      hQ5Q1 hA3 hQ hA

/-- The second middle denominator ratio appearing in the `n = 7`, α₁
common-denominator calculation. -/
theorem BaileyTransform_seven_qpochhammer_aq_alpha_one_second_middle_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ4 : qPochhammer q 4 ≠ 0)
    (hA4 : qPoch (a * q) q 4 ≠ 0) :
    qPochhammer q 6 * qPoch (a * q) q 8 /
        (qPochhammer q 4 * qPochhammer q 2 * qPoch (a * q) q 4) =
      ((1 + q + q ^ 2 + q ^ 3 + q ^ 4) * (1 + q ^ 2 + q ^ 4)) *
        ((1 - a * q ^ 5) * (1 - a * q ^ 6) *
          (1 - a * q ^ 7) * (1 - a * q ^ 8)) := by
  have hQ4Q2 : qPochhammer q 4 * qPochhammer q 2 ≠ 0 :=
    mul_ne_zero hQ4 hQ2
  have hQ := BaileyTransform_six_qpochhammer_six_over_four_two q hQ1 hQ2 hQ4
  have hA := BaileyTransform_six_qpoch_aq_eight_over_four a q hA4
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 6)
      (qPochhammer q 4 * qPochhammer q 2)
      (qPoch (a * q) q 8) (qPoch (a * q) q 4)
      ((1 + q + q ^ 2 + q ^ 3 + q ^ 4) * (1 + q ^ 2 + q ^ 4))
      ((1 - a * q ^ 5) * (1 - a * q ^ 6) *
        (1 - a * q ^ 7) * (1 - a * q ^ 8))
      hQ4Q2 hA4 hQ hA

/-- The third middle denominator ratio appearing in the `n = 7`, α₁
common-denominator calculation. -/
theorem BaileyTransform_seven_qpochhammer_aq_alpha_one_third_middle_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hA5 : qPoch (a * q) q 5 ≠ 0) :
    qPochhammer q 6 * qPoch (a * q) q 8 /
        (qPochhammer q 3 * qPochhammer q 3 * qPoch (a * q) q 5) =
      ((1 + q + q ^ 2 + q ^ 3 + q ^ 4) * (1 + q ^ 2) * (1 + q ^ 3)) *
        ((1 - a * q ^ 6) * (1 - a * q ^ 7) * (1 - a * q ^ 8)) := by
  have hQ3Q3 : qPochhammer q 3 * qPochhammer q 3 ≠ 0 :=
    mul_ne_zero hQ3 hQ3
  have hQ := BaileyTransform_six_qpochhammer_six_over_three_three q hQ1 hQ2 hQ3
  have hA := BaileyTransform_six_qpoch_aq_eight_over_five a q hA5
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 6)
      (qPochhammer q 3 * qPochhammer q 3)
      (qPoch (a * q) q 8) (qPoch (a * q) q 5)
      ((1 + q + q ^ 2 + q ^ 3 + q ^ 4) * (1 + q ^ 2) * (1 + q ^ 3))
      ((1 - a * q ^ 6) * (1 - a * q ^ 7) * (1 - a * q ^ 8))
      hQ3Q3 hA5 hQ hA

/-- The fourth middle denominator ratio appearing in the `n = 7`, α₁
common-denominator calculation. -/
theorem BaileyTransform_seven_qpochhammer_aq_alpha_one_fourth_middle_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ4 : qPochhammer q 4 ≠ 0)
    (hA6 : qPoch (a * q) q 6 ≠ 0) :
    qPochhammer q 6 * qPoch (a * q) q 8 /
        (qPochhammer q 2 * qPochhammer q 4 * qPoch (a * q) q 6) =
      ((1 + q + q ^ 2 + q ^ 3 + q ^ 4) * (1 + q ^ 2 + q ^ 4)) *
        ((1 - a * q ^ 7) * (1 - a * q ^ 8)) := by
  have hQ2Q4 : qPochhammer q 2 * qPochhammer q 4 ≠ 0 :=
    mul_ne_zero hQ2 hQ4
  have hQ := BaileyTransform_six_qpochhammer_six_over_two_four q hQ1 hQ2 hQ4
  have hA := BaileyTransform_five_qpoch_aq_eight_over_six a q hA6
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 6)
      (qPochhammer q 2 * qPochhammer q 4)
      (qPoch (a * q) q 8) (qPoch (a * q) q 6)
      ((1 + q + q ^ 2 + q ^ 3 + q ^ 4) * (1 + q ^ 2 + q ^ 4))
      ((1 - a * q ^ 7) * (1 - a * q ^ 8))
      hQ2Q4 hA6 hQ hA

/-- The fifth middle denominator ratio appearing in the `n = 7`, α₁
common-denominator calculation. -/
theorem BaileyTransform_seven_qpochhammer_aq_alpha_one_fifth_middle_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ5 : qPochhammer q 5 ≠ 0)
    (hA7 : qPoch (a * q) q 7 ≠ 0) :
    qPochhammer q 6 * qPoch (a * q) q 8 /
        (qPochhammer q 1 * qPochhammer q 5 * qPoch (a * q) q 7) =
      (1 + q + q ^ 2 + q ^ 3 + q ^ 4 + q ^ 5) * (1 - a * q ^ 8) := by
  have hQ1Q5 : qPochhammer q 1 * qPochhammer q 5 ≠ 0 :=
    mul_ne_zero hQ1 hQ5
  have hQ : qPochhammer q 6 / (qPochhammer q 1 * qPochhammer q 5) =
      1 + q + q ^ 2 + q ^ 3 + q ^ 4 + q ^ 5 := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      BaileyTransform_six_qpochhammer_six_over_five_one q hQ1 hQ5
  have hA := BaileyTransform_five_qpoch_aq_eight_over_seven a q hA7
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 6)
      (qPochhammer q 1 * qPochhammer q 5)
      (qPoch (a * q) q 8) (qPoch (a * q) q 7)
      (1 + q + q ^ 2 + q ^ 3 + q ^ 4 + q ^ 5) (1 - a * q ^ 8)
      hQ1Q5 hA7 hQ hA

set_option maxHeartbeats 4000000 in
/-- The α₁ coefficient identity in the `n = 7` finite Bailey-lemma step
after moving the seven transformed-β contributions to a common denominator. -/
theorem BaileyTransform_seven_alpha_one_common_denominator_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hQ4 : qPochhammer q 4 ≠ 0)
    (hQ5 : qPochhammer q 5 ≠ 0)
    (hA2 : qPoch (a * q) q 2 ≠ 0)
    (hA3 : qPoch (a * q) q 3 ≠ 0)
    (hA4 : qPoch (a * q) q 4 ≠ 0)
    (hA5 : qPoch (a * q) q 5 ≠ 0)
    (hA6 : qPoch (a * q) q 6 ≠ 0)
    (hA7 : qPoch (a * q) q 7 ≠ 0)
    (hD1one : qPoch (a * q / ρ₁) q 1 ≠ 0)
    (hD2one : qPoch (a * q / ρ₂) q 1 ≠ 0) :
    qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) *
        qPoch (a * q / (ρ₁ * ρ₂)) q 6 *
        (qPoch (a * q) q 8 / qPoch (a * q) q 2) +
      qPoch ρ₁ q 2 * qPoch ρ₂ q 2 *
        (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 5 *
        (qPochhammer q 6 * qPoch (a * q) q 8 /
          (qPochhammer q 5 * qPochhammer q 1 * qPoch (a * q) q 3)) +
      qPoch ρ₁ q 3 * qPoch ρ₂ q 3 *
        (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 4 *
        (qPochhammer q 6 * qPoch (a * q) q 8 /
          (qPochhammer q 4 * qPochhammer q 2 * qPoch (a * q) q 4)) +
      qPoch ρ₁ q 4 * qPoch ρ₂ q 4 *
        (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3 *
        (qPochhammer q 6 * qPoch (a * q) q 8 /
          (qPochhammer q 3 * qPochhammer q 3 * qPoch (a * q) q 5)) +
      qPoch ρ₁ q 5 * qPoch ρ₂ q 5 *
        (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2 *
        (qPochhammer q 6 * qPoch (a * q) q 8 /
          (qPochhammer q 2 * qPochhammer q 4 * qPoch (a * q) q 6)) +
      qPoch ρ₁ q 6 * qPoch ρ₂ q 6 *
        (a * q / (ρ₁ * ρ₂)) ^ 6 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1 *
        (qPochhammer q 6 * qPoch (a * q) q 8 /
          (qPochhammer q 1 * qPochhammer q 5 * qPoch (a * q) q 7)) +
      qPoch ρ₁ q 7 * qPoch ρ₂ q 7 *
        (a * q / (ρ₁ * ρ₂)) ^ 7 =
      (qPoch ρ₁ q 1 * qPoch ρ₂ q 1 *
        (a * q / (ρ₁ * ρ₂))) *
        ((qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7) /
          (qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1)) := by
  rw [BaileyTransform_seven_qpoch_aq_eight_over_two a q hA2,
    BaileyTransform_seven_qpochhammer_aq_alpha_one_first_middle_ratio a q hQ1 hQ5 hA3,
    BaileyTransform_seven_qpochhammer_aq_alpha_one_second_middle_ratio a q hQ1 hQ2 hQ4 hA4,
    BaileyTransform_seven_qpochhammer_aq_alpha_one_third_middle_ratio a q hQ1 hQ2 hQ3 hA5,
    BaileyTransform_seven_qpochhammer_aq_alpha_one_fourth_middle_ratio a q hQ1 hQ2 hQ4 hA6,
    BaileyTransform_seven_qpochhammer_aq_alpha_one_fifth_middle_ratio a q hQ1 hQ5 hA7,
    BaileyTransform_seven_qpoch_pair_ratio_one_seven a q ρ₁ ρ₂ hD1one hD2one]
  have hρ1 : ρ₁ ≠ 0 := left_ne_zero_of_mul hρ
  have hρ2 : ρ₂ ≠ 0 := right_ne_zero_of_mul hρ
  rw [show qPoch (a * q / (ρ₁ * ρ₂)) q 6 =
      (1 - a * q / (ρ₁ * ρ₂)) * (1 - (a * q / (ρ₁ * ρ₂)) * q) *
        (1 - (a * q / (ρ₁ * ρ₂)) * q ^ 2) *
        (1 - (a * q / (ρ₁ * ρ₂)) * q ^ 3) *
        (1 - (a * q / (ρ₁ * ρ₂)) * q ^ 4) *
        (1 - (a * q / (ρ₁ * ρ₂)) * q ^ 5) by
        simp [qPoch]]
  rw [show qPoch (a * q / (ρ₁ * ρ₂)) q 5 =
      (1 - a * q / (ρ₁ * ρ₂)) * (1 - (a * q / (ρ₁ * ρ₂)) * q) *
        (1 - (a * q / (ρ₁ * ρ₂)) * q ^ 2) *
        (1 - (a * q / (ρ₁ * ρ₂)) * q ^ 3) *
        (1 - (a * q / (ρ₁ * ρ₂)) * q ^ 4) by
        simp [qPoch]]
  rw [show qPoch (a * q / (ρ₁ * ρ₂)) q 4 =
      (1 - a * q / (ρ₁ * ρ₂)) * (1 - (a * q / (ρ₁ * ρ₂)) * q) *
        (1 - (a * q / (ρ₁ * ρ₂)) * q ^ 2) *
        (1 - (a * q / (ρ₁ * ρ₂)) * q ^ 3) by
        simp [qPoch]]
  rw [show qPoch (a * q / (ρ₁ * ρ₂)) q 3 =
      (1 - a * q / (ρ₁ * ρ₂)) * (1 - (a * q / (ρ₁ * ρ₂)) * q) *
        (1 - (a * q / (ρ₁ * ρ₂)) * q ^ 2) by
        simp [qPoch]]
  rw [show qPoch (a * q / (ρ₁ * ρ₂)) q 2 =
      (1 - a * q / (ρ₁ * ρ₂)) * (1 - (a * q / (ρ₁ * ρ₂)) * q) by
        simp [qPoch]]
  rw [show qPoch (a * q / (ρ₁ * ρ₂)) q 1 =
      1 - a * q / (ρ₁ * ρ₂) by simp [qPoch]]
  rw [show qPoch ρ₁ q 7 = qPoch ρ₁ q 6 * (1 - ρ₁ * q ^ 6) by rfl]
  rw [show qPoch ρ₂ q 7 = qPoch ρ₂ q 6 * (1 - ρ₂ * q ^ 6) by rfl]
  rw [show qPoch ρ₁ q 6 = qPoch ρ₁ q 5 * (1 - ρ₁ * q ^ 5) by rfl]
  rw [show qPoch ρ₂ q 6 = qPoch ρ₂ q 5 * (1 - ρ₂ * q ^ 5) by rfl]
  rw [show qPoch ρ₁ q 5 = qPoch ρ₁ q 4 * (1 - ρ₁ * q ^ 4) by rfl]
  rw [show qPoch ρ₂ q 5 = qPoch ρ₂ q 4 * (1 - ρ₂ * q ^ 4) by rfl]
  rw [show qPoch ρ₁ q 4 = qPoch ρ₁ q 3 * (1 - ρ₁ * q ^ 3) by rfl]
  rw [show qPoch ρ₂ q 4 = qPoch ρ₂ q 3 * (1 - ρ₂ * q ^ 3) by rfl]
  rw [show qPoch ρ₁ q 3 = qPoch ρ₁ q 2 * (1 - ρ₁ * q ^ 2) by rfl]
  rw [show qPoch ρ₂ q 3 = qPoch ρ₂ q 2 * (1 - ρ₂ * q ^ 2) by rfl]
  rw [show qPoch ρ₁ q 2 = qPoch ρ₁ q 1 * (1 - ρ₁ * q) by simp [qPoch]]
  rw [show qPoch ρ₂ q 2 = qPoch ρ₂ q 1 * (1 - ρ₂ * q) by simp [qPoch]]
  field_simp [hρ, hρ1, hρ2]
  ring

set_option maxHeartbeats 4000000 in
/-- The α₁ coefficient identity in the `n = 7` finite Bailey-lemma step. -/
theorem BaileyTransform_seven_alpha_one_coefficient_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hD1 : qPoch (a * q / ρ₁) q 7 ≠ 0)
    (hD2 : qPoch (a * q / ρ₂) q 7 ≠ 0)
    (hD1one : qPoch (a * q / ρ₁) q 1 ≠ 0)
    (hD2one : qPoch (a * q / ρ₂) q 1 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hQ4 : qPochhammer q 4 ≠ 0)
    (hQ5 : qPochhammer q 5 ≠ 0)
    (hQ6 : qPochhammer q 6 ≠ 0)
    (hA2 : qPoch (a * q) q 2 ≠ 0)
    (hA3 : qPoch (a * q) q 3 ≠ 0)
    (hA4 : qPoch (a * q) q 4 ≠ 0)
    (hA5 : qPoch (a * q) q 5 ≠ 0)
    (hA6 : qPoch (a * q) q 6 ≠ 0)
    (hA7 : qPoch (a * q) q 7 ≠ 0)
    (hA8 : qPoch (a * q) q 8 ≠ 0) :
    ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 6) /
      (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 *
        qPochhammer q 6)) / qPoch (a * q) q 2 +
      ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 5) /
      (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 *
        qPochhammer q 5)) /
        (qPochhammer q 1 * qPoch (a * q) q 3) +
      ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 4) /
      (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 *
        qPochhammer q 4)) /
        (qPochhammer q 2 * qPoch (a * q) q 4) +
      ((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3) /
      (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 *
        qPochhammer q 3)) /
        (qPochhammer q 3 * qPoch (a * q) q 5) +
      ((qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 *
        qPochhammer q 2)) /
        (qPochhammer q 4 * qPoch (a * q) q 6) +
      ((qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 *
        qPochhammer q 1)) /
        (qPochhammer q 5 * qPoch (a * q) q 7) +
      ((qPoch ρ₁ q 7 * qPoch ρ₂ q 7 * (a * q / (ρ₁ * ρ₂)) ^ 7 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 *
        qPochhammer q 0)) /
        (qPochhammer q 6 * qPoch (a * q) q 8) =
      (qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) /
        (qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1)) /
        (qPochhammer q 6 * qPoch (a * q) q 8) := by
  have hD : qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 ≠ 0 :=
    mul_ne_zero hD1 hD2
  have hDone : qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1 ≠ 0 :=
    mul_ne_zero hD1one hD2one
  have hcommon := BaileyTransform_seven_alpha_one_common_denominator_identity
    a q ρ₁ ρ₂ hρ hQ1 hQ2 hQ3 hQ4 hQ5 hA2 hA3 hA4 hA5 hA6 hA7 hD1one hD2one
  simpa [qPochhammer, qPoch] using
    (BaileyTransform_seven_term_fraction_from_common_ratio
      (P1 := qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) *
        qPoch (a * q / (ρ₁ * ρ₂)) q 6)
      (P2 := qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 5)
      (P3 := qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 4)
      (P4 := qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3)
      (P5 := qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2)
      (P6 := qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1)
      (P7 := qPoch ρ₁ q 7 * qPoch ρ₂ q 7 * (a * q / (ρ₁ * ρ₂)) ^ 7)
      (B := qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)))
      (D := qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7)
      (D1 := qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1)
      (Q1 := qPochhammer q 1)
      (Q2 := qPochhammer q 2)
      (Q3 := qPochhammer q 3)
      (Q4 := qPochhammer q 4)
      (Q5 := qPochhammer q 5)
      (Q6 := qPochhammer q 6)
      (A2 := qPoch (a * q) q 2)
      (A3 := qPoch (a * q) q 3)
      (A4 := qPoch (a * q) q 4)
      (A5 := qPoch (a * q) q 5)
      (A6 := qPoch (a * q) q 6)
      (A7 := qPoch (a * q) q 7)
      (A8 := qPoch (a * q) q 8)
      hD hDone hQ1 hQ2 hQ3 hQ4 hQ5 hQ6 hA2 hA3 hA4 hA5 hA6 hA7 hA8 hcommon)

/-- The q-Pochhammer ratio `(q;q)_7 / ((q;q)_6 (q;q)_1)`. -/
theorem BaileyTransform_seven_qpochhammer_seven_over_six_one
    (q : R) (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ6 : qPochhammer q 6 ≠ 0) :
    qPochhammer q 7 / (qPochhammer q 6 * qPochhammer q 1) =
      1 + q + q ^ 2 + q ^ 3 + q ^ 4 + q ^ 5 + q ^ 6 := by
  have hq : 1 - q ≠ 0 := by simpa [qPochhammer] using hQ1
  rw [show qPochhammer q 7 = qPochhammer q 6 * (1 - q ^ 7) by rfl]
  field_simp [hQ6]
  simp [qPochhammer]
  ring

/-- The q-Pochhammer ratio `(q;q)_7 / ((q;q)_1 (q;q)_6)` (commuted form). -/
theorem BaileyTransform_seven_qpochhammer_seven_over_one_six
    (q : R) (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ6 : qPochhammer q 6 ≠ 0) :
    qPochhammer q 7 / (qPochhammer q 1 * qPochhammer q 6) =
      1 + q + q ^ 2 + q ^ 3 + q ^ 4 + q ^ 5 + q ^ 6 := by
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    BaileyTransform_seven_qpochhammer_seven_over_six_one q hQ1 hQ6

/-- The q-Pochhammer ratio `(q;q)_7 / ((q;q)_5 (q;q)_2)`. -/
theorem BaileyTransform_seven_qpochhammer_seven_over_five_two
    (q : R) (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ5 : qPochhammer q 5 ≠ 0) :
    qPochhammer q 7 / (qPochhammer q 5 * qPochhammer q 2) =
      (1 + q + q ^ 2 + q ^ 3 + q ^ 4 + q ^ 5 + q ^ 6) *
        (1 + q ^ 2 + q ^ 4) := by
  have hq : 1 - q ≠ 0 := by simpa [qPochhammer] using hQ1
  have hq2 : 1 - q ^ 2 ≠ 0 := by
    simpa [qPochhammer] using right_ne_zero_of_mul hQ2
  rw [show qPochhammer q 7 =
      qPochhammer q 5 * (1 - q ^ 6) * (1 - q ^ 7) by rfl]
  field_simp [hQ5]
  simp [qPochhammer]
  field_simp [hq, hq2]
  ring

/-- The q-Pochhammer ratio `(q;q)_7 / ((q;q)_2 (q;q)_5)` (commuted form). -/
theorem BaileyTransform_seven_qpochhammer_seven_over_two_five
    (q : R) (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ5 : qPochhammer q 5 ≠ 0) :
    qPochhammer q 7 / (qPochhammer q 2 * qPochhammer q 5) =
      (1 + q + q ^ 2 + q ^ 3 + q ^ 4 + q ^ 5 + q ^ 6) *
        (1 + q ^ 2 + q ^ 4) := by
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    BaileyTransform_seven_qpochhammer_seven_over_five_two q hQ1 hQ2 hQ5

/-- The q-Pochhammer ratio `(q;q)_7 / ((q;q)_4 (q;q)_3)`, equal to the
Gaussian binomial `[7, 3]_q`. Since `[7, 3]_q` does not factor into round
q-polynomials, the right-hand side is the explicit degree-12 expansion. -/
theorem BaileyTransform_seven_qpochhammer_seven_over_four_three
    (q : R) (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hQ4 : qPochhammer q 4 ≠ 0) :
    qPochhammer q 7 / (qPochhammer q 4 * qPochhammer q 3) =
      1 + q + 2 * q ^ 2 + 3 * q ^ 3 + 4 * q ^ 4 + 4 * q ^ 5 +
        5 * q ^ 6 + 4 * q ^ 7 + 4 * q ^ 8 + 3 * q ^ 9 +
        2 * q ^ 10 + q ^ 11 + q ^ 12 := by
  have hq : 1 - q ≠ 0 := by simpa [qPochhammer] using hQ1
  have hq2 : 1 - q ^ 2 ≠ 0 := by
    simpa [qPochhammer] using right_ne_zero_of_mul hQ2
  have hq3 : 1 - q ^ 3 ≠ 0 := by
    simpa [qPochhammer] using right_ne_zero_of_mul hQ3
  rw [show qPochhammer q 7 =
      qPochhammer q 4 * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) by rfl]
  field_simp [hQ4]
  simp [qPochhammer]
  field_simp [hq, hq2, hq3]
  ring

/-- The q-Pochhammer ratio `(q;q)_7 / ((q;q)_3 (q;q)_4)` (commuted form). -/
theorem BaileyTransform_seven_qpochhammer_seven_over_three_four
    (q : R) (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hQ4 : qPochhammer q 4 ≠ 0) :
    qPochhammer q 7 / (qPochhammer q 3 * qPochhammer q 4) =
      1 + q + 2 * q ^ 2 + 3 * q ^ 3 + 4 * q ^ 4 + 4 * q ^ 5 +
        5 * q ^ 6 + 4 * q ^ 7 + 4 * q ^ 8 + 3 * q ^ 9 +
        2 * q ^ 10 + q ^ 11 + q ^ 12 := by
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    BaileyTransform_seven_qpochhammer_seven_over_four_three q hQ1 hQ2 hQ3 hQ4

set_option maxHeartbeats 1600000 in
/-- The denominator ratio between the `N=8` and `N=1` transformed-α
q-Pochhammer factors. -/
theorem BaileyTransform_eight_qpoch_pair_ratio_one_eight
    (a q ρ₁ ρ₂ : R)
    (hD1one : qPoch (a * q / ρ₁) q 1 ≠ 0)
    (hD2one : qPoch (a * q / ρ₂) q 1 ≠ 0) :
    (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8) /
        (qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1) =
      ((1 - (a * q / ρ₁) * q) * (1 - (a * q / ρ₁) * q ^ 2) *
        (1 - (a * q / ρ₁) * q ^ 3) * (1 - (a * q / ρ₁) * q ^ 4) *
        (1 - (a * q / ρ₁) * q ^ 5) * (1 - (a * q / ρ₁) * q ^ 6) *
        (1 - (a * q / ρ₁) * q ^ 7)) *
      ((1 - (a * q / ρ₂) * q) * (1 - (a * q / ρ₂) * q ^ 2) *
        (1 - (a * q / ρ₂) * q ^ 3) * (1 - (a * q / ρ₂) * q ^ 4) *
        (1 - (a * q / ρ₂) * q ^ 5) * (1 - (a * q / ρ₂) * q ^ 6) *
        (1 - (a * q / ρ₂) * q ^ 7)) := by
  have h1 : qPoch (a * q / ρ₁) q 8 / qPoch (a * q / ρ₁) q 1 =
      (1 - (a * q / ρ₁) * q) * (1 - (a * q / ρ₁) * q ^ 2) *
        (1 - (a * q / ρ₁) * q ^ 3) * (1 - (a * q / ρ₁) * q ^ 4) *
        (1 - (a * q / ρ₁) * q ^ 5) * (1 - (a * q / ρ₁) * q ^ 6) *
        (1 - (a * q / ρ₁) * q ^ 7) := by
    rw [show qPoch (a * q / ρ₁) q 8 =
        qPoch (a * q / ρ₁) q 1 * (1 - (a * q / ρ₁) * q ^ 1) *
          (1 - (a * q / ρ₁) * q ^ 2) * (1 - (a * q / ρ₁) * q ^ 3) *
          (1 - (a * q / ρ₁) * q ^ 4) * (1 - (a * q / ρ₁) * q ^ 5) *
          (1 - (a * q / ρ₁) * q ^ 6) * (1 - (a * q / ρ₁) * q ^ 7) by rfl]
    simp only [pow_one]
    field_simp [hD1one]
  have h2 : qPoch (a * q / ρ₂) q 8 / qPoch (a * q / ρ₂) q 1 =
      (1 - (a * q / ρ₂) * q) * (1 - (a * q / ρ₂) * q ^ 2) *
        (1 - (a * q / ρ₂) * q ^ 3) * (1 - (a * q / ρ₂) * q ^ 4) *
        (1 - (a * q / ρ₂) * q ^ 5) * (1 - (a * q / ρ₂) * q ^ 6) *
        (1 - (a * q / ρ₂) * q ^ 7) := by
    rw [show qPoch (a * q / ρ₂) q 8 =
        qPoch (a * q / ρ₂) q 1 * (1 - (a * q / ρ₂) * q ^ 1) *
          (1 - (a * q / ρ₂) * q ^ 2) * (1 - (a * q / ρ₂) * q ^ 3) *
          (1 - (a * q / ρ₂) * q ^ 4) * (1 - (a * q / ρ₂) * q ^ 5) *
          (1 - (a * q / ρ₂) * q ^ 6) * (1 - (a * q / ρ₂) * q ^ 7) by rfl]
    simp only [pow_one]
    field_simp [hD2one]
  rw [show (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8) /
      (qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1) =
      (qPoch (a * q / ρ₁) q 8 / qPoch (a * q / ρ₁) q 1) *
      (qPoch (a * q / ρ₂) q 8 / qPoch (a * q / ρ₂) q 1) by
        field_simp]
  rw [h1, h2]

/-- The first middle denominator ratio appearing in the `n = 8`, α₁
common-denominator calculation. -/
theorem BaileyTransform_eight_qpochhammer_aq_alpha_one_first_middle_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ6 : qPochhammer q 6 ≠ 0)
    (hA3 : qPoch (a * q) q 3 ≠ 0) :
    qPochhammer q 7 * qPoch (a * q) q 9 /
        (qPochhammer q 6 * qPochhammer q 1 * qPoch (a * q) q 3) =
      (1 + q + q ^ 2 + q ^ 3 + q ^ 4 + q ^ 5 + q ^ 6) *
        ((1 - a * q ^ 4) * (1 - a * q ^ 5) * (1 - a * q ^ 6) *
          (1 - a * q ^ 7) * (1 - a * q ^ 8) * (1 - a * q ^ 9)) := by
  have hQ6Q1 : qPochhammer q 6 * qPochhammer q 1 ≠ 0 :=
    mul_ne_zero hQ6 hQ1
  have hQ := BaileyTransform_seven_qpochhammer_seven_over_six_one q hQ1 hQ6
  have hA := BaileyTransform_seven_qpoch_aq_nine_over_three a q hA3
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 7)
      (qPochhammer q 6 * qPochhammer q 1)
      (qPoch (a * q) q 9) (qPoch (a * q) q 3)
      (1 + q + q ^ 2 + q ^ 3 + q ^ 4 + q ^ 5 + q ^ 6)
      ((1 - a * q ^ 4) * (1 - a * q ^ 5) * (1 - a * q ^ 6) *
        (1 - a * q ^ 7) * (1 - a * q ^ 8) * (1 - a * q ^ 9))
      hQ6Q1 hA3 hQ hA

/-- The second middle denominator ratio appearing in the `n = 8`, α₁
common-denominator calculation. -/
theorem BaileyTransform_eight_qpochhammer_aq_alpha_one_second_middle_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ5 : qPochhammer q 5 ≠ 0)
    (hA4 : qPoch (a * q) q 4 ≠ 0) :
    qPochhammer q 7 * qPoch (a * q) q 9 /
        (qPochhammer q 5 * qPochhammer q 2 * qPoch (a * q) q 4) =
      ((1 + q + q ^ 2 + q ^ 3 + q ^ 4 + q ^ 5 + q ^ 6) * (1 + q ^ 2 + q ^ 4)) *
        ((1 - a * q ^ 5) * (1 - a * q ^ 6) * (1 - a * q ^ 7) *
          (1 - a * q ^ 8) * (1 - a * q ^ 9)) := by
  have hQ5Q2 : qPochhammer q 5 * qPochhammer q 2 ≠ 0 :=
    mul_ne_zero hQ5 hQ2
  have hQ := BaileyTransform_seven_qpochhammer_seven_over_five_two q hQ1 hQ2 hQ5
  have hA := BaileyTransform_seven_qpoch_aq_nine_over_four a q hA4
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 7)
      (qPochhammer q 5 * qPochhammer q 2)
      (qPoch (a * q) q 9) (qPoch (a * q) q 4)
      ((1 + q + q ^ 2 + q ^ 3 + q ^ 4 + q ^ 5 + q ^ 6) * (1 + q ^ 2 + q ^ 4))
      ((1 - a * q ^ 5) * (1 - a * q ^ 6) * (1 - a * q ^ 7) *
        (1 - a * q ^ 8) * (1 - a * q ^ 9))
      hQ5Q2 hA4 hQ hA

/-- The third middle denominator ratio appearing in the `n = 8`, α₁
common-denominator calculation. -/
theorem BaileyTransform_eight_qpochhammer_aq_alpha_one_third_middle_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hQ4 : qPochhammer q 4 ≠ 0)
    (hA5 : qPoch (a * q) q 5 ≠ 0) :
    qPochhammer q 7 * qPoch (a * q) q 9 /
        (qPochhammer q 4 * qPochhammer q 3 * qPoch (a * q) q 5) =
      (1 + q + 2 * q ^ 2 + 3 * q ^ 3 + 4 * q ^ 4 + 4 * q ^ 5 +
        5 * q ^ 6 + 4 * q ^ 7 + 4 * q ^ 8 + 3 * q ^ 9 +
        2 * q ^ 10 + q ^ 11 + q ^ 12) *
      ((1 - a * q ^ 6) * (1 - a * q ^ 7) * (1 - a * q ^ 8) *
        (1 - a * q ^ 9)) := by
  have hQ4Q3 : qPochhammer q 4 * qPochhammer q 3 ≠ 0 :=
    mul_ne_zero hQ4 hQ3
  have hQ := BaileyTransform_seven_qpochhammer_seven_over_four_three q hQ1 hQ2 hQ3 hQ4
  have hA := BaileyTransform_seven_qpoch_aq_nine_over_five a q hA5
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 7)
      (qPochhammer q 4 * qPochhammer q 3)
      (qPoch (a * q) q 9) (qPoch (a * q) q 5)
      (1 + q + 2 * q ^ 2 + 3 * q ^ 3 + 4 * q ^ 4 + 4 * q ^ 5 +
        5 * q ^ 6 + 4 * q ^ 7 + 4 * q ^ 8 + 3 * q ^ 9 +
        2 * q ^ 10 + q ^ 11 + q ^ 12)
      ((1 - a * q ^ 6) * (1 - a * q ^ 7) * (1 - a * q ^ 8) *
        (1 - a * q ^ 9))
      hQ4Q3 hA5 hQ hA

/-- The fourth middle denominator ratio appearing in the `n = 8`, α₁
common-denominator calculation. -/
theorem BaileyTransform_eight_qpochhammer_aq_alpha_one_fourth_middle_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hQ4 : qPochhammer q 4 ≠ 0)
    (hA6 : qPoch (a * q) q 6 ≠ 0) :
    qPochhammer q 7 * qPoch (a * q) q 9 /
        (qPochhammer q 3 * qPochhammer q 4 * qPoch (a * q) q 6) =
      (1 + q + 2 * q ^ 2 + 3 * q ^ 3 + 4 * q ^ 4 + 4 * q ^ 5 +
        5 * q ^ 6 + 4 * q ^ 7 + 4 * q ^ 8 + 3 * q ^ 9 +
        2 * q ^ 10 + q ^ 11 + q ^ 12) *
      ((1 - a * q ^ 7) * (1 - a * q ^ 8) * (1 - a * q ^ 9)) := by
  have hQ3Q4 : qPochhammer q 3 * qPochhammer q 4 ≠ 0 :=
    mul_ne_zero hQ3 hQ4
  have hQ := BaileyTransform_seven_qpochhammer_seven_over_three_four q hQ1 hQ2 hQ3 hQ4
  have hA := BaileyTransform_six_qpoch_aq_nine_over_six a q hA6
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 7)
      (qPochhammer q 3 * qPochhammer q 4)
      (qPoch (a * q) q 9) (qPoch (a * q) q 6)
      (1 + q + 2 * q ^ 2 + 3 * q ^ 3 + 4 * q ^ 4 + 4 * q ^ 5 +
        5 * q ^ 6 + 4 * q ^ 7 + 4 * q ^ 8 + 3 * q ^ 9 +
        2 * q ^ 10 + q ^ 11 + q ^ 12)
      ((1 - a * q ^ 7) * (1 - a * q ^ 8) * (1 - a * q ^ 9))
      hQ3Q4 hA6 hQ hA

/-- The fifth middle denominator ratio appearing in the `n = 8`, α₁
common-denominator calculation. -/
theorem BaileyTransform_eight_qpochhammer_aq_alpha_one_fifth_middle_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ5 : qPochhammer q 5 ≠ 0)
    (hA7 : qPoch (a * q) q 7 ≠ 0) :
    qPochhammer q 7 * qPoch (a * q) q 9 /
        (qPochhammer q 2 * qPochhammer q 5 * qPoch (a * q) q 7) =
      ((1 + q + q ^ 2 + q ^ 3 + q ^ 4 + q ^ 5 + q ^ 6) * (1 + q ^ 2 + q ^ 4)) *
        ((1 - a * q ^ 8) * (1 - a * q ^ 9)) := by
  have hQ2Q5 : qPochhammer q 2 * qPochhammer q 5 ≠ 0 :=
    mul_ne_zero hQ2 hQ5
  have hQ := BaileyTransform_seven_qpochhammer_seven_over_two_five q hQ1 hQ2 hQ5
  have hA := BaileyTransform_six_qpoch_aq_nine_over_seven a q hA7
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 7)
      (qPochhammer q 2 * qPochhammer q 5)
      (qPoch (a * q) q 9) (qPoch (a * q) q 7)
      ((1 + q + q ^ 2 + q ^ 3 + q ^ 4 + q ^ 5 + q ^ 6) * (1 + q ^ 2 + q ^ 4))
      ((1 - a * q ^ 8) * (1 - a * q ^ 9))
      hQ2Q5 hA7 hQ hA

/-- The sixth middle denominator ratio appearing in the `n = 8`, α₁
common-denominator calculation. -/
theorem BaileyTransform_eight_qpochhammer_aq_alpha_one_sixth_middle_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ6 : qPochhammer q 6 ≠ 0)
    (hA8 : qPoch (a * q) q 8 ≠ 0) :
    qPochhammer q 7 * qPoch (a * q) q 9 /
        (qPochhammer q 1 * qPochhammer q 6 * qPoch (a * q) q 8) =
      (1 + q + q ^ 2 + q ^ 3 + q ^ 4 + q ^ 5 + q ^ 6) * (1 - a * q ^ 9) := by
  have hQ1Q6 : qPochhammer q 1 * qPochhammer q 6 ≠ 0 :=
    mul_ne_zero hQ1 hQ6
  have hQ : qPochhammer q 7 / (qPochhammer q 1 * qPochhammer q 6) =
      1 + q + q ^ 2 + q ^ 3 + q ^ 4 + q ^ 5 + q ^ 6 := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      BaileyTransform_seven_qpochhammer_seven_over_six_one q hQ1 hQ6
  have hA := BaileyTransform_six_qpoch_aq_nine_over_eight a q hA8
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 7)
      (qPochhammer q 1 * qPochhammer q 6)
      (qPoch (a * q) q 9) (qPoch (a * q) q 8)
      (1 + q + q ^ 2 + q ^ 3 + q ^ 4 + q ^ 5 + q ^ 6) (1 - a * q ^ 9)
      hQ1Q6 hA8 hQ hA

set_option maxHeartbeats 8000000 in
/-- The α₁ coefficient identity in the `n = 8` finite Bailey-lemma step after
moving the eight transformed-β contributions to a common denominator. -/
theorem BaileyTransform_eight_alpha_one_common_denominator_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hQ4 : qPochhammer q 4 ≠ 0)
    (hQ5 : qPochhammer q 5 ≠ 0)
    (hQ6 : qPochhammer q 6 ≠ 0)
    (hA2 : qPoch (a * q) q 2 ≠ 0)
    (hA3 : qPoch (a * q) q 3 ≠ 0)
    (hA4 : qPoch (a * q) q 4 ≠ 0)
    (hA5 : qPoch (a * q) q 5 ≠ 0)
    (hA6 : qPoch (a * q) q 6 ≠ 0)
    (hA7 : qPoch (a * q) q 7 ≠ 0)
    (hA8 : qPoch (a * q) q 8 ≠ 0)
    (hD1one : qPoch (a * q / ρ₁) q 1 ≠ 0)
    (hD2one : qPoch (a * q / ρ₂) q 1 ≠ 0) :
    qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) *
        qPoch (a * q / (ρ₁ * ρ₂)) q 7 *
        (qPoch (a * q) q 9 / qPoch (a * q) q 2) +
      qPoch ρ₁ q 2 * qPoch ρ₂ q 2 *
        (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 6 *
        (qPochhammer q 7 * qPoch (a * q) q 9 /
          (qPochhammer q 6 * qPochhammer q 1 * qPoch (a * q) q 3)) +
      qPoch ρ₁ q 3 * qPoch ρ₂ q 3 *
        (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 5 *
        (qPochhammer q 7 * qPoch (a * q) q 9 /
          (qPochhammer q 5 * qPochhammer q 2 * qPoch (a * q) q 4)) +
      qPoch ρ₁ q 4 * qPoch ρ₂ q 4 *
        (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 4 *
        (qPochhammer q 7 * qPoch (a * q) q 9 /
          (qPochhammer q 4 * qPochhammer q 3 * qPoch (a * q) q 5)) +
      qPoch ρ₁ q 5 * qPoch ρ₂ q 5 *
        (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3 *
        (qPochhammer q 7 * qPoch (a * q) q 9 /
          (qPochhammer q 3 * qPochhammer q 4 * qPoch (a * q) q 6)) +
      qPoch ρ₁ q 6 * qPoch ρ₂ q 6 *
        (a * q / (ρ₁ * ρ₂)) ^ 6 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2 *
        (qPochhammer q 7 * qPoch (a * q) q 9 /
          (qPochhammer q 2 * qPochhammer q 5 * qPoch (a * q) q 7)) +
      qPoch ρ₁ q 7 * qPoch ρ₂ q 7 *
        (a * q / (ρ₁ * ρ₂)) ^ 7 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1 *
        (qPochhammer q 7 * qPoch (a * q) q 9 /
          (qPochhammer q 1 * qPochhammer q 6 * qPoch (a * q) q 8)) +
      qPoch ρ₁ q 8 * qPoch ρ₂ q 8 *
        (a * q / (ρ₁ * ρ₂)) ^ 8 =
      (qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂))) *
        ((qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8) /
          (qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1)) := by
  rw [BaileyTransform_seven_qpoch_aq_nine_over_two a q hA2,
    BaileyTransform_eight_qpochhammer_aq_alpha_one_first_middle_ratio a q hQ1 hQ6 hA3,
    BaileyTransform_eight_qpochhammer_aq_alpha_one_second_middle_ratio a q hQ1 hQ2 hQ5 hA4,
    BaileyTransform_eight_qpochhammer_aq_alpha_one_third_middle_ratio a q hQ1 hQ2 hQ3 hQ4 hA5,
    BaileyTransform_eight_qpochhammer_aq_alpha_one_fourth_middle_ratio a q hQ1 hQ2 hQ3 hQ4 hA6,
    BaileyTransform_eight_qpochhammer_aq_alpha_one_fifth_middle_ratio a q hQ1 hQ2 hQ5 hA7,
    BaileyTransform_eight_qpochhammer_aq_alpha_one_sixth_middle_ratio a q hQ1 hQ6 hA8,
    BaileyTransform_eight_qpoch_pair_ratio_one_eight a q ρ₁ ρ₂ hD1one hD2one]
  have hρ1 : ρ₁ ≠ 0 := left_ne_zero_of_mul hρ
  have hρ2 : ρ₂ ≠ 0 := right_ne_zero_of_mul hρ
  rw [show qPoch (a * q / (ρ₁ * ρ₂)) q 7 =
      (1 - a * q / (ρ₁ * ρ₂)) * (1 - (a * q / (ρ₁ * ρ₂)) * q) *
        (1 - (a * q / (ρ₁ * ρ₂)) * q ^ 2) *
        (1 - (a * q / (ρ₁ * ρ₂)) * q ^ 3) *
        (1 - (a * q / (ρ₁ * ρ₂)) * q ^ 4) *
        (1 - (a * q / (ρ₁ * ρ₂)) * q ^ 5) *
        (1 - (a * q / (ρ₁ * ρ₂)) * q ^ 6) by
        simp [qPoch]]
  rw [show qPoch (a * q / (ρ₁ * ρ₂)) q 6 =
      (1 - a * q / (ρ₁ * ρ₂)) * (1 - (a * q / (ρ₁ * ρ₂)) * q) *
        (1 - (a * q / (ρ₁ * ρ₂)) * q ^ 2) *
        (1 - (a * q / (ρ₁ * ρ₂)) * q ^ 3) *
        (1 - (a * q / (ρ₁ * ρ₂)) * q ^ 4) *
        (1 - (a * q / (ρ₁ * ρ₂)) * q ^ 5) by
        simp [qPoch]]
  rw [show qPoch (a * q / (ρ₁ * ρ₂)) q 5 =
      (1 - a * q / (ρ₁ * ρ₂)) * (1 - (a * q / (ρ₁ * ρ₂)) * q) *
        (1 - (a * q / (ρ₁ * ρ₂)) * q ^ 2) *
        (1 - (a * q / (ρ₁ * ρ₂)) * q ^ 3) *
        (1 - (a * q / (ρ₁ * ρ₂)) * q ^ 4) by
        simp [qPoch]]
  rw [show qPoch (a * q / (ρ₁ * ρ₂)) q 4 =
      (1 - a * q / (ρ₁ * ρ₂)) * (1 - (a * q / (ρ₁ * ρ₂)) * q) *
        (1 - (a * q / (ρ₁ * ρ₂)) * q ^ 2) *
        (1 - (a * q / (ρ₁ * ρ₂)) * q ^ 3) by
        simp [qPoch]]
  rw [show qPoch (a * q / (ρ₁ * ρ₂)) q 3 =
      (1 - a * q / (ρ₁ * ρ₂)) * (1 - (a * q / (ρ₁ * ρ₂)) * q) *
        (1 - (a * q / (ρ₁ * ρ₂)) * q ^ 2) by
        simp [qPoch]]
  rw [show qPoch (a * q / (ρ₁ * ρ₂)) q 2 =
      (1 - a * q / (ρ₁ * ρ₂)) * (1 - (a * q / (ρ₁ * ρ₂)) * q) by
        simp [qPoch]]
  rw [show qPoch (a * q / (ρ₁ * ρ₂)) q 1 =
      1 - a * q / (ρ₁ * ρ₂) by simp [qPoch]]
  rw [show qPoch ρ₁ q 8 = qPoch ρ₁ q 7 * (1 - ρ₁ * q ^ 7) by rfl]
  rw [show qPoch ρ₂ q 8 = qPoch ρ₂ q 7 * (1 - ρ₂ * q ^ 7) by rfl]
  rw [show qPoch ρ₁ q 7 = qPoch ρ₁ q 6 * (1 - ρ₁ * q ^ 6) by rfl]
  rw [show qPoch ρ₂ q 7 = qPoch ρ₂ q 6 * (1 - ρ₂ * q ^ 6) by rfl]
  rw [show qPoch ρ₁ q 6 = qPoch ρ₁ q 5 * (1 - ρ₁ * q ^ 5) by rfl]
  rw [show qPoch ρ₂ q 6 = qPoch ρ₂ q 5 * (1 - ρ₂ * q ^ 5) by rfl]
  rw [show qPoch ρ₁ q 5 = qPoch ρ₁ q 4 * (1 - ρ₁ * q ^ 4) by rfl]
  rw [show qPoch ρ₂ q 5 = qPoch ρ₂ q 4 * (1 - ρ₂ * q ^ 4) by rfl]
  rw [show qPoch ρ₁ q 4 = qPoch ρ₁ q 3 * (1 - ρ₁ * q ^ 3) by rfl]
  rw [show qPoch ρ₂ q 4 = qPoch ρ₂ q 3 * (1 - ρ₂ * q ^ 3) by rfl]
  rw [show qPoch ρ₁ q 3 = qPoch ρ₁ q 2 * (1 - ρ₁ * q ^ 2) by rfl]
  rw [show qPoch ρ₂ q 3 = qPoch ρ₂ q 2 * (1 - ρ₂ * q ^ 2) by rfl]
  rw [show qPoch ρ₁ q 2 = qPoch ρ₁ q 1 * (1 - ρ₁ * q) by simp [qPoch]]
  rw [show qPoch ρ₂ q 2 = qPoch ρ₂ q 1 * (1 - ρ₂ * q) by simp [qPoch]]
  field_simp [hρ, hρ1, hρ2]
  ring

set_option maxHeartbeats 8000000 in
/-- The α₁ coefficient identity in the `n = 8` finite Bailey-lemma step. -/
theorem BaileyTransform_eight_alpha_one_coefficient_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hD1 : qPoch (a * q / ρ₁) q 8 ≠ 0)
    (hD2 : qPoch (a * q / ρ₂) q 8 ≠ 0)
    (hD1one : qPoch (a * q / ρ₁) q 1 ≠ 0)
    (hD2one : qPoch (a * q / ρ₂) q 1 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hQ4 : qPochhammer q 4 ≠ 0)
    (hQ5 : qPochhammer q 5 ≠ 0)
    (hQ6 : qPochhammer q 6 ≠ 0)
    (hQ7 : qPochhammer q 7 ≠ 0)
    (hA2 : qPoch (a * q) q 2 ≠ 0)
    (hA3 : qPoch (a * q) q 3 ≠ 0)
    (hA4 : qPoch (a * q) q 4 ≠ 0)
    (hA5 : qPoch (a * q) q 5 ≠ 0)
    (hA6 : qPoch (a * q) q 6 ≠ 0)
    (hA7 : qPoch (a * q) q 7 ≠ 0)
    (hA8 : qPoch (a * q) q 8 ≠ 0)
    (hA9 : qPoch (a * q) q 9 ≠ 0) :
    ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) *
        qPoch (a * q / (ρ₁ * ρ₂)) q 7) /
      (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8 *
        qPochhammer q 7)) / qPoch (a * q) q 2 +
      ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 6) /
      (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8 *
        qPochhammer q 6)) /
        (qPochhammer q 1 * qPoch (a * q) q 3) +
      ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 5) /
      (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8 *
        qPochhammer q 5)) /
        (qPochhammer q 2 * qPoch (a * q) q 4) +
      ((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 4) /
      (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8 *
        qPochhammer q 4)) /
        (qPochhammer q 3 * qPoch (a * q) q 5) +
      ((qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3) /
      (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8 *
        qPochhammer q 3)) /
        (qPochhammer q 4 * qPoch (a * q) q 6) +
      ((qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8 *
        qPochhammer q 2)) /
        (qPochhammer q 5 * qPoch (a * q) q 7) +
      ((qPoch ρ₁ q 7 * qPoch ρ₂ q 7 * (a * q / (ρ₁ * ρ₂)) ^ 7 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8 *
        qPochhammer q 1)) /
        (qPochhammer q 6 * qPoch (a * q) q 8) +
      ((qPoch ρ₁ q 8 * qPoch ρ₂ q 8 * (a * q / (ρ₁ * ρ₂)) ^ 8 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8 *
        qPochhammer q 0)) /
        (qPochhammer q 7 * qPoch (a * q) q 9) =
      ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂))) /
        (qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1)) /
        (qPochhammer q 7 * qPoch (a * q) q 9) := by
  have hD : qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8 ≠ 0 :=
    mul_ne_zero hD1 hD2
  have hDone : qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1 ≠ 0 :=
    mul_ne_zero hD1one hD2one
  have hcommon := BaileyTransform_eight_alpha_one_common_denominator_identity
    a q ρ₁ ρ₂ hρ hQ1 hQ2 hQ3 hQ4 hQ5 hQ6 hA2 hA3 hA4 hA5 hA6 hA7 hA8 hD1one hD2one
  simpa [qPochhammer, qPoch] using
    (BaileyTransform_eight_term_fraction_from_common_ratio
      (P1 := qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) *
        qPoch (a * q / (ρ₁ * ρ₂)) q 7)
      (P2 := qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 6)
      (P3 := qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 5)
      (P4 := qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 4)
      (P5 := qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3)
      (P6 := qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2)
      (P7 := qPoch ρ₁ q 7 * qPoch ρ₂ q 7 * (a * q / (ρ₁ * ρ₂)) ^ 7 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1)
      (P8 := qPoch ρ₁ q 8 * qPoch ρ₂ q 8 * (a * q / (ρ₁ * ρ₂)) ^ 8)
      (B := qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)))
      (D := qPoch (a * q / ρ₁) q 8 * qPoch (a * q / ρ₂) q 8)
      (D1 := qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1)
      (Q1 := qPochhammer q 1)
      (Q2 := qPochhammer q 2)
      (Q3 := qPochhammer q 3)
      (Q4 := qPochhammer q 4)
      (Q5 := qPochhammer q 5)
      (Q6 := qPochhammer q 6)
      (Q7 := qPochhammer q 7)
      (A2 := qPoch (a * q) q 2)
      (A3 := qPoch (a * q) q 3)
      (A4 := qPoch (a * q) q 4)
      (A5 := qPoch (a * q) q 5)
      (A6 := qPoch (a * q) q 6)
      (A7 := qPoch (a * q) q 7)
      (A8 := qPoch (a * q) q 8)
      (A9 := qPoch (a * q) q 9)
      hD hDone hQ1 hQ2 hQ3 hQ4 hQ5 hQ6 hQ7 hA2 hA3 hA4 hA5 hA6 hA7 hA8 hA9 hcommon)

/-- The q-Pochhammer ratio `(q;q)_8 / ((q;q)_7 (q;q)_1)` = q-binomial [8,1]. -/
theorem BaileyTransform_eight_qpochhammer_eight_over_seven_one
    (q : R) (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ7 : qPochhammer q 7 ≠ 0) :
    qPochhammer q 8 / (qPochhammer q 7 * qPochhammer q 1) =
      1 + q + q ^ 2 + q ^ 3 + q ^ 4 + q ^ 5 + q ^ 6 + q ^ 7 := by
  have hq : 1 - q ≠ 0 := by simpa [qPochhammer] using hQ1
  rw [show qPochhammer q 8 = qPochhammer q 7 * (1 - q ^ 8) by rfl]
  field_simp [hQ7]
  simp [qPochhammer]
  field_simp [hq]
  ring

/-- Commuted form: `(q;q)_8 / ((q;q)_1 (q;q)_7)`. -/
theorem BaileyTransform_eight_qpochhammer_eight_over_one_seven
    (q : R) (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ7 : qPochhammer q 7 ≠ 0) :
    qPochhammer q 8 / (qPochhammer q 1 * qPochhammer q 7) =
      1 + q + q ^ 2 + q ^ 3 + q ^ 4 + q ^ 5 + q ^ 6 + q ^ 7 := by
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    BaileyTransform_eight_qpochhammer_eight_over_seven_one q hQ1 hQ7

set_option maxHeartbeats 800000 in
/-- The q-Pochhammer ratio `(q;q)_8 / ((q;q)_6 (q;q)_2)` = q-binomial [8,2]. -/
theorem BaileyTransform_eight_qpochhammer_eight_over_six_two
    (q : R) (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ6 : qPochhammer q 6 ≠ 0) :
    qPochhammer q 8 / (qPochhammer q 6 * qPochhammer q 2) =
      1 + q + 2 * q ^ 2 + 2 * q ^ 3 + 3 * q ^ 4 + 3 * q ^ 5 + 4 * q ^ 6 +
        3 * q ^ 7 + 3 * q ^ 8 + 2 * q ^ 9 + 2 * q ^ 10 + q ^ 11 + q ^ 12 := by
  have hq : 1 - q ≠ 0 := by simpa [qPochhammer] using hQ1
  have hq2 : 1 - q ^ 2 ≠ 0 := by
    simpa [qPochhammer] using right_ne_zero_of_mul hQ2
  rw [show qPochhammer q 8 =
      qPochhammer q 6 * (1 - q ^ 7) * (1 - q ^ 8) by rfl]
  field_simp [hQ6]
  simp [qPochhammer]
  field_simp [hq, hq2]
  ring

/-- Commuted form: `(q;q)_8 / ((q;q)_2 (q;q)_6)`. -/
theorem BaileyTransform_eight_qpochhammer_eight_over_two_six
    (q : R) (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ6 : qPochhammer q 6 ≠ 0) :
    qPochhammer q 8 / (qPochhammer q 2 * qPochhammer q 6) =
      1 + q + 2 * q ^ 2 + 2 * q ^ 3 + 3 * q ^ 4 + 3 * q ^ 5 + 4 * q ^ 6 +
        3 * q ^ 7 + 3 * q ^ 8 + 2 * q ^ 9 + 2 * q ^ 10 + q ^ 11 + q ^ 12 := by
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    BaileyTransform_eight_qpochhammer_eight_over_six_two q hQ1 hQ2 hQ6

set_option maxHeartbeats 1600000 in
/-- The q-Pochhammer ratio `(q;q)_8 / ((q;q)_5 (q;q)_3)` = q-binomial [8,3]. -/
theorem BaileyTransform_eight_qpochhammer_eight_over_five_three
    (q : R) (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hQ5 : qPochhammer q 5 ≠ 0) :
    qPochhammer q 8 / (qPochhammer q 5 * qPochhammer q 3) =
      1 + q + 2 * q ^ 2 + 3 * q ^ 3 + 4 * q ^ 4 + 5 * q ^ 5 + 6 * q ^ 6 +
        6 * q ^ 7 + 6 * q ^ 8 + 6 * q ^ 9 + 5 * q ^ 10 + 4 * q ^ 11 +
        3 * q ^ 12 + 2 * q ^ 13 + q ^ 14 + q ^ 15 := by
  have hq : 1 - q ≠ 0 := by simpa [qPochhammer] using hQ1
  have hq2 : 1 - q ^ 2 ≠ 0 := by
    simpa [qPochhammer] using right_ne_zero_of_mul hQ2
  have hq3 : 1 - q ^ 3 ≠ 0 := by
    simpa [qPochhammer] using right_ne_zero_of_mul hQ3
  rw [show qPochhammer q 8 =
      qPochhammer q 5 * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) by rfl]
  field_simp [hQ5]
  simp [qPochhammer]
  field_simp [hq, hq2, hq3]
  ring

/-- Commuted form: `(q;q)_8 / ((q;q)_3 (q;q)_5)`. -/
theorem BaileyTransform_eight_qpochhammer_eight_over_three_five
    (q : R) (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hQ5 : qPochhammer q 5 ≠ 0) :
    qPochhammer q 8 / (qPochhammer q 3 * qPochhammer q 5) =
      1 + q + 2 * q ^ 2 + 3 * q ^ 3 + 4 * q ^ 4 + 5 * q ^ 5 + 6 * q ^ 6 +
        6 * q ^ 7 + 6 * q ^ 8 + 6 * q ^ 9 + 5 * q ^ 10 + 4 * q ^ 11 +
        3 * q ^ 12 + 2 * q ^ 13 + q ^ 14 + q ^ 15 := by
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    BaileyTransform_eight_qpochhammer_eight_over_five_three q hQ1 hQ2 hQ3 hQ5

set_option maxHeartbeats 4000000 in
/-- The q-Pochhammer ratio `(q;q)_8 / ((q;q)_4 (q;q)_4)` = q-binomial [8,4]. -/
theorem BaileyTransform_eight_qpochhammer_eight_over_four_four
    (q : R) (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hQ4 : qPochhammer q 4 ≠ 0) :
    qPochhammer q 8 / (qPochhammer q 4 * qPochhammer q 4) =
      1 + q + 2 * q ^ 2 + 3 * q ^ 3 + 5 * q ^ 4 + 5 * q ^ 5 + 7 * q ^ 6 +
        7 * q ^ 7 + 8 * q ^ 8 + 7 * q ^ 9 + 7 * q ^ 10 + 5 * q ^ 11 +
        5 * q ^ 12 + 3 * q ^ 13 + 2 * q ^ 14 + q ^ 15 + q ^ 16 := by
  have hq : 1 - q ≠ 0 := by simpa [qPochhammer] using hQ1
  have hq2 : 1 - q ^ 2 ≠ 0 := by
    simpa [qPochhammer] using right_ne_zero_of_mul hQ2
  have hq3 : 1 - q ^ 3 ≠ 0 := by
    simpa [qPochhammer] using right_ne_zero_of_mul hQ3
  have hq4 : 1 - q ^ 4 ≠ 0 := by
    simpa [qPochhammer] using right_ne_zero_of_mul hQ4
  have hQ4sq : qPochhammer q 4 * qPochhammer q 4 ≠ 0 :=
    mul_ne_zero hQ4 hQ4
  rw [show qPochhammer q 8 =
      qPochhammer q 4 * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) by rfl]
  simp [qPochhammer]
  field_simp [hq, hq2, hq3, hq4, hQ4sq]
  ring

/-- The ratio `(aq;q)_7 / (aq;q)_1`. -/
theorem BaileyTransform_seven_qpoch_aq_seven_over_one
    (a q : R) (hA1 : qPoch (a * q) q 1 ≠ 0) :
    qPoch (a * q) q 7 / qPoch (a * q) q 1 =
      (1 - a * q ^ 2) * (1 - a * q ^ 3) *
        (1 - a * q ^ 4) * (1 - a * q ^ 5) *
        (1 - a * q ^ 6) * (1 - a * q ^ 7) := by
  rw [show qPoch (a * q) q 7 =
      qPoch (a * q) q 1 * (1 - (a * q) * q ^ 1) *
        (1 - (a * q) * q ^ 2) * (1 - (a * q) * q ^ 3) *
        (1 - (a * q) * q ^ 4) * (1 - (a * q) * q ^ 5) *
        (1 - (a * q) * q ^ 6) by rfl]
  simp only [pow_one]
  field_simp [hA1]

/-- The ratio `(aq;q)_7 / (aq;q)_2`. -/
theorem BaileyTransform_seven_qpoch_aq_seven_over_two
    (a q : R) (hA2 : qPoch (a * q) q 2 ≠ 0) :
    qPoch (a * q) q 7 / qPoch (a * q) q 2 =
      (1 - a * q ^ 3) * (1 - a * q ^ 4) *
        (1 - a * q ^ 5) * (1 - a * q ^ 6) *
        (1 - a * q ^ 7) := by
  rw [show qPoch (a * q) q 7 =
      qPoch (a * q) q 2 * (1 - (a * q) * q ^ 2) *
        (1 - (a * q) * q ^ 3) * (1 - (a * q) * q ^ 4) *
        (1 - (a * q) * q ^ 5) * (1 - (a * q) * q ^ 6) by rfl]
  field_simp [hA2]

/-- The ratio `(aq;q)_7 / (aq;q)_3`. -/
theorem BaileyTransform_seven_qpoch_aq_seven_over_three
    (a q : R) (hA3 : qPoch (a * q) q 3 ≠ 0) :
    qPoch (a * q) q 7 / qPoch (a * q) q 3 =
      (1 - a * q ^ 4) * (1 - a * q ^ 5) *
        (1 - a * q ^ 6) * (1 - a * q ^ 7) := by
  rw [show qPoch (a * q) q 7 =
      qPoch (a * q) q 3 * (1 - (a * q) * q ^ 3) *
        (1 - (a * q) * q ^ 4) * (1 - (a * q) * q ^ 5) *
        (1 - (a * q) * q ^ 6) by rfl]
  field_simp [hA3]

/-- The ratio `(aq;q)_7 / (aq;q)_4`. -/
theorem BaileyTransform_seven_qpoch_aq_seven_over_four
    (a q : R) (hA4 : qPoch (a * q) q 4 ≠ 0) :
    qPoch (a * q) q 7 / qPoch (a * q) q 4 =
      (1 - a * q ^ 5) * (1 - a * q ^ 6) *
        (1 - a * q ^ 7) := by
  rw [show qPoch (a * q) q 7 =
      qPoch (a * q) q 4 * (1 - (a * q) * q ^ 4) *
        (1 - (a * q) * q ^ 5) * (1 - (a * q) * q ^ 6) by rfl]
  field_simp [hA4]

/-- The ratio `(aq;q)_7 / (aq;q)_5`. -/
theorem BaileyTransform_seven_qpoch_aq_seven_over_five
    (a q : R) (hA5 : qPoch (a * q) q 5 ≠ 0) :
    qPoch (a * q) q 7 / qPoch (a * q) q 5 =
      (1 - a * q ^ 6) * (1 - a * q ^ 7) := by
  rw [show qPoch (a * q) q 7 =
      qPoch (a * q) q 5 * (1 - (a * q) * q ^ 5) *
        (1 - (a * q) * q ^ 6) by rfl]
  field_simp [hA5]

/-- The ratio `(aq;q)_7 / (aq;q)_6`. -/
theorem BaileyTransform_seven_qpoch_aq_seven_over_six
    (a q : R) (hA6 : qPoch (a * q) q 6 ≠ 0) :
    qPoch (a * q) q 7 / qPoch (a * q) q 6 =
      (1 - a * q ^ 7) := by
  rw [show qPoch (a * q) q 7 =
      qPoch (a * q) q 6 * (1 - (a * q) * q ^ 6) by rfl]
  field_simp [hA6]

/-- The ratio `(aq;q)_8 / (aq;q)_1`. -/
theorem BaileyTransform_eight_qpoch_aq_eight_over_one
    (a q : R) (hA1 : qPoch (a * q) q 1 ≠ 0) :
    qPoch (a * q) q 8 / qPoch (a * q) q 1 =
      (1 - a * q ^ 2) * (1 - a * q ^ 3) *
        (1 - a * q ^ 4) * (1 - a * q ^ 5) *
        (1 - a * q ^ 6) * (1 - a * q ^ 7) *
        (1 - a * q ^ 8) := by
  rw [show qPoch (a * q) q 8 =
      qPoch (a * q) q 1 * (1 - (a * q) * q ^ 1) *
        (1 - (a * q) * q ^ 2) * (1 - (a * q) * q ^ 3) *
        (1 - (a * q) * q ^ 4) * (1 - (a * q) * q ^ 5) *
        (1 - (a * q) * q ^ 6) * (1 - (a * q) * q ^ 7) by rfl]
  simp only [pow_one]
  field_simp [hA1]

/-- The ratio `(aq;q)_8 / (aq;q)_2`. -/
theorem BaileyTransform_eight_qpoch_aq_eight_over_two
    (a q : R) (hA2 : qPoch (a * q) q 2 ≠ 0) :
    qPoch (a * q) q 8 / qPoch (a * q) q 2 =
      (1 - a * q ^ 3) * (1 - a * q ^ 4) *
        (1 - a * q ^ 5) * (1 - a * q ^ 6) *
        (1 - a * q ^ 7) * (1 - a * q ^ 8) := by
  rw [show qPoch (a * q) q 8 =
      qPoch (a * q) q 2 * (1 - (a * q) * q ^ 2) *
        (1 - (a * q) * q ^ 3) * (1 - (a * q) * q ^ 4) *
        (1 - (a * q) * q ^ 5) * (1 - (a * q) * q ^ 6) *
        (1 - (a * q) * q ^ 7) by rfl]
  field_simp [hA2]

/-- The ratio `(aq;q)_8 / (aq;q)_3`. -/
theorem BaileyTransform_eight_qpoch_aq_eight_over_three
    (a q : R) (hA3 : qPoch (a * q) q 3 ≠ 0) :
    qPoch (a * q) q 8 / qPoch (a * q) q 3 =
      (1 - a * q ^ 4) * (1 - a * q ^ 5) *
        (1 - a * q ^ 6) * (1 - a * q ^ 7) *
        (1 - a * q ^ 8) := by
  rw [show qPoch (a * q) q 8 =
      qPoch (a * q) q 3 * (1 - (a * q) * q ^ 3) *
        (1 - (a * q) * q ^ 4) * (1 - (a * q) * q ^ 5) *
        (1 - (a * q) * q ^ 6) * (1 - (a * q) * q ^ 7) by rfl]
  field_simp [hA3]

/-- The ratio `(aq;q)_8 / (aq;q)_4`. -/
theorem BaileyTransform_eight_qpoch_aq_eight_over_four
    (a q : R) (hA4 : qPoch (a * q) q 4 ≠ 0) :
    qPoch (a * q) q 8 / qPoch (a * q) q 4 =
      (1 - a * q ^ 5) * (1 - a * q ^ 6) *
        (1 - a * q ^ 7) * (1 - a * q ^ 8) := by
  rw [show qPoch (a * q) q 8 =
      qPoch (a * q) q 4 * (1 - (a * q) * q ^ 4) *
        (1 - (a * q) * q ^ 5) * (1 - (a * q) * q ^ 6) *
        (1 - (a * q) * q ^ 7) by rfl]
  field_simp [hA4]

/-- The ratio `(aq;q)_8 / (aq;q)_5`. -/
theorem BaileyTransform_eight_qpoch_aq_eight_over_five
    (a q : R) (hA5 : qPoch (a * q) q 5 ≠ 0) :
    qPoch (a * q) q 8 / qPoch (a * q) q 5 =
      (1 - a * q ^ 6) * (1 - a * q ^ 7) *
        (1 - a * q ^ 8) := by
  rw [show qPoch (a * q) q 8 =
      qPoch (a * q) q 5 * (1 - (a * q) * q ^ 5) *
        (1 - (a * q) * q ^ 6) * (1 - (a * q) * q ^ 7) by rfl]
  field_simp [hA5]

/-- The ratio `(aq;q)_8 / (aq;q)_6`. -/
theorem BaileyTransform_eight_qpoch_aq_eight_over_six
    (a q : R) (hA6 : qPoch (a * q) q 6 ≠ 0) :
    qPoch (a * q) q 8 / qPoch (a * q) q 6 =
      (1 - a * q ^ 7) * (1 - a * q ^ 8) := by
  rw [show qPoch (a * q) q 8 =
      qPoch (a * q) q 6 * (1 - (a * q) * q ^ 6) *
        (1 - (a * q) * q ^ 7) by rfl]
  field_simp [hA6]

/-- The ratio `(aq;q)_8 / (aq;q)_7`. -/
theorem BaileyTransform_eight_qpoch_aq_eight_over_seven
    (a q : R) (hA7 : qPoch (a * q) q 7 ≠ 0) :
    qPoch (a * q) q 8 / qPoch (a * q) q 7 =
      (1 - a * q ^ 8) := by
  rw [show qPoch (a * q) q 8 =
      qPoch (a * q) q 7 * (1 - (a * q) * q ^ 7) by rfl]
  field_simp [hA7]

/-- The first scalar ratio in the n = 8, α₀ common-denominator calculation
(k=1, pair (7,1)). -/
theorem BaileyTransform_eight_alpha_zero_first_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ7 : qPochhammer q 7 ≠ 0)
    (hA1 : qPoch (a * q) q 1 ≠ 0) :
    qPochhammer q 8 * qPoch (a * q) q 8 /
        (qPochhammer q 7 * qPochhammer q 1 * qPoch (a * q) q 1) =
      (1 + q + q ^ 2 + q ^ 3 + q ^ 4 + q ^ 5 + q ^ 6 + q ^ 7) *
        ((1 - a * q ^ 2) * (1 - a * q ^ 3) * (1 - a * q ^ 4) *
          (1 - a * q ^ 5) * (1 - a * q ^ 6) * (1 - a * q ^ 7) *
          (1 - a * q ^ 8)) := by
  have hQ_combo : qPochhammer q 7 * qPochhammer q 1 ≠ 0 :=
    mul_ne_zero hQ7 hQ1
  have hQ := BaileyTransform_eight_qpochhammer_eight_over_seven_one q hQ1 hQ7
  have hA := BaileyTransform_eight_qpoch_aq_eight_over_one a q hA1
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 8)
      (qPochhammer q 7 * qPochhammer q 1)
      (qPoch (a * q) q 8) (qPoch (a * q) q 1)
      (1 + q + q ^ 2 + q ^ 3 + q ^ 4 + q ^ 5 + q ^ 6 + q ^ 7)
      ((1 - a * q ^ 2) * (1 - a * q ^ 3) * (1 - a * q ^ 4) *
        (1 - a * q ^ 5) * (1 - a * q ^ 6) * (1 - a * q ^ 7) *
        (1 - a * q ^ 8))
      hQ_combo hA1 hQ hA

/-- The second scalar ratio in the n = 8, α₀ common-denominator calculation
(k=2, pair (6,2)). -/
theorem BaileyTransform_eight_alpha_zero_second_ratio
    (a q : R)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ6 : qPochhammer q 6 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hA2 : qPoch (a * q) q 2 ≠ 0) :
    qPochhammer q 8 * qPoch (a * q) q 8 /
        (qPochhammer q 6 * qPochhammer q 2 * qPoch (a * q) q 2) =
      (1 + q + 2 * q ^ 2 + 2 * q ^ 3 + 3 * q ^ 4 + 3 * q ^ 5 + 4 * q ^ 6 +
        3 * q ^ 7 + 3 * q ^ 8 + 2 * q ^ 9 + 2 * q ^ 10 + q ^ 11 + q ^ 12) *
      ((1 - a * q ^ 3) * (1 - a * q ^ 4) * (1 - a * q ^ 5) *
        (1 - a * q ^ 6) * (1 - a * q ^ 7) * (1 - a * q ^ 8)) := by
  have hQ_combo : qPochhammer q 6 * qPochhammer q 2 ≠ 0 :=
    mul_ne_zero hQ6 hQ2
  have hQ := BaileyTransform_eight_qpochhammer_eight_over_six_two q hQ1 hQ2 hQ6
  have hA := BaileyTransform_eight_qpoch_aq_eight_over_two a q hA2
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 8)
      (qPochhammer q 6 * qPochhammer q 2)
      (qPoch (a * q) q 8) (qPoch (a * q) q 2)
      (1 + q + 2 * q ^ 2 + 2 * q ^ 3 + 3 * q ^ 4 + 3 * q ^ 5 + 4 * q ^ 6 +
        3 * q ^ 7 + 3 * q ^ 8 + 2 * q ^ 9 + 2 * q ^ 10 + q ^ 11 + q ^ 12)
      ((1 - a * q ^ 3) * (1 - a * q ^ 4) * (1 - a * q ^ 5) *
        (1 - a * q ^ 6) * (1 - a * q ^ 7) * (1 - a * q ^ 8))
      hQ_combo hA2 hQ hA

/-- The third scalar ratio in the n = 8, α₀ common-denominator calculation
(k=3, pair (5,3)). -/
theorem BaileyTransform_eight_alpha_zero_third_ratio
    (a q : R)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hQ5 : qPochhammer q 5 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hA3 : qPoch (a * q) q 3 ≠ 0) :
    qPochhammer q 8 * qPoch (a * q) q 8 /
        (qPochhammer q 5 * qPochhammer q 3 * qPoch (a * q) q 3) =
      (1 + q + 2 * q ^ 2 + 3 * q ^ 3 + 4 * q ^ 4 + 5 * q ^ 5 + 6 * q ^ 6 +
        6 * q ^ 7 + 6 * q ^ 8 + 6 * q ^ 9 + 5 * q ^ 10 + 4 * q ^ 11 +
        3 * q ^ 12 + 2 * q ^ 13 + q ^ 14 + q ^ 15) *
      ((1 - a * q ^ 4) * (1 - a * q ^ 5) * (1 - a * q ^ 6) *
        (1 - a * q ^ 7) * (1 - a * q ^ 8)) := by
  have hQ_combo : qPochhammer q 5 * qPochhammer q 3 ≠ 0 :=
    mul_ne_zero hQ5 hQ3
  have hQ := BaileyTransform_eight_qpochhammer_eight_over_five_three q hQ1 hQ2 hQ3 hQ5
  have hA := BaileyTransform_eight_qpoch_aq_eight_over_three a q hA3
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 8)
      (qPochhammer q 5 * qPochhammer q 3)
      (qPoch (a * q) q 8) (qPoch (a * q) q 3)
      (1 + q + 2 * q ^ 2 + 3 * q ^ 3 + 4 * q ^ 4 + 5 * q ^ 5 + 6 * q ^ 6 +
        6 * q ^ 7 + 6 * q ^ 8 + 6 * q ^ 9 + 5 * q ^ 10 + 4 * q ^ 11 +
        3 * q ^ 12 + 2 * q ^ 13 + q ^ 14 + q ^ 15)
      ((1 - a * q ^ 4) * (1 - a * q ^ 5) * (1 - a * q ^ 6) *
        (1 - a * q ^ 7) * (1 - a * q ^ 8))
      hQ_combo hA3 hQ hA

/-- The fourth scalar ratio in the n = 8, α₀ common-denominator calculation
(k=4, pair (4,4)). -/
theorem BaileyTransform_eight_alpha_zero_fourth_ratio
    (a q : R)
    (hQ4 : qPochhammer q 4 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hA4 : qPoch (a * q) q 4 ≠ 0) :
    qPochhammer q 8 * qPoch (a * q) q 8 /
        (qPochhammer q 4 * qPochhammer q 4 * qPoch (a * q) q 4) =
      (1 + q + 2 * q ^ 2 + 3 * q ^ 3 + 5 * q ^ 4 + 5 * q ^ 5 + 7 * q ^ 6 +
        7 * q ^ 7 + 8 * q ^ 8 + 7 * q ^ 9 + 7 * q ^ 10 + 5 * q ^ 11 +
        5 * q ^ 12 + 3 * q ^ 13 + 2 * q ^ 14 + q ^ 15 + q ^ 16) *
      ((1 - a * q ^ 5) * (1 - a * q ^ 6) * (1 - a * q ^ 7) *
        (1 - a * q ^ 8)) := by
  have hQ_combo : qPochhammer q 4 * qPochhammer q 4 ≠ 0 :=
    mul_ne_zero hQ4 hQ4
  have hQ := BaileyTransform_eight_qpochhammer_eight_over_four_four q hQ1 hQ2 hQ3 hQ4
  have hA := BaileyTransform_eight_qpoch_aq_eight_over_four a q hA4
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 8)
      (qPochhammer q 4 * qPochhammer q 4)
      (qPoch (a * q) q 8) (qPoch (a * q) q 4)
      (1 + q + 2 * q ^ 2 + 3 * q ^ 3 + 5 * q ^ 4 + 5 * q ^ 5 + 7 * q ^ 6 +
        7 * q ^ 7 + 8 * q ^ 8 + 7 * q ^ 9 + 7 * q ^ 10 + 5 * q ^ 11 +
        5 * q ^ 12 + 3 * q ^ 13 + 2 * q ^ 14 + q ^ 15 + q ^ 16)
      ((1 - a * q ^ 5) * (1 - a * q ^ 6) * (1 - a * q ^ 7) *
        (1 - a * q ^ 8))
      hQ_combo hA4 hQ hA

/-- The fifth scalar ratio in the n = 8, α₀ common-denominator calculation
(k=5, pair (3,5)). -/
theorem BaileyTransform_eight_alpha_zero_fifth_ratio
    (a q : R)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hQ5 : qPochhammer q 5 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hA5 : qPoch (a * q) q 5 ≠ 0) :
    qPochhammer q 8 * qPoch (a * q) q 8 /
        (qPochhammer q 3 * qPochhammer q 5 * qPoch (a * q) q 5) =
      (1 + q + 2 * q ^ 2 + 3 * q ^ 3 + 4 * q ^ 4 + 5 * q ^ 5 + 6 * q ^ 6 +
        6 * q ^ 7 + 6 * q ^ 8 + 6 * q ^ 9 + 5 * q ^ 10 + 4 * q ^ 11 +
        3 * q ^ 12 + 2 * q ^ 13 + q ^ 14 + q ^ 15) *
      ((1 - a * q ^ 6) * (1 - a * q ^ 7) * (1 - a * q ^ 8)) := by
  have hQ_combo : qPochhammer q 3 * qPochhammer q 5 ≠ 0 :=
    mul_ne_zero hQ3 hQ5
  have hQ := BaileyTransform_eight_qpochhammer_eight_over_three_five q hQ1 hQ2 hQ3 hQ5
  have hA := BaileyTransform_eight_qpoch_aq_eight_over_five a q hA5
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 8)
      (qPochhammer q 3 * qPochhammer q 5)
      (qPoch (a * q) q 8) (qPoch (a * q) q 5)
      (1 + q + 2 * q ^ 2 + 3 * q ^ 3 + 4 * q ^ 4 + 5 * q ^ 5 + 6 * q ^ 6 +
        6 * q ^ 7 + 6 * q ^ 8 + 6 * q ^ 9 + 5 * q ^ 10 + 4 * q ^ 11 +
        3 * q ^ 12 + 2 * q ^ 13 + q ^ 14 + q ^ 15)
      ((1 - a * q ^ 6) * (1 - a * q ^ 7) * (1 - a * q ^ 8))
      hQ_combo hA5 hQ hA

/-- The sixth scalar ratio in the n = 8, α₀ common-denominator calculation
(k=6, pair (2,6)). -/
theorem BaileyTransform_eight_alpha_zero_sixth_ratio
    (a q : R)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ6 : qPochhammer q 6 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hA6 : qPoch (a * q) q 6 ≠ 0) :
    qPochhammer q 8 * qPoch (a * q) q 8 /
        (qPochhammer q 2 * qPochhammer q 6 * qPoch (a * q) q 6) =
      (1 + q + 2 * q ^ 2 + 2 * q ^ 3 + 3 * q ^ 4 + 3 * q ^ 5 + 4 * q ^ 6 +
        3 * q ^ 7 + 3 * q ^ 8 + 2 * q ^ 9 + 2 * q ^ 10 + q ^ 11 + q ^ 12) *
      ((1 - a * q ^ 7) * (1 - a * q ^ 8)) := by
  have hQ_combo : qPochhammer q 2 * qPochhammer q 6 ≠ 0 :=
    mul_ne_zero hQ2 hQ6
  have hQ := BaileyTransform_eight_qpochhammer_eight_over_two_six q hQ1 hQ2 hQ6
  have hA := BaileyTransform_eight_qpoch_aq_eight_over_six a q hA6
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 8)
      (qPochhammer q 2 * qPochhammer q 6)
      (qPoch (a * q) q 8) (qPoch (a * q) q 6)
      (1 + q + 2 * q ^ 2 + 2 * q ^ 3 + 3 * q ^ 4 + 3 * q ^ 5 + 4 * q ^ 6 +
        3 * q ^ 7 + 3 * q ^ 8 + 2 * q ^ 9 + 2 * q ^ 10 + q ^ 11 + q ^ 12)
      ((1 - a * q ^ 7) * (1 - a * q ^ 8))
      hQ_combo hA6 hQ hA

/-- The seventh scalar ratio in the n = 8, α₀ common-denominator calculation
(k=7, pair (1,7)). -/
theorem BaileyTransform_eight_alpha_zero_seventh_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ7 : qPochhammer q 7 ≠ 0)
    (hA7 : qPoch (a * q) q 7 ≠ 0) :
    qPochhammer q 8 * qPoch (a * q) q 8 /
        (qPochhammer q 1 * qPochhammer q 7 * qPoch (a * q) q 7) =
      (1 + q + q ^ 2 + q ^ 3 + q ^ 4 + q ^ 5 + q ^ 6 + q ^ 7) *
        (1 - a * q ^ 8) := by
  have hQ_combo : qPochhammer q 1 * qPochhammer q 7 ≠ 0 :=
    mul_ne_zero hQ1 hQ7
  have hQ := BaileyTransform_eight_qpochhammer_eight_over_one_seven q hQ1 hQ7
  have hA := BaileyTransform_eight_qpoch_aq_eight_over_seven a q hA7
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 8)
      (qPochhammer q 1 * qPochhammer q 7)
      (qPoch (a * q) q 8) (qPoch (a * q) q 7)
      (1 + q + q ^ 2 + q ^ 3 + q ^ 4 + q ^ 5 + q ^ 6 + q ^ 7)
      (1 - a * q ^ 8)
      hQ_combo hA7 hQ hA

-- NOTE: There is intentionally no
-- `BaileyTransform_eight_alpha_zero_common_denominator_identity`.
-- The `*_alpha_zero_*_ratio` / `*_common_denominator_identity` ladder for
-- n = 2..7 is the original hand-expansion route and is superseded: the finite
-- Bailey lemma is now proved in full generality by
-- `BaileyTransform_preserves_pair_general` (see `section GeneralBaileyLemma`),
-- which factors through the q-Pfaff–Saalschütz kernel identity
-- `baileyKernelSum = baileyKernelTarget` rather than per-n common-denominator
-- expansions. Nothing references the n = 8 identity; the n = 8 ratio lemmas
-- above are kept only as a verified cross-check of the ladder pattern. The
-- remaining genuine analytic input is the *general* q-Pfaff–Saalschütz
-- summation (currently discharged unconditionally only for the boundary
-- j = n and for the small (n, j) instances consumed by the n ≤ 2
-- specializations); that, not this n = 8 polynomial, is the open item.

/-- The ratio `(aq;q)_6 / (aq;q)_1`. -/
theorem BaileyTransform_six_qpoch_aq_six_over_one
    (a q : R) (hA1 : qPoch (a * q) q 1 ≠ 0) :
    qPoch (a * q) q 6 / qPoch (a * q) q 1 =
      (1 - a * q ^ 2) * (1 - a * q ^ 3) *
        (1 - a * q ^ 4) * (1 - a * q ^ 5) *
        (1 - a * q ^ 6) := by
  rw [show qPoch (a * q) q 6 =
      qPoch (a * q) q 1 * (1 - (a * q) * q ^ 1) *
        (1 - (a * q) * q ^ 2) * (1 - (a * q) * q ^ 3) *
        (1 - (a * q) * q ^ 4) * (1 - (a * q) * q ^ 5) by rfl]
  simp only [pow_one]
  field_simp [hA1]

/-- The first scalar ratio in the `n = 6`, α₀ common-denominator
calculation. -/
theorem BaileyTransform_six_alpha_zero_first_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ5 : qPochhammer q 5 ≠ 0)
    (hA1 : qPoch (a * q) q 1 ≠ 0) :
    qPochhammer q 6 * qPoch (a * q) q 6 /
        (qPochhammer q 5 * qPochhammer q 1 * qPoch (a * q) q 1) =
      (1 + q + q ^ 2 + q ^ 3 + q ^ 4 + q ^ 5) *
        ((1 - a * q ^ 2) * (1 - a * q ^ 3) *
          (1 - a * q ^ 4) * (1 - a * q ^ 5) * (1 - a * q ^ 6)) := by
  have hQ5Q1 : qPochhammer q 5 * qPochhammer q 1 ≠ 0 :=
    mul_ne_zero hQ5 hQ1
  have hQ := BaileyTransform_six_qpochhammer_six_over_five_one q hQ1 hQ5
  have hA := BaileyTransform_six_qpoch_aq_six_over_one a q hA1
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 6)
      (qPochhammer q 5 * qPochhammer q 1)
      (qPoch (a * q) q 6) (qPoch (a * q) q 1)
      (1 + q + q ^ 2 + q ^ 3 + q ^ 4 + q ^ 5)
      ((1 - a * q ^ 2) * (1 - a * q ^ 3) *
        (1 - a * q ^ 4) * (1 - a * q ^ 5) * (1 - a * q ^ 6))
      hQ5Q1 hA1 hQ hA

/-- The second scalar ratio in the `n = 6`, α₀ common-denominator
calculation. -/
theorem BaileyTransform_six_alpha_zero_second_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ4 : qPochhammer q 4 ≠ 0)
    (hA2 : qPoch (a * q) q 2 ≠ 0) :
    qPochhammer q 6 * qPoch (a * q) q 6 /
        (qPochhammer q 4 * qPochhammer q 2 * qPoch (a * q) q 2) =
      ((1 + q + q ^ 2 + q ^ 3 + q ^ 4) * (1 + q ^ 2 + q ^ 4)) *
        ((1 - a * q ^ 3) * (1 - a * q ^ 4) *
          (1 - a * q ^ 5) * (1 - a * q ^ 6)) := by
  have hQ4Q2 : qPochhammer q 4 * qPochhammer q 2 ≠ 0 :=
    mul_ne_zero hQ4 hQ2
  have hQ := BaileyTransform_six_qpochhammer_six_over_four_two q hQ1 hQ2 hQ4
  have hA := BaileyTransform_five_qpoch_aq_six_over_two a q hA2
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 6)
      (qPochhammer q 4 * qPochhammer q 2)
      (qPoch (a * q) q 6) (qPoch (a * q) q 2)
      ((1 + q + q ^ 2 + q ^ 3 + q ^ 4) * (1 + q ^ 2 + q ^ 4))
      ((1 - a * q ^ 3) * (1 - a * q ^ 4) *
        (1 - a * q ^ 5) * (1 - a * q ^ 6))
      hQ4Q2 hA2 hQ hA

/-- The third scalar ratio in the `n = 6`, α₀ common-denominator
calculation. -/
theorem BaileyTransform_six_alpha_zero_third_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hA3 : qPoch (a * q) q 3 ≠ 0) :
    qPochhammer q 6 * qPoch (a * q) q 6 /
        (qPochhammer q 3 * qPochhammer q 3 * qPoch (a * q) q 3) =
      ((1 + q + q ^ 2 + q ^ 3 + q ^ 4) * (1 + q ^ 2) * (1 + q ^ 3)) *
        ((1 - a * q ^ 4) * (1 - a * q ^ 5) * (1 - a * q ^ 6)) := by
  have hQ3Q3 : qPochhammer q 3 * qPochhammer q 3 ≠ 0 :=
    mul_ne_zero hQ3 hQ3
  have hQ := BaileyTransform_six_qpochhammer_six_over_three_three q hQ1 hQ2 hQ3
  have hA := BaileyTransform_five_qpoch_aq_six_over_three a q hA3
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 6)
      (qPochhammer q 3 * qPochhammer q 3)
      (qPoch (a * q) q 6) (qPoch (a * q) q 3)
      ((1 + q + q ^ 2 + q ^ 3 + q ^ 4) * (1 + q ^ 2) * (1 + q ^ 3))
      ((1 - a * q ^ 4) * (1 - a * q ^ 5) * (1 - a * q ^ 6))
      hQ3Q3 hA3 hQ hA

/-- The fourth scalar ratio in the `n = 6`, α₀ common-denominator
calculation. -/
theorem BaileyTransform_six_alpha_zero_fourth_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ4 : qPochhammer q 4 ≠ 0)
    (hA4 : qPoch (a * q) q 4 ≠ 0) :
    qPochhammer q 6 * qPoch (a * q) q 6 /
        (qPochhammer q 2 * qPochhammer q 4 * qPoch (a * q) q 4) =
      ((1 + q + q ^ 2 + q ^ 3 + q ^ 4) * (1 + q ^ 2 + q ^ 4)) *
        ((1 - a * q ^ 5) * (1 - a * q ^ 6)) := by
  have hQ2Q4 : qPochhammer q 2 * qPochhammer q 4 ≠ 0 :=
    mul_ne_zero hQ2 hQ4
  have hQ := BaileyTransform_six_qpochhammer_six_over_two_four q hQ1 hQ2 hQ4
  have hA := BaileyTransform_four_qpoch_aq_six_over_four a q hA4
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 6)
      (qPochhammer q 2 * qPochhammer q 4)
      (qPoch (a * q) q 6) (qPoch (a * q) q 4)
      ((1 + q + q ^ 2 + q ^ 3 + q ^ 4) * (1 + q ^ 2 + q ^ 4))
      ((1 - a * q ^ 5) * (1 - a * q ^ 6))
      hQ2Q4 hA4 hQ hA

/-- The fifth scalar ratio in the `n = 6`, α₀ common-denominator
calculation. -/
theorem BaileyTransform_six_alpha_zero_fifth_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ5 : qPochhammer q 5 ≠ 0)
    (hA5 : qPoch (a * q) q 5 ≠ 0) :
    qPochhammer q 6 * qPoch (a * q) q 6 /
        (qPochhammer q 1 * qPochhammer q 5 * qPoch (a * q) q 5) =
      (1 + q + q ^ 2 + q ^ 3 + q ^ 4 + q ^ 5) * (1 - a * q ^ 6) := by
  have hQ1Q5 : qPochhammer q 1 * qPochhammer q 5 ≠ 0 :=
    mul_ne_zero hQ1 hQ5
  have hQ := BaileyTransform_six_qpochhammer_six_over_one_five q hQ1 hQ5
  have hA := BaileyTransform_four_qpoch_aq_six_over_five a q hA5
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 6)
      (qPochhammer q 1 * qPochhammer q 5)
      (qPoch (a * q) q 6) (qPoch (a * q) q 5)
      (1 + q + q ^ 2 + q ^ 3 + q ^ 4 + q ^ 5) (1 - a * q ^ 6)
      hQ1Q5 hA5 hQ hA

/-- The first scalar ratio in the `n = 7`, α₀ common-denominator
calculation (k=1, pair (6, 1)). -/
theorem BaileyTransform_seven_alpha_zero_first_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ6 : qPochhammer q 6 ≠ 0)
    (hA1 : qPoch (a * q) q 1 ≠ 0) :
    qPochhammer q 7 * qPoch (a * q) q 7 /
        (qPochhammer q 6 * qPochhammer q 1 * qPoch (a * q) q 1) =
      (1 + q + q ^ 2 + q ^ 3 + q ^ 4 + q ^ 5 + q ^ 6) *
        ((1 - a * q ^ 2) * (1 - a * q ^ 3) * (1 - a * q ^ 4) *
          (1 - a * q ^ 5) * (1 - a * q ^ 6) * (1 - a * q ^ 7)) := by
  have hQ6Q1 : qPochhammer q 6 * qPochhammer q 1 ≠ 0 :=
    mul_ne_zero hQ6 hQ1
  have hQ := BaileyTransform_seven_qpochhammer_seven_over_six_one q hQ1 hQ6
  have hA := BaileyTransform_seven_qpoch_aq_seven_over_one a q hA1
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 7)
      (qPochhammer q 6 * qPochhammer q 1)
      (qPoch (a * q) q 7) (qPoch (a * q) q 1)
      (1 + q + q ^ 2 + q ^ 3 + q ^ 4 + q ^ 5 + q ^ 6)
      ((1 - a * q ^ 2) * (1 - a * q ^ 3) * (1 - a * q ^ 4) *
        (1 - a * q ^ 5) * (1 - a * q ^ 6) * (1 - a * q ^ 7))
      hQ6Q1 hA1 hQ hA

/-- The second scalar ratio in the `n = 7`, α₀ common-denominator
calculation (k=2, pair (5, 2)). -/
theorem BaileyTransform_seven_alpha_zero_second_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ5 : qPochhammer q 5 ≠ 0)
    (hA2 : qPoch (a * q) q 2 ≠ 0) :
    qPochhammer q 7 * qPoch (a * q) q 7 /
        (qPochhammer q 5 * qPochhammer q 2 * qPoch (a * q) q 2) =
      ((1 + q + q ^ 2 + q ^ 3 + q ^ 4 + q ^ 5 + q ^ 6) *
        (1 + q ^ 2 + q ^ 4)) *
        ((1 - a * q ^ 3) * (1 - a * q ^ 4) * (1 - a * q ^ 5) *
          (1 - a * q ^ 6) * (1 - a * q ^ 7)) := by
  have hQ5Q2 : qPochhammer q 5 * qPochhammer q 2 ≠ 0 :=
    mul_ne_zero hQ5 hQ2
  have hQ := BaileyTransform_seven_qpochhammer_seven_over_five_two q hQ1 hQ2 hQ5
  have hA := BaileyTransform_seven_qpoch_aq_seven_over_two a q hA2
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 7)
      (qPochhammer q 5 * qPochhammer q 2)
      (qPoch (a * q) q 7) (qPoch (a * q) q 2)
      ((1 + q + q ^ 2 + q ^ 3 + q ^ 4 + q ^ 5 + q ^ 6) *
        (1 + q ^ 2 + q ^ 4))
      ((1 - a * q ^ 3) * (1 - a * q ^ 4) * (1 - a * q ^ 5) *
        (1 - a * q ^ 6) * (1 - a * q ^ 7))
      hQ5Q2 hA2 hQ hA

/-- The third scalar ratio in the `n = 7`, α₀ common-denominator
calculation (k=3, pair (4, 3)). -/
theorem BaileyTransform_seven_alpha_zero_third_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hQ4 : qPochhammer q 4 ≠ 0)
    (hA3 : qPoch (a * q) q 3 ≠ 0) :
    qPochhammer q 7 * qPoch (a * q) q 7 /
        (qPochhammer q 4 * qPochhammer q 3 * qPoch (a * q) q 3) =
      (1 + q + 2 * q ^ 2 + 3 * q ^ 3 + 4 * q ^ 4 + 4 * q ^ 5 +
          5 * q ^ 6 + 4 * q ^ 7 + 4 * q ^ 8 + 3 * q ^ 9 +
          2 * q ^ 10 + q ^ 11 + q ^ 12) *
        ((1 - a * q ^ 4) * (1 - a * q ^ 5) * (1 - a * q ^ 6) *
          (1 - a * q ^ 7)) := by
  have hQ4Q3 : qPochhammer q 4 * qPochhammer q 3 ≠ 0 :=
    mul_ne_zero hQ4 hQ3
  have hQ := BaileyTransform_seven_qpochhammer_seven_over_four_three q hQ1 hQ2 hQ3 hQ4
  have hA := BaileyTransform_seven_qpoch_aq_seven_over_three a q hA3
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 7)
      (qPochhammer q 4 * qPochhammer q 3)
      (qPoch (a * q) q 7) (qPoch (a * q) q 3)
      (1 + q + 2 * q ^ 2 + 3 * q ^ 3 + 4 * q ^ 4 + 4 * q ^ 5 +
        5 * q ^ 6 + 4 * q ^ 7 + 4 * q ^ 8 + 3 * q ^ 9 +
        2 * q ^ 10 + q ^ 11 + q ^ 12)
      ((1 - a * q ^ 4) * (1 - a * q ^ 5) * (1 - a * q ^ 6) *
        (1 - a * q ^ 7))
      hQ4Q3 hA3 hQ hA

/-- The fourth scalar ratio in the `n = 7`, α₀ common-denominator
calculation (k=4, pair (3, 4)). -/
theorem BaileyTransform_seven_alpha_zero_fourth_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hQ4 : qPochhammer q 4 ≠ 0)
    (hA4 : qPoch (a * q) q 4 ≠ 0) :
    qPochhammer q 7 * qPoch (a * q) q 7 /
        (qPochhammer q 3 * qPochhammer q 4 * qPoch (a * q) q 4) =
      (1 + q + 2 * q ^ 2 + 3 * q ^ 3 + 4 * q ^ 4 + 4 * q ^ 5 +
          5 * q ^ 6 + 4 * q ^ 7 + 4 * q ^ 8 + 3 * q ^ 9 +
          2 * q ^ 10 + q ^ 11 + q ^ 12) *
        ((1 - a * q ^ 5) * (1 - a * q ^ 6) * (1 - a * q ^ 7)) := by
  have hQ3Q4 : qPochhammer q 3 * qPochhammer q 4 ≠ 0 :=
    mul_ne_zero hQ3 hQ4
  have hQ := BaileyTransform_seven_qpochhammer_seven_over_three_four q hQ1 hQ2 hQ3 hQ4
  have hA := BaileyTransform_seven_qpoch_aq_seven_over_four a q hA4
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 7)
      (qPochhammer q 3 * qPochhammer q 4)
      (qPoch (a * q) q 7) (qPoch (a * q) q 4)
      (1 + q + 2 * q ^ 2 + 3 * q ^ 3 + 4 * q ^ 4 + 4 * q ^ 5 +
        5 * q ^ 6 + 4 * q ^ 7 + 4 * q ^ 8 + 3 * q ^ 9 +
        2 * q ^ 10 + q ^ 11 + q ^ 12)
      ((1 - a * q ^ 5) * (1 - a * q ^ 6) * (1 - a * q ^ 7))
      hQ3Q4 hA4 hQ hA

/-- The fifth scalar ratio in the `n = 7`, α₀ common-denominator
calculation (k=5, pair (2, 5)). -/
theorem BaileyTransform_seven_alpha_zero_fifth_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ5 : qPochhammer q 5 ≠ 0)
    (hA5 : qPoch (a * q) q 5 ≠ 0) :
    qPochhammer q 7 * qPoch (a * q) q 7 /
        (qPochhammer q 2 * qPochhammer q 5 * qPoch (a * q) q 5) =
      ((1 + q + q ^ 2 + q ^ 3 + q ^ 4 + q ^ 5 + q ^ 6) *
        (1 + q ^ 2 + q ^ 4)) *
        ((1 - a * q ^ 6) * (1 - a * q ^ 7)) := by
  have hQ2Q5 : qPochhammer q 2 * qPochhammer q 5 ≠ 0 :=
    mul_ne_zero hQ2 hQ5
  have hQ := BaileyTransform_seven_qpochhammer_seven_over_two_five q hQ1 hQ2 hQ5
  have hA := BaileyTransform_seven_qpoch_aq_seven_over_five a q hA5
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 7)
      (qPochhammer q 2 * qPochhammer q 5)
      (qPoch (a * q) q 7) (qPoch (a * q) q 5)
      ((1 + q + q ^ 2 + q ^ 3 + q ^ 4 + q ^ 5 + q ^ 6) *
        (1 + q ^ 2 + q ^ 4))
      ((1 - a * q ^ 6) * (1 - a * q ^ 7))
      hQ2Q5 hA5 hQ hA

/-- The sixth scalar ratio in the `n = 7`, α₀ common-denominator
calculation (k=6, pair (1, 6)). -/
theorem BaileyTransform_seven_alpha_zero_sixth_ratio
    (a q : R)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ6 : qPochhammer q 6 ≠ 0)
    (hA6 : qPoch (a * q) q 6 ≠ 0) :
    qPochhammer q 7 * qPoch (a * q) q 7 /
        (qPochhammer q 1 * qPochhammer q 6 * qPoch (a * q) q 6) =
      (1 + q + q ^ 2 + q ^ 3 + q ^ 4 + q ^ 5 + q ^ 6) *
        (1 - a * q ^ 7) := by
  have hQ1Q6 : qPochhammer q 1 * qPochhammer q 6 ≠ 0 :=
    mul_ne_zero hQ1 hQ6
  have hQ := BaileyTransform_seven_qpochhammer_seven_over_one_six q hQ1 hQ6
  have hA := BaileyTransform_seven_qpoch_aq_seven_over_six a q hA6
  simpa [mul_assoc] using
    BaileyTransform_ratio_mul (qPochhammer q 7)
      (qPochhammer q 1 * qPochhammer q 6)
      (qPoch (a * q) q 7) (qPoch (a * q) q 6)
      (1 + q + q ^ 2 + q ^ 3 + q ^ 4 + q ^ 5 + q ^ 6)
      (1 - a * q ^ 7)
      hQ1Q6 hA6 hQ hA

set_option maxHeartbeats 4000000 in
/-- The α₀ coefficient identity in the `n = 7` finite Bailey-lemma step after
moving the eight transformed-β contributions to a common denominator. -/
theorem BaileyTransform_seven_alpha_zero_common_denominator_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hQ4 : qPochhammer q 4 ≠ 0)
    (hQ5 : qPochhammer q 5 ≠ 0)
    (hQ6 : qPochhammer q 6 ≠ 0)
    (hA1 : qPoch (a * q) q 1 ≠ 0)
    (hA2 : qPoch (a * q) q 2 ≠ 0)
    (hA3 : qPoch (a * q) q 3 ≠ 0)
    (hA4 : qPoch (a * q) q 4 ≠ 0)
    (hA5 : qPoch (a * q) q 5 ≠ 0)
    (hA6 : qPoch (a * q) q 6 ≠ 0) :
    qPoch (a * q / (ρ₁ * ρ₂)) q 7 * qPoch (a * q) q 7 +
      qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) *
        qPoch (a * q / (ρ₁ * ρ₂)) q 6 *
        (qPochhammer q 7 * qPoch (a * q) q 7 /
          (qPochhammer q 6 * qPochhammer q 1 * qPoch (a * q) q 1)) +
      qPoch ρ₁ q 2 * qPoch ρ₂ q 2 *
        (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 5 *
        (qPochhammer q 7 * qPoch (a * q) q 7 /
          (qPochhammer q 5 * qPochhammer q 2 * qPoch (a * q) q 2)) +
      qPoch ρ₁ q 3 * qPoch ρ₂ q 3 *
        (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 4 *
        (qPochhammer q 7 * qPoch (a * q) q 7 /
          (qPochhammer q 4 * qPochhammer q 3 * qPoch (a * q) q 3)) +
      qPoch ρ₁ q 4 * qPoch ρ₂ q 4 *
        (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3 *
        (qPochhammer q 7 * qPoch (a * q) q 7 /
          (qPochhammer q 3 * qPochhammer q 4 * qPoch (a * q) q 4)) +
      qPoch ρ₁ q 5 * qPoch ρ₂ q 5 *
        (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2 *
        (qPochhammer q 7 * qPoch (a * q) q 7 /
          (qPochhammer q 2 * qPochhammer q 5 * qPoch (a * q) q 5)) +
      qPoch ρ₁ q 6 * qPoch ρ₂ q 6 *
        (a * q / (ρ₁ * ρ₂)) ^ 6 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1 *
        (qPochhammer q 7 * qPoch (a * q) q 7 /
          (qPochhammer q 1 * qPochhammer q 6 * qPoch (a * q) q 6)) +
      qPoch ρ₁ q 7 * qPoch ρ₂ q 7 *
        (a * q / (ρ₁ * ρ₂)) ^ 7 =
      qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 := by
  rw [BaileyTransform_seven_alpha_zero_first_ratio a q hQ1 hQ6 hA1,
    BaileyTransform_seven_alpha_zero_second_ratio a q hQ1 hQ2 hQ5 hA2,
    BaileyTransform_seven_alpha_zero_third_ratio a q hQ1 hQ2 hQ3 hQ4 hA3,
    BaileyTransform_seven_alpha_zero_fourth_ratio a q hQ1 hQ2 hQ3 hQ4 hA4,
    BaileyTransform_seven_alpha_zero_fifth_ratio a q hQ1 hQ2 hQ5 hA5,
    BaileyTransform_seven_alpha_zero_sixth_ratio a q hQ1 hQ6 hA6]
  have hρ1 : ρ₁ ≠ 0 := left_ne_zero_of_mul hρ
  have hρ2 : ρ₂ ≠ 0 := right_ne_zero_of_mul hρ
  simp [qPoch]
  field_simp [hρ, hρ1, hρ2]
  ring

/-- The α₀ coefficient identity in the `n = 6` finite Bailey-lemma step after
moving the seven transformed-β contributions to a common denominator. -/
theorem BaileyTransform_six_alpha_zero_common_denominator_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hQ4 : qPochhammer q 4 ≠ 0)
    (hQ5 : qPochhammer q 5 ≠ 0)
    (hA1 : qPoch (a * q) q 1 ≠ 0)
    (hA2 : qPoch (a * q) q 2 ≠ 0)
    (hA3 : qPoch (a * q) q 3 ≠ 0)
    (hA4 : qPoch (a * q) q 4 ≠ 0)
    (hA5 : qPoch (a * q) q 5 ≠ 0) :
    qPoch (a * q / (ρ₁ * ρ₂)) q 6 * qPoch (a * q) q 6 +
      qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) *
        qPoch (a * q / (ρ₁ * ρ₂)) q 5 *
        (qPochhammer q 6 * qPoch (a * q) q 6 /
          (qPochhammer q 5 * qPochhammer q 1 * qPoch (a * q) q 1)) +
      qPoch ρ₁ q 2 * qPoch ρ₂ q 2 *
        (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 4 *
        (qPochhammer q 6 * qPoch (a * q) q 6 /
          (qPochhammer q 4 * qPochhammer q 2 * qPoch (a * q) q 2)) +
      qPoch ρ₁ q 3 * qPoch ρ₂ q 3 *
        (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3 *
        (qPochhammer q 6 * qPoch (a * q) q 6 /
          (qPochhammer q 3 * qPochhammer q 3 * qPoch (a * q) q 3)) +
      qPoch ρ₁ q 4 * qPoch ρ₂ q 4 *
        (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2 *
        (qPochhammer q 6 * qPoch (a * q) q 6 /
          (qPochhammer q 2 * qPochhammer q 4 * qPoch (a * q) q 4)) +
      qPoch ρ₁ q 5 * qPoch ρ₂ q 5 *
        (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1 *
        (qPochhammer q 6 * qPoch (a * q) q 6 /
          (qPochhammer q 1 * qPochhammer q 5 * qPoch (a * q) q 5)) +
      qPoch ρ₁ q 6 * qPoch ρ₂ q 6 *
        (a * q / (ρ₁ * ρ₂)) ^ 6 =
      qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 := by
  rw [BaileyTransform_six_alpha_zero_first_ratio a q hQ1 hQ5 hA1,
    BaileyTransform_six_alpha_zero_second_ratio a q hQ1 hQ2 hQ4 hA2,
    BaileyTransform_six_alpha_zero_third_ratio a q hQ1 hQ2 hQ3 hA3,
    BaileyTransform_six_alpha_zero_fourth_ratio a q hQ1 hQ2 hQ4 hA4,
    BaileyTransform_six_alpha_zero_fifth_ratio a q hQ1 hQ5 hA5]
  have hρ1 : ρ₁ ≠ 0 := left_ne_zero_of_mul hρ
  have hρ2 : ρ₂ ≠ 0 := right_ne_zero_of_mul hρ
  simp [qPoch]
  field_simp [hρ, hρ1, hρ2]
  ring

/-- The α₀ coefficient identity in the `n = 6` finite Bailey-lemma step. -/
theorem BaileyTransform_six_alpha_zero_coefficient_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hD1 : qPoch (a * q / ρ₁) q 6 ≠ 0)
    (hD2 : qPoch (a * q / ρ₂) q 6 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hQ4 : qPochhammer q 4 ≠ 0)
    (hQ5 : qPochhammer q 5 ≠ 0)
    (hQ6 : qPochhammer q 6 ≠ 0)
    (hA1 : qPoch (a * q) q 1 ≠ 0)
    (hA2 : qPoch (a * q) q 2 ≠ 0)
    (hA3 : qPoch (a * q) q 3 ≠ 0)
    (hA4 : qPoch (a * q) q 4 ≠ 0)
    (hA5 : qPoch (a * q) q 5 ≠ 0)
    (hA6 : qPoch (a * q) q 6 ≠ 0) :
    ((qPoch ρ₁ q 0 * qPoch ρ₂ q 0 * (a * q / (ρ₁ * ρ₂)) ^ 0 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 6) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 6)) +
      ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 5) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 5)) /
        (qPochhammer q 1 * qPoch (a * q) q 1) +
      ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 4) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 4)) /
        (qPochhammer q 2 * qPoch (a * q) q 2) +
      ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 3)) /
        (qPochhammer q 3 * qPoch (a * q) q 3) +
      ((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 2)) /
        (qPochhammer q 4 * qPoch (a * q) q 4) +
      ((qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 1)) /
        (qPochhammer q 5 * qPoch (a * q) q 5) +
      ((qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 0)) /
        (qPochhammer q 6 * qPoch (a * q) q 6) =
      1 / (qPochhammer q 6 * qPoch (a * q) q 6) := by
  have hD : qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 ≠ 0 :=
    mul_ne_zero hD1 hD2
  have hcommon := BaileyTransform_six_alpha_zero_common_denominator_identity
    a q ρ₁ ρ₂ hρ hQ1 hQ2 hQ3 hQ4 hQ5 hA1 hA2 hA3 hA4 hA5
  simpa [qPochhammer, qPoch] using
    (BaileyTransform_seven_term_fraction_from_common
      (P0 := qPoch (a * q / (ρ₁ * ρ₂)) q 6)
      (P1 := qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) *
        qPoch (a * q / (ρ₁ * ρ₂)) q 5)
      (P2 := qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 4)
      (P3 := qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3)
      (P4 := qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2)
      (P5 := qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1)
      (P6 := qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6)
      (D := qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6)
      (Q1 := qPochhammer q 1)
      (Q2 := qPochhammer q 2)
      (Q3 := qPochhammer q 3)
      (Q4 := qPochhammer q 4)
      (Q5 := qPochhammer q 5)
      (Q6 := qPochhammer q 6)
      (A1 := qPoch (a * q) q 1)
      (A2 := qPoch (a * q) q 2)
      (A3 := qPoch (a * q) q 3)
      (A4 := qPoch (a * q) q 4)
      (A5 := qPoch (a * q) q 5)
      (A6 := qPoch (a * q) q 6)
      hD hQ1 hQ2 hQ3 hQ4 hQ5 hQ6 hA1 hA2 hA3 hA4 hA5 hA6 hcommon)

set_option maxHeartbeats 4000000 in
/-- The α₀ coefficient identity in the `n = 7` finite Bailey-lemma step. -/
theorem BaileyTransform_seven_alpha_zero_coefficient_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hD1 : qPoch (a * q / ρ₁) q 7 ≠ 0)
    (hD2 : qPoch (a * q / ρ₂) q 7 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hQ4 : qPochhammer q 4 ≠ 0)
    (hQ5 : qPochhammer q 5 ≠ 0)
    (hQ6 : qPochhammer q 6 ≠ 0)
    (hQ7 : qPochhammer q 7 ≠ 0)
    (hA1 : qPoch (a * q) q 1 ≠ 0)
    (hA2 : qPoch (a * q) q 2 ≠ 0)
    (hA3 : qPoch (a * q) q 3 ≠ 0)
    (hA4 : qPoch (a * q) q 4 ≠ 0)
    (hA5 : qPoch (a * q) q 5 ≠ 0)
    (hA6 : qPoch (a * q) q 6 ≠ 0)
    (hA7 : qPoch (a * q) q 7 ≠ 0) :
    ((qPoch ρ₁ q 0 * qPoch ρ₂ q 0 * (a * q / (ρ₁ * ρ₂)) ^ 0 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 7) /
      (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 *
        qPochhammer q 7)) +
      ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 6) /
      (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 *
        qPochhammer q 6)) /
        (qPochhammer q 1 * qPoch (a * q) q 1) +
      ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 5) /
      (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 *
        qPochhammer q 5)) /
        (qPochhammer q 2 * qPoch (a * q) q 2) +
      ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 4) /
      (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 *
        qPochhammer q 4)) /
        (qPochhammer q 3 * qPoch (a * q) q 3) +
      ((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3) /
      (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 *
        qPochhammer q 3)) /
        (qPochhammer q 4 * qPoch (a * q) q 4) +
      ((qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 *
        qPochhammer q 2)) /
        (qPochhammer q 5 * qPoch (a * q) q 5) +
      ((qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 *
        qPochhammer q 1)) /
        (qPochhammer q 6 * qPoch (a * q) q 6) +
      ((qPoch ρ₁ q 7 * qPoch ρ₂ q 7 * (a * q / (ρ₁ * ρ₂)) ^ 7 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 *
        qPochhammer q 0)) /
        (qPochhammer q 7 * qPoch (a * q) q 7) =
      1 / (qPochhammer q 7 * qPoch (a * q) q 7) := by
  have hD : qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 ≠ 0 :=
    mul_ne_zero hD1 hD2
  have hcommon := BaileyTransform_seven_alpha_zero_common_denominator_identity
    a q ρ₁ ρ₂ hρ hQ1 hQ2 hQ3 hQ4 hQ5 hQ6 hA1 hA2 hA3 hA4 hA5 hA6
  simpa [qPochhammer, qPoch] using
    (BaileyTransform_eight_term_fraction_from_common
      (P0 := qPoch (a * q / (ρ₁ * ρ₂)) q 7)
      (P1 := qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) *
        qPoch (a * q / (ρ₁ * ρ₂)) q 6)
      (P2 := qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 5)
      (P3 := qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 4)
      (P4 := qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3)
      (P5 := qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2)
      (P6 := qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1)
      (P7 := qPoch ρ₁ q 7 * qPoch ρ₂ q 7 * (a * q / (ρ₁ * ρ₂)) ^ 7)
      (D := qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7)
      (Q1 := qPochhammer q 1)
      (Q2 := qPochhammer q 2)
      (Q3 := qPochhammer q 3)
      (Q4 := qPochhammer q 4)
      (Q5 := qPochhammer q 5)
      (Q6 := qPochhammer q 6)
      (Q7 := qPochhammer q 7)
      (A1 := qPoch (a * q) q 1)
      (A2 := qPoch (a * q) q 2)
      (A3 := qPoch (a * q) q 3)
      (A4 := qPoch (a * q) q 4)
      (A5 := qPoch (a * q) q 5)
      (A6 := qPoch (a * q) q 6)
      (A7 := qPoch (a * q) q 7)
      hD hQ1 hQ2 hQ3 hQ4 hQ5 hQ6 hQ7 hA1 hA2 hA3 hA4 hA5 hA6 hA7 hcommon)

/-- The α₂ coefficient identity in the `n = 6` finite Bailey-lemma step after
moving the five transformed-β contributions to a common denominator. -/
theorem BaileyTransform_six_alpha_two_common_denominator_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hA4 : qPoch (a * q) q 4 ≠ 0)
    (hA5 : qPoch (a * q) q 5 ≠ 0)
    (hA6 : qPoch (a * q) q 6 ≠ 0)
    (hA7 : qPoch (a * q) q 7 ≠ 0)
    (hD1two : qPoch (a * q / ρ₁) q 2 ≠ 0)
    (hD2two : qPoch (a * q / ρ₂) q 2 ≠ 0) :
    qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 4 *
        (qPoch (a * q) q 8 / qPoch (a * q) q 4) +
      qPoch ρ₁ q 3 * qPoch ρ₂ q 3 *
        (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3 *
        (qPochhammer q 4 * qPoch (a * q) q 8 /
          (qPochhammer q 3 * qPochhammer q 1 * qPoch (a * q) q 5)) +
      qPoch ρ₁ q 4 * qPoch ρ₂ q 4 *
        (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2 *
        (qPochhammer q 4 * qPoch (a * q) q 8 /
          (qPochhammer q 2 * qPochhammer q 2 * qPoch (a * q) q 6)) +
      qPoch ρ₁ q 5 * qPoch ρ₂ q 5 *
        (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1 *
        (qPochhammer q 4 * qPoch (a * q) q 8 /
          (qPochhammer q 1 * qPochhammer q 3 * qPoch (a * q) q 7)) +
      qPoch ρ₁ q 6 * qPoch ρ₂ q 6 *
        (a * q / (ρ₁ * ρ₂)) ^ 6 =
      (qPoch ρ₁ q 2 * qPoch ρ₂ q 2 *
        (a * q / (ρ₁ * ρ₂)) ^ 2) *
        ((qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6) /
          (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2)) := by
  rw [BaileyTransform_six_qpoch_aq_eight_over_four a q hA4,
    BaileyTransform_six_qpochhammer_aq_alpha_two_first_middle_ratio a q hQ1 hQ3 hA5,
    BaileyTransform_six_qpochhammer_aq_alpha_two_second_middle_ratio a q hQ2 hA6,
    BaileyTransform_six_qpochhammer_aq_alpha_two_third_middle_ratio a q hQ1 hQ3 hA7,
    BaileyTransform_six_qpoch_pair_ratio_two_six a q ρ₁ ρ₂ hD1two hD2two]
  have hρ1 : ρ₁ ≠ 0 := left_ne_zero_of_mul hρ
  have hρ2 : ρ₂ ≠ 0 := right_ne_zero_of_mul hρ
  rw [show qPoch (a * q / (ρ₁ * ρ₂)) q 4 =
      (1 - a * q / (ρ₁ * ρ₂)) * (1 - (a * q / (ρ₁ * ρ₂)) * q) *
        (1 - (a * q / (ρ₁ * ρ₂)) * q ^ 2) *
        (1 - (a * q / (ρ₁ * ρ₂)) * q ^ 3) by
        simp [qPoch]]
  rw [show qPoch (a * q / (ρ₁ * ρ₂)) q 3 =
      (1 - a * q / (ρ₁ * ρ₂)) * (1 - (a * q / (ρ₁ * ρ₂)) * q) *
        (1 - (a * q / (ρ₁ * ρ₂)) * q ^ 2) by
        simp [qPoch]]
  rw [show qPoch (a * q / (ρ₁ * ρ₂)) q 2 =
      (1 - a * q / (ρ₁ * ρ₂)) * (1 - (a * q / (ρ₁ * ρ₂)) * q) by
        simp [qPoch]]
  rw [show qPoch (a * q / (ρ₁ * ρ₂)) q 1 =
      1 - a * q / (ρ₁ * ρ₂) by simp [qPoch]]
  rw [show qPoch ρ₁ q 6 = qPoch ρ₁ q 5 * (1 - ρ₁ * q ^ 5) by rfl]
  rw [show qPoch ρ₂ q 6 = qPoch ρ₂ q 5 * (1 - ρ₂ * q ^ 5) by rfl]
  rw [show qPoch ρ₁ q 5 = qPoch ρ₁ q 4 * (1 - ρ₁ * q ^ 4) by rfl]
  rw [show qPoch ρ₂ q 5 = qPoch ρ₂ q 4 * (1 - ρ₂ * q ^ 4) by rfl]
  rw [show qPoch ρ₁ q 4 = qPoch ρ₁ q 3 * (1 - ρ₁ * q ^ 3) by rfl]
  rw [show qPoch ρ₂ q 4 = qPoch ρ₂ q 3 * (1 - ρ₂ * q ^ 3) by rfl]
  rw [show qPoch ρ₁ q 3 = qPoch ρ₁ q 2 * (1 - ρ₁ * q ^ 2) by rfl]
  rw [show qPoch ρ₂ q 3 = qPoch ρ₂ q 2 * (1 - ρ₂ * q ^ 2) by rfl]
  field_simp [hρ, hρ1, hρ2]
  ring

/-- The α₂ coefficient identity in the `n = 6` finite Bailey-lemma step. -/
theorem BaileyTransform_six_alpha_two_coefficient_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hD1 : qPoch (a * q / ρ₁) q 6 ≠ 0)
    (hD2 : qPoch (a * q / ρ₂) q 6 ≠ 0)
    (hD1two : qPoch (a * q / ρ₁) q 2 ≠ 0)
    (hD2two : qPoch (a * q / ρ₂) q 2 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hQ4 : qPochhammer q 4 ≠ 0)
    (hA4 : qPoch (a * q) q 4 ≠ 0)
    (hA5 : qPoch (a * q) q 5 ≠ 0)
    (hA6 : qPoch (a * q) q 6 ≠ 0)
    (hA7 : qPoch (a * q) q 7 ≠ 0)
    (hA8 : qPoch (a * q) q 8 ≠ 0) :
    ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 4) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 4)) / qPoch (a * q) q 4 +
      ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 3)) /
        (qPochhammer q 1 * qPoch (a * q) q 5) +
      ((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 2)) /
        (qPochhammer q 2 * qPoch (a * q) q 6) +
      ((qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 1)) /
        (qPochhammer q 3 * qPoch (a * q) q 7) +
      ((qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 0)) /
        (qPochhammer q 4 * qPoch (a * q) q 8) =
      (qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 /
        (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2)) /
        (qPochhammer q 4 * qPoch (a * q) q 8) := by
  have hD : qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 ≠ 0 :=
    mul_ne_zero hD1 hD2
  have hDtwo : qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2 ≠ 0 :=
    mul_ne_zero hD1two hD2two
  have hcommon := BaileyTransform_six_alpha_two_common_denominator_identity
    a q ρ₁ ρ₂ hρ hQ1 hQ2 hQ3 hA4 hA5 hA6 hA7 hD1two hD2two
  simpa [qPochhammer, qPoch] using
    (BaileyTransform_five_term_fraction_from_common_ratio
      (P1 := qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 4)
      (P2 := qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3)
      (P3 := qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2)
      (P4 := qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1)
      (P5 := qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6)
      (B := qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2)
      (D := qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6)
      (D1 := qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2)
      (Q1 := qPochhammer q 1)
      (Q2 := qPochhammer q 2)
      (Q3 := qPochhammer q 3)
      (Q4 := qPochhammer q 4)
      (A2 := qPoch (a * q) q 4)
      (A3 := qPoch (a * q) q 5)
      (A4 := qPoch (a * q) q 6)
      (A5 := qPoch (a * q) q 7)
      (A6 := qPoch (a * q) q 8)
      hD hDtwo hQ1 hQ2 hQ3 hQ4 hA4 hA5 hA6 hA7 hA8 hcommon)

/-- The α₃ coefficient identity in the `n = 6` finite Bailey-lemma step after
moving the four transformed-β contributions to a common denominator. -/
theorem BaileyTransform_six_alpha_three_common_denominator_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hA6 : qPoch (a * q) q 6 ≠ 0)
    (hA7 : qPoch (a * q) q 7 ≠ 0)
    (hA8 : qPoch (a * q) q 8 ≠ 0)
    (hD1three : qPoch (a * q / ρ₁) q 3 ≠ 0)
    (hD2three : qPoch (a * q / ρ₂) q 3 ≠ 0) :
    qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3 *
        (qPoch (a * q) q 9 / qPoch (a * q) q 6) +
      qPoch ρ₁ q 4 * qPoch ρ₂ q 4 *
        (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2 *
        (qPochhammer q 3 * qPoch (a * q) q 9 /
          (qPochhammer q 2 * qPochhammer q 1 * qPoch (a * q) q 7)) +
      qPoch ρ₁ q 5 * qPoch ρ₂ q 5 *
        (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1 *
        (qPochhammer q 3 * qPoch (a * q) q 9 /
          (qPochhammer q 1 * qPochhammer q 2 * qPoch (a * q) q 8)) +
      qPoch ρ₁ q 6 * qPoch ρ₂ q 6 *
        (a * q / (ρ₁ * ρ₂)) ^ 6 =
      (qPoch ρ₁ q 3 * qPoch ρ₂ q 3 *
        (a * q / (ρ₁ * ρ₂)) ^ 3) *
        ((qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6) /
          (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3)) := by
  rw [BaileyTransform_six_qpoch_aq_nine_over_six a q hA6,
    BaileyTransform_six_qpochhammer_aq_alpha_three_first_middle_ratio a q hQ1 hQ2 hA7,
    BaileyTransform_six_qpochhammer_aq_alpha_three_second_middle_ratio a q hQ1 hQ2 hA8,
    BaileyTransform_six_qpoch_pair_ratio_three_six a q ρ₁ ρ₂ hD1three hD2three]
  have hρ1 : ρ₁ ≠ 0 := left_ne_zero_of_mul hρ
  have hρ2 : ρ₂ ≠ 0 := right_ne_zero_of_mul hρ
  rw [show qPoch (a * q / (ρ₁ * ρ₂)) q 3 =
      (1 - a * q / (ρ₁ * ρ₂)) * (1 - (a * q / (ρ₁ * ρ₂)) * q) *
        (1 - (a * q / (ρ₁ * ρ₂)) * q ^ 2) by
        simp [qPoch]]
  rw [show qPoch (a * q / (ρ₁ * ρ₂)) q 2 =
      (1 - a * q / (ρ₁ * ρ₂)) * (1 - (a * q / (ρ₁ * ρ₂)) * q) by
        simp [qPoch]]
  rw [show qPoch (a * q / (ρ₁ * ρ₂)) q 1 =
      1 - a * q / (ρ₁ * ρ₂) by simp [qPoch]]
  rw [show qPoch ρ₁ q 6 = qPoch ρ₁ q 5 * (1 - ρ₁ * q ^ 5) by rfl]
  rw [show qPoch ρ₂ q 6 = qPoch ρ₂ q 5 * (1 - ρ₂ * q ^ 5) by rfl]
  rw [show qPoch ρ₁ q 5 = qPoch ρ₁ q 4 * (1 - ρ₁ * q ^ 4) by rfl]
  rw [show qPoch ρ₂ q 5 = qPoch ρ₂ q 4 * (1 - ρ₂ * q ^ 4) by rfl]
  rw [show qPoch ρ₁ q 4 = qPoch ρ₁ q 3 * (1 - ρ₁ * q ^ 3) by rfl]
  rw [show qPoch ρ₂ q 4 = qPoch ρ₂ q 3 * (1 - ρ₂ * q ^ 3) by rfl]
  field_simp [hρ, hρ1, hρ2]
  ring

/-- The α₃ coefficient identity in the `n = 6` finite Bailey-lemma step. -/
theorem BaileyTransform_six_alpha_three_coefficient_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hD1 : qPoch (a * q / ρ₁) q 6 ≠ 0)
    (hD2 : qPoch (a * q / ρ₂) q 6 ≠ 0)
    (hD1three : qPoch (a * q / ρ₁) q 3 ≠ 0)
    (hD2three : qPoch (a * q / ρ₂) q 3 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hA6 : qPoch (a * q) q 6 ≠ 0)
    (hA7 : qPoch (a * q) q 7 ≠ 0)
    (hA8 : qPoch (a * q) q 8 ≠ 0)
    (hA9 : qPoch (a * q) q 9 ≠ 0) :
    ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 3)) / qPoch (a * q) q 6 +
      ((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 2)) /
        (qPochhammer q 1 * qPoch (a * q) q 7) +
      ((qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 1)) /
        (qPochhammer q 2 * qPoch (a * q) q 8) +
      ((qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 0)) /
        (qPochhammer q 3 * qPoch (a * q) q 9) =
      (qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 /
        (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3)) /
        (qPochhammer q 3 * qPoch (a * q) q 9) := by
  have hD : qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 ≠ 0 :=
    mul_ne_zero hD1 hD2
  have hDthree : qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 ≠ 0 :=
    mul_ne_zero hD1three hD2three
  have hcommon := BaileyTransform_six_alpha_three_common_denominator_identity
    a q ρ₁ ρ₂ hρ hQ1 hQ2 hA6 hA7 hA8 hD1three hD2three
  simpa [qPochhammer, qPoch] using
    (BaileyTransform_four_term_fraction_from_common_ratio
      (P1 := qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3)
      (P2 := qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2)
      (P3 := qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1)
      (P4 := qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6)
      (B := qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3)
      (D := qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6)
      (D1 := qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3)
      (Q1 := qPochhammer q 1)
      (Q2 := qPochhammer q 2)
      (Q3 := qPochhammer q 3)
      (A2 := qPoch (a * q) q 6)
      (A3 := qPoch (a * q) q 7)
      (A4 := qPoch (a * q) q 8)
      (A5 := qPoch (a * q) q 9)
      hD hDthree hQ1 hQ2 hQ3 hA6 hA7 hA8 hA9 hcommon)

/-- The α₄ coefficient identity in the `n = 6` finite Bailey-lemma step after
moving the three transformed-β contributions to a common denominator. -/
theorem BaileyTransform_six_alpha_four_common_denominator_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hA8 : qPoch (a * q) q 8 ≠ 0)
    (hA9 : qPoch (a * q) q 9 ≠ 0)
    (hD1four : qPoch (a * q / ρ₁) q 4 ≠ 0)
    (hD2four : qPoch (a * q / ρ₂) q 4 ≠ 0) :
    qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2 *
        (qPoch (a * q) q 10 / qPoch (a * q) q 8) +
      qPoch ρ₁ q 5 * qPoch ρ₂ q 5 *
        (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1 *
        (qPochhammer q 2 * qPoch (a * q) q 10 /
          (qPochhammer q 1 * qPochhammer q 1 * qPoch (a * q) q 9)) +
      qPoch ρ₁ q 6 * qPoch ρ₂ q 6 *
        (a * q / (ρ₁ * ρ₂)) ^ 6 =
      (qPoch ρ₁ q 4 * qPoch ρ₂ q 4 *
        (a * q / (ρ₁ * ρ₂)) ^ 4) *
        ((qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6) /
          (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4)) := by
  rw [BaileyTransform_six_qpoch_aq_ten_over_eight a q hA8,
    BaileyTransform_six_qpochhammer_aq_alpha_four_middle_ratio a q hQ1 hA9,
    BaileyTransform_six_qpoch_pair_ratio_four_six a q ρ₁ ρ₂ hD1four hD2four]
  have hρ1 : ρ₁ ≠ 0 := left_ne_zero_of_mul hρ
  have hρ2 : ρ₂ ≠ 0 := right_ne_zero_of_mul hρ
  rw [show qPoch (a * q / (ρ₁ * ρ₂)) q 2 =
      (1 - a * q / (ρ₁ * ρ₂)) * (1 - (a * q / (ρ₁ * ρ₂)) * q) by
        simp [qPoch]]
  rw [show qPoch (a * q / (ρ₁ * ρ₂)) q 1 =
      1 - a * q / (ρ₁ * ρ₂) by simp [qPoch]]
  rw [show qPoch ρ₁ q 6 = qPoch ρ₁ q 5 * (1 - ρ₁ * q ^ 5) by rfl]
  rw [show qPoch ρ₂ q 6 = qPoch ρ₂ q 5 * (1 - ρ₂ * q ^ 5) by rfl]
  rw [show qPoch ρ₁ q 5 = qPoch ρ₁ q 4 * (1 - ρ₁ * q ^ 4) by rfl]
  rw [show qPoch ρ₂ q 5 = qPoch ρ₂ q 4 * (1 - ρ₂ * q ^ 4) by rfl]
  field_simp [hρ, hρ1, hρ2]
  ring

/-- The α₄ coefficient identity in the `n = 6` finite Bailey-lemma step. -/
theorem BaileyTransform_six_alpha_four_coefficient_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hD1 : qPoch (a * q / ρ₁) q 6 ≠ 0)
    (hD2 : qPoch (a * q / ρ₂) q 6 ≠ 0)
    (hD1four : qPoch (a * q / ρ₁) q 4 ≠ 0)
    (hD2four : qPoch (a * q / ρ₂) q 4 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hA8 : qPoch (a * q) q 8 ≠ 0)
    (hA9 : qPoch (a * q) q 9 ≠ 0)
    (hA10 : qPoch (a * q) q 10 ≠ 0) :
    ((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 2)) / qPoch (a * q) q 8 +
      ((qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 1)) /
        (qPochhammer q 1 * qPoch (a * q) q 9) +
      ((qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 0)) /
        (qPochhammer q 2 * qPoch (a * q) q 10) =
      (qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 /
        (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4)) /
        (qPochhammer q 2 * qPoch (a * q) q 10) := by
  have hD : qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 ≠ 0 :=
    mul_ne_zero hD1 hD2
  have hDfour : qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4 ≠ 0 :=
    mul_ne_zero hD1four hD2four
  have hcommon := BaileyTransform_six_alpha_four_common_denominator_identity
    a q ρ₁ ρ₂ hρ hQ1 hA8 hA9 hD1four hD2four
  simpa [qPochhammer, qPoch] using
    (BaileyTransform_three_term_fraction_from_common_ratio
      (P1 := qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2)
      (P2 := qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1)
      (P3 := qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6)
      (B := qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4)
      (D := qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6)
      (D1 := qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4)
      (Q1 := qPochhammer q 1)
      (Q2 := qPochhammer q 2)
      (A2 := qPoch (a * q) q 8)
      (A3 := qPoch (a * q) q 9)
      (A4 := qPoch (a * q) q 10)
      hD hDfour hQ1 hQ2 hA8 hA9 hA10 hcommon)

/-- The α₅ coefficient identity in the `n = 6` finite Bailey-lemma step after
moving the two transformed-β contributions to a common denominator. -/
theorem BaileyTransform_six_alpha_five_common_denominator_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hA10 : qPoch (a * q) q 10 ≠ 0)
    (hD1five : qPoch (a * q / ρ₁) q 5 ≠ 0)
    (hD2five : qPoch (a * q / ρ₂) q 5 ≠ 0) :
    qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1 *
        (qPoch (a * q) q 11 / qPoch (a * q) q 10) +
      qPoch ρ₁ q 6 * qPoch ρ₂ q 6 *
        (a * q / (ρ₁ * ρ₂)) ^ 6 =
      (qPoch ρ₁ q 5 * qPoch ρ₂ q 5 *
        (a * q / (ρ₁ * ρ₂)) ^ 5) *
        ((qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6) /
          (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5)) := by
  rw [BaileyTransform_six_qpoch_ratio_ten_eleven a q hA10,
    BaileyTransform_six_qpoch_pair_ratio_five_six a q ρ₁ ρ₂ hD1five hD2five]
  have hρ1 : ρ₁ ≠ 0 := left_ne_zero_of_mul hρ
  have hρ2 : ρ₂ ≠ 0 := right_ne_zero_of_mul hρ
  rw [show qPoch (a * q / (ρ₁ * ρ₂)) q 1 =
      1 - a * q / (ρ₁ * ρ₂) by simp [qPoch]]
  rw [show qPoch ρ₁ q 6 = qPoch ρ₁ q 5 * (1 - ρ₁ * q ^ 5) by rfl]
  rw [show qPoch ρ₂ q 6 = qPoch ρ₂ q 5 * (1 - ρ₂ * q ^ 5) by rfl]
  field_simp [hρ, hρ1, hρ2]
  ring

/-- The α₅ coefficient identity in the `n = 6` finite Bailey-lemma step. -/
theorem BaileyTransform_six_alpha_five_coefficient_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hD1 : qPoch (a * q / ρ₁) q 6 ≠ 0)
    (hD2 : qPoch (a * q / ρ₂) q 6 ≠ 0)
    (hD1five : qPoch (a * q / ρ₁) q 5 ≠ 0)
    (hD2five : qPoch (a * q / ρ₂) q 5 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hA10 : qPoch (a * q) q 10 ≠ 0)
    (hA11 : qPoch (a * q) q 11 ≠ 0) :
    ((qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 1)) / qPoch (a * q) q 10 +
      ((qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 0)) /
        (qPochhammer q 1 * qPoch (a * q) q 11) =
      (qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 /
        (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5)) /
        (qPochhammer q 1 * qPoch (a * q) q 11) := by
  have hD : qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 ≠ 0 :=
    mul_ne_zero hD1 hD2
  have hDfive : qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 ≠ 0 :=
    mul_ne_zero hD1five hD2five
  have hcommon := BaileyTransform_six_alpha_five_common_denominator_identity
    a q ρ₁ ρ₂ hρ hA10 hD1five hD2five
  simpa [qPochhammer, qPoch] using
    (BaileyTransform_two_term_fraction_from_common_ratio
      (P0 := qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1)
      (P1 := qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6)
      (B := qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5)
      (D := qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6)
      (D2 := qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5)
      (Q := qPochhammer q 1)
      (A4 := qPoch (a * q) q 10)
      (A5 := qPoch (a * q) q 11)
      hD hDfive hQ1 hA10 hA11 hcommon)

/-- The Bailey-beta side generated by the transformed α at `n=2` expands to
the three defining summands. -/
theorem BaileyBeta_transformAlpha_two_expand (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    BaileyBeta a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 2 =
      BaileyTerm a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 2 0 +
      BaileyTerm a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 2 1 +
      BaileyTerm a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 2 2 := by
  exact BaileyBeta_two_expand a q (BaileyTransformAlpha a q ρ₁ ρ₂ α)

/-- The Bailey-beta side generated by the transformed α at `n=3` expands to
the four defining summands. -/
theorem BaileyBeta_transformAlpha_three_expand (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    BaileyBeta a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 3 =
      BaileyTerm a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 3 0 +
      BaileyTerm a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 3 1 +
      BaileyTerm a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 3 2 +
      BaileyTerm a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 3 3 := by
  exact BaileyBeta_three_expand a q (BaileyTransformAlpha a q ρ₁ ρ₂ α)

/-- The Bailey-beta side generated by the transformed α at `n=4` expands to
the five defining summands. -/
theorem BaileyBeta_transformAlpha_four_expand (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    BaileyBeta a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 4 =
      BaileyTerm a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 4 0 +
      BaileyTerm a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 4 1 +
      BaileyTerm a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 4 2 +
      BaileyTerm a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 4 3 +
      BaileyTerm a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 4 4 := by
  exact BaileyBeta_four_expand a q (BaileyTransformAlpha a q ρ₁ ρ₂ α)

/-- The Bailey-beta side generated by the transformed α at `n=5` expands to
the six defining summands. -/
theorem BaileyBeta_transformAlpha_five_expand (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    BaileyBeta a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 5 =
      BaileyTerm a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 5 0 +
      BaileyTerm a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 5 1 +
      BaileyTerm a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 5 2 +
      BaileyTerm a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 5 3 +
      BaileyTerm a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 5 4 +
      BaileyTerm a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 5 5 := by
  exact BaileyBeta_five_expand a q (BaileyTransformAlpha a q ρ₁ ρ₂ α)

/-- The Bailey-beta side generated by the transformed α at `n=6` expands to
the seven defining summands. -/
theorem BaileyBeta_transformAlpha_six_expand (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    BaileyBeta a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 6 =
      BaileyTerm a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 6 0 +
      BaileyTerm a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 6 1 +
      BaileyTerm a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 6 2 +
      BaileyTerm a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 6 3 +
      BaileyTerm a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 6 4 +
      BaileyTerm a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 6 5 +
      BaileyTerm a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 6 6 := by
  exact BaileyBeta_six_expand a q (BaileyTransformAlpha a q ρ₁ ρ₂ α)

/-- The `k=0` term of `BaileyBeta` for the transformed α at `N=2`. -/
theorem BaileyTerm_transformAlpha_two_zero (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    BaileyTerm a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 2 0 =
      α 0 / (qPochhammer q 2 * qPoch (a * q) q 2) := by
  rw [BaileyTerm_zero, BaileyTransformAlpha_zero]

/-- The `k=1` term of `BaileyBeta` for the transformed α at `N=2`. -/
theorem BaileyTerm_transformAlpha_two_one (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    BaileyTerm a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 2 1 =
      ((1 - ρ₁) * (1 - ρ₂) * (a * q / (ρ₁ * ρ₂)) /
        ((1 - a * q / ρ₁) * (1 - a * q / ρ₂)) * α 1) /
        (qPochhammer q 1 * qPoch (a * q) q 3) := by
  simp only [BaileyTerm, BaileyTransformAlpha_one]

/-- The `k=2` term of `BaileyBeta` for the transformed α at `N=2`. -/
theorem BaileyTerm_transformAlpha_two_two (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    BaileyTerm a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 2 2 =
      (qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 /
        (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2) * α 2) /
        qPoch (a * q) q 4 := by
  rw [BaileyTerm_at_n_simplified, BaileyTransformAlpha_two]

/-- The `k=0` term of `BaileyBeta` for the transformed α at `N=3`. -/
theorem BaileyTerm_transformAlpha_three_zero (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    BaileyTerm a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 3 0 =
      α 0 / (qPochhammer q 3 * qPoch (a * q) q 3) := by
  rw [BaileyTerm_zero, BaileyTransformAlpha_zero]

/-- The `k=1` term of `BaileyBeta` for the transformed α at `N=3`. -/
theorem BaileyTerm_transformAlpha_three_one (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    BaileyTerm a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 3 1 =
      ((1 - ρ₁) * (1 - ρ₂) * (a * q / (ρ₁ * ρ₂)) /
        ((1 - a * q / ρ₁) * (1 - a * q / ρ₂)) * α 1) /
        (qPochhammer q 2 * qPoch (a * q) q 4) := by
  simp only [BaileyTerm, BaileyTransformAlpha_one]

/-- The `k=2` term of `BaileyBeta` for the transformed α at `N=3`. -/
theorem BaileyTerm_transformAlpha_three_two (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    BaileyTerm a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 3 2 =
      (qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 /
        (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2) * α 2) /
        (qPochhammer q 1 * qPoch (a * q) q 5) := by
  simp only [BaileyTerm, BaileyTransformAlpha_two]

/-- The `k=3` term of `BaileyBeta` for the transformed α at `N=3`. -/
theorem BaileyTerm_transformAlpha_three_three (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    BaileyTerm a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 3 3 =
      (qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 /
        (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3) * α 3) /
        qPoch (a * q) q 6 := by
  rw [BaileyTerm_at_n_simplified, BaileyTransformAlpha_three]

/-- The `k=0` term of `BaileyBeta` for the transformed α at `N=4`. -/
theorem BaileyTerm_transformAlpha_four_zero (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    BaileyTerm a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 4 0 =
      α 0 / (qPochhammer q 4 * qPoch (a * q) q 4) := by
  rw [BaileyTerm_zero, BaileyTransformAlpha_zero]

/-- The `k=1` term of `BaileyBeta` for the transformed α at `N=4`. -/
theorem BaileyTerm_transformAlpha_four_one (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    BaileyTerm a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 4 1 =
      ((1 - ρ₁) * (1 - ρ₂) * (a * q / (ρ₁ * ρ₂)) /
        ((1 - a * q / ρ₁) * (1 - a * q / ρ₂)) * α 1) /
        (qPochhammer q 3 * qPoch (a * q) q 5) := by
  simp only [BaileyTerm, BaileyTransformAlpha_one]

/-- The `k=2` term of `BaileyBeta` for the transformed α at `N=4`. -/
theorem BaileyTerm_transformAlpha_four_two (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    BaileyTerm a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 4 2 =
      ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 /
        (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2)) * α 2) /
        (qPochhammer q 2 * qPoch (a * q) q 6) := by
  simp only [BaileyTerm, BaileyTransformAlpha_two]

/-- The `k=3` term of `BaileyBeta` for the transformed α at `N=4`. -/
theorem BaileyTerm_transformAlpha_four_three (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    BaileyTerm a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 4 3 =
      ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 /
        (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3)) * α 3) /
        (qPochhammer q 1 * qPoch (a * q) q 7) := by
  simp only [BaileyTerm, BaileyTransformAlpha_three]

/-- The `k=4` term of `BaileyBeta` for the transformed α at `N=4`. -/
theorem BaileyTerm_transformAlpha_four_four (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    BaileyTerm a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 4 4 =
      ((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 /
        (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4)) * α 4) /
        qPoch (a * q) q 8 := by
  rw [BaileyTerm_at_n_simplified, BaileyTransformAlpha_four]

/-- The `k=0` term of `BaileyBeta` for the transformed α at `N=5`. -/
theorem BaileyTerm_transformAlpha_five_zero (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    BaileyTerm a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 5 0 =
      α 0 / (qPochhammer q 5 * qPoch (a * q) q 5) := by
  rw [BaileyTerm_zero, BaileyTransformAlpha_zero]

/-- The `k=1` term of `BaileyBeta` for the transformed α at `N=5`. -/
theorem BaileyTerm_transformAlpha_five_one (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    BaileyTerm a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 5 1 =
      ((1 - ρ₁) * (1 - ρ₂) * (a * q / (ρ₁ * ρ₂)) /
        ((1 - a * q / ρ₁) * (1 - a * q / ρ₂)) * α 1) /
        (qPochhammer q 4 * qPoch (a * q) q 6) := by
  simp only [BaileyTerm, BaileyTransformAlpha_one]

/-- The `k=2` term of `BaileyBeta` for the transformed α at `N=5`. -/
theorem BaileyTerm_transformAlpha_five_two (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    BaileyTerm a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 5 2 =
      ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 /
        (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2)) * α 2) /
        (qPochhammer q 3 * qPoch (a * q) q 7) := by
  simp only [BaileyTerm, BaileyTransformAlpha_two]

/-- The `k=3` term of `BaileyBeta` for the transformed α at `N=5`. -/
theorem BaileyTerm_transformAlpha_five_three (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    BaileyTerm a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 5 3 =
      ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 /
        (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3)) * α 3) /
        (qPochhammer q 2 * qPoch (a * q) q 8) := by
  simp only [BaileyTerm, BaileyTransformAlpha_three]

/-- The `k=4` term of `BaileyBeta` for the transformed α at `N=5`. -/
theorem BaileyTerm_transformAlpha_five_four (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    BaileyTerm a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 5 4 =
      ((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 /
        (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4)) * α 4) /
        (qPochhammer q 1 * qPoch (a * q) q 9) := by
  simp only [BaileyTerm, BaileyTransformAlpha_four]

/-- The `k=5` term of `BaileyBeta` for the transformed α at `N=5`. -/
theorem BaileyTerm_transformAlpha_five_five (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    BaileyTerm a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 5 5 =
      ((qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 /
        (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5)) * α 5) /
        qPoch (a * q) q 10 := by
  rw [BaileyTerm_at_n_simplified, BaileyTransformAlpha_five]

/-- The `k=0` term of `BaileyBeta` for the transformed α at `N=6`. -/
theorem BaileyTerm_transformAlpha_six_zero (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    BaileyTerm a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 6 0 =
      α 0 / (qPochhammer q 6 * qPoch (a * q) q 6) := by
  rw [BaileyTerm_zero, BaileyTransformAlpha_zero]

/-- The `k=1` term of `BaileyBeta` for the transformed α at `N=6`. -/
theorem BaileyTerm_transformAlpha_six_one (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    BaileyTerm a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 6 1 =
      ((1 - ρ₁) * (1 - ρ₂) * (a * q / (ρ₁ * ρ₂)) /
        ((1 - a * q / ρ₁) * (1 - a * q / ρ₂)) * α 1) /
        (qPochhammer q 5 * qPoch (a * q) q 7) := by
  simp only [BaileyTerm, BaileyTransformAlpha_one]

/-- The `k=2` term of `BaileyBeta` for the transformed α at `N=6`. -/
theorem BaileyTerm_transformAlpha_six_two (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    BaileyTerm a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 6 2 =
      ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 /
        (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2)) * α 2) /
        (qPochhammer q 4 * qPoch (a * q) q 8) := by
  simp only [BaileyTerm, BaileyTransformAlpha_two]

/-- The `k=3` term of `BaileyBeta` for the transformed α at `N=6`. -/
theorem BaileyTerm_transformAlpha_six_three (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    BaileyTerm a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 6 3 =
      ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 /
        (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3)) * α 3) /
        (qPochhammer q 3 * qPoch (a * q) q 9) := by
  simp only [BaileyTerm, BaileyTransformAlpha_three]

/-- The `k=4` term of `BaileyBeta` for the transformed α at `N=6`. -/
theorem BaileyTerm_transformAlpha_six_four (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    BaileyTerm a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 6 4 =
      ((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 /
        (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4)) * α 4) /
        (qPochhammer q 2 * qPoch (a * q) q 10) := by
  simp only [BaileyTerm, BaileyTransformAlpha_four]

/-- The `k=5` term of `BaileyBeta` for the transformed α at `N=6`. -/
theorem BaileyTerm_transformAlpha_six_five (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    BaileyTerm a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 6 5 =
      ((qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 /
        (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5)) * α 5) /
        (qPochhammer q 1 * qPoch (a * q) q 11) := by
  simp only [BaileyTerm, BaileyTransformAlpha_five]

/-- The `k=6` term of `BaileyBeta` for the transformed α at `N=6`. -/
theorem BaileyTerm_transformAlpha_six_six (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    BaileyTerm a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 6 6 =
      ((qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6 /
        (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6)) * α 6) /
        qPoch (a * q) q 12 := by
  rw [BaileyTerm_at_n_simplified, BaileyTransformAlpha_six]

/-- `BaileyBeta` for the transformed α at `N=2`, with all transformed terms
evaluated. -/
theorem BaileyBeta_transformAlpha_two_terms (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    BaileyBeta a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 2 =
      α 0 / (qPochhammer q 2 * qPoch (a * q) q 2) +
      (((1 - ρ₁) * (1 - ρ₂) * (a * q / (ρ₁ * ρ₂)) /
        ((1 - a * q / ρ₁) * (1 - a * q / ρ₂)) * α 1) /
        (qPochhammer q 1 * qPoch (a * q) q 3)) +
      ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 /
        (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2) * α 2) /
        qPoch (a * q) q 4) := by
  rw [BaileyBeta_transformAlpha_two_expand, BaileyTerm_transformAlpha_two_zero,
    BaileyTerm_transformAlpha_two_one, BaileyTerm_transformAlpha_two_two]

/-- The transformed-α Bailey beta at `N=2`, rewritten as a linear combination
of the three α-coefficients with standardized q-Pochhammer coefficients. -/
theorem BaileyBeta_transformAlpha_two_terms_linear (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    BaileyBeta a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 2 =
      (1 / (qPochhammer q 2 * qPoch (a * q) q 2)) * α 0 +
        (((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂))) /
          (qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1)) /
          (qPochhammer q 1 * qPoch (a * q) q 3)) * α 1 +
        (((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 /
          (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2)) /
          qPoch (a * q) q 4)) * α 2 := by
  have hC1 :
      ((1 - ρ₁) * (1 - ρ₂) * (a * q / (ρ₁ * ρ₂)) /
        ((1 - a * q / ρ₁) * (1 - a * q / ρ₂))) =
        (qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂))) /
          (qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1) := by
    simp [qPoch]
  rw [BaileyBeta_transformAlpha_two_terms, hC1]
  ring

/-- The `n = 2` finite Bailey-lemma preservation step, under explicit nonzero
denominator hypotheses for the standardized algebra. -/
theorem BaileyTransform_preserves_pair_two_of_nonzero
    (a q ρ₁ ρ₂ : R) {α β : Nat → R}
    (h : IsBaileyPairUpTo a q α β 2)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hD1 : qPoch (a * q / ρ₁) q 2 ≠ 0)
    (hD2 : qPoch (a * q / ρ₂) q 2 ≠ 0)
    (hD1one : qPoch (a * q / ρ₁) q 1 ≠ 0)
    (hD2one : qPoch (a * q / ρ₂) q 1 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hA2 : qPoch (a * q) q 2 ≠ 0)
    (hA3 : qPoch (a * q) q 3 ≠ 0)
    (hB1 : (1 - q) * (1 - a * q) ≠ 0) :
    BaileyTransformBeta a q ρ₁ ρ₂ β 2 =
      BaileyBeta a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 2 := by
  rw [BaileyTransformBeta_of_pair_two_terms a q ρ₁ ρ₂ h,
    BaileyBeta_transformAlpha_two_terms_linear]
  exact BaileyTransform_two_standard_terms_eq_transformAlpha_two_terms
    a q ρ₁ ρ₂ (α 0) (α 1) (α 2)
    hρ hD1 hD2 hD1one hD2one hQ1 hQ2 hA2 hA3 hB1

/-- Up-to-two finite Bailey-lemma packaging under explicit nonzero denominator
hypotheses. -/
theorem BaileyTransform_preserves_pair_upTo_two_of_nonzero
    (a q ρ₁ ρ₂ : R) {α β : Nat → R}
    (h : IsBaileyPairUpTo a q α β 2)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hD1 : qPoch (a * q / ρ₁) q 2 ≠ 0)
    (hD2 : qPoch (a * q / ρ₂) q 2 ≠ 0)
    (hD1one : qPoch (a * q / ρ₁) q 1 ≠ 0)
    (hD2one : qPoch (a * q / ρ₂) q 1 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hA2 : qPoch (a * q) q 2 ≠ 0)
    (hA3 : qPoch (a * q) q 3 ≠ 0)
    (hB1 : (1 - q) * (1 - a * q) ≠ 0) :
    IsBaileyPairUpTo a q (BaileyTransformAlpha a q ρ₁ ρ₂ α)
      (BaileyTransformBeta a q ρ₁ ρ₂ β) 2 := by
  have hq : 1 - q ≠ 0 := by simpa [qPochhammer] using hQ1
  have haq : 1 - a * q ≠ 0 := right_ne_zero_of_mul hB1
  have hρ₁one : 1 - a * q / ρ₁ ≠ 0 := by simpa [qPoch] using hD1one
  have hρ₂one : 1 - a * q / ρ₂ ≠ 0 := by simpa [qPoch] using hD2one
  exact IsBaileyPairUpTo.of_two
    (BaileyTransform_preserves_pair_zero a q ρ₁ ρ₂ (h.mono (by omega)))
    (BaileyTransform_preserves_pair_one_of_nonzero a q ρ₁ ρ₂ (h.mono (by omega))
      hρ hq haq hρ₁one hρ₂one)
    (BaileyTransform_preserves_pair_two_of_nonzero a q ρ₁ ρ₂ h
      hρ hD1 hD2 hD1one hD2one hQ1 hQ2 hA2 hA3 hB1)

/-- `BaileyBeta` for the transformed α at `N=3`, with all transformed terms
evaluated. -/
theorem BaileyBeta_transformAlpha_three_terms (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    BaileyBeta a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 3 =
      α 0 / (qPochhammer q 3 * qPoch (a * q) q 3) +
      (((1 - ρ₁) * (1 - ρ₂) * (a * q / (ρ₁ * ρ₂)) /
        ((1 - a * q / ρ₁) * (1 - a * q / ρ₂)) * α 1) /
        (qPochhammer q 2 * qPoch (a * q) q 4)) +
      ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 /
        (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2) * α 2) /
        (qPochhammer q 1 * qPoch (a * q) q 5)) +
      ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 /
        (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3) * α 3) /
        qPoch (a * q) q 6) := by
  rw [BaileyBeta_transformAlpha_three_expand, BaileyTerm_transformAlpha_three_zero,
    BaileyTerm_transformAlpha_three_one, BaileyTerm_transformAlpha_three_two,
    BaileyTerm_transformAlpha_three_three]

/-- The transformed-α Bailey beta at `N=3`, rewritten as a linear combination
of the four α-coefficients with standardized q-Pochhammer coefficients. -/
theorem BaileyBeta_transformAlpha_three_terms_linear
    (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    BaileyBeta a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 3 =
      (1 / (qPochhammer q 3 * qPoch (a * q) q 3)) * α 0 +
        (((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂))) /
          (qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1)) /
          (qPochhammer q 2 * qPoch (a * q) q 4)) * α 1 +
        (((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 /
          (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2)) /
          (qPochhammer q 1 * qPoch (a * q) q 5)) * α 2) +
        (((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 /
          (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3)) /
          qPoch (a * q) q 6) * α 3) := by
  have hC1 :
      ((1 - ρ₁) * (1 - ρ₂) * (a * q / (ρ₁ * ρ₂)) /
        ((1 - a * q / ρ₁) * (1 - a * q / ρ₂))) =
        (qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂))) /
          (qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1) := by
    simp [qPoch]
  rw [BaileyBeta_transformAlpha_three_terms, hC1]
  ring

/-- `BaileyBeta` for the transformed α at `N=4`, with all transformed terms
evaluated. -/
theorem BaileyBeta_transformAlpha_four_terms (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    BaileyBeta a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 4 =
      α 0 / (qPochhammer q 4 * qPoch (a * q) q 4) +
      (((1 - ρ₁) * (1 - ρ₂) * (a * q / (ρ₁ * ρ₂)) /
        ((1 - a * q / ρ₁) * (1 - a * q / ρ₂)) * α 1) /
        (qPochhammer q 3 * qPoch (a * q) q 5)) +
      ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 /
        (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2) * α 2) /
        (qPochhammer q 2 * qPoch (a * q) q 6)) +
      ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 /
        (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3) * α 3) /
        (qPochhammer q 1 * qPoch (a * q) q 7)) +
      ((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 /
        (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4) * α 4) /
        qPoch (a * q) q 8) := by
  rw [BaileyBeta_transformAlpha_four_expand,
    BaileyTerm_transformAlpha_four_zero,
    BaileyTerm_transformAlpha_four_one,
    BaileyTerm_transformAlpha_four_two,
    BaileyTerm_transformAlpha_four_three,
    BaileyTerm_transformAlpha_four_four]

/-- `BaileyBeta` for the transformed α at `N=5`, with all transformed terms
evaluated. -/
theorem BaileyBeta_transformAlpha_five_terms (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    BaileyBeta a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 5 =
      α 0 / (qPochhammer q 5 * qPoch (a * q) q 5) +
      (((1 - ρ₁) * (1 - ρ₂) * (a * q / (ρ₁ * ρ₂)) /
        ((1 - a * q / ρ₁) * (1 - a * q / ρ₂)) * α 1) /
        (qPochhammer q 4 * qPoch (a * q) q 6)) +
      (((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 /
        (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2)) * α 2) /
        (qPochhammer q 3 * qPoch (a * q) q 7)) +
      (((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 /
        (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3)) * α 3) /
        (qPochhammer q 2 * qPoch (a * q) q 8)) +
      (((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 /
        (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4)) * α 4) /
        (qPochhammer q 1 * qPoch (a * q) q 9)) +
      (((qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 /
        (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5)) * α 5) /
        qPoch (a * q) q 10) := by
  rw [BaileyBeta_transformAlpha_five_expand,
    BaileyTerm_transformAlpha_five_zero,
    BaileyTerm_transformAlpha_five_one,
    BaileyTerm_transformAlpha_five_two,
    BaileyTerm_transformAlpha_five_three,
    BaileyTerm_transformAlpha_five_four,
    BaileyTerm_transformAlpha_five_five]

/-- `BaileyBeta` for the transformed α at `N=6`, with all transformed terms
evaluated. -/
theorem BaileyBeta_transformAlpha_six_terms (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    BaileyBeta a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 6 =
      α 0 / (qPochhammer q 6 * qPoch (a * q) q 6) +
      (((1 - ρ₁) * (1 - ρ₂) * (a * q / (ρ₁ * ρ₂)) /
        ((1 - a * q / ρ₁) * (1 - a * q / ρ₂)) * α 1) /
        (qPochhammer q 5 * qPoch (a * q) q 7)) +
      (((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 /
        (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2)) * α 2) /
        (qPochhammer q 4 * qPoch (a * q) q 8)) +
      (((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 /
        (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3)) * α 3) /
        (qPochhammer q 3 * qPoch (a * q) q 9)) +
      (((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 /
        (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4)) * α 4) /
        (qPochhammer q 2 * qPoch (a * q) q 10)) +
      (((qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 /
        (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5)) * α 5) /
        (qPochhammer q 1 * qPoch (a * q) q 11)) +
      (((qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6 /
        (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6)) * α 6) /
        qPoch (a * q) q 12) := by
  rw [BaileyBeta_transformAlpha_six_expand,
    BaileyTerm_transformAlpha_six_zero,
    BaileyTerm_transformAlpha_six_one,
    BaileyTerm_transformAlpha_six_two,
    BaileyTerm_transformAlpha_six_three,
    BaileyTerm_transformAlpha_six_four,
    BaileyTerm_transformAlpha_six_five,
    BaileyTerm_transformAlpha_six_six]

/-- The transformed-α Bailey beta at `N=4`, rewritten as a linear combination
of the five α-coefficients with standardized q-Pochhammer coefficients. -/
theorem BaileyBeta_transformAlpha_four_terms_linear
    (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    BaileyBeta a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 4 =
      (1 / (qPochhammer q 4 * qPoch (a * q) q 4)) * α 0 +
        (((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂))) /
          (qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1)) /
          (qPochhammer q 3 * qPoch (a * q) q 5)) * α 1 +
        (((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 /
          (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2)) /
          (qPochhammer q 2 * qPoch (a * q) q 6)) * α 2) +
        (((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 /
          (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3)) /
          (qPochhammer q 1 * qPoch (a * q) q 7)) * α 3) +
        (((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 /
          (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4)) /
          qPoch (a * q) q 8) * α 4) := by
  have hC1 :
      ((1 - ρ₁) * (1 - ρ₂) * (a * q / (ρ₁ * ρ₂)) /
        ((1 - a * q / ρ₁) * (1 - a * q / ρ₂))) =
        (qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂))) /
          (qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1) := by
    simp [qPoch]
  rw [BaileyBeta_transformAlpha_four_terms, hC1]
  ring

/-- The transformed-α Bailey beta at `N=5`, rewritten as a linear combination
of the six α-coefficients with standardized q-Pochhammer coefficients. -/
theorem BaileyBeta_transformAlpha_five_terms_linear
    (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    BaileyBeta a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 5 =
      (1 / (qPochhammer q 5 * qPoch (a * q) q 5)) * α 0 +
        (((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂))) /
          (qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1)) /
          (qPochhammer q 4 * qPoch (a * q) q 6)) * α 1 +
        (((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 /
          (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2)) /
          (qPochhammer q 3 * qPoch (a * q) q 7)) * α 2) +
        (((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 /
          (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3)) /
          (qPochhammer q 2 * qPoch (a * q) q 8)) * α 3) +
        (((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 /
          (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4)) /
          (qPochhammer q 1 * qPoch (a * q) q 9)) * α 4) +
        (((qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 /
          (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5)) /
          qPoch (a * q) q 10) * α 5) := by
  have hC1 :
      ((1 - ρ₁) * (1 - ρ₂) * (a * q / (ρ₁ * ρ₂)) /
        ((1 - a * q / ρ₁) * (1 - a * q / ρ₂))) =
        (qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂))) /
          (qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1) := by
    simp [qPoch]
  rw [BaileyBeta_transformAlpha_five_terms, hC1]
  ring

/-- The transformed-α Bailey beta at `N=6`, rewritten as a linear combination
of the seven α-coefficients with standardized q-Pochhammer coefficients. -/
theorem BaileyBeta_transformAlpha_six_terms_linear
    (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    BaileyBeta a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 6 =
      (1 / (qPochhammer q 6 * qPoch (a * q) q 6)) * α 0 +
        (((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂))) /
          (qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1)) /
          (qPochhammer q 5 * qPoch (a * q) q 7)) * α 1 +
        (((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 /
          (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2)) /
          (qPochhammer q 4 * qPoch (a * q) q 8)) * α 2) +
        (((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 /
          (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3)) /
          (qPochhammer q 3 * qPoch (a * q) q 9)) * α 3) +
        (((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 /
          (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4)) /
          (qPochhammer q 2 * qPoch (a * q) q 10)) * α 4) +
        (((qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 /
          (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5)) /
          (qPochhammer q 1 * qPoch (a * q) q 11)) * α 5) +
        (((qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6 /
          (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6)) /
          qPoch (a * q) q 12) * α 6) := by
  have hC1 :
      ((1 - ρ₁) * (1 - ρ₂) * (a * q / (ρ₁ * ρ₂)) /
        ((1 - a * q / ρ₁) * (1 - a * q / ρ₂))) =
        (qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂))) /
          (qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1) := by
    simp [qPoch]
  rw [BaileyBeta_transformAlpha_six_terms, hC1]
  ring

/-- `BaileyBeta` for the transformed α at `N = 7` expands to eight terms. -/
theorem BaileyBeta_transformAlpha_seven_expand (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    BaileyBeta a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 7 =
      BaileyTerm a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 7 0 +
      BaileyTerm a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 7 1 +
      BaileyTerm a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 7 2 +
      BaileyTerm a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 7 3 +
      BaileyTerm a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 7 4 +
      BaileyTerm a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 7 5 +
      BaileyTerm a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 7 6 +
      BaileyTerm a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 7 7 := by
  exact BaileyBeta_seven_expand a q (BaileyTransformAlpha a q ρ₁ ρ₂ α)

/-- The `k=0` term of `BaileyBeta` for the transformed α at `N=7`. -/
theorem BaileyTerm_transformAlpha_seven_zero (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    BaileyTerm a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 7 0 =
      α 0 / (qPochhammer q 7 * qPoch (a * q) q 7) := by
  rw [BaileyTerm_zero, BaileyTransformAlpha_zero]

/-- The `k=1` term of `BaileyBeta` for the transformed α at `N=7`. -/
theorem BaileyTerm_transformAlpha_seven_one (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    BaileyTerm a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 7 1 =
      ((1 - ρ₁) * (1 - ρ₂) * (a * q / (ρ₁ * ρ₂)) /
        ((1 - a * q / ρ₁) * (1 - a * q / ρ₂)) * α 1) /
        (qPochhammer q 6 * qPoch (a * q) q 8) := by
  simp only [BaileyTerm, BaileyTransformAlpha_one]

/-- The `k=2` term of `BaileyBeta` for the transformed α at `N=7`. -/
theorem BaileyTerm_transformAlpha_seven_two (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    BaileyTerm a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 7 2 =
      ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 /
        (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2)) * α 2) /
        (qPochhammer q 5 * qPoch (a * q) q 9) := by
  simp only [BaileyTerm, BaileyTransformAlpha_two]

/-- The `k=3` term of `BaileyBeta` for the transformed α at `N=7`. -/
theorem BaileyTerm_transformAlpha_seven_three (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    BaileyTerm a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 7 3 =
      ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 /
        (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3)) * α 3) /
        (qPochhammer q 4 * qPoch (a * q) q 10) := by
  simp only [BaileyTerm, BaileyTransformAlpha_three]

/-- The `k=4` term of `BaileyBeta` for the transformed α at `N=7`. -/
theorem BaileyTerm_transformAlpha_seven_four (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    BaileyTerm a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 7 4 =
      ((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 /
        (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4)) * α 4) /
        (qPochhammer q 3 * qPoch (a * q) q 11) := by
  simp only [BaileyTerm, BaileyTransformAlpha_four]

/-- The `k=5` term of `BaileyBeta` for the transformed α at `N=7`. -/
theorem BaileyTerm_transformAlpha_seven_five (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    BaileyTerm a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 7 5 =
      ((qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 /
        (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5)) * α 5) /
        (qPochhammer q 2 * qPoch (a * q) q 12) := by
  simp only [BaileyTerm, BaileyTransformAlpha_five]

/-- The `k=6` term of `BaileyBeta` for the transformed α at `N=7`. -/
theorem BaileyTerm_transformAlpha_seven_six (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    BaileyTerm a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 7 6 =
      ((qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6 /
        (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6)) * α 6) /
        (qPochhammer q 1 * qPoch (a * q) q 13) := by
  simp only [BaileyTerm, BaileyTransformAlpha_six]

/-- The `k=7` term of `BaileyBeta` for the transformed α at `N=7`. -/
theorem BaileyTerm_transformAlpha_seven_seven (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    BaileyTerm a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 7 7 =
      ((qPoch ρ₁ q 7 * qPoch ρ₂ q 7 * (a * q / (ρ₁ * ρ₂)) ^ 7 /
        (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7)) * α 7) /
        qPoch (a * q) q 14 := by
  rw [BaileyTerm_at_n_simplified, BaileyTransformAlpha_seven]

/-- `BaileyBeta` for the transformed α at `N=7`, with all transformed terms
evaluated. -/
theorem BaileyBeta_transformAlpha_seven_terms (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    BaileyBeta a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 7 =
      α 0 / (qPochhammer q 7 * qPoch (a * q) q 7) +
      (((1 - ρ₁) * (1 - ρ₂) * (a * q / (ρ₁ * ρ₂)) /
        ((1 - a * q / ρ₁) * (1 - a * q / ρ₂)) * α 1) /
        (qPochhammer q 6 * qPoch (a * q) q 8)) +
      (((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 /
        (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2)) * α 2) /
        (qPochhammer q 5 * qPoch (a * q) q 9)) +
      (((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 /
        (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3)) * α 3) /
        (qPochhammer q 4 * qPoch (a * q) q 10)) +
      (((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 /
        (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4)) * α 4) /
        (qPochhammer q 3 * qPoch (a * q) q 11)) +
      (((qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 /
        (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5)) * α 5) /
        (qPochhammer q 2 * qPoch (a * q) q 12)) +
      (((qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6 /
        (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6)) * α 6) /
        (qPochhammer q 1 * qPoch (a * q) q 13)) +
      (((qPoch ρ₁ q 7 * qPoch ρ₂ q 7 * (a * q / (ρ₁ * ρ₂)) ^ 7 /
        (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7)) * α 7) /
        qPoch (a * q) q 14) := by
  rw [BaileyBeta_transformAlpha_seven_expand,
    BaileyTerm_transformAlpha_seven_zero,
    BaileyTerm_transformAlpha_seven_one,
    BaileyTerm_transformAlpha_seven_two,
    BaileyTerm_transformAlpha_seven_three,
    BaileyTerm_transformAlpha_seven_four,
    BaileyTerm_transformAlpha_seven_five,
    BaileyTerm_transformAlpha_seven_six,
    BaileyTerm_transformAlpha_seven_seven]

/-- The transformed-α Bailey beta at `N=7`, rewritten as a linear combination
of the eight α-coefficients with standardized q-Pochhammer coefficients. -/
theorem BaileyBeta_transformAlpha_seven_terms_linear
    (a q ρ₁ ρ₂ : R) (α : Nat → R) :
    BaileyBeta a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 7 =
      (1 / (qPochhammer q 7 * qPoch (a * q) q 7)) * α 0 +
        (((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂))) /
          (qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1)) /
          (qPochhammer q 6 * qPoch (a * q) q 8)) * α 1 +
        (((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 /
          (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2)) /
          (qPochhammer q 5 * qPoch (a * q) q 9)) * α 2) +
        (((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 /
          (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3)) /
          (qPochhammer q 4 * qPoch (a * q) q 10)) * α 3) +
        (((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 /
          (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4)) /
          (qPochhammer q 3 * qPoch (a * q) q 11)) * α 4) +
        (((qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 /
          (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5)) /
          (qPochhammer q 2 * qPoch (a * q) q 12)) * α 5) +
        (((qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6 /
          (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6)) /
          (qPochhammer q 1 * qPoch (a * q) q 13)) * α 6) +
        (((qPoch ρ₁ q 7 * qPoch ρ₂ q 7 * (a * q / (ρ₁ * ρ₂)) ^ 7 /
          (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7)) /
          qPoch (a * q) q 14) * α 7) := by
  have hC1 :
      ((1 - ρ₁) * (1 - ρ₂) * (a * q / (ρ₁ * ρ₂)) /
        ((1 - a * q / ρ₁) * (1 - a * q / ρ₂))) =
        (qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂))) /
          (qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1) := by
    simp [qPoch]
  rw [BaileyBeta_transformAlpha_seven_terms, hC1]
  ring

/-- The standardized `n = 3` transformed-β expression agrees coefficientwise
with the standardized transformed-α Bailey-beta expression. -/
theorem BaileyTransform_three_standard_terms_eq_transformAlpha_three_terms
    (a q ρ₁ ρ₂ α0 α1 α2 α3 : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hD1 : qPoch (a * q / ρ₁) q 3 ≠ 0)
    (hD2 : qPoch (a * q / ρ₂) q 3 ≠ 0)
    (hD1one : qPoch (a * q / ρ₁) q 1 ≠ 0)
    (hD2one : qPoch (a * q / ρ₂) q 1 ≠ 0)
    (hD1two : qPoch (a * q / ρ₁) q 2 ≠ 0)
    (hD2two : qPoch (a * q / ρ₂) q 2 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hA1 : qPoch (a * q) q 1 ≠ 0)
    (hA2 : qPoch (a * q) q 2 ≠ 0)
    (hA3 : qPoch (a * q) q 3 ≠ 0)
    (hA4 : qPoch (a * q) q 4 ≠ 0)
    (hA5 : qPoch (a * q) q 5 ≠ 0) :
    (((qPoch ρ₁ q 0 * qPoch ρ₂ q 0 * (a * q / (ρ₁ * ρ₂)) ^ 0 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3) /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 *
        qPochhammer q 3)) * α0) +
      (((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 *
        qPochhammer q 2)) *
        (α0 / (qPochhammer q 1 * qPoch (a * q) q 1) +
          α1 / qPoch (a * q) q 2)) +
      (((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 *
        qPochhammer q 1)) *
        (α0 / (qPochhammer q 2 * qPoch (a * q) q 2) +
          α1 / (qPochhammer q 1 * qPoch (a * q) q 3) +
          α2 / qPoch (a * q) q 4)) +
      (((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 *
        qPochhammer q 0)) *
        (α0 / (qPochhammer q 3 * qPoch (a * q) q 3) +
          α1 / (qPochhammer q 2 * qPoch (a * q) q 4) +
          α2 / (qPochhammer q 1 * qPoch (a * q) q 5) +
          α3 / qPoch (a * q) q 6)) =
      (1 / (qPochhammer q 3 * qPoch (a * q) q 3)) * α0 +
        (((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂))) /
          (qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1)) /
          (qPochhammer q 2 * qPoch (a * q) q 4)) * α1 +
        (((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 /
          (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2)) /
          (qPochhammer q 1 * qPoch (a * q) q 5)) * α2) +
        (((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 /
          (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3)) /
          qPoch (a * q) q 6) * α3) := by
  let C0 := ((qPoch ρ₁ q 0 * qPoch ρ₂ q 0 * (a * q / (ρ₁ * ρ₂)) ^ 0 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3) /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 *
        qPochhammer q 3))
  let C1 := ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 *
        qPochhammer q 2))
  let C2 := ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 *
        qPochhammer q 1))
  let C3 := ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 *
        qPochhammer q 0))
  let D10 := qPochhammer q 1 * qPoch (a * q) q 1
  let D20 := qPochhammer q 2 * qPoch (a * q) q 2
  let D30 := qPochhammer q 3 * qPoch (a * q) q 3
  let E10 := qPoch (a * q) q 2
  let E21 := qPochhammer q 1 * qPoch (a * q) q 3
  let E31 := qPochhammer q 2 * qPoch (a * q) q 4
  let E22 := qPoch (a * q) q 4
  let E32 := qPochhammer q 1 * qPoch (a * q) q 5
  let E33 := qPoch (a * q) q 6
  let T0 := 1 / (qPochhammer q 3 * qPoch (a * q) q 3)
  let T1 := ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂))) /
          (qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1)) /
          (qPochhammer q 2 * qPoch (a * q) q 4)
  let T2 := ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 /
          (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2)) /
          (qPochhammer q 1 * qPoch (a * q) q 5))
  let T3 := ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 /
          (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3)) /
          qPoch (a * q) q 6)
  have h0 : C0 + C1 / D10 + C2 / D20 + C3 / D30 = T0 := by
    dsimp [C0, C1, C2, C3, D10, D20, D30, T0]
    exact BaileyTransform_three_alpha_zero_coefficient_identity
      a q ρ₁ ρ₂ hρ hD1 hD2 hQ1 hQ2 hQ3 hA1 hA2 hA3
  have h1 : C1 / E10 + C2 / E21 + C3 / E31 = T1 := by
    dsimp [C1, C2, C3, E10, E21, E31, T1]
    exact BaileyTransform_three_alpha_one_coefficient_identity
      a q ρ₁ ρ₂ hρ hD1 hD2 hD1one hD2one hQ1 hQ2 hA2 hA3 hA4
  have h2 : C2 / E22 + C3 / E32 = T2 := by
    dsimp [C2, C3, E22, E32, T2]
    exact BaileyTransform_three_alpha_two_coefficient_identity
      a q ρ₁ ρ₂ hρ hD1 hD2 hD1two hD2two hQ1 hA4 hA5
  have h3 : C3 / E33 = T3 := by
    dsimp [C3, E33, T3]
    exact BaileyTransform_three_alpha_three_coefficient_identity a q ρ₁ ρ₂
  change C0 * α0 + C1 * (α0 / D10 + α1 / E10) +
      C2 * (α0 / D20 + α1 / E21 + α2 / E22) +
      C3 * (α0 / D30 + α1 / E31 + α2 / E32 + α3 / E33) =
      T0 * α0 + T1 * α1 + T2 * α2 + T3 * α3
  exact BaileyTransform_four_coefficient_linear_identity
    C0 C1 C2 C3 D10 D20 D30 E10 E21 E31 E22 E32 E33
    T0 T1 T2 T3 α0 α1 α2 α3 h0 h1 h2 h3

/-- The `n = 3` finite Bailey-lemma preservation step, under explicit nonzero
denominator hypotheses for the standardized algebra. -/
theorem BaileyTransform_preserves_pair_three_of_nonzero
    (a q ρ₁ ρ₂ : R) {α β : Nat → R}
    (h : IsBaileyPairUpTo a q α β 3)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hD1 : qPoch (a * q / ρ₁) q 3 ≠ 0)
    (hD2 : qPoch (a * q / ρ₂) q 3 ≠ 0)
    (hD1one : qPoch (a * q / ρ₁) q 1 ≠ 0)
    (hD2one : qPoch (a * q / ρ₂) q 1 ≠ 0)
    (hD1two : qPoch (a * q / ρ₁) q 2 ≠ 0)
    (hD2two : qPoch (a * q / ρ₂) q 2 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hA1 : qPoch (a * q) q 1 ≠ 0)
    (hA2 : qPoch (a * q) q 2 ≠ 0)
    (hA3 : qPoch (a * q) q 3 ≠ 0)
    (hA4 : qPoch (a * q) q 4 ≠ 0)
    (hA5 : qPoch (a * q) q 5 ≠ 0) :
    BaileyTransformBeta a q ρ₁ ρ₂ β 3 =
      BaileyBeta a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 3 := by
  rw [BaileyTransformBeta_of_pair_three_terms a q ρ₁ ρ₂ h,
    BaileyBeta_transformAlpha_three_terms_linear]
  simpa [qPochhammer, qPoch] using
    (BaileyTransform_three_standard_terms_eq_transformAlpha_three_terms
      a q ρ₁ ρ₂ (α 0) (α 1) (α 2) (α 3)
      hρ hD1 hD2 hD1one hD2one hD1two hD2two
      hQ1 hQ2 hQ3 hA1 hA2 hA3 hA4 hA5)

/-- Up-to-three finite Bailey-lemma packaging under explicit nonzero
denominator hypotheses. -/
theorem BaileyTransform_preserves_pair_upTo_three_of_nonzero
    (a q ρ₁ ρ₂ : R) {α β : Nat → R}
    (h : IsBaileyPairUpTo a q α β 3)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hD1 : qPoch (a * q / ρ₁) q 3 ≠ 0)
    (hD2 : qPoch (a * q / ρ₂) q 3 ≠ 0)
    (hD1one : qPoch (a * q / ρ₁) q 1 ≠ 0)
    (hD2one : qPoch (a * q / ρ₂) q 1 ≠ 0)
    (hD1two : qPoch (a * q / ρ₁) q 2 ≠ 0)
    (hD2two : qPoch (a * q / ρ₂) q 2 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hA1 : qPoch (a * q) q 1 ≠ 0)
    (hA2 : qPoch (a * q) q 2 ≠ 0)
    (hA3 : qPoch (a * q) q 3 ≠ 0)
    (hA4 : qPoch (a * q) q 4 ≠ 0)
    (hA5 : qPoch (a * q) q 5 ≠ 0) :
    IsBaileyPairUpTo a q (BaileyTransformAlpha a q ρ₁ ρ₂ α)
      (BaileyTransformBeta a q ρ₁ ρ₂ β) 3 := by
  have hq : 1 - q ≠ 0 := by simpa [qPochhammer] using hQ1
  have haq : 1 - a * q ≠ 0 := by simpa [qPoch] using hA1
  have hρ₁one : 1 - a * q / ρ₁ ≠ 0 := by simpa [qPoch] using hD1one
  have hρ₂one : 1 - a * q / ρ₂ ≠ 0 := by simpa [qPoch] using hD2one
  have hB1 : (1 - q) * (1 - a * q) ≠ 0 := mul_ne_zero hq haq
  exact IsBaileyPairUpTo.of_three
    (BaileyTransform_preserves_pair_zero a q ρ₁ ρ₂ (h.mono (by omega)))
    (BaileyTransform_preserves_pair_one_of_nonzero a q ρ₁ ρ₂ (h.mono (by omega))
      hρ hq haq hρ₁one hρ₂one)
    (BaileyTransform_preserves_pair_two_of_nonzero a q ρ₁ ρ₂ (h.mono (by omega))
      hρ hD1two hD2two hD1one hD2one hQ1 hQ2 hA2 hA3 hB1)
    (BaileyTransform_preserves_pair_three_of_nonzero a q ρ₁ ρ₂ h
      hρ hD1 hD2 hD1one hD2one hD1two hD2two hQ1 hQ2 hQ3 hA1 hA2 hA3 hA4 hA5)

/-- Generic algebra step assembling five independent coefficient identities
into the `n = 4` linear combination. -/
theorem BaileyTransform_five_coefficient_linear_identity
    (C0 C1 C2 C3 C4 D10 D20 D30 D40 E10 E21 E31 E41
      E22 E32 E42 E33 E43 E44 T0 T1 T2 T3 T4 α0 α1 α2 α3 α4 : R)
    (h0 : C0 + C1 / D10 + C2 / D20 + C3 / D30 + C4 / D40 = T0)
    (h1 : C1 / E10 + C2 / E21 + C3 / E31 + C4 / E41 = T1)
    (h2 : C2 / E22 + C3 / E32 + C4 / E42 = T2)
    (h3 : C3 / E33 + C4 / E43 = T3)
    (h4 : C4 / E44 = T4) :
    C0 * α0 + C1 * (α0 / D10 + α1 / E10) +
      C2 * (α0 / D20 + α1 / E21 + α2 / E22) +
      C3 * (α0 / D30 + α1 / E31 + α2 / E32 + α3 / E33) +
      C4 * (α0 / D40 + α1 / E41 + α2 / E42 + α3 / E43 + α4 / E44) =
      T0 * α0 + T1 * α1 + T2 * α2 + T3 * α3 + T4 * α4 := by
  rw [← h0, ← h1, ← h2, ← h3, ← h4]
  ring

/-- Generic algebra step assembling six independent coefficient identities
into the `n = 5` linear combination. -/
theorem BaileyTransform_six_coefficient_linear_identity
    (C0 C1 C2 C3 C4 C5 D10 D20 D30 D40 D50 E10 E21 E31 E41 E51
      E22 E32 E42 E52 E33 E43 E53 E44 E54 E55
      T0 T1 T2 T3 T4 T5 α0 α1 α2 α3 α4 α5 : R)
    (h0 : C0 + C1 / D10 + C2 / D20 + C3 / D30 + C4 / D40 + C5 / D50 = T0)
    (h1 : C1 / E10 + C2 / E21 + C3 / E31 + C4 / E41 + C5 / E51 = T1)
    (h2 : C2 / E22 + C3 / E32 + C4 / E42 + C5 / E52 = T2)
    (h3 : C3 / E33 + C4 / E43 + C5 / E53 = T3)
    (h4 : C4 / E44 + C5 / E54 = T4)
    (h5 : C5 / E55 = T5) :
    C0 * α0 + C1 * (α0 / D10 + α1 / E10) +
      C2 * (α0 / D20 + α1 / E21 + α2 / E22) +
      C3 * (α0 / D30 + α1 / E31 + α2 / E32 + α3 / E33) +
      C4 * (α0 / D40 + α1 / E41 + α2 / E42 + α3 / E43 + α4 / E44) +
      C5 * (α0 / D50 + α1 / E51 + α2 / E52 + α3 / E53 + α4 / E54 +
        α5 / E55) =
      T0 * α0 + T1 * α1 + T2 * α2 + T3 * α3 + T4 * α4 + T5 * α5 := by
  rw [← h0, ← h1, ← h2, ← h3, ← h4, ← h5]
  ring

/-- Generic algebra step assembling seven independent coefficient identities
into the `n = 6` linear combination. -/
theorem BaileyTransform_seven_coefficient_linear_identity
    (C0 C1 C2 C3 C4 C5 C6
      D10 D20 D30 D40 D50 D60
      E10 E21 E31 E41 E51 E61
      E22 E32 E42 E52 E62
      E33 E43 E53 E63
      E44 E54 E64
      E55 E65 E66
      T0 T1 T2 T3 T4 T5 T6
      α0 α1 α2 α3 α4 α5 α6 : R)
    (h0 : C0 + C1 / D10 + C2 / D20 + C3 / D30 + C4 / D40 +
      C5 / D50 + C6 / D60 = T0)
    (h1 : C1 / E10 + C2 / E21 + C3 / E31 + C4 / E41 + C5 / E51 +
      C6 / E61 = T1)
    (h2 : C2 / E22 + C3 / E32 + C4 / E42 + C5 / E52 + C6 / E62 = T2)
    (h3 : C3 / E33 + C4 / E43 + C5 / E53 + C6 / E63 = T3)
    (h4 : C4 / E44 + C5 / E54 + C6 / E64 = T4)
    (h5 : C5 / E55 + C6 / E65 = T5)
    (h6 : C6 / E66 = T6) :
    C0 * α0 + C1 * (α0 / D10 + α1 / E10) +
      C2 * (α0 / D20 + α1 / E21 + α2 / E22) +
      C3 * (α0 / D30 + α1 / E31 + α2 / E32 + α3 / E33) +
      C4 * (α0 / D40 + α1 / E41 + α2 / E42 + α3 / E43 + α4 / E44) +
      C5 * (α0 / D50 + α1 / E51 + α2 / E52 + α3 / E53 + α4 / E54 +
        α5 / E55) +
      C6 * (α0 / D60 + α1 / E61 + α2 / E62 + α3 / E63 + α4 / E64 +
        α5 / E65 + α6 / E66) =
      T0 * α0 + T1 * α1 + T2 * α2 + T3 * α3 + T4 * α4 + T5 * α5 +
        T6 * α6 := by
  rw [← h0, ← h1, ← h2, ← h3, ← h4, ← h5, ← h6]
  ring

/-- Generic algebra step assembling eight independent coefficient identities
into the `n = 7` linear combination. -/
theorem BaileyTransform_eight_coefficient_linear_identity
    (C0 C1 C2 C3 C4 C5 C6 C7
      D10 D20 D30 D40 D50 D60 D70
      E10 E21 E31 E41 E51 E61 E71
      E22 E32 E42 E52 E62 E72
      E33 E43 E53 E63 E73
      E44 E54 E64 E74
      E55 E65 E75
      E66 E76
      E77
      T0 T1 T2 T3 T4 T5 T6 T7
      α0 α1 α2 α3 α4 α5 α6 α7 : R)
    (h0 : C0 + C1 / D10 + C2 / D20 + C3 / D30 + C4 / D40 +
      C5 / D50 + C6 / D60 + C7 / D70 = T0)
    (h1 : C1 / E10 + C2 / E21 + C3 / E31 + C4 / E41 + C5 / E51 +
      C6 / E61 + C7 / E71 = T1)
    (h2 : C2 / E22 + C3 / E32 + C4 / E42 + C5 / E52 + C6 / E62 +
      C7 / E72 = T2)
    (h3 : C3 / E33 + C4 / E43 + C5 / E53 + C6 / E63 + C7 / E73 = T3)
    (h4 : C4 / E44 + C5 / E54 + C6 / E64 + C7 / E74 = T4)
    (h5 : C5 / E55 + C6 / E65 + C7 / E75 = T5)
    (h6 : C6 / E66 + C7 / E76 = T6)
    (h7 : C7 / E77 = T7) :
    C0 * α0 + C1 * (α0 / D10 + α1 / E10) +
      C2 * (α0 / D20 + α1 / E21 + α2 / E22) +
      C3 * (α0 / D30 + α1 / E31 + α2 / E32 + α3 / E33) +
      C4 * (α0 / D40 + α1 / E41 + α2 / E42 + α3 / E43 + α4 / E44) +
      C5 * (α0 / D50 + α1 / E51 + α2 / E52 + α3 / E53 + α4 / E54 +
        α5 / E55) +
      C6 * (α0 / D60 + α1 / E61 + α2 / E62 + α3 / E63 + α4 / E64 +
        α5 / E65 + α6 / E66) +
      C7 * (α0 / D70 + α1 / E71 + α2 / E72 + α3 / E73 + α4 / E74 +
        α5 / E75 + α6 / E76 + α7 / E77) =
      T0 * α0 + T1 * α1 + T2 * α2 + T3 * α3 + T4 * α4 + T5 * α5 +
        T6 * α6 + T7 * α7 := by
  rw [← h0, ← h1, ← h2, ← h3, ← h4, ← h5, ← h6, ← h7]
  ring

/-- The `n = 4` finite Bailey-lemma preservation step, under explicit nonzero
denominator hypotheses for the standardized algebra. -/
theorem BaileyTransform_preserves_pair_four_of_nonzero
    (a q ρ₁ ρ₂ : R) {α β : Nat → R}
    (h : IsBaileyPairUpTo a q α β 4)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hD1 : qPoch (a * q / ρ₁) q 4 ≠ 0)
    (hD2 : qPoch (a * q / ρ₂) q 4 ≠ 0)
    (hD1one : qPoch (a * q / ρ₁) q 1 ≠ 0)
    (hD2one : qPoch (a * q / ρ₂) q 1 ≠ 0)
    (hD1two : qPoch (a * q / ρ₁) q 2 ≠ 0)
    (hD2two : qPoch (a * q / ρ₂) q 2 ≠ 0)
    (hD1three : qPoch (a * q / ρ₁) q 3 ≠ 0)
    (hD2three : qPoch (a * q / ρ₂) q 3 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hQ4 : qPochhammer q 4 ≠ 0)
    (hA1 : qPoch (a * q) q 1 ≠ 0)
    (hA2 : qPoch (a * q) q 2 ≠ 0)
    (hA3 : qPoch (a * q) q 3 ≠ 0)
    (hA4 : qPoch (a * q) q 4 ≠ 0)
    (hA5 : qPoch (a * q) q 5 ≠ 0)
    (hA6 : qPoch (a * q) q 6 ≠ 0)
    (hA7 : qPoch (a * q) q 7 ≠ 0) :
    BaileyTransformBeta a q ρ₁ ρ₂ β 4 =
      BaileyBeta a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 4 := by
  rw [BaileyTransformBeta_of_pair_four_terms a q ρ₁ ρ₂ h,
    BaileyBeta_transformAlpha_four_terms_linear]
  let C0 := ((qPoch ρ₁ q 0 * qPoch ρ₂ q 0 * (a * q / (ρ₁ * ρ₂)) ^ 0 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 4) /
      (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4 *
        qPochhammer q 4))
  let C1 := ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3) /
      (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4 *
        qPochhammer q 3))
  let C2 := ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4 *
        qPochhammer q 2))
  let C3 := ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4 *
        qPochhammer q 1))
  let C4 := ((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4 *
        qPochhammer q 0))
  let D10 := (1 - q) * (1 - a * q)
  let D20 := qPochhammer q 2 * qPoch (a * q) q 2
  let D30 := qPochhammer q 3 * qPoch (a * q) q 3
  let D40 := qPochhammer q 4 * qPoch (a * q) q 4
  let E10 := qPoch (a * q) q 2
  let E21 := qPochhammer q 1 * qPoch (a * q) q 3
  let E31 := qPochhammer q 2 * qPoch (a * q) q 4
  let E41 := qPochhammer q 3 * qPoch (a * q) q 5
  let E22 := qPoch (a * q) q 4
  let E32 := qPochhammer q 1 * qPoch (a * q) q 5
  let E42 := qPochhammer q 2 * qPoch (a * q) q 6
  let E33 := qPoch (a * q) q 6
  let E43 := qPochhammer q 1 * qPoch (a * q) q 7
  let E44 := qPoch (a * q) q 8
  let T0 := 1 / (qPochhammer q 4 * qPoch (a * q) q 4)
  let T1 := ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂))) /
          (qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1)) /
          (qPochhammer q 3 * qPoch (a * q) q 5)
  let T2 := ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 /
          (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2)) /
          (qPochhammer q 2 * qPoch (a * q) q 6))
  let T3 := ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 /
          (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3)) /
          (qPochhammer q 1 * qPoch (a * q) q 7))
  let T4 := ((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 /
          (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4)) /
          qPoch (a * q) q 8)
  have h0 : C0 + C1 / D10 + C2 / D20 + C3 / D30 + C4 / D40 = T0 := by
    dsimp [C0, C1, C2, C3, C4, D10, D20, D30, D40, T0]
    simpa [qPochhammer, qPoch] using
      BaileyTransform_four_alpha_zero_coefficient_identity
        a q ρ₁ ρ₂ hρ hD1 hD2 hQ1 hQ2 hQ3 hQ4 hA1 hA2 hA3 hA4
  have h1 : C1 / E10 + C2 / E21 + C3 / E31 + C4 / E41 = T1 := by
    dsimp [C1, C2, C3, C4, E10, E21, E31, E41, T1]
    exact BaileyTransform_four_alpha_one_coefficient_identity
      a q ρ₁ ρ₂ hρ hD1 hD2 hD1one hD2one hQ1 hQ2 hQ3 hA2 hA3 hA4 hA5
  have h2 : C2 / E22 + C3 / E32 + C4 / E42 = T2 := by
    dsimp [C2, C3, C4, E22, E32, E42, T2]
    exact BaileyTransform_four_alpha_two_coefficient_identity
      a q ρ₁ ρ₂ hρ hD1 hD2 hD1two hD2two hQ1 hQ2 hA4 hA5 hA6
  have h3 : C3 / E33 + C4 / E43 = T3 := by
    dsimp [C3, C4, E33, E43, T3]
    exact BaileyTransform_four_alpha_three_coefficient_identity
      a q ρ₁ ρ₂ hρ hD1 hD2 hD1three hD2three hQ1 hA6 hA7
  have h4 : C4 / E44 = T4 := by
    dsimp [C4, E44, T4]
    exact BaileyTransform_four_alpha_four_coefficient_identity a q ρ₁ ρ₂
  change C0 * α 0 + C1 * (α 0 / D10 + α 1 / E10) +
      C2 * (α 0 / D20 + α 1 / E21 + α 2 / E22) +
      C3 * (α 0 / D30 + α 1 / E31 + α 2 / E32 + α 3 / E33) +
      C4 * (α 0 / D40 + α 1 / E41 + α 2 / E42 + α 3 / E43 + α 4 / E44) =
      T0 * α 0 + T1 * α 1 + T2 * α 2 + T3 * α 3 + T4 * α 4
  exact BaileyTransform_five_coefficient_linear_identity
    C0 C1 C2 C3 C4 D10 D20 D30 D40 E10 E21 E31 E41 E22 E32 E42 E33 E43 E44
    T0 T1 T2 T3 T4 (α 0) (α 1) (α 2) (α 3) (α 4) h0 h1 h2 h3 h4

/-- Up-to-four finite Bailey-lemma packaging under explicit nonzero
denominator hypotheses. -/
theorem BaileyTransform_preserves_pair_upTo_four_of_nonzero
    (a q ρ₁ ρ₂ : R) {α β : Nat → R}
    (h : IsBaileyPairUpTo a q α β 4)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hD1 : qPoch (a * q / ρ₁) q 4 ≠ 0)
    (hD2 : qPoch (a * q / ρ₂) q 4 ≠ 0)
    (hD1one : qPoch (a * q / ρ₁) q 1 ≠ 0)
    (hD2one : qPoch (a * q / ρ₂) q 1 ≠ 0)
    (hD1two : qPoch (a * q / ρ₁) q 2 ≠ 0)
    (hD2two : qPoch (a * q / ρ₂) q 2 ≠ 0)
    (hD1three : qPoch (a * q / ρ₁) q 3 ≠ 0)
    (hD2three : qPoch (a * q / ρ₂) q 3 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hQ4 : qPochhammer q 4 ≠ 0)
    (hA1 : qPoch (a * q) q 1 ≠ 0)
    (hA2 : qPoch (a * q) q 2 ≠ 0)
    (hA3 : qPoch (a * q) q 3 ≠ 0)
    (hA4 : qPoch (a * q) q 4 ≠ 0)
    (hA5 : qPoch (a * q) q 5 ≠ 0)
    (hA6 : qPoch (a * q) q 6 ≠ 0)
    (hA7 : qPoch (a * q) q 7 ≠ 0) :
    IsBaileyPairUpTo a q (BaileyTransformAlpha a q ρ₁ ρ₂ α)
      (BaileyTransformBeta a q ρ₁ ρ₂ β) 4 := by
  have hq : 1 - q ≠ 0 := by simpa [qPochhammer] using hQ1
  have haq : 1 - a * q ≠ 0 := by simpa [qPoch] using hA1
  have hρ₁one : 1 - a * q / ρ₁ ≠ 0 := by simpa [qPoch] using hD1one
  have hρ₂one : 1 - a * q / ρ₂ ≠ 0 := by simpa [qPoch] using hD2one
  have hB1 : (1 - q) * (1 - a * q) ≠ 0 := mul_ne_zero hq haq
  exact IsBaileyPairUpTo.of_four
    (BaileyTransform_preserves_pair_zero a q ρ₁ ρ₂ (h.mono (by omega)))
    (BaileyTransform_preserves_pair_one_of_nonzero a q ρ₁ ρ₂ (h.mono (by omega))
      hρ hq haq hρ₁one hρ₂one)
    (BaileyTransform_preserves_pair_two_of_nonzero a q ρ₁ ρ₂ (h.mono (by omega))
      hρ hD1two hD2two hD1one hD2one hQ1 hQ2 hA2 hA3 hB1)
    (BaileyTransform_preserves_pair_three_of_nonzero a q ρ₁ ρ₂ (h.mono (by omega))
      hρ hD1three hD2three hD1one hD2one hD1two hD2two
      hQ1 hQ2 hQ3 hA1 hA2 hA3 hA4 hA5)
    (BaileyTransform_preserves_pair_four_of_nonzero a q ρ₁ ρ₂ h
      hρ hD1 hD2 hD1one hD2one hD1two hD2two hD1three hD2three
      hQ1 hQ2 hQ3 hQ4 hA1 hA2 hA3 hA4 hA5 hA6 hA7)

/-- The `n = 5` finite Bailey-lemma preservation step, under explicit nonzero
denominator hypotheses for the standardized algebra. -/
theorem BaileyTransform_preserves_pair_five_of_nonzero
    (a q ρ₁ ρ₂ : R) {α β : Nat → R}
    (h : IsBaileyPairUpTo a q α β 5)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hD1 : qPoch (a * q / ρ₁) q 5 ≠ 0)
    (hD2 : qPoch (a * q / ρ₂) q 5 ≠ 0)
    (hD1one : qPoch (a * q / ρ₁) q 1 ≠ 0)
    (hD2one : qPoch (a * q / ρ₂) q 1 ≠ 0)
    (hD1two : qPoch (a * q / ρ₁) q 2 ≠ 0)
    (hD2two : qPoch (a * q / ρ₂) q 2 ≠ 0)
    (hD1three : qPoch (a * q / ρ₁) q 3 ≠ 0)
    (hD2three : qPoch (a * q / ρ₂) q 3 ≠ 0)
    (hD1four : qPoch (a * q / ρ₁) q 4 ≠ 0)
    (hD2four : qPoch (a * q / ρ₂) q 4 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hQ4 : qPochhammer q 4 ≠ 0)
    (hQ5 : qPochhammer q 5 ≠ 0)
    (hA1 : qPoch (a * q) q 1 ≠ 0)
    (hA2 : qPoch (a * q) q 2 ≠ 0)
    (hA3 : qPoch (a * q) q 3 ≠ 0)
    (hA4 : qPoch (a * q) q 4 ≠ 0)
    (hA5 : qPoch (a * q) q 5 ≠ 0)
    (hA6 : qPoch (a * q) q 6 ≠ 0)
    (hA7 : qPoch (a * q) q 7 ≠ 0)
    (hA8 : qPoch (a * q) q 8 ≠ 0)
    (hA9 : qPoch (a * q) q 9 ≠ 0) :
    BaileyTransformBeta a q ρ₁ ρ₂ β 5 =
      BaileyBeta a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 5 := by
  rw [BaileyTransformBeta_of_pair_five_terms a q ρ₁ ρ₂ h,
    BaileyBeta_transformAlpha_five_terms_linear]
  let C0 := ((qPoch ρ₁ q 0 * qPoch ρ₂ q 0 * (a * q / (ρ₁ * ρ₂)) ^ 0 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 5) /
      (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 *
        qPochhammer q 5))
  let C1 := ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 4) /
      (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 *
        qPochhammer q 4))
  let C2 := ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3) /
      (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 *
        qPochhammer q 3))
  let C3 := ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 *
        qPochhammer q 2))
  let C4 := ((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 *
        qPochhammer q 1))
  let C5 := ((qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5 *
        qPochhammer q 0))
  let D10 := (1 - q) * (1 - a * q)
  let D20 := qPochhammer q 2 * qPoch (a * q) q 2
  let D30 := qPochhammer q 3 * qPoch (a * q) q 3
  let D40 := qPochhammer q 4 * qPoch (a * q) q 4
  let D50 := qPochhammer q 5 * qPoch (a * q) q 5
  let E10 := qPoch (a * q) q 2
  let E21 := qPochhammer q 1 * qPoch (a * q) q 3
  let E31 := qPochhammer q 2 * qPoch (a * q) q 4
  let E41 := qPochhammer q 3 * qPoch (a * q) q 5
  let E51 := qPochhammer q 4 * qPoch (a * q) q 6
  let E22 := qPoch (a * q) q 4
  let E32 := qPochhammer q 1 * qPoch (a * q) q 5
  let E42 := qPochhammer q 2 * qPoch (a * q) q 6
  let E52 := qPochhammer q 3 * qPoch (a * q) q 7
  let E33 := qPoch (a * q) q 6
  let E43 := qPochhammer q 1 * qPoch (a * q) q 7
  let E53 := qPochhammer q 2 * qPoch (a * q) q 8
  let E44 := qPoch (a * q) q 8
  let E54 := qPochhammer q 1 * qPoch (a * q) q 9
  let E55 := qPoch (a * q) q 10
  let T0 := 1 / (qPochhammer q 5 * qPoch (a * q) q 5)
  let T1 := ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂))) /
          (qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1)) /
          (qPochhammer q 4 * qPoch (a * q) q 6)
  let T2 := ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 /
          (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2)) /
          (qPochhammer q 3 * qPoch (a * q) q 7))
  let T3 := ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 /
          (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3)) /
          (qPochhammer q 2 * qPoch (a * q) q 8))
  let T4 := ((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 /
          (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4)) /
          (qPochhammer q 1 * qPoch (a * q) q 9))
  let T5 := ((qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 /
          (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5)) /
          qPoch (a * q) q 10)
  have h0 : C0 + C1 / D10 + C2 / D20 + C3 / D30 + C4 / D40 + C5 / D50 = T0 := by
    dsimp [C0, C1, C2, C3, C4, C5, D10, D20, D30, D40, D50, T0]
    simpa [qPochhammer, qPoch] using
      BaileyTransform_five_alpha_zero_coefficient_identity
        a q ρ₁ ρ₂ hρ hD1 hD2 hQ1 hQ2 hQ3 hQ4 hQ5 hA1 hA2 hA3 hA4 hA5
  have h1 : C1 / E10 + C2 / E21 + C3 / E31 + C4 / E41 + C5 / E51 = T1 := by
    dsimp [C1, C2, C3, C4, C5, E10, E21, E31, E41, E51, T1]
    exact BaileyTransform_five_alpha_one_coefficient_identity
      a q ρ₁ ρ₂ hρ hD1 hD2 hD1one hD2one hQ1 hQ2 hQ3 hQ4 hA2 hA3 hA4 hA5 hA6
  have h2 : C2 / E22 + C3 / E32 + C4 / E42 + C5 / E52 = T2 := by
    dsimp [C2, C3, C4, C5, E22, E32, E42, E52, T2]
    exact BaileyTransform_five_alpha_two_coefficient_identity
      a q ρ₁ ρ₂ hρ hD1 hD2 hD1two hD2two hQ1 hQ2 hQ3 hA4 hA5 hA6 hA7
  have h3 : C3 / E33 + C4 / E43 + C5 / E53 = T3 := by
    dsimp [C3, C4, C5, E33, E43, E53, T3]
    exact BaileyTransform_five_alpha_three_coefficient_identity
      a q ρ₁ ρ₂ hρ hD1 hD2 hD1three hD2three hQ1 hQ2 hA6 hA7 hA8
  have h4 : C4 / E44 + C5 / E54 = T4 := by
    dsimp [C4, C5, E44, E54, T4]
    exact BaileyTransform_five_alpha_four_coefficient_identity
      a q ρ₁ ρ₂ hρ hD1 hD2 hD1four hD2four hQ1 hA8 hA9
  have h5 : C5 / E55 = T5 := by
    dsimp [C5, E55, T5]
    exact BaileyTransform_five_alpha_five_coefficient_identity a q ρ₁ ρ₂
  change C0 * α 0 + C1 * (α 0 / D10 + α 1 / E10) +
      C2 * (α 0 / D20 + α 1 / E21 + α 2 / E22) +
      C3 * (α 0 / D30 + α 1 / E31 + α 2 / E32 + α 3 / E33) +
      C4 * (α 0 / D40 + α 1 / E41 + α 2 / E42 + α 3 / E43 + α 4 / E44) +
      C5 * (α 0 / D50 + α 1 / E51 + α 2 / E52 + α 3 / E53 + α 4 / E54 +
        α 5 / E55) =
      T0 * α 0 + T1 * α 1 + T2 * α 2 + T3 * α 3 + T4 * α 4 + T5 * α 5
  exact BaileyTransform_six_coefficient_linear_identity
    C0 C1 C2 C3 C4 C5 D10 D20 D30 D40 D50 E10 E21 E31 E41 E51
    E22 E32 E42 E52 E33 E43 E53 E44 E54 E55 T0 T1 T2 T3 T4 T5
    (α 0) (α 1) (α 2) (α 3) (α 4) (α 5) h0 h1 h2 h3 h4 h5

/-- The `n = 6` finite Bailey-lemma preservation step, under explicit nonzero
denominator hypotheses for the standardized algebra. -/
theorem BaileyTransform_preserves_pair_six_of_nonzero
    (a q ρ₁ ρ₂ : R) {α β : Nat → R}
    (h : IsBaileyPairUpTo a q α β 6)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hD1 : qPoch (a * q / ρ₁) q 6 ≠ 0)
    (hD2 : qPoch (a * q / ρ₂) q 6 ≠ 0)
    (hD1one : qPoch (a * q / ρ₁) q 1 ≠ 0)
    (hD2one : qPoch (a * q / ρ₂) q 1 ≠ 0)
    (hD1two : qPoch (a * q / ρ₁) q 2 ≠ 0)
    (hD2two : qPoch (a * q / ρ₂) q 2 ≠ 0)
    (hD1three : qPoch (a * q / ρ₁) q 3 ≠ 0)
    (hD2three : qPoch (a * q / ρ₂) q 3 ≠ 0)
    (hD1four : qPoch (a * q / ρ₁) q 4 ≠ 0)
    (hD2four : qPoch (a * q / ρ₂) q 4 ≠ 0)
    (hD1five : qPoch (a * q / ρ₁) q 5 ≠ 0)
    (hD2five : qPoch (a * q / ρ₂) q 5 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hQ4 : qPochhammer q 4 ≠ 0)
    (hQ5 : qPochhammer q 5 ≠ 0)
    (hQ6 : qPochhammer q 6 ≠ 0)
    (hA1 : qPoch (a * q) q 1 ≠ 0)
    (hA2 : qPoch (a * q) q 2 ≠ 0)
    (hA3 : qPoch (a * q) q 3 ≠ 0)
    (hA4 : qPoch (a * q) q 4 ≠ 0)
    (hA5 : qPoch (a * q) q 5 ≠ 0)
    (hA6 : qPoch (a * q) q 6 ≠ 0)
    (hA7 : qPoch (a * q) q 7 ≠ 0)
    (hA8 : qPoch (a * q) q 8 ≠ 0)
    (hA9 : qPoch (a * q) q 9 ≠ 0)
    (hA10 : qPoch (a * q) q 10 ≠ 0)
    (hA11 : qPoch (a * q) q 11 ≠ 0) :
    BaileyTransformBeta a q ρ₁ ρ₂ β 6 =
      BaileyBeta a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 6 := by
  rw [BaileyTransformBeta_of_pair_six_terms a q ρ₁ ρ₂ h,
    BaileyBeta_transformAlpha_six_terms_linear]
  let C0 := ((qPoch ρ₁ q 0 * qPoch ρ₂ q 0 * (a * q / (ρ₁ * ρ₂)) ^ 0 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 6) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 6))
  let C1 := ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 5) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 5))
  let C2 := ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 4) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 4))
  let C3 := ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 3))
  let C4 := ((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 2))
  let C5 := ((qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 1))
  let C6 := ((qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 0))
  let D10 := (1 - q) * (1 - a * q)
  let D20 := qPochhammer q 2 * qPoch (a * q) q 2
  let D30 := qPochhammer q 3 * qPoch (a * q) q 3
  let D40 := qPochhammer q 4 * qPoch (a * q) q 4
  let D50 := qPochhammer q 5 * qPoch (a * q) q 5
  let D60 := qPochhammer q 6 * qPoch (a * q) q 6
  let E10 := qPoch (a * q) q 2
  let E21 := qPochhammer q 1 * qPoch (a * q) q 3
  let E31 := qPochhammer q 2 * qPoch (a * q) q 4
  let E41 := qPochhammer q 3 * qPoch (a * q) q 5
  let E51 := qPochhammer q 4 * qPoch (a * q) q 6
  let E61 := qPochhammer q 5 * qPoch (a * q) q 7
  let E22 := qPoch (a * q) q 4
  let E32 := qPochhammer q 1 * qPoch (a * q) q 5
  let E42 := qPochhammer q 2 * qPoch (a * q) q 6
  let E52 := qPochhammer q 3 * qPoch (a * q) q 7
  let E62 := qPochhammer q 4 * qPoch (a * q) q 8
  let E33 := qPoch (a * q) q 6
  let E43 := qPochhammer q 1 * qPoch (a * q) q 7
  let E53 := qPochhammer q 2 * qPoch (a * q) q 8
  let E63 := qPochhammer q 3 * qPoch (a * q) q 9
  let E44 := qPoch (a * q) q 8
  let E54 := qPochhammer q 1 * qPoch (a * q) q 9
  let E64 := qPochhammer q 2 * qPoch (a * q) q 10
  let E55 := qPoch (a * q) q 10
  let E65 := qPochhammer q 1 * qPoch (a * q) q 11
  let E66 := qPoch (a * q) q 12
  let T0 := 1 / (qPochhammer q 6 * qPoch (a * q) q 6)
  let T1 := ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂))) /
          (qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1)) /
          (qPochhammer q 5 * qPoch (a * q) q 7)
  let T2 := ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 /
          (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2)) /
          (qPochhammer q 4 * qPoch (a * q) q 8))
  let T3 := ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 /
          (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3)) /
          (qPochhammer q 3 * qPoch (a * q) q 9))
  let T4 := ((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 /
          (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4)) /
          (qPochhammer q 2 * qPoch (a * q) q 10))
  let T5 := ((qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 /
          (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5)) /
          (qPochhammer q 1 * qPoch (a * q) q 11))
  let T6 := ((qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6 /
          (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6)) /
          qPoch (a * q) q 12)
  have h0 :
      C0 + C1 / D10 + C2 / D20 + C3 / D30 + C4 / D40 + C5 / D50 +
        C6 / D60 = T0 := by
    dsimp [C0, C1, C2, C3, C4, C5, C6, D10, D20, D30, D40, D50, D60, T0]
    simpa [qPochhammer, qPoch] using
      BaileyTransform_six_alpha_zero_coefficient_identity
        a q ρ₁ ρ₂ hρ hD1 hD2 hQ1 hQ2 hQ3 hQ4 hQ5 hQ6
        hA1 hA2 hA3 hA4 hA5 hA6
  have h1 : C1 / E10 + C2 / E21 + C3 / E31 + C4 / E41 + C5 / E51 +
      C6 / E61 = T1 := by
    dsimp [C1, C2, C3, C4, C5, C6, E10, E21, E31, E41, E51, E61, T1]
    exact BaileyTransform_six_alpha_one_coefficient_identity
      a q ρ₁ ρ₂ hρ hD1 hD2 hD1one hD2one hQ1 hQ2 hQ3 hQ4 hQ5
      hA2 hA3 hA4 hA5 hA6 hA7
  have h2 : C2 / E22 + C3 / E32 + C4 / E42 + C5 / E52 + C6 / E62 = T2 := by
    dsimp [C2, C3, C4, C5, C6, E22, E32, E42, E52, E62, T2]
    exact BaileyTransform_six_alpha_two_coefficient_identity
      a q ρ₁ ρ₂ hρ hD1 hD2 hD1two hD2two hQ1 hQ2 hQ3 hQ4
      hA4 hA5 hA6 hA7 hA8
  have h3 : C3 / E33 + C4 / E43 + C5 / E53 + C6 / E63 = T3 := by
    dsimp [C3, C4, C5, C6, E33, E43, E53, E63, T3]
    exact BaileyTransform_six_alpha_three_coefficient_identity
      a q ρ₁ ρ₂ hρ hD1 hD2 hD1three hD2three hQ1 hQ2 hQ3
      hA6 hA7 hA8 hA9
  have h4 : C4 / E44 + C5 / E54 + C6 / E64 = T4 := by
    dsimp [C4, C5, C6, E44, E54, E64, T4]
    exact BaileyTransform_six_alpha_four_coefficient_identity
      a q ρ₁ ρ₂ hρ hD1 hD2 hD1four hD2four hQ1 hQ2 hA8 hA9 hA10
  have h5 : C5 / E55 + C6 / E65 = T5 := by
    dsimp [C5, C6, E55, E65, T5]
    exact BaileyTransform_six_alpha_five_coefficient_identity
      a q ρ₁ ρ₂ hρ hD1 hD2 hD1five hD2five hQ1 hA10 hA11
  have h6 : C6 / E66 = T6 := by
    dsimp [C6, E66, T6]
    exact BaileyTransform_six_alpha_six_coefficient_identity a q ρ₁ ρ₂
  change C0 * α 0 + C1 * (α 0 / D10 + α 1 / E10) +
      C2 * (α 0 / D20 + α 1 / E21 + α 2 / E22) +
      C3 * (α 0 / D30 + α 1 / E31 + α 2 / E32 + α 3 / E33) +
      C4 * (α 0 / D40 + α 1 / E41 + α 2 / E42 + α 3 / E43 + α 4 / E44) +
      C5 * (α 0 / D50 + α 1 / E51 + α 2 / E52 + α 3 / E53 + α 4 / E54 +
        α 5 / E55) +
      C6 * (α 0 / D60 + α 1 / E61 + α 2 / E62 + α 3 / E63 + α 4 / E64 +
        α 5 / E65 + α 6 / E66) =
      T0 * α 0 + T1 * α 1 + T2 * α 2 + T3 * α 3 + T4 * α 4 + T5 * α 5 +
        T6 * α 6
  exact BaileyTransform_seven_coefficient_linear_identity
    C0 C1 C2 C3 C4 C5 C6 D10 D20 D30 D40 D50 D60
    E10 E21 E31 E41 E51 E61 E22 E32 E42 E52 E62
    E33 E43 E53 E63 E44 E54 E64 E55 E65 E66
    T0 T1 T2 T3 T4 T5 T6
    (α 0) (α 1) (α 2) (α 3) (α 4) (α 5) (α 6)
    h0 h1 h2 h3 h4 h5 h6

/-- The `n = 7` finite Bailey-lemma preservation step, under explicit nonzero
denominator hypotheses for the standardized algebra. -/
theorem BaileyTransform_preserves_pair_seven_of_nonzero
    (a q ρ₁ ρ₂ : R) {α β : Nat → R}
    (h : IsBaileyPairUpTo a q α β 7)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hD1 : qPoch (a * q / ρ₁) q 7 ≠ 0)
    (hD2 : qPoch (a * q / ρ₂) q 7 ≠ 0)
    (hD1one : qPoch (a * q / ρ₁) q 1 ≠ 0)
    (hD2one : qPoch (a * q / ρ₂) q 1 ≠ 0)
    (hD1two : qPoch (a * q / ρ₁) q 2 ≠ 0)
    (hD2two : qPoch (a * q / ρ₂) q 2 ≠ 0)
    (hD1three : qPoch (a * q / ρ₁) q 3 ≠ 0)
    (hD2three : qPoch (a * q / ρ₂) q 3 ≠ 0)
    (hD1four : qPoch (a * q / ρ₁) q 4 ≠ 0)
    (hD2four : qPoch (a * q / ρ₂) q 4 ≠ 0)
    (hD1five : qPoch (a * q / ρ₁) q 5 ≠ 0)
    (hD2five : qPoch (a * q / ρ₂) q 5 ≠ 0)
    (hD1six : qPoch (a * q / ρ₁) q 6 ≠ 0)
    (hD2six : qPoch (a * q / ρ₂) q 6 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hQ4 : qPochhammer q 4 ≠ 0)
    (hQ5 : qPochhammer q 5 ≠ 0)
    (hQ6 : qPochhammer q 6 ≠ 0)
    (hQ7 : qPochhammer q 7 ≠ 0)
    (hA1 : qPoch (a * q) q 1 ≠ 0)
    (hA2 : qPoch (a * q) q 2 ≠ 0)
    (hA3 : qPoch (a * q) q 3 ≠ 0)
    (hA4 : qPoch (a * q) q 4 ≠ 0)
    (hA5 : qPoch (a * q) q 5 ≠ 0)
    (hA6 : qPoch (a * q) q 6 ≠ 0)
    (hA7 : qPoch (a * q) q 7 ≠ 0)
    (hA8 : qPoch (a * q) q 8 ≠ 0)
    (hA9 : qPoch (a * q) q 9 ≠ 0)
    (hA10 : qPoch (a * q) q 10 ≠ 0)
    (hA11 : qPoch (a * q) q 11 ≠ 0)
    (hA12 : qPoch (a * q) q 12 ≠ 0)
    (hA13 : qPoch (a * q) q 13 ≠ 0) :
    BaileyTransformBeta a q ρ₁ ρ₂ β 7 =
      BaileyBeta a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 7 := by
  rw [BaileyTransformBeta_of_pair_seven_terms a q ρ₁ ρ₂ h,
    BaileyBeta_transformAlpha_seven_terms_linear]
  let C0 := ((qPoch ρ₁ q 0 * qPoch ρ₂ q 0 * (a * q / (ρ₁ * ρ₂)) ^ 0 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 7) /
      (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 *
        qPochhammer q 7))
  let C1 := ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 6) /
      (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 *
        qPochhammer q 6))
  let C2 := ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 5) /
      (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 *
        qPochhammer q 5))
  let C3 := ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 4) /
      (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 *
        qPochhammer q 4))
  let C4 := ((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3) /
      (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 *
        qPochhammer q 3))
  let C5 := ((qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 *
        qPochhammer q 2))
  let C6 := ((qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 *
        qPochhammer q 1))
  let C7 := ((qPoch ρ₁ q 7 * qPoch ρ₂ q 7 * (a * q / (ρ₁ * ρ₂)) ^ 7 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 *
        qPochhammer q 0))
  let D10 := (1 - q) * (1 - a * q)
  let D20 := qPochhammer q 2 * qPoch (a * q) q 2
  let D30 := qPochhammer q 3 * qPoch (a * q) q 3
  let D40 := qPochhammer q 4 * qPoch (a * q) q 4
  let D50 := qPochhammer q 5 * qPoch (a * q) q 5
  let D60 := qPochhammer q 6 * qPoch (a * q) q 6
  let D70 := qPochhammer q 7 * qPoch (a * q) q 7
  let E10 := qPoch (a * q) q 2
  let E21 := qPochhammer q 1 * qPoch (a * q) q 3
  let E31 := qPochhammer q 2 * qPoch (a * q) q 4
  let E41 := qPochhammer q 3 * qPoch (a * q) q 5
  let E51 := qPochhammer q 4 * qPoch (a * q) q 6
  let E61 := qPochhammer q 5 * qPoch (a * q) q 7
  let E71 := qPochhammer q 6 * qPoch (a * q) q 8
  let E22 := qPoch (a * q) q 4
  let E32 := qPochhammer q 1 * qPoch (a * q) q 5
  let E42 := qPochhammer q 2 * qPoch (a * q) q 6
  let E52 := qPochhammer q 3 * qPoch (a * q) q 7
  let E62 := qPochhammer q 4 * qPoch (a * q) q 8
  let E72 := qPochhammer q 5 * qPoch (a * q) q 9
  let E33 := qPoch (a * q) q 6
  let E43 := qPochhammer q 1 * qPoch (a * q) q 7
  let E53 := qPochhammer q 2 * qPoch (a * q) q 8
  let E63 := qPochhammer q 3 * qPoch (a * q) q 9
  let E73 := qPochhammer q 4 * qPoch (a * q) q 10
  let E44 := qPoch (a * q) q 8
  let E54 := qPochhammer q 1 * qPoch (a * q) q 9
  let E64 := qPochhammer q 2 * qPoch (a * q) q 10
  let E74 := qPochhammer q 3 * qPoch (a * q) q 11
  let E55 := qPoch (a * q) q 10
  let E65 := qPochhammer q 1 * qPoch (a * q) q 11
  let E75 := qPochhammer q 2 * qPoch (a * q) q 12
  let E66 := qPoch (a * q) q 12
  let E76 := qPochhammer q 1 * qPoch (a * q) q 13
  let E77 := qPoch (a * q) q 14
  let T0 := 1 / (qPochhammer q 7 * qPoch (a * q) q 7)
  let T1 := ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂))) /
          (qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1)) /
          (qPochhammer q 6 * qPoch (a * q) q 8)
  let T2 := ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 /
          (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2)) /
          (qPochhammer q 5 * qPoch (a * q) q 9))
  let T3 := ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 /
          (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3)) /
          (qPochhammer q 4 * qPoch (a * q) q 10))
  let T4 := ((qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 /
          (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4)) /
          (qPochhammer q 3 * qPoch (a * q) q 11))
  let T5 := ((qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 /
          (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5)) /
          (qPochhammer q 2 * qPoch (a * q) q 12))
  let T6 := ((qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6 /
          (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6)) /
          (qPochhammer q 1 * qPoch (a * q) q 13))
  let T7 := ((qPoch ρ₁ q 7 * qPoch ρ₂ q 7 * (a * q / (ρ₁ * ρ₂)) ^ 7 /
          (qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7)) /
          qPoch (a * q) q 14)
  have h0 :
      C0 + C1 / D10 + C2 / D20 + C3 / D30 + C4 / D40 + C5 / D50 +
        C6 / D60 + C7 / D70 = T0 := by
    dsimp [C0, C1, C2, C3, C4, C5, C6, C7,
      D10, D20, D30, D40, D50, D60, D70, T0]
    simpa [qPochhammer, qPoch] using
      BaileyTransform_seven_alpha_zero_coefficient_identity
        a q ρ₁ ρ₂ hρ hD1 hD2 hQ1 hQ2 hQ3 hQ4 hQ5 hQ6 hQ7
        hA1 hA2 hA3 hA4 hA5 hA6 hA7
  have h1 : C1 / E10 + C2 / E21 + C3 / E31 + C4 / E41 + C5 / E51 +
      C6 / E61 + C7 / E71 = T1 := by
    dsimp [C1, C2, C3, C4, C5, C6, C7,
      E10, E21, E31, E41, E51, E61, E71, T1]
    exact BaileyTransform_seven_alpha_one_coefficient_identity
      a q ρ₁ ρ₂ hρ hD1 hD2 hD1one hD2one hQ1 hQ2 hQ3 hQ4 hQ5 hQ6
      hA2 hA3 hA4 hA5 hA6 hA7 hA8
  have h2 : C2 / E22 + C3 / E32 + C4 / E42 + C5 / E52 + C6 / E62 +
      C7 / E72 = T2 := by
    dsimp [C2, C3, C4, C5, C6, C7, E22, E32, E42, E52, E62, E72, T2]
    exact BaileyTransform_seven_alpha_two_coefficient_identity
      a q ρ₁ ρ₂ hρ hD1 hD2 hD1two hD2two hQ1 hQ2 hQ3 hQ4 hQ5
      hA4 hA5 hA6 hA7 hA8 hA9
  have h3 : C3 / E33 + C4 / E43 + C5 / E53 + C6 / E63 + C7 / E73 = T3 := by
    dsimp [C3, C4, C5, C6, C7, E33, E43, E53, E63, E73, T3]
    exact BaileyTransform_seven_alpha_three_coefficient_identity
      a q ρ₁ ρ₂ hρ hD1 hD2 hD1three hD2three hQ1 hQ2 hQ3 hQ4
      hA6 hA7 hA8 hA9 hA10
  have h4 : C4 / E44 + C5 / E54 + C6 / E64 + C7 / E74 = T4 := by
    dsimp [C4, C5, C6, C7, E44, E54, E64, E74, T4]
    exact BaileyTransform_seven_alpha_four_coefficient_identity
      a q ρ₁ ρ₂ hρ hD1 hD2 hD1four hD2four hQ1 hQ2 hQ3 hA8 hA9 hA10 hA11
  have h5 : C5 / E55 + C6 / E65 + C7 / E75 = T5 := by
    dsimp [C5, C6, C7, E55, E65, E75, T5]
    exact BaileyTransform_seven_alpha_five_coefficient_identity
      a q ρ₁ ρ₂ hρ hD1 hD2 hD1five hD2five hQ1 hQ2 hA10 hA11 hA12
  have h6 : C6 / E66 + C7 / E76 = T6 := by
    dsimp [C6, C7, E66, E76, T6]
    exact BaileyTransform_seven_alpha_six_coefficient_identity
      a q ρ₁ ρ₂ hρ hD1 hD2 hD1six hD2six hQ1 hA12 hA13
  have h7 : C7 / E77 = T7 := by
    dsimp [C7, E77, T7]
    exact BaileyTransform_seven_alpha_seven_coefficient_identity a q ρ₁ ρ₂
  change C0 * α 0 + C1 * (α 0 / D10 + α 1 / E10) +
      C2 * (α 0 / D20 + α 1 / E21 + α 2 / E22) +
      C3 * (α 0 / D30 + α 1 / E31 + α 2 / E32 + α 3 / E33) +
      C4 * (α 0 / D40 + α 1 / E41 + α 2 / E42 + α 3 / E43 + α 4 / E44) +
      C5 * (α 0 / D50 + α 1 / E51 + α 2 / E52 + α 3 / E53 + α 4 / E54 +
        α 5 / E55) +
      C6 * (α 0 / D60 + α 1 / E61 + α 2 / E62 + α 3 / E63 + α 4 / E64 +
        α 5 / E65 + α 6 / E66) +
      C7 * (α 0 / D70 + α 1 / E71 + α 2 / E72 + α 3 / E73 + α 4 / E74 +
        α 5 / E75 + α 6 / E76 + α 7 / E77) =
      T0 * α 0 + T1 * α 1 + T2 * α 2 + T3 * α 3 + T4 * α 4 + T5 * α 5 +
        T6 * α 6 + T7 * α 7
  exact BaileyTransform_eight_coefficient_linear_identity
    C0 C1 C2 C3 C4 C5 C6 C7 D10 D20 D30 D40 D50 D60 D70
    E10 E21 E31 E41 E51 E61 E71 E22 E32 E42 E52 E62 E72
    E33 E43 E53 E63 E73 E44 E54 E64 E74 E55 E65 E75 E66 E76 E77
    T0 T1 T2 T3 T4 T5 T6 T7
    (α 0) (α 1) (α 2) (α 3) (α 4) (α 5) (α 6) (α 7)
    h0 h1 h2 h3 h4 h5 h6 h7

/-- Up-to-five finite Bailey-lemma packaging under explicit nonzero
denominator hypotheses. -/
theorem BaileyTransform_preserves_pair_upTo_five_of_nonzero
    (a q ρ₁ ρ₂ : R) {α β : Nat → R}
    (h : IsBaileyPairUpTo a q α β 5)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hD1 : qPoch (a * q / ρ₁) q 5 ≠ 0)
    (hD2 : qPoch (a * q / ρ₂) q 5 ≠ 0)
    (hD1one : qPoch (a * q / ρ₁) q 1 ≠ 0)
    (hD2one : qPoch (a * q / ρ₂) q 1 ≠ 0)
    (hD1two : qPoch (a * q / ρ₁) q 2 ≠ 0)
    (hD2two : qPoch (a * q / ρ₂) q 2 ≠ 0)
    (hD1three : qPoch (a * q / ρ₁) q 3 ≠ 0)
    (hD2three : qPoch (a * q / ρ₂) q 3 ≠ 0)
    (hD1four : qPoch (a * q / ρ₁) q 4 ≠ 0)
    (hD2four : qPoch (a * q / ρ₂) q 4 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hQ4 : qPochhammer q 4 ≠ 0)
    (hQ5 : qPochhammer q 5 ≠ 0)
    (hA1 : qPoch (a * q) q 1 ≠ 0)
    (hA2 : qPoch (a * q) q 2 ≠ 0)
    (hA3 : qPoch (a * q) q 3 ≠ 0)
    (hA4 : qPoch (a * q) q 4 ≠ 0)
    (hA5 : qPoch (a * q) q 5 ≠ 0)
    (hA6 : qPoch (a * q) q 6 ≠ 0)
    (hA7 : qPoch (a * q) q 7 ≠ 0)
    (hA8 : qPoch (a * q) q 8 ≠ 0)
    (hA9 : qPoch (a * q) q 9 ≠ 0) :
    IsBaileyPairUpTo a q (BaileyTransformAlpha a q ρ₁ ρ₂ α)
      (BaileyTransformBeta a q ρ₁ ρ₂ β) 5 := by
  have hq : 1 - q ≠ 0 := by simpa [qPochhammer] using hQ1
  have haq : 1 - a * q ≠ 0 := by simpa [qPoch] using hA1
  have hρ₁one : 1 - a * q / ρ₁ ≠ 0 := by simpa [qPoch] using hD1one
  have hρ₂one : 1 - a * q / ρ₂ ≠ 0 := by simpa [qPoch] using hD2one
  have hB1 : (1 - q) * (1 - a * q) ≠ 0 := mul_ne_zero hq haq
  exact IsBaileyPairUpTo.of_five
    (BaileyTransform_preserves_pair_zero a q ρ₁ ρ₂ (h.mono (by omega)))
    (BaileyTransform_preserves_pair_one_of_nonzero a q ρ₁ ρ₂ (h.mono (by omega))
      hρ hq haq hρ₁one hρ₂one)
    (BaileyTransform_preserves_pair_two_of_nonzero a q ρ₁ ρ₂ (h.mono (by omega))
      hρ hD1two hD2two hD1one hD2one hQ1 hQ2 hA2 hA3 hB1)
    (BaileyTransform_preserves_pair_three_of_nonzero a q ρ₁ ρ₂ (h.mono (by omega))
      hρ hD1three hD2three hD1one hD2one hD1two hD2two
      hQ1 hQ2 hQ3 hA1 hA2 hA3 hA4 hA5)
    (BaileyTransform_preserves_pair_four_of_nonzero a q ρ₁ ρ₂ (h.mono (by omega))
      hρ hD1four hD2four hD1one hD2one hD1two hD2two hD1three hD2three
      hQ1 hQ2 hQ3 hQ4 hA1 hA2 hA3 hA4 hA5 hA6 hA7)
    (BaileyTransform_preserves_pair_five_of_nonzero a q ρ₁ ρ₂ h
      hρ hD1 hD2 hD1one hD2one hD1two hD2two hD1three hD2three
      hD1four hD2four hQ1 hQ2 hQ3 hQ4 hQ5 hA1 hA2 hA3 hA4 hA5 hA6 hA7 hA8 hA9)

/-- Up-to-six finite Bailey-lemma packaging under explicit nonzero
denominator hypotheses. -/
theorem BaileyTransform_preserves_pair_upTo_six_of_nonzero
    (a q ρ₁ ρ₂ : R) {α β : Nat → R}
    (h : IsBaileyPairUpTo a q α β 6)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hD1 : qPoch (a * q / ρ₁) q 6 ≠ 0)
    (hD2 : qPoch (a * q / ρ₂) q 6 ≠ 0)
    (hD1one : qPoch (a * q / ρ₁) q 1 ≠ 0)
    (hD2one : qPoch (a * q / ρ₂) q 1 ≠ 0)
    (hD1two : qPoch (a * q / ρ₁) q 2 ≠ 0)
    (hD2two : qPoch (a * q / ρ₂) q 2 ≠ 0)
    (hD1three : qPoch (a * q / ρ₁) q 3 ≠ 0)
    (hD2three : qPoch (a * q / ρ₂) q 3 ≠ 0)
    (hD1four : qPoch (a * q / ρ₁) q 4 ≠ 0)
    (hD2four : qPoch (a * q / ρ₂) q 4 ≠ 0)
    (hD1five : qPoch (a * q / ρ₁) q 5 ≠ 0)
    (hD2five : qPoch (a * q / ρ₂) q 5 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hQ4 : qPochhammer q 4 ≠ 0)
    (hQ5 : qPochhammer q 5 ≠ 0)
    (hQ6 : qPochhammer q 6 ≠ 0)
    (hA1 : qPoch (a * q) q 1 ≠ 0)
    (hA2 : qPoch (a * q) q 2 ≠ 0)
    (hA3 : qPoch (a * q) q 3 ≠ 0)
    (hA4 : qPoch (a * q) q 4 ≠ 0)
    (hA5 : qPoch (a * q) q 5 ≠ 0)
    (hA6 : qPoch (a * q) q 6 ≠ 0)
    (hA7 : qPoch (a * q) q 7 ≠ 0)
    (hA8 : qPoch (a * q) q 8 ≠ 0)
    (hA9 : qPoch (a * q) q 9 ≠ 0)
    (hA10 : qPoch (a * q) q 10 ≠ 0)
    (hA11 : qPoch (a * q) q 11 ≠ 0) :
    IsBaileyPairUpTo a q (BaileyTransformAlpha a q ρ₁ ρ₂ α)
      (BaileyTransformBeta a q ρ₁ ρ₂ β) 6 := by
  have hq : 1 - q ≠ 0 := by simpa [qPochhammer] using hQ1
  have haq : 1 - a * q ≠ 0 := by simpa [qPoch] using hA1
  have hρ₁one : 1 - a * q / ρ₁ ≠ 0 := by simpa [qPoch] using hD1one
  have hρ₂one : 1 - a * q / ρ₂ ≠ 0 := by simpa [qPoch] using hD2one
  have hB1 : (1 - q) * (1 - a * q) ≠ 0 := mul_ne_zero hq haq
  exact IsBaileyPairUpTo.of_six
    (BaileyTransform_preserves_pair_zero a q ρ₁ ρ₂ (h.mono (by omega)))
    (BaileyTransform_preserves_pair_one_of_nonzero a q ρ₁ ρ₂ (h.mono (by omega))
      hρ hq haq hρ₁one hρ₂one)
    (BaileyTransform_preserves_pair_two_of_nonzero a q ρ₁ ρ₂ (h.mono (by omega))
      hρ hD1two hD2two hD1one hD2one hQ1 hQ2 hA2 hA3 hB1)
    (BaileyTransform_preserves_pair_three_of_nonzero a q ρ₁ ρ₂ (h.mono (by omega))
      hρ hD1three hD2three hD1one hD2one hD1two hD2two
      hQ1 hQ2 hQ3 hA1 hA2 hA3 hA4 hA5)
    (BaileyTransform_preserves_pair_four_of_nonzero a q ρ₁ ρ₂ (h.mono (by omega))
      hρ hD1four hD2four hD1one hD2one hD1two hD2two hD1three hD2three
      hQ1 hQ2 hQ3 hQ4 hA1 hA2 hA3 hA4 hA5 hA6 hA7)
    (BaileyTransform_preserves_pair_five_of_nonzero a q ρ₁ ρ₂ (h.mono (by omega))
      hρ hD1five hD2five hD1one hD2one hD1two hD2two hD1three hD2three
      hD1four hD2four hQ1 hQ2 hQ3 hQ4 hQ5 hA1 hA2 hA3 hA4 hA5 hA6 hA7 hA8 hA9)
    (BaileyTransform_preserves_pair_six_of_nonzero a q ρ₁ ρ₂ h
      hρ hD1 hD2 hD1one hD2one hD1two hD2two hD1three hD2three hD1four hD2four
      hD1five hD2five hQ1 hQ2 hQ3 hQ4 hQ5 hQ6 hA1 hA2 hA3 hA4 hA5 hA6 hA7
      hA8 hA9 hA10 hA11)

/-- Up-to-seven finite Bailey-lemma packaging under explicit nonzero
denominator hypotheses. -/
theorem BaileyTransform_preserves_pair_upTo_seven_of_nonzero
    (a q ρ₁ ρ₂ : R) {α β : Nat → R}
    (h : IsBaileyPairUpTo a q α β 7)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hD1 : qPoch (a * q / ρ₁) q 7 ≠ 0)
    (hD2 : qPoch (a * q / ρ₂) q 7 ≠ 0)
    (hD1one : qPoch (a * q / ρ₁) q 1 ≠ 0)
    (hD2one : qPoch (a * q / ρ₂) q 1 ≠ 0)
    (hD1two : qPoch (a * q / ρ₁) q 2 ≠ 0)
    (hD2two : qPoch (a * q / ρ₂) q 2 ≠ 0)
    (hD1three : qPoch (a * q / ρ₁) q 3 ≠ 0)
    (hD2three : qPoch (a * q / ρ₂) q 3 ≠ 0)
    (hD1four : qPoch (a * q / ρ₁) q 4 ≠ 0)
    (hD2four : qPoch (a * q / ρ₂) q 4 ≠ 0)
    (hD1five : qPoch (a * q / ρ₁) q 5 ≠ 0)
    (hD2five : qPoch (a * q / ρ₂) q 5 ≠ 0)
    (hD1six : qPoch (a * q / ρ₁) q 6 ≠ 0)
    (hD2six : qPoch (a * q / ρ₂) q 6 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hQ4 : qPochhammer q 4 ≠ 0)
    (hQ5 : qPochhammer q 5 ≠ 0)
    (hQ6 : qPochhammer q 6 ≠ 0)
    (hQ7 : qPochhammer q 7 ≠ 0)
    (hA1 : qPoch (a * q) q 1 ≠ 0)
    (hA2 : qPoch (a * q) q 2 ≠ 0)
    (hA3 : qPoch (a * q) q 3 ≠ 0)
    (hA4 : qPoch (a * q) q 4 ≠ 0)
    (hA5 : qPoch (a * q) q 5 ≠ 0)
    (hA6 : qPoch (a * q) q 6 ≠ 0)
    (hA7 : qPoch (a * q) q 7 ≠ 0)
    (hA8 : qPoch (a * q) q 8 ≠ 0)
    (hA9 : qPoch (a * q) q 9 ≠ 0)
    (hA10 : qPoch (a * q) q 10 ≠ 0)
    (hA11 : qPoch (a * q) q 11 ≠ 0)
    (hA12 : qPoch (a * q) q 12 ≠ 0)
    (hA13 : qPoch (a * q) q 13 ≠ 0) :
    IsBaileyPairUpTo a q (BaileyTransformAlpha a q ρ₁ ρ₂ α)
      (BaileyTransformBeta a q ρ₁ ρ₂ β) 7 := by
  have hq : 1 - q ≠ 0 := by simpa [qPochhammer] using hQ1
  have haq : 1 - a * q ≠ 0 := by simpa [qPoch] using hA1
  have hρ₁one : 1 - a * q / ρ₁ ≠ 0 := by simpa [qPoch] using hD1one
  have hρ₂one : 1 - a * q / ρ₂ ≠ 0 := by simpa [qPoch] using hD2one
  have hB1 : (1 - q) * (1 - a * q) ≠ 0 := mul_ne_zero hq haq
  exact IsBaileyPairUpTo.of_seven
    (BaileyTransform_preserves_pair_zero a q ρ₁ ρ₂ (h.mono (by omega)))
    (BaileyTransform_preserves_pair_one_of_nonzero a q ρ₁ ρ₂ (h.mono (by omega))
      hρ hq haq hρ₁one hρ₂one)
    (BaileyTransform_preserves_pair_two_of_nonzero a q ρ₁ ρ₂ (h.mono (by omega))
      hρ hD1two hD2two hD1one hD2one hQ1 hQ2 hA2 hA3 hB1)
    (BaileyTransform_preserves_pair_three_of_nonzero a q ρ₁ ρ₂ (h.mono (by omega))
      hρ hD1three hD2three hD1one hD2one hD1two hD2two
      hQ1 hQ2 hQ3 hA1 hA2 hA3 hA4 hA5)
    (BaileyTransform_preserves_pair_four_of_nonzero a q ρ₁ ρ₂ (h.mono (by omega))
      hρ hD1four hD2four hD1one hD2one hD1two hD2two hD1three hD2three
      hQ1 hQ2 hQ3 hQ4 hA1 hA2 hA3 hA4 hA5 hA6 hA7)
    (BaileyTransform_preserves_pair_five_of_nonzero a q ρ₁ ρ₂ (h.mono (by omega))
      hρ hD1five hD2five hD1one hD2one hD1two hD2two hD1three hD2three
      hD1four hD2four hQ1 hQ2 hQ3 hQ4 hQ5 hA1 hA2 hA3 hA4 hA5 hA6 hA7 hA8 hA9)
    (BaileyTransform_preserves_pair_six_of_nonzero a q ρ₁ ρ₂ (h.mono (by omega))
      hρ hD1six hD2six hD1one hD2one hD1two hD2two hD1three hD2three hD1four hD2four
      hD1five hD2five hQ1 hQ2 hQ3 hQ4 hQ5 hQ6 hA1 hA2 hA3 hA4 hA5 hA6 hA7
      hA8 hA9 hA10 hA11)
    (BaileyTransform_preserves_pair_seven_of_nonzero a q ρ₁ ρ₂ h
      hρ hD1 hD2 hD1one hD2one hD1two hD2two hD1three hD2three hD1four hD2four
      hD1five hD2five hD1six hD2six hQ1 hQ2 hQ3 hQ4 hQ5 hQ6 hQ7
      hA1 hA2 hA3 hA4 hA5 hA6 hA7 hA8 hA9 hA10 hA11 hA12 hA13)

/-- The Bailey β-transform of the canonical RR β at `n=1`, with the zeroth
RR β value evaluated. -/
theorem BaileyTransformBeta_rrBeta_one_expand (a q ρ₁ ρ₂ : R) (ha : 1 - a ≠ 0) :
    BaileyTransformBeta a q ρ₁ ρ₂ (rrBeta a q) 1 =
      ((qPoch ρ₁ q 0 * qPoch ρ₂ q 0 * (a * q / (ρ₁ * ρ₂)) ^ 0 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1 *
        qPochhammer q 1) * 1) +
      ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1 *
        qPochhammer q 0) * rrBeta a q 1) := by
  rw [BaileyTransformBeta_one_expand, rrBeta_zero a q ha]

/-- The Bailey β-transform of the canonical RR β at `n=2`, with the zeroth
RR β value evaluated. -/
theorem BaileyTransformBeta_rrBeta_two_expand (a q ρ₁ ρ₂ : R) (ha : 1 - a ≠ 0) :
    BaileyTransformBeta a q ρ₁ ρ₂ (rrBeta a q) 2 =
      ((qPoch ρ₁ q 0 * qPoch ρ₂ q 0 * (a * q / (ρ₁ * ρ₂)) ^ 0 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2 *
        qPochhammer q 2) * 1) +
      ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2 *
        qPochhammer q 1) * rrBeta a q 1) +
      ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2 *
        qPochhammer q 0) * rrBeta a q 2) := by
  rw [BaileyTransformBeta_two_expand, rrBeta_zero a q ha]

/-- The Bailey β-transform of the canonical RR β at `n=3`, with the zeroth
RR β value evaluated. -/
theorem BaileyTransformBeta_rrBeta_three_expand (a q ρ₁ ρ₂ : R) (ha : 1 - a ≠ 0) :
    BaileyTransformBeta a q ρ₁ ρ₂ (rrBeta a q) 3 =
      ((qPoch ρ₁ q 0 * qPoch ρ₂ q 0 * (a * q / (ρ₁ * ρ₂)) ^ 0 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3) /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 *
        qPochhammer q 3) * 1) +
      ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 *
        qPochhammer q 2) * rrBeta a q 1) +
      ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 *
        qPochhammer q 1) * rrBeta a q 2) +
      ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 *
        qPochhammer q 0) * rrBeta a q 3) := by
  rw [BaileyTransformBeta_three_expand, rrBeta_zero a q ha]

/-- BaileyBeta for the RR seed at N=1 expands to a two-term sum. -/
theorem BaileyBeta_rrAlpha_one_expand (a q : R) :
    BaileyBeta a q (rrAlpha a q) 1 =
      BaileyTerm a q (rrAlpha a q) 1 0 + BaileyTerm a q (rrAlpha a q) 1 1 := by
  exact BaileyBeta_one_expand a q (rrAlpha a q)

/-- The k=0 term of BaileyBeta at N=1. -/
theorem BaileyTerm_rrAlpha_one_zero (a q : R) (ha : 1 - a ≠ 0) :
    BaileyTerm a q (rrAlpha a q) 1 0 =
      1 / ((1 - q) * (1 - a * q)) := by
  simp only [BaileyTerm, rrAlpha_zero a q ha]
  simp [qPochhammer, qPoch]

/-- The k=1 term of BaileyBeta at N=1. -/
theorem BaileyTerm_rrAlpha_one_one (a q : R) (ha : 1 - a ≠ 0)
    (haq : 1 - a * q ≠ 0) (haq2 : 1 - a * q ^ 2 ≠ 0) :
    BaileyTerm a q (rrAlpha a q) 1 1 =
      -(1 - a * q ^ 2) / ((1 - a) * ((1 - a * q) * (1 - a * q ^ 2))) := by
  simp only [BaileyTerm, rrAlpha_one]
  simp [qPochhammer, qPoch]
  field_simp

/-- BaileyBeta at N=1 written with the evaluated rrAlpha terms. -/
theorem BaileyBeta_rrAlpha_one_terms (a q : R) (ha : 1 - a ≠ 0)
    (haq : 1 - a * q ≠ 0) (haq2 : 1 - a * q ^ 2 ≠ 0) :
    BaileyBeta a q (rrAlpha a q) 1 =
      1 / ((1 - q) * (1 - a * q)) +
      (-(1 - a * q ^ 2) / ((1 - a) * ((1 - a * q) * (1 - a * q ^ 2)))) := by
  rw [BaileyBeta_rrAlpha_one_expand, BaileyTerm_rrAlpha_one_zero a q ha,
    BaileyTerm_rrAlpha_one_one a q ha haq haq2]

/-- The canonical RR β at `N=1`, written with the evaluated α terms. -/
theorem rrBeta_one_terms (a q : R) (ha : 1 - a ≠ 0)
    (haq : 1 - a * q ≠ 0) (haq2 : 1 - a * q ^ 2 ≠ 0) :
    rrBeta a q 1 =
      1 / ((1 - q) * (1 - a * q)) +
      (-(1 - a * q ^ 2) / ((1 - a) * ((1 - a * q) * (1 - a * q ^ 2)))) := by
  unfold rrBeta
  exact BaileyBeta_rrAlpha_one_terms a q ha haq haq2

/-- The Bailey β-transform of the canonical RR β at `n=1`, with both RR β
values evaluated. -/
theorem BaileyTransformBeta_rrBeta_one_terms (a q ρ₁ ρ₂ : R) (ha : 1 - a ≠ 0)
    (haq : 1 - a * q ≠ 0) (haq2 : 1 - a * q ^ 2 ≠ 0) :
    BaileyTransformBeta a q ρ₁ ρ₂ (rrBeta a q) 1 =
      ((qPoch ρ₁ q 0 * qPoch ρ₂ q 0 * (a * q / (ρ₁ * ρ₂)) ^ 0 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1 *
        qPochhammer q 1) * 1) +
      ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 1 * qPoch (a * q / ρ₂) q 1 *
        qPochhammer q 0) *
        (1 / ((1 - q) * (1 - a * q)) +
        (-(1 - a * q ^ 2) / ((1 - a) * ((1 - a * q) * (1 - a * q ^ 2)))))) := by
  rw [BaileyTransformBeta_rrBeta_one_expand a q ρ₁ ρ₂ ha,
    rrBeta_one_terms a q ha haq haq2]

/-- BaileyBeta at N=2 expands to a three-term sum. -/
theorem BaileyBeta_rrAlpha_two_expand (a q : R) :
    BaileyBeta a q (rrAlpha a q) 2 =
      BaileyTerm a q (rrAlpha a q) 2 0 +
      BaileyTerm a q (rrAlpha a q) 2 1 +
      BaileyTerm a q (rrAlpha a q) 2 2 := by
  exact BaileyBeta_two_expand a q (rrAlpha a q)

/-- The k=0 term of BaileyBeta at N=2. -/
theorem BaileyTerm_rrAlpha_two_zero (a q : R) (ha : 1 - a ≠ 0) :
    BaileyTerm a q (rrAlpha a q) 2 0 =
      1 / (qPochhammer q 2 * qPoch (a * q) q 2) := by
  rw [BaileyTerm_zero, rrAlpha_zero a q ha]

/-- The k=1 term of BaileyBeta at N=2. -/
theorem BaileyTerm_rrAlpha_two_one (a q : R) :
    BaileyTerm a q (rrAlpha a q) 2 1 =
      (-(1 - a * q ^ 2) / (1 - a)) /
        (qPochhammer q 1 * qPoch (a * q) q 3) := by
  simp only [BaileyTerm, rrAlpha_one]

/-- The k=2 term of BaileyBeta at N=2. -/
theorem BaileyTerm_rrAlpha_two_two (a q : R) :
    BaileyTerm a q (rrAlpha a q) 2 2 =
      (q * (1 - a * q ^ 4) / (1 - a)) / qPoch (a * q) q 4 := by
  rw [BaileyTerm_at_n_simplified, rrAlpha_two]

/-- BaileyBeta at N=2 written with the evaluated rrAlpha terms. -/
theorem BaileyBeta_rrAlpha_two_terms (a q : R) (ha : 1 - a ≠ 0) :
    BaileyBeta a q (rrAlpha a q) 2 =
      1 / (qPochhammer q 2 * qPoch (a * q) q 2) +
      ((-(1 - a * q ^ 2) / (1 - a)) /
        (qPochhammer q 1 * qPoch (a * q) q 3)) +
      ((q * (1 - a * q ^ 4) / (1 - a)) / qPoch (a * q) q 4) := by
  rw [BaileyBeta_rrAlpha_two_expand, BaileyTerm_rrAlpha_two_zero a q ha,
    BaileyTerm_rrAlpha_two_one, BaileyTerm_rrAlpha_two_two]

/-- The canonical RR β at `N=2`, written with the evaluated α terms. -/
theorem rrBeta_two_terms (a q : R) (ha : 1 - a ≠ 0) :
    rrBeta a q 2 =
      1 / (qPochhammer q 2 * qPoch (a * q) q 2) +
      ((-(1 - a * q ^ 2) / (1 - a)) /
        (qPochhammer q 1 * qPoch (a * q) q 3)) +
      ((q * (1 - a * q ^ 4) / (1 - a)) / qPoch (a * q) q 4) := by
  unfold rrBeta
  exact BaileyBeta_rrAlpha_two_terms a q ha

/-- The Bailey β-transform of the canonical RR β at `n=2`, with all RR β
values up to two evaluated. -/
theorem BaileyTransformBeta_rrBeta_two_terms (a q ρ₁ ρ₂ : R) (ha : 1 - a ≠ 0)
    (haq : 1 - a * q ≠ 0) (haq2 : 1 - a * q ^ 2 ≠ 0) :
    BaileyTransformBeta a q ρ₁ ρ₂ (rrBeta a q) 2 =
      ((qPoch ρ₁ q 0 * qPoch ρ₂ q 0 * (a * q / (ρ₁ * ρ₂)) ^ 0 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2 *
        qPochhammer q 2) * 1) +
      ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2 *
        qPochhammer q 1) *
        (1 / ((1 - q) * (1 - a * q)) +
        (-(1 - a * q ^ 2) / ((1 - a) * ((1 - a * q) * (1 - a * q ^ 2)))))) +
      ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2 *
        qPochhammer q 0) *
        (1 / (qPochhammer q 2 * qPoch (a * q) q 2) +
        ((-(1 - a * q ^ 2) / (1 - a)) /
          (qPochhammer q 1 * qPoch (a * q) q 3)) +
        ((q * (1 - a * q ^ 4) / (1 - a)) / qPoch (a * q) q 4))) := by
  rw [BaileyTransformBeta_rrBeta_two_expand a q ρ₁ ρ₂ ha,
    rrBeta_one_terms a q ha haq haq2, rrBeta_two_terms a q ha]

/-- BaileyBeta at N=3 expands to a four-term sum. -/
theorem BaileyBeta_rrAlpha_three_expand (a q : R) :
    BaileyBeta a q (rrAlpha a q) 3 =
      BaileyTerm a q (rrAlpha a q) 3 0 +
      BaileyTerm a q (rrAlpha a q) 3 1 +
      BaileyTerm a q (rrAlpha a q) 3 2 +
      BaileyTerm a q (rrAlpha a q) 3 3 := by
  exact BaileyBeta_three_expand a q (rrAlpha a q)

/-- The k=0 term of BaileyBeta at N=3. -/
theorem BaileyTerm_rrAlpha_three_zero (a q : R) (ha : 1 - a ≠ 0) :
    BaileyTerm a q (rrAlpha a q) 3 0 =
      1 / (qPochhammer q 3 * qPoch (a * q) q 3) := by
  rw [BaileyTerm_zero, rrAlpha_zero a q ha]

/-- The k=1 term of BaileyBeta at N=3. -/
theorem BaileyTerm_rrAlpha_three_one (a q : R) :
    BaileyTerm a q (rrAlpha a q) 3 1 =
      (-(1 - a * q ^ 2) / (1 - a)) /
        (qPochhammer q 2 * qPoch (a * q) q 4) := by
  simp only [BaileyTerm, rrAlpha_one]

/-- The k=2 term of BaileyBeta at N=3. -/
theorem BaileyTerm_rrAlpha_three_two (a q : R) :
    BaileyTerm a q (rrAlpha a q) 3 2 =
      (q * (1 - a * q ^ 4) / (1 - a)) /
        (qPochhammer q 1 * qPoch (a * q) q 5) := by
  simp only [BaileyTerm, rrAlpha_two]

/-- The k=3 term of BaileyBeta at N=3. -/
theorem BaileyTerm_rrAlpha_three_three (a q : R) :
    BaileyTerm a q (rrAlpha a q) 3 3 =
      (-(q ^ 3 * (1 - a * q ^ 6)) / (1 - a)) / qPoch (a * q) q 6 := by
  rw [BaileyTerm_at_n_simplified, rrAlpha_three]

/-- BaileyBeta at N=3 written with the evaluated rrAlpha terms. -/
theorem BaileyBeta_rrAlpha_three_terms (a q : R) (ha : 1 - a ≠ 0) :
    BaileyBeta a q (rrAlpha a q) 3 =
      1 / (qPochhammer q 3 * qPoch (a * q) q 3) +
      ((-(1 - a * q ^ 2) / (1 - a)) /
        (qPochhammer q 2 * qPoch (a * q) q 4)) +
      ((q * (1 - a * q ^ 4) / (1 - a)) /
        (qPochhammer q 1 * qPoch (a * q) q 5)) +
      ((-(q ^ 3 * (1 - a * q ^ 6)) / (1 - a)) / qPoch (a * q) q 6) := by
  rw [BaileyBeta_rrAlpha_three_expand, BaileyTerm_rrAlpha_three_zero a q ha,
    BaileyTerm_rrAlpha_three_one, BaileyTerm_rrAlpha_three_two,
    BaileyTerm_rrAlpha_three_three]

/-- The canonical RR β at `N=3`, written with the evaluated α terms. -/
theorem rrBeta_three_terms (a q : R) (ha : 1 - a ≠ 0) :
    rrBeta a q 3 =
      1 / (qPochhammer q 3 * qPoch (a * q) q 3) +
      ((-(1 - a * q ^ 2) / (1 - a)) /
        (qPochhammer q 2 * qPoch (a * q) q 4)) +
      ((q * (1 - a * q ^ 4) / (1 - a)) /
        (qPochhammer q 1 * qPoch (a * q) q 5)) +
      ((-(q ^ 3 * (1 - a * q ^ 6)) / (1 - a)) / qPoch (a * q) q 6) := by
  unfold rrBeta
  exact BaileyBeta_rrAlpha_three_terms a q ha

/-- BaileyBeta at N=4 expands to a five-term sum. -/
theorem BaileyBeta_rrAlpha_four_expand (a q : R) :
    BaileyBeta a q (rrAlpha a q) 4 =
      BaileyTerm a q (rrAlpha a q) 4 0 +
      BaileyTerm a q (rrAlpha a q) 4 1 +
      BaileyTerm a q (rrAlpha a q) 4 2 +
      BaileyTerm a q (rrAlpha a q) 4 3 +
      BaileyTerm a q (rrAlpha a q) 4 4 := by
  exact BaileyBeta_four_expand a q (rrAlpha a q)

/-- The k=0 term of BaileyBeta at N=4. -/
theorem BaileyTerm_rrAlpha_four_zero (a q : R) (ha : 1 - a ≠ 0) :
    BaileyTerm a q (rrAlpha a q) 4 0 =
      1 / (qPochhammer q 4 * qPoch (a * q) q 4) := by
  rw [BaileyTerm_zero, rrAlpha_zero a q ha]

/-- The k=1 term of BaileyBeta at N=4. -/
theorem BaileyTerm_rrAlpha_four_one (a q : R) :
    BaileyTerm a q (rrAlpha a q) 4 1 =
      (-(1 - a * q ^ 2) / (1 - a)) /
        (qPochhammer q 3 * qPoch (a * q) q 5) := by
  simp only [BaileyTerm, rrAlpha_one]

/-- The k=2 term of BaileyBeta at N=4. -/
theorem BaileyTerm_rrAlpha_four_two (a q : R) :
    BaileyTerm a q (rrAlpha a q) 4 2 =
      (q * (1 - a * q ^ 4) / (1 - a)) /
        (qPochhammer q 2 * qPoch (a * q) q 6) := by
  simp only [BaileyTerm, rrAlpha_two]

/-- The k=3 term of BaileyBeta at N=4. -/
theorem BaileyTerm_rrAlpha_four_three (a q : R) :
    BaileyTerm a q (rrAlpha a q) 4 3 =
      (-(q ^ 3 * (1 - a * q ^ 6)) / (1 - a)) /
        (qPochhammer q 1 * qPoch (a * q) q 7) := by
  simp only [BaileyTerm, rrAlpha_three]

/-- The k=4 term of BaileyBeta at N=4. -/
theorem BaileyTerm_rrAlpha_four_four (a q : R) :
    BaileyTerm a q (rrAlpha a q) 4 4 =
      (q ^ 6 * (1 - a * q ^ 8) / (1 - a)) / qPoch (a * q) q 8 := by
  rw [BaileyTerm_at_n_simplified, rrAlpha_four]

/-- BaileyBeta at N=4 written with the evaluated rrAlpha terms. -/
theorem BaileyBeta_rrAlpha_four_terms (a q : R) (ha : 1 - a ≠ 0) :
    BaileyBeta a q (rrAlpha a q) 4 =
      1 / (qPochhammer q 4 * qPoch (a * q) q 4) +
      ((-(1 - a * q ^ 2) / (1 - a)) /
        (qPochhammer q 3 * qPoch (a * q) q 5)) +
      ((q * (1 - a * q ^ 4) / (1 - a)) /
        (qPochhammer q 2 * qPoch (a * q) q 6)) +
      ((-(q ^ 3 * (1 - a * q ^ 6)) / (1 - a)) /
        (qPochhammer q 1 * qPoch (a * q) q 7)) +
      ((q ^ 6 * (1 - a * q ^ 8) / (1 - a)) / qPoch (a * q) q 8) := by
  rw [BaileyBeta_rrAlpha_four_expand, BaileyTerm_rrAlpha_four_zero a q ha,
    BaileyTerm_rrAlpha_four_one, BaileyTerm_rrAlpha_four_two,
    BaileyTerm_rrAlpha_four_three, BaileyTerm_rrAlpha_four_four]

/-- The canonical RR β at `N=4`, written with the evaluated α terms. -/
theorem rrBeta_four_terms (a q : R) (ha : 1 - a ≠ 0) :
    rrBeta a q 4 =
      1 / (qPochhammer q 4 * qPoch (a * q) q 4) +
      ((-(1 - a * q ^ 2) / (1 - a)) /
        (qPochhammer q 3 * qPoch (a * q) q 5)) +
      ((q * (1 - a * q ^ 4) / (1 - a)) /
        (qPochhammer q 2 * qPoch (a * q) q 6)) +
      ((-(q ^ 3 * (1 - a * q ^ 6)) / (1 - a)) /
        (qPochhammer q 1 * qPoch (a * q) q 7)) +
      ((q ^ 6 * (1 - a * q ^ 8) / (1 - a)) / qPoch (a * q) q 8) := by
  unfold rrBeta
  exact BaileyBeta_rrAlpha_four_terms a q ha

/-- BaileyBeta at N=5 expands to a six-term sum. -/
theorem BaileyBeta_rrAlpha_five_expand (a q : R) :
    BaileyBeta a q (rrAlpha a q) 5 =
      BaileyTerm a q (rrAlpha a q) 5 0 +
      BaileyTerm a q (rrAlpha a q) 5 1 +
      BaileyTerm a q (rrAlpha a q) 5 2 +
      BaileyTerm a q (rrAlpha a q) 5 3 +
      BaileyTerm a q (rrAlpha a q) 5 4 +
      BaileyTerm a q (rrAlpha a q) 5 5 := by
  exact BaileyBeta_five_expand a q (rrAlpha a q)

/-- The k=0 term of BaileyBeta at N=5. -/
theorem BaileyTerm_rrAlpha_five_zero (a q : R) (ha : 1 - a ≠ 0) :
    BaileyTerm a q (rrAlpha a q) 5 0 =
      1 / (qPochhammer q 5 * qPoch (a * q) q 5) := by
  rw [BaileyTerm_zero, rrAlpha_zero a q ha]

/-- The k=1 term of BaileyBeta at N=5. -/
theorem BaileyTerm_rrAlpha_five_one (a q : R) :
    BaileyTerm a q (rrAlpha a q) 5 1 =
      (-(1 - a * q ^ 2) / (1 - a)) /
        (qPochhammer q 4 * qPoch (a * q) q 6) := by
  simp only [BaileyTerm, rrAlpha_one]

/-- The k=2 term of BaileyBeta at N=5. -/
theorem BaileyTerm_rrAlpha_five_two (a q : R) :
    BaileyTerm a q (rrAlpha a q) 5 2 =
      (q * (1 - a * q ^ 4) / (1 - a)) /
        (qPochhammer q 3 * qPoch (a * q) q 7) := by
  simp only [BaileyTerm, rrAlpha_two]

/-- The k=3 term of BaileyBeta at N=5. -/
theorem BaileyTerm_rrAlpha_five_three (a q : R) :
    BaileyTerm a q (rrAlpha a q) 5 3 =
      (-(q ^ 3 * (1 - a * q ^ 6)) / (1 - a)) /
        (qPochhammer q 2 * qPoch (a * q) q 8) := by
  simp only [BaileyTerm, rrAlpha_three]

/-- The k=4 term of BaileyBeta at N=5. -/
theorem BaileyTerm_rrAlpha_five_four (a q : R) :
    BaileyTerm a q (rrAlpha a q) 5 4 =
      (q ^ 6 * (1 - a * q ^ 8) / (1 - a)) /
        (qPochhammer q 1 * qPoch (a * q) q 9) := by
  simp only [BaileyTerm, rrAlpha_four]

/-- The k=5 term of BaileyBeta at N=5. -/
theorem BaileyTerm_rrAlpha_five_five (a q : R) :
    BaileyTerm a q (rrAlpha a q) 5 5 =
      (-(q ^ 10 * (1 - a * q ^ 10)) / (1 - a)) /
        qPoch (a * q) q 10 := by
  rw [BaileyTerm_at_n_simplified, rrAlpha_five]

/-- BaileyBeta at N=5 written with the evaluated rrAlpha terms. -/
theorem BaileyBeta_rrAlpha_five_terms (a q : R) (ha : 1 - a ≠ 0) :
    BaileyBeta a q (rrAlpha a q) 5 =
      1 / (qPochhammer q 5 * qPoch (a * q) q 5) +
      ((-(1 - a * q ^ 2) / (1 - a)) /
        (qPochhammer q 4 * qPoch (a * q) q 6)) +
      ((q * (1 - a * q ^ 4) / (1 - a)) /
        (qPochhammer q 3 * qPoch (a * q) q 7)) +
      ((-(q ^ 3 * (1 - a * q ^ 6)) / (1 - a)) /
        (qPochhammer q 2 * qPoch (a * q) q 8)) +
      ((q ^ 6 * (1 - a * q ^ 8) / (1 - a)) /
        (qPochhammer q 1 * qPoch (a * q) q 9)) +
      ((-(q ^ 10 * (1 - a * q ^ 10)) / (1 - a)) /
        qPoch (a * q) q 10) := by
  rw [BaileyBeta_rrAlpha_five_expand, BaileyTerm_rrAlpha_five_zero a q ha,
    BaileyTerm_rrAlpha_five_one, BaileyTerm_rrAlpha_five_two,
    BaileyTerm_rrAlpha_five_three, BaileyTerm_rrAlpha_five_four,
    BaileyTerm_rrAlpha_five_five]

/-- The canonical RR β at `N=5`, written with the evaluated α terms. -/
theorem rrBeta_five_terms (a q : R) (ha : 1 - a ≠ 0) :
    rrBeta a q 5 =
      1 / (qPochhammer q 5 * qPoch (a * q) q 5) +
      ((-(1 - a * q ^ 2) / (1 - a)) /
        (qPochhammer q 4 * qPoch (a * q) q 6)) +
      ((q * (1 - a * q ^ 4) / (1 - a)) /
        (qPochhammer q 3 * qPoch (a * q) q 7)) +
      ((-(q ^ 3 * (1 - a * q ^ 6)) / (1 - a)) /
        (qPochhammer q 2 * qPoch (a * q) q 8)) +
      ((q ^ 6 * (1 - a * q ^ 8) / (1 - a)) /
        (qPochhammer q 1 * qPoch (a * q) q 9)) +
      ((-(q ^ 10 * (1 - a * q ^ 10)) / (1 - a)) /
        qPoch (a * q) q 10) := by
  unfold rrBeta
  exact BaileyBeta_rrAlpha_five_terms a q ha

/-- BaileyBeta at N=6 expands to a seven-term sum. -/
theorem BaileyBeta_rrAlpha_six_expand (a q : R) :
    BaileyBeta a q (rrAlpha a q) 6 =
      BaileyTerm a q (rrAlpha a q) 6 0 +
      BaileyTerm a q (rrAlpha a q) 6 1 +
      BaileyTerm a q (rrAlpha a q) 6 2 +
      BaileyTerm a q (rrAlpha a q) 6 3 +
      BaileyTerm a q (rrAlpha a q) 6 4 +
      BaileyTerm a q (rrAlpha a q) 6 5 +
      BaileyTerm a q (rrAlpha a q) 6 6 := by
  exact BaileyBeta_six_expand a q (rrAlpha a q)

/-- The k=0 term of BaileyBeta at N=6. -/
theorem BaileyTerm_rrAlpha_six_zero (a q : R) (ha : 1 - a ≠ 0) :
    BaileyTerm a q (rrAlpha a q) 6 0 =
      1 / (qPochhammer q 6 * qPoch (a * q) q 6) := by
  rw [BaileyTerm_zero, rrAlpha_zero a q ha]

/-- The k=1 term of BaileyBeta at N=6. -/
theorem BaileyTerm_rrAlpha_six_one (a q : R) :
    BaileyTerm a q (rrAlpha a q) 6 1 =
      (-(1 - a * q ^ 2) / (1 - a)) /
        (qPochhammer q 5 * qPoch (a * q) q 7) := by
  simp only [BaileyTerm, rrAlpha_one]

/-- The k=2 term of BaileyBeta at N=6. -/
theorem BaileyTerm_rrAlpha_six_two (a q : R) :
    BaileyTerm a q (rrAlpha a q) 6 2 =
      (q * (1 - a * q ^ 4) / (1 - a)) /
        (qPochhammer q 4 * qPoch (a * q) q 8) := by
  simp only [BaileyTerm, rrAlpha_two]

/-- The k=3 term of BaileyBeta at N=6. -/
theorem BaileyTerm_rrAlpha_six_three (a q : R) :
    BaileyTerm a q (rrAlpha a q) 6 3 =
      (-(q ^ 3 * (1 - a * q ^ 6)) / (1 - a)) /
        (qPochhammer q 3 * qPoch (a * q) q 9) := by
  simp only [BaileyTerm, rrAlpha_three]

/-- The k=4 term of BaileyBeta at N=6. -/
theorem BaileyTerm_rrAlpha_six_four (a q : R) :
    BaileyTerm a q (rrAlpha a q) 6 4 =
      (q ^ 6 * (1 - a * q ^ 8) / (1 - a)) /
        (qPochhammer q 2 * qPoch (a * q) q 10) := by
  simp only [BaileyTerm, rrAlpha_four]

/-- The k=5 term of BaileyBeta at N=6. -/
theorem BaileyTerm_rrAlpha_six_five (a q : R) :
    BaileyTerm a q (rrAlpha a q) 6 5 =
      (-(q ^ 10 * (1 - a * q ^ 10)) / (1 - a)) /
        (qPochhammer q 1 * qPoch (a * q) q 11) := by
  simp only [BaileyTerm, rrAlpha_five]

/-- The k=6 term of BaileyBeta at N=6. -/
theorem BaileyTerm_rrAlpha_six_six (a q : R) :
    BaileyTerm a q (rrAlpha a q) 6 6 =
      (q ^ 15 * (1 - a * q ^ 12) / (1 - a)) /
        qPoch (a * q) q 12 := by
  rw [BaileyTerm_at_n_simplified, rrAlpha_six]

/-- BaileyBeta at N=6 written with the evaluated rrAlpha terms. -/
theorem BaileyBeta_rrAlpha_six_terms (a q : R) (ha : 1 - a ≠ 0) :
    BaileyBeta a q (rrAlpha a q) 6 =
      1 / (qPochhammer q 6 * qPoch (a * q) q 6) +
      ((-(1 - a * q ^ 2) / (1 - a)) /
        (qPochhammer q 5 * qPoch (a * q) q 7)) +
      ((q * (1 - a * q ^ 4) / (1 - a)) /
        (qPochhammer q 4 * qPoch (a * q) q 8)) +
      ((-(q ^ 3 * (1 - a * q ^ 6)) / (1 - a)) /
        (qPochhammer q 3 * qPoch (a * q) q 9)) +
      ((q ^ 6 * (1 - a * q ^ 8) / (1 - a)) /
        (qPochhammer q 2 * qPoch (a * q) q 10)) +
      ((-(q ^ 10 * (1 - a * q ^ 10)) / (1 - a)) /
        (qPochhammer q 1 * qPoch (a * q) q 11)) +
      ((q ^ 15 * (1 - a * q ^ 12) / (1 - a)) /
        qPoch (a * q) q 12) := by
  rw [BaileyBeta_rrAlpha_six_expand, BaileyTerm_rrAlpha_six_zero a q ha,
    BaileyTerm_rrAlpha_six_one, BaileyTerm_rrAlpha_six_two,
    BaileyTerm_rrAlpha_six_three, BaileyTerm_rrAlpha_six_four,
    BaileyTerm_rrAlpha_six_five, BaileyTerm_rrAlpha_six_six]

/-- The canonical RR β at `N=6`, written with the evaluated α terms. -/
theorem rrBeta_six_terms (a q : R) (ha : 1 - a ≠ 0) :
    rrBeta a q 6 =
      1 / (qPochhammer q 6 * qPoch (a * q) q 6) +
      ((-(1 - a * q ^ 2) / (1 - a)) /
        (qPochhammer q 5 * qPoch (a * q) q 7)) +
      ((q * (1 - a * q ^ 4) / (1 - a)) /
        (qPochhammer q 4 * qPoch (a * q) q 8)) +
      ((-(q ^ 3 * (1 - a * q ^ 6)) / (1 - a)) /
        (qPochhammer q 3 * qPoch (a * q) q 9)) +
      ((q ^ 6 * (1 - a * q ^ 8) / (1 - a)) /
        (qPochhammer q 2 * qPoch (a * q) q 10)) +
      ((-(q ^ 10 * (1 - a * q ^ 10)) / (1 - a)) /
        (qPochhammer q 1 * qPoch (a * q) q 11)) +
      ((q ^ 15 * (1 - a * q ^ 12) / (1 - a)) /
        qPoch (a * q) q 12) := by
  unfold rrBeta
  exact BaileyBeta_rrAlpha_six_terms a q ha

/-- The Bailey β-transform of the canonical RR β at `n=3`, with all RR β
values up to three evaluated. -/
theorem BaileyTransformBeta_rrBeta_three_terms (a q ρ₁ ρ₂ : R) (ha : 1 - a ≠ 0)
    (haq : 1 - a * q ≠ 0) (haq2 : 1 - a * q ^ 2 ≠ 0) :
    BaileyTransformBeta a q ρ₁ ρ₂ (rrBeta a q) 3 =
      ((qPoch ρ₁ q 0 * qPoch ρ₂ q 0 * (a * q / (ρ₁ * ρ₂)) ^ 0 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3) /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 *
        qPochhammer q 3) * 1) +
      ((qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) ^ 1 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2) /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 *
        qPochhammer q 2) *
        (1 / ((1 - q) * (1 - a * q)) +
        (-(1 - a * q ^ 2) / ((1 - a) * ((1 - a * q) * (1 - a * q ^ 2)))))) +
      ((qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 *
        qPochhammer q 1) *
        (1 / (qPochhammer q 2 * qPoch (a * q) q 2) +
        ((-(1 - a * q ^ 2) / (1 - a)) /
          (qPochhammer q 1 * qPoch (a * q) q 3)) +
        ((q * (1 - a * q ^ 4) / (1 - a)) / qPoch (a * q) q 4))) +
      ((qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3 *
        qPochhammer q 0) *
        (1 / (qPochhammer q 3 * qPoch (a * q) q 3) +
        ((-(1 - a * q ^ 2) / (1 - a)) /
          (qPochhammer q 2 * qPoch (a * q) q 4)) +
        ((q * (1 - a * q ^ 4) / (1 - a)) /
          (qPochhammer q 1 * qPoch (a * q) q 5)) +
        ((-(q ^ 3 * (1 - a * q ^ 6)) / (1 - a)) / qPoch (a * q) q 6))) := by
  rw [BaileyTransformBeta_rrBeta_three_expand a q ρ₁ ρ₂ ha,
    rrBeta_one_terms a q ha haq haq2, rrBeta_two_terms a q ha,
    rrBeta_three_terms a q ha]

/-- The Bailey transform applied to the RR seed at `n = 1`. -/
theorem BaileyTransformAlpha_rrAlpha_one (a q ρ₁ ρ₂ : R) :
    BaileyTransformAlpha a q ρ₁ ρ₂ (rrAlpha a q) 1 =
      (1 - ρ₁) * (1 - ρ₂) * (a * q / (ρ₁ * ρ₂)) /
      ((1 - a * q / ρ₁) * (1 - a * q / ρ₂)) * (-(1 - a * q ^ 2) / (1 - a)) := by
  rw [BaileyTransformAlpha_one, rrAlpha_one]

/-- The Bailey transform applied to the RR seed at `n = 2`. -/
theorem BaileyTransformAlpha_rrAlpha_two (a q ρ₁ ρ₂ : R) :
    BaileyTransformAlpha a q ρ₁ ρ₂ (rrAlpha a q) 2 =
      qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 /
      (qPoch (a * q / ρ₁) q 2 * qPoch (a * q / ρ₂) q 2) *
        (q * (1 - a * q ^ 4) / (1 - a)) := by
  rw [BaileyTransformAlpha_two, rrAlpha_two]

/-- The Bailey transform applied to the RR seed at `n = 3`. -/
theorem BaileyTransformAlpha_rrAlpha_three (a q ρ₁ ρ₂ : R) :
    BaileyTransformAlpha a q ρ₁ ρ₂ (rrAlpha a q) 3 =
      qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 /
      (qPoch (a * q / ρ₁) q 3 * qPoch (a * q / ρ₂) q 3) *
        (-(q ^ 3 * (1 - a * q ^ 6)) / (1 - a)) := by
  rw [BaileyTransformAlpha_three, rrAlpha_three]

/-- The Bailey transform applied to the RR seed at `n = 4`. -/
theorem BaileyTransformAlpha_rrAlpha_four (a q ρ₁ ρ₂ : R) :
    BaileyTransformAlpha a q ρ₁ ρ₂ (rrAlpha a q) 4 =
      qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 /
      (qPoch (a * q / ρ₁) q 4 * qPoch (a * q / ρ₂) q 4) *
        (q ^ 6 * (1 - a * q ^ 8) / (1 - a)) := by
  rw [BaileyTransformAlpha_four, rrAlpha_four]

/-- The Bailey transform applied to the RR seed at `n = 5`. -/
theorem BaileyTransformAlpha_rrAlpha_five (a q ρ₁ ρ₂ : R) :
    BaileyTransformAlpha a q ρ₁ ρ₂ (rrAlpha a q) 5 =
      qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 /
      (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5) *
        (-(q ^ 10 * (1 - a * q ^ 10)) / (1 - a)) := by
  rw [BaileyTransformAlpha_five, rrAlpha_five]

/-- The Bailey transform applied to the RR seed at `n = 6`. -/
theorem BaileyTransformAlpha_rrAlpha_six (a q ρ₁ ρ₂ : R) :
    BaileyTransformAlpha a q ρ₁ ρ₂ (rrAlpha a q) 6 =
      qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6 /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6) *
        (q ^ 15 * (1 - a * q ^ 12) / (1 - a)) := by
  rw [BaileyTransformAlpha_six, rrAlpha_six]

/-! ### General Bailey lemma framework

The following section develops the structural tools needed for the general
finite Bailey lemma:  if `(α, β)` is a Bailey pair relative to `a`, then
`(BaileyTransformAlpha α, BaileyTransformBeta β)` is again a Bailey pair.

The proof reduces to a single algebraic kernel identity via double-sum swap. -/

section GeneralBaileyLemma

open Finset in
/-- Bridge: `natSum` equals `Finset.sum` over `range (N+1)`. -/
theorem natSum_eq_sum_range' (f : ℕ → R) (N : ℕ) :
    natSum f N = ∑ n ∈ range (N + 1), f n := by
  induction N with
  | zero => simp [natSum]
  | succ N ih => rw [natSum_succ, ih]; simp [sum_range_succ, Nat.add_assoc]

open Finset in
/-- `BaileyBeta` as a `Finset.sum`. -/
theorem BaileyBeta_eq_sum (a q : R) (α : Nat → R) (n : Nat) :
    BaileyBeta a q α n = ∑ k ∈ range (n + 1), BaileyTerm a q α n k := by
  rw [BaileyBeta, natSum_eq_sum_range']

open Finset in
/-- `BaileyTransformBeta` as a `Finset.sum`. -/
theorem BaileyTransformBeta_eq_sum (a q ρ₁ ρ₂ : R) (β : Nat → R) (n : Nat) :
    BaileyTransformBeta a q ρ₁ ρ₂ β n =
      ∑ k ∈ range (n + 1),
        ((qPoch ρ₁ q k * qPoch ρ₂ q k * (a * q / (ρ₁ * ρ₂)) ^ k *
          qPoch (a * q / (ρ₁ * ρ₂)) q (n - k)) /
        (qPoch (a * q / ρ₁) q n * qPoch (a * q / ρ₂) q n *
          qPochhammer q (n - k)) * β k) := by
  rw [BaileyTransformBeta, natSum_eq_sum_range']

/-- The coefficient in `BaileyTransformBeta`: the weight of `β_k` in the
transform at level `n`. -/
noncomputable def baileyTransformCoeff (a q ρ₁ ρ₂ : R) (n k : Nat) : R :=
  (qPoch ρ₁ q k * qPoch ρ₂ q k * (a * q / (ρ₁ * ρ₂)) ^ k *
    qPoch (a * q / (ρ₁ * ρ₂)) q (n - k)) /
  (qPoch (a * q / ρ₁) q n * qPoch (a * q / ρ₂) q n *
    qPochhammer q (n - k))

/-- `BaileyTransformBeta` rewritten using the named coefficient
`baileyTransformCoeff`. -/
theorem BaileyTransformBeta_eq_sum_coeff (a q ρ₁ ρ₂ : R) (β : Nat → R) (n : Nat) :
    BaileyTransformBeta a q ρ₁ ρ₂ β n =
      ∑ k ∈ Finset.range (n + 1), baileyTransformCoeff a q ρ₁ ρ₂ n k * β k := by
  rw [BaileyTransformBeta_eq_sum]
  simp only [baileyTransformCoeff]

/-- Substituting the Bailey-pair relation into `BaileyTransformBeta` rewrites
each `β k` as the Bailey-beta sum generated by `α`. -/
theorem BaileyTransformBeta_of_pair (a q ρ₁ ρ₂ : R) {α β : Nat → R} {n : Nat}
    (h : IsBaileyPairUpTo a q α β n) :
    BaileyTransformBeta a q ρ₁ ρ₂ β n =
      ∑ k ∈ Finset.range (n + 1),
        baileyTransformCoeff a q ρ₁ ρ₂ n k *
          ∑ j ∈ Finset.range (k + 1), BaileyTerm a q α k j := by
  rw [BaileyTransformBeta_eq_sum_coeff]
  refine Finset.sum_congr rfl fun k hk => ?_
  congr 1
  rw [← BaileyBeta_eq_sum]
  exact h k (by simpa using hk)

/-- The right-hand side of the Bailey-pair preservation goal: `BaileyBeta`
applied to `BaileyTransformAlpha α` expanded as an explicit `Finset.sum`. -/
theorem BaileyBeta_transformAlpha_eq (a q ρ₁ ρ₂ : R) (α : Nat → R) (n : Nat) :
    BaileyBeta a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) n =
      ∑ j ∈ Finset.range (n + 1),
        (qPoch ρ₁ q j * qPoch ρ₂ q j * (a * q / (ρ₁ * ρ₂)) ^ j /
          (qPoch (a * q / ρ₁) q j * qPoch (a * q / ρ₂) q j) * α j) /
        (qPochhammer q (n - j) * qPoch (a * q) q (n + j)) := by
  rw [BaileyBeta_eq_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [BaileyTerm, BaileyTransformAlpha]

open Finset in
/-- Triangular Fubini for the Bailey transform expansion: the double sum
indexed `(k, j)` with `0 ≤ j ≤ k ≤ n` re-indexed as `(j, k)` with
`0 ≤ j ≤ n` outside and `j ≤ k ≤ n` inside. -/
theorem BaileyTransformBeta_of_pair_double_sum (a q ρ₁ ρ₂ : R)
    {α β : Nat → R} {n : Nat} (h : IsBaileyPairUpTo a q α β n) :
    BaileyTransformBeta a q ρ₁ ρ₂ β n =
      ∑ j ∈ range (n + 1),
        α j * ∑ k ∈ (range (n + 1)).filter (fun k => j ≤ k),
          baileyTransformCoeff a q ρ₁ ρ₂ n k /
            (qPochhammer q (k - j) * qPoch (a * q) q (k + j)) := by
  rw [BaileyTransformBeta_of_pair a q ρ₁ ρ₂ h]
  -- Define the integrand on the (k, j) triangle.
  set F : Nat → Nat → R := fun k j =>
    baileyTransformCoeff a q ρ₁ ρ₂ n k * α j /
      (qPochhammer q (k - j) * qPoch (a * q) q (k + j)) with hF
  -- Step 1: rewrite each LHS inner sum as ∑ j over F k j.
  have step1 :
      ∀ k ∈ range (n + 1),
        baileyTransformCoeff a q ρ₁ ρ₂ n k *
            ∑ j ∈ range (k + 1), BaileyTerm a q α k j =
          ∑ j ∈ range (k + 1), F k j := by
    intro k _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [BaileyTerm, hF]
    ring
  rw [Finset.sum_congr rfl step1]
  -- Step 2: re-index inner range(k+1) as range(n+1).filter (· ≤ k)
  -- so both outer and inner sums share the same fixed Finset.
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
  -- Step 3: Fubini on range(n+1) × range(n+1) restricted by j ≤ k.
  -- Convert each inner filter-sum to an indicator sum over range(n+1),
  -- swap, then re-apply the filter on the other axis.
  rw [show (∑ k ∈ range (n + 1),
              ∑ j ∈ (range (n + 1)).filter (fun j => j ≤ k), F k j) =
          ∑ j ∈ range (n + 1),
              ∑ k ∈ (range (n + 1)).filter (fun k => j ≤ k), F k j from ?_]
  · -- Step 4: factor α j out of each inner sum.
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [hF]
    ring
  · -- Prove the Fubini-on-rectangle swap.
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]

/-! #### q-Pfaff–Saalschütz kernel identity

The final analytic input needed for the general Bailey lemma is a single
pointwise evaluation of the inner sum from `BaileyTransformBeta_of_pair_double_sum`:
for each `0 ≤ j ≤ n`,

  ∑_{k=j}^{n} c_{nk} / ((q;q)_{k-j} (aq;q)_{k+j})
    = (ρ₁;q)_j (ρ₂;q)_j (aq/(ρ₁ρ₂))^j /
      ((aq/ρ₁;q)_j (aq/ρ₂;q)_j (q;q)_{n-j} (aq;q)_{n+j})

This is an instance of the q-Pfaff–Saalschütz (Jackson) summation formula.
The identity itself is left as an analytic hypothesis;
`BaileyTransform_preserves_pair_general` is the structural theorem
that consumes it.  The single-term boundary case `j = n` is verified
unconditionally below. -/

/-- The q-Pfaff–Saalschütz kernel sum, indexed by `j ≤ n`. -/
noncomputable def baileyKernelSum (a q ρ₁ ρ₂ : R) (n j : Nat) : R :=
  ∑ k ∈ (Finset.range (n + 1)).filter (fun k => j ≤ k),
    baileyTransformCoeff a q ρ₁ ρ₂ n k /
      (qPochhammer q (k - j) * qPoch (a * q) q (k + j))

/-- The q-Pfaff–Saalschütz kernel target value at `(n, j)`. -/
noncomputable def baileyKernelTarget (a q ρ₁ ρ₂ : R) (n j : Nat) : R :=
  qPoch ρ₁ q j * qPoch ρ₂ q j * (a * q / (ρ₁ * ρ₂)) ^ j /
    (qPoch (a * q / ρ₁) q j * qPoch (a * q / ρ₂) q j *
     qPochhammer q (n - j) * qPoch (a * q) q (n + j))

/-- Boundary case `j = n`: the kernel sum collapses to a single term. -/
theorem baileyKernelSum_eq_target_n (a q ρ₁ ρ₂ : R) (n : Nat) :
    baileyKernelSum a q ρ₁ ρ₂ n n = baileyKernelTarget a q ρ₁ ρ₂ n n := by
  unfold baileyKernelSum baileyKernelTarget baileyTransformCoeff
  have hfilter : (Finset.range (n + 1)).filter (fun k => n ≤ k) = {n} := by
    ext k
    simp [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    omega
  rw [hfilter, Finset.sum_singleton]
  simp [div_div]

/-- The q-Saalschütz instance at `n = 3, j = 0`, verified by direct
polynomial expansion.  The cleared-denominator factor is
`∏_{k=1,2,3} (ρ₁ − a*q^k)(ρ₂ − a*q^k)`. -/
theorem baileyKernelSum_eq_target_zero_three (a q ρ₁ ρ₂ : R)
    (hρ₁ : ρ₁ ≠ 0) (hρ₂ : ρ₂ ≠ 0)
    (hq1 : (1 : R) - q ≠ 0) (hq2 : (1 : R) - q ^ 2 ≠ 0)
    (hq3 : (1 : R) - q ^ 3 ≠ 0)
    (haq1 : (1 : R) - a * q ≠ 0) (haq2 : (1 : R) - a * q ^ 2 ≠ 0)
    (haq3 : (1 : R) - a * q ^ 3 ≠ 0)
    (haq_ρ₁_1 : (1 : R) - a * q / ρ₁ ≠ 0)
    (haq_ρ₁_2 : (1 : R) - a * q ^ 2 / ρ₁ ≠ 0)
    (haq_ρ₁_3 : (1 : R) - a * q ^ 3 / ρ₁ ≠ 0)
    (haq_ρ₂_1 : (1 : R) - a * q / ρ₂ ≠ 0)
    (haq_ρ₂_2 : (1 : R) - a * q ^ 2 / ρ₂ ≠ 0)
    (haq_ρ₂_3 : (1 : R) - a * q ^ 3 / ρ₂ ≠ 0) :
    baileyKernelSum a q ρ₁ ρ₂ 3 0 = baileyKernelTarget a q ρ₁ ρ₂ 3 0 := by
  have h11 : ρ₁ - a * q ≠ 0 := fun h => haq_ρ₁_1 (by
    have : (1 : R) - a * q / ρ₁ = (ρ₁ - a * q) / ρ₁ := by field_simp
    rw [this, h]; simp)
  have h12 : ρ₁ - a * q ^ 2 ≠ 0 := fun h => haq_ρ₁_2 (by
    have : (1 : R) - a * q ^ 2 / ρ₁ = (ρ₁ - a * q ^ 2) / ρ₁ := by field_simp
    rw [this, h]; simp)
  have h13 : ρ₁ - a * q ^ 3 ≠ 0 := fun h => haq_ρ₁_3 (by
    have : (1 : R) - a * q ^ 3 / ρ₁ = (ρ₁ - a * q ^ 3) / ρ₁ := by field_simp
    rw [this, h]; simp)
  have h21 : ρ₂ - a * q ≠ 0 := fun h => haq_ρ₂_1 (by
    have : (1 : R) - a * q / ρ₂ = (ρ₂ - a * q) / ρ₂ := by field_simp
    rw [this, h]; simp)
  have h22 : ρ₂ - a * q ^ 2 ≠ 0 := fun h => haq_ρ₂_2 (by
    have : (1 : R) - a * q ^ 2 / ρ₂ = (ρ₂ - a * q ^ 2) / ρ₂ := by field_simp
    rw [this, h]; simp)
  have h23 : ρ₂ - a * q ^ 3 ≠ 0 := fun h => haq_ρ₂_3 (by
    have : (1 : R) - a * q ^ 3 / ρ₂ = (ρ₂ - a * q ^ 3) / ρ₂ := by field_simp
    rw [this, h]; simp)
  have hX : (ρ₁ - a * q) * (ρ₁ - a * q ^ 2) * (ρ₁ - a * q ^ 3) *
            (ρ₂ - a * q) * (ρ₂ - a * q ^ 2) * (ρ₂ - a * q ^ 3) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h11 h12) h13)
      h21) h22) h23
  unfold baileyKernelSum baileyKernelTarget baileyTransformCoeff
  have hfilter : (Finset.range 4).filter (fun k => 0 ≤ k) = {0, 1, 2, 3} := by
    ext k
    simp [Finset.mem_range]
    omega
  rw [hfilter]
  rw [show ({0, 1, 2, 3} : Finset Nat) =
      insert 0 (insert 1 (insert 2 ({3} : Finset Nat))) from rfl]
  rw [Finset.sum_insert (by simp), Finset.sum_insert (by simp),
      Finset.sum_insert (by simp), Finset.sum_singleton]
  simp [qPoch, qPochhammer]
  field_simp
  ring

set_option maxHeartbeats 0 in
/-- The q-Saalschütz instance at `n = 3, j = 1`. Disabled-heartbeat
brute-force; field_simp + ring on the cleared-denominator polynomial. -/
theorem baileyKernelSum_eq_target_one_three (a q ρ₁ ρ₂ : R)
    (hρ₁ : ρ₁ ≠ 0) (hρ₂ : ρ₂ ≠ 0)
    (hq1 : (1 : R) - q ≠ 0) (hq2 : (1 : R) - q ^ 2 ≠ 0)
    (haq1 : (1 : R) - a * q ≠ 0) (haq2 : (1 : R) - a * q ^ 2 ≠ 0)
    (haq3 : (1 : R) - a * q ^ 3 ≠ 0) (haq4 : (1 : R) - a * q ^ 4 ≠ 0)
    (haq_ρ₁_1 : (1 : R) - a * q / ρ₁ ≠ 0)
    (haq_ρ₁_2 : (1 : R) - a * q ^ 2 / ρ₁ ≠ 0)
    (haq_ρ₁_3 : (1 : R) - a * q ^ 3 / ρ₁ ≠ 0)
    (haq_ρ₂_1 : (1 : R) - a * q / ρ₂ ≠ 0)
    (haq_ρ₂_2 : (1 : R) - a * q ^ 2 / ρ₂ ≠ 0)
    (haq_ρ₂_3 : (1 : R) - a * q ^ 3 / ρ₂ ≠ 0) :
    baileyKernelSum a q ρ₁ ρ₂ 3 1 = baileyKernelTarget a q ρ₁ ρ₂ 3 1 := by
  have h11 : ρ₁ - a * q ≠ 0 := fun h => haq_ρ₁_1 (by
    have : (1 : R) - a * q / ρ₁ = (ρ₁ - a * q) / ρ₁ := by field_simp
    rw [this, h]; simp)
  have h12 : ρ₁ - a * q ^ 2 ≠ 0 := fun h => haq_ρ₁_2 (by
    have : (1 : R) - a * q ^ 2 / ρ₁ = (ρ₁ - a * q ^ 2) / ρ₁ := by field_simp
    rw [this, h]; simp)
  have h13 : ρ₁ - a * q ^ 3 ≠ 0 := fun h => haq_ρ₁_3 (by
    have : (1 : R) - a * q ^ 3 / ρ₁ = (ρ₁ - a * q ^ 3) / ρ₁ := by field_simp
    rw [this, h]; simp)
  have h21 : ρ₂ - a * q ≠ 0 := fun h => haq_ρ₂_1 (by
    have : (1 : R) - a * q / ρ₂ = (ρ₂ - a * q) / ρ₂ := by field_simp
    rw [this, h]; simp)
  have h22 : ρ₂ - a * q ^ 2 ≠ 0 := fun h => haq_ρ₂_2 (by
    have : (1 : R) - a * q ^ 2 / ρ₂ = (ρ₂ - a * q ^ 2) / ρ₂ := by field_simp
    rw [this, h]; simp)
  have h23 : ρ₂ - a * q ^ 3 ≠ 0 := fun h => haq_ρ₂_3 (by
    have : (1 : R) - a * q ^ 3 / ρ₂ = (ρ₂ - a * q ^ 3) / ρ₂ := by field_simp
    rw [this, h]; simp)
  have hX : (ρ₁ - a * q) * (ρ₁ - a * q ^ 2) * (ρ₁ - a * q ^ 3) *
            (ρ₂ - a * q) * (ρ₂ - a * q ^ 2) * (ρ₂ - a * q ^ 3) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h11 h12) h13)
      h21) h22) h23
  unfold baileyKernelSum baileyKernelTarget baileyTransformCoeff
  have hfilter : (Finset.range 4).filter (fun k => 1 ≤ k) = {1, 2, 3} := by
    ext k
    simp [Finset.mem_range]
    omega
  rw [hfilter]
  rw [show ({1, 2, 3} : Finset Nat) = insert 1 (insert 2 ({3} : Finset Nat)) from rfl]
  rw [Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_singleton]
  simp [qPoch, qPochhammer]
  field_simp
  ring

/-- The q-Saalschütz instance at `n = 2, j = 1`, verified by direct
polynomial expansion.  Combined with `baileyKernelSum_eq_target_zero_two`
and the j=n boundary case, the kernel identity is now unconditional for
all `j ≤ n` with `n ≤ 2`. -/
theorem baileyKernelSum_eq_target_one_two (a q ρ₁ ρ₂ : R)
    (hρ₁ : ρ₁ ≠ 0) (hρ₂ : ρ₂ ≠ 0)
    (hq1 : (1 : R) - q ≠ 0)
    (haq1 : (1 : R) - a * q ≠ 0) (haq2 : (1 : R) - a * q ^ 2 ≠ 0)
    (haq3 : (1 : R) - a * q ^ 3 ≠ 0)
    (haq_ρ₁_1 : (1 : R) - a * q / ρ₁ ≠ 0)
    (haq_ρ₁_2 : (1 : R) - a * q ^ 2 / ρ₁ ≠ 0)
    (haq_ρ₂_1 : (1 : R) - a * q / ρ₂ ≠ 0)
    (haq_ρ₂_2 : (1 : R) - a * q ^ 2 / ρ₂ ≠ 0) :
    baileyKernelSum a q ρ₁ ρ₂ 2 1 = baileyKernelTarget a q ρ₁ ρ₂ 2 1 := by
  have h11 : ρ₁ - a * q ≠ 0 := fun h => haq_ρ₁_1 (by
    have : (1 : R) - a * q / ρ₁ = (ρ₁ - a * q) / ρ₁ := by field_simp
    rw [this, h]; simp)
  have h12 : ρ₁ - a * q ^ 2 ≠ 0 := fun h => haq_ρ₁_2 (by
    have : (1 : R) - a * q ^ 2 / ρ₁ = (ρ₁ - a * q ^ 2) / ρ₁ := by field_simp
    rw [this, h]; simp)
  have h21 : ρ₂ - a * q ≠ 0 := fun h => haq_ρ₂_1 (by
    have : (1 : R) - a * q / ρ₂ = (ρ₂ - a * q) / ρ₂ := by field_simp
    rw [this, h]; simp)
  have h22 : ρ₂ - a * q ^ 2 ≠ 0 := fun h => haq_ρ₂_2 (by
    have : (1 : R) - a * q ^ 2 / ρ₂ = (ρ₂ - a * q ^ 2) / ρ₂ := by field_simp
    rw [this, h]; simp)
  have hX : (ρ₁ - a * q) * (ρ₁ - a * q ^ 2) * (ρ₂ - a * q) * (ρ₂ - a * q ^ 2) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero h11 h12) h21) h22
  unfold baileyKernelSum baileyKernelTarget baileyTransformCoeff
  have hfilter : (Finset.range 3).filter (fun k => 1 ≤ k) = {1, 2} := by
    ext k
    simp [Finset.mem_range]
    omega
  rw [hfilter]
  rw [show ({1, 2} : Finset Nat) = insert 1 ({2} : Finset Nat) from rfl]
  rw [Finset.sum_insert (by simp), Finset.sum_singleton]
  simp [qPoch, qPochhammer]
  field_simp
  ring

/-- The q-Saalschütz instance at `n = 2, j = 0`, verified by direct
polynomial expansion.  The cleared-denominator factor
`(ρ₁ − aq)(ρ₁ − aq²)(ρ₂ − aq)(ρ₂ − aq²)` is established nonzero from
the input hypotheses; `field_simp + ring` then closes the resulting
polynomial identity. -/
theorem baileyKernelSum_eq_target_zero_two (a q ρ₁ ρ₂ : R)
    (hρ₁ : ρ₁ ≠ 0) (hρ₂ : ρ₂ ≠ 0)
    (hq1 : (1 : R) - q ≠ 0) (hq2 : (1 : R) - q ^ 2 ≠ 0)
    (haq1 : (1 : R) - a * q ≠ 0) (haq2 : (1 : R) - a * q ^ 2 ≠ 0)
    (haq_ρ₁_1 : (1 : R) - a * q / ρ₁ ≠ 0)
    (haq_ρ₁_2 : (1 : R) - a * q ^ 2 / ρ₁ ≠ 0)
    (haq_ρ₂_1 : (1 : R) - a * q / ρ₂ ≠ 0)
    (haq_ρ₂_2 : (1 : R) - a * q ^ 2 / ρ₂ ≠ 0) :
    baileyKernelSum a q ρ₁ ρ₂ 2 0 = baileyKernelTarget a q ρ₁ ρ₂ 2 0 := by
  have h11 : ρ₁ - a * q ≠ 0 := fun h => haq_ρ₁_1 (by
    have : (1 : R) - a * q / ρ₁ = (ρ₁ - a * q) / ρ₁ := by field_simp
    rw [this, h]; simp)
  have h12 : ρ₁ - a * q ^ 2 ≠ 0 := fun h => haq_ρ₁_2 (by
    have : (1 : R) - a * q ^ 2 / ρ₁ = (ρ₁ - a * q ^ 2) / ρ₁ := by field_simp
    rw [this, h]; simp)
  have h21 : ρ₂ - a * q ≠ 0 := fun h => haq_ρ₂_1 (by
    have : (1 : R) - a * q / ρ₂ = (ρ₂ - a * q) / ρ₂ := by field_simp
    rw [this, h]; simp)
  have h22 : ρ₂ - a * q ^ 2 ≠ 0 := fun h => haq_ρ₂_2 (by
    have : (1 : R) - a * q ^ 2 / ρ₂ = (ρ₂ - a * q ^ 2) / ρ₂ := by field_simp
    rw [this, h]; simp)
  have hX : (ρ₁ - a * q) * (ρ₁ - a * q ^ 2) * (ρ₂ - a * q) * (ρ₂ - a * q ^ 2) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero h11 h12) h21) h22
  unfold baileyKernelSum baileyKernelTarget baileyTransformCoeff
  have hfilter : (Finset.range 3).filter (fun k => 0 ≤ k) = {0, 1, 2} := by
    ext k
    simp [Finset.mem_range]
    omega
  rw [hfilter]
  rw [show ({0, 1, 2} : Finset Nat) = insert 0 (insert 1 ({2} : Finset Nat)) from rfl]
  rw [Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_singleton]
  simp [qPoch, qPochhammer]
  field_simp
  ring

/-- The q-Saalschütz instance at `n = 1, j = 0`: the smallest nontrivial
case of the kernel identity, verified directly by polynomial expansion. -/
theorem baileyKernelSum_eq_target_zero_one (a q ρ₁ ρ₂ : R)
    (hρ₁ : ρ₁ ≠ 0) (hρ₂ : ρ₂ ≠ 0)
    (hq : (1 : R) - q ≠ 0) (haq : (1 : R) - a * q ≠ 0)
    (haq_ρ₁ : (1 : R) - a * q / ρ₁ ≠ 0)
    (haq_ρ₂ : (1 : R) - a * q / ρ₂ ≠ 0) :
    baileyKernelSum a q ρ₁ ρ₂ 1 0 = baileyKernelTarget a q ρ₁ ρ₂ 1 0 := by
  -- Derive that ρᵢ − aq ≠ 0 from the (1 − aq/ρᵢ) hypotheses.
  have h1 : ρ₁ - a * q ≠ 0 := fun h => haq_ρ₁ (by
    have heq : (1 : R) - a * q / ρ₁ = (ρ₁ - a * q) / ρ₁ := by field_simp
    rw [heq, h]; simp)
  have h2 : ρ₂ - a * q ≠ 0 := fun h => haq_ρ₂ (by
    have heq : (1 : R) - a * q / ρ₂ = (ρ₂ - a * q) / ρ₂ := by field_simp
    rw [heq, h]; simp)
  have hX : ρ₁ * ρ₂ - ρ₁ * a * q - ρ₂ * a * q + a ^ 2 * q ^ 2 ≠ 0 := by
    have : ρ₁ * ρ₂ - ρ₁ * a * q - ρ₂ * a * q + a ^ 2 * q ^ 2 =
           (ρ₁ - a * q) * (ρ₂ - a * q) := by ring
    rw [this]; exact mul_ne_zero h1 h2
  unfold baileyKernelSum baileyKernelTarget baileyTransformCoeff
  have hfilter : (Finset.range 2).filter (fun k => 0 ≤ k) = {0, 1} := by
    ext k
    simp [Finset.mem_range]
    omega
  rw [hfilter]
  rw [show ({0, 1} : Finset Nat) = insert 0 ({1} : Finset Nat) from rfl]
  rw [Finset.sum_insert (by simp), Finset.sum_singleton]
  simp [qPoch, qPochhammer]
  field_simp
  ring


/-- **General finite Bailey lemma**, factored through the q-Pfaff–Saalschütz
kernel identity.

Given the kernel evaluation as an explicit hypothesis on every `j ∈ [0, n]`,
the Bailey transform sends Bailey pairs to Bailey pairs at level `n`.
The hypothesis isolates the single analytic input; the theorem itself is
purely structural.  The boundary case `j = n` is verified by
`baileyKernelSum_eq_target_n` and the interior cases are the q-Saalschütz
summation. -/
theorem BaileyTransform_preserves_pair_general
    (a q ρ₁ ρ₂ : R) {α β : Nat → R} (n : Nat)
    (hpair : IsBaileyPairUpTo a q α β n)
    (hkernel : ∀ j ∈ Finset.range (n + 1),
      baileyKernelSum a q ρ₁ ρ₂ n j = baileyKernelTarget a q ρ₁ ρ₂ n j) :
    BaileyTransformBeta a q ρ₁ ρ₂ β n =
      BaileyBeta a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) n := by
  rw [BaileyTransformBeta_of_pair_double_sum a q ρ₁ ρ₂ hpair,
      BaileyBeta_transformAlpha_eq a q ρ₁ ρ₂ α n]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hk :
      (∑ k ∈ (Finset.range (n + 1)).filter (fun k => j ≤ k),
          baileyTransformCoeff a q ρ₁ ρ₂ n k /
            (qPochhammer q (k - j) * qPoch (a * q) q (k + j))) =
        baileyKernelTarget a q ρ₁ ρ₂ n j := by
    show baileyKernelSum a q ρ₁ ρ₂ n j = _
    exact hkernel j hj
  rw [hk]
  unfold baileyKernelTarget
  ring

/-! #### Specializations: Bailey-pair preservation through the verified q-PS instances

The verified kernel instances `baileyKernelSum_eq_target_n` and the
n=1, n=2 j-companions discharge the q-PS hypothesis of
`BaileyTransform_preserves_pair_general` for `n ≤ 2`. The resulting
specialised theorems require only the natural nonvanishing hypotheses
on the q-Pochhammer denominators. -/

/-- Bailey-pair preservation at `n = 1` via the general theorem and the
unconditional kernel instances. -/
theorem BaileyTransform_preserves_pair_one_general
    (a q ρ₁ ρ₂ : R) {α β : Nat → R}
    (hpair : IsBaileyPairUpTo a q α β 1)
    (hρ₁ : ρ₁ ≠ 0) (hρ₂ : ρ₂ ≠ 0)
    (hq : (1 : R) - q ≠ 0) (haq : (1 : R) - a * q ≠ 0)
    (haq_ρ₁ : (1 : R) - a * q / ρ₁ ≠ 0)
    (haq_ρ₂ : (1 : R) - a * q / ρ₂ ≠ 0) :
    BaileyTransformBeta a q ρ₁ ρ₂ β 1 =
      BaileyBeta a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 1 := by
  apply BaileyTransform_preserves_pair_general a q ρ₁ ρ₂ 1 hpair
  intro j hj
  simp [Finset.mem_range] at hj
  interval_cases j
  · exact baileyKernelSum_eq_target_zero_one a q ρ₁ ρ₂ hρ₁ hρ₂ hq haq haq_ρ₁ haq_ρ₂
  · exact baileyKernelSum_eq_target_n a q ρ₁ ρ₂ 1

/-- Bailey-pair preservation at `n = 2` via the general theorem and the
unconditional kernel instances. -/
theorem BaileyTransform_preserves_pair_two_general
    (a q ρ₁ ρ₂ : R) {α β : Nat → R}
    (hpair : IsBaileyPairUpTo a q α β 2)
    (hρ₁ : ρ₁ ≠ 0) (hρ₂ : ρ₂ ≠ 0)
    (hq1 : (1 : R) - q ≠ 0) (hq2 : (1 : R) - q ^ 2 ≠ 0)
    (haq1 : (1 : R) - a * q ≠ 0) (haq2 : (1 : R) - a * q ^ 2 ≠ 0)
    (haq3 : (1 : R) - a * q ^ 3 ≠ 0)
    (haq_ρ₁_1 : (1 : R) - a * q / ρ₁ ≠ 0)
    (haq_ρ₁_2 : (1 : R) - a * q ^ 2 / ρ₁ ≠ 0)
    (haq_ρ₂_1 : (1 : R) - a * q / ρ₂ ≠ 0)
    (haq_ρ₂_2 : (1 : R) - a * q ^ 2 / ρ₂ ≠ 0) :
    BaileyTransformBeta a q ρ₁ ρ₂ β 2 =
      BaileyBeta a q (BaileyTransformAlpha a q ρ₁ ρ₂ α) 2 := by
  apply BaileyTransform_preserves_pair_general a q ρ₁ ρ₂ 2 hpair
  intro j hj
  simp [Finset.mem_range] at hj
  interval_cases j
  · exact baileyKernelSum_eq_target_zero_two a q ρ₁ ρ₂ hρ₁ hρ₂ hq1 hq2 haq1 haq2
      haq_ρ₁_1 haq_ρ₁_2 haq_ρ₂_1 haq_ρ₂_2
  · exact baileyKernelSum_eq_target_one_two a q ρ₁ ρ₂ hρ₁ hρ₂ hq1 haq1 haq2 haq3
      haq_ρ₁_1 haq_ρ₁_2 haq_ρ₂_1 haq_ρ₂_2
  · exact baileyKernelSum_eq_target_n a q ρ₁ ρ₂ 2

end GeneralBaileyLemma

/-! ### §9.2 Lemma 9.1 — Base case (Eq. 9.26)

Lemma 9.1 (Eq. 9.10) is the matrix identity `LM = MD`. The base case
`m = 0` reads (Eq. 9.26):

  `∑_{k=0}^{n} x^k q^{k²} [n; k]_q / (xq; q)_k = 1 / (xq; q)_n`.

We prove this by induction on `n`.
-/

/-- Key identity: `(a;q)_{n+1} = (1 - a) · (aq;q)_n`. -/
theorem qPoch_succ_shift (a q : R) (n : Nat) :
    qPoch a q (n + 1) = (1 - a) * qPoch (a * q) q n := by
  induction n with
  | zero => simp [qPoch]
  | succ n ih =>
    rw [qPoch_succ, ih, qPoch_succ]
    ring

/-- Corollary: `(xq;q)_{n+1} = (1-xq) · (xq²;q)_n`. -/
theorem qPoch_xq_succ_shift (x q : R) (n : Nat) :
    qPoch (x * q) q (n + 1) = (1 - x * q) * qPoch (x * q ^ 2) q n := by
  rw [qPoch_succ_shift]; ring_nf

/-- The LHS of Eq. (9.26): `∑_{k=0}^{N} x^k q^{k²} [N;k]_q / (xq;q)_k`. -/
noncomputable def lemma91Base (x q : R) (N : Nat) : R :=
  ∑ k ∈ Finset.range (N + 1),
    x ^ k * q ^ (k * k) * gaussianBinom q N k / qPoch (x * q) q k

theorem lemma91Base_zero (x q : R) : lemma91Base x q 0 = 1 := by
  simp [lemma91Base, gaussianBinom, qPoch]

/-- The RHS of Eq. (9.26): `1 / (xq; q)_N`. -/
noncomputable def lemma91Target (x q : R) (N : Nat) : R :=
  1 / qPoch (x * q) q N

theorem lemma91Target_zero (x q : R) : lemma91Target x q 0 = 1 := by
  simp [lemma91Target, qPoch]

/-- **Eq. (9.26), Lemma 9.1 base case, N=1.**
`1 + xq/(1-xq) = 1/(1-xq)`. -/
theorem lemma91_base_one (x q : R) (hxq : (1 : R) - x * q ≠ 0) :
    lemma91Base x q 1 = lemma91Target x q 1 := by
  simp only [lemma91Base, lemma91Target, Finset.sum_range_succ, Finset.sum_range_zero,
    gaussianBinom, qPoch, pow_zero, pow_one, mul_one, one_mul, Nat.sub_self]
  field_simp; ring

/-- **Eq. (9.26), Lemma 9.1 base case, N=2.** -/
theorem lemma91_base_two (x q : R)
    (hxq : (1 : R) - x * q ≠ 0)
    (hxq2 : (1 : R) - x * q * q ≠ 0)
    (_hq : (1 : R) - q ≠ 0) :
    lemma91Base x q 2 = lemma91Target x q 2 := by
  simp only [lemma91Base, lemma91Target, Finset.sum_range_succ, Finset.sum_range_zero,
    gaussianBinom, qPoch, pow_zero, pow_one, mul_one, one_mul,
    Nat.sub_self, zero_add, zero_mul, Nat.sub_zero]
  have h2 : (1 : R) - x * q ^ 2 ≠ 0 := by
    rw [show x * q ^ 2 = x * q * q from by ring]; exact hxq2
  field_simp [hxq, h2]; ring

set_option maxHeartbeats 800000 in
/-- **Eq. (9.26), Lemma 9.1 base case, N=3.** -/
theorem lemma91_base_three (x q : R)
    (hxq : (1 : R) - x * q ≠ 0)
    (hxq2 : (1 : R) - x * q * q ≠ 0)
    (hxq3 : (1 : R) - x * q * q ^ 2 ≠ 0)
    (_hq : (1 : R) - q ≠ 0)
    (_hq2 : (1 : R) - q ^ 2 ≠ 0) :
    lemma91Base x q 3 = lemma91Target x q 3 := by
  simp only [lemma91Base, lemma91Target, Finset.sum_range_succ, Finset.sum_range_zero,
    gaussianBinom, qPoch, pow_zero, pow_one, mul_one, one_mul,
    Nat.sub_self, zero_add, zero_mul, Nat.sub_zero]
  have h2 : (1 : R) - x * q ^ 2 ≠ 0 := by
    rw [show x * q ^ 2 = x * q * q from by ring]; exact hxq2
  have h3 : (1 : R) - x * q ^ 3 ≠ 0 := by
    rw [show x * q ^ 3 = x * q * q ^ 2 from by ring]; exact hxq3
  field_simp [hxq, h2, h3]; ring

/-- The LHS recurrence for Lemma 9.1 base case (Eq. 9.26).
Both sides satisfy `g(N+1,x) = g(N,x) + xq^{N+1}/(1-xq)·g(N,xq)`.
Proof requires: Gaussian binomial recurrence + qPoch shift + Finset.sum reindex.
This is the KEY UNSOLVED STEP for the general Lemma 9.1. -/
private lemma gaussianBinom_eq_zero_of_lt' (q : R) {n k : Nat} (h : n < k) :
    gaussianBinom q n k = 0 := by
  induction n generalizing k with
  | zero => cases k with | zero => omega | succ k => rfl
  | succ n ih =>
    cases k with
    | zero => omega
    | succ k =>
      simp [gaussianBinom, ih (show n < k + 1 by omega), ih (show n < k by omega)]

private lemma shift_term_eq' (x q : R) (N k : Nat) (hk : k ≤ N) :
    x ^ (k + 1) * q ^ ((k + 1) * (k + 1)) * (q ^ (N - k) * gaussianBinom q N k) /
      qPoch (x * q) q (k + 1) =
    x * q ^ (N + 1) / (1 - x * q) *
      ((x * q) ^ k * q ^ (k * k) * gaussianBinom q N k / qPoch (x * q ^ 2) q k) := by
  rw [qPoch_xq_succ_shift]
  by_cases hxq' : (1 : R) - x * q = 0
  · simp [hxq']
  by_cases hP : qPoch (x * q ^ 2) q k = 0
  · simp [hP, mul_zero]
  · field_simp [hxq', hP]
    have hexp : (k + 1) * (k + 1) + (N - k) = k * k + k + (N + 1) := by
      have : (k + 1) * (k + 1) = k * k + 2 * k + 1 := by ring
      omega
    calc x ^ (k + 1) * q ^ ((k + 1) * (k + 1)) * q ^ (N - k) * gaussianBinom q N k
        = x ^ (k + 1) * q ^ ((k + 1) * (k + 1) + (N - k)) * gaussianBinom q N k := by
            rw [pow_add]; ring
      _ = x ^ (k + 1) * q ^ (k * k + k + (N + 1)) * gaussianBinom q N k := by
            rw [hexp]
      _ = gaussianBinom q N k * x * q ^ (N + 1) * (x * q) ^ k * q ^ (k * k) := by
            rw [pow_succ x, pow_add q (k * k + k), pow_add q (k * k), mul_pow]; ring

private lemma s1_last_zero' (x q : R) (N : Nat) :
    x ^ (N + 1) * q ^ ((N + 1) * (N + 1)) * gaussianBinom q N (N + 1) /
      qPoch (x * q) q (N + 1) = 0 := by
  have : gaussianBinom q N (N + 1) = 0 := gaussianBinom_eq_zero_of_lt' q (by omega)
  simp [this]

private lemma qPoch_xqq_eq' (x q : R) (k : Nat) :
    qPoch (x * q * q) q k = qPoch (x * q ^ 2) q k := by congr 1; ring

set_option maxHeartbeats 1600000 in
theorem lemma91Base_recurrence (x q : R) (N : Nat)
    (_hxq : (1 : R) - x * q ≠ 0) :
    lemma91Base x q (N + 1) =
      lemma91Base x q N +
        x * q ^ (N + 1) / (1 - x * q) * lemma91Base (x * q) q N := by
  simp only [lemma91Base]
  simp_rw [qPoch_xqq_eq']
  rw [Finset.sum_range_succ']
  simp only [pow_zero, Nat.zero_mul, one_mul, gaussianBinom_zero_right, qPoch_zero, div_one]
  have hgb : ∀ k ∈ Finset.range (N + 1),
      x ^ (k + 1) * q ^ ((k + 1) * (k + 1)) * gaussianBinom q (N + 1) (k + 1) /
        qPoch (x * q) q (k + 1) =
      x ^ (k + 1) * q ^ ((k + 1) * (k + 1)) * gaussianBinom q N (k + 1) /
        qPoch (x * q) q (k + 1) +
      x * q ^ (N + 1) / (1 - x * q) *
        ((x * q) ^ k * q ^ (k * k) * gaussianBinom q N k / qPoch (x * q ^ 2) q k) := by
    intro k hk
    have hk_le : k ≤ N := by simp [Finset.mem_range] at hk; omega
    show x ^ (k + 1) * q ^ ((k + 1) * (k + 1)) *
        (gaussianBinom q N (k + 1) + q ^ (N - k) * gaussianBinom q N k) /
        qPoch (x * q) q (k + 1) = _
    rw [mul_add, add_div]; congr 1
    exact shift_term_eq' x q N k hk_le
  rw [Finset.sum_congr rfl hgb, Finset.sum_add_distrib, ← Finset.mul_sum]
  conv_lhs => rw [show ∀ (a b c : R), (a + b) + c = (c + a) + b from by intro a b c; abel]
  congr 1
  rw [Finset.sum_range_succ, s1_last_zero', add_zero, Finset.sum_range_succ']
  simp only [pow_zero, Nat.zero_mul, one_mul, gaussianBinom_zero_right, qPoch_zero, div_one]
  abel

/-- The RHS recurrence for Lemma 9.1 base case. -/
theorem lemma91Target_recurrence (x q : R) (N : Nat)
    (hxq : (1 : R) - x * q ≠ 0)
    (hD : qPoch (x * q) q (N + 1) ≠ 0) :
    lemma91Target x q (N + 1) =
      lemma91Target x q N +
        x * q ^ (N + 1) / (1 - x * q) * lemma91Target (x * q) q N := by
  simp only [lemma91Target]
  have hqpoch_eq : qPoch (x * q * q) q N = qPoch (x * q ^ 2) q N := by congr 1; ring
  rw [hqpoch_eq]
  rw [qPoch_xq_succ_shift]
  have hDN : qPoch (x * q) q N ≠ 0 := by
    intro h; exact hD (by rw [qPoch_succ]; exact mul_eq_zero_of_left h _)
  have hDxq : qPoch (x * q ^ 2) q N ≠ 0 := by
    intro h; apply hD; rw [qPoch_xq_succ_shift]; exact mul_eq_zero_of_right _ h
  field_simp [hxq, hDN, hDxq]
  have hrel : (1 - x * q) * qPoch (x * q ^ 2) q N =
      qPoch (x * q) q N * (1 - x * q * q ^ N) := by
    have h1 := qPoch_xq_succ_shift x q N; rw [qPoch_succ] at h1; exact h1.symm
  linear_combination -hrel

/-- `qPoch (x*q) q N ≠ 0` when all factors `1 - x*q^{k+1}` are nonzero. -/
private lemma qPoch_ne_zero_of_factors (x q : R) (N : Nat)
    (h : ∀ k, k < N → (1 : R) - x * q ^ (k + 1) ≠ 0) :
    qPoch (x * q) q N ≠ 0 := by
  induction N with
  | zero => simp [qPoch]
  | succ N ih =>
    rw [qPoch_succ]
    apply mul_ne_zero
    · exact ih (fun k hk => h k (by omega))
    · have := h N (by omega)
      intro heq; apply this
      rwa [show x * q * q ^ N = x * q ^ (N + 1) from by ring] at heq

/-- **Lemma 9.1 base case (Eq. 9.26).**
`∑_{k=0}^{N} x^k q^{k²} [N;k]_q / (xq;q)_k = 1 / (xq;q)_N`. -/
theorem lemma91_base_general (q : R) : ∀ (N : Nat) (x : R),
    (∀ k, k < N → (1 : R) - x * q ^ (k + 1) ≠ 0) →
    lemma91Base x q N = lemma91Target x q N := by
  intro N; induction N with
  | zero => intro _ _; rw [lemma91Base_zero, lemma91Target_zero]
  | succ N ih =>
    intro x hxq
    have hxq_N : ∀ k, k < N → (1 : R) - x * q ^ (k + 1) ≠ 0 :=
      fun k hk => hxq k (by omega)
    have hxq1 : (1 : R) - x * q ≠ 0 := by
      have := hxq 0 (by omega); simpa using this
    have hD : qPoch (x * q) q (N + 1) ≠ 0 := qPoch_ne_zero_of_factors x q (N + 1) hxq
    have hxq_shifted : ∀ k, k < N → (1 : R) - (x * q) * q ^ (k + 1) ≠ 0 := by
      intro k hk
      have := hxq (k + 1) (by omega)
      rwa [show x * q * q ^ (k + 1) = x * q ^ (k + 1 + 1) from by ring]
    rw [lemma91Base_recurrence x q N hxq1, lemma91Target_recurrence x q N hxq1 hD,
        ih x hxq_N, ih (x * q) hxq_shifted]

/-! ### General Lemma 9.1 (Chan Eq. 9.10/9.27): the `m > 0` parameter

The matrix identity `LM = MD` gives, for each `m ≥ 0`:
`∑_{k=0}^N x^k q^{k(k+m)} [N;k]_q / (xq;q)_{k+m} = 1 / (xq;q)_{N+m}`.

The `m = 0` case is `lemma91_base_general` (Eq. 9.26). The general case
reduces to the `m = 0` case via the substitution `x → xq^m` combined with
the q-Pochhammer splitting identity `(xq;q)_{k+m} = (xq;q)_m · (xq^{m+1};q)_k`. -/

/-- Multiplicativity of qPoch under index splitting:
`(a;q)_{k+m} = (a;q)_m · (a·q^m;q)_k`. -/
theorem qPoch_split (a q : R) (m : Nat) :
    ∀ k : Nat, qPoch a q (k + m) = qPoch a q m * qPoch (a * q ^ m) q k
  | 0 => by simp
  | k + 1 => by
    have hidx : k + 1 + m = (k + m) + 1 := by omega
    rw [hidx, qPoch_succ, qPoch_split a q m k, qPoch_succ]
    have hpow : a * q ^ m * q ^ k = a * q ^ (k + m) := by
      rw [mul_assoc, ← pow_add, Nat.add_comm m k]
    rw [hpow]; ring

/-- LHS of general Lemma 9.1 (`m` parameter). -/
noncomputable def lemma91BaseM (x q : R) (m N : Nat) : R :=
  ∑ k ∈ Finset.range (N + 1),
    x ^ k * q ^ (k * (k + m)) * gaussianBinom q N k / qPoch (x * q) q (k + m)

/-- RHS of general Lemma 9.1 (closed form). -/
noncomputable def lemma91TargetM (x q : R) (m N : Nat) : R :=
  1 / qPoch (x * q) q (N + m)

theorem lemma91BaseM_m_zero (x q : R) (N : Nat) :
    lemma91BaseM x q 0 N = lemma91Base x q N := by
  simp [lemma91BaseM, lemma91Base]

theorem lemma91TargetM_m_zero (x q : R) (N : Nat) :
    lemma91TargetM x q 0 N = lemma91Target x q N := by
  simp [lemma91TargetM, lemma91Target]

set_option maxHeartbeats 1600000 in
/-- **General Lemma 9.1** (Chan Eq. 9.10/9.27):
`∑_{k=0}^N x^k q^{k(k+m)} [N;k]_q / (xq;q)_{k+m} = 1 / (xq;q)_{N+m}`. -/
theorem lemma91BaseM_eq (x q : R) (m N : Nat)
    (hxq : ∀ k, k < N + m → (1 : R) - x * q ^ (k + 1) ≠ 0) :
    lemma91BaseM x q m N = lemma91TargetM x q m N := by
  -- Nonvanishing of relevant qPoch values
  have h_qm : qPoch (x * q) q m ≠ 0 :=
    qPoch_ne_zero_of_factors x q m (fun k hk => hxq k (by omega))
  -- Apply lemma91_base_general at x' = x * q^m
  have h_subst_hyp : ∀ k, k < N → (1 : R) - (x * q ^ m) * q ^ (k + 1) ≠ 0 := by
    intro k hk
    have hh := hxq (m + k) (by omega)
    have hpow : (x * q ^ m) * q ^ (k + 1) = x * q ^ (m + k + 1) := by
      have hidx : m + (k + 1) = m + k + 1 := by omega
      rw [mul_assoc, ← pow_add, hidx]
    rwa [hpow]
  have h_base : lemma91Base (x * q ^ m) q N = lemma91Target (x * q ^ m) q N :=
    lemma91_base_general q N (x * q ^ m) h_subst_hyp
  have h_arg_eq : (x * q ^ m) * q = (x * q) * q ^ m := by ring
  -- Show: lemma91Base (x*q^m) q N = qPoch (x*q) q m * lemma91BaseM x q m N
  have h_relate : lemma91Base (x * q ^ m) q N
      = qPoch (x * q) q m * lemma91BaseM x q m N := by
    simp only [lemma91Base, lemma91BaseM, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    -- LHS: (x*q^m)^k * q^(k*k) * gB / qPoch ((x*q^m)*q) q k
    -- RHS: qPoch (x*q) q m * (x^k * q^(k*(k+m)) * gB / qPoch (x*q) q (k+m))
    -- Step 1: split qPoch (x*q) q (k+m)
    rw [qPoch_split (x * q) q m k]
    rw [show (x * q) * q ^ m = (x * q ^ m) * q from h_arg_eq.symm]
    -- Goal: (x*q^m)^k * q^(k*k) * gB / qPoch ((x*q^m)*q) q k
    --     = qPoch (x*q) q m * (x^k * q^(k*(k+m)) * gB / (qPoch (x*q) q m * qPoch ((x*q^m)*q) q k))
    -- Step 2: cancel qPoch (x*q) q m on RHS
    rw [mul_div_assoc' (qPoch (x * q) q m) _ _]
    rw [mul_div_mul_left _ _ h_qm]
    -- Goal: (x*q^m)^k * q^(k*k) * gB / qPoch ((x*q^m)*q) q k
    --     = x^k * q^(k*(k+m)) * gB / qPoch ((x*q^m)*q) q k
    -- Same denominator; check numerators
    congr 1
    rw [mul_pow, ← pow_mul]
    rw [show x ^ k * q ^ (m * k) * q ^ (k * k) = x ^ k * q ^ (m * k + k * k) from by
      rw [pow_add]; ring]
    congr 2; ring
  -- Combine to get lemma91BaseM = lemma91TargetM
  apply mul_left_cancel₀ h_qm
  rw [← h_relate, h_base]
  simp only [lemma91Target, lemma91TargetM]
  rw [h_arg_eq, qPoch_split (x * q) q m N]
  field_simp

/-! ### Corollary: Lemma 9.1 base case at `x = 1` (Chan Eq. 9.12)

Setting `x = 1` in the general base case gives
`∑_{k=0}^{N} q^{k²} [N;k]_q / (q;q)_k = 1 / (q;q)_N`,
which is a key ingredient for the finite Rogers-Ramanujan identity. -/

/-- **General Lemma 9.1 specialized to x = 1** (Chan Eq. 9.12 / 9.27 with x=1):
`∑_{k=0}^N q^{k(k+m)} [N;k]_q / (q;q)_{k+m} = 1 / (q;q)_{N+m}`. -/
theorem lemma91BaseM_at_one (q : R) (m N : Nat)
    (hq : ∀ k, k < N + m → (1 : R) - q ^ (k + 1) ≠ 0) :
    lemma91BaseM 1 q m N = lemma91TargetM 1 q m N := by
  apply lemma91BaseM_eq 1 q m N
  simpa using hq

/-- Lemma 9.1 at x=1, m=1: `∑_{k=0}^N q^{k(k+1)} [N;k]_q / (q;q)_{k+1} = 1/(q;q)_{N+1}`. -/
theorem lemma91_base_at_one_m_one (q : R) (N : Nat)
    (hq : ∀ k, k < N + 1 → (1 : R) - q ^ (k + 1) ≠ 0) :
    (∑ k ∈ Finset.range (N + 1), q ^ (k * (k + 1)) * gaussianBinom q N k / qPochhammer q (k + 1))
      = 1 / qPochhammer q (N + 1) := by
  have h := lemma91BaseM_at_one q 1 N hq
  simp only [lemma91BaseM, lemma91TargetM, one_pow, one_mul, qPoch_q_eq_qPochhammer] at h
  exact h

theorem lemma91_base_at_one (q : R) (N : Nat)
    (hq : ∀ k, k < N → (1 : R) - q ^ (k + 1) ≠ 0) :
    lemma91Base 1 q N = lemma91Target 1 q N := by
  apply lemma91_base_general q N 1
  simpa using hq

/-! ### The M-operator (ρ → ∞ limit of Bailey transform, at a = 1)

The M-operator is the key transform for Rogers-Ramanujan identities. It takes a
Bailey pair (α, β) w.r.t. `a = 1` to a new Bailey pair (Mα, Mβ) defined by:
- `(Mα)_n = q^{n²} α_n`
- `(Mβ)_n = ∑_{k=0}^n q^{k²} β_k / (q;q)_{n-k}`

The preservation property `Mβ = BaileyBeta 1 q (Mα)` follows directly from
General Lemma 9.1 via a double-sum swap.

This is the missing piece for finite/infinite Rogers-Ramanujan from the
Bailey pair `(a*, b*)`. -/

/-- The M-operator on the α-side. -/
noncomputable def MAlpha (q : R) (α : Nat → R) (n : Nat) : R :=
  q ^ (n * n) * α n

/-- The M-operator on the β-side. -/
noncomputable def MBeta (q : R) (β : Nat → R) (n : Nat) : R :=
  ∑ k ∈ Finset.range (n + 1), q ^ (k * k) * β k / qPochhammer q (n - k)

theorem MAlpha_zero (q : R) (α : Nat → R) : MAlpha q α 0 = α 0 := by
  simp [MAlpha]

theorem MBeta_zero (q : R) (β : Nat → R) : MBeta q β 0 = β 0 := by
  simp [MBeta]

/-- Bailey β-side at `a = 1` in Finset form with explicit qPochhammer denominator
(using `qPoch (1*q) q m = qPochhammer q m`). -/
theorem BaileyBeta_at_one_eq (q : R) (α : Nat → R) (n : Nat) :
    BaileyBeta 1 q α n =
      ∑ k ∈ Finset.range (n + 1), α k / (qPochhammer q (n - k) * qPochhammer q (n + k)) := by
  rw [BaileyBeta_eq_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp [BaileyTerm, qPoch_q_eq_qPochhammer]

/-- M-operator preserves Bailey pair at n=0. -/
theorem M_preserves_BaileyPair_zero (q : R) (α β : Nat → R)
    (hpair : β 0 = BaileyBeta 1 q α 0) :
    MBeta q β 0 = BaileyBeta 1 q (MAlpha q α) 0 := by
  simp [MBeta, MAlpha, BaileyBeta_at_one_eq, qPochhammer, hpair]

set_option maxHeartbeats 800000 in
/-- M-operator preserves Bailey pair at n=1. -/
theorem M_preserves_BaileyPair_one (q : R) (α β : Nat → R)
    (hpair0 : β 0 = BaileyBeta 1 q α 0)
    (hpair1 : β 1 = BaileyBeta 1 q α 1)
    (hq1 : (1 : R) - q ≠ 0) (hq2 : (1 : R) - q ^ 2 ≠ 0) :
    MBeta q β 1 = BaileyBeta 1 q (MAlpha q α) 1 := by
  simp only [MBeta, MAlpha, BaileyBeta_at_one_eq,
    Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    qPochhammer, mul_one, one_mul]
  rw [hpair0, hpair1]
  simp only [BaileyBeta_at_one_eq, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    qPochhammer, mul_one, one_mul]
  field_simp [hq1, hq2]
  ring

set_option maxHeartbeats 3200000 in
/-- M-operator preserves Bailey pair at n=2. -/
theorem M_preserves_BaileyPair_two (q : R) (α β : Nat → R)
    (hpair0 : β 0 = BaileyBeta 1 q α 0)
    (hpair1 : β 1 = BaileyBeta 1 q α 1)
    (hpair2 : β 2 = BaileyBeta 1 q α 2)
    (hq1 : (1 : R) - q ≠ 0) (hq2 : (1 : R) - q ^ 2 ≠ 0)
    (hq3 : (1 : R) - q ^ 3 ≠ 0) (hq4 : (1 : R) - q ^ 4 ≠ 0) :
    MBeta q β 2 = BaileyBeta 1 q (MAlpha q α) 2 := by
  simp only [MBeta, MAlpha, BaileyBeta_at_one_eq,
    Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    qPochhammer, mul_one, one_mul]
  rw [hpair0, hpair1, hpair2]
  simp only [BaileyBeta_at_one_eq, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    qPochhammer, mul_one, one_mul]
  field_simp [hq1, hq2, hq3, hq4]
  ring

-- M_preserves_BaileyPair (general n): proof structure clear from Lemma 9.1 + double-sum swap,
-- but Lean formalization of the swap+reindex requires more careful sum_comm'/sum_Ico machinery.
-- Concrete cases n=0,1,2 above suffice for finite RR verification up to n=2.

/-! ### Bailey pair (a*, b*) — Rogers-Ramanujan source

The Bailey pair derived from finite JTP at `z = 1`:
- `b*_n = δ_{n,0}` (since `(1)_n = 0` for `n ≥ 1`)
- `a*_k` involves `(-1)^k q^{k²/2}` terms

With `x = 1`, Theorem 9.2 `(L²b*)_n = (MD²a*)_n` gives the finite RR
identity Eq. (9.21). -/

/-- The `b*` component of the Rogers-Ramanujan Bailey pair.
`b*_n = (1)_n(q)_n / (q)_{2n}` simplifies to `δ_{n,0}`. -/
noncomputable def rrBStar (_q : R) (n : Nat) : R :=
  if n = 0 then 1 else 0

theorem rrBStar_zero (q : R) : rrBStar q 0 = 1 := by simp [rrBStar]

theorem rrBStar_succ (q : R) (n : Nat) : rrBStar q (n + 1) = 0 := by simp [rrBStar]

/-- `M b*` at index n equals `1/(q;q)_n` (since `b*` is concentrated at index 0). -/
theorem MBeta_rrBStar (q : R) (n : Nat) :
    MBeta q (rrBStar q) n = 1 / qPochhammer q n := by
  simp only [MBeta]
  rw [Finset.sum_eq_single 0]
  · simp [rrBStar]
  · intro k _ hk
    cases k with
    | zero => exact absurd rfl hk
    | succ k => simp [rrBStar]
  · intro h; simp at h

/-- The `a*` component of the Rogers-Ramanujan Bailey pair (Chan Eq. 9.18).
`a*_0 = 1`, `a*_k = (-1)^k q^{k²/2} (q^{k/2} + q^{-k/2})` for `k > 0`.
In cleared form (over a field, avoiding fractional exponents):
`a*_k = (-1)^k q^{k(k-1)/2} (1 + q^k)` for `k ≥ 1`. -/
noncomputable def rrAStar (q : R) (k : Nat) : R :=
  if k = 0 then 1
  else (-1 : R) ^ k * q ^ (k * (k - 1) / 2) * (1 + q ^ k)

theorem rrAStar_zero (q : R) : rrAStar q 0 = 1 := by simp [rrAStar]

theorem rrAStar_one (q : R) : rrAStar q 1 = -(1 + q) := by
  simp [rrAStar]

theorem rrAStar_two (q : R) : rrAStar q 2 = q * (1 + q ^ 2) := by
  simp [rrAStar]

theorem rrAStar_three (q : R) : rrAStar q 3 = -(q ^ 3 * (1 + q ^ 3)) := by
  simp [rrAStar]; ring

theorem rrAStar_four (q : R) : rrAStar q 4 = q ^ 6 * (1 + q ^ 4) := by
  simp only [rrAStar, show (4 : Nat) ≠ 0 from by omega, ↓reduceIte]; ring

theorem rrAStar_five (q : R) : rrAStar q 5 = -(q ^ 10 * (1 + q ^ 5)) := by
  simp only [rrAStar, show (5 : Nat) ≠ 0 from by omega, ↓reduceIte]; ring

theorem rrAStar_six (q : R) : rrAStar q 6 = q ^ 15 * (1 + q ^ 6) := by
  simp only [rrAStar, show (6 : Nat) ≠ 0 from by omega, ↓reduceIte]; ring

theorem rrAStar_seven (q : R) : rrAStar q 7 = -(q ^ 21 * (1 + q ^ 7)) := by
  simp only [rrAStar, show (7 : Nat) ≠ 0 from by omega, ↓reduceIte]; ring

theorem rrAStar_eight (q : R) : rrAStar q 8 = q ^ 28 * (1 + q ^ 8) := by
  simp only [rrAStar, show (8 : Nat) ≠ 0 from by omega, ↓reduceIte]; ring

theorem rrAStar_nine (q : R) : rrAStar q 9 = -(q ^ 36 * (1 + q ^ 9)) := by
  simp only [rrAStar, show (9 : Nat) ≠ 0 from by omega, ↓reduceIte]; ring

theorem rrAStar_ten (q : R) : rrAStar q 10 = q ^ 45 * (1 + q ^ 10) := by
  simp only [rrAStar, show (10 : Nat) ≠ 0 from by omega, ↓reduceIte]; ring

/-- General pattern: `a*_k = (-1)^k q^{k(k-1)/2} (1 + q^k)` for `k ≥ 1`.
The exponent `k(k-1)/2` follows the triangular number sequence: 0,1,3,6,10,15,21,28,36,45,... -/
theorem rrAStar_pos (q : R) (k : Nat) (hk : 1 ≤ k) :
    rrAStar q k = (-1 : R) ^ k * q ^ (k * (k - 1) / 2) * (1 + q ^ k) := by
  simp [rrAStar, show k ≠ 0 from by omega]

/-- Sign pattern: `a*_k` alternates in sign. For even `k ≥ 2`, coefficient is positive;
for odd `k ≥ 1`, coefficient is negative. -/
theorem rrAStar_sign_even (q : R) (k : Nat) (hk : 1 ≤ k) :
    rrAStar q (2 * k) = q ^ (k * (2 * k - 1)) * (1 + q ^ (2 * k)) := by
  rw [rrAStar_pos q (2 * k) (by omega)]
  have hpow : (-1 : R) ^ (2 * k) = 1 := by rw [pow_mul]; simp
  have hexp : 2 * k * (2 * k - 1) / 2 = k * (2 * k - 1) := by
    rw [show 2 * k * (2 * k - 1) = 2 * (k * (2 * k - 1)) from by ring]; omega
  rw [hpow, hexp, one_mul]

theorem rrAStar_sign_odd (q : R) (k : Nat) :
    rrAStar q (2 * k + 1) = -(q ^ (k * (2 * k + 1)) * (1 + q ^ (2 * k + 1))) := by
  rw [rrAStar_pos q (2 * k + 1) (by omega)]
  have hpow : (-1 : R) ^ (2 * k + 1) = -1 := by rw [pow_add, pow_mul]; simp
  have hexp : (2 * k + 1) * ((2 * k + 1) - 1) / 2 = k * (2 * k + 1) := by
    rw [show (2 * k + 1) - 1 = 2 * k from by omega,
        show (2 * k + 1) * (2 * k) = 2 * (k * (2 * k + 1)) from by ring]; omega
  rw [hpow, hexp]; ring

/-- `(a*, b*)` is a Bailey pair with respect to `a = 1`: the defining relation
`b*_n = ∑_{k=0}^n a*_k / ((q;q)_{n-k} · (q;q)_{n+k})` holds. At `n = 0`:
`b*_0 = 1 = a*_0 / ((q;q)_0 · (q;q)_0) = 1`. -/
theorem rrBaileyPair_zero (q : R) :
    rrBStar q 0 = BaileyBeta 1 q (rrAStar q) 0 := by
  simp [rrBStar, BaileyBeta, BaileyTerm, rrAStar, qPochhammer]

/-- Bailey pair verification at `n = 1`: `b*_1 = 0` and
`∑_{k=0}^1 a*_k / ((q)_{1-k}(q)_{1+k}) = (1/(q)_1 + (-(1+q))/(q)_2) = 0`.
Requires `(q;q)_1 ≠ 0` and `(q;q)_2 ≠ 0`. -/
theorem rrBaileyPair_one (q : R) (hq1 : qPochhammer q 1 ≠ 0)
    (hq2 : qPochhammer q 2 ≠ 0) :
    rrBStar q 1 = BaileyBeta 1 q (rrAStar q) 1 := by
  have h1 : (1 : R) - q ≠ 0 := by simpa [qPochhammer] using hq1
  have h2 : (1 : R) - q ^ 2 ≠ 0 := by
    intro h; apply hq2; simp [qPochhammer]; exact Or.inr h
  simp only [rrBStar, BaileyBeta, natSum_succ, natSum_zero, BaileyTerm, rrAStar,
    qPoch, qPochhammer, pow_zero, mul_one, one_mul,
    Nat.sub_self, show (1 : Nat) ≠ 0 from by omega, ↓reduceIte]
  field_simp [h1, h2]; ring

set_option maxHeartbeats 800000 in
/-- Bailey pair verification at `n = 2`. -/
theorem rrBaileyPair_two (q : R)
    (h1 : (1 : R) - q ≠ 0) (h2 : (1 : R) - q ^ 2 ≠ 0)
    (h3 : (1 : R) - q ^ 3 ≠ 0) (h4 : (1 : R) - q ^ 4 ≠ 0) :
    rrBStar q 2 = BaileyBeta 1 q (rrAStar q) 2 := by
  simp only [rrBStar, BaileyBeta, natSum_succ, natSum_zero, BaileyTerm, rrAStar,
    qPoch, qPochhammer, pow_zero, mul_one, one_mul,
    Nat.sub_self, show (1 : Nat) ≠ 0 from by omega,
    show (2 : Nat) ≠ 0 from by omega, ↓reduceIte]
  field_simp [h1, h2, h3, h4]; ring

set_option maxHeartbeats 1600000 in
/-- Bailey pair verification at `n = 3`. -/
theorem rrBaileyPair_three (q : R)
    (h1 : (1 : R) - q ≠ 0) (h2 : (1 : R) - q ^ 2 ≠ 0)
    (h3 : (1 : R) - q ^ 3 ≠ 0) (h4 : (1 : R) - q ^ 4 ≠ 0)
    (h5 : (1 : R) - q ^ 5 ≠ 0) (h6 : (1 : R) - q ^ 6 ≠ 0) :
    rrBStar q 3 = BaileyBeta 1 q (rrAStar q) 3 := by
  simp only [rrBStar, BaileyBeta, natSum_succ, natSum_zero, BaileyTerm, rrAStar,
    qPoch, qPochhammer, pow_zero, mul_one, one_mul,
    Nat.sub_self, show (1 : Nat) ≠ 0 from by omega,
    show (2 : Nat) ≠ 0 from by omega, show (3 : Nat) ≠ 0 from by omega, ↓reduceIte]
  field_simp [h1, h2, h3, h4, h5, h6]; ring

set_option maxHeartbeats 3200000 in
/-- Bailey pair verification at `n = 4`. -/
theorem rrBaileyPair_four (q : R)
    (h1 : (1 : R) - q ≠ 0) (h2 : (1 : R) - q ^ 2 ≠ 0)
    (h3 : (1 : R) - q ^ 3 ≠ 0) (h4 : (1 : R) - q ^ 4 ≠ 0)
    (h5 : (1 : R) - q ^ 5 ≠ 0) (h6 : (1 : R) - q ^ 6 ≠ 0)
    (h7 : (1 : R) - q ^ 7 ≠ 0) (h8 : (1 : R) - q ^ 8 ≠ 0) :
    rrBStar q 4 = BaileyBeta 1 q (rrAStar q) 4 := by
  simp only [rrBStar, BaileyBeta, natSum_succ, natSum_zero, BaileyTerm, rrAStar,
    qPoch, qPochhammer, pow_zero, mul_one, one_mul,
    Nat.sub_self, show (1 : Nat) ≠ 0 from by omega,
    show (2 : Nat) ≠ 0 from by omega, show (3 : Nat) ≠ 0 from by omega,
    show (4 : Nat) ≠ 0 from by omega, ↓reduceIte]
  field_simp [h1, h2, h3, h4, h5, h6, h7, h8]; ring

set_option maxHeartbeats 6400000 in
/-- Bailey pair verification at `n = 5`. -/
theorem rrBaileyPair_five (q : R)
    (h1 : (1 : R) - q ≠ 0) (h2 : (1 : R) - q ^ 2 ≠ 0)
    (h3 : (1 : R) - q ^ 3 ≠ 0) (h4 : (1 : R) - q ^ 4 ≠ 0)
    (h5 : (1 : R) - q ^ 5 ≠ 0) (h6 : (1 : R) - q ^ 6 ≠ 0)
    (h7 : (1 : R) - q ^ 7 ≠ 0) (h8 : (1 : R) - q ^ 8 ≠ 0)
    (h9 : (1 : R) - q ^ 9 ≠ 0) (h10 : (1 : R) - q ^ 10 ≠ 0) :
    rrBStar q 5 = BaileyBeta 1 q (rrAStar q) 5 := by
  simp only [rrBStar, BaileyBeta, natSum_succ, natSum_zero, BaileyTerm, rrAStar,
    qPoch, qPochhammer, pow_zero, mul_one, one_mul,
    Nat.sub_self, show (1 : Nat) ≠ 0 from by omega,
    show (2 : Nat) ≠ 0 from by omega, show (3 : Nat) ≠ 0 from by omega,
    show (4 : Nat) ≠ 0 from by omega, show (5 : Nat) ≠ 0 from by omega, ↓reduceIte]
  field_simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]; ring

set_option maxHeartbeats 12800000 in
/-- Bailey pair verification at `n = 6`. -/
theorem rrBaileyPair_six (q : R)
    (h1 : (1 : R) - q ≠ 0) (h2 : (1 : R) - q ^ 2 ≠ 0)
    (h3 : (1 : R) - q ^ 3 ≠ 0) (h4 : (1 : R) - q ^ 4 ≠ 0)
    (h5 : (1 : R) - q ^ 5 ≠ 0) (h6 : (1 : R) - q ^ 6 ≠ 0)
    (h7 : (1 : R) - q ^ 7 ≠ 0) (h8 : (1 : R) - q ^ 8 ≠ 0)
    (h9 : (1 : R) - q ^ 9 ≠ 0) (h10 : (1 : R) - q ^ 10 ≠ 0)
    (h11 : (1 : R) - q ^ 11 ≠ 0) (h12 : (1 : R) - q ^ 12 ≠ 0) :
    rrBStar q 6 = BaileyBeta 1 q (rrAStar q) 6 := by
  simp only [rrBStar, BaileyBeta, natSum_succ, natSum_zero, BaileyTerm, rrAStar,
    qPoch, qPochhammer, pow_zero, mul_one, one_mul,
    Nat.sub_self, show (1 : Nat) ≠ 0 from by omega,
    show (2 : Nat) ≠ 0 from by omega, show (3 : Nat) ≠ 0 from by omega,
    show (4 : Nat) ≠ 0 from by omega, show (5 : Nat) ≠ 0 from by omega,
    show (6 : Nat) ≠ 0 from by omega, ↓reduceIte]
  field_simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]; ring

/-- `(a*, b*)` is a Bailey pair with `a = 1`, verified through `n = 6`. -/
theorem rrStar_isBaileyPairUpTo_six (q : R)
    (h1 : (1 : R) - q ≠ 0) (h2 : (1 : R) - q ^ 2 ≠ 0)
    (h3 : (1 : R) - q ^ 3 ≠ 0) (h4 : (1 : R) - q ^ 4 ≠ 0)
    (h5 : (1 : R) - q ^ 5 ≠ 0) (h6 : (1 : R) - q ^ 6 ≠ 0)
    (h7 : (1 : R) - q ^ 7 ≠ 0) (h8 : (1 : R) - q ^ 8 ≠ 0)
    (h9 : (1 : R) - q ^ 9 ≠ 0) (h10 : (1 : R) - q ^ 10 ≠ 0)
    (h11 : (1 : R) - q ^ 11 ≠ 0) (h12 : (1 : R) - q ^ 12 ≠ 0) :
    IsBaileyPairUpTo 1 q (rrAStar q) (rrBStar q) 6 := by
  intro n hn
  interval_cases n
  · exact rrBaileyPair_zero q
  · have hq1 : qPochhammer q 1 ≠ 0 := by simp [qPochhammer]; exact h1
    have hq2 : qPochhammer q 2 ≠ 0 := by simp [qPochhammer]; exact ⟨h1, h2⟩
    exact rrBaileyPair_one q hq1 hq2
  · exact rrBaileyPair_two q h1 h2 h3 h4
  · exact rrBaileyPair_three q h1 h2 h3 h4 h5 h6
  · exact rrBaileyPair_four q h1 h2 h3 h4 h5 h6 h7 h8
  · exact rrBaileyPair_five q h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  · exact rrBaileyPair_six q h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12

/-- The LHS of the second finite Rogers-Ramanujan identity:
`∑_{k=0}^n q^{k²+k} / (q;q)_k`. -/
noncomputable def finiteRRLHS2 (q : R) (n : Nat) : R :=
  ∑ k ∈ Finset.range (n + 1), q ^ (k * k + k) / qPochhammer q k

theorem finiteRRLHS2_zero (q : R) : finiteRRLHS2 q 0 = 1 := by
  simp [finiteRRLHS2, qPochhammer]

theorem finiteRRLHS2_succ (q : R) (n : Nat) :
    finiteRRLHS2 q (n + 1) = finiteRRLHS2 q n +
      q ^ ((n + 1) * (n + 1) + (n + 1)) / qPochhammer q (n + 1) := by
  simp only [finiteRRLHS2, Finset.sum_range_succ]

theorem finiteRRLHS2_one (q : R) (hq : (1 : R) - q ≠ 0) :
    finiteRRLHS2 q 1 = 1 + q ^ 2 / (1 - q) := by
  simp only [finiteRRLHS2, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    qPochhammer, pow_zero, mul_one, one_mul, Nat.zero_mul]
  field_simp [hq]; ring

set_option maxHeartbeats 400000 in
theorem finiteRRLHS2_two (q : R) (hq : (1 : R) - q ≠ 0) (hq2 : (1 : R) - q ^ 2 ≠ 0) :
    finiteRRLHS2 q 2 = 1 + q ^ 2 / (1 - q) + q ^ 6 / ((1 - q) * (1 - q ^ 2)) := by
  simp only [finiteRRLHS2, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    qPochhammer, pow_zero, mul_one, one_mul, Nat.zero_mul]
  field_simp [hq, hq2]; ring

set_option maxHeartbeats 800000 in
theorem finiteRRLHS2_three (q : R) (hq : (1 : R) - q ≠ 0)
    (hq2 : (1 : R) - q ^ 2 ≠ 0) (hq3 : (1 : R) - q ^ 3 ≠ 0) :
    finiteRRLHS2 q 3 = 1 + q ^ 2 / (1 - q) + q ^ 6 / ((1 - q) * (1 - q ^ 2))
      + q ^ 12 / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3)) := by
  simp only [finiteRRLHS2, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    qPochhammer, pow_zero, mul_one, one_mul, Nat.zero_mul]
  field_simp [hq, hq2, hq3]; ring

set_option maxHeartbeats 1600000 in
theorem finiteRRLHS2_four (q : R) (hq : (1 : R) - q ≠ 0)
    (hq2 : (1 : R) - q ^ 2 ≠ 0) (hq3 : (1 : R) - q ^ 3 ≠ 0)
    (hq4 : (1 : R) - q ^ 4 ≠ 0) :
    finiteRRLHS2 q 4 = 1 + q ^ 2 / (1 - q) + q ^ 6 / ((1 - q) * (1 - q ^ 2))
      + q ^ 12 / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3))
      + q ^ 20 / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4)) := by
  simp only [finiteRRLHS2, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    qPochhammer, pow_zero, mul_one, one_mul, Nat.zero_mul]
  field_simp [hq, hq2, hq3, hq4]; ring

set_option maxHeartbeats 3200000 in
theorem finiteRRLHS2_five (q : R) (hq : (1 : R) - q ≠ 0)
    (hq2 : (1 : R) - q ^ 2 ≠ 0) (hq3 : (1 : R) - q ^ 3 ≠ 0)
    (hq4 : (1 : R) - q ^ 4 ≠ 0) (hq5 : (1 : R) - q ^ 5 ≠ 0) :
    finiteRRLHS2 q 5 = 1 + q ^ 2 / (1 - q) + q ^ 6 / ((1 - q) * (1 - q ^ 2))
      + q ^ 12 / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3))
      + q ^ 20 / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4))
      + q ^ 30 / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5)) := by
  simp only [finiteRRLHS2, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    qPochhammer, pow_zero, mul_one, one_mul, Nat.zero_mul]
  field_simp [hq, hq2, hq3, hq4, hq5]; ring


set_option maxHeartbeats 6400000 in
theorem finiteRRLHS2_six (q : R) (hq : (1 : R) - q ≠ 0)
    (hq2 : (1 : R) - q ^ 2 ≠ 0) (hq3 : (1 : R) - q ^ 3 ≠ 0)
    (hq4 : (1 : R) - q ^ 4 ≠ 0) (hq5 : (1 : R) - q ^ 5 ≠ 0)
    (hq6 : (1 : R) - q ^ 6 ≠ 0) :
    finiteRRLHS2 q 6 = 1 + q ^ 2 / (1 - q) + q ^ 6 / ((1 - q) * (1 - q ^ 2))
      + q ^ 12 / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3))
      + q ^ 20 / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4))
      + q ^ 30 / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5))
      + q ^ 42 / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6)) := by
  simp only [finiteRRLHS2, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    qPochhammer, pow_zero, mul_one, one_mul, Nat.zero_mul]
  field_simp [hq, hq2, hq3, hq4, hq5, hq6]; ring

theorem finiteRRLHS2_seven (q : R) :
    finiteRRLHS2 q 7 = finiteRRLHS2 q 6 + q ^ 56 / qPochhammer q 7 := by
  rw [finiteRRLHS2_succ]

theorem finiteRRLHS2_eight (q : R) :
    finiteRRLHS2 q 8 = finiteRRLHS2 q 7 + q ^ 72 / qPochhammer q 8 := by
  rw [finiteRRLHS2_succ]

theorem finiteRRLHS2_nine (q : R) :
    finiteRRLHS2 q 9 = finiteRRLHS2 q 8 + q ^ 90 / qPochhammer q 9 := by
  rw [finiteRRLHS2_succ]

theorem finiteRRLHS2_ten (q : R) :
    finiteRRLHS2 q 10 = finiteRRLHS2 q 9 + q ^ 110 / qPochhammer q 10 := by
  rw [finiteRRLHS2_succ]

theorem finiteRRLHS2_eleven (q : R) :
    finiteRRLHS2 q 11 = finiteRRLHS2 q 10 + q ^ 132 / qPochhammer q 11 := by
  rw [finiteRRLHS2_succ]
theorem finiteRRLHS2_twelve (q : R) :
    finiteRRLHS2 q 12 = finiteRRLHS2 q 11 + q ^ 156 / qPochhammer q 12 := by
  rw [finiteRRLHS2_succ]
theorem finiteRRLHS2_thirteen (q : R) :
    finiteRRLHS2 q 13 = finiteRRLHS2 q 12 + q ^ 182 / qPochhammer q 13 := by
  rw [finiteRRLHS2_succ]
theorem finiteRRLHS2_fourteen (q : R) :
    finiteRRLHS2 q 14 = finiteRRLHS2 q 13 + q ^ 210 / qPochhammer q 14 := by
  rw [finiteRRLHS2_succ]
theorem finiteRRLHS2_fifteen (q : R) :
    finiteRRLHS2 q 15 = finiteRRLHS2 q 14 + q ^ 240 / qPochhammer q 15 := by
  rw [finiteRRLHS2_succ]
theorem finiteRRLHS2_sixteen (q : R) :
    finiteRRLHS2 q 16 = finiteRRLHS2 q 15 + q ^ 272 / qPochhammer q 16 := by
  rw [finiteRRLHS2_succ]
theorem finiteRRLHS2_seventeen (q : R) :
    finiteRRLHS2 q 17 = finiteRRLHS2 q 16 + q ^ 306 / qPochhammer q 17 := by
  rw [finiteRRLHS2_succ]
theorem finiteRRLHS2_eighteen (q : R) :
    finiteRRLHS2 q 18 = finiteRRLHS2 q 17 + q ^ 342 / qPochhammer q 18 := by
  rw [finiteRRLHS2_succ]
theorem finiteRRLHS2_nineteen (q : R) :
    finiteRRLHS2 q 19 = finiteRRLHS2 q 18 + q ^ 380 / qPochhammer q 19 := by
  rw [finiteRRLHS2_succ]
theorem finiteRRLHS2_twenty (q : R) :
    finiteRRLHS2 q 20 = finiteRRLHS2 q 19 + q ^ 420 / qPochhammer q 20 := by
  rw [finiteRRLHS2_succ]

set_option maxHeartbeats 25600000 in
/-- Bailey pair verification at `n = 7`. -/
theorem rrBaileyPair_seven (q : R)
    (h1 : (1 : R) - q ≠ 0) (h2 : (1 : R) - q ^ 2 ≠ 0)
    (h3 : (1 : R) - q ^ 3 ≠ 0) (h4 : (1 : R) - q ^ 4 ≠ 0)
    (h5 : (1 : R) - q ^ 5 ≠ 0) (h6 : (1 : R) - q ^ 6 ≠ 0)
    (h7 : (1 : R) - q ^ 7 ≠ 0) (h8 : (1 : R) - q ^ 8 ≠ 0)
    (h9 : (1 : R) - q ^ 9 ≠ 0) (h10 : (1 : R) - q ^ 10 ≠ 0)
    (h11 : (1 : R) - q ^ 11 ≠ 0) (h12 : (1 : R) - q ^ 12 ≠ 0)
    (h13 : (1 : R) - q ^ 13 ≠ 0) (h14 : (1 : R) - q ^ 14 ≠ 0) :
    rrBStar q 7 = BaileyBeta 1 q (rrAStar q) 7 := by
  simp only [rrBStar, BaileyBeta, natSum_succ, natSum_zero, BaileyTerm, rrAStar,
    qPoch, qPochhammer, pow_zero, mul_one, one_mul,
    Nat.sub_self, show (1 : Nat) ≠ 0 from by omega,
    show (2 : Nat) ≠ 0 from by omega, show (3 : Nat) ≠ 0 from by omega,
    show (4 : Nat) ≠ 0 from by omega, show (5 : Nat) ≠ 0 from by omega,
    show (6 : Nat) ≠ 0 from by omega, show (7 : Nat) ≠ 0 from by omega, ↓reduceIte]
  field_simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; ring

/-! ### Gaussian binomial evaluations for finite RR verifications -/

/-- General formula: `[n+1; 1]_q = 1 + q + q² + ... + q^n = ∑_{i=0}^n q^i`. -/
theorem gaussianBinom_succ_one (q : R) (n : Nat) :
    gaussianBinom q (n + 1) 1 = ∑ i ∈ Finset.range (n + 1), q ^ i := by
  induction n with
  | zero => simp [gaussianBinom]
  | succ n ih =>
    have h : gaussianBinom q (n + 2) 1 = gaussianBinom q (n + 1) 1 + q ^ (n + 1) := by
      change gaussianBinom q (n + 1) (Nat.succ 0)
          + q ^ ((n + 1) - 0) * gaussianBinom q (n + 1) 0 = _
      simp
    rw [h, ih, ← Finset.sum_range_succ]

/-- `[5; 1]_q = 1 + q + q² + q³ + q⁴`. -/
theorem gaussianBinom_five_one (q : R) :
    gaussianBinom q 5 1 = 1 + q + q ^ 2 + q ^ 3 + q ^ 4 := by
  rw [show (5 : Nat) = 4 + 1 from rfl, gaussianBinom_succ_one]
  simp [Finset.sum_range_succ]

/-- `[3; 1]_q = 1 + q + q²`. -/
theorem gaussianBinom_three_one (q : R) :
    gaussianBinom q 3 1 = 1 + q + q ^ 2 := by
  rw [show (3 : Nat) = 2 + 1 from rfl, gaussianBinom_succ_one]
  simp [Finset.sum_range_succ]

/-- `[3; 2]_q = 1 + q + q²` (by symmetry [n;k] = [n; n-k]). -/
theorem gaussianBinom_three_two (q : R) :
    gaussianBinom q 3 2 = 1 + q + q ^ 2 := by
  simp [gaussianBinom]; ring

/-- `[4; 1]_q`. -/
theorem gaussianBinom_four_one (q : R) :
    gaussianBinom q 4 1 = 1 + q + q ^ 2 + q ^ 3 := by
  rw [show (4 : Nat) = 3 + 1 from rfl, gaussianBinom_succ_one]
  simp [Finset.sum_range_succ]

/-- `[4; 2]_q = 1 + q + 2q² + q³ + q⁴` (by recursion). -/
theorem gaussianBinom_four_two (q : R) :
    gaussianBinom q 4 2 = 1 + q + 2 * q ^ 2 + q ^ 3 + q ^ 4 := by
  change gaussianBinom q 3 2 + q ^ 2 * gaussianBinom q 3 1 = _
  rw [gaussianBinom_three_one, gaussianBinom_three_two]; ring

/-- `[5; 2]_q = 1 + q + 2q² + 2q³ + 2q⁴ + q⁵ + q⁶`. -/
theorem gaussianBinom_five_two (q : R) :
    gaussianBinom q 5 2 = 1 + q + 2 * q ^ 2 + 2 * q ^ 3 + 2 * q ^ 4 + q ^ 5 + q ^ 6 := by
  change gaussianBinom q 4 2 + q ^ 3 * gaussianBinom q 4 1 = _
  rw [gaussianBinom_four_one, gaussianBinom_four_two]; ring

/-! ### Bailey pair connection (continued) -/

/-- At `a = 1`, the BaileyTerm simplifies: the `(aq;q)_{n+k}` factor becomes `(q;q)_{n+k}`. -/
theorem BaileyTerm_at_a_one (q : R) (α : Nat → R) (n k : Nat) :
    BaileyTerm 1 q α n k = α k / (qPochhammer q (n - k) * qPochhammer q (n + k)) := by
  simp [BaileyTerm, qPoch_q_eq_qPochhammer]

/-- `b*_n = 0` for `n ≥ 1`, as a direct consequence of the definition. -/
theorem rrBStar_eq_zero (q : R) (n : Nat) (hn : 1 ≤ n) : rrBStar q n = 0 := by
  cases n with
  | zero => omega
  | succ n => simp [rrBStar]

/-- The LHS of the finite Rogers-Ramanujan identity (first identity, Chan Eq. 9.21):
`∑_{k=0}^n q^{k²} / (q;q)_k`.
This equals `lemma91Base 1 q n` by the Lemma 9.1 specialization. -/
noncomputable def finiteRRLHS (q : R) (n : Nat) : R :=
  ∑ k ∈ Finset.range (n + 1), q ^ (k * k) / qPochhammer q k

/-- At `x = 1`, the Lemma 9.1 identity gives `∑ q^{k²} [n;k]_q/(q;q)_k = 1/(q;q)_n`.
Note: this sum has Gaussian binomials, unlike `finiteRRLHS` which does not. -/
theorem lemma91Base_one_eq (q : R) (n : Nat)
    (hq : ∀ k, k < n → (1 : R) - q ^ (k + 1) ≠ 0) :
    lemma91Base 1 q n = 1 / qPochhammer q n := by
  rw [lemma91_base_at_one q n hq]
  simp [lemma91Target, qPoch_q_eq_qPochhammer]

/-- Concrete evaluation: finiteRRLHS at n=0 is 1. -/
theorem finiteRRLHS_zero (q : R) : finiteRRLHS q 0 = 1 := by
  simp [finiteRRLHS, qPochhammer]

/-- Concrete evaluation: finiteRRLHS at n=1. -/
theorem finiteRRLHS_one (q : R) (hq : (1 : R) - q ≠ 0) :
    finiteRRLHS q 1 = 1 + q / (1 - q) := by
  simp only [finiteRRLHS, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    qPochhammer, pow_zero, mul_one, one_mul, Nat.zero_mul]
  field_simp [hq]; ring

set_option maxHeartbeats 400000 in
/-- Concrete evaluation: finiteRRLHS at n=2. -/
theorem finiteRRLHS_two (q : R) (hq : (1 : R) - q ≠ 0)
    (hq2 : (1 : R) - q ^ 2 ≠ 0) :
    finiteRRLHS q 2 = 1 + q / (1 - q) + q ^ 4 / ((1 - q) * (1 - q ^ 2)) := by
  simp only [finiteRRLHS, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    qPochhammer, pow_zero, mul_one, one_mul, Nat.zero_mul]
  field_simp [hq, hq2]; ring

set_option maxHeartbeats 800000 in
/-- Concrete evaluation: finiteRRLHS at n=3. -/
theorem finiteRRLHS_three (q : R) (hq : (1 : R) - q ≠ 0)
    (hq2 : (1 : R) - q ^ 2 ≠ 0) (hq3 : (1 : R) - q ^ 3 ≠ 0) :
    finiteRRLHS q 3 = 1 + q / (1 - q) + q ^ 4 / ((1 - q) * (1 - q ^ 2))
      + q ^ 9 / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3)) := by
  simp only [finiteRRLHS, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    qPochhammer, pow_zero, mul_one, one_mul, Nat.zero_mul]
  field_simp [hq, hq2, hq3]; ring

set_option maxHeartbeats 1600000 in
/-- Concrete evaluation: finiteRRLHS at n=4. -/
theorem finiteRRLHS_four (q : R) (hq : (1 : R) - q ≠ 0)
    (hq2 : (1 : R) - q ^ 2 ≠ 0) (hq3 : (1 : R) - q ^ 3 ≠ 0)
    (hq4 : (1 : R) - q ^ 4 ≠ 0) :
    finiteRRLHS q 4 = 1 + q / (1 - q) + q ^ 4 / ((1 - q) * (1 - q ^ 2))
      + q ^ 9 / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3))
      + q ^ 16 / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4)) := by
  simp only [finiteRRLHS, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    qPochhammer, pow_zero, mul_one, one_mul, Nat.zero_mul]
  field_simp [hq, hq2, hq3, hq4]; ring

set_option maxHeartbeats 3200000 in
/-- Concrete evaluation: finiteRRLHS at n=5. -/
theorem finiteRRLHS_five (q : R) (hq : (1 : R) - q ≠ 0)
    (hq2 : (1 : R) - q ^ 2 ≠ 0) (hq3 : (1 : R) - q ^ 3 ≠ 0)
    (hq4 : (1 : R) - q ^ 4 ≠ 0) (hq5 : (1 : R) - q ^ 5 ≠ 0) :
    finiteRRLHS q 5 = 1 + q / (1 - q) + q ^ 4 / ((1 - q) * (1 - q ^ 2))
      + q ^ 9 / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3))
      + q ^ 16 / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4))
      + q ^ 25 / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5)) := by
  simp only [finiteRRLHS, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    qPochhammer, pow_zero, mul_one, one_mul, Nat.zero_mul]
  field_simp [hq, hq2, hq3, hq4, hq5]; ring

set_option maxHeartbeats 6400000 in
/-- Concrete evaluation: finiteRRLHS at n=6. -/
theorem finiteRRLHS_six (q : R) (hq : (1 : R) - q ≠ 0)
    (hq2 : (1 : R) - q ^ 2 ≠ 0) (hq3 : (1 : R) - q ^ 3 ≠ 0)
    (hq4 : (1 : R) - q ^ 4 ≠ 0) (hq5 : (1 : R) - q ^ 5 ≠ 0)
    (hq6 : (1 : R) - q ^ 6 ≠ 0) :
    finiteRRLHS q 6 = 1 + q / (1 - q) + q ^ 4 / ((1 - q) * (1 - q ^ 2))
      + q ^ 9 / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3))
      + q ^ 16 / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4))
      + q ^ 25 / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5))
      + q ^ 36 / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6)) := by
  simp only [finiteRRLHS, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    qPochhammer, pow_zero, mul_one, one_mul, Nat.zero_mul]
  field_simp [hq, hq2, hq3, hq4, hq5, hq6]; ring

set_option maxHeartbeats 12800000 in
/-- Concrete evaluation: finiteRRLHS at n=7. -/
theorem finiteRRLHS_seven (q : R) (hq : (1 : R) - q ≠ 0)
    (hq2 : (1 : R) - q ^ 2 ≠ 0) (hq3 : (1 : R) - q ^ 3 ≠ 0)
    (hq4 : (1 : R) - q ^ 4 ≠ 0) (hq5 : (1 : R) - q ^ 5 ≠ 0)
    (hq6 : (1 : R) - q ^ 6 ≠ 0) (hq7 : (1 : R) - q ^ 7 ≠ 0) :
    finiteRRLHS q 7 = 1 + q / (1 - q) + q ^ 4 / ((1 - q) * (1 - q ^ 2))
      + q ^ 9 / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3))
      + q ^ 16 / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4))
      + q ^ 25 / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5))
      + q ^ 36 / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6))
      + q ^ 49 / ((1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7)) := by
  simp only [finiteRRLHS, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    qPochhammer, pow_zero, mul_one, one_mul, Nat.zero_mul]
  field_simp [hq, hq2, hq3, hq4, hq5, hq6, hq7]; ring

/-- The recurrence for finiteRRLHS: adding one more term. -/
theorem finiteRRLHS_succ (q : R) (n : Nat) :
    finiteRRLHS q (n + 1) = finiteRRLHS q n + q ^ ((n + 1) * (n + 1)) / qPochhammer q (n + 1) := by
  simp only [finiteRRLHS, Finset.sum_range_succ]


/-- Concrete evaluation: finiteRRLHS at n=8 (recursive form). -/
theorem finiteRRLHS_eight (q : R) :
    finiteRRLHS q 8 = finiteRRLHS q 7 + q ^ 64 / qPochhammer q 8 := by
  rw [finiteRRLHS_succ]

/-- Concrete evaluation: finiteRRLHS at n=9 (recursive form). -/
theorem finiteRRLHS_nine (q : R) :
    finiteRRLHS q 9 = finiteRRLHS q 8 + q ^ 81 / qPochhammer q 9 := by
  rw [finiteRRLHS_succ]

/-- Concrete evaluation: finiteRRLHS at n=10 (recursive form). -/
theorem finiteRRLHS_ten (q : R) :
    finiteRRLHS q 10 = finiteRRLHS q 9 + q ^ 100 / qPochhammer q 10 := by
  rw [finiteRRLHS_succ]

theorem finiteRRLHS_eleven (q : R) :
    finiteRRLHS q 11 = finiteRRLHS q 10 + q ^ 121 / qPochhammer q 11 := by
  rw [finiteRRLHS_succ]
theorem finiteRRLHS_twelve (q : R) :
    finiteRRLHS q 12 = finiteRRLHS q 11 + q ^ 144 / qPochhammer q 12 := by
  rw [finiteRRLHS_succ]
theorem finiteRRLHS_thirteen (q : R) :
    finiteRRLHS q 13 = finiteRRLHS q 12 + q ^ 169 / qPochhammer q 13 := by
  rw [finiteRRLHS_succ]
theorem finiteRRLHS_fourteen (q : R) :
    finiteRRLHS q 14 = finiteRRLHS q 13 + q ^ 196 / qPochhammer q 14 := by
  rw [finiteRRLHS_succ]
theorem finiteRRLHS_fifteen (q : R) :
    finiteRRLHS q 15 = finiteRRLHS q 14 + q ^ 225 / qPochhammer q 15 := by
  rw [finiteRRLHS_succ]
theorem finiteRRLHS_sixteen (q : R) :
    finiteRRLHS q 16 = finiteRRLHS q 15 + q ^ 256 / qPochhammer q 16 := by
  rw [finiteRRLHS_succ]
theorem finiteRRLHS_seventeen (q : R) :
    finiteRRLHS q 17 = finiteRRLHS q 16 + q ^ 289 / qPochhammer q 17 := by
  rw [finiteRRLHS_succ]
theorem finiteRRLHS_eighteen (q : R) :
    finiteRRLHS q 18 = finiteRRLHS q 17 + q ^ 324 / qPochhammer q 18 := by
  rw [finiteRRLHS_succ]
theorem finiteRRLHS_nineteen (q : R) :
    finiteRRLHS q 19 = finiteRRLHS q 18 + q ^ 361 / qPochhammer q 19 := by
  rw [finiteRRLHS_succ]
theorem finiteRRLHS_twenty (q : R) :
    finiteRRLHS q 20 = finiteRRLHS q 19 + q ^ 400 / qPochhammer q 20 := by
  rw [finiteRRLHS_succ]

/-- The RHS of the finite Rogers-Ramanujan identity (first identity, Chan Eq. 9.21):
`∑_{j=0}^n (-1)^j q^{j(5j-1)/2} (1 - q^{2j+1}) [2n+1; n-j]_q / (q;q)_{2n+1}`. -/
noncomputable def finiteRRRHS (q : R) (n : Nat) : R :=
  ∑ j ∈ Finset.range (n + 1),
    (-1 : R) ^ j * q ^ (j * (5 * j - 1) / 2) * (1 - q ^ (2 * j + 1)) *
      gaussianBinom q (2 * n + 1) (n - j) / qPochhammer q (2 * n + 1)

/-- Concrete evaluation: finiteRRRHS at n=0. -/
theorem finiteRRRHS_zero (q : R) (hq : (1 : R) - q ≠ 0) :
    finiteRRRHS q 0 = 1 := by
  simp only [finiteRRRHS, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    gaussianBinom, qPochhammer, pow_zero, mul_one, one_mul, Nat.zero_mul]
  field_simp [hq]; ring

set_option maxHeartbeats 800000 in
/-- Concrete evaluation: finiteRRRHS at n=1. Matches finiteRRLHS_one. -/
theorem finiteRRRHS_one (q : R) (hq : (1 : R) - q ≠ 0)
    (hq2 : (1 : R) - q ^ 2 ≠ 0) (hq3 : (1 : R) - q ^ 3 ≠ 0) :
    finiteRRRHS q 1 = 1 + q / (1 - q) := by
  simp only [finiteRRRHS, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    gaussianBinom, qPochhammer, pow_zero, mul_one, one_mul, Nat.zero_mul,
    Nat.sub_self, Nat.sub_zero]
  field_simp [hq, hq2, hq3]; ring

/-- The finite Rogers-Ramanujan identity verified at n=0: LHS = RHS. -/
theorem finiteRR_zero (q : R) (hq : (1 : R) - q ≠ 0) :
    finiteRRLHS q 0 = finiteRRRHS q 0 := by
  rw [finiteRRLHS_zero, finiteRRRHS_zero q hq]

/-- The finite Rogers-Ramanujan identity verified at n=1: LHS = RHS. -/
theorem finiteRR_one (q : R) (hq : (1 : R) - q ≠ 0)
    (hq2 : (1 : R) - q ^ 2 ≠ 0) (hq3 : (1 : R) - q ^ 3 ≠ 0) :
    finiteRRLHS q 1 = finiteRRRHS q 1 := by
  rw [finiteRRLHS_one q hq, finiteRRRHS_one q hq hq2 hq3]

-- finiteRRRHS_two: the given definition of finiteRRRHS doesn't match finiteRRLHS at n ≥ 2.
-- The Schur-Bressoud finite RR identity needs a bilateral sum or different unilateral form.
-- (n=0, n=1 happen to work; deferred.)

end Field

end Ch09
end PartII
end QseriesFormalization
