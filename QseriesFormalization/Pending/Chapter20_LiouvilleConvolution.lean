import QseriesFormalization.Chapter20
import Mathlib.NumberTheory.Bernoulli
import Mathlib.Tactic

/-!
# Chapter 20: Liouville-style convolution scaffold

This file isolates the finite four-variable arithmetic used in the classical
Liouville proof of the `sigma_1 * sigma_3` convolution identity.

The eventual target is the all-`n` proof of the Lahiri/Ramanujan identity

`240 * sum_{k=1}^{n-1} sigma_1(k) sigma_3(n-k)
  = 21 sigma_5(n) + (10 - 30n) sigma_3(n) - sigma_1(n)`.

The file currently formalizes the finite set `Q_n`, the swap symmetry, the
basic weight identity, the polynomial telescoping step, and the two elementary
`Q_n`-preserving transformations used in Liouville's proof.
-/

namespace QseriesFormalization
namespace Pending
namespace Ch20LiouvilleConvolution

/-- Integer-valued divisor-power sum used in the arithmetic convolution. -/
def sigmaPowZ (r n : Nat) : Int :=
  (Nat.divisorSum n fun d => d ^ r : Int)

def sigma1Sigma3ConvZ (n : Nat) : Int :=
  ∑ k ∈ Finset.Icc 1 (n - 1), sigmaPowZ 1 k * sigmaPowZ 3 (n - k)

def sigmaSigmaConvZ (r s n : Nat) : Int :=
  ∑ k ∈ Finset.Icc 1 (n - 1), sigmaPowZ r k * sigmaPowZ s (n - k)

/-- Divisor sums as bounded factor-pair sums, using the right factor as the
divisor variable.  This is the version matching the Liouville weight
`b*d^3` for tuples with `a*b + c*d = n`. -/
lemma sigmaPowZ_eq_sum_factorPairs_right_of_pos_le (r k N : Nat)
    (hk0 : 0 < k) (hkN : k ≤ N) :
    sigmaPowZ r k =
      ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
        if a * b = k then ((b ^ r : Nat) : Int) else 0 := by
  unfold sigmaPowZ Nat.divisorSum
  rw [Nat.cast_sum]
  calc
    (∑ d ∈ Finset.Icc 1 k, ↑(if d ∣ k then d ^ r else 0 : Nat))
        = ∑ b ∈ Finset.Icc 1 N, ∑ a ∈ Finset.Icc 1 N,
            if a * b = k then ((b ^ r : Nat) : Int) else 0 := by
      rw [← Finset.sum_subset (s₁ := Finset.Icc 1 k) (s₂ := Finset.Icc 1 N)]
      · refine Finset.sum_congr rfl ?_
        intro b hb
        rw [Nat.cast_ite]
        by_cases hdiv : b ∣ k
        · rw [if_pos hdiv]
          rcases hdiv with ⟨a, ha⟩
          have hb1 : 1 ≤ b := (Finset.mem_Icc.mp hb).1
          have hb0 : 0 < b := hb1
          have hapos : 0 < a := by
            by_contra ha0not
            have ha0 : a = 0 := Nat.eq_zero_of_not_pos ha0not
            subst a
            simp at ha
            omega
          have haN : a ≤ N := by
            have hak : a ≤ k := by
              rw [ha]
              exact Nat.le_mul_of_pos_left a hb0
            exact le_trans hak hkN
          rw [Finset.sum_eq_single a]
          · simp [ha, Nat.mul_comm]
          · intro a' _ hane
            by_cases h : a' * b = k
            · have ha' : a' = a := by
                have hba' : b * a' = b * a := by
                  rw [Nat.mul_comm b a', h, ha]
                exact Nat.mul_left_cancel hb0 hba'
              exact False.elim (hane ha')
            · simp [h]
          · intro hanot
            exact False.elim (hanot (Finset.mem_Icc.mpr ⟨hapos, haN⟩))
        · rw [if_neg hdiv]
          symm
          apply Finset.sum_eq_zero
          intro a _
          by_cases h : a * b = k
          · exact False.elim (hdiv ⟨a, by rw [← h, Nat.mul_comm]⟩)
          · simp [h]
      · intro b hb
        exact Finset.mem_Icc.mpr
          ⟨(Finset.mem_Icc.mp hb).1, le_trans (Finset.mem_Icc.mp hb).2 hkN⟩
      · intro b hbN hbNotSmall
        have hb1 : 1 ≤ b := (Finset.mem_Icc.mp hbN).1
        have hkb : k < b := by
          have hnot : ¬ b ≤ k := by
            intro hbk
            exact hbNotSmall (Finset.mem_Icc.mpr ⟨hb1, hbk⟩)
          omega
        apply Finset.sum_eq_zero
        intro a hamem
        by_cases h : a * b = k
        · have hapos : 0 < a := (Finset.mem_Icc.mp hamem).1
          have : b ≤ k := by
            rw [← h]
            exact Nat.le_mul_of_pos_left b hapos
          omega
        · simp [h]
    _ = ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
            if a * b = k then ((b ^ r : Nat) : Int) else 0 := by
      rw [Finset.sum_comm]

/-- The `sigma_1 * sigma_3` convolution after expanding each divisor sum into
bounded factor pairs, with right factors carrying the divisor powers. -/
def sigma1Sigma3FactorPairRightSplitSumZ (n : Nat) : Int :=
  ∑ k ∈ Finset.Icc 1 (n - 1),
    (∑ a ∈ Finset.Icc 1 n, ∑ b ∈ Finset.Icc 1 n,
      if a * b = k then ((b ^ 1 : Nat) : Int) else 0) *
    (∑ c ∈ Finset.Icc 1 n, ∑ d ∈ Finset.Icc 1 n,
      if c * d = n - k then ((d ^ 3 : Nat) : Int) else 0)

def sigmaSigmaFactorPairRightSplitSumZ (r s n : Nat) : Int :=
  ∑ k ∈ Finset.Icc 1 (n - 1),
    (∑ a ∈ Finset.Icc 1 n, ∑ b ∈ Finset.Icc 1 n,
      if a * b = k then ((b ^ r : Nat) : Int) else 0) *
    (∑ c ∈ Finset.Icc 1 n, ∑ d ∈ Finset.Icc 1 n,
      if c * d = n - k then ((d ^ s : Nat) : Int) else 0)

theorem sigma1Sigma3ConvZ_eq_factorPairRightSplitSumZ (n : Nat) :
    sigma1Sigma3ConvZ n = sigma1Sigma3FactorPairRightSplitSumZ n := by
  unfold sigma1Sigma3ConvZ sigma1Sigma3FactorPairRightSplitSumZ
  apply Finset.sum_congr rfl
  intro k hk
  have hk0 : 0 < k := (Finset.mem_Icc.mp hk).1
  have hkn1 : k ≤ n - 1 := (Finset.mem_Icc.mp hk).2
  have hkn : k ≤ n := by omega
  have hnk0 : 0 < n - k := by omega
  have hnkle : n - k ≤ n := by omega
  rw [sigmaPowZ_eq_sum_factorPairs_right_of_pos_le 1 k n hk0 hkn,
    sigmaPowZ_eq_sum_factorPairs_right_of_pos_le 3 (n - k) n hnk0 hnkle]

theorem sigmaSigmaConvZ_eq_factorPairRightSplitSumZ (r s n : Nat) :
    sigmaSigmaConvZ r s n = sigmaSigmaFactorPairRightSplitSumZ r s n := by
  unfold sigmaSigmaConvZ sigmaSigmaFactorPairRightSplitSumZ
  apply Finset.sum_congr rfl
  intro k hk
  have hk0 : 0 < k := (Finset.mem_Icc.mp hk).1
  have hkn1 : k ≤ n - 1 := (Finset.mem_Icc.mp hk).2
  have hkn : k ≤ n := by omega
  have hnk0 : 0 < n - k := by omega
  have hnkle : n - k ≤ n := by omega
  rw [sigmaPowZ_eq_sum_factorPairs_right_of_pos_le r k n hk0 hkn,
    sigmaPowZ_eq_sum_factorPairs_right_of_pos_le s (n - k) n hnk0 hnkle]

theorem divisorQuotPowSumZ_eq_sigmaPowZ (r n : Nat) :
    (∑ a ∈ Finset.Icc 1 n,
      if a ∣ n then (((n / a) ^ r : Nat) : Int) else 0) = sigmaPowZ r n := by
  by_cases hn : n = 0
  · subst n
    simp [sigmaPowZ, Nat.divisorSum]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    rw [sigmaPowZ_eq_sum_factorPairs_right_of_pos_le r n n hnpos le_rfl]
    apply Finset.sum_congr rfl
    intro a ha
    have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
    have ha0 : 0 < a := ha1
    by_cases hdiv : a ∣ n
    · rw [if_pos hdiv]
      rw [Finset.sum_eq_single (n / a)]
      · have hmul : a * (n / a) = n := by
          rw [Nat.mul_comm, Nat.div_mul_cancel hdiv]
        simp [hmul]
      · intro b _ hbne
        by_cases hmul : a * b = n
        · have hb_eq : b = n / a := by
            rw [← hmul, Nat.mul_comm]
            exact (Nat.mul_div_left b ha0).symm
          exact False.elim (hbne hb_eq)
        · simp [hmul]
      · intro hnot
        have hmem : n / a ∈ Finset.Icc 1 n := by
          exact Finset.mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd hnpos hdiv) ha0,
            Nat.div_le_self n a⟩
        exact False.elim (hnot hmem)
    · rw [if_neg hdiv]
      symm
      apply Finset.sum_eq_zero
      intro b _
      by_cases hmul : a * b = n
      · exact False.elim (hdiv ⟨b, hmul.symm⟩)
      · simp [hmul]

/-- A positive quadruple candidate `(a,b,c,d)`.  Positivity and the equation
`a*b + c*d = n` are imposed by `liouvilleQ`. -/
structure LQuad where
  a : Nat
  b : Nat
  c : Nat
  d : Nat
deriving DecidableEq, Repr

namespace LQuad

@[ext] theorem ext {q r : LQuad}
    (ha : q.a = r.a) (hb : q.b = r.b) (hc : q.c = r.c) (hd : q.d = r.d) :
    q = r := by
  cases q
  cases r
  simp_all

end LQuad

/-- Bounded positive quadruples.  The bound `n` is enough for every coordinate
of a quadruple satisfying `a*b + c*d = n`. -/
def liouvilleBox (n : Nat) : Finset LQuad :=
  (((Finset.Icc 1 n).product (Finset.Icc 1 n)).product
    ((Finset.Icc 1 n).product (Finset.Icc 1 n))).image fun x =>
      { a := x.1.1, b := x.1.2, c := x.2.1, d := x.2.2 }

theorem mem_liouvilleBox_iff (n : Nat) (q : LQuad) :
    q ∈ liouvilleBox n ↔
      q.a ∈ Finset.Icc 1 n ∧ q.b ∈ Finset.Icc 1 n ∧
        q.c ∈ Finset.Icc 1 n ∧ q.d ∈ Finset.Icc 1 n := by
  constructor
  · intro hq
    rw [liouvilleBox, Finset.mem_image] at hq
    rcases hq with ⟨x, hx, rfl⟩
    have hx' := Finset.mem_product.mp hx
    have hx1 := Finset.mem_product.mp hx'.1
    have hx2 := Finset.mem_product.mp hx'.2
    exact ⟨hx1.1, hx1.2, hx2.1, hx2.2⟩
  · rintro ⟨ha, hb, hc, hd⟩
    rw [liouvilleBox, Finset.mem_image]
    refine ⟨((q.a, q.b), (q.c, q.d)), ?_, ?_⟩
    · simp [ha, hb, hc, hd]
    · rfl

/-- The finite set `Q_n = {(a,b,c,d) > 0 : a*b + c*d = n}`. -/
def liouvilleQ (n : Nat) : Finset LQuad :=
  (liouvilleBox n).filter fun q => q.a * q.b + q.c * q.d = n

theorem mem_liouvilleQ_iff (n : Nat) (q : LQuad) :
    q ∈ liouvilleQ n ↔
      1 ≤ q.a ∧ q.a ≤ n ∧ 1 ≤ q.b ∧ q.b ≤ n ∧
        1 ≤ q.c ∧ q.c ≤ n ∧ 1 ≤ q.d ∧ q.d ≤ n ∧
          q.a * q.b + q.c * q.d = n := by
  rw [liouvilleQ, Finset.mem_filter, mem_liouvilleBox_iff]
  constructor
  · rintro ⟨hbox, hsum⟩
    exact ⟨(Finset.mem_Icc.mp hbox.1).1, (Finset.mem_Icc.mp hbox.1).2,
      (Finset.mem_Icc.mp hbox.2.1).1, (Finset.mem_Icc.mp hbox.2.1).2,
      (Finset.mem_Icc.mp hbox.2.2.1).1, (Finset.mem_Icc.mp hbox.2.2.1).2,
      (Finset.mem_Icc.mp hbox.2.2.2).1, (Finset.mem_Icc.mp hbox.2.2.2).2,
      hsum⟩
  · rintro ⟨ha1, han, hb1, hbn, hc1, hcn, hd1, hdn, hsum⟩
    exact ⟨⟨Finset.mem_Icc.mpr ⟨ha1, han⟩,
      Finset.mem_Icc.mpr ⟨hb1, hbn⟩,
      Finset.mem_Icc.mpr ⟨hc1, hcn⟩,
      Finset.mem_Icc.mpr ⟨hd1, hdn⟩⟩, hsum⟩

/-- Boundary part with `a = c`. -/
def eqPart (n : Nat) : Finset LQuad :=
  (liouvilleQ n).filter fun q => q.a = q.c

/-- Strict part with `a > c`. -/
def gtPart (n : Nat) : Finset LQuad :=
  (liouvilleQ n).filter fun q => q.c < q.a

/-- Strict part with `c > a`. -/
def ltPart (n : Nat) : Finset LQuad :=
  (liouvilleQ n).filter fun q => q.a < q.c

/-- Boundary part with `b = d`. -/
def eqBDPart (n : Nat) : Finset LQuad :=
  (liouvilleQ n).filter fun q => q.b = q.d

theorem mem_eqPart_iff (n : Nat) (q : LQuad) :
    q ∈ eqPart n ↔ q ∈ liouvilleQ n ∧ q.a = q.c := by
  simp [eqPart]

theorem mem_gtPart_iff (n : Nat) (q : LQuad) :
    q ∈ gtPart n ↔ q ∈ liouvilleQ n ∧ q.c < q.a := by
  simp [gtPart]

theorem mem_ltPart_iff (n : Nat) (q : LQuad) :
    q ∈ ltPart n ↔ q ∈ liouvilleQ n ∧ q.a < q.c := by
  simp [ltPart]

theorem mem_eqBDPart_iff (n : Nat) (q : LQuad) :
    q ∈ eqBDPart n ↔ q ∈ liouvilleQ n ∧ q.b = q.d := by
  simp [eqBDPart]

theorem liouvilleQ_eq_parts_union (n : Nat) :
    liouvilleQ n = (eqPart n ∪ gtPart n) ∪ ltPart n := by
  ext q
  rw [Finset.mem_union, Finset.mem_union, mem_eqPart_iff, mem_gtPart_iff,
    mem_ltPart_iff]
  constructor
  · intro hq
    rcases lt_trichotomy q.a q.c with hac | hac | hac
    · exact Or.inr ⟨hq, hac⟩
    · exact Or.inl (Or.inl ⟨hq, hac⟩)
    · exact Or.inl (Or.inr ⟨hq, hac⟩)
  · intro h
    rcases h with hleft | hlt
    · rcases hleft with heq | hgt
      · exact heq.1
      · exact hgt.1
    · exact hlt.1

theorem eqPart_disjoint_gtPart (n : Nat) :
    Disjoint (eqPart n) (gtPart n) := by
  rw [Finset.disjoint_left]
  intro q heq hgt
  rw [mem_eqPart_iff] at heq
  rw [mem_gtPart_iff] at hgt
  omega

theorem eqPart_disjoint_ltPart (n : Nat) :
    Disjoint (eqPart n) (ltPart n) := by
  rw [Finset.disjoint_left]
  intro q heq hlt
  rw [mem_eqPart_iff] at heq
  rw [mem_ltPart_iff] at hlt
  omega

theorem gtPart_disjoint_ltPart (n : Nat) :
    Disjoint (gtPart n) (ltPart n) := by
  rw [Finset.disjoint_left]
  intro q hgt hlt
  rw [mem_gtPart_iff] at hgt
  rw [mem_ltPart_iff] at hlt
  omega

theorem eqGtPart_union_disjoint_ltPart (n : Nat) :
    Disjoint (eqPart n ∪ gtPart n) (ltPart n) := by
  rw [Finset.disjoint_left]
  intro q hleft hlt
  rw [Finset.mem_union] at hleft
  rcases hleft with heq | hgt
  · exact Finset.disjoint_left.mp (eqPart_disjoint_ltPart n) heq hlt
  · exact Finset.disjoint_left.mp (gtPart_disjoint_ltPart n) hgt hlt

theorem sum_liouvilleQ_eq_parts (n : Nat) (F : LQuad → Int) :
    (∑ q ∈ liouvilleQ n, F q) =
      (∑ q ∈ eqPart n, F q) + (∑ q ∈ gtPart n, F q) +
        ∑ q ∈ ltPart n, F q := by
  rw [liouvilleQ_eq_parts_union n]
  rw [Finset.sum_union (eqGtPart_union_disjoint_ltPart n),
    Finset.sum_union (eqPart_disjoint_gtPart n)]

theorem eqPart_mul_add_eq {n : Nat} {q : LQuad}
    (hq : q ∈ eqPart n) :
    q.a * (q.b + q.d) = n := by
  rw [mem_eqPart_iff] at hq
  have hqQ := (mem_liouvilleQ_iff n q).mp hq.1
  rcases hqQ with ⟨_, _, _, _, _, _, _, _, hsum⟩
  rw [← hsum, hq.2]
  ring

theorem eqBDPart_add_mul_eq {n : Nat} {q : LQuad}
    (hq : q ∈ eqBDPart n) :
    (q.a + q.c) * q.b = n := by
  rw [mem_eqBDPart_iff] at hq
  have hqQ := (mem_liouvilleQ_iff n q).mp hq.1
  rcases hqQ with ⟨_, _, _, _, _, _, _, _, hsum⟩
  rw [← hsum, hq.2]
  ring

theorem eqPart_eqBDPart_two_mul_eq {n : Nat} {q : LQuad}
    (ha : q ∈ eqPart n) (hb : q ∈ eqBDPart n) :
    2 * q.a * q.b = n := by
  rw [mem_eqPart_iff] at ha
  rw [mem_eqBDPart_iff] at hb
  have hqQ := (mem_liouvilleQ_iff n q).mp ha.1
  rcases hqQ with ⟨_, _, _, _, _, _, _, _, hsum⟩
  rw [← hsum, ha.2, hb.2]
  ring

def swapQuad (q : LQuad) : LQuad :=
  { a := q.c, b := q.d, c := q.a, d := q.b }

def swapQuadEquiv : LQuad ≃ LQuad where
  toFun := swapQuad
  invFun := swapQuad
  left_inv := by
    intro q
    ext <;> rfl
  right_inv := by
    intro q
    ext <;> rfl

theorem swapQuad_mem_liouvilleQ_iff (n : Nat) (q : LQuad) :
    swapQuad q ∈ liouvilleQ n ↔ q ∈ liouvilleQ n := by
  rw [mem_liouvilleQ_iff, mem_liouvilleQ_iff]
  constructor
  · rintro ⟨hc1, hcn, hd1, hdn, ha1, han, hb1, hbn, hsum⟩
    exact ⟨ha1, han, hb1, hbn, hc1, hcn, hd1, hdn, by simpa [swapQuad, add_comm] using hsum⟩
  · rintro ⟨ha1, han, hb1, hbn, hc1, hcn, hd1, hdn, hsum⟩
    exact ⟨hc1, hcn, hd1, hdn, ha1, han, hb1, hbn, by simpa [swapQuad, add_comm] using hsum⟩

def weightBD3 (q : LQuad) : Int :=
  (q.b : Int) * (q.d : Int) ^ 3

def weightBD5 (q : LQuad) : Int :=
  (q.b : Int) * (q.d : Int) ^ 5

def weightB3D3 (q : LQuad) : Int :=
  (q.b : Int) ^ 3 * (q.d : Int) ^ 3

def weightP15T (q : LQuad) : Int :=
  6 * (q.b : Int) ^ 5 * (q.d : Int) +
    14 * (q.b : Int) ^ 3 * (q.d : Int) ^ 3 +
      6 * (q.b : Int) * (q.d : Int) ^ 5

def weightBpowDpow (r s : Nat) (q : LQuad) : Int :=
  (q.b : Int) ^ r * (q.d : Int) ^ s

def weightW (q : LQuad) : Int :=
  (q.b : Int) * (q.d : Int) * ((q.b : Int) ^ 2 + (q.d : Int) ^ 2)

def liouvilleBD3Sum (n : Nat) : Int :=
  ∑ q ∈ liouvilleQ n, weightBD3 q

def liouvilleBD5Sum (n : Nat) : Int :=
  ∑ q ∈ liouvilleQ n, weightBD5 q

def liouvilleB3D3Sum (n : Nat) : Int :=
  ∑ q ∈ liouvilleQ n, weightB3D3 q

def liouvilleBpowDpowSum (r s n : Nat) : Int :=
  ∑ q ∈ liouvilleQ n, weightBpowDpow r s q

def liouvilleWSum (n : Nat) : Int :=
  ∑ q ∈ liouvilleQ n, weightW q

def factorPairRightSplitMatchesQ (n : Nat) : Prop :=
  sigma1Sigma3FactorPairRightSplitSumZ n = liouvilleBD3Sum n

instance decidableFactorPairRightSplitMatchesQ (n : Nat) :
    Decidable (factorPairRightSplitMatchesQ n) := by
  unfold factorPairRightSplitMatchesQ
  infer_instance

def factorPairRightSplitMatchesQThrough8Check : Bool :=
  (List.range 9).all fun n => decide (factorPairRightSplitMatchesQ n)

theorem factorPairRightSplitMatchesQThrough8Check_true :
    factorPairRightSplitMatchesQThrough8Check = true := by
  native_decide

theorem sum_liouvilleBox_eq_nested (n : Nat) (F : LQuad → Int) :
    (∑ q ∈ liouvilleBox n, F q) =
      ∑ a ∈ Finset.Icc 1 n, ∑ b ∈ Finset.Icc 1 n,
        ∑ c ∈ Finset.Icc 1 n, ∑ d ∈ Finset.Icc 1 n,
          F { a := a, b := b, c := c, d := d } := by
  unfold liouvilleBox
  rw [Finset.sum_image]
  · simp [Finset.sum_product]
  · intro x _ y _ hxy
    rcases x with ⟨⟨a, b⟩, ⟨c, d⟩⟩
    rcases y with ⟨⟨a', b'⟩, ⟨c', d'⟩⟩
    simp at hxy ⊢
    exact ⟨⟨hxy.1, hxy.2.1⟩, hxy.2.2.1, hxy.2.2.2⟩

theorem liouvilleBpowDpowSum_eq_nested (r s n : Nat) :
    liouvilleBpowDpowSum r s n =
      ∑ a ∈ Finset.Icc 1 n, ∑ b ∈ Finset.Icc 1 n,
        ∑ c ∈ Finset.Icc 1 n, ∑ d ∈ Finset.Icc 1 n,
          if a * b + c * d = n then (b : Int) ^ r * (d : Int) ^ s else 0 := by
  unfold liouvilleBpowDpowSum weightBpowDpow liouvilleQ
  rw [Finset.sum_filter]
  rw [sum_liouvilleBox_eq_nested]

theorem liouvilleBD3Sum_eq_nested (n : Nat) :
    liouvilleBD3Sum n =
      ∑ a ∈ Finset.Icc 1 n, ∑ b ∈ Finset.Icc 1 n,
        ∑ c ∈ Finset.Icc 1 n, ∑ d ∈ Finset.Icc 1 n,
          if a * b + c * d = n then (b : Int) * (d : Int) ^ 3 else 0 := by
  unfold liouvilleBD3Sum liouvilleQ
  rw [Finset.sum_filter]
  rw [sum_liouvilleBox_eq_nested]
  rfl

theorem factorPairRightSplit_product_expansion_general (r s n k : Nat) :
    ((∑ a ∈ Finset.Icc 1 n, ∑ b ∈ Finset.Icc 1 n,
      if a * b = k then ((b ^ r : Nat) : Int) else 0) *
    (∑ c ∈ Finset.Icc 1 n, ∑ d ∈ Finset.Icc 1 n,
      if c * d = n - k then ((d ^ s : Nat) : Int) else 0)) =
      ∑ a ∈ Finset.Icc 1 n, ∑ b ∈ Finset.Icc 1 n,
        ∑ c ∈ Finset.Icc 1 n, ∑ d ∈ Finset.Icc 1 n,
          (if a * b = k then ((b ^ r : Nat) : Int) else 0) *
            (if c * d = n - k then ((d ^ s : Nat) : Int) else 0) := by
  rw [mul_comm]
  simp only [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro d _
  ring

theorem factorPairRightSplit_product_expansion (n k : Nat) :
    ((∑ a ∈ Finset.Icc 1 n, ∑ b ∈ Finset.Icc 1 n,
      if a * b = k then ((b ^ 1 : Nat) : Int) else 0) *
    (∑ c ∈ Finset.Icc 1 n, ∑ d ∈ Finset.Icc 1 n,
      if c * d = n - k then ((d ^ 3 : Nat) : Int) else 0)) =
      ∑ a ∈ Finset.Icc 1 n, ∑ b ∈ Finset.Icc 1 n,
        ∑ c ∈ Finset.Icc 1 n, ∑ d ∈ Finset.Icc 1 n,
          (if a * b = k then ((b ^ 1 : Nat) : Int) else 0) *
            (if c * d = n - k then ((d ^ 3 : Nat) : Int) else 0) := by
  rw [mul_comm]
  simp only [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro d _
  ring

theorem sum_factorPair_k_eq_liouville_weight_general {r s n a b c d : Nat}
    (ha : a ∈ Finset.Icc 1 n) (hb : b ∈ Finset.Icc 1 n)
    (hc : c ∈ Finset.Icc 1 n) (hd : d ∈ Finset.Icc 1 n) :
    (∑ k ∈ Finset.Icc 1 (n - 1),
      (if a * b = k then ((b ^ r : Nat) : Int) else 0) *
        (if c * d = n - k then ((d ^ s : Nat) : Int) else 0)) =
      if a * b + c * d = n then (b : Int) ^ r * (d : Int) ^ s else 0 := by
  have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
  have hb1 : 1 ≤ b := (Finset.mem_Icc.mp hb).1
  have hc1 : 1 ≤ c := (Finset.mem_Icc.mp hc).1
  have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
  by_cases hsum : a * b + c * d = n
  · rw [if_pos hsum]
    rw [Finset.sum_eq_single (a * b)]
    · have hcdpos : 1 ≤ c * d := Nat.mul_pos hc1 hd1
      have hab_le : a * b ≤ n := by omega
      have hsub : n - a * b = c * d := by omega
      simp [hsub, Nat.cast_pow]
    · intro k _ hne
      have hab_ne : ¬ a * b = k := fun h => hne h.symm
      simp [hab_ne]
    · intro hnot
      have habpos : 1 ≤ a * b := Nat.mul_pos ha1 hb1
      have hcdpos : 1 ≤ c * d := Nat.mul_pos hc1 hd1
      have hab_le_pred : a * b ≤ n - 1 := by omega
      exact False.elim (hnot (Finset.mem_Icc.mpr ⟨habpos, hab_le_pred⟩))
  · rw [if_neg hsum]
    apply Finset.sum_eq_zero
    intro k hk
    by_cases hab : a * b = k
    · by_cases hcd : c * d = n - k
      · have hk_le : k ≤ n := by
          have hk' := (Finset.mem_Icc.mp hk).2
          omega
        have hsum' : a * b + c * d = n := by
          rw [hab, hcd]
          omega
        exact False.elim (hsum hsum')
      · simp [hab, hcd]
    · simp [hab]

theorem sum_factorPair_k_eq_liouville_weight {n a b c d : Nat}
    (ha : a ∈ Finset.Icc 1 n) (hb : b ∈ Finset.Icc 1 n)
    (hc : c ∈ Finset.Icc 1 n) (hd : d ∈ Finset.Icc 1 n) :
    (∑ k ∈ Finset.Icc 1 (n - 1),
      (if a * b = k then ((b ^ 1 : Nat) : Int) else 0) *
        (if c * d = n - k then ((d ^ 3 : Nat) : Int) else 0)) =
      if a * b + c * d = n then (b : Int) * (d : Int) ^ 3 else 0 := by
  have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
  have hb1 : 1 ≤ b := (Finset.mem_Icc.mp hb).1
  have hc1 : 1 ≤ c := (Finset.mem_Icc.mp hc).1
  have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
  by_cases hsum : a * b + c * d = n
  · rw [if_pos hsum]
    rw [Finset.sum_eq_single (a * b)]
    · have hcdpos : 1 ≤ c * d := Nat.mul_pos hc1 hd1
      have hab_le : a * b ≤ n := by omega
      have hsub : n - a * b = c * d := by omega
      simp [hsub]
    · intro k _ hne
      have hab_ne : ¬ a * b = k := fun h => hne h.symm
      simp [hab_ne]
    · intro hnot
      have habpos : 1 ≤ a * b := Nat.mul_pos ha1 hb1
      have hcdpos : 1 ≤ c * d := Nat.mul_pos hc1 hd1
      have hab_le_pred : a * b ≤ n - 1 := by omega
      exact False.elim (hnot (Finset.mem_Icc.mpr ⟨habpos, hab_le_pred⟩))
  · rw [if_neg hsum]
    apply Finset.sum_eq_zero
    intro k hk
    by_cases hab : a * b = k
    · by_cases hcd : c * d = n - k
      · have hk_le : k ≤ n := by
          have hk' := (Finset.mem_Icc.mp hk).2
          omega
        have hsum' : a * b + c * d = n := by
          rw [hab, hcd]
          omega
        exact False.elim (hsum hsum')
      · simp [hab, hcd]
    · simp [hab]

theorem factorPairRightSplitSumZ_eq_liouvilleBD3Sum (n : Nat) :
    sigma1Sigma3FactorPairRightSplitSumZ n = liouvilleBD3Sum n := by
  rw [liouvilleBD3Sum_eq_nested]
  unfold sigma1Sigma3FactorPairRightSplitSumZ
  calc
    (∑ k ∈ Finset.Icc 1 (n - 1),
      (∑ a ∈ Finset.Icc 1 n, ∑ b ∈ Finset.Icc 1 n,
        if a * b = k then ↑(b ^ 1) else 0) *
        ∑ c ∈ Finset.Icc 1 n, ∑ d ∈ Finset.Icc 1 n,
          if c * d = n - k then ↑(d ^ 3) else 0)
        = ∑ k ∈ Finset.Icc 1 (n - 1),
            ∑ a ∈ Finset.Icc 1 n, ∑ b ∈ Finset.Icc 1 n,
              ∑ c ∈ Finset.Icc 1 n, ∑ d ∈ Finset.Icc 1 n,
                (if a * b = k then ((b ^ 1 : Nat) : Int) else 0) *
                  (if c * d = n - k then ((d ^ 3 : Nat) : Int) else 0) := by
          apply Finset.sum_congr rfl
          intro k _
          exact factorPairRightSplit_product_expansion n k
    _ = ∑ a ∈ Finset.Icc 1 n, ∑ b ∈ Finset.Icc 1 n,
          ∑ c ∈ Finset.Icc 1 n, ∑ d ∈ Finset.Icc 1 n,
            ∑ k ∈ Finset.Icc 1 (n - 1),
              (if a * b = k then ((b ^ 1 : Nat) : Int) else 0) *
                (if c * d = n - k then ((d ^ 3 : Nat) : Int) else 0) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro b _
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro c _
          rw [Finset.sum_comm]
    _ = ∑ a ∈ Finset.Icc 1 n, ∑ b ∈ Finset.Icc 1 n,
          ∑ c ∈ Finset.Icc 1 n, ∑ d ∈ Finset.Icc 1 n,
            if a * b + c * d = n then (b : Int) * (d : Int) ^ 3 else 0 := by
          apply Finset.sum_congr rfl
          intro a ha
          apply Finset.sum_congr rfl
          intro b hb
          apply Finset.sum_congr rfl
          intro c hc
          apply Finset.sum_congr rfl
          intro d hd
          exact sum_factorPair_k_eq_liouville_weight ha hb hc hd

theorem sigmaSigmaFactorPairRightSplitSumZ_eq_liouvilleBpowDpowSum
    (r s n : Nat) :
    sigmaSigmaFactorPairRightSplitSumZ r s n = liouvilleBpowDpowSum r s n := by
  rw [liouvilleBpowDpowSum_eq_nested]
  unfold sigmaSigmaFactorPairRightSplitSumZ
  calc
    (∑ k ∈ Finset.Icc 1 (n - 1),
      (∑ a ∈ Finset.Icc 1 n, ∑ b ∈ Finset.Icc 1 n,
        if a * b = k then ↑(b ^ r) else 0) *
        ∑ c ∈ Finset.Icc 1 n, ∑ d ∈ Finset.Icc 1 n,
          if c * d = n - k then ↑(d ^ s) else 0)
        = ∑ k ∈ Finset.Icc 1 (n - 1),
            ∑ a ∈ Finset.Icc 1 n, ∑ b ∈ Finset.Icc 1 n,
              ∑ c ∈ Finset.Icc 1 n, ∑ d ∈ Finset.Icc 1 n,
                (if a * b = k then ((b ^ r : Nat) : Int) else 0) *
                  (if c * d = n - k then ((d ^ s : Nat) : Int) else 0) := by
          apply Finset.sum_congr rfl
          intro k _
          exact factorPairRightSplit_product_expansion_general r s n k
    _ = ∑ a ∈ Finset.Icc 1 n, ∑ b ∈ Finset.Icc 1 n,
          ∑ c ∈ Finset.Icc 1 n, ∑ d ∈ Finset.Icc 1 n,
            ∑ k ∈ Finset.Icc 1 (n - 1),
              (if a * b = k then ((b ^ r : Nat) : Int) else 0) *
                (if c * d = n - k then ((d ^ s : Nat) : Int) else 0) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro b _
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro c _
          rw [Finset.sum_comm]
    _ = ∑ a ∈ Finset.Icc 1 n, ∑ b ∈ Finset.Icc 1 n,
          ∑ c ∈ Finset.Icc 1 n, ∑ d ∈ Finset.Icc 1 n,
            if a * b + c * d = n then (b : Int) ^ r * (d : Int) ^ s else 0 := by
          apply Finset.sum_congr rfl
          intro a ha
          apply Finset.sum_congr rfl
          intro b hb
          apply Finset.sum_congr rfl
          intro c hc
          apply Finset.sum_congr rfl
          intro d hd
          exact sum_factorPair_k_eq_liouville_weight_general ha hb hc hd

theorem sigmaSigmaConvZ_eq_liouvilleBpowDpowSum (r s n : Nat) :
    sigmaSigmaConvZ r s n = liouvilleBpowDpowSum r s n := by
  rw [sigmaSigmaConvZ_eq_factorPairRightSplitSumZ,
    sigmaSigmaFactorPairRightSplitSumZ_eq_liouvilleBpowDpowSum]

theorem sigma1Sigma5ConvZ_eq_liouvilleBD5Sum (n : Nat) :
    sigmaSigmaConvZ 1 5 n = liouvilleBD5Sum n := by
  rw [sigmaSigmaConvZ_eq_liouvilleBpowDpowSum]
  unfold liouvilleBpowDpowSum liouvilleBD5Sum weightBpowDpow weightBD5
  simp

theorem sigma3Sigma3ConvZ_eq_liouvilleB3D3Sum (n : Nat) :
    sigmaSigmaConvZ 3 3 n = liouvilleB3D3Sum n := by
  rw [sigmaSigmaConvZ_eq_liouvilleBpowDpowSum]
  unfold liouvilleBpowDpowSum liouvilleB3D3Sum weightBpowDpow weightB3D3
  rfl

theorem sigma1Sigma3ConvZ_eq_liouvilleBD3Sum (n : Nat) :
    sigma1Sigma3ConvZ n = liouvilleBD3Sum n := by
  rw [sigma1Sigma3ConvZ_eq_factorPairRightSplitSumZ,
    factorPairRightSplitSumZ_eq_liouvilleBD3Sum]

theorem sum_swap_liouvilleQ (n : Nat) (F : LQuad → Int) :
    (∑ q ∈ liouvilleQ n, F (swapQuad q)) =
      ∑ q ∈ liouvilleQ n, F q := by
  refine Finset.sum_equiv swapQuadEquiv ?_ ?_
  · intro q
    exact (swapQuad_mem_liouvilleQ_iff n q).symm
  · intro q _
    rfl

theorem two_mul_liouvilleBD3Sum_eq_liouvilleWSum (n : Nat) :
    2 * liouvilleBD3Sum n = liouvilleWSum n := by
  unfold liouvilleBD3Sum liouvilleWSum
  have hswap :
      (∑ q ∈ liouvilleQ n, weightBD3 (swapQuad q)) =
        ∑ q ∈ liouvilleQ n, weightBD3 q :=
    sum_swap_liouvilleQ n weightBD3
  calc
    2 * (∑ q ∈ liouvilleQ n, weightBD3 q)
        = (∑ q ∈ liouvilleQ n, weightBD3 q) +
            ∑ q ∈ liouvilleQ n, weightBD3 (swapQuad q) := by
              rw [hswap]
              ring
    _ = ∑ q ∈ liouvilleQ n, (weightBD3 q + weightBD3 (swapQuad q)) := by
              rw [Finset.sum_add_distrib]
    _ = ∑ q ∈ liouvilleQ n, weightW q := by
              apply Finset.sum_congr rfl
              intro q _
              unfold weightBD3 weightW swapQuad
              ring

def liouvilleP (b d : Int) : Int :=
  (b ^ 2 + b * d + d ^ 2) ^ 2

def liouvilleWBD (b d : Int) : Int :=
  b * d * (b ^ 2 + d ^ 2)

theorem liouvilleP_step_int (b d : Int) :
    liouvilleP b d - liouvilleP b (d - b) = 4 * liouvilleWBD b d := by
  unfold liouvilleP liouvilleWBD
  ring

theorem liouvilleP_step_nat {b d : Nat} (hbd : b ≤ d) :
    liouvilleP (b : Int) (d : Int) -
      liouvilleP (b : Int) ((d - b : Nat) : Int) =
        4 * liouvilleWBD (b : Int) (d : Int) := by
  rw [Nat.cast_sub hbd]
  exact liouvilleP_step_int (b : Int) (d : Int)

theorem liouvilleP_comm (b d : Int) :
    liouvilleP b d = liouvilleP d b := by
  unfold liouvilleP
  ring

def liouvilleP15 (b d : Int) : Int :=
  (b ^ 2 + b * d + d ^ 2) ^ 3

def liouvilleP33 (b d : Int) : Int :=
  b ^ 2 * d ^ 2 * (b + d) ^ 2

theorem liouvilleP15_step_int (b d : Int) :
    liouvilleP15 b d - liouvilleP15 b (d - b) =
      6 * b ^ 5 * d + 14 * b ^ 3 * d ^ 3 + 6 * b * d ^ 5 := by
  unfold liouvilleP15
  ring

theorem liouvilleP33_step_int (b d : Int) :
    liouvilleP33 b d - liouvilleP33 b (d - b) =
      4 * b ^ 3 * d ^ 3 := by
  unfold liouvilleP33
  ring

theorem liouvilleP15_comm (b d : Int) :
    liouvilleP15 b d = liouvilleP15 d b := by
  unfold liouvilleP15
  ring

theorem liouvilleP33_comm (b d : Int) :
    liouvilleP33 b d = liouvilleP33 d b := by
  unfold liouvilleP33
  ring

def liouvillePQ (b d : ℚ) : ℚ :=
  (b ^ 2 + b * d + d ^ 2) ^ 2

def liouvilleP33Q (b d : ℚ) : ℚ :=
  b ^ 2 * d ^ 2 * (b + d) ^ 2

def liouvilleP15Q (b d : ℚ) : ℚ :=
  (b ^ 2 + b * d + d ^ 2) ^ 3

theorem sum_Ico_pow_one_Q (M : Nat) :
    (∑ x ∈ Finset.Ico 1 (M + 1), (x : ℚ) ^ 1) =
      ((M : ℚ) ^ 2 + (M : ℚ)) / 2 := by
  rw [sum_Ico_pow M 1]
  norm_num [Finset.sum_range_succ, bernoulli'_zero, bernoulli'_one]
  ring_nf

theorem sum_Ico_pow_two_Q (M : Nat) :
    (∑ x ∈ Finset.Ico 1 (M + 1), (x : ℚ) ^ 2) =
      ((M : ℚ) ^ 3 * 2 + (M : ℚ) ^ 2 * 3 + (M : ℚ)) / 6 := by
  rw [sum_Ico_pow M 2]
  norm_num [Finset.sum_range_succ, bernoulli'_zero, bernoulli'_one,
    bernoulli'_two]
  ring_nf

theorem sum_Ico_pow_three_Q (M : Nat) :
    (∑ x ∈ Finset.Ico 1 (M + 1), (x : ℚ) ^ 3) =
      ((M : ℚ) ^ 4 + 2 * (M : ℚ) ^ 3 + (M : ℚ) ^ 2) / 4 := by
  rw [sum_Ico_pow M 3]
  norm_num [Finset.sum_range_succ, bernoulli'_zero, bernoulli'_one,
    bernoulli'_two, bernoulli'_three, Nat.choose]
  ring_nf

theorem sum_Ico_pow_four_Q (M : Nat) :
    (∑ x ∈ Finset.Ico 1 (M + 1), (x : ℚ) ^ 4) =
      (6 * (M : ℚ) ^ 5 + 15 * (M : ℚ) ^ 4 + 10 * (M : ℚ) ^ 3 -
        (M : ℚ)) / 30 := by
  rw [sum_Ico_pow M 4]
  norm_num [Finset.sum_range_succ, bernoulli'_zero, bernoulli'_one,
    bernoulli'_two, bernoulli'_three, bernoulli'_four, Nat.choose]
  ring_nf

theorem sum_Ico_pow_five_Q (M : Nat) :
    (∑ x ∈ Finset.Ico 1 (M + 1), (x : ℚ) ^ 5) =
      (2 * (M : ℚ) ^ 6 + 6 * (M : ℚ) ^ 5 +
        5 * (M : ℚ) ^ 4 - (M : ℚ) ^ 2) / 12 := by
  rw [sum_Ico_pow M 5]
  norm_num [Finset.sum_range_succ, bernoulli'_zero, bernoulli'_one,
    bernoulli'_two, bernoulli'_three, bernoulli'_four]
  have hb5 : bernoulli' 5 = (0 : ℚ) := by native_decide
  rw [hb5]
  norm_num [Nat.choose]
  ring_nf

theorem sum_Ico_pow_six_Q (M : Nat) :
    (∑ x ∈ Finset.Ico 1 (M + 1), (x : ℚ) ^ 6) =
      (6 * (M : ℚ) ^ 7 + 21 * (M : ℚ) ^ 6 +
        21 * (M : ℚ) ^ 5 - 7 * (M : ℚ) ^ 3 + (M : ℚ)) / 42 := by
  rw [sum_Ico_pow M 6]
  norm_num [Finset.sum_range_succ, bernoulli'_zero, bernoulli'_one,
    bernoulli'_two, bernoulli'_three, bernoulli'_four]
  have hb5 : bernoulli' 5 = (0 : ℚ) := by native_decide
  have hb6 : bernoulli' 6 = (1 / 42 : ℚ) := by native_decide
  rw [hb5, hb6]
  norm_num [Nat.choose]
  ring_nf

theorem sum_liouvillePQ_antidiagonal_expanded (M : Nat) :
    (∑ b ∈ Finset.Ico 1 (M + 1),
        liouvillePQ (b : ℚ) (((M + 1 : Nat) : ℚ) - (b : ℚ))) =
      ((M + 1 : Nat) : ℚ) ^ 4 * ((Finset.Ico 1 (M + 1)).card : ℚ) -
        2 * ((M + 1 : Nat) : ℚ) ^ 3 *
          (∑ b ∈ Finset.Ico 1 (M + 1), (b : ℚ) ^ 1) +
        3 * ((M + 1 : Nat) : ℚ) ^ 2 *
          (∑ b ∈ Finset.Ico 1 (M + 1), (b : ℚ) ^ 2) -
        2 * ((M + 1 : Nat) : ℚ) *
          (∑ b ∈ Finset.Ico 1 (M + 1), (b : ℚ) ^ 3) +
        ∑ b ∈ Finset.Ico 1 (M + 1), (b : ℚ) ^ 4 := by
  let mm : ℚ := ((M + 1 : Nat) : ℚ)
  let s := Finset.Ico 1 (M + 1)
  have hs1 :
      (∑ x ∈ s, 2 * mm ^ 3 * (x : ℚ) ^ 1) =
        2 * mm ^ 3 * ∑ x ∈ s, (x : ℚ) ^ 1 := by
    rw [← Finset.mul_sum]
  have hs2 :
      (∑ x ∈ s, 3 * mm ^ 2 * (x : ℚ) ^ 2) =
        3 * mm ^ 2 * ∑ x ∈ s, (x : ℚ) ^ 2 := by
    rw [← Finset.mul_sum]
  have hs3 :
      (∑ x ∈ s, 2 * mm * (x : ℚ) ^ 3) =
        2 * mm * ∑ x ∈ s, (x : ℚ) ^ 3 := by
    rw [← Finset.mul_sum]
  change (∑ b ∈ s, liouvillePQ (b : ℚ) (mm - (b : ℚ))) =
      mm ^ 4 * (s.card : ℚ) -
        2 * mm ^ 3 * (∑ b ∈ s, (b : ℚ) ^ 1) +
        3 * mm ^ 2 * (∑ b ∈ s, (b : ℚ) ^ 2) -
        2 * mm * (∑ b ∈ s, (b : ℚ) ^ 3) +
        ∑ b ∈ s, (b : ℚ) ^ 4
  calc
    (∑ b ∈ s, liouvillePQ (b : ℚ) (mm - (b : ℚ)))
        = ∑ b ∈ s,
            (mm ^ 4 - 2 * mm ^ 3 * (b : ℚ) ^ 1 +
              3 * mm ^ 2 * (b : ℚ) ^ 2 - 2 * mm * (b : ℚ) ^ 3 +
                (b : ℚ) ^ 4) := by
          apply Finset.sum_congr rfl
          intro b _
          unfold liouvillePQ
          ring
    _ = _ := by
          simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
            Finset.sum_const, nsmul_eq_mul]
          rw [hs1, hs2, hs3]
          ring

theorem thirty_mul_sum_liouvillePQ_antidiagonal (m : Nat) :
    (30 : ℚ) *
      (∑ b ∈ Finset.Ico 1 m,
        liouvillePQ (b : ℚ) ((m - b : Nat) : ℚ)) =
      21 * (m : ℚ) ^ 5 - 30 * (m : ℚ) ^ 4 +
        10 * (m : ℚ) ^ 3 - (m : ℚ) := by
  cases m with
  | zero =>
      simp [liouvillePQ]
  | succ M =>
      calc
        (30 : ℚ) *
            (∑ b ∈ Finset.Ico 1 (M + 1),
              liouvillePQ (b : ℚ) (((M + 1) - b : Nat) : ℚ))
            = (30 : ℚ) *
                (∑ b ∈ Finset.Ico 1 (M + 1),
                  liouvillePQ (b : ℚ) (((M + 1 : Nat) : ℚ) - (b : ℚ))) := by
              congr 1
              apply Finset.sum_congr rfl
              intro b hb
              have hbm : b ≤ M + 1 := le_of_lt (Finset.mem_Ico.mp hb).2
              rw [Nat.cast_sub hbm]
        _ = 21 * ((M + 1 : Nat) : ℚ) ^ 5 -
              30 * ((M + 1 : Nat) : ℚ) ^ 4 +
              10 * ((M + 1 : Nat) : ℚ) ^ 3 -
                (((M + 1 : Nat) : ℚ)) := by
              rw [sum_liouvillePQ_antidiagonal_expanded]
              rw [sum_Ico_pow_one_Q, sum_Ico_pow_two_Q,
                sum_Ico_pow_three_Q, sum_Ico_pow_four_Q]
              simp [Nat.card_Ico]
              ring

theorem liouvilleP_cast_Q (b d : Nat) :
    ((liouvilleP (b : Int) (d : Int) : Int) : ℚ) =
      liouvillePQ (b : ℚ) (d : ℚ) := by
  unfold liouvilleP liouvillePQ
  push_cast
  rfl

theorem thirty_mul_sum_liouvilleP_antidiagonal (m : Nat) :
    (30 : Int) *
      (∑ b ∈ Finset.Ico 1 m,
        liouvilleP (b : Int) ((m - b : Nat) : Int)) =
      21 * (m : Int) ^ 5 - 30 * (m : Int) ^ 4 +
        10 * (m : Int) ^ 3 - (m : Int) := by
  apply (Int.cast_injective (α := ℚ))
  rw [Int.cast_mul, Int.cast_sum]
  have hsum :
      (∑ b ∈ Finset.Ico 1 m,
        ((liouvilleP (b : Int) ((m - b : Nat) : Int) : Int) : ℚ)) =
        ∑ b ∈ Finset.Ico 1 m,
          liouvillePQ (b : ℚ) ((m - b : Nat) : ℚ) := by
    apply Finset.sum_congr rfl
    intro b _
    exact liouvilleP_cast_Q b (m - b)
  rw [hsum]
  norm_num only [Int.cast_ofNat]
  rw [thirty_mul_sum_liouvillePQ_antidiagonal]
  push_cast
  ring

theorem thirty_mul_sum_liouvilleP33Q_antidiagonal (m : Nat) :
    (30 : ℚ) *
      (∑ b ∈ Finset.Ico 1 m,
        liouvilleP33Q (b : ℚ) ((m - b : Nat) : ℚ)) =
      (m : ℚ) ^ 7 - (m : ℚ) ^ 3 := by
  cases m with
  | zero =>
      simp [liouvilleP33Q]
  | succ M =>
      let mm : ℚ := ((M + 1 : Nat) : ℚ)
      let s := Finset.Ico 1 (M + 1)
      have hcast :
          (∑ b ∈ s,
            liouvilleP33Q (b : ℚ) (((M + 1) - b : Nat) : ℚ)) =
            ∑ b ∈ s, liouvilleP33Q (b : ℚ) (mm - (b : ℚ)) := by
        apply Finset.sum_congr rfl
        intro b hb
        have hbm : b ≤ M + 1 := le_of_lt (Finset.mem_Ico.mp hb).2
        rw [Nat.cast_sub hbm]
      have hs2 :
          (∑ b ∈ s, mm ^ 4 * (b : ℚ) ^ 2) =
            mm ^ 4 * ∑ b ∈ s, (b : ℚ) ^ 2 := by
        rw [← Finset.mul_sum]
      have hs3 :
          (∑ b ∈ s, 2 * mm ^ 3 * (b : ℚ) ^ 3) =
            2 * mm ^ 3 * ∑ b ∈ s, (b : ℚ) ^ 3 := by
        rw [← Finset.mul_sum]
      have hs4 :
          (∑ b ∈ s, mm ^ 2 * (b : ℚ) ^ 4) =
            mm ^ 2 * ∑ b ∈ s, (b : ℚ) ^ 4 := by
        rw [← Finset.mul_sum]
      have hsum :
          (∑ b ∈ s, liouvilleP33Q (b : ℚ) (mm - (b : ℚ))) =
            mm ^ 4 * (∑ b ∈ s, (b : ℚ) ^ 2) -
              2 * mm ^ 3 * (∑ b ∈ s, (b : ℚ) ^ 3) +
                mm ^ 2 * (∑ b ∈ s, (b : ℚ) ^ 4) := by
        calc
          (∑ b ∈ s, liouvilleP33Q (b : ℚ) (mm - (b : ℚ)))
              = ∑ b ∈ s,
                  (mm ^ 4 * (b : ℚ) ^ 2 -
                    2 * mm ^ 3 * (b : ℚ) ^ 3 +
                      mm ^ 2 * (b : ℚ) ^ 4) := by
                apply Finset.sum_congr rfl
                intro b _
                unfold liouvilleP33Q
                ring_nf
          _ = _ := by
                simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
                rw [hs2, hs3, hs4]
      calc
        (30 : ℚ) *
            (∑ b ∈ Finset.Ico 1 (M + 1),
              liouvilleP33Q (b : ℚ) (((M + 1) - b : Nat) : ℚ))
            = 30 * (∑ b ∈ s, liouvilleP33Q (b : ℚ) (mm - (b : ℚ))) := by
              rw [hcast]
        _ = 30 * (mm ^ 4 * (∑ b ∈ s, (b : ℚ) ^ 2) -
              2 * mm ^ 3 * (∑ b ∈ s, (b : ℚ) ^ 3) +
                mm ^ 2 * (∑ b ∈ s, (b : ℚ) ^ 4)) := by
              rw [hsum]
        _ = ((M + 1 : Nat) : ℚ) ^ 7 - ((M + 1 : Nat) : ℚ) ^ 3 := by
              unfold s mm
              rw [sum_Ico_pow_two_Q, sum_Ico_pow_three_Q,
                sum_Ico_pow_four_Q]
              norm_num [Nat.cast_add, Nat.cast_one]
              ring_nf

theorem liouvilleP33_cast_Q (b d : Nat) :
    ((liouvilleP33 (b : Int) (d : Int) : Int) : ℚ) =
      liouvilleP33Q (b : ℚ) (d : ℚ) := by
  unfold liouvilleP33 liouvilleP33Q
  push_cast
  ring

theorem thirty_mul_sum_liouvilleP33_antidiagonal (m : Nat) :
    (30 : Int) *
      (∑ b ∈ Finset.Ico 1 m,
        liouvilleP33 (b : Int) ((m - b : Nat) : Int)) =
      (m : Int) ^ 7 - (m : Int) ^ 3 := by
  apply (Int.cast_injective (α := ℚ))
  rw [Int.cast_mul, Int.cast_sum]
  have hsum :
      (∑ b ∈ Finset.Ico 1 m,
        ((liouvilleP33 (b : Int) ((m - b : Nat) : Int) : Int) : ℚ)) =
        ∑ b ∈ Finset.Ico 1 m,
          liouvilleP33Q (b : ℚ) ((m - b : Nat) : ℚ) := by
    apply Finset.sum_congr rfl
    intro b _
    exact liouvilleP33_cast_Q b (m - b)
  rw [hsum]
  norm_num only [Int.cast_ofNat]
  rw [thirty_mul_sum_liouvilleP33Q_antidiagonal]
  push_cast
  ring

theorem liouvilleP15_cast_Q (b d : Nat) :
    ((liouvilleP15 (b : Int) (d : Int) : Int) : ℚ) =
      liouvilleP15Q (b : ℚ) (d : ℚ) := by
  unfold liouvilleP15 liouvilleP15Q
  push_cast
  ring

def liouvilleP15P33ComboQ (m b : Nat) : ℚ :=
  let d := m - b
  (1008 : ℚ) * liouvilleP15Q (b : ℚ) (d : ℚ) -
    17928 * liouvilleP33Q (b : ℚ) (d : ℚ)

def liouvilleP15P33ComboZ (m b : Nat) : Int :=
  let d := m - b
  (1008 : Int) * liouvilleP15 (b : Int) (d : Int) -
    17928 * liouvilleP33 (b : Int) (d : Int)

theorem sum_liouvilleP15_P33_comboQ_antidiagonal (m : Nat) :
    (∑ b ∈ Finset.Ico 1 m, liouvilleP15P33ComboQ m b) =
      24 * (m : ℚ) + 480 * (m : ℚ) ^ 3 +
        504 * (m : ℚ) ^ 5 - 1008 * (m : ℚ) ^ 6 := by
  cases m with
  | zero =>
      simp [liouvilleP15P33ComboQ]
  | succ M =>
      let mm : ℚ := ((M + 1 : Nat) : ℚ)
      let s := Finset.Ico 1 (M + 1)
      have hcast :
          (∑ b ∈ s, liouvilleP15P33ComboQ (M + 1) b) =
            ∑ b ∈ s,
              (1008 * liouvilleP15Q (b : ℚ) (mm - (b : ℚ)) -
                17928 * liouvilleP33Q (b : ℚ) (mm - (b : ℚ))) := by
        apply Finset.sum_congr rfl
        intro b hb
        have hbm : b ≤ M + 1 := le_of_lt (Finset.mem_Ico.mp hb).2
        dsimp [liouvilleP15P33ComboQ]
        rw [Nat.cast_sub hbm]
      have hsum :
          (∑ b ∈ s,
              (1008 * liouvilleP15Q (b : ℚ) (mm - (b : ℚ)) -
                17928 * liouvilleP33Q (b : ℚ) (mm - (b : ℚ)))) =
            1008 * (∑ b ∈ s, (b : ℚ) ^ 6) -
              3024 * mm * (∑ b ∈ s, (b : ℚ) ^ 5) -
              11880 * mm ^ 2 * (∑ b ∈ s, (b : ℚ) ^ 4) +
              28800 * mm ^ 3 * (∑ b ∈ s, (b : ℚ) ^ 3) -
              11880 * mm ^ 4 * (∑ b ∈ s, (b : ℚ) ^ 2) -
              3024 * mm ^ 5 * (∑ b ∈ s, (b : ℚ) ^ 1) +
              1008 * mm ^ 6 * (s.card : ℚ) := by
        calc
          (∑ b ∈ s,
              (1008 * liouvilleP15Q (b : ℚ) (mm - (b : ℚ)) -
                17928 * liouvilleP33Q (b : ℚ) (mm - (b : ℚ))))
              = ∑ b ∈ s,
                  (1008 * (b : ℚ) ^ 6 -
                    3024 * mm * (b : ℚ) ^ 5 -
                    11880 * mm ^ 2 * (b : ℚ) ^ 4 +
                    28800 * mm ^ 3 * (b : ℚ) ^ 3 -
                    11880 * mm ^ 4 * (b : ℚ) ^ 2 -
                    3024 * mm ^ 5 * (b : ℚ) ^ 1 +
                    1008 * mm ^ 6) := by
                apply Finset.sum_congr rfl
                intro b _
                unfold liouvilleP15Q liouvilleP33Q
                ring_nf
          _ = _ := by
                simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
                  Finset.sum_const, nsmul_eq_mul]
                rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
                  Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
                ring
      calc
        (∑ b ∈ Finset.Ico 1 (M + 1), liouvilleP15P33ComboQ (M + 1) b)
            = ∑ b ∈ s,
                (1008 * liouvilleP15Q (b : ℚ) (mm - (b : ℚ)) -
                  17928 * liouvilleP33Q (b : ℚ) (mm - (b : ℚ))) := by
              rw [hcast]
        _ = 1008 * (∑ b ∈ s, (b : ℚ) ^ 6) -
              3024 * mm * (∑ b ∈ s, (b : ℚ) ^ 5) -
              11880 * mm ^ 2 * (∑ b ∈ s, (b : ℚ) ^ 4) +
              28800 * mm ^ 3 * (∑ b ∈ s, (b : ℚ) ^ 3) -
              11880 * mm ^ 4 * (∑ b ∈ s, (b : ℚ) ^ 2) -
              3024 * mm ^ 5 * (∑ b ∈ s, (b : ℚ) ^ 1) +
              1008 * mm ^ 6 * (s.card : ℚ) := by
              rw [hsum]
        _ = 24 * ((M + 1 : Nat) : ℚ) +
              480 * ((M + 1 : Nat) : ℚ) ^ 3 +
              504 * ((M + 1 : Nat) : ℚ) ^ 5 -
              1008 * ((M + 1 : Nat) : ℚ) ^ 6 := by
              unfold s mm
              rw [sum_Ico_pow_one_Q, sum_Ico_pow_two_Q,
                sum_Ico_pow_three_Q, sum_Ico_pow_four_Q,
                sum_Ico_pow_five_Q, sum_Ico_pow_six_Q]
              simp [Nat.card_Ico]
              ring_nf

theorem sum_liouvilleP15_P33_combo_antidiagonal (m : Nat) :
    (∑ b ∈ Finset.Ico 1 m, liouvilleP15P33ComboZ m b) =
      24 * (m : Int) + 480 * (m : Int) ^ 3 +
        504 * (m : Int) ^ 5 - 1008 * (m : Int) ^ 6 := by
  apply (Int.cast_injective (α := ℚ))
  rw [Int.cast_sum]
  have hsum :
      (∑ b ∈ Finset.Ico 1 m,
        ((liouvilleP15P33ComboZ m b : Int) : ℚ)) =
        ∑ b ∈ Finset.Ico 1 m, liouvilleP15P33ComboQ m b := by
    apply Finset.sum_congr rfl
    intro b _
    unfold liouvilleP15P33ComboZ liouvilleP15P33ComboQ
    rw [Int.cast_sub, Int.cast_mul, Int.cast_mul,
      liouvilleP15_cast_Q, liouvilleP33_cast_Q]
    norm_num
  rw [hsum]
  rw [sum_liouvilleP15_P33_comboQ_antidiagonal]
  push_cast
  ring

def leftMove (q : LQuad) : LQuad :=
  { a := q.a - q.c, b := q.b, c := q.c, d := q.b + q.d }

def rightMove (q : LQuad) : LQuad :=
  { a := q.a, b := q.b + q.d, c := q.c - q.a, d := q.d }

def leftMoveInv (q : LQuad) : LQuad :=
  { a := q.a + q.c, b := q.b, c := q.c, d := q.d - q.b }

def rightMoveInv (q : LQuad) : LQuad :=
  { a := q.a, b := q.b - q.d, c := q.a + q.c, d := q.d }

/-- Region with `d > b`, the image of `gtPart` under `leftMove`. -/
def dGtBPart (n : Nat) : Finset LQuad :=
  (liouvilleQ n).filter fun q => q.b < q.d

/-- Region with `b > d`, the image of `ltPart` under `rightMove`. -/
def bGtDPart (n : Nat) : Finset LQuad :=
  (liouvilleQ n).filter fun q => q.d < q.b

theorem mem_dGtBPart_iff (n : Nat) (q : LQuad) :
    q ∈ dGtBPart n ↔ q ∈ liouvilleQ n ∧ q.b < q.d := by
  simp [dGtBPart]

theorem mem_bGtDPart_iff (n : Nat) (q : LQuad) :
    q ∈ bGtDPart n ↔ q ∈ liouvilleQ n ∧ q.d < q.b := by
  simp [bGtDPart]

theorem liouvilleQ_eq_bd_parts_union (n : Nat) :
    liouvilleQ n = (eqBDPart n ∪ dGtBPart n) ∪ bGtDPart n := by
  ext q
  rw [Finset.mem_union, Finset.mem_union, mem_eqBDPart_iff, mem_dGtBPart_iff,
    mem_bGtDPart_iff]
  constructor
  · intro hq
    rcases lt_trichotomy q.b q.d with hbd | hbd | hbd
    · exact Or.inl (Or.inr ⟨hq, hbd⟩)
    · exact Or.inl (Or.inl ⟨hq, hbd⟩)
    · exact Or.inr ⟨hq, hbd⟩
  · intro h
    rcases h with hleft | hbgt
    · rcases hleft with heq | hdgt
      · exact heq.1
      · exact hdgt.1
    · exact hbgt.1

theorem eqBDPart_disjoint_dGtBPart (n : Nat) :
    Disjoint (eqBDPart n) (dGtBPart n) := by
  rw [Finset.disjoint_left]
  intro q heq hdgt
  rw [mem_eqBDPart_iff] at heq
  rw [mem_dGtBPart_iff] at hdgt
  omega

theorem eqBDPart_disjoint_bGtDPart (n : Nat) :
    Disjoint (eqBDPart n) (bGtDPart n) := by
  rw [Finset.disjoint_left]
  intro q heq hbgt
  rw [mem_eqBDPart_iff] at heq
  rw [mem_bGtDPart_iff] at hbgt
  omega

theorem dGtBPart_disjoint_bGtDPart (n : Nat) :
    Disjoint (dGtBPart n) (bGtDPart n) := by
  rw [Finset.disjoint_left]
  intro q hdgt hbgt
  rw [mem_dGtBPart_iff] at hdgt
  rw [mem_bGtDPart_iff] at hbgt
  omega

theorem eqBDDgtPart_union_disjoint_bGtDPart (n : Nat) :
    Disjoint (eqBDPart n ∪ dGtBPart n) (bGtDPart n) := by
  rw [Finset.disjoint_left]
  intro q hleft hbgt
  rw [Finset.mem_union] at hleft
  rcases hleft with heq | hdgt
  · exact Finset.disjoint_left.mp (eqBDPart_disjoint_bGtDPart n) heq hbgt
  · exact Finset.disjoint_left.mp (dGtBPart_disjoint_bGtDPart n) hdgt hbgt

theorem sum_liouvilleQ_eq_bd_parts (n : Nat) (F : LQuad → Int) :
    (∑ q ∈ liouvilleQ n, F q) =
      (∑ q ∈ eqBDPart n, F q) + (∑ q ∈ dGtBPart n, F q) +
        ∑ q ∈ bGtDPart n, F q := by
  rw [liouvilleQ_eq_bd_parts_union n]
  rw [Finset.sum_union (eqBDDgtPart_union_disjoint_bGtDPart n),
    Finset.sum_union (eqBDPart_disjoint_dGtBPart n)]

theorem leftMove_mem_liouvilleQ {n : Nat} {q : LQuad}
    (hq : q ∈ liouvilleQ n) (hac : q.c < q.a) :
    leftMove q ∈ liouvilleQ n := by
  rw [mem_liouvilleQ_iff] at hq ⊢
  rcases hq with ⟨ha1, han, hb1, hbn, hc1, hcn, hd1, hdn, hsum⟩
  have hcle : q.c ≤ q.a := le_of_lt hac
  have hapos : 1 ≤ q.a - q.c := Nat.succ_le_iff.mpr (Nat.sub_pos_of_lt hac)
  have hsum' : (q.a - q.c) * q.b + q.c * (q.b + q.d) = n := by
    rw [← hsum]
    have hsub : (q.a - q.c) * q.b = q.a * q.b - q.c * q.b := by
      exact Nat.sub_mul q.a q.c q.b
    have hmul_le : q.c * q.b ≤ q.a * q.b := Nat.mul_le_mul_right q.b hcle
    rw [hsub]
    rw [Nat.mul_add]
    omega
  have hbd_le_n : q.b + q.d ≤ n := by
    have hle_prod : q.b + q.d ≤ q.c * (q.b + q.d) :=
      Nat.le_mul_of_pos_left (q.b + q.d) hc1
    have hprod_le : q.c * (q.b + q.d) ≤ n := by
      rw [← hsum']
      exact Nat.le_add_left _ _
    exact le_trans hle_prod hprod_le
  have hbd_pos : 1 ≤ q.b + q.d := by omega
  exact ⟨hapos, le_trans (Nat.sub_le q.a q.c) han,
    hb1, hbn, hc1, hcn, hbd_pos, hbd_le_n, hsum'⟩

theorem rightMove_mem_liouvilleQ {n : Nat} {q : LQuad}
    (hq : q ∈ liouvilleQ n) (hca : q.a < q.c) :
    rightMove q ∈ liouvilleQ n := by
  rw [mem_liouvilleQ_iff] at hq ⊢
  rcases hq with ⟨ha1, han, hb1, hbn, hc1, hcn, hd1, hdn, hsum⟩
  have hale : q.a ≤ q.c := le_of_lt hca
  have hcpos : 1 ≤ q.c - q.a := Nat.succ_le_iff.mpr (Nat.sub_pos_of_lt hca)
  have hsum' : q.a * (q.b + q.d) + (q.c - q.a) * q.d = n := by
    rw [← hsum]
    have hsub : (q.c - q.a) * q.d = q.c * q.d - q.a * q.d := by
      exact Nat.sub_mul q.c q.a q.d
    have hmul_le : q.a * q.d ≤ q.c * q.d := Nat.mul_le_mul_right q.d hale
    rw [hsub]
    rw [Nat.mul_add]
    omega
  have hbd_le_n : q.b + q.d ≤ n := by
    have hle_prod : q.b + q.d ≤ q.a * (q.b + q.d) :=
      Nat.le_mul_of_pos_left (q.b + q.d) ha1
    have hprod_le : q.a * (q.b + q.d) ≤ n := by
      rw [← hsum']
      exact Nat.le_add_right _ _
    exact le_trans hle_prod hprod_le
  have hbd_pos : 1 ≤ q.b + q.d := by omega
  exact ⟨ha1, han, hbd_pos, hbd_le_n, hcpos, le_trans (Nat.sub_le q.c q.a) hcn,
    hd1, hdn, hsum'⟩

theorem leftMove_mem_dGtBPart {n : Nat} {q : LQuad}
    (hq : q ∈ gtPart n) :
    leftMove q ∈ dGtBPart n := by
  rw [mem_gtPart_iff] at hq
  rw [mem_dGtBPart_iff]
  have hqQ := hq.1
  have hqQ' := (mem_liouvilleQ_iff n q).mp hqQ
  have hd1 : 1 ≤ q.d := by
    rcases hqQ' with ⟨_, _, _, _, _, _, hd1, _, _⟩
    exact hd1
  exact ⟨leftMove_mem_liouvilleQ hqQ hq.2, by
    dsimp [leftMove]
    exact Nat.lt_add_of_pos_right hd1⟩

theorem rightMove_mem_bGtDPart {n : Nat} {q : LQuad}
    (hq : q ∈ ltPart n) :
    rightMove q ∈ bGtDPart n := by
  rw [mem_ltPart_iff] at hq
  rw [mem_bGtDPart_iff]
  have hqQ := hq.1
  have hqQ' := (mem_liouvilleQ_iff n q).mp hqQ
  have hb1 : 1 ≤ q.b := by
    rcases hqQ' with ⟨_, _, hb1, _, _, _, _, _, _⟩
    exact hb1
  exact ⟨rightMove_mem_liouvilleQ hqQ hq.2, by
    dsimp [rightMove]
    exact Nat.lt_add_of_pos_left hb1⟩

theorem leftMoveInv_mem_gtPart {n : Nat} {q : LQuad}
    (hq : q ∈ dGtBPart n) :
    leftMoveInv q ∈ gtPart n := by
  rw [mem_dGtBPart_iff] at hq
  rw [mem_gtPart_iff]
  have hqQ := hq.1
  have hqQ' := (mem_liouvilleQ_iff n q).mp hqQ
  rcases hqQ' with ⟨ha1, han, hb1, hbn, hc1, hcn, hd1, hdn, hsum⟩
  have hbdle : q.b ≤ q.d := le_of_lt hq.2
  have hdsub_pos : 1 ≤ q.d - q.b := Nat.succ_le_iff.mpr (Nat.sub_pos_of_lt hq.2)
  have hsum' : (q.a + q.c) * q.b + q.c * (q.d - q.b) = n := by
    rw [← hsum]
    have hsub : q.c * (q.d - q.b) = q.c * q.d - q.c * q.b :=
      Nat.mul_sub_left_distrib q.c q.d q.b
    have hmul_le : q.c * q.b ≤ q.c * q.d := Nat.mul_le_mul_left q.c hbdle
    rw [hsub, Nat.add_mul]
    omega
  have ha_c_le_n : q.a + q.c ≤ n := by
    have hle_prod : q.a + q.c ≤ (q.a + q.c) * q.b :=
      Nat.le_mul_of_pos_right (q.a + q.c) hb1
    have hprod_le : (q.a + q.c) * q.b ≤ n := by
      rw [← hsum']
      exact Nat.le_add_right _ _
    exact le_trans hle_prod hprod_le
  have hleftQ : leftMoveInv q ∈ liouvilleQ n := by
    rw [mem_liouvilleQ_iff]
    simp only [leftMoveInv]
    exact ⟨le_trans ha1 (Nat.le_add_right q.a q.c), ha_c_le_n, hb1, hbn, hc1, hcn, hdsub_pos,
      le_trans (Nat.sub_le q.d q.b) hdn, hsum'⟩
  exact ⟨hleftQ, by
    dsimp [leftMoveInv]
    exact Nat.lt_add_of_pos_left ha1⟩

theorem rightMoveInv_mem_ltPart {n : Nat} {q : LQuad}
    (hq : q ∈ bGtDPart n) :
    rightMoveInv q ∈ ltPart n := by
  rw [mem_bGtDPart_iff] at hq
  rw [mem_ltPart_iff]
  have hqQ := hq.1
  have hqQ' := (mem_liouvilleQ_iff n q).mp hqQ
  rcases hqQ' with ⟨ha1, han, hb1, hbn, hc1, hcn, hd1, hdn, hsum⟩
  have hdble : q.d ≤ q.b := le_of_lt hq.2
  have hbsub_pos : 1 ≤ q.b - q.d := Nat.succ_le_iff.mpr (Nat.sub_pos_of_lt hq.2)
  have hsum' : q.a * (q.b - q.d) + (q.a + q.c) * q.d = n := by
    rw [← hsum]
    have hsub : q.a * (q.b - q.d) = q.a * q.b - q.a * q.d :=
      Nat.mul_sub_left_distrib q.a q.b q.d
    have hmul_le : q.a * q.d ≤ q.a * q.b := Nat.mul_le_mul_left q.a hdble
    rw [hsub, Nat.add_mul]
    omega
  have ha_c_le_n : q.a + q.c ≤ n := by
    have hle_prod : q.a + q.c ≤ (q.a + q.c) * q.d :=
      Nat.le_mul_of_pos_right (q.a + q.c) hd1
    have hprod_le : (q.a + q.c) * q.d ≤ n := by
      rw [← hsum']
      exact Nat.le_add_left _ _
    exact le_trans hle_prod hprod_le
  have hrightQ : rightMoveInv q ∈ liouvilleQ n := by
    rw [mem_liouvilleQ_iff]
    simp only [rightMoveInv]
    exact ⟨ha1, han, hbsub_pos, le_trans (Nat.sub_le q.b q.d) hbn,
      le_trans hc1 (Nat.le_add_left q.c q.a), ha_c_le_n, hd1, hdn, hsum'⟩
  exact ⟨hrightQ, by
    dsimp [rightMoveInv]
    exact Nat.lt_add_of_pos_right hc1⟩

theorem leftMoveInv_leftMove {n : Nat} {q : LQuad}
    (hq : q ∈ gtPart n) :
    leftMoveInv (leftMove q) = q := by
  rw [mem_gtPart_iff] at hq
  rcases q with ⟨a, b, c, d⟩
  simp [leftMoveInv, leftMove] at *
  omega

theorem leftMove_leftMoveInv {n : Nat} {q : LQuad}
    (hq : q ∈ dGtBPart n) :
    leftMove (leftMoveInv q) = q := by
  rw [mem_dGtBPart_iff] at hq
  rcases q with ⟨a, b, c, d⟩
  simp [leftMoveInv, leftMove] at *
  omega

theorem rightMoveInv_rightMove {n : Nat} {q : LQuad}
    (hq : q ∈ ltPart n) :
    rightMoveInv (rightMove q) = q := by
  rw [mem_ltPart_iff] at hq
  rcases q with ⟨a, b, c, d⟩
  simp [rightMoveInv, rightMove] at *
  omega

theorem rightMove_rightMoveInv {n : Nat} {q : LQuad}
    (hq : q ∈ bGtDPart n) :
    rightMove (rightMoveInv q) = q := by
  rw [mem_bGtDPart_iff] at hq
  rcases q with ⟨a, b, c, d⟩
  simp [rightMoveInv, rightMove] at *
  omega

theorem sum_gtPart_leftMove (n : Nat) (F : LQuad → Int) :
    (∑ q ∈ gtPart n, F (leftMove q)) =
      ∑ q ∈ dGtBPart n, F q := by
  refine Finset.sum_bij' (fun q _ => leftMove q) (fun q _ => leftMoveInv q)
    ?_ ?_ ?_ ?_ ?_
  · intro q hq
    exact leftMove_mem_dGtBPart hq
  · intro q hq
    exact leftMoveInv_mem_gtPart hq
  · intro q hq
    exact leftMoveInv_leftMove hq
  · intro q hq
    exact leftMove_leftMoveInv hq
  · intro q _
    rfl

theorem sum_gtPart_leftMove_weightW_eq_sum_dGtBPart_weightW (n : Nat) :
    (∑ q ∈ gtPart n, weightW (leftMove q)) =
      ∑ q ∈ dGtBPart n, weightW q :=
  sum_gtPart_leftMove n weightW

theorem sum_ltPart_rightMove (n : Nat) (F : LQuad → Int) :
    (∑ q ∈ ltPart n, F (rightMove q)) =
      ∑ q ∈ bGtDPart n, F q := by
  refine Finset.sum_bij' (fun q _ => rightMove q) (fun q _ => rightMoveInv q)
    ?_ ?_ ?_ ?_ ?_
  · intro q hq
    exact rightMove_mem_bGtDPart hq
  · intro q hq
    exact rightMoveInv_mem_ltPart hq
  · intro q hq
    exact rightMoveInv_rightMove hq
  · intro q hq
    exact rightMove_rightMoveInv hq
  · intro q _
    rfl

theorem sum_ltPart_rightMove_weightW_eq_sum_bGtDPart_weightW (n : Nat) :
    (∑ q ∈ ltPart n, weightW (rightMove q)) =
      ∑ q ∈ bGtDPart n, weightW q :=
  sum_ltPart_rightMove n weightW

theorem four_mul_weightW_eq_P_step_of_dGtB {n : Nat} {q : LQuad}
    (hq : q ∈ dGtBPart n) :
    4 * weightW q =
      liouvilleP (q.b : Int) (q.d : Int) -
        liouvilleP (q.b : Int) ((q.d - q.b : Nat) : Int) := by
  have hbd : q.b ≤ q.d := le_of_lt ((mem_dGtBPart_iff n q).mp hq).2
  have h := liouvilleP_step_nat (b := q.b) (d := q.d) hbd
  unfold weightW
  rw [h]
  unfold liouvilleWBD
  ring

theorem four_mul_weightW_eq_P_step_of_bGtD {n : Nat} {q : LQuad}
    (hq : q ∈ bGtDPart n) :
    4 * weightW q =
      liouvilleP (q.d : Int) (q.b : Int) -
        liouvilleP (q.d : Int) ((q.b - q.d : Nat) : Int) := by
  have hdb : q.d ≤ q.b := le_of_lt ((mem_bGtDPart_iff n q).mp hq).2
  have h := liouvilleP_step_nat (b := q.d) (d := q.b) hdb
  unfold weightW
  rw [h]
  unfold liouvilleWBD
  ring

theorem four_mul_sum_weightW_dGtB_eq_sum_P_step (n : Nat) :
    4 * (∑ q ∈ dGtBPart n, weightW q) =
      ∑ q ∈ dGtBPart n,
        (liouvilleP (q.b : Int) (q.d : Int) -
          liouvilleP (q.b : Int) ((q.d - q.b : Nat) : Int)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  exact four_mul_weightW_eq_P_step_of_dGtB hq

theorem four_mul_sum_weightW_bGtD_eq_sum_P_step (n : Nat) :
    4 * (∑ q ∈ bGtDPart n, weightW q) =
      ∑ q ∈ bGtDPart n,
        (liouvilleP (q.d : Int) (q.b : Int) -
          liouvilleP (q.d : Int) ((q.b - q.d : Nat) : Int)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  exact four_mul_weightW_eq_P_step_of_bGtD hq

theorem sum_dGtBPart_weightW_eq_sum_gtPart_leftMove_weightW (n : Nat) :
    (∑ q ∈ dGtBPart n, weightW q) =
      ∑ q ∈ gtPart n, weightW (leftMove q) := by
  simpa using (sum_gtPart_leftMove n weightW).symm

theorem sum_bGtDPart_weightW_eq_sum_ltPart_rightMove_weightW (n : Nat) :
    (∑ q ∈ bGtDPart n, weightW q) =
      ∑ q ∈ ltPart n, weightW (rightMove q) := by
  simpa using (sum_ltPart_rightMove n weightW).symm

theorem four_mul_sum_gtPart_leftMove_weightW_eq_sum_P_step (n : Nat) :
    4 * (∑ q ∈ gtPart n, weightW (leftMove q)) =
      ∑ q ∈ dGtBPart n,
        (liouvilleP (q.b : Int) (q.d : Int) -
          liouvilleP (q.b : Int) ((q.d - q.b : Nat) : Int)) := by
  rw [← sum_dGtBPart_weightW_eq_sum_gtPart_leftMove_weightW,
    four_mul_sum_weightW_dGtB_eq_sum_P_step]

theorem four_mul_sum_ltPart_rightMove_weightW_eq_sum_P_step (n : Nat) :
    4 * (∑ q ∈ ltPart n, weightW (rightMove q)) =
      ∑ q ∈ bGtDPart n,
        (liouvilleP (q.d : Int) (q.b : Int) -
          liouvilleP (q.d : Int) ((q.b - q.d : Nat) : Int)) := by
  rw [← sum_bGtDPart_weightW_eq_sum_ltPart_rightMove_weightW,
    four_mul_sum_weightW_bGtD_eq_sum_P_step]

theorem sum_dGtB_P_step_eq_sum_gtPart_leftMove_P_step (n : Nat) :
    (∑ q ∈ dGtBPart n,
      (liouvilleP (q.b : Int) (q.d : Int) -
        liouvilleP (q.b : Int) ((q.d - q.b : Nat) : Int))) =
      ∑ q ∈ gtPart n,
        (liouvilleP (q.b : Int) ((q.b + q.d : Nat) : Int) -
          liouvilleP (q.b : Int) (q.d : Int)) := by
  rw [← sum_gtPart_leftMove n
    (fun q =>
      liouvilleP (q.b : Int) (q.d : Int) -
        liouvilleP (q.b : Int) ((q.d - q.b : Nat) : Int))]
  apply Finset.sum_congr rfl
  intro q _
  simp [leftMove]

theorem sum_bGtD_P_step_eq_sum_ltPart_rightMove_P_step (n : Nat) :
    (∑ q ∈ bGtDPart n,
      (liouvilleP (q.d : Int) (q.b : Int) -
        liouvilleP (q.d : Int) ((q.b - q.d : Nat) : Int))) =
      ∑ q ∈ ltPart n,
        (liouvilleP (q.d : Int) ((q.b + q.d : Nat) : Int) -
          liouvilleP (q.d : Int) (q.b : Int)) := by
  rw [← sum_ltPart_rightMove n
    (fun q =>
      liouvilleP (q.d : Int) (q.b : Int) -
        liouvilleP (q.d : Int) ((q.b - q.d : Nat) : Int))]
  apply Finset.sum_congr rfl
  intro q _
  simp [rightMove]

theorem four_mul_sum_gtPart_leftMove_weightW_eq_gtPart_P_step (n : Nat) :
    4 * (∑ q ∈ gtPart n, weightW (leftMove q)) =
      ∑ q ∈ gtPart n,
        (liouvilleP (q.b : Int) ((q.b + q.d : Nat) : Int) -
          liouvilleP (q.b : Int) (q.d : Int)) := by
  rw [four_mul_sum_gtPart_leftMove_weightW_eq_sum_P_step,
    sum_dGtB_P_step_eq_sum_gtPart_leftMove_P_step]

theorem four_mul_sum_ltPart_rightMove_weightW_eq_ltPart_P_step (n : Nat) :
    4 * (∑ q ∈ ltPart n, weightW (rightMove q)) =
      ∑ q ∈ ltPart n,
        (liouvilleP (q.d : Int) ((q.b + q.d : Nat) : Int) -
          liouvilleP (q.d : Int) (q.b : Int)) := by
  rw [four_mul_sum_ltPart_rightMove_weightW_eq_sum_P_step,
    sum_bGtD_P_step_eq_sum_ltPart_rightMove_P_step]

theorem sum_dGtB_P_lower_eq_sum_gtPart_P (n : Nat) :
    (∑ q ∈ dGtBPart n,
      liouvilleP (q.b : Int) ((q.d - q.b : Nat) : Int)) =
      ∑ q ∈ gtPart n, liouvilleP (q.b : Int) (q.d : Int) := by
  refine Finset.sum_bij' (fun q _ => leftMoveInv q) (fun q _ => leftMove q)
    ?_ ?_ ?_ ?_ ?_
  · intro q hq
    exact leftMoveInv_mem_gtPart hq
  · intro q hq
    exact leftMove_mem_dGtBPart hq
  · intro q hq
    exact leftMove_leftMoveInv hq
  · intro q hq
    exact leftMoveInv_leftMove hq
  · intro q hq
    rw [mem_dGtBPart_iff] at hq
    have hbd : q.b ≤ q.d := le_of_lt hq.2
    simp [leftMoveInv, Nat.cast_sub hbd]

theorem sum_bGtD_P_lower_eq_sum_ltPart_P (n : Nat) :
    (∑ q ∈ bGtDPart n,
      liouvilleP (q.d : Int) ((q.b - q.d : Nat) : Int)) =
      ∑ q ∈ ltPart n, liouvilleP (q.d : Int) (q.b : Int) := by
  refine Finset.sum_bij' (fun q _ => rightMoveInv q) (fun q _ => rightMove q)
    ?_ ?_ ?_ ?_ ?_
  · intro q hq
    exact rightMoveInv_mem_ltPart hq
  · intro q hq
    exact rightMove_mem_bGtDPart hq
  · intro q hq
    exact rightMove_rightMoveInv hq
  · intro q hq
    exact rightMoveInv_rightMove hq
  · intro q hq
    rw [mem_bGtDPart_iff] at hq
    have hdb : q.d ≤ q.b := le_of_lt hq.2
    simp [rightMoveInv, Nat.cast_sub hdb]

theorem four_mul_sum_weightW_dGtB_telescope (n : Nat) :
    4 * (∑ q ∈ dGtBPart n, weightW q) =
      (∑ q ∈ dGtBPart n, liouvilleP (q.b : Int) (q.d : Int)) -
        ∑ q ∈ gtPart n, liouvilleP (q.b : Int) (q.d : Int) := by
  rw [four_mul_sum_weightW_dGtB_eq_sum_P_step n]
  rw [Finset.sum_sub_distrib]
  rw [sum_dGtB_P_lower_eq_sum_gtPart_P n]

theorem four_mul_sum_weightW_bGtD_telescope (n : Nat) :
    4 * (∑ q ∈ bGtDPart n, weightW q) =
      (∑ q ∈ bGtDPart n, liouvilleP (q.d : Int) (q.b : Int)) -
        ∑ q ∈ ltPart n, liouvilleP (q.d : Int) (q.b : Int) := by
  rw [four_mul_sum_weightW_bGtD_eq_sum_P_step n]
  rw [Finset.sum_sub_distrib]
  rw [sum_bGtD_P_lower_eq_sum_ltPart_P n]

theorem swapQuad_mem_gtPart_iff_ltPart (n : Nat) (q : LQuad) :
    swapQuad q ∈ gtPart n ↔ q ∈ ltPart n := by
  rw [mem_gtPart_iff, mem_ltPart_iff, swapQuad_mem_liouvilleQ_iff]
  simp [swapQuad]

theorem swapQuad_mem_dGtBPart_iff_bGtDPart (n : Nat) (q : LQuad) :
    swapQuad q ∈ dGtBPart n ↔ q ∈ bGtDPart n := by
  rw [mem_dGtBPart_iff, mem_bGtDPart_iff, swapQuad_mem_liouvilleQ_iff]
  simp [swapQuad]

theorem sum_ltPart_Pdb_eq_sum_gtPart_Pbd (n : Nat) :
    (∑ q ∈ ltPart n, liouvilleP (q.d : Int) (q.b : Int)) =
      ∑ q ∈ gtPart n, liouvilleP (q.b : Int) (q.d : Int) := by
  refine Finset.sum_equiv swapQuadEquiv ?_ ?_
  · intro q
    exact (swapQuad_mem_gtPart_iff_ltPart n q).symm
  · intro q _
    rfl

theorem sum_bGtD_Pdb_eq_sum_dGtB_Pbd (n : Nat) :
    (∑ q ∈ bGtDPart n, liouvilleP (q.d : Int) (q.b : Int)) =
      ∑ q ∈ dGtBPart n, liouvilleP (q.b : Int) (q.d : Int) := by
  refine Finset.sum_equiv swapQuadEquiv ?_ ?_
  · intro q
    exact (swapQuad_mem_dGtBPart_iff_bGtDPart n q).symm
  · intro q _
    rfl

theorem two_mul_strict_bd_P_difference_eq_boundary_P_difference (n : Nat) :
    2 * ((∑ q ∈ dGtBPart n, liouvilleP (q.b : Int) (q.d : Int)) -
      ∑ q ∈ gtPart n, liouvilleP (q.b : Int) (q.d : Int)) =
      (∑ q ∈ eqPart n, liouvilleP (q.b : Int) (q.d : Int)) -
        ∑ q ∈ eqBDPart n, liouvilleP (q.b : Int) (q.d : Int) := by
  have hbd := sum_liouvilleQ_eq_bd_parts n
    (fun q => liouvilleP (q.b : Int) (q.d : Int))
  have hac := sum_liouvilleQ_eq_parts n
    (fun q => liouvilleP (q.b : Int) (q.d : Int))
  have hbgt :
      (∑ q ∈ bGtDPart n, liouvilleP (q.b : Int) (q.d : Int)) =
        ∑ q ∈ dGtBPart n, liouvilleP (q.b : Int) (q.d : Int) := by
    calc
      (∑ q ∈ bGtDPart n, liouvilleP (q.b : Int) (q.d : Int))
          = ∑ q ∈ bGtDPart n, liouvilleP (q.d : Int) (q.b : Int) := by
              apply Finset.sum_congr rfl
              intro q _
              exact liouvilleP_comm (q.b : Int) (q.d : Int)
      _ = ∑ q ∈ dGtBPart n, liouvilleP (q.b : Int) (q.d : Int) :=
              sum_bGtD_Pdb_eq_sum_dGtB_Pbd n
  have hlt :
      (∑ q ∈ ltPart n, liouvilleP (q.b : Int) (q.d : Int)) =
        ∑ q ∈ gtPart n, liouvilleP (q.b : Int) (q.d : Int) := by
    calc
      (∑ q ∈ ltPart n, liouvilleP (q.b : Int) (q.d : Int))
          = ∑ q ∈ ltPart n, liouvilleP (q.d : Int) (q.b : Int) := by
              apply Finset.sum_congr rfl
              intro q _
              exact liouvilleP_comm (q.b : Int) (q.d : Int)
      _ = ∑ q ∈ gtPart n, liouvilleP (q.b : Int) (q.d : Int) :=
              sum_ltPart_Pdb_eq_sum_gtPart_Pbd n
  linarith

theorem four_mul_sum_strict_bd_weightW_eq_boundary_P_difference (n : Nat) :
    4 * ((∑ q ∈ dGtBPart n, weightW q) +
      ∑ q ∈ bGtDPart n, weightW q) =
      (∑ q ∈ eqPart n, liouvilleP (q.b : Int) (q.d : Int)) -
        ∑ q ∈ eqBDPart n, liouvilleP (q.b : Int) (q.d : Int) := by
  have hd := four_mul_sum_weightW_dGtB_telescope n
  have hb := four_mul_sum_weightW_bGtD_telescope n
  have hb' :
      4 * (∑ q ∈ bGtDPart n, weightW q) =
        (∑ q ∈ dGtBPart n, liouvilleP (q.b : Int) (q.d : Int)) -
          ∑ q ∈ gtPart n, liouvilleP (q.b : Int) (q.d : Int) := by
    rw [hb, sum_bGtD_Pdb_eq_sum_dGtB_Pbd,
      sum_ltPart_Pdb_eq_sum_gtPart_Pbd]
  have hboundary := two_mul_strict_bd_P_difference_eq_boundary_P_difference n
  linarith

theorem four_mul_weightW_sub_liouvilleP_of_eqBD {n : Nat} {q : LQuad}
    (hq : q ∈ eqBDPart n) :
    4 * weightW q - liouvilleP (q.b : Int) (q.d : Int) =
      -((q.b : Int) ^ 4) := by
  rw [mem_eqBDPart_iff] at hq
  unfold weightW liouvilleP
  rw [hq.2]
  ring

theorem four_mul_sum_eqBDPart_weightW_eq_boundary (n : Nat) :
    4 * (∑ q ∈ eqBDPart n, weightW q) =
      (∑ q ∈ eqBDPart n, liouvilleP (q.b : Int) (q.d : Int)) -
        ∑ q ∈ eqBDPart n, (q.b : Int) ^ 4 := by
  rw [Finset.mul_sum]
  calc
    (∑ q ∈ eqBDPart n, 4 * weightW q)
        = ∑ q ∈ eqBDPart n,
            (liouvilleP (q.b : Int) (q.d : Int) - (q.b : Int) ^ 4) := by
          apply Finset.sum_congr rfl
          intro q hq
          have h := four_mul_weightW_sub_liouvilleP_of_eqBD hq
          linarith
    _ = (∑ q ∈ eqBDPart n, liouvilleP (q.b : Int) (q.d : Int)) -
          ∑ q ∈ eqBDPart n, (q.b : Int) ^ 4 := by
          rw [Finset.sum_sub_distrib]

theorem four_mul_liouvilleWSum_eq_boundary (n : Nat) :
    4 * liouvilleWSum n =
      (∑ q ∈ eqPart n, liouvilleP (q.b : Int) (q.d : Int)) -
        ∑ q ∈ eqBDPart n, (q.b : Int) ^ 4 := by
  unfold liouvilleWSum
  have hsplit := sum_liouvilleQ_eq_bd_parts n weightW
  have hstrict := four_mul_sum_strict_bd_weightW_eq_boundary_P_difference n
  have heqBD := four_mul_sum_eqBDPart_weightW_eq_boundary n
  linarith

theorem sum_dGtB_P_lower_eq_sum_gtPart_P_general (n : Nat)
    (P : Int → Int → Int) :
    (∑ q ∈ dGtBPart n,
      P (q.b : Int) ((q.d - q.b : Nat) : Int)) =
      ∑ q ∈ gtPart n, P (q.b : Int) (q.d : Int) := by
  refine Finset.sum_bij' (fun q _ => leftMoveInv q) (fun q _ => leftMove q)
    ?_ ?_ ?_ ?_ ?_
  · intro q hq
    exact leftMoveInv_mem_gtPart hq
  · intro q hq
    exact leftMove_mem_dGtBPart hq
  · intro q hq
    exact leftMove_leftMoveInv hq
  · intro q hq
    exact leftMoveInv_leftMove hq
  · intro q hq
    rw [mem_dGtBPart_iff] at hq
    have hbd : q.b ≤ q.d := le_of_lt hq.2
    simp [leftMoveInv, Nat.cast_sub hbd]

theorem sum_bGtD_P_lower_eq_sum_ltPart_P_general (n : Nat)
    (P : Int → Int → Int) :
    (∑ q ∈ bGtDPart n,
      P (q.d : Int) ((q.b - q.d : Nat) : Int)) =
      ∑ q ∈ ltPart n, P (q.d : Int) (q.b : Int) := by
  refine Finset.sum_bij' (fun q _ => rightMoveInv q) (fun q _ => rightMove q)
    ?_ ?_ ?_ ?_ ?_
  · intro q hq
    exact rightMoveInv_mem_ltPart hq
  · intro q hq
    exact rightMove_mem_bGtDPart hq
  · intro q hq
    exact rightMove_rightMoveInv hq
  · intro q hq
    exact rightMoveInv_rightMove hq
  · intro q hq
    rw [mem_bGtDPart_iff] at hq
    have hdb : q.d ≤ q.b := le_of_lt hq.2
    simp [rightMoveInv, Nat.cast_sub hdb]

theorem sum_ltPart_Pdb_eq_sum_gtPart_Pbd_general (n : Nat)
    (P : Int → Int → Int) :
    (∑ q ∈ ltPart n, P (q.d : Int) (q.b : Int)) =
      ∑ q ∈ gtPart n, P (q.b : Int) (q.d : Int) := by
  refine Finset.sum_equiv swapQuadEquiv ?_ ?_
  · intro q
    exact (swapQuad_mem_gtPart_iff_ltPart n q).symm
  · intro q _
    rfl

theorem sum_bGtD_Pdb_eq_sum_dGtB_Pbd_general (n : Nat)
    (P : Int → Int → Int) :
    (∑ q ∈ bGtDPart n, P (q.d : Int) (q.b : Int)) =
      ∑ q ∈ dGtBPart n, P (q.b : Int) (q.d : Int) := by
  refine Finset.sum_equiv swapQuadEquiv ?_ ?_
  · intro q
    exact (swapQuad_mem_dGtBPart_iff_bGtDPart n q).symm
  · intro q _
    rfl

theorem two_mul_strict_bd_P_difference_eq_boundary_P_difference_general
    (n : Nat) (P : Int → Int → Int)
    (hcomm : ∀ b d, P b d = P d b) :
    2 * ((∑ q ∈ dGtBPart n, P (q.b : Int) (q.d : Int)) -
      ∑ q ∈ gtPart n, P (q.b : Int) (q.d : Int)) =
      (∑ q ∈ eqPart n, P (q.b : Int) (q.d : Int)) -
        ∑ q ∈ eqBDPart n, P (q.b : Int) (q.d : Int) := by
  have hbd := sum_liouvilleQ_eq_bd_parts n
    (fun q => P (q.b : Int) (q.d : Int))
  have hac := sum_liouvilleQ_eq_parts n
    (fun q => P (q.b : Int) (q.d : Int))
  have hbgt :
      (∑ q ∈ bGtDPart n, P (q.b : Int) (q.d : Int)) =
        ∑ q ∈ dGtBPart n, P (q.b : Int) (q.d : Int) := by
    calc
      (∑ q ∈ bGtDPart n, P (q.b : Int) (q.d : Int))
          = ∑ q ∈ bGtDPart n, P (q.d : Int) (q.b : Int) := by
              apply Finset.sum_congr rfl
              intro q _
              exact hcomm (q.b : Int) (q.d : Int)
      _ = ∑ q ∈ dGtBPart n, P (q.b : Int) (q.d : Int) :=
              sum_bGtD_Pdb_eq_sum_dGtB_Pbd_general n P
  have hlt :
      (∑ q ∈ ltPart n, P (q.b : Int) (q.d : Int)) =
        ∑ q ∈ gtPart n, P (q.b : Int) (q.d : Int) := by
    calc
      (∑ q ∈ ltPart n, P (q.b : Int) (q.d : Int))
          = ∑ q ∈ ltPart n, P (q.d : Int) (q.b : Int) := by
              apply Finset.sum_congr rfl
              intro q _
              exact hcomm (q.b : Int) (q.d : Int)
      _ = ∑ q ∈ gtPart n, P (q.b : Int) (q.d : Int) :=
              sum_ltPart_Pdb_eq_sum_gtPart_Pbd_general n P
  linarith

theorem scaled_sum_liouvilleQ_eq_boundary_general
    (n : Nat) (C : Int) (P : Int → Int → Int) (T B : LQuad → Int)
    (hcomm : ∀ b d, P b d = P d b)
    (hstepD : ∀ {q : LQuad}, q ∈ dGtBPart n →
      C * T q =
        P (q.b : Int) (q.d : Int) -
          P (q.b : Int) ((q.d - q.b : Nat) : Int))
    (hstepB : ∀ {q : LQuad}, q ∈ bGtDPart n →
      C * T q =
        P (q.d : Int) (q.b : Int) -
          P (q.d : Int) ((q.b - q.d : Nat) : Int))
    (heqBD : ∀ {q : LQuad}, q ∈ eqBDPart n →
      C * T q = P (q.b : Int) (q.d : Int) - B q) :
    C * (∑ q ∈ liouvilleQ n, T q) =
      (∑ q ∈ eqPart n, P (q.b : Int) (q.d : Int)) -
        ∑ q ∈ eqBDPart n, B q := by
  have hD :
      C * (∑ q ∈ dGtBPart n, T q) =
        (∑ q ∈ dGtBPart n, P (q.b : Int) (q.d : Int)) -
          ∑ q ∈ gtPart n, P (q.b : Int) (q.d : Int) := by
    rw [Finset.mul_sum]
    calc
      (∑ q ∈ dGtBPart n, C * T q)
          = ∑ q ∈ dGtBPart n,
              (P (q.b : Int) (q.d : Int) -
                P (q.b : Int) ((q.d - q.b : Nat) : Int)) := by
            apply Finset.sum_congr rfl
            intro q hq
            exact hstepD hq
      _ = _ := by
            rw [Finset.sum_sub_distrib,
              sum_dGtB_P_lower_eq_sum_gtPart_P_general n P]
  have hB :
      C * (∑ q ∈ bGtDPart n, T q) =
        (∑ q ∈ dGtBPart n, P (q.b : Int) (q.d : Int)) -
          ∑ q ∈ gtPart n, P (q.b : Int) (q.d : Int) := by
    rw [Finset.mul_sum]
    calc
      (∑ q ∈ bGtDPart n, C * T q)
          = ∑ q ∈ bGtDPart n,
              (P (q.d : Int) (q.b : Int) -
                P (q.d : Int) ((q.b - q.d : Nat) : Int)) := by
            apply Finset.sum_congr rfl
            intro q hq
            exact hstepB hq
      _ = (∑ q ∈ bGtDPart n, P (q.d : Int) (q.b : Int)) -
            ∑ q ∈ ltPart n, P (q.d : Int) (q.b : Int) := by
            rw [Finset.sum_sub_distrib,
              sum_bGtD_P_lower_eq_sum_ltPart_P_general n P]
      _ = _ := by
            rw [sum_bGtD_Pdb_eq_sum_dGtB_Pbd_general n P,
              sum_ltPart_Pdb_eq_sum_gtPart_Pbd_general n P]
  have hstrict :
      C * ((∑ q ∈ dGtBPart n, T q) +
        ∑ q ∈ bGtDPart n, T q) =
        (∑ q ∈ eqPart n, P (q.b : Int) (q.d : Int)) -
          ∑ q ∈ eqBDPart n, P (q.b : Int) (q.d : Int) := by
    have hboundary :=
      two_mul_strict_bd_P_difference_eq_boundary_P_difference_general
        n P hcomm
    linarith
  have heq :
      C * (∑ q ∈ eqBDPart n, T q) =
        (∑ q ∈ eqBDPart n, P (q.b : Int) (q.d : Int)) -
          ∑ q ∈ eqBDPart n, B q := by
    rw [Finset.mul_sum]
    calc
      (∑ q ∈ eqBDPart n, C * T q)
          = ∑ q ∈ eqBDPart n, (P (q.b : Int) (q.d : Int) - B q) := by
              apply Finset.sum_congr rfl
              intro q hq
              exact heqBD hq
      _ = _ := by rw [Finset.sum_sub_distrib]
  have hsplit := sum_liouvilleQ_eq_bd_parts n T
  rw [hsplit]
  calc
    C * ((∑ q ∈ eqBDPart n, T q) + (∑ q ∈ dGtBPart n, T q) +
        ∑ q ∈ bGtDPart n, T q)
        = C * (∑ q ∈ eqBDPart n, T q) +
            C * ((∑ q ∈ dGtBPart n, T q) +
              ∑ q ∈ bGtDPart n, T q) := by
          ring
    _ = ((∑ q ∈ eqBDPart n, P (q.b : Int) (q.d : Int)) -
            ∑ q ∈ eqBDPart n, B q) +
          ((∑ q ∈ eqPart n, P (q.b : Int) (q.d : Int)) -
            ∑ q ∈ eqBDPart n, P (q.b : Int) (q.d : Int)) := by
          rw [heq, hstrict]
    _ = (∑ q ∈ eqPart n, P (q.b : Int) (q.d : Int)) -
          ∑ q ∈ eqBDPart n, B q := by
          ring

theorem four_mul_liouvilleB3D3Sum_eq_boundaryP33 (n : Nat) :
    4 * liouvilleB3D3Sum n =
      ∑ q ∈ eqPart n, liouvilleP33 (q.b : Int) (q.d : Int) := by
  unfold liouvilleB3D3Sum
  have h :=
    scaled_sum_liouvilleQ_eq_boundary_general n (4 : Int) liouvilleP33
      weightB3D3 (fun _ => 0) liouvilleP33_comm
      (by
        intro q hq
        have hbd : q.b ≤ q.d := le_of_lt ((mem_dGtBPart_iff n q).mp hq).2
        calc
          (4 : Int) * weightB3D3 q =
              4 * (q.b : Int) ^ 3 * (q.d : Int) ^ 3 := by
                unfold weightB3D3
                ring
          _ = liouvilleP33 (q.b : Int) (q.d : Int) -
              liouvilleP33 (q.b : Int) ((q.d - q.b : Nat) : Int) := by
                rw [Nat.cast_sub hbd]
                exact (liouvilleP33_step_int (q.b : Int) (q.d : Int)).symm)
      (by
        intro q hq
        have hdb : q.d ≤ q.b := le_of_lt ((mem_bGtDPart_iff n q).mp hq).2
        calc
          (4 : Int) * weightB3D3 q =
              4 * (q.d : Int) ^ 3 * (q.b : Int) ^ 3 := by
                unfold weightB3D3
                ring
          _ = liouvilleP33 (q.d : Int) (q.b : Int) -
              liouvilleP33 (q.d : Int) ((q.b - q.d : Nat) : Int) := by
                rw [Nat.cast_sub hdb]
                exact (liouvilleP33_step_int (q.d : Int) (q.b : Int)).symm)
      (by
        intro q hq
        rw [mem_eqBDPart_iff] at hq
        unfold weightB3D3 liouvilleP33
        rw [hq.2]
        ring)
  simpa using h

theorem sum_weightP15T_eq_twelve_BD5_add_fourteen_B3D3 (n : Nat) :
    (∑ q ∈ liouvilleQ n, weightP15T q) =
      12 * liouvilleBD5Sum n + 14 * liouvilleB3D3Sum n := by
  unfold liouvilleBD5Sum liouvilleB3D3Sum weightP15T weightBD5 weightB3D3
  have hswap :
      (∑ q ∈ liouvilleQ n,
        ((swapQuad q).b : Int) * ((swapQuad q).d : Int) ^ 5) =
          ∑ q ∈ liouvilleQ n, (q.b : Int) * (q.d : Int) ^ 5 := by
    simpa [weightBD5] using sum_swap_liouvilleQ n weightBD5
  have hswap' :
      (∑ q ∈ liouvilleQ n, (q.d : Int) * (q.b : Int) ^ 5) =
          ∑ q ∈ liouvilleQ n, (q.b : Int) * (q.d : Int) ^ 5 := by
    simpa [swapQuad, mul_comm, mul_left_comm, mul_assoc] using hswap
  have hswap'' :
      (∑ q ∈ liouvilleQ n, (q.b : Int) ^ 5 * (q.d : Int)) =
          ∑ q ∈ liouvilleQ n, (q.b : Int) * (q.d : Int) ^ 5 := by
    calc
      (∑ q ∈ liouvilleQ n, (q.b : Int) ^ 5 * (q.d : Int))
          = ∑ q ∈ liouvilleQ n, (q.d : Int) * (q.b : Int) ^ 5 := by
              apply Finset.sum_congr rfl
              intro q _
              ring
      _ = ∑ q ∈ liouvilleQ n, (q.b : Int) * (q.d : Int) ^ 5 := hswap'
  calc
    (∑ q ∈ liouvilleQ n,
      (6 * (q.b : Int) ^ 5 * (q.d : Int) +
        14 * (q.b : Int) ^ 3 * (q.d : Int) ^ 3 +
          6 * (q.b : Int) * (q.d : Int) ^ 5))
        = 6 * (∑ q ∈ liouvilleQ n, (q.b : Int) ^ 5 * (q.d : Int)) +
            14 * (∑ q ∈ liouvilleQ n,
              (q.b : Int) ^ 3 * (q.d : Int) ^ 3) +
              6 * (∑ q ∈ liouvilleQ n,
        (q.b : Int) * (q.d : Int) ^ 5) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          simp only [mul_assoc]
    _ = 12 * (∑ q ∈ liouvilleQ n, (q.b : Int) * (q.d : Int) ^ 5) +
          14 * (∑ q ∈ liouvilleQ n,
            (q.b : Int) ^ 3 * (q.d : Int) ^ 3) := by
          rw [hswap'']
          ring

theorem twelve_mul_liouvilleBD5Sum_add_fourteen_mul_liouvilleB3D3Sum_eq_boundaryP15
    (n : Nat) :
    12 * liouvilleBD5Sum n + 14 * liouvilleB3D3Sum n =
      (∑ q ∈ eqPart n, liouvilleP15 (q.b : Int) (q.d : Int)) -
        ∑ q ∈ eqBDPart n, (q.b : Int) ^ 6 := by
  have h :=
    scaled_sum_liouvilleQ_eq_boundary_general n (1 : Int) liouvilleP15
      weightP15T (fun q => (q.b : Int) ^ 6) liouvilleP15_comm
      (by
        intro q hq
        have hbd : q.b ≤ q.d := le_of_lt ((mem_dGtBPart_iff n q).mp hq).2
        calc
          (1 : Int) * weightP15T q =
              6 * (q.b : Int) ^ 5 * (q.d : Int) +
                14 * (q.b : Int) ^ 3 * (q.d : Int) ^ 3 +
                  6 * (q.b : Int) * (q.d : Int) ^ 5 := by
                unfold weightP15T
                ring
          _ = liouvilleP15 (q.b : Int) (q.d : Int) -
              liouvilleP15 (q.b : Int) ((q.d - q.b : Nat) : Int) := by
                rw [Nat.cast_sub hbd]
                exact (liouvilleP15_step_int (q.b : Int) (q.d : Int)).symm)
      (by
        intro q hq
        have hdb : q.d ≤ q.b := le_of_lt ((mem_bGtDPart_iff n q).mp hq).2
        calc
          (1 : Int) * weightP15T q =
              6 * (q.d : Int) ^ 5 * (q.b : Int) +
                14 * (q.d : Int) ^ 3 * (q.b : Int) ^ 3 +
                  6 * (q.d : Int) * (q.b : Int) ^ 5 := by
                unfold weightP15T
                ring
          _ = liouvilleP15 (q.d : Int) (q.b : Int) -
              liouvilleP15 (q.d : Int) ((q.b - q.d : Nat) : Int) := by
                rw [Nat.cast_sub hdb]
                exact (liouvilleP15_step_int (q.d : Int) (q.b : Int)).symm)
      (by
        intro q hq
        rw [mem_eqBDPart_iff] at hq
        rcases q with ⟨a, b, c, d⟩
        simp at hq
        have hbd : b = d := hq.2
        subst d
        unfold weightP15T liouvilleP15
        simp
        ring)
  have hsum := sum_weightP15T_eq_twelve_BD5_add_fourteen_B3D3 n
  calc
    12 * liouvilleBD5Sum n + 14 * liouvilleB3D3Sum n
        = ∑ q ∈ liouvilleQ n, weightP15T q := by rw [hsum]
    _ = (∑ q ∈ eqPart n, liouvilleP15 (q.b : Int) (q.d : Int)) -
          ∑ q ∈ eqBDPart n, (q.b : Int) ^ 6 := by
          simpa using h

theorem eight_mul_liouvilleBD3Sum_eq_boundary (n : Nat) :
    8 * liouvilleBD3Sum n =
      (∑ q ∈ eqPart n, liouvilleP (q.b : Int) (q.d : Int)) -
        ∑ q ∈ eqBDPart n, (q.b : Int) ^ 4 := by
  have hW := four_mul_liouvilleWSum_eq_boundary n
  have hBD := two_mul_liouvilleBD3Sum_eq_liouvilleWSum n
  linarith

/-- The `a = c` boundary sum after telescoping. -/
def eqPartBoundaryActualZ (n : Nat) : Int :=
  ∑ q ∈ eqPart n, liouvilleP (q.b : Int) (q.d : Int)

/-- The `b = d` boundary sum after telescoping. -/
def eqBDPartBoundaryActualZ (n : Nat) : Int :=
  ∑ q ∈ eqBDPart n, (q.b : Int) ^ 4

theorem eight_mul_liouvilleBD3Sum_eq_boundary_actual (n : Nat) :
    8 * liouvilleBD3Sum n =
      eqPartBoundaryActualZ n - eqBDPartBoundaryActualZ n := by
  unfold eqPartBoundaryActualZ eqBDPartBoundaryActualZ
  exact eight_mul_liouvilleBD3Sum_eq_boundary n

/-- Parameters `(x,y)` with `x | n` and `1 ≤ y < n / x`.  This single
parameter set is used for both boundaries: for `a = c`, `x = a, y = b`; for
`b = d`, `x = b, y = a`. -/
def boundaryParam (n : Nat) : Finset (Nat × Nat) :=
  ((Finset.Icc 1 n).product (Finset.Icc 1 n)).filter fun p =>
    p.1 ∣ n ∧ p.2 < n / p.1

/-- Sum over `boundaryParam` for the `a = c` boundary. -/
def eqPartBoundaryParamSumZ (n : Nat) : Int :=
  ∑ p ∈ boundaryParam n,
    liouvilleP (p.2 : Int) ((n / p.1 - p.2 : Nat) : Int)

/-- Sum over `boundaryParam` for the `b = d` boundary. -/
def eqBDPartBoundaryParamSumZ (n : Nat) : Int :=
  ∑ p ∈ boundaryParam n, (p.1 : Int) ^ 4

def eqPartParamToQuad (n : Nat) (p : Nat × Nat) : LQuad :=
  { a := p.1, b := p.2, c := p.1, d := n / p.1 - p.2 }

def eqBDPartParamToQuad (n : Nat) (p : Nat × Nat) : LQuad :=
  { a := p.2, b := p.1, c := n / p.1 - p.2, d := p.1 }

theorem eqPartParamToQuad_mem_eqPart {n : Nat} {p : Nat × Nat}
    (hp : p ∈ boundaryParam n) :
    eqPartParamToQuad n p ∈ eqPart n := by
  rcases p with ⟨a, b⟩
  rw [boundaryParam, Finset.mem_filter] at hp
  rcases hp with ⟨hpProd, hdiv, hbLt⟩
  have hpProd' := Finset.mem_product.mp hpProd
  rcases hpProd' with ⟨haMem, hbMem⟩
  have ha := Finset.mem_Icc.mp haMem
  have hb := Finset.mem_Icc.mp hbMem
  have hbLe : b ≤ n / a := le_of_lt hbLt
  have hdPos : 1 ≤ n / a - b := Nat.succ_le_iff.mpr (Nat.sub_pos_of_lt hbLt)
  have hdLe : n / a - b ≤ n := le_trans (Nat.sub_le (n / a) b) (Nat.div_le_self n a)
  have hsum : a * b + a * (n / a - b) = n := by
    rw [← Nat.mul_add, Nat.add_sub_of_le hbLe, Nat.mul_comm, Nat.div_mul_cancel hdiv]
  rw [mem_eqPart_iff, mem_liouvilleQ_iff]
  exact ⟨⟨ha.1, ha.2, hb.1, hb.2, ha.1, ha.2, hdPos, hdLe, hsum⟩, rfl⟩

theorem eqBDPartParamToQuad_mem_eqBDPart {n : Nat} {p : Nat × Nat}
    (hp : p ∈ boundaryParam n) :
    eqBDPartParamToQuad n p ∈ eqBDPart n := by
  rcases p with ⟨b, a⟩
  rw [boundaryParam, Finset.mem_filter] at hp
  rcases hp with ⟨hpProd, hdiv, haLt⟩
  have hpProd' := Finset.mem_product.mp hpProd
  rcases hpProd' with ⟨hbMem, haMem⟩
  have hb := Finset.mem_Icc.mp hbMem
  have ha := Finset.mem_Icc.mp haMem
  have haLe : a ≤ n / b := le_of_lt haLt
  have hcPos : 1 ≤ n / b - a := Nat.succ_le_iff.mpr (Nat.sub_pos_of_lt haLt)
  have hcLe : n / b - a ≤ n := le_trans (Nat.sub_le (n / b) a) (Nat.div_le_self n b)
  have hmulLe : a * b ≤ (n / b) * b := Nat.mul_le_mul_right b haLe
  have hsum : a * b + (n / b - a) * b = n := by
    rw [← Nat.add_mul, Nat.add_sub_of_le haLe, Nat.div_mul_cancel hdiv]
  rw [mem_eqBDPart_iff, mem_liouvilleQ_iff]
  exact ⟨⟨ha.1, ha.2, hb.1, hb.2, hcPos, hcLe, hb.1, hb.2, hsum⟩, rfl⟩

theorem eqPart_quad_param_mem_boundaryParam {n : Nat} {q : LQuad}
    (hq : q ∈ eqPart n) :
    (q.a, q.b) ∈ boundaryParam n := by
  have hqPart := (mem_eqPart_iff n q).mp hq
  have hqQ := (mem_liouvilleQ_iff n q).mp hqPart.1
  rcases hqQ with ⟨ha1, han, hb1, hbn, _hc1, _hcn, hd1, _hdn, _hsum⟩
  have hmul : q.a * (q.b + q.d) = n := eqPart_mul_add_eq hq
  have hdiv : q.a ∣ n := ⟨q.b + q.d, hmul.symm⟩
  have hdivValue : n / q.a = q.b + q.d := by
    rw [← hmul]
    exact Nat.mul_div_cancel_left (q.b + q.d) ha1
  have hbLt : q.b < n / q.a := by
    rw [hdivValue]
    omega
  rw [boundaryParam, Finset.mem_filter]
  exact ⟨Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨ha1, han⟩,
    Finset.mem_Icc.mpr ⟨hb1, hbn⟩⟩, hdiv, hbLt⟩

theorem eqBDPart_quad_param_mem_boundaryParam {n : Nat} {q : LQuad}
    (hq : q ∈ eqBDPart n) :
    (q.b, q.a) ∈ boundaryParam n := by
  have hqPart := (mem_eqBDPart_iff n q).mp hq
  have hqQ := (mem_liouvilleQ_iff n q).mp hqPart.1
  rcases hqQ with ⟨ha1, han, hb1, hbn, hc1, _hcn, _hd1, _hdn, _hsum⟩
  have hmul : (q.a + q.c) * q.b = n := eqBDPart_add_mul_eq hq
  have hdiv : q.b ∣ n := ⟨q.a + q.c, by
    rw [Nat.mul_comm]
    exact hmul.symm⟩
  have hdivValue : n / q.b = q.a + q.c := by
    rw [← hmul, Nat.mul_comm (q.a + q.c) q.b]
    exact Nat.mul_div_cancel_left (q.a + q.c) hb1
  have haLt : q.a < n / q.b := by
    rw [hdivValue]
    omega
  rw [boundaryParam, Finset.mem_filter]
  exact ⟨Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hb1, hbn⟩,
    Finset.mem_Icc.mpr ⟨ha1, han⟩⟩, hdiv, haLt⟩

theorem eqPartParamToQuad_of_quad {n : Nat} {q : LQuad}
    (hq : q ∈ eqPart n) :
    eqPartParamToQuad n (q.a, q.b) = q := by
  have hqPart := (mem_eqPart_iff n q).mp hq
  have hqQ := (mem_liouvilleQ_iff n q).mp hqPart.1
  rcases hqQ with ⟨ha1, _han, _hb1, _hbn, _hc1, _hcn, hd1, _hdn, _hsum⟩
  have hmul : q.a * (q.b + q.d) = n := eqPart_mul_add_eq hq
  have hdivValue : n / q.a = q.b + q.d := by
    rw [← hmul]
    exact Nat.mul_div_cancel_left (q.b + q.d) ha1
  ext <;> simp [eqPartParamToQuad]
  · exact hqPart.2
  · rw [hdivValue]
    omega

theorem eqBDPartParamToQuad_of_quad {n : Nat} {q : LQuad}
    (hq : q ∈ eqBDPart n) :
    eqBDPartParamToQuad n (q.b, q.a) = q := by
  have hqPart := (mem_eqBDPart_iff n q).mp hq
  have hqQ := (mem_liouvilleQ_iff n q).mp hqPart.1
  rcases hqQ with ⟨_ha1, _han, hb1, _hbn, hc1, _hcn, _hd1, _hdn, _hsum⟩
  have hmul : (q.a + q.c) * q.b = n := eqBDPart_add_mul_eq hq
  have hdivValue : n / q.b = q.a + q.c := by
    rw [← hmul, Nat.mul_comm (q.a + q.c) q.b]
    exact Nat.mul_div_cancel_left (q.a + q.c) hb1
  ext <;> simp [eqBDPartParamToQuad]
  · rw [hdivValue]
    omega
  · exact hqPart.2

theorem eqPartBoundaryParamSumZ_eq_actual (n : Nat) :
    eqPartBoundaryParamSumZ n = eqPartBoundaryActualZ n := by
  unfold eqPartBoundaryParamSumZ eqPartBoundaryActualZ
  refine Finset.sum_bij' (fun p _ => eqPartParamToQuad n p)
    (fun q _ => (q.a, q.b)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    exact eqPartParamToQuad_mem_eqPart hp
  · intro q hq
    exact eqPart_quad_param_mem_boundaryParam hq
  · intro p hp
    rcases p with ⟨a, b⟩
    rfl
  · intro q hq
    exact eqPartParamToQuad_of_quad hq
  · intro p hp
    rcases p with ⟨a, b⟩
    rfl

theorem eqBDPartBoundaryParamSumZ_eq_actual (n : Nat) :
    eqBDPartBoundaryParamSumZ n = eqBDPartBoundaryActualZ n := by
  unfold eqBDPartBoundaryParamSumZ eqBDPartBoundaryActualZ
  refine Finset.sum_bij' (fun p _ => eqBDPartParamToQuad n p)
    (fun q _ => (q.b, q.a)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    exact eqBDPartParamToQuad_mem_eqBDPart hp
  · intro q hq
    exact eqBDPart_quad_param_mem_boundaryParam hq
  · intro p hp
    rcases p with ⟨b, a⟩
    rfl
  · intro q hq
    exact eqBDPartParamToQuad_of_quad hq
  · intro p hp
    rcases p with ⟨b, a⟩
    rfl

def eqPartBoundaryActualWithZ (P : Int → Int → Int) (n : Nat) : Int :=
  ∑ q ∈ eqPart n, P (q.b : Int) (q.d : Int)

def eqPartBoundaryParamSumWithZ (P : Int → Int → Int) (n : Nat) : Int :=
  ∑ p ∈ boundaryParam n, P (p.2 : Int) ((n / p.1 - p.2 : Nat) : Int)

def eqPartBoundaryDivisorSumWithZ (P : Int → Int → Int) (n : Nat) : Int :=
  ∑ a ∈ Finset.Icc 1 n,
    if a ∣ n then
      ∑ b ∈ Finset.Icc 1 (n / a - 1),
        P (b : Int) ((n / a - b : Nat) : Int)
    else 0

theorem eqPartBoundaryParamSumWithZ_eq_actual
    (P : Int → Int → Int) (n : Nat) :
    eqPartBoundaryParamSumWithZ P n = eqPartBoundaryActualWithZ P n := by
  unfold eqPartBoundaryParamSumWithZ eqPartBoundaryActualWithZ
  refine Finset.sum_bij' (fun p _ => eqPartParamToQuad n p)
    (fun q _ => (q.a, q.b)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    exact eqPartParamToQuad_mem_eqPart hp
  · intro q hq
    exact eqPart_quad_param_mem_boundaryParam hq
  · intro p hp
    rcases p with ⟨a, b⟩
    rfl
  · intro q hq
    exact eqPartParamToQuad_of_quad hq
  · intro p hp
    rcases p with ⟨a, b⟩
    rfl

theorem sum_Icc_one_if_lt_eq_sum_Icc_pred (N m : Nat) (F : Nat → Int)
    (hmN : m - 1 ≤ N) :
    (∑ b ∈ Finset.Icc 1 N, if b < m then F b else 0) =
      ∑ b ∈ Finset.Icc 1 (m - 1), F b := by
  have hsub : Finset.Icc 1 (m - 1) ⊆ Finset.Icc 1 N := by
    intro b hb
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hb).1,
      le_trans (Finset.mem_Icc.mp hb).2 hmN⟩
  calc
    (∑ b ∈ Finset.Icc 1 N, if b < m then F b else 0)
        = ∑ b ∈ Finset.Icc 1 (m - 1), if b < m then F b else 0 := by
          exact (Finset.sum_subset hsub (by
            intro b hbN hbNotSmall
            by_cases hb_lt : b < m
            · have hbSmall : b ∈ Finset.Icc 1 (m - 1) := by
                exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hbN).1, by omega⟩
              exact False.elim (hbNotSmall hbSmall)
            · simp [hb_lt])).symm
    _ = ∑ b ∈ Finset.Icc 1 (m - 1), F b := by
          apply Finset.sum_congr rfl
          intro b hb
          have hb_lt : b < m := by
            have hb' := Finset.mem_Icc.mp hb
            omega
          simp [hb_lt]

theorem Icc_one_sub_one_eq_Ico_one (m : Nat) :
    Finset.Icc 1 (m - 1) = Finset.Ico 1 m := by
  ext b
  simp
  omega

theorem eqPartBoundaryParamSumWithZ_eq_divisor
    (P : Int → Int → Int) (n : Nat) :
    eqPartBoundaryParamSumWithZ P n = eqPartBoundaryDivisorSumWithZ P n := by
  unfold eqPartBoundaryParamSumWithZ boundaryParam
  rw [Finset.sum_filter]
  rw [show
      (∑ p ∈ (Finset.Icc 1 n).product (Finset.Icc 1 n),
        if p.1 ∣ n ∧ p.2 < n / p.1 then
          P (p.2 : Int) ((n / p.1 - p.2 : Nat) : Int)
        else 0) =
        ∑ a ∈ Finset.Icc 1 n, ∑ b ∈ Finset.Icc 1 n,
          if a ∣ n ∧ b < n / a then
            P (b : Int) ((n / a - b : Nat) : Int)
          else 0 from by
        simpa using (Finset.sum_product (Finset.Icc 1 n) (Finset.Icc 1 n)
          (fun p : Nat × Nat =>
            if p.1 ∣ n ∧ p.2 < n / p.1 then
              P (p.2 : Int) ((n / p.1 - p.2 : Nat) : Int)
            else 0))]
  unfold eqPartBoundaryDivisorSumWithZ
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hdiv : a ∣ n
  · simp [hdiv]
    exact sum_Icc_one_if_lt_eq_sum_Icc_pred n (n / a)
      (fun b => P (b : Int) ((n / a - b : Nat) : Int))
      (le_trans (Nat.sub_le (n / a) 1) (Nat.div_le_self n a))
  · simp [hdiv]

theorem eqPartBoundaryActualWithZ_eq_divisor
    (P : Int → Int → Int) (n : Nat) :
    eqPartBoundaryActualWithZ P n = eqPartBoundaryDivisorSumWithZ P n := by
  rw [← eqPartBoundaryParamSumWithZ_eq_actual P n]
  exact eqPartBoundaryParamSumWithZ_eq_divisor P n

def eqBDPartBoundaryActualWithZ (F : Nat → Int) (n : Nat) : Int :=
  ∑ q ∈ eqBDPart n, F q.b

def eqBDPartBoundaryParamSumWithZ (F : Nat → Int) (n : Nat) : Int :=
  ∑ p ∈ boundaryParam n, F p.1

def eqBDPartBoundaryDivisorSumWithZ (F : Nat → Int) (n : Nat) : Int :=
  ∑ b ∈ Finset.Icc 1 n,
    if b ∣ n then
      ∑ _a ∈ Finset.Icc 1 (n / b - 1), F b
    else 0

theorem eqBDPartBoundaryParamSumWithZ_eq_actual
    (F : Nat → Int) (n : Nat) :
    eqBDPartBoundaryParamSumWithZ F n = eqBDPartBoundaryActualWithZ F n := by
  unfold eqBDPartBoundaryParamSumWithZ eqBDPartBoundaryActualWithZ
  refine Finset.sum_bij' (fun p _ => eqBDPartParamToQuad n p)
    (fun q _ => (q.b, q.a)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    exact eqBDPartParamToQuad_mem_eqBDPart hp
  · intro q hq
    exact eqBDPart_quad_param_mem_boundaryParam hq
  · intro p hp
    rcases p with ⟨b, a⟩
    rfl
  · intro q hq
    exact eqBDPartParamToQuad_of_quad hq
  · intro p hp
    rcases p with ⟨b, a⟩
    rfl

theorem eqBDPartBoundaryParamSumWithZ_eq_divisor
    (F : Nat → Int) (n : Nat) :
    eqBDPartBoundaryParamSumWithZ F n = eqBDPartBoundaryDivisorSumWithZ F n := by
  unfold eqBDPartBoundaryParamSumWithZ boundaryParam
  rw [Finset.sum_filter]
  rw [show
      (∑ p ∈ (Finset.Icc 1 n).product (Finset.Icc 1 n),
        if p.1 ∣ n ∧ p.2 < n / p.1 then F p.1 else 0) =
        ∑ b ∈ Finset.Icc 1 n, ∑ a ∈ Finset.Icc 1 n,
          if b ∣ n ∧ a < n / b then F b else 0 from by
        simpa using (Finset.sum_product (Finset.Icc 1 n) (Finset.Icc 1 n)
          (fun p : Nat × Nat =>
            if p.1 ∣ n ∧ p.2 < n / p.1 then F p.1 else 0))]
  unfold eqBDPartBoundaryDivisorSumWithZ
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hdiv : b ∣ n
  · rw [if_pos hdiv]
    simp only [hdiv, true_and]
    exact sum_Icc_one_if_lt_eq_sum_Icc_pred n (n / b) (fun _a => F b)
      (le_trans (Nat.sub_le (n / b) 1) (Nat.div_le_self n b))
  · rw [if_neg hdiv]
    simp [hdiv]

theorem eqBDPartBoundaryActualWithZ_eq_divisor
    (F : Nat → Int) (n : Nat) :
    eqBDPartBoundaryActualWithZ F n = eqBDPartBoundaryDivisorSumWithZ F n := by
  rw [← eqBDPartBoundaryParamSumWithZ_eq_actual F n]
  exact eqBDPartBoundaryParamSumWithZ_eq_divisor F n

theorem eqBDPartBoundaryPowSix_eq_sigma (n : Nat) :
    eqBDPartBoundaryActualWithZ (fun b => (b : Int) ^ 6) n =
      (n : Int) * sigmaPowZ 5 n - sigmaPowZ 6 n := by
  rw [eqBDPartBoundaryActualWithZ_eq_divisor]
  unfold eqBDPartBoundaryDivisorSumWithZ sigmaPowZ Nat.divisorSum
  rw [Nat.cast_sum, Nat.cast_sum]
  simp_rw [Nat.cast_ite, Nat.cast_pow]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  have hb1 : 1 ≤ b := (Finset.mem_Icc.mp hb).1
  have hb0 : 0 < b := hb1
  have hbn : b ≤ n := (Finset.mem_Icc.mp hb).2
  by_cases hdiv : b ∣ n
  · rw [if_pos hdiv, if_pos hdiv, if_pos hdiv]
    simp [Finset.sum_const, Nat.card_Icc]
    have hdivpos : 1 ≤ n / b := Nat.div_pos hbn hb0
    rw [Nat.cast_sub hdivpos]
    have hmul : (n : Int) = ((n / b : Nat) : Int) * (b : Int) := by
      rw [← Nat.cast_mul, Nat.div_mul_cancel hdiv]
    rw [hmul]
    ring
  · rw [if_neg hdiv, if_neg hdiv, if_neg hdiv]
    simp

/-- Divisor-parametrized form of the `a = c` boundary:
for each divisor `a | n`, write `m = n / a` and sum over
`b = 1, ..., m - 1` with `d = m - b`. -/
def eqPartBoundaryDivisorSumZ (n : Nat) : Int :=
  ∑ a ∈ Finset.Icc 1 n,
    if a ∣ n then
      ∑ b ∈ Finset.Icc 1 (n / a - 1),
        liouvilleP (b : Int) ((n / a - b : Nat) : Int)
    else 0

/-- Divisor-parametrized form of the `b = d` boundary.  Notice the
multiplicity `n / b - 1`: for fixed `b`, the positive pairs `(a,c)` with
`(a+c) * b = n` are `a = 1, ..., n / b - 1`. -/
def eqBDPartBoundaryDivisorSumZ (n : Nat) : Int :=
  ∑ b ∈ Finset.Icc 1 n,
    if b ∣ n then
      ∑ _a ∈ Finset.Icc 1 (n / b - 1), (b : Int) ^ 4
    else 0

/-- The collapsed `b = d` boundary divisor sum. -/
def eqBDPartBoundaryCollapsedSumZ (n : Nat) : Int :=
  ∑ b ∈ Finset.Icc 1 n,
    if b ∣ n then ((n / b - 1 : Nat) : Int) * (b : Int) ^ 4 else 0

theorem eqPartBoundaryParamSumZ_eq_divisor (n : Nat) :
    eqPartBoundaryParamSumZ n = eqPartBoundaryDivisorSumZ n := by
  unfold eqPartBoundaryParamSumZ boundaryParam
  rw [Finset.sum_filter]
  rw [show
      (∑ p ∈ (Finset.Icc 1 n).product (Finset.Icc 1 n),
        if p.1 ∣ n ∧ p.2 < n / p.1 then
          liouvilleP (p.2 : Int) ((n / p.1 - p.2 : Nat) : Int)
        else 0) =
        ∑ a ∈ Finset.Icc 1 n, ∑ b ∈ Finset.Icc 1 n,
          if a ∣ n ∧ b < n / a then
            liouvilleP (b : Int) ((n / a - b : Nat) : Int)
          else 0 from by
        simpa using (Finset.sum_product (Finset.Icc 1 n) (Finset.Icc 1 n)
          (fun p : Nat × Nat =>
            if p.1 ∣ n ∧ p.2 < n / p.1 then
              liouvilleP (p.2 : Int) ((n / p.1 - p.2 : Nat) : Int)
            else 0))]
  unfold eqPartBoundaryDivisorSumZ
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hdiv : a ∣ n
  · simp [hdiv]
    exact sum_Icc_one_if_lt_eq_sum_Icc_pred n (n / a)
      (fun b => liouvilleP (b : Int) ((n / a - b : Nat) : Int))
      (le_trans (Nat.sub_le (n / a) 1) (Nat.div_le_self n a))
  · simp [hdiv]

theorem eqBDPartBoundaryParamSumZ_eq_divisor (n : Nat) :
    eqBDPartBoundaryParamSumZ n = eqBDPartBoundaryDivisorSumZ n := by
  exact eqBDPartBoundaryParamSumWithZ_eq_divisor
    (fun b => (b : Int) ^ 4) n

theorem eqPartBoundaryActualZ_eq_divisor (n : Nat) :
    eqPartBoundaryActualZ n = eqPartBoundaryDivisorSumZ n := by
  rw [← eqPartBoundaryParamSumZ_eq_actual n]
  exact eqPartBoundaryParamSumZ_eq_divisor n

theorem eqBDPartBoundaryActualZ_eq_divisor (n : Nat) :
    eqBDPartBoundaryActualZ n = eqBDPartBoundaryDivisorSumZ n := by
  rw [← eqBDPartBoundaryParamSumZ_eq_actual n]
  exact eqBDPartBoundaryParamSumZ_eq_divisor n

theorem eqBDPartBoundaryDivisorSumZ_eq_collapsed (n : Nat) :
    eqBDPartBoundaryDivisorSumZ n = eqBDPartBoundaryCollapsedSumZ n := by
  unfold eqBDPartBoundaryDivisorSumZ eqBDPartBoundaryCollapsedSumZ
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hdiv : b ∣ n
  · simp [hdiv, Finset.sum_const, Nat.card_Icc]
  · simp [hdiv]

theorem eqBDPartBoundaryCollapsedSumZ_eq_sigma (n : Nat) :
    eqBDPartBoundaryCollapsedSumZ n =
      (n : Int) * sigmaPowZ 3 n - sigmaPowZ 4 n := by
  unfold eqBDPartBoundaryCollapsedSumZ sigmaPowZ Nat.divisorSum
  rw [Nat.cast_sum, Nat.cast_sum]
  simp_rw [Nat.cast_ite, Nat.cast_pow]
  rw [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  have hb1 : 1 ≤ b := (Finset.mem_Icc.mp hb).1
  have hb0 : 0 < b := hb1
  have hbn : b ≤ n := (Finset.mem_Icc.mp hb).2
  by_cases hdiv : b ∣ n
  · rw [if_pos hdiv, if_pos hdiv, if_pos hdiv]
    have hdivpos : 1 ≤ n / b := Nat.div_pos hbn hb0
    rw [Nat.cast_sub hdivpos]
    have hmul : (n : Int) = ((n / b : Nat) : Int) * (b : Int) := by
      rw [← Nat.cast_mul, Nat.div_mul_cancel hdiv]
    rw [hmul]
    ring
  · rw [if_neg hdiv, if_neg hdiv, if_neg hdiv]
    ring

theorem eqBDPartBoundaryDivisorSumZ_eq_sigma (n : Nat) :
    eqBDPartBoundaryDivisorSumZ n =
      (n : Int) * sigmaPowZ 3 n - sigmaPowZ 4 n := by
  rw [eqBDPartBoundaryDivisorSumZ_eq_collapsed,
    eqBDPartBoundaryCollapsedSumZ_eq_sigma]

theorem liouvilleP_b_m_sub_b_eq_poly (m b : Nat) (hb : b ≤ m) :
    liouvilleP (b : Int) ((m - b : Nat) : Int) =
      ((b : Int) ^ 2 - (b : Int) * (m : Int) + (m : Int) ^ 2) ^ 2 := by
  rw [Nat.cast_sub hb]
  unfold liouvilleP
  ring

/-- The same `a = c` boundary, with the inner summand expanded to the
Faulhaber-ready polynomial in `b` and `m = n / a`. -/
def eqPartBoundaryPolynomialSumZ (n : Nat) : Int :=
  ∑ a ∈ Finset.Icc 1 n,
    if a ∣ n then
      let m := n / a
      ∑ b ∈ Finset.Icc 1 (m - 1),
        ((b : Int) ^ 2 - (b : Int) * (m : Int) + (m : Int) ^ 2) ^ 2
    else 0

theorem eqPartBoundaryDivisorSumZ_eq_polynomial (n : Nat) :
    eqPartBoundaryDivisorSumZ n = eqPartBoundaryPolynomialSumZ n := by
  unfold eqPartBoundaryDivisorSumZ eqPartBoundaryPolynomialSumZ
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hdiv : a ∣ n
  · simp [hdiv]
    apply Finset.sum_congr rfl
    intro b hb
    have hb_le : b ≤ n / a := by
      have hb' := (Finset.mem_Icc.mp hb).2
      exact le_trans hb' (Nat.sub_le (n / a) 1)
    exact liouvilleP_b_m_sub_b_eq_poly (n / a) b hb_le
  · simp [hdiv]

/-- Closed numerator for the Faulhaber evaluation of the `a = c` inner sum:
`30 * sum_{b=1}^{m-1} (b^2 - bm + m^2)^2`. -/
def eqPartInnerClosedNumeratorZ (m : Nat) : Int :=
  (m : Int) * ((m - 1 : Nat) : Int) *
    (21 * (m : Int) ^ 3 - 9 * (m : Int) ^ 2 + (m : Int) + 1)

def eqPartInnerPolynomialSumZ (m : Nat) : Int :=
  ∑ b ∈ Finset.Icc 1 (m - 1),
    ((b : Int) ^ 2 - (b : Int) * (m : Int) + (m : Int) ^ 2) ^ 2

theorem thirty_mul_eqPartBoundaryDivisorSumZ_eq_sigma (n : Nat) :
    (30 : Int) * eqPartBoundaryDivisorSumZ n =
      21 * sigmaPowZ 5 n - 30 * sigmaPowZ 4 n +
        10 * sigmaPowZ 3 n - sigmaPowZ 1 n := by
  unfold eqPartBoundaryDivisorSumZ
  rw [Finset.mul_sum]
  calc
    (∑ a ∈ Finset.Icc 1 n,
      30 * if a ∣ n then
        ∑ b ∈ Finset.Icc 1 (n / a - 1),
          liouvilleP (b : Int) ((n / a - b : Nat) : Int)
      else 0)
        = ∑ a ∈ Finset.Icc 1 n,
            if a ∣ n then
              21 * ((n / a : Nat) : Int) ^ 5 -
                30 * ((n / a : Nat) : Int) ^ 4 +
                10 * ((n / a : Nat) : Int) ^ 3 - ((n / a : Nat) : Int)
            else 0 := by
          apply Finset.sum_congr rfl
          intro a _
          by_cases hdiv : a ∣ n
          · simp [hdiv]
            rw [Icc_one_sub_one_eq_Ico_one]
            exact thirty_mul_sum_liouvilleP_antidiagonal (n / a)
          · simp [hdiv]
    _ = 21 * sigmaPowZ 5 n - 30 * sigmaPowZ 4 n +
        10 * sigmaPowZ 3 n - sigmaPowZ 1 n := by
          rw [← divisorQuotPowSumZ_eq_sigmaPowZ 5 n,
            ← divisorQuotPowSumZ_eq_sigmaPowZ 4 n,
            ← divisorQuotPowSumZ_eq_sigmaPowZ 3 n,
            ← divisorQuotPowSumZ_eq_sigmaPowZ 1 n]
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          rw [← Finset.sum_sub_distrib]
          rw [← Finset.sum_add_distrib]
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro a _
          by_cases hdiv : a ∣ n <;> simp [hdiv]

theorem thirty_mul_eqPartBoundaryP33DivisorSum_eq_sigma (n : Nat) :
    (30 : Int) * eqPartBoundaryDivisorSumWithZ liouvilleP33 n =
      sigmaPowZ 7 n - sigmaPowZ 3 n := by
  unfold eqPartBoundaryDivisorSumWithZ
  rw [Finset.mul_sum]
  calc
    (∑ a ∈ Finset.Icc 1 n,
      30 * if a ∣ n then
        ∑ b ∈ Finset.Icc 1 (n / a - 1),
          liouvilleP33 (b : Int) ((n / a - b : Nat) : Int)
      else 0)
        = ∑ a ∈ Finset.Icc 1 n,
            if a ∣ n then
              ((n / a : Nat) : Int) ^ 7 - ((n / a : Nat) : Int) ^ 3
            else 0 := by
          apply Finset.sum_congr rfl
          intro a _
          by_cases hdiv : a ∣ n
          · simp [hdiv]
            rw [Icc_one_sub_one_eq_Ico_one]
            exact thirty_mul_sum_liouvilleP33_antidiagonal (n / a)
          · simp [hdiv]
    _ = sigmaPowZ 7 n - sigmaPowZ 3 n := by
          rw [← divisorQuotPowSumZ_eq_sigmaPowZ 7 n,
            ← divisorQuotPowSumZ_eq_sigmaPowZ 3 n]
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro a _
          by_cases hdiv : a ∣ n <;> simp [hdiv]

theorem thirty_mul_eqPartBoundaryP33Actual_eq_sigma (n : Nat) :
    (30 : Int) * eqPartBoundaryActualWithZ liouvilleP33 n =
      sigmaPowZ 7 n - sigmaPowZ 3 n := by
  rw [← eqPartBoundaryParamSumWithZ_eq_actual liouvilleP33 n,
    eqPartBoundaryParamSumWithZ_eq_divisor]
  exact thirty_mul_eqPartBoundaryP33DivisorSum_eq_sigma n

theorem one_twenty_mul_liouvilleB3D3Sum_eq_sigma7_sub_sigma3 (n : Nat) :
    (120 : Int) * liouvilleB3D3Sum n = sigmaPowZ 7 n - sigmaPowZ 3 n := by
  have h4 := four_mul_liouvilleB3D3Sum_eq_boundaryP33 n
  have h30 := thirty_mul_eqPartBoundaryP33Actual_eq_sigma n
  calc
    (120 : Int) * liouvilleB3D3Sum n =
        30 * (4 * liouvilleB3D3Sum n) := by
          ring
    _ = 30 * (∑ q ∈ eqPart n, liouvilleP33 (q.b : Int) (q.d : Int)) := by
          rw [h4]
    _ = sigmaPowZ 7 n - sigmaPowZ 3 n := by
          simpa [eqPartBoundaryActualWithZ] using h30

theorem one_twenty_mul_sigma3Sigma3ConvZ_eq_sigma7_sub_sigma3 (n : Nat) :
    (120 : Int) * sigmaSigmaConvZ 3 3 n = sigmaPowZ 7 n - sigmaPowZ 3 n := by
  rw [sigma3Sigma3ConvZ_eq_liouvilleB3D3Sum]
  exact one_twenty_mul_liouvilleB3D3Sum_eq_sigma7_sub_sigma3 n

theorem eqPartBoundaryComboP15P33_eq_sigma (n : Nat) :
    (1008 : Int) * eqPartBoundaryActualWithZ liouvilleP15 n -
      17928 * eqPartBoundaryActualWithZ liouvilleP33 n =
        24 * sigmaPowZ 1 n + 480 * sigmaPowZ 3 n +
          504 * sigmaPowZ 5 n - 1008 * sigmaPowZ 6 n := by
  rw [eqPartBoundaryActualWithZ_eq_divisor,
    eqPartBoundaryActualWithZ_eq_divisor]
  unfold eqPartBoundaryDivisorSumWithZ
  calc
    (1008 : Int) *
        (∑ a ∈ Finset.Icc 1 n,
          if a ∣ n then
            ∑ b ∈ Finset.Icc 1 (n / a - 1),
              liouvilleP15 (b : Int) ((n / a - b : Nat) : Int)
          else 0) -
      17928 *
        (∑ a ∈ Finset.Icc 1 n,
          if a ∣ n then
            ∑ b ∈ Finset.Icc 1 (n / a - 1),
              liouvilleP33 (b : Int) ((n / a - b : Nat) : Int)
          else 0)
        = ∑ a ∈ Finset.Icc 1 n,
            if a ∣ n then
              24 * ((n / a : Nat) : Int) +
                480 * ((n / a : Nat) : Int) ^ 3 +
                504 * ((n / a : Nat) : Int) ^ 5 -
                1008 * ((n / a : Nat) : Int) ^ 6
            else 0 := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro a _
          by_cases hdiv : a ∣ n
          · simp [hdiv]
            rw [Icc_one_sub_one_eq_Ico_one]
            calc
              1008 *
                  (∑ b ∈ Finset.Ico 1 (n / a),
                    liouvilleP15 (b : Int) ((n / a - b : Nat) : Int)) -
                17928 *
                  (∑ b ∈ Finset.Ico 1 (n / a),
                    liouvilleP33 (b : Int) ((n / a - b : Nat) : Int))
                  = ∑ b ∈ Finset.Ico 1 (n / a),
                      liouvilleP15P33ComboZ (n / a) b := by
                    rw [Finset.mul_sum, Finset.mul_sum,
                      ← Finset.sum_sub_distrib]
                    apply Finset.sum_congr rfl
                    intro b _
                    unfold liouvilleP15P33ComboZ
                    rfl
              _ = 24 * ((n / a : Nat) : Int) +
                    480 * ((n / a : Nat) : Int) ^ 3 +
                    504 * ((n / a : Nat) : Int) ^ 5 -
                    1008 * ((n / a : Nat) : Int) ^ 6 :=
                    sum_liouvilleP15_P33_combo_antidiagonal (n / a)
          · simp [hdiv]
    _ = 24 * sigmaPowZ 1 n + 480 * sigmaPowZ 3 n +
          504 * sigmaPowZ 5 n - 1008 * sigmaPowZ 6 n := by
          rw [← divisorQuotPowSumZ_eq_sigmaPowZ 1 n,
            ← divisorQuotPowSumZ_eq_sigmaPowZ 3 n,
            ← divisorQuotPowSumZ_eq_sigmaPowZ 5 n,
            ← divisorQuotPowSumZ_eq_sigmaPowZ 6 n]
          simp_rw [Nat.cast_pow]
          calc
            (∑ a ∈ Finset.Icc 1 n,
              if a ∣ n then
                24 * ((n / a : Nat) : Int) +
                  480 * ((n / a : Nat) : Int) ^ 3 +
                  504 * ((n / a : Nat) : Int) ^ 5 -
                  1008 * ((n / a : Nat) : Int) ^ 6
              else 0)
                = ∑ a ∈ Finset.Icc 1 n,
                    (24 * (if a ∣ n then ((n / a : Nat) : Int) ^ 1 else 0) +
                      480 * (if a ∣ n then ((n / a : Nat) : Int) ^ 3 else 0) +
                      504 * (if a ∣ n then ((n / a : Nat) : Int) ^ 5 else 0) -
                      1008 * (if a ∣ n then ((n / a : Nat) : Int) ^ 6 else 0)) := by
                  apply Finset.sum_congr rfl
                  intro a _
                  by_cases hdiv : a ∣ n <;> simp [hdiv]
            _ = 24 * (∑ a ∈ Finset.Icc 1 n,
                    if a ∣ n then ((n / a : Nat) : Int) ^ 1 else 0) +
                  480 * (∑ a ∈ Finset.Icc 1 n,
                    if a ∣ n then ((n / a : Nat) : Int) ^ 3 else 0) +
                  504 * (∑ a ∈ Finset.Icc 1 n,
                    if a ∣ n then ((n / a : Nat) : Int) ^ 5 else 0) -
                  1008 * (∑ a ∈ Finset.Icc 1 n,
                    if a ∣ n then ((n / a : Nat) : Int) ^ 6 else 0) := by
                  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
                  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
                    Finset.mul_sum]

theorem boundaryP15P33MinusEqBDPowSix_eq_e6_sigma_rhs (n : Nat) :
    (1008 : Int) *
        ((∑ q ∈ eqPart n, liouvilleP15 (q.b : Int) (q.d : Int)) -
          ∑ q ∈ eqBDPart n, (q.b : Int) ^ 6) -
      17928 * (∑ q ∈ eqPart n, liouvilleP33 (q.b : Int) (q.d : Int)) =
        -1008 * (n : Int) * sigmaPowZ 5 n +
          504 * sigmaPowZ 5 n + 24 * sigmaPowZ 1 n +
            480 * sigmaPowZ 3 n := by
  have heq := eqPartBoundaryComboP15P33_eq_sigma n
  have hbd := eqBDPartBoundaryPowSix_eq_sigma n
  unfold eqPartBoundaryActualWithZ at heq
  unfold eqBDPartBoundaryActualWithZ at hbd
  calc
    (1008 : Int) *
        ((∑ q ∈ eqPart n, liouvilleP15 (q.b : Int) (q.d : Int)) -
          ∑ q ∈ eqBDPart n, (q.b : Int) ^ 6) -
      17928 * (∑ q ∈ eqPart n, liouvilleP33 (q.b : Int) (q.d : Int))
        =
          (1008 * (∑ q ∈ eqPart n,
              liouvilleP15 (q.b : Int) (q.d : Int)) -
            17928 * (∑ q ∈ eqPart n,
              liouvilleP33 (q.b : Int) (q.d : Int))) -
            1008 * (∑ q ∈ eqBDPart n, (q.b : Int) ^ 6) := by
          ring
    _ = (24 * sigmaPowZ 1 n + 480 * sigmaPowZ 3 n +
            504 * sigmaPowZ 5 n - 1008 * sigmaPowZ 6 n) -
          1008 * ((n : Int) * sigmaPowZ 5 n - sigmaPowZ 6 n) := by
          rw [heq, hbd]
    _ = -1008 * (n : Int) * sigmaPowZ 5 n +
          504 * sigmaPowZ 5 n + 24 * sigmaPowZ 1 n +
            480 * sigmaPowZ 3 n := by
          ring

theorem e6_liouville_convolution_identity (n : Nat) :
    (12096 : Int) * liouvilleBD5Sum n -
      57600 * liouvilleB3D3Sum n =
        -1008 * (n : Int) * sigmaPowZ 5 n +
          504 * sigmaPowZ 5 n + 24 * sigmaPowZ 1 n +
            480 * sigmaPowZ 3 n := by
  have h15 :=
    twelve_mul_liouvilleBD5Sum_add_fourteen_mul_liouvilleB3D3Sum_eq_boundaryP15 n
  have h33 := four_mul_liouvilleB3D3Sum_eq_boundaryP33 n
  have hboundary := boundaryP15P33MinusEqBDPowSix_eq_e6_sigma_rhs n
  calc
    (12096 : Int) * liouvilleBD5Sum n - 57600 * liouvilleB3D3Sum n
        = 1008 * (12 * liouvilleBD5Sum n +
            14 * liouvilleB3D3Sum n) -
          17928 * (4 * liouvilleB3D3Sum n) := by
          ring
    _ = 1008 *
          ((∑ q ∈ eqPart n, liouvilleP15 (q.b : Int) (q.d : Int)) -
            ∑ q ∈ eqBDPart n, (q.b : Int) ^ 6) -
          17928 * (∑ q ∈ eqPart n,
            liouvilleP33 (q.b : Int) (q.d : Int)) := by
          rw [h15, h33]
    _ = -1008 * (n : Int) * sigmaPowZ 5 n +
          504 * sigmaPowZ 5 n + 24 * sigmaPowZ 1 n +
            480 * sigmaPowZ 3 n :=
          hboundary

theorem e6_sigma_convolution_identity (n : Nat) :
    (12096 : Int) * sigmaSigmaConvZ 1 5 n -
      57600 * sigmaSigmaConvZ 3 3 n =
        -1008 * (n : Int) * sigmaPowZ 5 n +
          504 * sigmaPowZ 5 n + 24 * sigmaPowZ 1 n +
            480 * sigmaPowZ 3 n := by
  rw [sigma1Sigma5ConvZ_eq_liouvilleBD5Sum,
    sigma3Sigma3ConvZ_eq_liouvilleB3D3Sum]
  exact e6_liouville_convolution_identity n

theorem thirty_mul_boundaryDivisorDifference_eq_lahiri (n : Nat) :
    (30 : Int) * (eqPartBoundaryDivisorSumZ n - eqBDPartBoundaryDivisorSumZ n) =
      21 * sigmaPowZ 5 n + (10 - 30 * (n : Int)) * sigmaPowZ 3 n -
        sigmaPowZ 1 n := by
  have heq := thirty_mul_eqPartBoundaryDivisorSumZ_eq_sigma n
  have hbd := eqBDPartBoundaryDivisorSumZ_eq_sigma n
  calc
    (30 : Int) * (eqPartBoundaryDivisorSumZ n - eqBDPartBoundaryDivisorSumZ n)
        = 30 * eqPartBoundaryDivisorSumZ n -
            30 * eqBDPartBoundaryDivisorSumZ n := by
          ring
    _ = (21 * sigmaPowZ 5 n - 30 * sigmaPowZ 4 n +
            10 * sigmaPowZ 3 n - sigmaPowZ 1 n) -
          30 * ((n : Int) * sigmaPowZ 3 n - sigmaPowZ 4 n) := by
          rw [heq, hbd]
    _ = 21 * sigmaPowZ 5 n + (10 - 30 * (n : Int)) * sigmaPowZ 3 n -
          sigmaPowZ 1 n := by
          ring

theorem thirty_mul_boundaryActualDifference_eq_lahiri (n : Nat) :
    (30 : Int) * (eqPartBoundaryActualZ n - eqBDPartBoundaryActualZ n) =
      21 * sigmaPowZ 5 n + (10 - 30 * (n : Int)) * sigmaPowZ 3 n -
        sigmaPowZ 1 n := by
  calc
    (30 : Int) * (eqPartBoundaryActualZ n - eqBDPartBoundaryActualZ n)
        = 30 * (eqPartBoundaryParamSumZ n - eqBDPartBoundaryParamSumZ n) := by
          rw [eqPartBoundaryParamSumZ_eq_actual, eqBDPartBoundaryParamSumZ_eq_actual]
    _ = 30 * (eqPartBoundaryDivisorSumZ n - eqBDPartBoundaryDivisorSumZ n) := by
          rw [eqPartBoundaryParamSumZ_eq_divisor, eqBDPartBoundaryParamSumZ_eq_divisor]
    _ = 21 * sigmaPowZ 5 n + (10 - 30 * (n : Int)) * sigmaPowZ 3 n -
          sigmaPowZ 1 n :=
          thirty_mul_boundaryDivisorDifference_eq_lahiri n

theorem twoforty_mul_liouvilleBD3Sum_eq_lahiri (n : Nat) :
    (240 : Int) * liouvilleBD3Sum n =
      21 * sigmaPowZ 5 n + (10 - 30 * (n : Int)) * sigmaPowZ 3 n -
        sigmaPowZ 1 n := by
  have h8 := eight_mul_liouvilleBD3Sum_eq_boundary_actual n
  have h30 := thirty_mul_boundaryActualDifference_eq_lahiri n
  calc
    (240 : Int) * liouvilleBD3Sum n = 30 * (8 * liouvilleBD3Sum n) := by
      ring
    _ = 30 * (eqPartBoundaryActualZ n - eqBDPartBoundaryActualZ n) := by
      rw [h8]
    _ = 21 * sigmaPowZ 5 n + (10 - 30 * (n : Int)) * sigmaPowZ 3 n -
        sigmaPowZ 1 n := h30

theorem twoforty_mul_sigma1Sigma3ConvZ_eq_lahiri (n : Nat) :
    (240 : Int) * sigma1Sigma3ConvZ n =
      21 * sigmaPowZ 5 n + (10 - 30 * (n : Int)) * sigmaPowZ 3 n -
        sigmaPowZ 1 n := by
  rw [sigma1Sigma3ConvZ_eq_liouvilleBD3Sum]
  exact twoforty_mul_liouvilleBD3Sum_eq_lahiri n

def boundaryDivisorEvaluationCheck (N : Nat) : Bool :=
  (List.range (N + 1)).all fun n =>
    decide (eqPartBoundaryActualZ n = eqPartBoundaryDivisorSumZ n) &&
    decide (eqBDPartBoundaryActualZ n = eqBDPartBoundaryDivisorSumZ n) &&
    decide (eqBDPartBoundaryDivisorSumZ n = eqBDPartBoundaryCollapsedSumZ n) &&
    decide (eqPartBoundaryDivisorSumZ n = eqPartBoundaryPolynomialSumZ n) &&
    decide (8 * liouvilleBD3Sum n =
      eqPartBoundaryActualZ n - eqBDPartBoundaryActualZ n)

theorem boundaryDivisorEvaluationThrough8Check_true :
    boundaryDivisorEvaluationCheck 8 = true := by
  native_decide

def eqBDPartSigma4ClaimCheck (N : Nat) : Bool :=
  (List.range (N + 1)).all fun n =>
    decide (eqBDPartBoundaryActualZ n = sigmaPowZ 4 n)

theorem eqBDPartSigma4ClaimThrough5Check_false :
    eqBDPartSigma4ClaimCheck 5 = false := by
  native_decide

end Ch20LiouvilleConvolution
end Pending
end QseriesFormalization
