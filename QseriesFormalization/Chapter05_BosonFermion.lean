import QseriesFormalization.Chapter03
import QseriesFormalization.Chapter05

/-!
# Chapter 5 Boson-Fermion partition function

This file adds the Chapter 5 partition-function layer on top of the
`AdmissibleState` setup in `Chapter05.lean`.

The global partition function is the formal/infinite sum over all admissible
states.  The closed proofs below are finite-mode versions: for modes
`0, ..., N - 1`, the state sum factors into the fermionic product over
single-mode occupations, and the same finite sum decomposes by charge sector.

The energy convention is the one already present in `Chapter05.lean`:
mode `n` contributes `n + 1`, avoiding half-powers.
-/

namespace QseriesFormalization
namespace PartI
namespace Ch05

open scoped BigOperators
open Filter
open scoped Topology

/-- Plural alias for the Chapter 5 state space used by the partition function. -/
abbrev AdmissibleStates := AdmissibleState

/-- The monomial attached to a state: `z^charge q^energy`. -/
noncomputable def stateMonomial (q z : ℂ) (S : AdmissibleStates) : ℂ :=
  z ^ charge S * q ^ energy S

/-- The full Boson-Fermion partition function over admissible states. -/
noncomputable def Z (q z : ℂ) : ℂ :=
  ∑' S : AdmissibleStates, stateMonomial q z S

/-- Contribution of occupying a positive mode `n`. -/
noncomputable def addedModeWeight (q z : ℂ) (n : Nat) : ℂ :=
  z * q ^ (n + 1)

/-- Contribution of creating a hole in negative mode `n`. -/
noncomputable def removedModeWeight (q z : ℂ) (n : Nat) : ℂ :=
  z⁻¹ * q ^ (n + 1)

/-- The two fermionic occupation choices at one added mode. -/
noncomputable def addedFermionPartial (N : Nat) (q z : ℂ) : ℂ :=
  ∏ n ∈ Finset.range N, (1 + addedModeWeight q z n)

/-- The two fermionic occupation choices at one removed mode. -/
noncomputable def removedFermionPartial (N : Nat) (q z : ℂ) : ℂ :=
  ∏ n ∈ Finset.range N, (1 + removedModeWeight q z n)

/-- Factorized finite fermionic product, separated into added and removed modes. -/
noncomputable def fermionicProductPartial (N : Nat) (q z : ℂ) : ℂ :=
  addedFermionPartial N q z * removedFermionPartial N q z

/-- The complete one-mode fermionic factor. -/
noncomputable def fermionicModeFactor (q z : ℂ) (n : Nat) : ℂ :=
  (1 + addedModeWeight q z n) * (1 + removedModeWeight q z n)

/-- The same finite fermionic product as a product over modes. -/
noncomputable def fermionicModeProductPartial (N : Nat) (q z : ℂ) : ℂ :=
  ∏ n ∈ Finset.range N, fermionicModeFactor q z n

/-- Infinite fermionic product suggested by the finite-mode evaluation. -/
noncomputable def fermionicProduct (q z : ℂ) : ℂ :=
  ∏' n : Nat, fermionicModeFactor q z n

/-- Euler factor that converts the fermionic partition function to the
Jacobi-type product in the current integer-energy convention. -/
noncomputable def bosonEulerProduct (q : ℂ) : ℂ :=
  ∏' n : Nat, (1 - q ^ (n + 1))

/-- Theta series in the current integer-energy convention. -/
noncomputable def bosonFermionThetaSeries (q z : ℂ) : ℂ :=
  ∑' n : Int, z ^ n * q ^ (n * (n + 1) / 2)

/-- Finite state sum over subsets of the first `N` added and removed modes. -/
noncomputable def finiteZ (N : Nat) (q z : ℂ) : ℂ :=
  ∑ A ∈ (Finset.range N).powerset, ∑ R ∈ (Finset.range N).powerset,
    stateMonomial q z ⟨A, R⟩

/-- A bounded state represented as the pair `(added, removed)`. -/
noncomputable def boundedStatePairs (N : Nat) : Finset (Finset Nat × Finset Nat) :=
  (Finset.range N).powerset.product (Finset.range N).powerset

/-- The bounded pair-state sets are monotone in the cutoff. -/
theorem boundedStatePairs_mono : Monotone boundedStatePairs := by
  intro N M hNM p hp
  rcases p with ⟨A, R⟩
  change (A, R) ∈ (Finset.range N).powerset ×ˢ (Finset.range N).powerset at hp
  change (A, R) ∈ (Finset.range M).powerset ×ˢ (Finset.range M).powerset
  rw [Finset.mem_product, Finset.mem_powerset, Finset.mem_powerset] at hp ⊢
  exact ⟨hp.1.trans (Finset.range_subset_range.mpr hNM),
    hp.2.trans (Finset.range_subset_range.mpr hNM)⟩

/-- The bounded pair-state finsets exhaust all finite pair-states. -/
theorem tendsto_boundedStatePairs_atTop :
    Tendsto boundedStatePairs atTop atTop := by
  refine boundedStatePairs_mono.tendsto_atTop_finset ?_
  intro p
  rcases p with ⟨A, R⟩
  rcases Finset.exists_nat_subset_range A with ⟨NA, hA⟩
  rcases Finset.exists_nat_subset_range R with ⟨NR, hR⟩
  refine ⟨max NA NR, ?_⟩
  change (A, R) ∈ (Finset.range (max NA NR)).powerset ×ˢ
    (Finset.range (max NA NR)).powerset
  rw [Finset.mem_product, Finset.mem_powerset, Finset.mem_powerset]
  exact ⟨hA.trans (Finset.range_subset_range.mpr (le_max_left NA NR)),
    hR.trans (Finset.range_subset_range.mpr (le_max_right NA NR))⟩

/-- Charge of a bounded pair-state. -/
def pairCharge (p : Finset Nat × Finset Nat) : Int :=
  charge ⟨p.1, p.2⟩

/-- Monomial of a bounded pair-state. -/
noncomputable def pairMonomial (q z : ℂ) (p : Finset Nat × Finset Nat) : ℂ :=
  stateMonomial q z ⟨p.1, p.2⟩

/-- The state space is equivalent to pairs of added/removed finite sets. -/
def admissibleStatesEquivPairs : AdmissibleStates ≃ Finset Nat × Finset Nat where
  toFun S := (S.added, S.removed)
  invFun p := ⟨p.1, p.2⟩
  left_inv := by
    intro S
    cases S
    rfl
  right_inv := by
    intro p
    cases p
    rfl

/-- The `Z`-sum can be reindexed as a `tsum` over pair-states. -/
theorem Z_eq_pair_tsum (q z : ℂ) :
    Z q z = ∑' p : Finset Nat × Finset Nat, pairMonomial q z p := by
  simpa [Z, pairMonomial, admissibleStatesEquivPairs] using
    (admissibleStatesEquivPairs.tsum_eq (pairMonomial q z))

/-- Energy-only monomial of a bounded pair-state. -/
noncomputable def pairEnergyMonomial (q : ℂ) (p : Finset Nat × Finset Nat) : ℂ :=
  q ^ energy ⟨p.1, p.2⟩

/-- The finite set of charge values appearing among states bounded by `N`. -/
noncomputable def finiteChargeSpectrum (N : Nat) : Finset Int :=
  (boundedStatePairs N).image pairCharge

/-- Finite charge sector in the bounded state sum. -/
noncomputable def finiteChargeSector (N : Nat) (q z : ℂ) (c : Int) : ℂ :=
  ∑ p ∈ boundedStatePairs N with pairCharge p = c, pairMonomial q z p

/-- Energy generating function inside one finite charge sector. -/
noncomputable def finiteChargeEnergySector (N : Nat) (q : ℂ) (c : Int) : ℂ :=
  ∑ p ∈ boundedStatePairs N with pairCharge p = c, pairEnergyMonomial q p

/-- Infinite charge sector of `Z`, without asserting summability or interchanging sums. -/
noncomputable def chargeSectorZ (q z : ℂ) (c : Int) : ℂ :=
  ∑' S : {S : AdmissibleStates // charge S = c}, stateMonomial q z S.1

/-- Energy-only infinite charge sector. -/
noncomputable def chargeEnergySectorZ (q : ℂ) (c : Int) : ℂ :=
  ∑' S : {S : AdmissibleStates // charge S = c}, q ^ energy S.1

/-- Reindex states by their charge and then by the corresponding charge fiber. -/
def chargeSigmaEquivStates :
    (Sigma fun c : Int => {S : AdmissibleStates // charge S = c}) ≃
      AdmissibleStates where
  toFun x := x.2.1
  invFun S := ⟨charge S, ⟨S, rfl⟩⟩
  left_inv := by
    rintro ⟨c, S, hS⟩
    cases hS
    rfl
  right_inv := by
    intro S
    rfl

/-- In each infinite charge sector, the `z`-power factors out. -/
theorem chargeSectorZ_eq_zpow_mul_chargeEnergySectorZ (q z : ℂ) (c : Int) :
    chargeSectorZ q z c = z ^ c * chargeEnergySectorZ q c := by
  rw [chargeSectorZ, chargeEnergySectorZ, ← tsum_mul_left]
  apply tsum_congr
  intro S
  simp [stateMonomial, S.property]

lemma addedSubsetWeight_eq_zpow_qpow (q z : ℂ) (A : Finset Nat) :
    (∏ n ∈ A, addedModeWeight q z n) =
      z ^ A.card * q ^ A.sum (fun n => n + 1) := by
  simp [addedModeWeight, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.prod_pow_eq_pow_sum]

lemma removedSubsetWeight_eq_zpow_qpow (q z : ℂ) (A : Finset Nat) :
    (∏ n ∈ A, removedModeWeight q z n) =
      (z⁻¹) ^ A.card * q ^ A.sum (fun n => n + 1) := by
  simp [removedModeWeight, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.prod_pow_eq_pow_sum]

/-- The charge/energy monomial equals the product of independent mode weights. -/
theorem stateMonomial_mk_eq_products (q z : ℂ) (hz : z ≠ 0)
    (A R : Finset Nat) :
    stateMonomial q z ⟨A, R⟩ =
      (∏ n ∈ A, addedModeWeight q z n) *
        (∏ n ∈ R, removedModeWeight q z n) := by
  rw [addedSubsetWeight_eq_zpow_qpow, removedSubsetWeight_eq_zpow_qpow]
  unfold stateMonomial charge energy
  rw [pow_add]
  rw [show z ^ ((A.card : Int) - (R.card : Int)) =
      z ^ (A.card : Int) * z ^ (-(R.card : Int)) by
    rw [sub_eq_add_neg]
    exact zpow_add₀ hz (A.card : Int) (-(R.card : Int))]
  rw [zpow_natCast, zpow_neg, zpow_natCast]
  ring

/-- Sum over added-mode subsets equals the added fermionic product. -/
theorem added_powerset_evaluation (N : Nat) (q z : ℂ) :
    (∑ A ∈ (Finset.range N).powerset,
        ∏ n ∈ A, addedModeWeight q z n) =
      addedFermionPartial N q z := by
  simpa [addedFermionPartial] using
    (Finset.prod_one_add (s := Finset.range N) (f := addedModeWeight q z)).symm

/-- Sum over removed-mode subsets equals the removed fermionic product. -/
theorem removed_powerset_evaluation (N : Nat) (q z : ℂ) :
    (∑ A ∈ (Finset.range N).powerset,
        ∏ n ∈ A, removedModeWeight q z n) =
      removedFermionPartial N q z := by
  simpa [removedFermionPartial] using
    (Finset.prod_one_add (s := Finset.range N) (f := removedModeWeight q z)).symm

/-- Finite fermionic evaluation: the bounded state sum factors by occupation modes. -/
theorem finiteZ_eq_fermionicProductPartial (N : Nat) (q z : ℂ) (hz : z ≠ 0) :
    finiteZ N q z = fermionicProductPartial N q z := by
  unfold finiteZ fermionicProductPartial
  simp_rw [stateMonomial_mk_eq_products q z hz]
  calc
    (∑ A ∈ (Finset.range N).powerset,
        ∑ R ∈ (Finset.range N).powerset,
          (∏ n ∈ A, addedModeWeight q z n) *
            (∏ n ∈ R, removedModeWeight q z n))
        = ∑ A ∈ (Finset.range N).powerset,
            (∏ n ∈ A, addedModeWeight q z n) *
              (∑ R ∈ (Finset.range N).powerset,
                ∏ n ∈ R, removedModeWeight q z n) := by
          apply Finset.sum_congr rfl
          intro A _hA
          rw [Finset.mul_sum]
    _ = (∑ A ∈ (Finset.range N).powerset,
            ∏ n ∈ A, addedModeWeight q z n) *
          (∑ R ∈ (Finset.range N).powerset,
            ∏ n ∈ R, removedModeWeight q z n) := by
          rw [Finset.sum_mul]
    _ = addedFermionPartial N q z * removedFermionPartial N q z := by
          rw [added_powerset_evaluation, removed_powerset_evaluation]

/-- The separated finite fermionic product is the product of one-mode factors. -/
theorem fermionicProductPartial_eq_modeProductPartial (N : Nat) (q z : ℂ) :
    fermionicProductPartial N q z = fermionicModeProductPartial N q z := by
  unfold fermionicProductPartial addedFermionPartial removedFermionPartial
    fermionicModeProductPartial
  rw [← Finset.prod_mul_distrib]
  rfl

/-- Finite fermionic evaluation in the one-factor-per-mode form. -/
theorem finiteZ_eq_fermionicModeProductPartial (N : Nat) (q z : ℂ) (hz : z ≠ 0) :
    finiteZ N q z = fermionicModeProductPartial N q z := by
  rw [finiteZ_eq_fermionicProductPartial N q z hz,
    fermionicProductPartial_eq_modeProductPartial]

/-- Recurrence form of the finite fermionic evaluation. -/
theorem finiteZ_succ (N : Nat) (q z : ℂ) (hz : z ≠ 0) :
    finiteZ (N + 1) q z = finiteZ N q z * fermionicModeFactor q z N := by
  rw [finiteZ_eq_fermionicModeProductPartial (N + 1) q z hz,
    finiteZ_eq_fermionicModeProductPartial N q z hz]
  unfold fermionicModeProductPartial
  rw [Finset.prod_range_succ]

/-! ### Infinite fermionic side -/

/-- A shifted complex geometric sequence has summable norms inside the unit disk. -/
theorem summable_norm_mul_qpow_succ (q c : ℂ) (hq : ‖q‖ < 1) :
    Summable fun n : Nat => ‖c * q ^ (n + 1)‖ := by
  have hgeom : Summable fun n : Nat => ‖(c * q) * q ^ n‖ :=
    summable_norm_iff.mpr ((summable_geometric_of_norm_lt_one hq).mul_left (c * q))
  refine hgeom.congr fun n => ?_
  congr 1
  rw [pow_succ']
  ring

/-- Added-mode one-particle weights are absolutely summable for `‖q‖ < 1`. -/
theorem summable_norm_addedModeWeight (q z : ℂ) (hq : ‖q‖ < 1) :
    Summable fun n : Nat => ‖addedModeWeight q z n‖ := by
  simpa [addedModeWeight] using summable_norm_mul_qpow_succ q z hq

/-- Removed-mode one-particle weights are absolutely summable for `‖q‖ < 1`. -/
theorem summable_norm_removedModeWeight (q z : ℂ) (hq : ‖q‖ < 1) :
    Summable fun n : Nat => ‖removedModeWeight q z n‖ := by
  simpa [removedModeWeight] using summable_norm_mul_qpow_succ q z⁻¹ hq

/-- If one-particle weights have summable norms, then all finite-subset products
have summable norms. -/
theorem summable_norm_finset_prod_of_summable_norm_complex {w : Nat → ℂ}
    (hw : Summable fun n : Nat => ‖w n‖) :
    Summable fun A : Finset Nat => ‖∏ n ∈ A, w n‖ := by
  refine summable_of_sum_le (c := Real.exp (∑' n : Nat, ‖w n‖))
    (fun A : Finset Nat => norm_nonneg _) ?_
  intro T
  let U : Finset Nat := T.biUnion id
  have hT : T ⊆ U.powerset := by
    intro A hA
    exact Finset.mem_powerset.mpr (Finset.subset_biUnion_of_mem id hA)
  calc
    ∑ A ∈ T, ‖∏ n ∈ A, w n‖
        ≤ ∑ A ∈ U.powerset, ‖∏ n ∈ A, w n‖ := by
          exact Finset.sum_le_sum_of_subset_of_nonneg hT
            (fun A _hAU _hAT => norm_nonneg _)
    _ = ∑ A ∈ U.powerset, ∏ n ∈ A, ‖w n‖ := by
          apply Finset.sum_congr rfl
          intro A _hA
          exact Complex.norm_prod A w
    _ = ∏ n ∈ U, (1 + ‖w n‖) := by
          simpa using (Finset.prod_one_add (s := U) (f := fun n : Nat => ‖w n‖)).symm
    _ ≤ ∏ n ∈ U, Real.exp (‖w n‖) := by
          exact Finset.prod_le_prod
            (fun n _hn => by positivity)
            (fun n _hn => by
              simpa [add_comm] using Real.add_one_le_exp (‖w n‖))
    _ = Real.exp (∑ n ∈ U, ‖w n‖) := by
          rw [Real.exp_sum]
    _ ≤ Real.exp (∑' n : Nat, ‖w n‖) := by
          exact Real.exp_le_exp.mpr (hw.sum_le_tsum U (fun n _hn => norm_nonneg _))

/-- Added finite-subset products have summable norms in the unit disk. -/
theorem summable_norm_addedSubsetProduct (q z : ℂ) (hq : ‖q‖ < 1) :
    Summable fun A : Finset Nat => ‖∏ n ∈ A, addedModeWeight q z n‖ :=
  summable_norm_finset_prod_of_summable_norm_complex
    (summable_norm_addedModeWeight q z hq)

/-- Removed finite-subset products have summable norms in the unit disk. -/
theorem summable_norm_removedSubsetProduct (q z : ℂ) (hq : ‖q‖ < 1) :
    Summable fun A : Finset Nat => ‖∏ n ∈ A, removedModeWeight q z n‖ :=
  summable_norm_finset_prod_of_summable_norm_complex
    (summable_norm_removedModeWeight q z hq)

/-- Pair-state monomials are summable in the unit disk. -/
theorem summable_pairMonomial (q z : ℂ) (hq : ‖q‖ < 1) (hz : z ≠ 0) :
    Summable fun p : Finset Nat × Finset Nat => pairMonomial q z p := by
  have hprod : Summable fun p : Finset Nat × Finset Nat =>
      (∏ n ∈ p.1, addedModeWeight q z n) *
        (∏ n ∈ p.2, removedModeWeight q z n) :=
    summable_mul_of_summable_norm
      (R := ℂ) (ι := Finset Nat) (ι' := Finset Nat)
      (f := fun A : Finset Nat => ∏ n ∈ A, addedModeWeight q z n)
      (g := fun R : Finset Nat => ∏ n ∈ R, removedModeWeight q z n)
      (summable_norm_addedSubsetProduct q z hq)
      (summable_norm_removedSubsetProduct q z hq)
  refine hprod.congr fun p => ?_
  rcases p with ⟨A, R⟩
  exact (stateMonomial_mk_eq_products q z hz A R).symm

/-- State monomials are summable in the unit disk. -/
theorem summable_stateMonomial (q z : ℂ) (hq : ‖q‖ < 1) (hz : z ≠ 0) :
    Summable fun S : AdmissibleStates => stateMonomial q z S := by
  have hpair := summable_pairMonomial q z hq hz
  simpa [pairMonomial, admissibleStatesEquivPairs] using
    (admissibleStatesEquivPairs.summable_iff (f := pairMonomial q z)).2 hpair

/-- The added fermionic factor family is multipliable. -/
theorem multipliable_addedFermionFactor (q z : ℂ) (hq : ‖q‖ < 1) :
    Multipliable fun n : Nat => 1 + addedModeWeight q z n :=
  multipliable_one_add_of_summable (summable_norm_addedModeWeight q z hq)

/-- The removed fermionic factor family is multipliable. -/
theorem multipliable_removedFermionFactor (q z : ℂ) (hq : ‖q‖ < 1) :
    Multipliable fun n : Nat => 1 + removedModeWeight q z n :=
  multipliable_one_add_of_summable (summable_norm_removedModeWeight q z hq)

/-- The full one-mode fermionic factor family is multipliable. -/
theorem multipliable_fermionicModeFactor (q z : ℂ) (hq : ‖q‖ < 1) :
    Multipliable fun n : Nat => fermionicModeFactor q z n := by
  exact ((multipliable_addedFermionFactor q z hq).mul
    (multipliable_removedFermionFactor q z hq)).congr fun n => by
      simp [fermionicModeFactor]

/-- The infinite fermionic product splits into the added and removed products. -/
theorem fermionicProduct_eq_separated_tprod (q z : ℂ) (hq : ‖q‖ < 1) :
    fermionicProduct q z =
      (∏' n : Nat, (1 + addedModeWeight q z n)) *
        (∏' n : Nat, (1 + removedModeWeight q z n)) := by
  rw [fermionicProduct]
  rw [show (∏' n : Nat, fermionicModeFactor q z n) =
      ∏' n : Nat, (1 + addedModeWeight q z n) *
        (1 + removedModeWeight q z n) by
    exact tprod_congr fun n => by simp [fermionicModeFactor]]
  exact Multipliable.tprod_mul
    (multipliable_addedFermionFactor q z hq)
    (multipliable_removedFermionFactor q z hq)

/-- Finite added-mode products converge to the added infinite product. -/
theorem tendsto_addedFermionPartial (q z : ℂ) (hq : ‖q‖ < 1) :
    Tendsto (fun N : Nat => addedFermionPartial N q z) atTop
      (𝓝 (∏' n : Nat, (1 + addedModeWeight q z n))) := by
  have h := (multipliable_addedFermionFactor q z hq).hasProd.tendsto_prod_nat
  simpa [addedFermionPartial] using h

/-- Finite removed-mode products converge to the removed infinite product. -/
theorem tendsto_removedFermionPartial (q z : ℂ) (hq : ‖q‖ < 1) :
    Tendsto (fun N : Nat => removedFermionPartial N q z) atTop
      (𝓝 (∏' n : Nat, (1 + removedModeWeight q z n))) := by
  have h := (multipliable_removedFermionFactor q z hq).hasProd.tendsto_prod_nat
  simpa [removedFermionPartial] using h

/-- The finite fermionic products converge to the infinite fermionic product. -/
theorem tendsto_fermionicProductPartial (q z : ℂ) (hq : ‖q‖ < 1) :
    Tendsto (fun N : Nat => fermionicProductPartial N q z) atTop
      (𝓝 (fermionicProduct q z)) := by
  rw [fermionicProduct_eq_separated_tprod q z hq]
  simpa [fermionicProductPartial] using
    (tendsto_addedFermionPartial q z hq).mul
      (tendsto_removedFermionPartial q z hq)

/-- The finite state sums converge to the infinite fermionic product. -/
theorem tendsto_finiteZ_fermionicProduct (q z : ℂ) (hq : ‖q‖ < 1) (hz : z ≠ 0) :
    Tendsto (fun N : Nat => finiteZ N q z) atTop (𝓝 (fermionicProduct q z)) := by
  have hlim := tendsto_fermionicProductPartial q z hq
  have hfinite : (fun N : Nat => finiteZ N q z) =
      fun N : Nat => fermionicProductPartial N q z := by
    funext N
    exact finiteZ_eq_fermionicProductPartial N q z hz
  simpa [hfinite] using hlim

/-- Once the bounded state sums are known to exhaust the `tsum` defining `Z`,
the infinite fermionic evaluation follows. -/
theorem Z_eq_fermionicProduct_of_tendsto_finiteZ (q z : ℂ)
    (hq : ‖q‖ < 1) (hz : z ≠ 0)
    (hZ : Tendsto (fun N : Nat => finiteZ N q z) atTop (𝓝 (Z q z))) :
    Z q z = fermionicProduct q z :=
  tendsto_nhds_unique hZ (tendsto_finiteZ_fermionicProduct q z hq hz)

/-- The nested bounded state sum is the sum over bounded pair-states. -/
theorem finiteZ_eq_pair_sum (N : Nat) (q z : ℂ) :
    finiteZ N q z = ∑ p ∈ boundedStatePairs N, pairMonomial q z p := by
  unfold finiteZ boundedStatePairs pairMonomial
  simpa using
    (Finset.sum_product
      (s := (Finset.range N).powerset)
      (t := (Finset.range N).powerset)
      (f := fun p : Finset Nat × Finset Nat =>
        stateMonomial q z ⟨p.1, p.2⟩)).symm

/-- If the pair-state monomials are summable, the bounded state sums exhaust `Z`. -/
theorem tendsto_finiteZ_Z_of_summable_pairMonomial (q z : ℂ)
    (hsum : Summable fun p : Finset Nat × Finset Nat => pairMonomial q z p) :
    Tendsto (fun N : Nat => finiteZ N q z) atTop (𝓝 (Z q z)) := by
  rw [Z_eq_pair_tsum q z]
  have hhas :
      HasSum (pairMonomial q z)
        (∑' p : Finset Nat × Finset Nat, pairMonomial q z p) :=
    hsum.hasSum
  have hlim := hhas.comp tendsto_boundedStatePairs_atTop
  have hfinite : (fun N : Nat => finiteZ N q z) =
      fun N : Nat => ∑ p ∈ boundedStatePairs N, pairMonomial q z p := by
    funext N
    exact finiteZ_eq_pair_sum N q z
  simpa [hfinite] using hlim

/-- Fermionic evaluation reduced to absolute summability of the pair-state monomials. -/
theorem Z_eq_fermionicProduct_of_summable_pairMonomial (q z : ℂ)
    (hq : ‖q‖ < 1) (hz : z ≠ 0)
    (hsum : Summable fun p : Finset Nat × Finset Nat => pairMonomial q z p) :
    Z q z = fermionicProduct q z :=
  Z_eq_fermionicProduct_of_tendsto_finiteZ q z hq hz
    (tendsto_finiteZ_Z_of_summable_pairMonomial q z hsum)

/-- Infinite fermionic evaluation of the Boson-Fermion state sum. -/
theorem Z_eq_fermionicProduct (q z : ℂ) (hq : ‖q‖ < 1) (hz : z ≠ 0) :
    Z q z = fermionicProduct q z :=
  Z_eq_fermionicProduct_of_summable_pairMonomial q z hq hz
    (summable_pairMonomial q z hq hz)

/-- Infinite bosonic decomposition of `Z` into charge sectors. -/
theorem Z_eq_tsum_chargeSectorZ (q z : ℂ) (hq : ‖q‖ < 1) (hz : z ≠ 0) :
    Z q z = ∑' c : Int, chargeSectorZ q z c := by
  have hstate := summable_stateMonomial q z hq hz
  have hsigma : Summable fun x :
      Sigma fun c : Int => {S : AdmissibleStates // charge S = c} =>
        stateMonomial q z x.2.1 := by
    simpa [chargeSigmaEquivStates] using
      (chargeSigmaEquivStates.summable_iff (f := stateMonomial q z)).2 hstate
  have hfiber :
      ∀ c : Int, Summable fun S : {S : AdmissibleStates // charge S = c} =>
        stateMonomial q z S.1 := by
    intro c
    simpa [Function.comp_def] using
      hstate.subtype {S : AdmissibleStates | charge S = c}
  calc
    Z q z = ∑' S : AdmissibleStates, stateMonomial q z S := rfl
    _ = ∑' x : Sigma fun c : Int => {S : AdmissibleStates // charge S = c},
          stateMonomial q z x.2.1 := by
          exact (chargeSigmaEquivStates.tsum_eq (stateMonomial q z)).symm
    _ = ∑' c : Int, ∑' S : {S : AdmissibleStates // charge S = c},
          stateMonomial q z S.1 := by
          exact Summable.tsum_sigma' hfiber hsigma
    _ = ∑' c : Int, chargeSectorZ q z c := by
          rfl

/-- Infinite bosonic decomposition with the charge monomial factored out. -/
theorem Z_eq_tsum_zpow_chargeEnergySectorZ (q z : ℂ)
    (hq : ‖q‖ < 1) (hz : z ≠ 0) :
    Z q z = ∑' c : Int, z ^ c * chargeEnergySectorZ q c := by
  rw [Z_eq_tsum_chargeSectorZ q z hq hz]
  apply tsum_congr
  intro c
  exact chargeSectorZ_eq_zpow_mul_chargeEnergySectorZ q z c

/-! ### Boson-Fermion product side as Jacobi's triple product -/

/-- Product side `(q, zq, z⁻¹q; q)_∞` in the shifted JTP convention. -/
noncomputable def shiftedJTPProduct (q z : ℂ) : ℂ :=
  (∏' n : Nat, (1 - q ^ (n + 1))) *
    (∏' n : Nat, (1 - z * q ^ (n + 1))) *
      (∏' n : Nat, (1 - z⁻¹ * q ^ (n + 1)))

private theorem summable_norm_shiftedJTPFactor_tail
    (c q : ℂ) (hq : ‖q‖ < 1) :
    Summable fun n : Nat => ‖-(c * q) * q ^ n‖ :=
  Ch02.summable_norm_mul_geometric_complex (-(c * q)) q hq

private theorem multipliable_shiftedJTPFactor
    (c q : ℂ) (hq : ‖q‖ < 1) :
    Multipliable fun n : Nat => 1 - c * q ^ (n + 1) := by
  have h := multipliable_one_add_of_summable
    (summable_norm_shiftedJTPFactor_tail c q hq)
  refine h.congr fun n => ?_
  rw [show q ^ (n + 1) = q * q ^ n by
    rw [show n + 1 = 1 + n by omega, pow_add, pow_one]]
  ring

private lemma norm_of_sq_eq_lt_one {Y q : ℂ}
    (hYq : Y ^ 2 = q) (hq : ‖q‖ < 1) :
    ‖Y‖ < 1 := by
  have hY_sq : ‖Y‖ ^ 2 = ‖q‖ := by
    rw [← norm_pow, hYq]
  rw [← hY_sq] at hq
  exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) (by simpa using hq)

private lemma jacobiProductEvenFactor_reparam
    (q Y : ℂ) (hYq : Y ^ 2 = q) (n : Nat) :
    Ch02.jacobiProductEvenFactor Y n = 1 - q ^ (n + 1) := by
  simp [Ch02.jacobiProductEvenFactor]
  rw [show Y ^ (2 * (n + 1)) = (Y ^ 2) ^ (n + 1) by rw [pow_mul], hYq]

private lemma jacobiProductOddFactor_reparam
    (z q Y : ℂ) (hYq : Y ^ 2 = q) (n : Nat) :
    Ch02.jacobiProductOddFactor Y (-(z * Y)) n =
      1 - z * q ^ (n + 1) := by
  simp [Ch02.jacobiProductOddFactor]
  have hpow :
      Y * Y ^ (2 * (n + 1) - 1) = q ^ (n + 1) := by
    have hsucc : 2 * (n + 1) - 1 + 1 = 2 * (n + 1) := by omega
    calc
      Y * Y ^ (2 * (n + 1) - 1) = Y ^ (2 * (n + 1) - 1 + 1) := by
        rw [← pow_succ']
      _ = Y ^ (2 * (n + 1)) := by rw [hsucc]
      _ = (Y ^ 2) ^ (n + 1) := by rw [pow_mul]
      _ = q ^ (n + 1) := by rw [hYq]
  rw [show z * Y * Y ^ (2 * (n + 1) - 1) =
      z * (Y * Y ^ (2 * (n + 1) - 1)) by ring, hpow]
  ring

private lemma jacobiProductOddFactor_inv_reparam_zero
    (z Y : ℂ) (hz : z ≠ 0) (hY : Y ≠ 0) :
    Ch02.jacobiProductOddFactor Y (-(z * Y))⁻¹ 0 = 1 - z⁻¹ := by
  simp [Ch02.jacobiProductOddFactor]
  field_simp [hz, hY]
  ring

private lemma jacobiProductOddFactor_inv_reparam_tail
    (z q Y : ℂ) (hz : z ≠ 0) (hY : Y ≠ 0) (hYq : Y ^ 2 = q) (n : Nat) :
    Ch02.jacobiProductOddFactor Y (-(z * Y))⁻¹ (n + 1) =
      1 - z⁻¹ * q ^ (n + 1) := by
  simp [Ch02.jacobiProductOddFactor]
  have hpow :
      Y ^ (2 * (n + 1 + 1) - 1) = Y * q ^ (n + 1) := by
    have hexp : 2 * (n + 1 + 1) - 1 = 2 * (n + 1) + 1 := by omega
    rw [hexp, pow_succ']
    rw [show Y ^ (2 * (n + 1)) = (Y ^ 2) ^ (n + 1) by rw [pow_mul], hYq]
  rw [hpow]
  field_simp [hz, hY]
  ring

private theorem jacobiInfiniteProduct_reparam_shifted
    (z q Y : ℂ) (hz : z ≠ 0) (hY : Y ≠ 0) (hYq : Y ^ 2 = q)
    (hq : ‖q‖ < 1) :
    Ch02.jacobiInfiniteProduct Y (-(z * Y)) =
      (1 - z⁻¹) * shiftedJTPProduct q z := by
  have hYnorm : ‖Y‖ < 1 := norm_of_sq_eq_lt_one hYq hq
  rw [Ch02.jacobiInfiniteProduct_eq_tprod_components Y (-(z * Y)) hYnorm]
  have h_even :
      (∏' n : Nat, Ch02.jacobiProductEvenFactor Y n) =
        ∏' n : Nat, (1 - q ^ (n + 1)) :=
    tprod_congr fun n => jacobiProductEvenFactor_reparam q Y hYq n
  have h_odd :
      (∏' n : Nat, Ch02.jacobiProductOddFactor Y (-(z * Y)) n) =
        ∏' n : Nat, (1 - z * q ^ (n + 1)) :=
    tprod_congr fun n => jacobiProductOddFactor_reparam z q Y hYq n
  have h_tail_mult :
      Multipliable fun n : Nat =>
        Ch02.jacobiProductOddFactor Y (-(z * Y))⁻¹ (n + 1) := by
    exact (multipliable_shiftedJTPFactor z⁻¹ q hq).congr
      fun n => (jacobiProductOddFactor_inv_reparam_tail z q Y hz hY hYq n).symm
  have h_inv :
      (∏' n : Nat, Ch02.jacobiProductOddFactor Y (-(z * Y))⁻¹ n) =
        (1 - z⁻¹) * ∏' n : Nat, (1 - z⁻¹ * q ^ (n + 1)) := by
    rw [tprod_eq_zero_mul' h_tail_mult]
    rw [jacobiProductOddFactor_inv_reparam_zero z Y hz hY]
    congr 1
    exact tprod_congr fun n =>
      jacobiProductOddFactor_inv_reparam_tail z q Y hz hY hYq n
  rw [h_even, h_odd, h_inv]
  simp [shiftedJTPProduct]
  ring

private lemma int_two_dvd_mul_self_add_one (n : Int) :
    (2 : Int) ∣ n * (n + 1) := by
  rcases Int.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · exact ⟨m * (n + 1), by rw [hm]; ring⟩
  · exact ⟨n * (m + 1), by rw [hm]; ring⟩

private lemma int_triangular_ne_zero_of_ne (n : Int)
    (hn0 : n ≠ 0) (hnneg : n ≠ -1) :
    n * (n + 1) / 2 ≠ 0 := by
  intro h
  have hdiv : (2 : Int) ∣ n * (n + 1) := int_two_dvd_mul_self_add_one n
  have hprod : n * (n + 1) = 0 := by
    rw [← Int.ediv_mul_cancel hdiv]
    rw [h]
    ring
  rcases mul_eq_zero.mp hprod with h0 | h1
  · exact hn0 h0
  · have : n = -1 := by omega
    exact hnneg this

private lemma zpow_sq_add_self_reparam
    (q Y : ℂ) (hYq : Y ^ 2 = q) (n : Int) :
    Y ^ (n ^ 2 + n) = q ^ (n * (n + 1) / 2) := by
  have hdiv : (2 : Int) ∣ n * (n + 1) := int_two_dvd_mul_self_add_one n
  have hmul : 2 * (n * (n + 1) / 2) = n * (n + 1) := by
    rw [show 2 * (n * (n + 1) / 2) = (n * (n + 1) / 2) * 2 by ring]
    exact Int.ediv_mul_cancel hdiv
  calc
    Y ^ (n ^ 2 + n) = Y ^ (n * (n + 1)) := by ring_nf
    _ = Y ^ (2 * (n * (n + 1) / 2)) := by rw [hmul]
    _ = (Y ^ (2 : Int)) ^ (n * (n + 1) / 2) := by rw [zpow_mul]
    _ = (Y ^ 2) ^ (n * (n + 1) / 2) := by rfl
    _ = q ^ (n * (n + 1) / 2) := by rw [hYq]

private theorem jacobiInfiniteSeries_reparam_triangular
    (z q Y : ℂ) (hY : Y ≠ 0) (hYq : Y ^ 2 = q) :
    Ch02.jacobiInfiniteSeries Y (-(z * Y)) =
      ∑' n : Int, (-z : ℂ) ^ n * q ^ (n * (n + 1) / 2) := by
  rw [Ch02.jacobiInfiniteSeries]
  refine tsum_congr fun n => ?_
  have hbase : (-(z * Y) : ℂ) = (-z) * Y := by ring
  rw [hbase, mul_zpow]
  have hmul : Y ^ n * Y ^ (n ^ 2) = Y ^ (n + n ^ 2) := by
    rw [← zpow_add₀ hY]
  rw [show ((-z : ℂ) ^ n * Y ^ n) * Y ^ (n ^ 2) =
      (-z : ℂ) ^ n * (Y ^ n * Y ^ (n ^ 2)) by ring]
  rw [hmul, show n + n ^ 2 = n ^ 2 + n by ring]
  rw [zpow_sq_add_self_reparam q Y hYq n]

/-- Shifted form of Jacobi's triple product:
`(1 - z⁻¹)(q, zq, z⁻¹q; q)_∞ = ∑ (-z)^n q^{n(n+1)/2}`. -/
theorem shiftedJTPProduct_eq_triangularTheta_of_ne_zero
    (q z : ℂ) (hq : ‖q‖ < 1) (hz : z ≠ 0) (hq0 : q ≠ 0) :
    (1 - z⁻¹) * shiftedJTPProduct q z =
      ∑' n : Int, (-z : ℂ) ^ n * q ^ (n * (n + 1) / 2) := by
  obtain ⟨Y, hYq⟩ := IsAlgClosed.exists_pow_nat_eq q (n := 2) (by norm_num)
  have hY : Y ≠ 0 := by
    intro hY0
    apply hq0
    rw [← hYq, hY0]
    ring
  have hYnorm : ‖Y‖ < 1 := norm_of_sq_eq_lt_one hYq hq
  have harg : (-(z * Y) : ℂ) ≠ 0 :=
    neg_ne_zero.mpr (mul_ne_zero hz hY)
  rw [← jacobiInfiniteProduct_reparam_shifted z q Y hz hY hYq hq]
  rw [Ch02.jacobiTripleProduct Y (-(z * Y)) hYnorm harg]
  rw [jacobiInfiniteSeries_reparam_triangular z q Y hY hYq]

private theorem bosonFermionThetaSeries_zero (z : ℂ) :
    bosonFermionThetaSeries 0 z = 1 + z⁻¹ := by
  rw [bosonFermionThetaSeries]
  rw [tsum_eq_sum (s := ({(-1 : Int), 0} : Finset Int))]
  · simp
    ring
  · intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    have hnneg : n ≠ -1 := fun h => hn (Or.inl h)
    have hn0 : n ≠ 0 := fun h => hn (Or.inr h)
    have htri_ne : n * (n + 1) / 2 ≠ 0 :=
      int_triangular_ne_zero_of_ne n hn0 hnneg
    rw [zero_zpow _ htri_ne, mul_zero]

private theorem shiftedJTPProduct_neg_eq_bosonEuler_mul_fermionic
    (q z : ℂ) (hq : ‖q‖ < 1) :
    shiftedJTPProduct q (-z) = bosonEulerProduct q * fermionicProduct q z := by
  rw [shiftedJTPProduct, bosonEulerProduct,
    fermionicProduct_eq_separated_tprod q z hq]
  have h_added :
      (∏' n : Nat, (1 - (-z) * q ^ (n + 1))) =
        ∏' n : Nat, (1 + addedModeWeight q z n) :=
    tprod_congr fun n => by
      simp [addedModeWeight]
  have h_removed :
      (∏' n : Nat, (1 - (-z)⁻¹ * q ^ (n + 1))) =
        ∏' n : Nat, (1 + removedModeWeight q z n) :=
    tprod_congr fun n => by
      simp [removedModeWeight]
  rw [h_added, h_removed]
  ring

/-- Product form of the Boson-Fermion side, away from the removable `q = 0`
endpoint. -/
theorem bosonEuler_mul_fermionicProduct_eq_theta_of_ne_zero
    (q z : ℂ) (hq : ‖q‖ < 1) (hz : z ≠ 0) (hq0 : q ≠ 0) :
    (1 + z⁻¹) * bosonEulerProduct q * fermionicProduct q z =
      bosonFermionThetaSeries q z := by
  have hjtp :=
    shiftedJTPProduct_eq_triangularTheta_of_ne_zero q (-z) hq
      (neg_ne_zero.mpr hz) hq0
  rw [shiftedJTPProduct_neg_eq_bosonEuler_mul_fermionic q z hq] at hjtp
  calc
    (1 + z⁻¹) * bosonEulerProduct q * fermionicProduct q z =
        (1 - (-z)⁻¹) * (bosonEulerProduct q * fermionicProduct q z) := by
          simp
          ring
    _ = bosonFermionThetaSeries q z := by
          simpa [bosonFermionThetaSeries] using hjtp

/-- Product form of the Boson-Fermion side in the full disk `‖q‖ < 1`. -/
theorem bosonEuler_mul_fermionicProduct_eq_theta
    (q z : ℂ) (hq : ‖q‖ < 1) (hz : z ≠ 0) :
    (1 + z⁻¹) * bosonEulerProduct q * fermionicProduct q z =
      bosonFermionThetaSeries q z := by
  by_cases hq0 : q = 0
  · subst q
    rw [bosonFermionThetaSeries_zero]
    simp [bosonEulerProduct, fermionicProduct, fermionicModeFactor,
      addedModeWeight, removedModeWeight]
  · exact bosonEuler_mul_fermionicProduct_eq_theta_of_ne_zero q z hq hz hq0

/-- Boson-Fermion derivation of the shifted Jacobi triple product, using the
already-proved fermionic evaluation of `Z`. -/
theorem bosonFermion_JTP_of_ne_zero (q z : ℂ)
    (hq : ‖q‖ < 1) (hz : z ≠ 0) (hq0 : q ≠ 0) :
    (1 + z⁻¹) * Z q z * bosonEulerProduct q =
      bosonFermionThetaSeries q z := by
  rw [Z_eq_fermionicProduct q z hq hz]
  calc
    (1 + z⁻¹) * fermionicProduct q z * bosonEulerProduct q =
        (1 + z⁻¹) * bosonEulerProduct q * fermionicProduct q z := by
          ring
    _ = bosonFermionThetaSeries q z :=
          bosonEuler_mul_fermionicProduct_eq_theta_of_ne_zero q z hq hz hq0

/-- Boson-Fermion derivation of the shifted Jacobi triple product, using the
already-proved fermionic evaluation of `Z`. -/
theorem bosonFermion_JTP (q z : ℂ)
    (hq : ‖q‖ < 1) (hz : z ≠ 0) :
    (1 + z⁻¹) * Z q z * bosonEulerProduct q =
      bosonFermionThetaSeries q z := by
  rw [Z_eq_fermionicProduct q z hq hz]
  calc
    (1 + z⁻¹) * fermionicProduct q z * bosonEulerProduct q =
        (1 + z⁻¹) * bosonEulerProduct q * fermionicProduct q z := by
          ring
    _ = bosonFermionThetaSeries q z :=
          bosonEuler_mul_fermionicProduct_eq_theta q z hq hz

/-- Finite bosonic decomposition: the bounded state sum splits by charge. -/
theorem finiteZ_eq_sum_chargeSectors (N : Nat) (q z : ℂ) :
    finiteZ N q z = ∑ c ∈ finiteChargeSpectrum N, finiteChargeSector N q z c := by
  rw [finiteZ_eq_pair_sum]
  unfold finiteChargeSpectrum finiteChargeSector
  exact (Finset.sum_fiberwise_of_maps_to
    (s := boundedStatePairs N) (t := (boundedStatePairs N).image pairCharge)
    (g := pairCharge) (f := pairMonomial q z)
    (by
      intro p hp
      exact Finset.mem_image_of_mem pairCharge hp)).symm

/-- Inside one charge sector, the `z`-power factors out as `z^c`. -/
theorem finiteChargeSector_eq_zpow_mul_energySector
    (N : Nat) (q z : ℂ) (c : Int) :
    finiteChargeSector N q z c =
      z ^ c * finiteChargeEnergySector N q c := by
  unfold finiteChargeSector finiteChargeEnergySector pairMonomial pairEnergyMonomial
    stateMonomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hcharge : charge { added := p.1, removed := p.2 } = c :=
    (Finset.mem_filter.mp hp).2
  simp [hcharge]

/-- Charge-sector form with the sector energy generating functions exposed. -/
theorem finiteZ_eq_sum_zpow_chargeEnergySectors (N : Nat) (q z : ℂ) :
    finiteZ N q z =
      ∑ c ∈ finiteChargeSpectrum N, z ^ c * finiteChargeEnergySector N q c := by
  rw [finiteZ_eq_sum_chargeSectors]
  apply Finset.sum_congr rfl
  intro c _hc
  exact finiteChargeSector_eq_zpow_mul_energySector N q z c

lemma sum_range_succ_eq_triangular (m : Nat) :
    (∑ n ∈ Finset.range m, (n + 1)) = triangular m := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih, triangular_succ]

/-- Positive charge ground state in the current integer-energy convention. -/
def positiveChargeGroundState (m : Nat) : AdmissibleState :=
  ⟨Finset.range m, ∅⟩

/-- Negative charge ground state in the current integer-energy convention. -/
def negativeChargeGroundState (m : Nat) : AdmissibleState :=
  ⟨∅, Finset.range m⟩

@[simp] theorem charge_positiveChargeGroundState (m : Nat) :
    charge (positiveChargeGroundState m) = m := by
  simp [positiveChargeGroundState, charge]

@[simp] theorem energy_positiveChargeGroundState (m : Nat) :
    energy (positiveChargeGroundState m) = triangular m := by
  simp [positiveChargeGroundState, energy, sum_range_succ_eq_triangular]

@[simp] theorem charge_negativeChargeGroundState (m : Nat) :
    charge (negativeChargeGroundState m) = -(m : Int) := by
  simp [negativeChargeGroundState, charge]

@[simp] theorem energy_negativeChargeGroundState (m : Nat) :
    energy (negativeChargeGroundState m) = triangular m := by
  simp [negativeChargeGroundState, energy, sum_range_succ_eq_triangular]

/-- Weight of the positive charge ground state. -/
theorem stateMonomial_positiveChargeGroundState (q z : ℂ) (m : Nat) :
    stateMonomial q z (positiveChargeGroundState m) =
      z ^ (m : Int) * q ^ triangular m := by
  simp [stateMonomial]

/-- Weight of the negative charge ground state. -/
theorem stateMonomial_negativeChargeGroundState (q z : ℂ) (m : Nat) :
    stateMonomial q z (negativeChargeGroundState m) =
      z ^ (-(m : Int)) * q ^ triangular m := by
  simp [stateMonomial]

end Ch05
end PartI
end QseriesFormalization
