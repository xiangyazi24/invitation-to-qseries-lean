/-
  Audit file for the Q-series formalization project.

  ⚠️  PARTIAL AUDIT — DOES NOT CONSTITUTE "PLAYBOOK PASS".

  This file runs `#print axioms` on listed theorems to verify they use only
  the core three axioms (propext, Classical.choice, Quot.sound).  This covers
  **only points 1, 2, 10** of the playbook's 11-point Phase 3 audit (Chapter
  3.1 of `formalization-playbook.md`):

    1. 0 sorry         ✓ (grep-checked)
    2. 0 custom axiom  ✓ (grep-checked)
   10. #print axioms   ✓ (this file)
    5. full build      ✓ (CI build)

  The following points are **NOT** verified by this file:

    3. 0 assumption-structure evasion
    4. 0 trivially-true conclusions  (Ch12 `ramanujanRRCFValue := α⁻¹ + β`
        with `_placeholder_zero` proving it `= 0` is a known violation;
        not yet cleaned up.)
    6. 0 Prop-assumption evasion
    7. end-to-end definability of statement from raw mathematical inputs
    8. minimal-interface check (derivable assumptions not exposed)
    9. counter-example checks for long-standing sorries
   11. honest conditional/unconditional classification per theorem

  Furthermore, this file lists theorems by name only; it does NOT certify
  that each listed theorem is **the chapter's main result** in Chan's book.
  After cross-checking with Chan's PDF TOC (PLAYBOOK_AUDIT.md 2026-05-22):

    PASS  (chapter content + main thm proved):   Ch01 Ch02 Ch03 Ch04 Ch07
                                                  Ch18 Ch19
    AUX   (real content, main result partial):    Ch08 Ch09 Ch11 Ch14 Ch17
                                                  Ch20
    SHADOW (only trunc_N boilerplate):            Ch10 Ch12 Ch13 Ch16
    MISLABELED (file ≠ Chan's chapter content):   Ch05 Ch06 Ch15

  Listing a theorem from a MISLABELED file (e.g. Ch05.franklinInv_*) below
  attests only that its axiom set is clean; it does NOT attest that the
  theorem is the chapter-main result for that chapter number.  Several
  entries below carry explicit comments to this effect.
-/

import QseriesFormalization.Chapter01_GenFun
import QseriesFormalization.Chapter19_Section5
import QseriesFormalization.Chapter17_SectionBridge
import QseriesFormalization.Chapter17_Mod5ResidueAnalysis
import QseriesFormalization.Chapter17_PerTermAnalysis
import QseriesFormalization.Chapter19_JacobiTripleSignChar
import QseriesFormalization.Pending.JacobiCubeAnalyticToFormal
import QseriesFormalization.Pending.Chapter17_Ramanujan5Conditional
import QseriesFormalization.Pending.Chapter19_B2_FromCubeConvolution
import QseriesFormalization.Pending.Chapter17_Ramanujan7
import QseriesFormalization.Pending.Chapter06_Macdonald_A1
import QseriesFormalization.Pending.Chapter05_JTP
import QseriesFormalization.Pending.Chapter17_Hirschhorn_Combination
import QseriesFormalization.Pending.Chapter17_Hirschhorn_Mod11
import QseriesFormalization.Pending.Chapter20_TauParity
import QseriesFormalization.Pending.SignSequences_Mod3
import QseriesFormalization.Chapter14_CrankN9
import QseriesFormalization.Pending.Chapter17_ASD_Mod5
import QseriesFormalization.Pending.Chapter17_ASD_Mod7
import QseriesFormalization.Pending.Chapter08_FiniteRR
import QseriesFormalization.Pending.Chapter08_Gaussian
import QseriesFormalization.Pending.Chapter16_MBI_Proof
import QseriesFormalization.Pending.Chapter17_ASD_Mod5_Full
import QseriesFormalization.Pending.Chapter17_ASD_Mod7_Full
import QseriesFormalization.Pending.JTP_FormalPS_Pentagonal
import QseriesFormalization.Pending.ASD_EtaProducts
import QseriesFormalization.Pending.JTP_FormalPS_Mod7
import QseriesFormalization.Pending.ASD_Mod7_EtaQuotient
import QseriesFormalization.Pending.RamanujanQuintic
import QseriesFormalization.Pending.RamanujanQuinticJTP
import QseriesFormalization.Chapter17_Mod7PerTermAnalysis
import QseriesFormalization.Chapter01_PartitionCount12
import QseriesFormalization.Chapter01_PartitionCount13
import QseriesFormalization.Chapter01_PartitionCount14
import QseriesFormalization.Chapter01_PartitionCount15
import QseriesFormalization.Chapter01_PartitionCount16
import QseriesFormalization.Chapter01_PartitionCount17
import QseriesFormalization.Chapter01_RecurrenceGeneral
import QseriesFormalization.Chapter01_PartitionCount18
import QseriesFormalization.Chapter01_PartitionCount19
import QseriesFormalization.Chapter01_PartitionCount20
import QseriesFormalization.Chapter01_PartitionCount21
import QseriesFormalization.Chapter01_PartitionCount22
import QseriesFormalization.Chapter01_PartitionCount23
import QseriesFormalization.Chapter01_PartitionCount24
import QseriesFormalization.Chapter01_PartitionCount25
import QseriesFormalization.Chapter01_PartitionCount26
import QseriesFormalization.Chapter01_PartitionCount27
import QseriesFormalization.Chapter01_PartitionCount28
import QseriesFormalization.Chapter01_PartitionCount29
import QseriesFormalization.Chapter01_PartitionCount30
import QseriesFormalization.Chapter01_PartitionCount31
import QseriesFormalization.Chapter01_PartitionCount32
import QseriesFormalization.Chapter01_PartitionCount33
import QseriesFormalization.Chapter01_PartitionCount34
import QseriesFormalization.Chapter01_PartitionCount35
import QseriesFormalization.Chapter01_PartitionCount36
import QseriesFormalization.Chapter01_PartitionCount37
import QseriesFormalization.Chapter01_PartitionCount38
import QseriesFormalization.Chapter01_PartitionCount39
import QseriesFormalization.Chapter01_PartitionCount40
import QseriesFormalization.Chapter01_PartitionCount41
import QseriesFormalization.Chapter01_PartitionCount42
import QseriesFormalization.Chapter01_PartitionCount43
import QseriesFormalization.Chapter01_PartitionCount44
import QseriesFormalization.Chapter01_PartitionCount45
import QseriesFormalization.Chapter01_PartitionCount46
import QseriesFormalization.Chapter01_PartitionCount47
import QseriesFormalization.Chapter01_PartitionCount48
import QseriesFormalization.Chapter01_PartitionCount49
import QseriesFormalization.Chapter01_PartitionCount50
import QseriesFormalization.Chapter01_PartitionCount51
import QseriesFormalization.Chapter01_PartitionCount52
import QseriesFormalization.Chapter01_PartitionCount53
import QseriesFormalization.Chapter01_PartitionCount54
import QseriesFormalization.Chapter17_HigherCases
import QseriesFormalization.Chapter14_CrankN4
import QseriesFormalization.Chapter14_CrankN14
import QseriesFormalization.Chapter14_CrankN19
import QseriesFormalization.Chapter14_CrankN24
import QseriesFormalization.Chapter14_CrankN29
import QseriesFormalization.Chapter14_CrankN34
import QseriesFormalization.Chapter14_CrankGenFun
import QseriesFormalization.Chapter14_Thm116
import QseriesFormalization.Chapter02
import QseriesFormalization.Chapter03
import QseriesFormalization.Chapter04
import QseriesFormalization.Chapter04_T43
import QseriesFormalization.Chapter05_Franklin
import QseriesFormalization.Chapter05_BosonFermion
import QseriesFormalization.Chapter07
import QseriesFormalization.Chapter07_RRStep1
import QseriesFormalization.Chapter07_RRStep1H
import QseriesFormalization.Chapter07_RRStep5
import QseriesFormalization.Chapter07_RRStep5H
import QseriesFormalization.Chapter09
import QseriesFormalization.Chapter09_BaileyLemma
import QseriesFormalization.Chapter06
import QseriesFormalization.Chapter08
import QseriesFormalization.Chapter10
import QseriesFormalization.Chapter11
import QseriesFormalization.Chapter12
import QseriesFormalization.Chapter13
import QseriesFormalization.Chapter14
import QseriesFormalization.Chapter15
import QseriesFormalization.Chapter16
import QseriesFormalization.Chapter17
import QseriesFormalization.Chapter18
import QseriesFormalization.Chapter19
import QseriesFormalization.Chapter20
import QseriesFormalization.Pending.Chapter13_RRCF_RForm
import QseriesFormalization.Pending.Chapter10_MockTheta_PS
import QseriesFormalization.Pending.Chapter10_Bridge
import QseriesFormalization.Pending.Chapter11_RRCF_Convergent
import QseriesFormalization.Pending.Chapter12_SpecialValue
import QseriesFormalization.Pending.Chapter15_WronskianIndependent
import QseriesFormalization.Pending.Chapter15_R_ODE

namespace QseriesFormalization.Audit

open QseriesFormalization.PartIV.Ch19
open QseriesFormalization.PartIV.Ch20

-- Flagship Ch19 theorems
#print axioms partitionGenFun_eq_tprod
#print axioms multipliable_one_sub_X_pow_succ
#print axioms factor_geom_series_identity
#print axioms qPochInfPS_eq_tprod
#print axioms coeff_tprod_one_sub_X_pow_succ
#print axioms coeff_qPochInfPS_eq_coeff_finite_product
#print axioms partial_prod_one_sub_X_pow_succ_coeff_stable
#print axioms partial_prod_one_sub_X_pow_succ_coeff_eq

-- Flagship Ch19 algebraic theorems
#print axioms partitionGenFun_mul_qPochInfPS
#print axioms ramanujan_key_identity
#print axioms coeff_mul_expand_of_lt
#print axioms ramanujan_from_pochInf_vanishes
#print axioms coeff_pochInfPow_eq_partitionCount_of_lt

-- Naturality theorems
#print axioms map_partitionGenFun
#print axioms map_qPochInfPS

-- Flagship Ch20 theorems
#print axioms discriminantPS_eq_X_mul_tprod_pow_24
#print axioms discriminantPS_mul_partitionGenFun_pow_24
#print axioms map_discriminantPS
#print axioms cast_ramanujanTau_int

-- A1 bridge theorems (this session)
#print axioms QseriesFormalization.PartIV.Ch19.coeff_qPochInfPS_eq_coeff_finite_product_of_lt
#print axioms QseriesFormalization.PartIV.Ch19.trunc_qPochInfPS_eq_trunc_finite_product
#print axioms QseriesFormalization.PartIV.Ch19.coeff_qPochInfPS_pow_eq_coeff_finite_product_pow
#print axioms ramanujanTau_eq_coeff_finite_product
#print axioms ramanujanTau_eq_coeff_prod_of_pow

-- B1 Euler pentagonal step 1 (this session)
#print axioms QseriesFormalization.PartIV.Ch19.genFun_signedStrictChar_eq_qPochInfPS
#print axioms QseriesFormalization.PartIV.Ch19.coeff_qPochInfPS_eq_signedStrictCount

-- B1 Step 2 FINAL: Euler Pentagonal Number Theorem as formal PS
-- (Note: coeff_qPochInfPS_int_eq_pentagonalSign pulls in Lean.ofReduceBool
-- via Ch05's native_decide-based dependencies; this is the only theorem in
-- the audit not in the core-three-axioms set.)
#print axioms QseriesFormalization.PartIV.Ch19.coeff_finite_product_one_sub_X_pow_succ
#print axioms QseriesFormalization.PartIV.Ch19.coeff_finite_product_eq_signedStrictPartitionCount
#print axioms QseriesFormalization.PartIV.Ch19.coeff_qPochInfPS_int_eq_pentagonalSign
#print axioms QseriesFormalization.PartIV.Ch19.coeff_qPochInfPS_eq_pentagonalSign
#print axioms QseriesFormalization.PartI.Ch05.euler_pentagonal_combinatorial

-- B2 groundwork
#print axioms QseriesFormalization.PartIV.Ch19.jacobiThetaPS
#print axioms QseriesFormalization.PartIV.Ch19.coeff_jacobiThetaPS

-- B2 HEADLINE (closed 2026-05-23 via analytic-formal Taylor uniqueness)
#print axioms QseriesFormalization.Pending.JacobiCubeAnalyticToFormal.qPochInfPS_pow_three_eq_jacobiThetaPS_complex
#print axioms QseriesFormalization.Pending.JacobiCubeAnalyticToFormal.qPochInfPS_pow_three_eq_jacobiThetaPS_int
#print axioms QseriesFormalization.Pending.JacobiCubeAnalyticToFormal.qPochInfPS_pow_three_eq_jacobiThetaPS
#print axioms QseriesFormalization.PartIV.Ch19.eulerPentagonalInfiniteProduct_eq_tsum_pentagonalSign
#print axioms QseriesFormalization.PartIV.Ch19.pentagonalSign_pentagonalIndex_eq
#print axioms QseriesFormalization.PartIV.Ch19.coeff_qPochInfPS_pow_three_int_eq_cubeConvolution
#print axioms QseriesFormalization.Pending.Ch19B2.pentagonalSign_cube_convolution_eq_jacobiTripleSign

-- Ramanujan ∀n 5∣p(5n+4) — chapter-main result for Ch17
#print axioms QseriesFormalization.PartIV.Ch17.ramanujan_5_dvd_p_5n_plus_4

-- Ramanujan ∀n 7∣p(7n+5) — second congruence (2026-05-23)
#print axioms QseriesFormalization.Pending.Ch17p7.ramanujan_7_dvd_p_7n_plus_5
#print axioms QseriesFormalization.PartIV.Ch17.jacobiTripleSign_squared_per_term_zero_mod_7

-- Explicit Ramanujan formulas (this session)
#print axioms QseriesFormalization.PartIV.Ch19.coeff_qPochInfPS_pow_p_in_ZMod_p
#print axioms QseriesFormalization.PartIV.Ch19.coeff_qPochInfPS_pow_pred_at_AP

-- Additional Ch20 modular form / Hecke / multiplicativity theorems
#print axioms ramanujanTau_six
#print axioms ramanujanTau_hecke_two_one
#print axioms ramanujanTau_hecke_two_two
#print axioms ramanujanTau_two_mod_two
#print axioms ramanujanTau_three_mod_three
#print axioms ramanujanTau_five_mod_five
#print axioms ramanujanTau_seven_mod_seven
#print axioms discriminantPS_pow_eq_expand
#print axioms etaPS_isUnit
#print axioms discriminantPS_not_isUnit

-- Ch07 Rogers-Ramanujan analytic infrastructure
#print axioms QseriesFormalization.PartII.Ch07.rrJInf_functional_eq
#print axioms QseriesFormalization.PartII.Ch07.rrJInf_zero

-- Ch07 Rogers-Ramanujan IDENTITIES (Schur 1917) — both first and second
#print axioms QseriesFormalization.PartII.Ch07.rogersRamanujan_first
#print axioms QseriesFormalization.PartII.Ch07.rogersRamanujan_second

-- Ch05 Franklin Euler pentagonal (full combinatorial).
-- NOTE: These are in `QseriesFormalization.PartI.Ch05` namespace per the
-- repo's historical numbering, but their content is the Franklin involution
-- proof of Euler pentagonal, which is **Chan §4 combinatorial content**
-- (NOT Chan §5 Boson-Fermion correspondence). See PLAYBOOK_AUDIT.md
-- for the MISLABELED status of Chapter05.lean.
#print axioms QseriesFormalization.PartI.Ch05.franklinInv_involutive
#print axioms QseriesFormalization.PartI.Ch05.franklinInv_card

-- Ch11 golden ratio (Rogers-Ramanujan continued fraction prerequisites)
#print axioms QseriesFormalization.PartIII.Ch11.α_add_β
#print axioms QseriesFormalization.PartIII.Ch11.α_mul_β
#print axioms QseriesFormalization.PartIII.Ch11.α_sq

-- Ch15 q-Taylor / q-calculus.
-- NOTE: These are real q-calculus theorems but they are **NOT** Chan §15's
-- chapter-main result (the differential equation for R(q), Thm 15.1).
-- Chan §15's actual content is missing from the repo; see
-- PLAYBOOK_AUDIT.md for the MISLABELED status of Chapter15.lean.
#print axioms QseriesFormalization.PartIII.Ch15.qDeriv_qPoch
#print axioms QseriesFormalization.PartIII.Ch15.qDerivIter_pow_aux
#print axioms QseriesFormalization.PartIII.Ch15.qTaylorMonomialTopTerm_eq_pow

-- Ch18 t-core / hook lengths (staircase partition theory)
#print axioms QseriesFormalization.PartIV.Ch18.filter_staircasePartition_length
#print axioms QseriesFormalization.PartIV.Ch18.legLength_staircasePartition
#print axioms QseriesFormalization.PartIV.Ch18.hookLength_staircasePartition

-- Ch01 partition counting (foundation)
#print axioms QseriesFormalization.Ch01.partitionCount_zero
#print axioms QseriesFormalization.Ch01.partitionCount_seven
#print axioms QseriesFormalization.Ch01.partitionCount_eleven

-- Ch01: p(12) = 77 and p(13) = 101 via Euler-pentagonal recurrence
-- (2026-05-23, Chapter01_PartitionCount12.lean + _13.lean — formal-PS
-- extraction of the recurrence avoids the partition enumeration that
-- would be required by `decide`)
#print axioms QseriesFormalization.Ch01.partitionCount_twelve
#print axioms QseriesFormalization.Ch01.partitionCount_thirteen
#print axioms QseriesFormalization.Ch01.partitionCount_fourteen
#print axioms QseriesFormalization.Ch01.partitionCount_fifteen
#print axioms QseriesFormalization.Ch01.partitionCount_sixteen
#print axioms QseriesFormalization.Ch01.partitionCount_seventeen
#print axioms QseriesFormalization.Ch01.partitionCount_eighteen
#print axioms QseriesFormalization.Ch01.partitionCount_nineteen
#print axioms QseriesFormalization.Ch01.partitionCount_twenty
#print axioms QseriesFormalization.Ch01.partitionCount_twentyone
#print axioms QseriesFormalization.Ch01.partitionCount_twentytwo
#print axioms QseriesFormalization.Ch01.partitionCount_twentythree
#print axioms QseriesFormalization.Ch01.partitionCount_twentyfour
#print axioms QseriesFormalization.Ch01.partitionCount_twentyfive
#print axioms QseriesFormalization.Ch01.partitionCount_twentysix
#print axioms QseriesFormalization.Ch01.partitionCount_twentyseven
#print axioms QseriesFormalization.Ch01.partitionCount_twentyeight
#print axioms QseriesFormalization.Ch01.partitionCount_twentynine
#print axioms QseriesFormalization.Ch01.partitionCount_thirty
#print axioms QseriesFormalization.Ch01.partitionCount_thirtyone
#print axioms QseriesFormalization.Ch01.partitionCount_thirtytwo
#print axioms QseriesFormalization.Ch01.partitionCount_thirtythree
#print axioms QseriesFormalization.Ch01.partitionCount_thirtyfour
#print axioms QseriesFormalization.Ch01.partitionCount_thirtyfive
#print axioms QseriesFormalization.Ch01.partitionCount_thirtysix
#print axioms QseriesFormalization.Ch01.partitionCount_thirtyseven
#print axioms QseriesFormalization.Ch01.partitionCount_thirtyeight
#print axioms QseriesFormalization.Ch01.partitionCount_thirtynine
#print axioms QseriesFormalization.Ch01.partitionCount_forty
#print axioms QseriesFormalization.Ch01.partitionCount_fortyone
#print axioms QseriesFormalization.Ch01.partitionCount_fortytwo
#print axioms QseriesFormalization.Ch01.partitionCount_fortythree
#print axioms QseriesFormalization.Ch01.partitionCount_fortyfour
#print axioms QseriesFormalization.Ch01.partitionCount_fortyfive
#print axioms QseriesFormalization.Ch01.partitionCount_fortysix
#print axioms QseriesFormalization.Ch01.partitionCount_fortyseven
#print axioms QseriesFormalization.Ch01.partitionCount_fortyeight
#print axioms QseriesFormalization.Ch01.partitionCount_fortynine
#print axioms QseriesFormalization.Ch01.partitionCount_fifty
#print axioms QseriesFormalization.Ch01.partitionCount_fiftyone
#print axioms QseriesFormalization.Ch01.partitionCount_fiftytwo
#print axioms QseriesFormalization.Ch01.partitionCount_fiftythree
#print axioms QseriesFormalization.Ch01.partitionCount_fiftyfour

-- General recurrence helper (Chapter01_RecurrenceGeneral.lean)
#print axioms QseriesFormalization.Ch01.partitionCount_pentagonalSign_convolution_pos

-- k-section operator (Chapter19_Section5.lean) — foundation for MBI / general
-- Ramanujan ∀ n proof, working over (ZMod p)⟦X⟧.
#print axioms QseriesFormalization.PartIV.Ch19.section_kr
#print axioms QseriesFormalization.PartIV.Ch19.coeff_section_kr
#print axioms QseriesFormalization.PartIV.Ch19.section_kr_add
#print axioms QseriesFormalization.PartIV.Ch19.section_kr_expand_eq_zero
#print axioms QseriesFormalization.PartIV.Ch19.section_kr_X_pow_mul_expand
#print axioms QseriesFormalization.PartIV.Ch19.five_smul_eq_zero_in_ZMod_five

-- Section-operator routing to Ramanujan ∀n statement
-- (Chapter17_SectionBridge.lean — only the MBI sorry stands between this
-- iff statement and the unconditional general Ramanujan congruence.)
#print axioms QseriesFormalization.PartIV.Ch17.section_kr_partitionGenFun_eq_zero_iff
#print axioms QseriesFormalization.PartIV.Ch17.ramanujan_congruence_from_section_vanishing

-- Mod-5 residue analysis for the Ramanujan-Watson proof
-- (Chapter17_Mod5ResidueAnalysis.lean)
#print axioms QseriesFormalization.PartIV.Ch17.triangularMod5_range
#print axioms QseriesFormalization.PartIV.Ch17.pentagonalMod5_range
#print axioms QseriesFormalization.PartIV.Ch17.jacobi_coeff_zero_iff
#print axioms QseriesFormalization.PartIV.Ch17.triangular_when_jacobi_nonzero
#print axioms QseriesFormalization.PartIV.Ch17.triangular_plus_pentagonal_ne_four

-- Per-term analysis helpers (Chapter17_PerTermAnalysis.lean) — extract
-- triangular index from nonzero jacobiTripleSign.
#print axioms QseriesFormalization.PartIV.Ch17.jacobiTripleSign_ne_zero_extract
#print axioms QseriesFormalization.PartIV.Ch17.pentagonalSign_ne_zero_extract
#print axioms QseriesFormalization.PartIV.Ch17.triangular_cast_eq_triangularMod5
#print axioms QseriesFormalization.PartIV.Ch17.pentagonalMod5Minus_range
#print axioms QseriesFormalization.PartIV.Ch17.triangular_plus_pentagonalMinus_ne_four
#print axioms QseriesFormalization.PartIV.Ch17.pentagonal_plus_cast_eq_pentagonalMod5
#print axioms QseriesFormalization.PartIV.Ch17.pentagonal_minus_cast_eq_pentagonalMod5Minus

-- **THE per-term residue obstruction**: assembled from all building blocks above
-- (extracts + cast bridges + residue analysis).  This is the key lemma that
-- closes the Finset.sum convolution sorry in Pending/Chapter17_Ramanujan5Conditional.
#print axioms QseriesFormalization.PartIV.Ch17.jacobiPentagonal_per_term_zero_mod_5

-- Ch01 chapter-main: Euler generating function for p(n) (added 2026-05-22
-- via Chapter01_GenFun.lean re-export from Ch19's formal-PS framework)
#print axioms QseriesFormalization.Ch01.coeff_partitionGenFun
#print axioms QseriesFormalization.Ch01.partitionGenFun_eq_euler_product
#print axioms QseriesFormalization.Ch01.euler_factor_geometric

-- Ch09 Bailey pair infrastructure
#print axioms QseriesFormalization.PartII.Ch09.BaileyTerm_zero
#print axioms QseriesFormalization.PartII.Ch09.BaileyBeta_zero_expand

-- Ch08 D_trunc series
#print axioms QseriesFormalization.PartII.Ch08.D_partialSum_zero
#print axioms QseriesFormalization.PartII.Ch08.D_trunc_succ

-- Ch10 mock theta f(q) truncations
#print axioms QseriesFormalization.PartII.Ch10.ramanujanMockF_trunc_one

-- Ch13 deep identity (Chan's Theorem 13.X)
#print axioms QseriesFormalization.PartIII.Ch13.deepIdentityLHSTrunc_succ

-- Ch06 Dedekind eta truncation.
-- NOTE: These lemmas compute `(q;q)_N := ∏ (1-q^k)` for small N; they are
-- correct but they are **NOT** Chan §6's chapter-main result (Macdonald's
-- identity for `η(q)^{t²-1}`, Thm 6.1).  See PLAYBOOK_AUDIT.md for the
-- MISLABELED status of Chapter06.lean.
#print axioms QseriesFormalization.PartI.Ch06.dedekindEtaTrunc_succ
#print axioms QseriesFormalization.PartI.Ch06.dedekindEtaTrunc_one

-- Ch12 RRCF evaluation
-- REMOVED 2026-05-22: `ramanujanRRCFValue_eq` was a `:= rfl` lemma over the
-- placeholder definition `ramanujanRRCFValue := α⁻¹ + β`, both of which have
-- been deleted from Chapter12.lean.  Ch12's true chapter-main-result (RRCF
-- convergence/evaluation) is not yet formalized; see TODO_THEOREMS.md #17.

-- Ch16 MBI (Macdonald-Bailey identity) truncation
#print axioms QseriesFormalization.PartIV.Ch16.mbiLHSTrunc_one
#print axioms QseriesFormalization.PartIV.Ch16.mbiLHSTrunc_two

-- ============================================================================
-- Book-wide flagship theorems (across chapters)
-- ============================================================================

-- Ch03 (in Ch02 namespace per Mathlib-style export): Jacobi Triple Product
#print axioms QseriesFormalization.PartI.Ch02.jacobiTripleProduct

-- Ch03: Finite Jacobi Triple Product (purely algebraic)
#print axioms QseriesFormalization.PartI.Ch03.finite_jacobi_triple_product

-- Ch03: q-Binomial Theorem (Chan's form)
#print axioms QseriesFormalization.PartI.Ch03.qBinomialTheorem_chanForm

-- Ch04: Euler Pentagonal infinite product = tsum
#print axioms QseriesFormalization.PartI.Ch04.eulerPentagonalInfiniteProduct_eq_tsum

-- Ch04: Quintuple Product Identity
#print axioms QseriesFormalization.PartI.Ch04.quintupleProduct_identity

-- Ch04 T4.3: Jacobi's identity (qPoch^3 = theta-series)
#print axioms QseriesFormalization.PartI.Ch04.jacobiIdentity

-- Ch17 chapter-main: conditional general Ramanujan (added 2026-05-22)
#print axioms QseriesFormalization.PartIV.Ch17.ramanujan_congruence_general

-- Ch17: Specific finite Ramanujan partition congruences
#print axioms QseriesFormalization.PartIV.Ch17.partition_four_dvd_five
#print axioms QseriesFormalization.PartIV.Ch17.partition_six_dvd_eleven
#print axioms QseriesFormalization.PartIV.Ch17.partition_5n_plus_4_mod_5_n_zero
#print axioms QseriesFormalization.PartIV.Ch17.partition_5n_plus_4_mod_5_n_one
#print axioms QseriesFormalization.PartIV.Ch17.partition_7n_plus_5_mod_7_n_zero
#print axioms QseriesFormalization.PartIV.Ch17.partition_11n_plus_6_mod_11_n_zero
#print axioms QseriesFormalization.PartIV.Ch17.partition_nine_dvd_five
#print axioms QseriesFormalization.PartIV.Ch17.partition_five_dvd_seven

-- Ch17: Ramanujan congruences at higher n (2026-05-23, Chapter17_HigherCases.lean,
-- using new partitionCount 12..22 values)
#print axioms QseriesFormalization.PartIV.Ch17.partition_5n_plus_4_mod_5_n_two
#print axioms QseriesFormalization.PartIV.Ch17.partition_5n_plus_4_mod_5_n_three
#print axioms QseriesFormalization.PartIV.Ch17.partition_7n_plus_5_mod_7_n_one
#print axioms QseriesFormalization.PartIV.Ch17.partition_7n_plus_5_mod_7_n_two
#print axioms QseriesFormalization.PartIV.Ch17.partition_11n_plus_6_mod_11_n_one
#print axioms QseriesFormalization.PartIV.Ch17.partition_5n_plus_4_mod_5_n_four
#print axioms QseriesFormalization.PartIV.Ch17.partition_7n_plus_5_mod_7_n_three
#print axioms QseriesFormalization.PartIV.Ch17.partition_11n_plus_6_mod_11_n_two
#print axioms QseriesFormalization.PartIV.Ch17.partition_5n_plus_4_mod_5_n_five
#print axioms QseriesFormalization.PartIV.Ch17.partition_7n_plus_5_mod_7_n_four
#print axioms QseriesFormalization.PartIV.Ch17.partition_11n_plus_6_mod_11_n_three
#print axioms QseriesFormalization.PartIV.Ch17.partition_5n_plus_4_mod_5_n_six
#print axioms QseriesFormalization.PartIV.Ch17.partition_5n_plus_4_mod_5_n_seven
#print axioms QseriesFormalization.PartIV.Ch17.partition_7n_plus_5_mod_7_n_five
#print axioms QseriesFormalization.PartIV.Ch17.partition_5n_plus_4_mod_5_n_eight
#print axioms QseriesFormalization.PartIV.Ch17.partition_7n_plus_5_mod_7_n_six
#print axioms QseriesFormalization.PartIV.Ch17.partition_11n_plus_6_mod_11_n_four
#print axioms QseriesFormalization.PartIV.Ch17.partition_5n_plus_4_mod_5_n_nine
#print axioms QseriesFormalization.PartIV.Ch17.partition_5n_plus_4_mod_5_n_ten
#print axioms QseriesFormalization.PartIV.Ch17.partition_7n_plus_5_mod_7_n_seven

-- Ch20: Ramanujan tau values + congruences (this session)
#print axioms ramanujanTau_one
#print axioms ramanujanTau_two
#print axioms ramanujanTau_three
#print axioms ramanujanTau_mul_two_three
#print axioms ramanujan_partition_four_mod_five
#print axioms ramanujan_partition_five_mod_seven
#print axioms ramanujan_partition_six_mod_eleven

-- Ch14: Crank statistic verification
#print axioms QseriesFormalization.PartIII.Ch14.crank_singleton

-- Ch14 chapter-main (n = 0 case): crank surjects onto ZMod 5 for partitions of 4
-- (added 2026-05-23 in Chapter14_CrankN4.lean)
#print axioms QseriesFormalization.PartIII.Ch14.crank_partitionFourThreeOne
#print axioms QseriesFormalization.PartIII.Ch14.crank_partitionFourTwoTwo
#print axioms QseriesFormalization.PartIII.Ch14.crank_partitionFourTwoOneOne
#print axioms QseriesFormalization.PartIII.Ch14.crank_n4_surjective_mod_five

-- Ch06 chapter-main (t = 2 / affine A₁ case): Macdonald's identity = Jacobi's identity
-- (added 2026-05-24 in Pending/Chapter06_Macdonald_A1.lean)
#print axioms QseriesFormalization.Pending.Ch06Macdonald.macdonald_A1_identity
#print axioms QseriesFormalization.Pending.Ch06Macdonald.coeff_macdonald_A1_triangular

-- Ch05 chapter-main: Jacobi Triple Product (Chan §5's main theorem)
-- (re-export 2026-05-24 in Pending/Chapter05_JTP.lean; proved via finite-JTP, not Boson-Fermion)
#print axioms QseriesFormalization.Pending.Ch05JTP.jacobi_triple_product

-- Ch17 mod-11: Hirschhorn §3.5 combination identity (algebraic core, 2026-05-24)
-- P = Σ M_r R_r over any char-11 ring (Hirschhorn's "left as an exercise")
#print axioms QseriesFormalization.Pending.HirschhornComb.hirschhorn_P_eq_combination

-- Ch17 mod-11 HEADLINE: Ramanujan's third congruence, fully closed 2026-05-24
-- (extraction by codex/gpt-5.5 on the-build-server; combination identity above).
#print axioms QseriesFormalization.Pending.Hirschhorn11.ramanujan_11_dvd_p_11n_plus_6

-- Ch20: Ramanujan's tau parity theorem (2026-05-24)
#print axioms QseriesFormalization.Pending.TauParity.ramanujanTau_odd_iff_odd_square
-- Ch20 τ values τ(9)..τ(13) + multiplicativity τ(10)=τ(2)τ(5) (consolidated in Chapter20.lean)
#print axioms QseriesFormalization.PartIV.Ch20.ramanujanTau_thirteen
#print axioms QseriesFormalization.PartIV.Ch20.ramanujanTau_ten_eq
-- Ch20 τ(14),τ(15) + multiplicativity τ(14)=τ(2)τ(7), τ(15)=τ(3)τ(5) (consolidated in Chapter20.lean)
#print axioms QseriesFormalization.PartIV.Ch20.ramanujanTau_fifteen_eq
#print axioms QseriesFormalization.PartIV.Ch20.ramanujanTau_fourteen_eq
-- Ch20 τ(16)..τ(21) extension + multiplicativity τ(21)=τ(3)τ(7), τ(18)=τ(2)τ(9) (2026-05-26)
#print axioms QseriesFormalization.PartIV.Ch20.ramanujanTau_twentyone
#print axioms QseriesFormalization.PartIV.Ch20.ramanujanTau_twentyone_eq
#print axioms QseriesFormalization.PartIV.Ch20.ramanujanTau_eighteen_eq
#print axioms QseriesFormalization.PartIV.Ch20.ramanujanTau_twentytwo_eq
#print axioms QseriesFormalization.PartIV.Ch20.ramanujanTau_thirtythree_eq
-- Ch20 Hecke recursion at prime powers (2026-05-27):
-- τ(p^{k+1}) = τ(p)·τ(p^k) - p^{11}·τ(p^{k-1}). The general Hecke property is
-- open (full Δ modularity), but each instance is unconditional arithmetic.
#print axioms QseriesFormalization.PartIV.Ch20.ramanujanTau_hecke_two_three
#print axioms QseriesFormalization.PartIV.Ch20.ramanujanTau_hecke_two_four
#print axioms QseriesFormalization.PartIV.Ch20.ramanujanTau_hecke_three_one
#print axioms QseriesFormalization.PartIV.Ch20.ramanujanTau_hecke_three_two
#print axioms QseriesFormalization.PartIV.Ch20.ramanujanTau_hecke_five_one
#print axioms QseriesFormalization.PartIV.Ch20.ramanujanTau_thirtyfour_eq
#print axioms QseriesFormalization.PartIV.Ch20.ramanujanTau_thirtyfive_eq
#print axioms QseriesFormalization.PartIV.Ch20.ramanujanTau_twenty_eq
#print axioms QseriesFormalization.PartIV.Ch20.ramanujanTau_twentyfour_eq
#print axioms QseriesFormalization.PartIV.Ch20.ramanujanTau_twelve_eq
#print axioms QseriesFormalization.PartIV.Ch20.ramanujanTau_twentysix_eq
#print axioms QseriesFormalization.PartIV.Ch20.ramanujanTau_twentyeight_eq
#print axioms QseriesFormalization.PartIV.Ch20.ramanujanTau_thirty_eq
#print axioms QseriesFormalization.PartIV.Ch20.ramanujanTau_thirty_eq'

-- Ch14: crank n=1 surjectivity mod 5 (2026-05-24)
#print axioms QseriesFormalization.PartIII.Ch14.crank_n9_surjective_mod_five
-- Ch14 chapter-main (n = 2 case): crank surjects onto ZMod 5 for partitions of 14 (Chapter14_CrankN14.lean)
#print axioms QseriesFormalization.PartIII.Ch14.crank_n14_surjective_mod_five
#print axioms QseriesFormalization.PartIII.Ch14.crank_n19_surjective_mod_five
#print axioms QseriesFormalization.PartIII.Ch14.crank_n24_surjective_mod_five
#print axioms QseriesFormalization.PartIII.Ch14.crank_n29_surjective_mod_five
#print axioms QseriesFormalization.PartIII.Ch14.crank_n34_surjective_mod_five

-- Mod-3 sign-sequence identity (2026-05-24)
#print axioms QseriesFormalization.Pending.SignMod3.jacobiTripleSign_mod3

-- Parallel codex wave 1 (2026-05-24): ASD mod-5/7, Ch08 finite RR, MBI partial
#print axioms QseriesFormalization.Pending.ASDMod5.qPochInfPS_cube_decompose_mod_5
#print axioms QseriesFormalization.Pending.ASDMod5.ramanujan_5_dvd_p_5n_plus_4
#print axioms QseriesFormalization.Pending.Hirschhorn7.qPochInfPS_cube_decompose_mod_7
#print axioms QseriesFormalization.PartII.Ch08.EFinite_recurrence
#print axioms QseriesFormalization.Pending.Ch16MBIProof.qPochInfPS_five_dissection
#print axioms QseriesFormalization.Pending.Ch16MBIProof.E5_zero_mul_two_eq_neg_one_sq_rat

-- Parallel codex wave 2 (2026-05-24): MBI (5.3.2) full, Ch08 uniqueness bridge, ASD-5 full sections
#print axioms QseriesFormalization.Pending.Ch16MBIProof.E5_one_eq_neg_X_mul_expand_twentyfive_qPochInfPS
#print axioms QseriesFormalization.Pending.Ch16MBIProof.E5_bracket_collapse_rat
#print axioms QseriesFormalization.PartII.Ch08.second_order_recurrence_unique
#print axioms QseriesFormalization.Pending.ASDMod5Full.partition_5n_plus_4_eq_zero_mod_5
#print axioms QseriesFormalization.Pending.ASDMod5Full.partitionGenFun_mul_D5_sq_eq_S5_cube

-- Parallel codex wave 3 (2026-05-24): Ch08 Thm 8.1 (a=0,1), MBI residue-4, ASD-7 full
#print axioms QseriesFormalization.PartII.Ch08.EFinite_eq_DFinite_a0
#print axioms QseriesFormalization.PartII.Ch08.EFinite_eq_DFinite_a1
#print axioms QseriesFormalization.Pending.ASDMod7Full.partition_7n_plus_5_eq_zero_mod_7
#print axioms QseriesFormalization.Pending.ASDMod7Full.partitionGenFun_mul_D7_eq_S7_sq

-- Wave 4 (2026-05-24): MBI conditional reduction + Ch08 a≤2 (with a≥2 counterexamples)
#print axioms QseriesFormalization.Pending.Ch16MBIProof.most_beautiful_identity_of_denominator_rationalization
#print axioms QseriesFormalization.PartII.Ch08.DFinite_recurrence_of_a_le_two
#print axioms QseriesFormalization.PartII.Ch08.DFinite_recurrence_fails_a3_at_zero

-- Infra moonshots (2026-05-24): MBI reduced to explicit denominator identity; JTP formal-PS scaffold
#print axioms QseriesFormalization.Pending.Ch16MBIProof.most_beautiful_identity_of_E5_denominator_identity
#print axioms QseriesFormalization.Pending.JTPFormalPSPentagonal.pentagonalProduct014PS_eq_tprod
#print axioms QseriesFormalization.Pending.JTPFormalPSPentagonal.analytic_pentagonal014_eq_mod5_product

-- KEYSTONE (2026-05-24): JTP product=series formal-PS equalities (bilateral bridge closed)
#print axioms QseriesFormalization.Pending.JTPFormalPSPentagonal.pentagonalProduct014PS_eq_pentagonal014SeriesPS_complex
#print axioms QseriesFormalization.Pending.JTPFormalPSPentagonal.pentagonalProduct023PS_eq_pentagonal023SeriesPS_complex
-- ASD eta-products: F,G mod-25 product=theta (Hirschhorn 3.6.5)
#print axioms QseriesFormalization.Pending.ASDEtaProducts.asd5FProductPS_eq_asd5FSeriesPS_complex
#print axioms QseriesFormalization.Pending.ASDEtaProducts.asd5GProductPS_eq_asd5GSeriesPS_complex
-- ASD mod-5 UNCONDITIONAL eta-quotient congruences (Hirschhorn 3.6.7): A0=F, A1=-3qG over ZMod 5
#print axioms QseriesFormalization.Pending.ASDEtaProducts.A0_eq_asd5FProductPS_zmod5
#print axioms QseriesFormalization.Pending.ASDEtaProducts.partition_section_0_eq_eta_product
#print axioms QseriesFormalization.Pending.ASDEtaProducts.partition_section_3_eq_eta_product
-- mod-7 keystone + H,J,K eta-products (Hirschhorn 3.7.2) + ASD-7 eta-quotient congruences (3.7)
#print axioms QseriesFormalization.Pending.JTPFormalPSMod7.asd7HProductPS_eq_asd7HSeriesPS_complex
#print axioms QseriesFormalization.Pending.ASDMod7EtaQuotient.ASD7_0_eq_asd7HProductPS_zmod7
#print axioms QseriesFormalization.Pending.ASDMod7EtaQuotient.partition_section_6_eq_eta_product
-- MBI: pentagonal AP-product factorisation (MBI reduced to the Ramanujan quintic)
#print axioms QseriesFormalization.Pending.Ch16MBIProof.pentagonalProduct014_mul_pentagonalProduct023_eq_qPochInfPS_mul_expand_five_qPochInfPS_rat
-- Ramanujan quintic infra: scaleX ring hom + 5th-root product collapse (toward core·P5 = E^11)
#print axioms QseriesFormalization.Pending.RamanujanQuintic.scaleX_qPochFinitePS
#print axioms QseriesFormalization.Pending.RamanujanQuintic.quinticCyclotomic_qPochFinitePS_fifth_collapse
-- JTP-at-η (Hirschhorn §8.3) scaffolding: book α/β reconciliation + 5th-power linear collapse
#print axioms QseriesFormalization.Pending.RamanujanQuinticJTP.prod_sub_scaled_primitive_fifth_powerSeries
#print axioms QseriesFormalization.Pending.RamanujanQuinticJTP.quintic_factor_pair_mul_eq_core_of_book_periods
-- JTP-at-η round 2: product-side dominated-convergence analytic→formal transfer + conditional factor-identity bridge
#print axioms QseriesFormalization.Pending.RamanujanQuinticJTP.hasFPowerSeriesOnBall_section83JTPProductAnalytic_productCoeff_small
#print axioms QseriesFormalization.Pending.RamanujanQuinticJTP.section83JTPProductPS_eq_rhs_pair14_of_rhs_taylor
-- JTP-at-η round 4: η-period collapse + UNCONDITIONAL §8.3 factor identities (8.3.1)/(8.3.2)
#print axioms QseriesFormalization.Pending.RamanujanQuinticJTP.section83JTPProductPS_eq_rhs_pair14
#print axioms QseriesFormalization.Pending.RamanujanQuinticJTP.section83JTPProductPS_eq_rhs_pair23
-- *** UNCONDITIONAL Ramanujan Most Beautiful Identity (Chan §16) ***  ∑p(5n+4)qⁿ = 5(q⁵;q⁵)⁵/(q;q)⁶
#print axioms QseriesFormalization.Pending.RamanujanQuinticJTP.prod_scaleX_qPochInfPS_fifth_collapse_complex
#print axioms QseriesFormalization.Pending.RamanujanQuinticJTP.most_beautiful_identity
-- Chan Thm 8.1 (finite Rogers-Ramanujan, a=0,1 = Chan's exact statement)
#print axioms QseriesFormalization.PartII.Ch08.chan_theorem_8_1_a0
#print axioms QseriesFormalization.PartII.Ch08.chan_theorem_8_1_a1
-- Ch14 crank generating function infra + Andrews-Garvan at z=1 (partial; full arbitrary-z open)
#print axioms QseriesFormalization.PartIII.Ch14.andrewsGarvanCrankIdentity_at_one
-- Ch14 Thm 11.6 (Lost Notebook) partial: LHS·section83 = (qPoch)² via JTP-at-ζ; full Thm reduced to RR-product blocker
#print axioms QseriesFormalization.PartIII.Ch14Thm116.chan116LHS_mul_section83_rhs_pair14
-- Ch14 Thm 11.6 (Lost Notebook, Andrews-Berndt top-10 #3) CLOSED unconditionally + hE0 (compressed_E5_zero_bridge) proven
#print axioms QseriesFormalization.PartIII.Ch14Thm116.chan116_theorem_11_6
#print axioms QseriesFormalization.Pending.Ch16MBIProof.compressed_E5_zero_bridge
-- Ch9 Bailey lemma partial: Lemma 9.1 coeff identity (Eq 9.10) + x=1 finite cases. (fullBaileyTransform_* are CONDITIONAL on unproven q-Pfaff-Saalschütz kernel — not unconditional Bailey lemma.)
#print axioms QseriesFormalization.PartII.Ch09.lemma91_matrix_entry_shifted
#print axioms QseriesFormalization.PartII.Ch09.theorem91_x_one_two
-- Ch9 UNCONDITIONAL Bailey's lemma (Thm 9.1/9.2) via Fubini reindex of lemma91_matrix_entry_shifted (NO kernel) — chapter-main
#print axioms QseriesFormalization.PartII.Ch09.lemma91_operator
#print axioms QseriesFormalization.PartII.Ch09.theorem91
#print axioms QseriesFormalization.PartII.Ch09.theorem92
-- Ch5 Boson-Fermion: finite evaluations + INFINITE fermionic Z=fermionicProduct + corrected JTP (1+z⁻¹)Z·bosonEuler=∑z^n q^{n(n+1)/2}
#print axioms QseriesFormalization.PartI.Ch05.finiteZ_eq_fermionicProductPartial
#print axioms QseriesFormalization.PartI.Ch05.finiteZ_eq_sum_zpow_chargeEnergySectors
#print axioms QseriesFormalization.PartI.Ch05.Z_eq_fermionicProduct
#print axioms QseriesFormalization.PartI.Ch05.bosonFermion_JTP
-- MBI: keystone lifted to ℚ + conditional full-MBI via product bridges
#print axioms QseriesFormalization.Pending.Ch16MBIProof.most_beautiful_identity_of_mod5_product_bridges

-- Ch13 RRCF foundation (2026-05-26): well-definedness of r(q) = R(q)/q^{1/5}
-- as a formal power series, via constant-coefficient = 1 of denominator
-- (q²,q³,q⁵;q⁵)_∞ and the PowerSeries inverse machinery. Prerequisite for
-- any future closure of Chan's "deep and difficult" identity (Thm 11.5,
-- Gugg telescoping). Does NOT close Ch13's chapter-main result.
#print axioms QseriesFormalization.Pending.Ch13RRCF.coeff_zero_pentagonal023SeriesPS_rat
#print axioms QseriesFormalization.Pending.Ch13RRCF.coeff_zero_pentagonal014SeriesPS_rat
#print axioms QseriesFormalization.Pending.Ch13RRCF.pentagonal014Exp_one
#print axioms QseriesFormalization.Pending.Ch13RRCF.pentagonal023Exp_zero
#print axioms QseriesFormalization.Pending.Ch13RRCF.isUnit_pentagonal023SeriesPS_rat
#print axioms QseriesFormalization.Pending.Ch13RRCF.constantCoeff_pentagonal023SeriesPS_rat_ne_zero
#print axioms QseriesFormalization.Pending.Ch13RRCF.rrcf_r_mul_pentagonal023SeriesPS_eq
#print axioms QseriesFormalization.Pending.Ch13RRCF.coeff_zero_rrcf_v_eq_zero
#print axioms QseriesFormalization.Pending.Ch13RRCF.rrcf_v_mul_expand_pentagonal023SeriesPS_eq
#print axioms QseriesFormalization.Pending.Ch13RRCF.isUnit_rrcfDenomLHS
#print axioms QseriesFormalization.Pending.Ch13RRCF.isUnit_rrcfDenomRHS
-- Ch13: first coefficient-wise verification of Chan Thm 11.5 (constant term)
#print axioms QseriesFormalization.Pending.Ch13RRCF.coeff_zero_rrcf_r
#print axioms QseriesFormalization.Pending.Ch13RRCF.coeff_zero_chan_theorem_11_5_LHS_eq_RHS

-- Ch10 mock theta f(q) formal-power-series foundation (2026-05-26, SHADOW->AUX).
-- Ramanujan's f(q) = ∑ q^{n²}/(-q;q)_n² over ℚ⟦X⟧: summand definition,
-- partial sum + recursion, constant coefficient = 1.
#print axioms QseriesFormalization.Pending.Ch10MockThetaPS.ramanujanMockSummandPS_zero
#print axioms QseriesFormalization.Pending.Ch10MockThetaPS.coeff_zero_ramanujanMockSummandPS_of_pos
#print axioms QseriesFormalization.Pending.Ch10MockThetaPS.ramanujanMockFPartialPS_zero
#print axioms QseriesFormalization.Pending.Ch10MockThetaPS.ramanujanMockFPartialPS_succ
#print axioms QseriesFormalization.Pending.Ch10MockThetaPS.coeff_zero_ramanujanMockFPartialPS

-- Ch11 correct RRCF convergents (2026-05-26): the existing Chapter11.R_trunc
-- is degenerate (q^k on the outside vanishes as k→∞); this introduces the
-- standard backward-recurrence convergents A_n/B_n that have q^k inside.
-- Chapter-main result (T_n → R(q)/q^{1/5}) remains open.
#print axioms QseriesFormalization.Pending.Ch11RRCFConvergent.rrcf_A_two
#print axioms QseriesFormalization.Pending.Ch11RRCFConvergent.rrcf_B_two
#print axioms QseriesFormalization.Pending.Ch11RRCFConvergent.rrcf_A_three
#print axioms QseriesFormalization.Pending.Ch11RRCFConvergent.rrcf_B_three
-- Ch11 formal-PS RRCF convergents (2026-05-27, corrected base cases per Chan §11):
-- lifts from ℂ→ℂ to ℚ⟦X⟧ for X-adic convergence statements.
#print axioms QseriesFormalization.Pending.Ch11RRCFConvergent.constantCoeff_rrcf_APS
#print axioms QseriesFormalization.Pending.Ch11RRCFConvergent.constantCoeff_rrcf_BPS
#print axioms QseriesFormalization.Pending.Ch11RRCFConvergent.isUnit_rrcf_BPS
#print axioms QseriesFormalization.Pending.Ch11RRCFConvergent.rrcf_TPS_zero
-- Ch11 CF cross-determinant identity (2026-05-27):
-- A_{n+1}·B_n − A_n·B_{n+1} = (−1)^n · X^{(n+1)(n+2)/2}.
-- Bridge to X-adic convergence (key step toward Chan §11 Theorem 11.1).
#print axioms QseriesFormalization.Pending.Ch11RRCFConvergent.rrcf_cross_det_PS
#print axioms QseriesFormalization.Pending.Ch11RRCFConvergent.rrcf_TPS_succ_diff_mul
-- Ch11 correct r-convergent R_n := B_n/A_n (which converges to r(q));
-- T_n = A_n/B_n converges to 1/r(q). Both have same X-adic stabilization rate.
#print axioms QseriesFormalization.Pending.Ch11RRCFConvergent.rrcf_RPS_zero
#print axioms QseriesFormalization.Pending.Ch11RRCFConvergent.rrcf_RPS_succ_diff_mul
-- X-adic divisibility estimates: directly give Cauchy-ness of T_n and R_n.
#print axioms QseriesFormalization.Pending.Ch11RRCFConvergent.X_pow_triangular_dvd_rrcf_TPS_succ_diff
#print axioms QseriesFormalization.Pending.Ch11RRCFConvergent.X_pow_triangular_dvd_rrcf_RPS_succ_diff
-- Coefficient stabilization (X-adic Cauchy in concrete form):
-- for n ≥ k, (rrcf_TPS (n+1)).coeff k = (rrcf_TPS n).coeff k.
#print axioms QseriesFormalization.Pending.Ch11RRCFConvergent.rrcf_TPS_succ_coeff_eq_of_le
#print axioms QseriesFormalization.Pending.Ch11RRCFConvergent.rrcf_RPS_succ_coeff_eq_of_le
-- The X-adic limit r(q) defined via the CF convergents (Chan §11 Theorem 11.1 LHS).
#print axioms QseriesFormalization.Pending.Ch11RRCFConvergent.rrcf_RPS_coeff_eq_of_le
#print axioms QseriesFormalization.Pending.Ch11RRCFConvergent.coeff_rrcf_r_via_CF
#print axioms QseriesFormalization.Pending.Ch11RRCFConvergent.coeff_rrcf_r_via_CF_of_le
#print axioms QseriesFormalization.Pending.Ch11RRCFConvergent.coeff_zero_rrcf_r_via_CF
#print axioms QseriesFormalization.Pending.Ch11RRCFConvergent.rrcf_RPS_one
#print axioms QseriesFormalization.Pending.Ch11RRCFConvergent.rrcf_APS_two
#print axioms QseriesFormalization.Pending.Ch11RRCFConvergent.rrcf_BPS_two
#print axioms QseriesFormalization.Pending.Ch11RRCFConvergent.rrcf_RPS_two
#print axioms QseriesFormalization.Pending.Ch11RRCFConvergent.coeff_one_rrcf_r_via_CF
-- Cross-chapter X^0 match (Ch11 CF limit ↔ Ch13 product form, Chan §11 Thm 11.1 at degree 0):
#print axioms QseriesFormalization.Pending.Ch11RRCFConvergent.coeff_zero_rrcf_r_via_CF_eq_rrcf_r
#print axioms QseriesFormalization.Pending.Ch11RRCFConvergent.rrcf_APS_three
#print axioms QseriesFormalization.Pending.Ch11RRCFConvergent.rrcf_BPS_three
#print axioms QseriesFormalization.Pending.Ch11RRCFConvergent.rrcf_RPS_three

-- Ch12 Ramanujan special value (2026-05-26): R(e^{-2π}) target as a real number.
-- Chan §12 chapter-main equality remains open (needs Ch11 CF convergence + special-value evaluation).
#print axioms QseriesFormalization.Pending.Ch12SpecialValue.ramanujanRRCFSpecialValue

-- ============================================================================
-- Ch15 CHAPTER-MAIN — Chan §15 / Theorem 11.7 (the Rogers–Ramanujan continued
-- fraction differential equation), closed 2026-06-03 via Dobbie's identity proved
-- by the Gaussian-5-string telescoping (the S(5M)=-6S(M)-25S(M/5) recurrence).
-- All clean-three, independently #print-axioms-verified on rebuilt oleans.
-- ============================================================================
-- Dobbie's identity (the deep crux): pentagonal Wronskian coeff = Jacobi-theta-square coeff.
#print axioms QseriesFormalization.Pending.Ch15WronskianIndependent.pentagonalWronskianCoeff_eq_jacobiThetaSquareCoeff
-- Unconditional Wronskian = (q;q)_∞^6  (= Jacobi Θ², via the proved Dobbie identity).
#print axioms QseriesFormalization.Pending.Ch15WronskianIndependent.wronskian_at_pentagonal_level
-- Chapter-main content: the quintuple-product logarithmic-derivative factor equals
-- (q;q)_∞^5 / (q^5;q^5)_∞, i.e. Chan Eq. 15.8 / Thm 11.7 (the RRCF differential equation).
#print axioms QseriesFormalization.Pending.Ch15WronskianIndependent.quintupleProduct_log_derivative_identity
#print axioms QseriesFormalization.Pending.Ch15WronskianIndependent.quintupleLogFactor_eq_apSigmaLambertFactor
-- Chan §15 / Theorem 11.7 in its faithful ring-general form (closed 2026-06-03):
--   chan15LHSPS R * expand 5 (qPochInfPS R) = (qPochInfPS R)^5  for every CommRing R.
#print axioms QseriesFormalization.Pending.Ch15RODE.chan_theorem_11_7

end QseriesFormalization.Audit

-- Ch10: Chan Eq 10.15 (tenth-order mock theta) via the source route (TwoVar + Bridge, 2026-06-05)
#print axioms QseriesFormalization.Pending.Ch10Bridge.chan1015
#print axioms QseriesFormalization.Ch10TwoVar.chan_eq_10_15_CTxy
#print axioms QseriesFormalization.Ch10TwoVar.zwegers_lemma_10_1_x
#print axioms QseriesFormalization.Ch10TwoVar.hickerson_mul
