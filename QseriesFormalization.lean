-- Root library module.
import QseriesFormalization.Basic
import QseriesFormalization.Chapter01
import QseriesFormalization.Chapter02
import QseriesFormalization.Chapter03
import QseriesFormalization.Chapter04
import QseriesFormalization.Chapter04_FranklinPentagonal
import QseriesFormalization.Chapter05_Franklin
import QseriesFormalization.Chapter05_BosonFermion  -- §5 Boson-Fermion finite evaluations
import QseriesFormalization.Chapter06
import QseriesFormalization.Chapter07
import QseriesFormalization.Chapter07_RRStep1
import QseriesFormalization.Chapter07_RRStep1H
import QseriesFormalization.Chapter07_RRStep5
import QseriesFormalization.Chapter07_RRStep5H
import QseriesFormalization.Chapter08
import QseriesFormalization.Chapter09
import QseriesFormalization.Chapter09_BaileyLemma  -- Bailey lemma: L/M/D operators + Lemma 9.1 coeff identity + x=1 finite cases
-- import QseriesFormalization.BaileyqPS  -- scratch file, not in build graph (see file header)
import QseriesFormalization.Chapter10
import QseriesFormalization.Chapter11
import QseriesFormalization.Chapter12
import QseriesFormalization.Chapter13
import QseriesFormalization.Chapter14
import QseriesFormalization.QCalculus
import QseriesFormalization.Chapter16
import QseriesFormalization.Chapter17
import QseriesFormalization.Chapter18
import QseriesFormalization.Chapter19
import QseriesFormalization.Chapter19_Section5
import QseriesFormalization.Chapter19_JacobiTripleSignChar
import QseriesFormalization.Pending.JacobiCubeAnalyticToFormal
import QseriesFormalization.Pending.Chapter17_Ramanujan5Conditional
import QseriesFormalization.Pending.Chapter19_B2_FromCubeConvolution
import QseriesFormalization.Pending.Sylvester_TripleSum
import QseriesFormalization.Pending.RamanujanTau_via_B2
import QseriesFormalization.Pending.Chapter17_Ramanujan7
import QseriesFormalization.Pending.Chapter17_Ramanujan11_PartialDecide
import QseriesFormalization.Pending.Chapter17_Hirschhorn_Mod11
import QseriesFormalization.Pending.Chapter06_Macdonald_A1
import QseriesFormalization.Pending.Chapter05_JTP
import QseriesFormalization.Pending.Chapter17_Hirschhorn_Combination
import QseriesFormalization.Pending.Chapter20_TauParity
import QseriesFormalization.Pending.SignSequences_Mod3
import QseriesFormalization.Chapter14_CrankN9
import QseriesFormalization.Pending.Chapter17_ASD_Mod5
import QseriesFormalization.Pending.Chapter17_ASD_Mod7
import QseriesFormalization.Pending.Chapter08_FiniteRR
import QseriesFormalization.Pending.Chapter08_Gaussian  -- Chan Thm 8.1 (a=0,1) named exposure
import QseriesFormalization.Pending.Chapter16_MBI_Proof
import QseriesFormalization.Pending.Chapter17_ASD_Mod5_Full
import QseriesFormalization.Pending.Chapter17_ASD_Mod7_Full
import QseriesFormalization.Pending.JTP_FormalPS_Pentagonal
import QseriesFormalization.Pending.ASD_EtaProducts
import QseriesFormalization.Pending.JTP_FormalPS_Mod7
import QseriesFormalization.Pending.ASD_Mod7_EtaQuotient
import QseriesFormalization.Pending.RamanujanQuintic
import QseriesFormalization.Pending.RamanujanQuinticJTP
import QseriesFormalization.Pending.Chapter13_RRCF_RForm  -- Ch13 r(q) foundation (fractional-power-free RRCF)
import QseriesFormalization.Pending.Chapter10_MockTheta_PS  -- Ch10 mock theta f(q) as formal power series
import QseriesFormalization.Pending.Chapter11_RRCF_Convergent  -- Ch11 correct RRCF convergents (backward recurrence)
import QseriesFormalization.Pending.Chapter12_SpecialValue  -- Ch12 Ramanujan special value R(e^{-2π})
import QseriesFormalization.Chapter20  -- Δ/τ values through 50 + Hecke/parity checks
import QseriesFormalization.Chapter20_Ono  -- Ono-style Theorem 20.1 statement + closed 5/7/11 infinite AP cases
import QseriesFormalization.Chapter17_SectionBridge
import QseriesFormalization.Chapter17_Mod5ResidueAnalysis
import QseriesFormalization.Chapter17_PerTermAnalysis
import QseriesFormalization.Chapter17_Mod7PerTermAnalysis
import QseriesFormalization.Chapter17_Mod11PerTermAnalysis
import QseriesFormalization.Chapter01_GenFun  -- after Ch19; exposes Ch01 chapter-main theorem
import QseriesFormalization.Chapter01_PartitionCount12  -- p(12) = 77 via Euler pentagonal recurrence
import QseriesFormalization.Chapter01_PartitionCount13  -- p(13) = 101 via same framework
import QseriesFormalization.Chapter01_PartitionCount14  -- p(14) = 135
import QseriesFormalization.Chapter01_PartitionCount15  -- p(15) = 176 (pentagonal σ(15) = -1)
import QseriesFormalization.Chapter01_PartitionCount16  -- p(16) = 231
import QseriesFormalization.Chapter01_PartitionCount17  -- p(17) = 297
import QseriesFormalization.Chapter01_RecurrenceGeneral  -- general recurrence helper
import QseriesFormalization.Chapter01_PartitionCount18  -- p(18) = 385 (first to use general helper)
import QseriesFormalization.Chapter01_PartitionCount19  -- p(19) = 490
import QseriesFormalization.Chapter01_PartitionCount20  -- p(20) = 627
import QseriesFormalization.Chapter01_PartitionCount21  -- p(21) = 792
import QseriesFormalization.Chapter01_PartitionCount22  -- p(22) = 1002 (pentagonal σ(22) = +1)
import QseriesFormalization.Chapter01_PartitionCount23  -- p(23) = 1255
import QseriesFormalization.Chapter01_PartitionCount24  -- p(24) = 1575 (enables 5∣p(24) at n=4)
import QseriesFormalization.Chapter01_PartitionCount25  -- p(25) = 1958
import QseriesFormalization.Chapter01_PartitionCount26  -- p(26) = 2436 (pentagonal σ(26) = +1)
import QseriesFormalization.Chapter01_PartitionCount27  -- p(27) = 3010
import QseriesFormalization.Chapter01_PartitionCount28  -- p(28) = 3718 (enables 11∣p(28) at n=2)
import QseriesFormalization.Chapter01_PartitionCount29  -- p(29) = 4565 (enables 5∣p(29) at n=5)
import QseriesFormalization.Chapter01_PartitionCount30  -- p(30) = 5604
import QseriesFormalization.Chapter01_PartitionCount31  -- p(31) = 6842
import QseriesFormalization.Chapter01_PartitionCount32  -- p(32) = 8349
import QseriesFormalization.Chapter01_PartitionCount33  -- p(33) = 10143 (enables 7∣p(33) at n=4)
import QseriesFormalization.Chapter01_PartitionCount34  -- p(34) = 12310
import QseriesFormalization.Chapter01_PartitionCount35  -- p(35) = 14883 (pentagonal σ(35) = -1)
import QseriesFormalization.Chapter01_PartitionCount36  -- p(36) = 17977
import QseriesFormalization.Chapter01_PartitionCount37  -- p(37) = 21637
import QseriesFormalization.Chapter01_PartitionCount38  -- p(38) = 26015
import QseriesFormalization.Chapter01_PartitionCount39  -- p(39) = 31185 (enables 11∣p(39) at n=3)
import QseriesFormalization.Chapter01_PartitionCount40  -- p(40) = 37338 (pentagonal σ(40) = -1; enables 7∣p(40) at n=5)
import QseriesFormalization.Chapter01_PartitionCount41  -- p(41) = 44583
import QseriesFormalization.Chapter01_PartitionCount42  -- p(42) = 53174
import QseriesFormalization.Chapter01_PartitionCount43  -- p(43) = 63261
import QseriesFormalization.Chapter01_PartitionCount44  -- p(44) = 75175 (enables 5∣p(44) at n=8)
import QseriesFormalization.Chapter01_PartitionCount45  -- p(45) = 89134
import QseriesFormalization.Chapter01_PartitionCount46  -- p(46) = 105558
import QseriesFormalization.Chapter01_PartitionCount47  -- p(47) = 124754 (enables 7∣p(47) at n=6)
import QseriesFormalization.Chapter01_PartitionCount48  -- p(48) = 147273
import QseriesFormalization.Chapter01_PartitionCount49  -- p(49) = 173525
import QseriesFormalization.Chapter01_PartitionCount50  -- p(50) = 204226 (enables 11∣p(50) at n=4)
import QseriesFormalization.Chapter01_PartitionCount51  -- p(51) = 239943 (pentagonal σ(51) = +1)
import QseriesFormalization.Chapter01_PartitionCount52  -- p(52) = 281589
import QseriesFormalization.Chapter01_PartitionCount53  -- p(53) = 329931
import QseriesFormalization.Chapter01_PartitionCount54  -- p(54) = 386155 (enables 5∣p(54) at n=10 AND 7∣p(54) at n=7)
import QseriesFormalization.Chapter17_HigherCases  -- Ramanujan congruences at n=2,3 using new p(n)
import QseriesFormalization.Chapter14_CrankN4  -- crank distribution on partitions of 4
import QseriesFormalization.Chapter14_CrankN14  -- crank surjectivity mod 5, n=2 (partitions of 14)
import QseriesFormalization.Chapter14_CrankN19  -- crank surjectivity mod 5, n=3 (partitions of 19)
import QseriesFormalization.Chapter14_CrankN24  -- crank surjectivity mod 5, n=4 (partitions of 24)
import QseriesFormalization.Chapter14_CrankN29  -- crank surjectivity mod 5, n=5 (partitions of 29)
import QseriesFormalization.Chapter14_CrankN34  -- crank surjectivity mod 5, n=6 (partitions of 34)
import QseriesFormalization.Chapter14_CrankGenFun  -- crank genfun infra + Andrews-Garvan at z=1
import QseriesFormalization.Chapter14_Thm116  -- Thm 11.6 partial: LHS reduction via JTP-at-ζ; RR-product blocker isolated
import QseriesFormalization.Exercises
import QseriesFormalization.Audit
