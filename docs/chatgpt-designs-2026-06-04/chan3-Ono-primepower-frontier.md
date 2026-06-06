# ChatGPT Pro (chan3): Ono / prime-power congruence frontier — battle plan

## VERDICT: Do Target A (p(25n+24)≡0 mod 25) first. FPS-only, no modular forms.
Target B (mod 13) genuinely needs half-integral weight modular forms — the real campaign, later.

## Target A — p(25n+24)≡0 mod 25  (clean FPS proof, reuses existing mod-5 result)
Notation: E_m=(q^m;q^m)_∞, P=1/E_1=∑p(n)q^n, U_{M,r}(∑a_n q^n)=∑a_{Mn+r}q^n, V_M(∑a_n q^n)=∑a_n q^{Mn}.
KEY DEPENDENCY (exact, over ℤ):  U_{5,4}P = 5·E_5^5/E_1^6   (Ramanujan's exact identity ∑p(5n+4)q^n=5·E_5^5/E_1^6)
Then:
  U_{25,24}P = U_{5,4}(U_{5,4}P) = 5·U_{5,4}(E_5^5/E_1^6).
  mod 5 (Freshman E_5≡E_1^5): E_5^5/E_1^6 ≡ E_1^{19} ≡ E_1^{15}·E_1^4 ≡ E_5^3·E_1^4.
  E_5^3 = V_5(E_1^3), and U_{5,4}(V_5(A)·B) = A·U_{5,4}(B), so
  U_{5,4}(E_5^3·E_1^4) = E_1^3·U_{5,4}(E_1^4) = E_1^3·0 = 0   [uses existing ramanujan5 E_1^4 vanishing].
  ⟹ U_{25,24}P = 5·(≡0 mod5) ≡ 0 mod 25 ⟹ ∀n p(25n+24)≡0 mod 25.

### Ordered Lean lemma spine (18)
1 qPoch_E (E_m). 2 partition_gf P=E_1^{-1}. 3 U_residue_def. 4 V_def. 5 U_U compose: U_{m,r}(U_{n,s}F)=U_{mn,nr+s}F (so U_{5,4}∘U_{5,4}=U_{25,24}).
6 ramanujan5_gf_exact: U_{5,4}P = 5·E_5^5/E_1^6 in ℤ[[q]].  [KEY DEPENDENCY — check repo Ch16]
7 ramanujan5_E1_pow4_vanish: U_{5,4}(E_1^4)=0 in ZMod5[[q]].  [HAVE]
8 map_zmod5_E5: E_5=E_1^5 in ZMod5 (Freshman). 9 E_5^5/E_1^6=E_1^{19} mod5. 10 E_1^{15}=E_5^3 mod5. 11 E_5^5/E_1^6=E_5^3 E_1^4 mod5.
12 E5_pow3_eq_V5_E1_pow3: E_5^3=V_5(E_1^3). 13 U_5_4_mul_V5_left: U_{5,4}(V_5(A)·B)=A·U_{5,4}(B). 14 inner vanish: U_{5,4}(E_5^5/E_1^6)=0 mod5.
15 coeff_div5_of_map_zmod5_zero. 16 5F≡0 mod25 if F≡0 mod5. 17 U25_24_partition_gf_mod25_zero: U_{25,24}P=0 in ZMod25.
18 partition_congr_25: ∀n p(25n+24)≡0 mod25.  [coeff extraction [q^n]U_{25,24}P=p(25n+24)]

### Watson full identity (later strengthening, NOT needed for the congruence):
∑p(25n+24)q^n = 5^2·63·E_5^6/E_1^7 + 5^5·52·q·E_5^12/E_1^13 + 5^7·63·q^2·E_5^18/E_1^19 + 5^10·6·q^3·E_5^24/E_1^25 + 5^12·q^4·E_5^30/E_1^31.
Needs the two 5-dissections E_1^6/E_5^6=A^5-11q+q^2 B^5 and E_5/E_{1/5}=... (A=(q^2;q^5)(q^3;q^5)/((q;q^5)(q^4;q^5)), AB=-1).

## Target B — smallest clean Ono mod-13 (NEEDS half-integral weight modular forms)
Ono's displayed congruence: p(157525693 n + 111247) ≡ 0 mod 13, where 157525693=13·59^4, 111247=(13·59^3+1)/24.
Route: F(13,1;z)=∑_{n≡11(24)} p((13n+1)/24) q^n ≡ 11·η^{11}(24z) mod 13. Finite check: η^{11}(24z)|T(59^2)≡0 mod13.
η^{11}(24z) ∈ S_{11/2}(Γ_0(576)), half-integral weight 11/2. Sturm bound = ⌊(11/24)·[SL2:Γ_0(576)]⌋ = ⌊(11/24)·1152⌋ = 528.
Finite certificate: [q^n](η^{11}(24z)|T(59^2)) ≡ 0 mod 13 for all 0≤n≤528.
MINIMAL INFRA (unavoidable for the clean route): (1) η(24z)^11 ∈ S_{11/2}(Γ_0(576),χ); (2) half-int Hecke T(Q^2), Q=59;
(3) its coeff formula; (4) half-integral Sturm bound; (5) finite coeff compute through q^528.
The GENERAL Ono theorem (∞ many primes Q) needs half-integral Shimura + Serre mod-ℓ — a full campaign.
Smallest Atkin-O'Brien mod-13: p(17303 n+237)≡0 mod13 (17303=13·11^3) but NOT in the clean δ_13 class (237≡3≠6 mod13) — harder, skip.
