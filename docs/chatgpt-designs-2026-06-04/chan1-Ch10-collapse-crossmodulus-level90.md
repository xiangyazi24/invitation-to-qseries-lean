# ChatGPT Pro (chan1): Ch10 collapse — cross-modulus bridge to common level 90

## The obstruction (confirmed)
Riemann theta relation is SAME-modulus / same-nome. It cannot bridge moduli {9,15} → {18,90,270}.
The missing bridge is AP-refinement to common level 90. BUT that does NOT turn the 31-term sum into one
product — the sum-of-products survives (product formulae change the multiplicative basis; addition/Riemann
identities are additive). So the genuine remaining crux is an ADDITIVE level-90 theta/AP identity.

## Notation
P_r := (Q^r;Q^90)_∞,  1≤r≤90.   K := J(90,270) = P_90 = (Q^90;Q^90)_∞.

## AP-refinement lemma (m | 90)
  (Q^r;Q^m)_∞ = ∏_{t=0}^{90/m-1} (Q^{r+tm};Q^90)_∞
Equivalently, for 0<a<m, m|90:
  J(a,m) = ∏_{r=1}^{90} P_r^{ 1_{r≡0 (m)} + 1_{r≡a (m)} + 1_{r≡-a (m)} }

## The four cross-modulus bridge lemmas (EXACT, provable via jLaurent_eq_tripleProductInf + AP-refine)
J_3_18_bridge:  jLaurent 3 18 * K^6 =
   jLaurent 3 90 * jLaurent 15 90 * jLaurent 18 90 * jLaurent 21 90 * jLaurent 33 90 * jLaurent 36 90 * jLaurent 39 90
J_6_18_bridge:  jLaurent 6 18 * K^6 =
   jLaurent 6 90 * jLaurent 12 90 * jLaurent 18 90 * jLaurent 24 90 * jLaurent 30 90 * jLaurent 36 90 * jLaurent 42 90
J_9_18_bridge:  jLaurent 9 18 * K^6 =
   (jLaurent 9 90)^2 * jLaurent 18 90 * (jLaurent 27 90)^2 * jLaurent 36 90 * jLaurent 45 90
J_3_9_pow5_J_3_15_bridge:  (jLaurent 3 9)^5 * jLaurent 3 15 * K^75 = A_0, where
  A_0 = J(3,90)^6 J(6,90)^5 J(9,90)^5 J(12,90)^6 J(15,90)^6 J(18,90)^6 J(21,90)^5 J(24,90)^5
        J(27,90)^6 J(30,90)^6 J(33,90)^6 J(36,90)^5 J(39,90)^5 J(42,90)^6 J(45,90)^3
  exponent table (a : power of J(a,90)):
    3:6 6:5 9:5 12:6 15:6 18:6 21:5 24:5 27:6 30:6 33:6 36:5 39:5 42:6 45:3
  (K^75: A_0 side has 81 copies of P_90 via its J(a,90) factors; J(3,9)^5 J(3,15) has P_90^6; 81-6=75.)

## After the bridges: the residual at common level 90 (ADDITIVE — NOT exponent-matching)
A_3 = J(3,90)J(15,90)J(18,90)J(21,90)J(33,90)J(36,90)J(39,90),
A_6 = J(6,90)J(12,90)J(18,90)J(24,90)J(30,90)J(36,90)J(42,90),
A_9 = J(9,90)^2 J(18,90) J(27,90)^2 J(36,90) J(45,90).
Each correction term i has J(3,18)^{u_i} J(6,18)^{v_i} J(9,18)^{w_i}, u_i+v_i+w_i=5, plus K^3 and a B_i (mod-90 product).
Common-cleared residual (multiply by K^75; K is a unit since constantCoeff K = 1):
  K^75 * R = -Q^4 * A_0 * B_0 + K^48 * ∑_{i=1}^{30} c_i Q^{n_i} A_3^{u_i} A_6^{v_i} A_9^{w_i} B_i = 0.
This additive level-90 identity is the genuine remaining crux. NOT closable by exponent-vector matching.
Viable closures:
  (1) Riemann certificate ENTIRELY at modulus 90 — now that everything is level 90, jLaurent_riemann (M=90)
      CAN do the additive cancellation (the earlier obstruction was cross-modulus; gone after the bridges).
  (2) one explicit level-90 5-dissection/modular-equation lemma = the boxed K^75 R = 0 identity.
  (3) modular-form/Sturm finite coeff (needs modular-form infra).

## Lean route
1. def P r := pochhammerAP r 90;  K := jLaurent 90 270;  K_eq_P90 : K = P 90.
2. pochhammerAP_refine_90 (r m)(hm: m∣90): pochhammerAP r m = ∏_{t<90/m} pochhammerAP (r+t*m) 90.
3. The four bridge lemmas (rewrite every J via jLaurent_eq_tripleProductInf, apply AP-refine, close finite
   residue arithmetic with norm_num / an AP-monomial normalizer).
4. K is a unit (constantCoeff = 1). suffices K^75 * R = 0.
5. Rewrite cross-modulus atoms via the four bridges → the additive level-90 goal.
6. Close the additive level-90 identity via Riemann-at-90 (option 1) — the Riemann ideal at M=90 should now
   span it since all factors are mod 90.

KEY TAKEAWAY: AP machinery supplies ONLY the cross-modulus bridge. The crux remains an ADDITIVE level-90
identity, closed by Riemann-at-90 AFTER bridging — not a pure exponent-vector product identity.
