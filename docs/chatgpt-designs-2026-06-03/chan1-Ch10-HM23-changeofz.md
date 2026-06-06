# ChatGPT Pro (chan1): HM Theorem 2.3 — Appell–Lerch change-of-z, formal proof

This is the design for the FIRST of Ch10's two remaining cruxes:
`hm23ClearedThetaLHS a z0 z1 = hm23ClearedThetaRHS a z0 z1` (∀ a z0 z1 : ℤ).

It matches the file EXACTLY with `X=Q^a, Z0=Q^{z0}, Z1=Q^{z1}, q=Q^{90}`,
`S(X,Z)=appellNumeratorLaurent a z`, `J=JOneLaurent`.

## Formalization warning (CRITICAL)
Over plain `ℚ((Q))` the `m`-sum's inverses `(1 − Q^{r-1}xz)^{-1}` do NOT have a
single geometric expansion: for `r>1` expand in nonneg powers, for `r<1` expand
in `−∑_{t≥1} Q^{-a t} U^{-t}`. So either fix a valuation convention per term, or
work in a localized coefficient ring
`ℚ[x^{±1},z0^{±1},z1^{±1},(1−xz0)^{-1},…]((Q))` and map down. The identity is
formal-localized, NOT a polynomial identity before the convention is fixed.

## Notation
`J := (q;q)_∞`, `binom(r,2)=r(r-1)/2`.
`S(x,z) := ∑_{r∈ℤ} (−1)^r q^{binom(r,2)} z^r / (1 − q^{r-1} x z)`,  `m(x,q,z)=S(x,z)/j(z;q)`.

Theta identities:
- (T1) `j(q^n u;q) = (−1)^n q^{−binom(n,2)} u^{−n} j(u;q)`
- (T2) `j(u;q)=j(q/u;q)=−u·j(u^{-1};q)`
- (PF) `∑_{k∈ℤ} (−1)^k q^{k(k+1)/2}/(1 − q^k u) = J³/j(u;q)`   [HM eq (1.3)]
- (PF') reindex k=r−1: `∑_{r∈ℤ} (−1)^r q^{binom(r,2)}/(1 − q^{r-1} u) = −J³/j(u;q)`

## The cleared identity (the Lean target — equals the file's hm23Cleared LHS=RHS)
```
j(xz0;q) j(xz1;q) ( j(z0;q) S(x,z1) − j(z1;q) S(x,z0) ) = z0 J³ j(z1/z0;q) j(xz0z1;q)   (C)
```
(HM 2.3 multiplied by j(z0)j(z1)j(xz0)j(xz1).)

## Proof (elliptic difference + residues)
Fix x,z0; variable z=z1. `Δ(x,z,z0) := z0 J³ j(z/z0)j(xz0z) / (j(z0)j(z)j(xz0)j(xz))`.
`F(z) := m(x,q,z) − m(x,q,z0) − Δ(x,z,z0)`. Show F is q-periodic, pole-free, F(z0)=0 ⟹ F≡0.

- **Step 1 (m q-periodic):** `m(x,q,qz)=m(x,q,z)`. Use `j(qz;q)=−z^{-1}j(z;q)`, reindex s=r+1.
- **Step 2 (Δ q-periodic):** four applications of (T1): numerator ×(1/(xz²)), denom ×(1/(xz²)), cancel.
  ⟹ `F(qz)=F(z)`.
- **Residues at z=q^k:** `Res_{z=q^k} 1/j(z;q) = (−1)^{k+1} q^{k(k+1)/2}/J³`  (Rj).
  `S(x,q^k) = (−1)^{k+1} q^{−binom(k,2)} J³/j(x;q)`  (reindex s=r+k, use PF').
  ⟹ `Res_{z=q^k} m = q^k/j(x;q)` (M1). Same for Δ (use T1 thrice) ⟹ `Res = q^k/j(x;q)` (D1). Cancel.
- **Residues at xz=q^k (z*=q^k/x):** unique summand r=1−k. `Res_{z=q^k/x} m = −q^k/(x j(x;q))` (M2).
  Δ pole from 1/j(xz): `Res = −q^k/(x j(x;q))` (D2). Cancel.
- **F(z0)=0:** Δ(x,z0,z0)=0 since j(1;q)=0.
- **Elliptic zero principle (HM Prop 1.3, C=1,n=0):** q-periodic, holomorphic, one zero ⟹ ≡0.

## Ordered Lean lemma list
1. JTP: `j(u;q)=(u;q)_∞(q/u;q)_∞(q;q)_∞`.
2. theta shift (T1) + specials `j(qu;q)=−u^{-1}j(u;q)`, `j(u)=j(q/u)=−u j(u^{-1})`.
3. `j(1;q)=0` (factor 1−1 in product form).
4. **(PF) partial fraction** `∑_k (−1)^k q^{k(k+1)/2}/(1−q^k u)=J³/j(u;q)` + reindexed (PF'). [THE key analytic input]
5. `S(x,q^k)=(−1)^{k+1} q^{−binom(k,2)} J³/j(x;q)` (reindex + PF').
6. `Res_{z=q^k} 1/j = (−1)^{k+1} q^{k(k+1)/2}/J³`; or the local expansion `j(z;q)=(−1)^{k+1}q^{−k(k+1)/2}J³·(z−q^k)/q^k + O((z−q^k)²)`.
7. `m(x,q,qz)=m(x,q,z)` (reindex r↦r+1).
8. `Δ(x,qz,z0)=Δ(x,z,z0)` (four T1).
9. residue cancel at z=q^k: both `= q^k/j(x;q)`.
10. residue cancel at xz=q^k: both `= −q^k/(x j(x;q))`.
11. formal elliptic zero principle (q-periodic + residues 0 + one zero ⟹ 0); finite over orbit reps.
12. HM difference: F≡0.
13. cleared identity (C) [store this — it IS hm23ClearedThetaLHS=RHS].
14. divided HM 2.3 (localize/invert the four j-factors).

## Honest formalization note
The residue/elliptic-zero route (Lemmas 6,9,10,11) needs formal residues + the
zero-count principle — Mathlib lacks these. The workhorse alternative: prove (PF)
(Lemma 4) as a formal-localized identity, then Lemmas 5,9,10 are reindex+PF
coefficient algebra, and (C) follows by clearing. (PF) is the genuine hard
analytic input; everything else is theta-shift bookkeeping.
