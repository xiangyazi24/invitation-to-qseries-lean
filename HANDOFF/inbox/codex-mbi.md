# TASK (codex / gpt-5.5): Ramanujan's Most Beautiful Identity (Chan §16 / Hirschhorn §5)

## Output file (yours only)
Create `QseriesFormalization/Pending/Chapter16_MBI_Proof.lean`.
Do NOT edit `QseriesFormalization.lean`, `Audit.lean`, `Pending/Chapter16_MBI.lean`,
or any other agent's file. Verify ONLY with single-file:
```
cd ~/repos/Q-series-and-Chan-s-work
export NVM_DIR=~/.nvm; source ~/.nvm/nvm.sh; nvm use 22 >/dev/null
~/.elan/bin/lake env lean QseriesFormalization/Pending/Chapter16_MBI_Proof.lean
```
Do NOT run full `lake build` (3 other codex agents edit the same tree concurrently).
0 sorry/axiom/admit. Confirm no `sorryAx` via `#print axioms` re-elaborated from source.
Reply to `HANDOFF/outbox/codex-mbi-reply.md`.

## Goal — the formal power series MBI
With `E(q) = (q;q)_∞ = qPochInfPS R` and `partitionGenFun R = 1/E(q)`:
$$\sum_{n\ge0} p(5n+4)\,q^n \;=\; 5\,\frac{E(q^5)^5}{E(q)^6}.$$
In repo formal-PS terms (over a suitable commutative ring `R`, e.g. `ℚ` or `ℂ`):
`PowerSeries.mk (fun n => (partitionGenFun R).coeff (5*n+4)) = 5 • ((expand 5 (qPochInfPS R))^5 * (partitionGenFun R)^6)`.
(This exact statement is already stated as a `sorry` in `Pending/Chapter16_MBI.lean`
as `most_beautiful_identity_formal` — you may prove THAT, or restate cleanly in your file.)

## Proof roadmap (Hirschhorn "The Power of q" §§5.1–5.4)
Let `E_i` = the residue-`i`-mod-5 section of `E(q)` (use the section-operator idea
from `Pending/Chapter17_Hirschhorn_Mod11.lean`, adapted to mod 5; `E = E_0 + E_1 + E_2`
since pentagonal exponents `(3k²−k)/2 mod 5 ∈ {0,1,2}`).
1. Two **surprising formal identities** (prove these first — they are the crux):
   - (5.3.1)  `E_0·E_2 = −E_1²`
   - (5.3.2)  `E_1 = −q · E(q^25)`   (i.e. `E_1 = −X · expand 25 (qPochInfPS R)`)
   Both are formal-PS identities provable from the Euler-pentagonal dissection
   (`coeff_qPochInfPS_eq_pentagonalSign`) + arithmetic of the pentagonal exponents mod 5,
   possibly with the cube identity B2.
2. The residue-4 part of `p(n)` generating function:
   `∑ p(5n+4) q^{5n+4} = (E(q^25)/E(q^5)^6)·(E_0²E_2² − 3E_0E_1²E_2 + E_1⁴)`  (5.2.6).
   (Derive by rationalising `1/E` against its 5-dissection; the denominator collapses to
   `E(q^5)^6/E(q^25)`. If the roots-of-unity rationalisation is awkward formally, an
   equivalent route is to multiply through by `E(q^5)^6` and match the residue-4 section.)
3. Substitute (5.3.1)+(5.3.2): the bracket `E_0²E_2² − 3E_0E_1²E_2 + E_1⁴` collapses to
   `5E_1⁴ = 5 q^4 E(q^25)^4`. Hence `∑ p(5n+4)q^{5n+4} = 5 q^4 E(q^25)^5 / E(q^5)^6`.
4. Divide by `q^4` and substitute `q^5 → q` (the `expand 5` ↔ section bookkeeping) to get
   `∑ p(5n+4) q^n = 5 E(q^5)^5/E(q)^6`.

## Reusable infrastructure
- B2 `qPochInfPS_pow_three_eq_jacobiThetaPS`; Frobenius `PowerSeries.expand_eq_pow_zmod`
  (note: that one is mod p; here you work over ℚ/ℂ, so use `PowerSeries.expand` directly
  and its `coeff_expand`).
- `coeff_qPochInfPS_eq_pentagonalSign`, `pentagonalSign`, `coeff_jacobiThetaPS`.
- `partitionGenFun`, `partitionGenFun_eq...`, `qPochInfPS`, `subXPow` (Ch19).
- section-operator pattern from `Pending/Chapter17_Hirschhorn_Mod11.lean`.

## Deliverable (largest you can close, 0 sorry)
Best: the full `most_beautiful_identity_formal`. If the full chain is too large, the two
surprising identities (5.3.1)+(5.3.2) as standalone proved lemmas are a valuable partial
deliverable — state precisely what you closed in the reply. THIS IS HARD; partial genuine
progress with 0 sorry beats a fake full claim.
