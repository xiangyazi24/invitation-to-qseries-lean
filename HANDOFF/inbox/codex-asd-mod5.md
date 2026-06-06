# TASK (codex / gpt-5.5): Atkin–Swinnerton-Dyer congruences mod 5 (Hirschhorn §3.6)

## Output file (yours only — do NOT touch any other file)
Create `QseriesFormalization/Pending/Chapter17_ASD_Mod5.lean`.
Do NOT edit `QseriesFormalization.lean`, `Audit.lean`, or any other chapter file.

## Hard constraints (playbook)
0 `sorry`, 0 `axiom`, 0 `admit`, no weakened statements, no `native_decide` that
hides math. Verify ONLY with single-file:
```
cd ~/repos/Q-series-and-Chan-s-work
export NVM_DIR=~/.nvm; source ~/.nvm/nvm.sh; nvm use 22 >/dev/null
~/.elan/bin/lake env lean QseriesFormalization/Pending/Chapter17_ASD_Mod5.lean
```
Do NOT run full `lake build` (other agents are editing the same tree concurrently).
After finishing, append `#print axioms <your main thms>` to a scratch copy and confirm
no `sorryAx` (re-elaborate from source; a stale olean can show a phantom sorryAx).
Write a short summary to `HANDOFF/outbox/codex-asd-mod5-reply.md`.

## Math goal
Over `ZMod 5`, mirror the mod-11 dissection proof already in
`QseriesFormalization/Pending/Chapter17_Hirschhorn_Mod11.lean` (study it — reuse the
`section`/`IsRes` pattern, adapting from modulus 11 to modulus 5).

Hirschhorn §3.6 (The Power of q):
- `(q;q)³_∞ ≡ F(q⁵) − 3q·G(q⁵)  (mod 5)`   ... (3.6.4)
  where `F(q⁵) = Σ_k (−1)^k q^{(25k²−5k)/2}`, `G(q⁵) = Σ_k (−1)^k q^{(25k²−15k)/2}`,
  equivalently the residue-0 and residue-3-after-shift parts of `(q;q)³` mod 5.
- Then `Σ p(n)qⁿ = 1/(q;q) = (q;q)⁹/(q;q)¹⁰ = ((q;q)³)³/((q;q)⁵)²`
  `≡ (F(q⁵) − 3q G(q⁵))³ / (q⁵;q⁵)²  (mod 5)`,  using Frobenius `(q;q)⁵ = expand 5 qPoch`.
- Extracting residue-4 terms gives `Σ p(5n+4) qⁿ ≡ 0 (mod 5)`.

## Minimum deliverable (MUST close, 0 sorry)
The clean reachable target — the **mod-5 cube decomposition** + the **residue-4 vanishing**:
1. `(qPochInfPS (ZMod 5))^3 = (sum of its residue-r sections for the r with nonzero
   jacobiTripleSign mod 5)`. (Determine the residues by: triangular `T_k mod 5 ∈ {0,1,3}`,
   excluding `k ≡ 2 (mod 5)` where `2k+1 ≡ 0`. This mirrors `qPochInfPS_cube_decompose_mod_11`.)
2. Re-derive `∀ n, ((qPochInfPS (ZMod 5))^4).coeff (5n+4) = 0` (hence `5 ∣ p(5n+4)`) via this
   dissection — OR if simpler, just prove the decomposition (1) cleanly as the deliverable.

## Reusable infrastructure (already proven — use, don't reprove)
- B2: `QseriesFormalization.Pending.JacobiCubeAnalyticToFormal.qPochInfPS_pow_three_eq_jacobiThetaPS`.
- Frobenius: `QseriesFormalization.PartIV.Ch19.PowerSeries.expand_eq_pow_zmod`.
- `coeff_qPochInfPS_pow_p_in_ZMod_p`, `coeff_qPochInfPS_eq_pentagonalSign`, `coeff_jacobiThetaPS`,
  `jacobiTripleSign_triangular`, `jacobiTripleSign_of_not_triangular` (all in Ch19).
- The whole `section11`/`IsRes`/`isRes_mul`/`isRes_pow` machinery in
  `Pending/Chapter17_Hirschhorn_Mod11.lean` — copy/adapt the `section`-mod-5 analogues.

(Stretch, only if time: identify `F`,`G` as the η-products `(q¹⁰,q¹⁵,q²⁵;q²⁵)`,
`(q⁵,q²⁰,q²⁵;q²⁵)` and state the full ASD congruences `Σp(5n+j)qⁿ ≡ η-quotient` — this needs
JTP specialisations, harder; skip if the minimum deliverable took the time.)
