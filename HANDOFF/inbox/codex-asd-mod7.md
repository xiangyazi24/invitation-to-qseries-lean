# TASK (codex / gpt-5.5): Atkin–Swinnerton-Dyer congruences mod 7 (Hirschhorn §3.7)

## Output file (yours only — do NOT touch any other file)
Create `QseriesFormalization/Pending/Chapter17_ASD_Mod7.lean`.
Do NOT edit `QseriesFormalization.lean`, `Audit.lean`, or any other chapter file.

## Hard constraints (playbook)
0 `sorry`/`axiom`/`admit`, no weakened statements. Verify ONLY single-file:
```
cd ~/repos/Q-series-and-Chan-s-work
export NVM_DIR=~/.nvm; source ~/.nvm/nvm.sh; nvm use 22 >/dev/null
~/.elan/bin/lake env lean QseriesFormalization/Pending/Chapter17_ASD_Mod7.lean
```
Do NOT run full `lake build` (other agents edit the same tree concurrently).
Confirm no `sorryAx` via `#print axioms` re-elaborated from source. Summary to
`HANDOFF/outbox/codex-asd-mod7-reply.md`.

## Math goal
Over `ZMod 7`, mirror the mod-11 dissection in
`QseriesFormalization/Pending/Chapter17_Hirschhorn_Mod11.lean` (reuse `section`/`IsRes`).

Hirschhorn §3.7:
- `(q;q)³_∞ ≡ H(q⁷) − 3q·J(q⁷) + 5q³·K(q⁷)  (mod 7)`   ... (3.7.1)
  where `H,J,K` are the residue components (theta series `Σ(−1)^k q^{(49k²−7k)/2}` etc.).
- `Σ p(n)qⁿ = 1/(q;q) = (q;q)⁶/(q;q)⁷ = ((q;q)³)²/(q;q)⁷`
  `≡ (H − 3qJ + 5q³K)² / (q⁷;q⁷)  (mod 7)`,  using Frobenius `(q;q)⁷ = expand 7 qPoch`.
- Extracting residue-5 terms gives `Σ p(7n+5) qⁿ ≡ 0 (mod 7)`.

## Minimum deliverable (MUST close, 0 sorry)
1. The **mod-7 cube decomposition** `(qPochInfPS (ZMod 7))^3 = sum of its residue-r sections`
   for the r with nonzero `jacobiTripleSign mod 7` (triangular `T_k mod 7 ∈ {0,1,3,6}`,
   excluding `k ≡ 3 (mod 7)` where `2k+1 ≡ 0`).  Mirror `qPochInfPS_cube_decompose_mod_11`.
   NOTE: a mod-7 residue analysis already exists in `QseriesFormalization/Chapter17_Mod7PerTermAnalysis.lean`
   (`triangular_mod_7_in`, `jacobiTripleSign_nonzero_mod_7_residue`) — reuse it.
2. Optionally re-derive `7 ∣ p(7n+5)` via this dissection (already proven elsewhere; the
   decomposition (1) is the required deliverable).

## Reusable infrastructure (use, don't reprove)
- B2, Frobenius `expand_eq_pow_zmod`, `coeff_qPochInfPS_pow_p_in_ZMod_p`, `coeff_jacobiThetaPS`,
  `jacobiTripleSign_triangular/_of_not_triangular` (Ch19).
- `Chapter17_Mod7PerTermAnalysis` mod-7 residue lemmas.
- `section11`/`IsRes` pattern in `Pending/Chapter17_Hirschhorn_Mod11.lean` (adapt to mod 7).

(Stretch only if time: identify H,J,K as η-products and state full `Σp(7n+j)qⁿ ≡ η-quotient`
congruences — needs JTP, harder; skip if minimum took the time.)
