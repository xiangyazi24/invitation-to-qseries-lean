# TASK (codex/gpt-5.5): FINAL ASSEMBLY of the Most Beautiful Identity

Extend `QseriesFormalization/Pending/Chapter16_MBI_Proof.lean` (namespace `Ch16MBIProof`).
Touch ONLY this file. Verify single-file `lake env lean` (no `lake build`); 0 sorry/axiom/admit;
confirm no `sorryAx` re-elaborated from source. Reply to `HANDOFF/outbox/codex-mbi-assemble-reply.md`.

## Already proven in this file (REUSE — do not redo)
- `qPochInfPS_five_dissection : qPochInfPS R = E5 R 0 + E5 R 1 + E5 R 2`
- (5.3.1) `E5_zero_mul_two_eq_neg_one_sq_rat : E5 ℚ 0 * E5 ℚ 2 = -(E5 ℚ 1)^2`
- (5.3.2) FULL `E5_one_eq_neg_X_mul_expand_twentyfive_qPochInfPS : E5 R 1 = -X * expand 25 (qPochInfPS R)`
- `E5_bracket_collapse_rat`, `E5_one_pow_four_eq_X_pow_four_expand_twentyfive_qPochInfPS_pow_four_rat`

## Goal — close the full identity `most_beautiful_identity`
`PowerSeries.mk (fun n => (partitionGenFun ℚ).coeff (5*n+4)) = 5 • ((expand 5 (qPochInfPS ℚ))^5 * (partitionGenFun ℚ)^6)`.

## Roadmap (Hirschhorn 5.2.6 → 5.4 → 5.1.1)
1. `1/E(q) = E(q)^9 / E(q)^10 = (E(q)^3)^3 / (E(q)^5)^2`. Over ℚ, with `partitionGenFun = (qPochInfPS)⁻¹`:
   relate `partitionGenFun ℚ` to `(qPochInfPS ℚ)^9 * ((expand 5 (qPochInfPS ℚ))^2)⁻¹` — but better, AVOID
   inverses: prove the equivalent product form by multiplying both target sides by `(qPochInfPS ℚ)^6`:
   the identity ⇔ `mk(...) * (qPochInfPS ℚ)^6 = 5 • (expand 5 (qPochInfPS ℚ))^5`, OR work via
   `partitionGenFun * qPochInfPS = 1` (`partitionGenFun_mul...` in Ch19) to clear denominators.
2. Use the dissection `qPochInfPS^3 = E5 0 + E5 1 + E5 2` and extract the residue-4 part of the cube^... ;
   the residue-4 component of `(E5 0 + E5 1 + E5 2)^3` is `E5 0^2 E5 2^2 - 3 E5 0 E5 1^2 E5 2 + E5 1^4`
   (after the residue/section convolution — reuse `section5`/`isRes5_mul`/`isRes5_pow`).
3. Apply (5.3.1) [`E5 0 E5 2 = -E5 1^2`] to collapse that bracket to `5 E5 1^4`
   (already `E5_bracket_collapse_rat`).
4. Apply (5.3.2)/`E5_one_pow_four_...` [`E5 1^4 = X^4 (expand 25 qPoch)^4`] and the Frobenius
   `(qPochInfPS)^5 = expand 5 qPochInfPS`... and `expand 5 ∘ expand 5 = expand 25` bookkeeping, to land
   `mk (p(5n+4)) = 5 • (expand 5 qPoch)^5 * partitionGenFun^6`.

Hardest part is step 1-2 (the residue-4 extraction from `1/E`). If full assembly proves too large,
deliver the residue-4 cube-bracket lemma (step 2 result as a standalone proved lemma) as partial.
0-sorry partial beats fake-complete.
