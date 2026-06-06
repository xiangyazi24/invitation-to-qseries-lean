# TASK (codex / gpt-5.5): FINISH the Most Beautiful Identity

## File (extend the existing one — it is committed, add lemmas, keep everything that's there)
`QseriesFormalization/Pending/Chapter16_MBI_Proof.lean` (namespace `Ch16MBIProof`).
Do NOT touch any other file. Verify single-file:
```
cd ~/repos/Q-series-and-Chan-s-work
export NVM_DIR=~/.nvm; source ~/.nvm/nvm.sh; nvm use 22 >/dev/null
~/.elan/bin/lake env lean QseriesFormalization/Pending/Chapter16_MBI_Proof.lean
```
Do NOT run full `lake build`. 0 sorry/axiom/admit. Confirm no `sorryAx` (re-elaborate
from source). Reply to `HANDOFF/outbox/codex-mbi-finish-reply.md`.

## Already proven in this file (REUSE — do not redo)
- `section5`, `IsRes5`, add/mul/pow support lemmas.
- `qPochInfPS_five_dissection : qPochInfPS R = E5 R 0 + E5 R 1 + E5 R 2`.
- `E5_zero_mul_two_eq_neg_one_sq_rat : E5 ℚ 0 * E5 ℚ 2 = -(E5 ℚ 1)^2`  (Hirschhorn 5.3.1).
- `coeff_E5_one_eq_zero_of_not_twentyfive_dvd : ¬ 25 ∣ (n-1) → (E5 R 1).coeff n = 0`
  (the support half of 5.3.2).

## What to close (in order)
1. **Sign reindexing**: `pentagonalSign (25*m + 1) = - pentagonalSign m`  (as ℤ).
   This is the missing arithmetic fact. The pentagonal generalised number at index `k`
   maps under `k ↦ 5k±1`-type reindexing; work it out from the definition of
   `pentagonalSign` (Ch05_Franklin) and the pentagonal-exponent identity
   `(3(5k±?)²±(5k±?))/2 = 25·(3k²±k)/2 + 1`. Use `two_mul_triangular`-style helpers
   and the explicit pentagonal generator.
2. **(5.3.2) full**: `E5 R 1 = - PowerSeries.X * PowerSeries.expand 25 _ (qPochInfPS R)`
   (i.e. `E_1 = -q·E(q^25)`), combining `coeff_E5_one_eq_zero_of_not_twentyfive_dvd`
   (support) with step 1 (the value at `25m+1`).
3. **Assembly** (Hirschhorn 5.2.6 → 5.4 → 5.1.1), over `ℚ` (or `ℂ`):
   - residue-4 GF: `mk (fun n => (partitionGenFun ℚ).coeff (5n+4))` relates to
     `(E5 0)²(E5 2)² − 3(E5 0)(E5 1)²(E5 2) + (E5 1)⁴` over `(q⁵;q⁵)⁶/(q²⁵;q²⁵)`-type denom.
   - Use (5.3.1) to collapse the bracket to `5·(E5 1)⁴`, then (5.3.2) to get `5q⁴E(q²⁵)⁴`.
   - Conclude `most_beautiful_identity_formal` (the statement already sorried in
     `Pending/Chapter16_MBI.lean` — restate & prove it in YOUR file as
     `most_beautiful_identity` to avoid touching that file):
     `mk (fun n => (partitionGenFun ℚ).coeff (5n+4)) = 5 • ((expand 5 (qPochInfPS ℚ))^5 * (partitionGenFun ℚ)^6)`.

If the assembly (step 3) proves too large, **closing steps 1+2 (the full 5.3.2) is a
valuable deliverable** — report precisely what closed. Partial 0-sorry beats fake-complete.
