# Ch10 HM/Appell-Lerch start reply

## Commits

- `8c8f2f5 ch10: add HM table numeric verifier`
  - Adds `scripts/ch10_hm_verify.py`.
- `becec08 ch10: scaffold HM Appell-Lerch reduction`
  - Adds `QseriesFormalization/Pending/Chapter10_HM.lean`.
  - Does not touch `QseriesFormalization.lean`, `Audit.lean`, or root wiring.

## Numeric verification

Command:

```bash
python3 scripts/ch10_hm_verify.py
```

Output:

```text
Checking shifted T_ij HM table against direct f_{2,3,2} through Q^44
T00: sign=+1, C= 1, X=18, Y=18, ell=+1, nonzero<=44 direct= 3, HM= 3: OK
T01: sign=-1, C= 5, X=27, Y=24, ell=+1, nonzero<=44 direct= 4, HM= 4: OK
T02: sign=+1, C=11, X=36, Y=30, ell=+2, nonzero<=44 direct= 3, HM= 3: OK
T10: sign=-1, C= 5, X=24, Y=27, ell=+2, nonzero<=44 direct= 4, HM= 4: OK
T11: sign=+1, C=12, X=33, Y=33, ell=+1, nonzero<=44 direct= 3, HM= 3: OK
T12: sign=-1, C=21, X=42, Y=39, ell=+1, nonzero<=44 direct= 4, HM= 4: OK
T20: sign=+1, C=11, X=30, Y=36, ell=+1, nonzero<=44 direct= 3, HM= 3: OK
T21: sign=-1, C=21, X=39, Y=42, ell=+1, nonzero<=44 direct= 4, HM= 4: OK
T22: sign=+1, C=33, X=48, Y=48, ell=+1, nonzero<=44 direct= 3, HM= 3: OK
Chan combination vs -E3^5*E6^-2*j(12,15) through Q^44: OK
nonzero coefficients through Q^44:
[(0, -1), (3, 6), (6, -12), (9, 7), (12, 1), (15, 6), (18, -4), (21, -14), (24, 18), (27, -18), (33, 13), (36, 28), (39, -18), (42, -8)]
```

Important correction found during verification:

- The requested `docs/chatgpt-designs-2026-06-03/chan1-Ch10-HM-appell-lerch-reduction.md` is not present in this checkout.
- Using HM Eq. `(f232)` directly with `ell = 1` and simply dropping `J_{18k}=0` terms fails for `T02` and `T10`: those are `0 * infinity` specializations, not safe zero terms.
- The verifier keeps `ell = 1` for the seven nonsingular entries and uses the same HM corollary with `ell = 2` for `T02` and `T10`. With that explicit nonsingular choice, all nine shifted entries match the direct cone sum through `Q^44`.

## Lean status

Commands:

```bash
lake env lean QseriesFormalization/Pending/Chapter10_HM.lean
lake build QseriesFormalization.Pending.Chapter10_HM
```

Result:

```text
Build completed successfully
warning: QseriesFormalization/Pending/Chapter10_HM.lean:226:8: declaration uses 'sorry'
```

The file contains:

- exponent-level definitions:
  - `jExp`, `jExpTwice`
  - `appellNumeratorExp`, `appellDenomExp`
- proved exponent lemmas:
  - `jExpTwice_symm`
  - `jExpTwice_periodic_zero_pair`
  - `appellDenomExp_period_z`
- HM table data:
  - `HMTerm`
  - `hmF232Terms`
  - `Cij`, `Xij`, `Yij`, `TijSign`, `hmEll`, `tijData`
  - concrete checked rows `tijData_00` ... `tijData_22`
  - concrete HM rows for `T00`, `T02`, `T10`

## Axioms

Command:

```lean
import QseriesFormalization.Pending.Chapter10_HM
#print axioms QseriesFormalization.Pending.Ch10HM.jExpTwice_symm
#print axioms QseriesFormalization.Pending.Ch10HM.jExpTwice_periodic_zero_pair
#print axioms QseriesFormalization.Pending.Ch10HM.appellDenomExp_period_z
#print axioms QseriesFormalization.Pending.Ch10HM.tijData_02
#print axioms QseriesFormalization.Pending.Ch10HM.hmF232Terms_T02
#print axioms QseriesFormalization.Pending.Ch10HM.hmF232Terms_T10
#print axioms QseriesFormalization.Pending.Ch10HM.appell_cancel
```

Output:

```text
'QseriesFormalization.Pending.Ch10HM.jExpTwice_symm' depends on axioms: [propext, Classical.choice, Quot.sound]
'QseriesFormalization.Pending.Ch10HM.jExpTwice_periodic_zero_pair' depends on axioms: [propext, Classical.choice, Quot.sound]
'QseriesFormalization.Pending.Ch10HM.appellDenomExp_period_z' depends on axioms: [propext, Classical.choice, Quot.sound]
'QseriesFormalization.Pending.Ch10HM.tijData_02' depends on axioms: [propext]
'QseriesFormalization.Pending.Ch10HM.hmF232Terms_T02' depends on axioms: [propext]
'QseriesFormalization.Pending.Ch10HM.hmF232Terms_T10' depends on axioms: [propext, Classical.choice, Quot.sound]
'QseriesFormalization.Pending.Ch10HM.appell_cancel' depends on axioms: [sorryAx]
```

No `native_decide`, no `axiom`, no `opaque`, no `def : Prop` dodge.

## Isolated crux

Exact Lean statement:

```lean
theorem appell_cancel : appellCancelExpr = HMExpr.zero := by
  sorry
```

Docstring in the file marks this as the one remaining mock-theta crux:

```text
Appell-Lerch cancellation in Chan's special linear combination. Closing this
requires HM Theorem 2.3 / Appell-Lerch change-of-z identities plus
theta-product algebra.
```

It is not wired to `Audit.lean`.

## Remaining work estimate

To close this for real:

1. Build actual Laurent/Hahn-series semantics for `j(Q^a;Q^b)` and `m(Q^a,Q^90,Q^z)`, including support/well-foundedness and coefficient extraction.
2. Formalize or import the HM `f_{2,3,2}` Corollary 8.2 specialization. The singular `J_{18k} * M` cases need either regularized products or a systematic nonsingular `ell` selection theorem.
3. Prove Appell cancellation using Appell-Lerch change-of-`z` identities, especially the HM Theorem 2.3 theta quotient.
4. Prove the remaining theta/product evaluation:
   `theta_part_eval = -E3^5 * E6^-2 * j(Q^12;Q^15)`.

The numerical evidence now protects the table and final target through degree 44, but the formal proof still needs the real Appell-Lerch framework.
