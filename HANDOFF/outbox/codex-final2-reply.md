# codex-final2 reply

Read `HANDOFF/inbox/codex-final2.md`.

Result: not a clean close. I reduced the two target theorem bodies to projections
from one precisely isolated bridge:

```lean
theorem ch10_classical_theta_identities_from_jtp :
    (forall a z0 z1 : Int,
        hm23ClearedThetaLHS a z0 z1 = hm23ClearedThetaRHS a z0 z1) /\
      E6Laurent ^ 2 * thetaCorrectionLaurent =
        -(E3Laurent ^ 5) * jLaurent 12 15
```

The remaining bridge is exactly the combined analytic-to-formal JTP
stabilization input: HM 2.3 cleared theta addition plus the finite 20-term
theta-correction product collapse. The original two target theorem statements
now have no direct `sorry` bodies, but both depend on this single bridge.

Why I stopped here:

- `hm23ClearedThetaIdentity` still needs a genuine Appell-Lerch/HM 2.3
  analytic-to-formal bridge. The repository has JTP stabilization templates
  (`JacobiCubeAnalyticToFormal`, `JTP_FormalPS_Mod7`), but no existing HM
  Appell-Lerch change-of-z theorem or Riemann theta-addition layer to reuse.
- `theta_correction_cleared_product_identity` is not only fixed-modulus
  `jLaurent_symm`/`jLaurent_shift`: after expanding `hm23ThetaQuotient`, the
  denominators are mod-90 theta factors and the cleared identity uses
  `E6Laurent = jLaurent 6 18`. The proof needs the cross-modulus AP-product/JTP
  factorization before ring normalization can finish it.
- Direct full unfolding plus `ring_nf` was too large and, structurally, still
  lacks those product-factorization rewrites.

Remaining gap count in `QseriesFormalization/Pending/Chapter10_HM.lean`:

```text
2012:  sorry
```

No `native_decide`, `axiom`, `admit`, or `opaque` was added.

Validation run:

```text
lake env lean QseriesFormalization/Pending/Chapter10_HM.lean
  passed, with warning: declaration uses 'sorry'

lake build QseriesFormalization.Pending.Chapter10_HM
  passed, with warning: declaration uses 'sorry'

python3 scripts/ch10_hm_verify.py
  HM Def. 0.1 quotient samples: OK
  HM Theorem 2.3 samples through Q^44: OK
  all nine shifted T_ij checks through Q^44: OK
  Chan combination vs -E3^5*E6^-2*j(12,15) through Q^44: OK
  Corr weighted Delta-sum vs -E3^5*E6^-2*j(12,15) through Q^44: OK
  Corr terms off 3Z through Q^44: none
```

`#print axioms`:

```text
'QseriesFormalization.Pending.Ch10HM.hm23ClearedThetaIdentity' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Ch10HM.theta_correction_cleared_product_identity' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
```
