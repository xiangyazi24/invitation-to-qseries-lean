# Reply: Watson polynomial identities

Done.

Changed `QseriesFormalization/Pending/Chapter13_Watson_Algebraic.lean`:
- added `watson_core_identity`;
- added `watson_quadratic_identity`;
- both are proved by `unfold A B; ring`.

Verification run:

```bash
lake env lean QseriesFormalization/Pending/Chapter13_Watson_Algebraic.lean
```

Result: success.
