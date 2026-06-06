# Dobbie identity specialization

Created:

- `QseriesFormalization/Pending/DobbieIdentity.lean`
- `Pending/DobbieIdentity.lean` as a thin root-path check file for the requested command

Main exported theorem:

```lean
QseriesFormalization.Pending.DobbieIdentity.specialized_dobbie_identity
```

with statement:

```lean
chan15LHSPS R * expand5Qpoch R = (qPochInfPS R) ^ 5
```

Also exported the `ℂ`, `ℤ`, and `ℚ` specializations, coefficient form, the
`ζ = exp(2πi/5)` primitive-root lemma, the Dobbie `F(x,z)` product-side
definition, and the fifth-root q-Pochhammer collapse at `ζ`.

Verification:

```bash
lake env lean QseriesFormalization/Pending/DobbieIdentity.lean
lake env lean Pending/DobbieIdentity.lean
rg -n "\bsorry\b|\badmit\b|^\s*axiom\b" QseriesFormalization/Pending/DobbieIdentity.lean Pending/DobbieIdentity.lean
```

Both Lean checks pass. The `rg` check returns no matches.
