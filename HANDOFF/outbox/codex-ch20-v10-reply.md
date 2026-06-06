# codex-ch20-v10 reply

## Result

I did not get a proof of the full formal identity

```lean
discriminantPS (ZMod 691) = eisensteinE12PSMod691
```

and I did not get a sustainable `≤ 691` / `≤ 692` certificate into
`Chapter20.lean`.

I did add a faster mod-691 coefficient framework and pushed the finite
congruence from `≤ 50` to a checked theorem through `≤ 200`:

```lean
theorem ramanujanTau_congr_sigma11_mod_691_through_two_hundred
    (n : Nat) (hn : n ≤ 200) :
    (ramanujanTau ℤ n : ZMod 691) = (sigma11 n : ZMod 691)
```

## What changed

Added direct `ZMod 691` computation, avoiding enormous integer tau
coefficients:

```lean
def sigma11Mod691 (n : Nat) : ZMod 691
theorem sigma11Mod691_eq_sigma11 (n : Nat) :
    sigma11Mod691 n = (sigma11 n : ZMod 691)

def tauEtaPowStepMod691
def tauEtaPowVecMod691
theorem tauEtaPowVecMod691_spec
theorem ramanujanTau_succ_eq_tauEtaPowVecMod691

def ramanujanTauCoeffMod691FromVec
theorem ramanujanTau_eq_tauCoeffMod691FromVec
```

Finite certificate currently retained in the main file:

```lean
theorem tauCoeffMod691_congr_sigma11_mod691_through_two_hundred :
    (let v := tauEtaPowVecMod691 199 24
     ∀ i : Fin (200 + 1),
      ramanujanTauCoeffMod691FromVec 199 i.1 v = sigma11Mod691 i.1)
```

This proves the public `≤ 200` congruence using `cast_ramanujanTau_int`.

## Experiments

- `≤ 50` with the new `ZMod 691` vector: passed quickly in scratch.
- `≤ 200`: passed in scratch and in `Chapter20.lean`.
- `≤ 400`: passed in scratch, but when placed in `Chapter20.lean` it pushed
  Lean to about 24GB RSS and still had not finished; I removed it from the
  main file.
- `≤ 691`: tried both a `∀ i : Fin 692` certificate and a Boolean
  `check = true` certificate.  Both stayed at 100% CPU for several minutes
  without closing; I killed the runs instead of committing a non-sustainable
  theorem.

So the blocker is now computational, not mathematical: the current vector
convolution is still too expensive at 691 inside the already-heavy Chapter20.
The next practical optimization is a sparse pentagonal convolution for
`etaPS`, since only pentagonal exponents contribute to `(q;q)_∞`.

## Note on uniqueness

Verifying through 692 would not by itself prove the infinite formal identity
from the theta recurrence.  It only gets past the first missing coefficient;
the next free coefficient is at `1383`, then `2074`, etc.  A true infinite
theorem still needs a modular-form/Sturm/dimension input, or a formal product
identity strong enough to control all Frobenius-obstruction coefficients.

## Verification

Ran:

```bash
lake env lean QseriesFormalization/Chapter20.lean
rg -n "sorry|admit|axiom" QseriesFormalization/Chapter20.lean
```

Result:

- `lake env lean QseriesFormalization/Chapter20.lean` passed.
- `rg` returned no matches.
