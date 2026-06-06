# Bailey Lemma `Field` vs `CommRing` audit

Task: investigate whether `Chapter09_BaileyLemma.lean` key theorems
`lemma91_operator`, `theorem91`, and `theorem92` can be relaxed from
`[Field R]` to `[CommRing R]`, especially for formal power series where the
q-Pochhammer denominators are units.

No Lean source files were modified.

## Short verdict

The current theorems cannot be relaxed by a local edit from
`[Field R]` to `[CommRing R]`.

Reason: the current API is built around `/`, and `/` is not available under
plain `[CommRing R]`. This is not only a proof issue: the definitions of
`L`, `M`, `BaileyTerm`, `BaileyBeta`, `lemma91BaseM`, and
`lemma91TargetM` are Field-scoped because they use division.

Mathematically, the three key identities should have a `CommRing`/formal-PS
version once the divisions by q-Pochhammer factors are replaced by unit
inverses. After the shifted matrix-entry identity is ported to unit inverses,
`lemma91_operator`, `theorem91`, and `theorem92` themselves are just structural
wrappers and should not need field-specific algebra.

## Verified facts

`Chapter09_BaileyLemma.lean`

- Lines 18-20 put the whole file in `section Field` with `[Field R]`.
- `L` at lines 24-26 uses `/ qPochhammer q (n-k)`.
- `M` at lines 30-31 aliases `BaileyBeta`, whose definition is Field-scoped in
  `Chapter09.lean`.
- `lemma91_operator` at lines 283-288 only calls `lemma91_operator_at`.
- `theorem91` at lines 291-302 only rewrites the Bailey-pair hypothesis and
  calls `lemma91_operator`.
- `theorem92` at lines 305-315 only iterates `theorem91`.

`Chapter09.lean`

- Lines 25-27 put the Bailey-pair infrastructure under `[Field R]`.
- `BaileyTerm` at lines 32-33 is
  `alpha k / (qPochhammer q (n-k) * qPoch (a*q) q (n+k))`.
- `BaileyBeta` at lines 62-63 sums `BaileyTerm`.
- `lemma91BaseM_eq`, used by `Chapter09_BaileyLemma.lean`, is also Field-scoped
  and uses `field_simp` in its proof path.

Existing reusable non-Field pieces:

- `qPochhammer` and `qPoch` are already defined for `[CommRing R]`
  (`Basic.lean`, lines 120-144).
- `gaussianBinom` is defined for `[CommSemiring R]` and the closed product
  theorem `gaussianBinom_mul_qPochhammer_eq` is already `[CommRing R]`
  (`Chapter03.lean`, lines 329-345).

Lean checks run with `lake env lean --stdin`:

```lean
variable {R : Type*} [CommRing R]
#check fun (a b : R) => a / b
```

This fails with:

```text
failed to synthesize instance of type class HDiv R R ?m
```

So the current statements are not even syntactically available under
`[CommRing R]`.

The current checked types are:

```lean
lemma91_operator :
  {R : Type u} -> [Field R] -> ...

theorem91 :
  {R : Type u} -> [Field R] -> ...

theorem92 :
  {R : Type u} -> [Field R] -> ...
```

All three are sorry-free modulo standard axioms:

```text
[propext, Classical.choice, Quot.sound]
```

## Where Field is really used today

### Definition-level Field dependency

These cannot move to `[CommRing R]` unchanged:

- `Chapter09_BaileyLemma.L`, because it uses `/`.
- `Chapter09_BaileyLemma.M`, because it is `BaileyBeta`.
- `Chapter09.BaileyTerm` and `Chapter09.BaileyBeta`, because `BaileyTerm` uses
  `/`.
- `Chapter09.lemma91Base`, `lemma91Target`, `lemma91BaseM`,
  `lemma91TargetM`, because they use `/`.

Under a `CommRing`, these definitions need explicit unit inverses, for example
coercions of `h.unit⁻¹` for `h : IsUnit denom`.

### Proof-level Field dependency

The main current proof bottleneck is not `theorem91` or `theorem92`; it is the
matrix-entry identity underneath them.

In `Chapter09_BaileyLemma.lean`:

- `lemma91_matrix_entry_shifted` calls `lemma91BaseM_eq` and uses
  `field_simp` at line 131.
- `lemma91_operator_inner_sum` depends on `lemma91_matrix_entry_shifted`.
- `lemma91_operator_at` depends on `L_comp_M_double_sum` and
  `lemma91_operator_inner_sum`.
- `lemma91_operator` depends on `lemma91_operator_at`.

In `Chapter09.lean`, the proof of `lemma91BaseM_eq` depends on several
Field-style cancellation steps:

- small base cases use `field_simp` at lines 13846, 13859, 13877;
- `shift_term_eq'` uses `field_simp` at line 13903;
- `lemma91Target_recurrence` uses `field_simp` at line 13970;
- `lemma91BaseM_eq` uses `mul_div_mul_left` and `field_simp` around
  lines 14083-14098.

These are algebraically unit-cancellation steps, not inherently field-only
mathematics, but the current proof scripts use Field tools.

### Wrappers that should port after unit inverse infrastructure exists

These do not perform essential field algebra themselves:

- `L_comp_M_double_sum`: finite sum expansion/reindexing; proof uses unfolding,
  `Finset.sum_comm`, and `ring`-style associativity after the definitions
  have been expanded.
- `lemma91_operator_inner_sum`: mostly index shifting; its only hard dependency
  is `lemma91_matrix_entry_shifted`.
- `lemma91_operator_at`: combines the double-sum expansion with the inner-sum
  evaluation.
- `lemma91_operator`: just packages `lemma91_operator_at`.
- `theorem91`: just substitutes `beta = M alpha` and calls
  `lemma91_operator`.
- `theorem92`: just iterates `theorem91`.

So, once a unit-inverse version of `lemma91_matrix_entry_shifted` exists,
`lemma91_operator`, `theorem91`, and `theorem92` should be routine.

## Nonzero hypotheses are not enough over `CommRing`

The current Field theorem assumes:

```lean
hxq : forall k, 1 - x * q^(k+1) != 0
hQ  : forall k, qPochhammer q k != 0
```

In a Field, nonzero means invertible, so this is enough for division.

In a general `CommRing`, nonzero is too weak. The replacement hypotheses must
be unit hypotheses, e.g.

```lean
hQ  : forall k, IsUnit (qPochhammer q k)
hxq : forall k, IsUnit (1 - x * q^(k+1))
```

or more directly:

```lean
hQ  : forall k, IsUnit (qPochhammer q k)
hXQ : forall k, IsUnit (qPoch (x*q) q k)
```

For formal power series with `q = X` (or more generally
`constantCoeff q = 0`), these unit hypotheses should be provable because all
factors have constant term `1`.

## Formal power series observations

Mathlib has the right unit criterion over rings:

```lean
PowerSeries.isUnit_iff_constantCoeff :
  [Ring A] -> IsUnit phi <-> IsUnit (constantCoeff phi)
```

But the global inverse API for power series is Field-based:

```lean
PowerSeries.mul_inv_cancel :
  [Field k] -> (phi : k[[X]]) ->
  constantCoeff phi != 0 -> phi * phi^-1 = 1
```

Also verified:

```lean
variable {A : Type*} [CommRing A]
#check fun (phi : PowerSeries A) => Inv.inv phi
```

This fails: there is no `Inv (PowerSeries A)` instance under plain
`[CommRing A]`.

Therefore, a genuine `CommRing` formal-PS version should not use the global
inverse operation or `PowerSeries.mul_inv_cancel`. It should use units
explicitly:

```lean
have h : IsUnit phi := ...
h.unit.inv
```

Useful lemmas checked:

```lean
Units.mul_inv
Units.inv_mul
Units.mul_left_inj
Units.mul_right_inj
IsUnit.mul
IsUnit.pow
IsUnit.mul_left_cancel
```

There is already a local formal-PS pattern in
`Pending/RogersRamanujan_FormalPS.lean`:

- `qPochPS n := qPochhammer X n`;
- `constantCoeff_qPochPS n : constantCoeff (qPochPS n) = 1`;
- `isUnit_qPochPS n : IsUnit (qPochPS n)`.

That file is over `QQ`, but the same constant-term argument should generalize
to arbitrary coefficient `CommRing`/`Ring`. A Bailey formal-PS port would also
need the analogous lemma for `qPoch (x*X) X n`.

## Recommended migration path

1. Do not try to edit the existing `Field` theorems in place first. Keep them
   as the scalar-field API.

2. Add a separate unit-inverse API for the formal-PS/CommRing setting:

   ```lean
   noncomputable def invOfUnit {R} [CommRing R] {a : R} (ha : IsUnit a) : R :=
     ha.unit.inv
   ```

   Then write denominators as multiplication by `invOfUnit hden`.

3. Prove unit lemmas for the denominator families:

   - `IsUnit (qPochhammer q n)` when `q` has zero constant coefficient in a
     power series ring;
   - `IsUnit (qPoch (x*q) q n)` under the same condition;
   - product-unit lemmas via `IsUnit.mul`.

4. Port `lemma91BaseM_eq` first. This is the real Field bottleneck. Replace
   `field_simp` and `mul_div_mul_left` uses with explicit unit cancellation:

   - multiply both sides by the relevant denominator unit;
   - rewrite with `Units.mul_inv` / `Units.inv_mul`;
   - use `Units.mul_left_inj` / `Units.mul_right_inj` or
     `IsUnit.mul_left_cancel`;
   - finish remaining polynomial identities with `ring`.

5. Port `lemma91_matrix_entry_shifted` using the new `lemma91BaseM_eq`.

6. Port `L_comp_M_double_sum`, `lemma91_operator_inner_sum`,
   `lemma91_operator_at`, `lemma91_operator`, `theorem91`, and `theorem92`.
   These should be mostly mechanical once the definitions use unit inverses.

## Bottom line

`Field` is not mathematically essential for Chan Lemma 9.1 / Theorems 9.1-9.2
in the formal-power-series setting. It is essential for the current Lean
statements because they use `/` and because the supporting Bailey definitions
are Field-scoped. The correct relaxation is not `Field -> CommRing` alone, but
`Field division -> explicit q-Pochhammer unit inverses`; after that, the three
key theorem wrappers should port cleanly.
