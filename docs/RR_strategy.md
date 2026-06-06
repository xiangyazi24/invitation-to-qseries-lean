# Rogers-Ramanujan first proof (Chapter 7) — strategy

**Source**: ChatGPT consultation 2026-05-14 (task `0368c49d`).

**Goal**: prove the Rogers-Ramanujan first identity in product form:
```
G(q) := rrJInf 1 q = 1 / ((q;q^5)_∞ · (q^4;q^5)_∞)
H(q) := rrJInf q q = 1 / ((q^2;q^5)_∞ · (q^3;q^5)_∞)
```

## Path (4 steps, **NOT** through continued fractions or Bailey)

### Step 1: Sum-to-theta reductions (the real core)

Prove:
```lean
theorem rrG_mul_qPoch_eq_theta (q : ℂ) (hq : ‖q‖ < 1) :
    eulerPentagonalInfiniteProduct q * rrJInf 1 q =
      ∑' j : ℤ, (-1 : ℂ)^j * q^(j * (5*j + 1) / 2)

theorem rrH_mul_qPoch_eq_theta (q : ℂ) (hq : ‖q‖ < 1) :
    eulerPentagonalInfiniteProduct q * rrJInf q q =
      ∑' j : ℤ, (-1 : ℂ)^j * q^(j * (5*j + 3) / 2)
```

Prove via finite q-binomial / finite JTP / Tannery. The Ch7 telescoping
lemmas (`rrJInf_telescope_finite`, etc.) help with analytic convergence
but don't directly give the product form.

### Step 2: Evaluate the theta sums via JTP at q^5

```lean
∑' j, (-1)^j q^(j*(5*j+1)/2) = (q^2;q^5)_∞ * (q^3;q^5)_∞ * (q^5;q^5)_∞
∑' j, (-1)^j q^(j*(5*j+3)/2) = (q;q^5)_∞ * (q^4;q^5)_∞ * (q^5;q^5)_∞
```

These are clean JTP specializations. Likely belongs in Chapter04.

### Step 3: Mod-5 product regrouping

```lean
eulerPentagonalInfiniteProduct q =
  (q;q^5)_∞ * (q^2;q^5)_∞ * (q^3;q^5)_∞ * (q^4;q^5)_∞ * (q^5;q^5)_∞
```

Use the same partial-product limit method as the QPI proof's
`qpoch_q4_residue_split` (NOT raw `Nat.divModEquiv` inside `tprod` —
that approach caused 1.6M heartbeat timeouts).

Mathlib infrastructure:
- `Multipliable.tendsto_prod_tprod_nat`
- `HasProd.unique`
- `Tendsto.mul`
- `tendsto_nhds_unique`
- `Finset.prod_range_succ`

### Step 4: Divide by the regrouped product

Assuming nonvanishing of each residue product under `‖q‖ < 1`:
```lean
rrJInf 1 q = 1 / ((q;q^5)_∞ * (q^4;q^5)_∞)
rrJInf q q = 1 / ((q^2;q^5)_∞ * (q^3;q^5)_∞)
```

Use `field_simp [nonzero lemmas]; ring` or avoid division until the
final line by proving the multiplied form first.

## Why not continued fractions?

CFs introduce convergents, CF convergence, Watson/R-R CF identification,
then product identification — much heavier than theta-reduction + JTP.

## Why not Bailey (Ch9)?

Bailey is elegant but requires q-Pfaff-Saalschütz + limiting Bailey lemma.
If Ch9 still blocks on those (CHECKPOINT: alpha_0 common-denominator at N=8
hits ring-tactic Gröbner blowup), the Ch4/JTP route is faster.

## Implementation order

1. Start with **Step 3** (mod-5 regrouping) — most independent, uses
   familiar partial-product machinery.
2. Then **Step 2** (theta sums) — direct JTP application.
3. Then **Step 1** (sum-to-theta reduction) — the hardest, needs Tannery.
4. **Step 4** (assembly) — `field_simp` + ring.

## Status

- [ ] Step 1: rrG_mul_qPoch_eq_theta, rrH_mul_qPoch_eq_theta
- [ ] Step 2: theta sum JTP evaluations (probably in Ch4)
- [ ] Step 3: mod-5 product regrouping (probably in Ch4 or new module)
- [ ] Step 4: G(q) / H(q) product forms (Ch7 closing)
