# TASK (codex / gpt-5.5): Ch5 Boson-Fermion → JTP — CORRECTED target (Opus verified the identity)

## Your previous `hsector` was FALSE — do not use it
`bosonFermion_JTP_of_chargeEnergySectorZ` is conditional on
`∀ c, bosonEulerProduct q * chargeEnergySectorZ q c = q^(triangular |c|)`, which is **false**
(Opus checked numerically). The true per-sector value is the alternating tail
`q^{tri(|c|)} − q^{tri(|c|+1)} + q^{tri(|c|+2)} − …`, NOT a single power. Drop that route.

## The CORRECT identity (Opus-verified to deg 30, residual 0, all z-powers)
```
(1 + z⁻¹) · Z q z · bosonEulerProduct q  =  ∑_{n ∈ ℤ}  z^n · q^(n(n+1)/2)
```
Equivalently the standard Jacobi Triple Product
```
(q;q)∞ · (−zq;q)∞ · (−z⁻¹;q)∞  =  ∑_{n∈ℤ} z^n q^{n(n+1)/2}
```
where the boundary factor is exactly `(−z⁻¹;q)∞ = (1 + z⁻¹)·(−z⁻¹q;q)∞`. Your earlier per-sector
attempt dropped this `(1+z⁻¹)` (you used `(−z⁻¹q;q)` from j=1), which is why it was off.

## Proof path (keep the already-proven `Z_eq_fermionicProduct`)
1. `Z q z = fermionicProduct q z = (−zq;q)∞·(−z⁻¹q;q)∞ = ∏_{j≥1}(1+zq^j)(1+z⁻¹q^j)` — DONE
   (`Z_eq_fermionicProduct`, unconditional). Re-express fermionicProduct in `(−zq;q)/(−z⁻¹q;q)` product
   form if helpful.
2. `Z q z · bosonEulerProduct q = (q;q)∞·(−zq;q)∞·(−z⁻¹q;q)∞` — pure product algebra
   (`bosonEulerProduct = (q;q)∞ = ∏(1-q^{j+1})`).
3. Multiply by `(1+z⁻¹)`: `(1+z⁻¹)·(−z⁻¹q;q)∞ = (−z⁻¹;q)∞`, giving `(q;q)∞(−zq;q)∞(−z⁻¹;q)∞`.
4. Identify with `∑_{n∈ℤ} z^n q^{n(n+1)/2}` via the repo's JTP. The repo has
   `PartI.Ch02.jacobiTripleProduct : jacobiInfiniteProduct q z = jacobiInfiniteSeries q z`
   (Chapter03.lean:1526; series `∑_{n∈ℤ} z^n q^{n²}`, q²-base/even-odd-split convention) and the FINITE
   `Chapter03.finite_jacobi_triple_product`. **Convention bridge needed** (same q²↔q reparametrization
   as the MBI §8.3 work in RamanujanQuinticJTP): match `(q;q)(−zq;q)(−z⁻¹;q)` (base-q, triangular
   `q^{n(n+1)/2}`) to Ch02's base-q² `q^{n²}` form by `q ↦ q^{1/2}`-style substitution / the standard
   `n² → n(n+1)/2` shift. If a clean formal-PS bridge is heavy, state the triangular JTP as the target and
   reduce to the existing analytic JTP.

## Deliverable
Replace/supersede the false endpoint with the CORRECT theorem (define the theta as
`∑_{n∈ℤ} z^n q^{n(n+1)/2}` — fix `bosonFermionThetaSeries` if it currently encodes the wrong
`q^{tri(|c|)}` form). Prove the unconditional
`(1+z⁻¹)·Z q z·bosonEulerProduct q = bosonFermionThetaSeries q z` (or the `(q;q)(−zq;q)(−z⁻¹;q)=theta`
form). This is Chan §5's Boson-Fermion proof of JTP, done in the integer-energy convention.

## Rules
- Edit ONLY `Chapter05_BosonFermion.lean`. NEVER native_decide; NEVER lake build; verify
  `lake env lean QseriesFormalization/Chapter05_BosonFermion.lean`. 0 sorry/axiom/admit; clean-3 axioms.
- The identity is Opus-verified — if a Lean step resists, report the exact goal state, don't abandon.
- Do NOT reintroduce the false `q^(triangular |c|)` per-sector claim. Reply to
  `HANDOFF/outbox/codex-ch5-jtp-corrected-reply.md`.
