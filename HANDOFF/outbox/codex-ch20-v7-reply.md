Implemented the finite mod-691 tau congruence check in
`QseriesFormalization/Chapter20.lean`.

Added:

- `sigma11 : Nat → Nat`, defined as `∑_{d ∣ n} d^11` using the existing
  `Nat.divisorSum` convention, so `sigma11 0 = 0`.
- `ramanujanTau_congr_sigma11_mod_691_through_fifty`:
  for every `n ≤ 50`,
  `(ramanujanTau ℤ n : ZMod 691) = (sigma11 n : ZMod 691)`.

The proof is finite: it splits on `n` with `interval_cases`, rewrites the
known tau values through 50, unfolds `sigma11`, and closes the divisor-power
sum computations in `ZMod 691` by `native_decide`.

Verification:

- `lake env lean QseriesFormalization/Chapter20.lean` passed.
- `rg -n "sorry|admit|axiom" QseriesFormalization/Chapter20.lean` returned no matches.
