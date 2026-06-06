Implemented the Ch20 mod-691 verification scripts.

Files added:
- `HANDOFF/tmp/ch20_mod691_verify.py`
- `HANDOFF/tmp/ch20_mod691_small.lean`

Python verification:
- Mirrors the `Chapter20.lean` convolution engine:
  - `tauEtaCoeffZ n := pentagonalSign n`
  - repeated truncated convolution for `tauEtaPowVec N 24`
  - `ramanujanTau(n) = tauEtaPowCoeffZ 24 (n - 1)` for `n >= 1`
- Checks

  ```text
  tau(n) mod 691 = sigma11(n) mod 691
  ```

  for every `1 <= n <= 692`.
- Ran:

  ```bash
  python3 HANDOFF/tmp/ch20_mod691_verify.py
  ```

  Output:

  ```text
  OK: tau(n) == sigma11(n) mod 691 for 1 <= n <= 692
  n=1: tau=1, sigma11=1
  n=2: tau=667, sigma11=667
  n=3: tau=252, sigma11=252
  n=50: tau=14, sigma11=14
  n=690: tau=436, sigma11=436
  n=691: tau=1, sigma11=1
  n=692: tau=37, sigma11=37
  ```

Lean-side decidable check:
- Added a standalone small proof:

  ```lean
  theorem ch20_tau_sigma_mod691_first_ten_by_decide :
      ∀ i : Fin 10,
        ((tauEtaPowCoeffZ 24 i.1 : ZMod 691) =
          (sigma11 (i.1 + 1) : ZMod 691)) := by
    decide
  ```

- Ran:

  ```bash
  lake env lean HANDOFF/tmp/ch20_mod691_small.lean
  ```

  This passed.
- I first tried `Fin 20`; direct `by decide` over the full reducible
  convolution hit the heartbeat limit, so I left the passing `Fin 10` version.

Notes:
- I did not modify `QseriesFormalization/Chapter20.lean`; the verification is
  standalone.
- The Python range includes `n = 692`, i.e. it passes the first place where the
  log-derivative recurrence coefficient `(n - 1)` is `0 mod 691`.
