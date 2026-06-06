#!/usr/bin/env python3
"""Verify Ramanujan's tau congruence mod 691 through n = 692.

This mirrors the computable coefficient engine in
QseriesFormalization/Chapter20.lean:

  tauEtaCoeffZ n        := pentagonalSign n
  tauEtaPowStep N v     := truncated convolution with tauEtaCoeffZ
  tauEtaPowCoeffZ 24 n  := coefficient n of eta(q)^24
  ramanujanTau (n + 1)  := tauEtaPowCoeffZ 24 n

The verification compares tau(n) and sigma_11(n) modulo 691 for n = 1..692.
"""

from __future__ import annotations

MOD = 691
MAX_N = 692
ETA_POWER = 24


def pentagonal_sign(n: int) -> int:
    """Lean's PartI.Ch05.pentagonalSign.

    Coefficient of (q;q)_infty:
      1 at n = 0,
      (-1)^k at generalized pentagonal numbers k(3k +/- 1)/2,
      0 otherwise.
    """
    if n == 0:
        return 1
    k = 1
    while True:
        g1 = k * (3 * k - 1) // 2
        g2 = k * (3 * k + 1) // 2
        if n == g1 or n == g2:
            return -1 if k % 2 else 1
        if g1 > n and g2 > n:
            return 0
        k += 1


def tau_eta_coeff_z(n: int) -> int:
    return pentagonal_sign(n)


def tau_eta_pow_vec(power: int, max_degree: int) -> list[int]:
    """Truncated coefficients of eta(q)^power through max_degree.

    This is the same recurrence as Lean's tauEtaPowVec:
    start from 1, then repeatedly convolve with tauEtaCoeffZ.
    """
    v = [0] * (max_degree + 1)
    v[0] = 1
    eta = [tau_eta_coeff_z(n) for n in range(max_degree + 1)]
    for _ in range(power):
        nxt = [0] * (max_degree + 1)
        for j in range(max_degree + 1):
            total = 0
            for i in range(j + 1):
                total += v[i] * eta[j - i]
            nxt[j] = total
        v = nxt
    return v


def tau_mod_values(max_n: int = MAX_N) -> list[int]:
    """Return tau(n) mod 691 for 0 <= n <= max_n."""
    eta24 = tau_eta_pow_vec(ETA_POWER, max_n - 1)
    tau = [0] * (max_n + 1)
    for n in range(1, max_n + 1):
        tau[n] = eta24[n - 1] % MOD
    return tau


def sigma11_mod(n: int) -> int:
    total = 0
    for d in range(1, n + 1):
        if n % d == 0:
            total += pow(d, 11, MOD)
    return total % MOD


def verify(max_n: int = MAX_N) -> None:
    tau = tau_mod_values(max_n)
    failures: list[tuple[int, int, int]] = []
    for n in range(1, max_n + 1):
        lhs = tau[n] % MOD
        rhs = sigma11_mod(n)
        if lhs != rhs:
            failures.append((n, lhs, rhs))

    if failures:
        print(f"FAILED: {len(failures)} mismatches through n={max_n}")
        for n, lhs, rhs in failures[:20]:
            print(f"n={n}: tau={lhs}, sigma11={rhs}")
        raise SystemExit(1)

    print(f"OK: tau(n) == sigma11(n) mod {MOD} for 1 <= n <= {max_n}")
    for n in [1, 2, 3, 50, 690, 691, 692]:
        if n <= max_n:
            print(f"n={n}: tau={tau[n] % MOD}, sigma11={sigma11_mod(n)}")


if __name__ == "__main__":
    verify()
