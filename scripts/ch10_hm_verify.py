#!/usr/bin/env python3
"""Numerical checks for the Ch10 Hickerson-Mortenson f_{2,3,2} table.

The calculations are exact integer Laurent/power series truncations in Q.
They verify the nine shifted T_ij entries against the direct Hecke cone sum
and then verify the assembled Chan combination through Q^44.
"""

from __future__ import annotations

from collections import defaultdict
from dataclasses import dataclass

LOW = -800
HIGH = 220
CHECK_DEG = 44

Series = dict[int, int]


def clean(s: Series) -> Series:
    return {e: c for e, c in s.items() if c}


def add(a: Series, b: Series, scale: int = 1) -> Series:
    out = defaultdict(int, a)
    for e, c in b.items():
        out[e] += scale * c
    return clean(dict(out))


def shift(a: Series, k: int, scale: int = 1, low: int = LOW, high: int = HIGH) -> Series:
    return {e + k: scale * c for e, c in a.items() if low <= e + k <= high and scale * c}


def mul(a: Series, b: Series, low: int = LOW, high: int = HIGH) -> Series:
    out: dict[int, int] = defaultdict(int)
    for ea, ca in a.items():
        for eb, cb in b.items():
            e = ea + eb
            if low <= e <= high:
                out[e] += ca * cb
    return clean(dict(out))


def pow_series(a: Series, n: int, low: int = 0, high: int = CHECK_DEG) -> Series:
    out: Series = {0: 1}
    base = a
    m = n
    while m:
        if m & 1:
            out = mul(out, base, low, high)
        m >>= 1
        if m:
            base = mul(base, base, low, high)
    return out


def inv_power_series(a: Series, high: int) -> Series:
    if a.get(0, 0) != 1:
        raise ValueError(f"expected constant term 1, got {a.get(0, 0)}")
    out: Series = {0: 1}
    for n in range(1, high + 1):
        total = 0
        for k in range(1, n + 1):
            total += a.get(k, 0) * out.get(n - k, 0)
        if total:
            out[n] = -total
    return out


def inv_laurent(a: Series, low: int = LOW, high: int = HIGH) -> Series:
    a = clean(a)
    valuation = min(a)
    leading = a[valuation]
    if leading not in (1, -1):
        raise ValueError(f"non-unit leading coefficient {leading} at {valuation}")
    shifted = {e - valuation: c * leading for e, c in a.items()}
    inv_shifted = inv_power_series(shifted, high - valuation)
    return shift(inv_shifted, -valuation, leading, low, high)


def neg_one_pow_int(n: int) -> int:
    return -1 if n % 2 else 1


def j_series(a: int, b: int, low: int = LOW, high: int = HIGH) -> Series:
    out: dict[int, int] = defaultdict(int)
    # This range is intentionally wider than needed for degree 44 checks.
    for n in range(-80, 81):
        e = b * n * (n - 1) // 2 + a * n
        if low <= e <= high:
            out[e] += neg_one_pow_int(n)
    return clean(dict(out))


def geom_inv(d: int, low: int = LOW, high: int = HIGH) -> Series:
    if d == 0:
        raise ZeroDivisionError("1 - Q^0")
    out: Series = {}
    if d > 0:
        k = 0
        while k * d <= high:
            e = k * d
            if low <= e:
                out[e] = 1
            k += 1
    else:
        step = -d
        k = 1
        while k * step <= high:
            e = k * step
            if low <= e:
                out[e] = -1
            k += 1
    return out


def appell_numerator(a: int, z: int, low: int = LOW, high: int = HIGH) -> Series:
    """The numerator sum in HM Def. 0.1 for m(Q^a,Q^90,Q^z)."""
    numerator: Series = {}
    for r in range(-80, 81):
        base = 90 * r * (r - 1) // 2 + z * r
        d = 90 * (r - 1) + a + z
        term = shift(geom_inv(d, low - base, high - base), base, neg_one_pow_int(r), low, high)
        numerator = add(numerator, term)
    return numerator


def appell_m(a: int, z: int, low: int = LOW, high: int = HIGH) -> Series:
    denom_inv = inv_laurent(j_series(z, 90, low, high), low, high)
    return mul(denom_inv, appell_numerator(a, z, low, high), low, high)


def hm23_theta_quotient(a: int, z0: int, z1: int, low: int = LOW, high: int = HIGH) -> Series:
    """HM Theorem 2.3 RHS for x=Q^a, q=Q^90, z_i=Q^z_i."""
    j1_cubed = pow_series(j_series(90, 270, low, high), 3, low, high)
    numerator = shift(
        mul(
            mul(j1_cubed, j_series(z1 - z0, 90, low, high), low, high),
            j_series(a + z0 + z1, 90, low, high),
            low,
            high,
        ),
        z0,
        1,
        low,
        high,
    )
    denominator = mul(
        mul(j_series(z0, 90, low, high), j_series(z1, 90, low, high), low, high),
        mul(j_series(a + z0, 90, low, high), j_series(a + z1, 90, low, high), low, high),
        low,
        high,
    )
    return mul(numerator, inv_laurent(denominator, low, high), low, high)


def hecke_f232_direct(x: int, y: int, q: int = 9, low: int = LOW, high: int = HIGH) -> Series:
    out: dict[int, int] = defaultdict(int)
    for r in range(-80, 81):
        for s in range(-80, 81):
            same_nonnegative = r >= 0 and s >= 0
            same_negative = r < 0 and s < 0
            if not (same_nonnegative or same_negative):
                continue
            sg = 1 if same_nonnegative else -1
            e = x * r + y * s + q * (
                r * (r - 1) + 3 * r * s + s * (s - 1)
            )
            if low <= e <= high:
                out[e] += sg * neg_one_pow_int(r + s)
    return clean(dict(out))


@dataclass(frozen=True)
class TijData:
    i: int
    j: int
    sign: int
    c: int
    x: int
    y: int


def tij_data(i: int, j: int) -> TijData:
    c = i * i + 3 * i * j + j * j + 3 * i + 3 * j + 1
    x = 6 * i + 9 * j + 18
    y = 9 * i + 6 * j + 18
    return TijData(i=i, j=j, sign=neg_one_pow_int(i + j), c=c, x=x, y=y)


def hm_f232(x: int, y: int, ell: int, low: int = LOW, high: int = HIGH) -> Series:
    out: Series = {}

    terms = hm_terms(x, y, ell)
    for lead, j_a, m_a, m_z in terms:
        # j(Q^(18k); Q^18)=0.  We only drop nonsingular zero-coefficient
        # products.  The chosen ell-values below avoid the 0*infinity cases.
        if j_a % 18 == 0:
            if any(90 * (r - 1) + m_a + m_z == 0 for r in range(-10, 11)):
                raise ZeroDivisionError(f"zero-pole product J_{j_a} * M({m_a},{m_z})")
            continue
        term = mul(j_series(j_a, 18, low, high), appell_m(m_a, m_z, low, high), low, high)
        out = add(out, shift(term, lead, 1, low, high))
    return out


def hm_terms(x: int, y: int, ell: int) -> list[tuple[int, int, int, int]]:
    return [
        (0, y, 54 + 2 * x - 3 * y, 18 * ell + 2 * y - 2 * x),
        (0, x, 54 + 2 * y - 3 * x, 2 * x - 2 * y - 18 * ell),
        (x - y - 9, y + 9, 9 + 2 * x - 3 * y, 18 * ell + 2 * y - 2 * x),
        (y - x - 9, x + 9, 9 + 2 * y - 3 * x, 2 * x - 2 * y - 18 * ell),
    ]


def hm_ell_for_tij(i: int, j: int) -> int:
    """Minimal nonsingular correction to the requested ell=1 table.

    The raw ell=1 specialization contains two 0*infinity products:
    T02 and T10.  The HM corollary is ell-independent after regularization;
    using ell=2 for exactly those two entries avoids the singular product and
    gives the same f_{2,3,2} series by direct coefficient verification.
    """
    return 2 if (i, j) in {(0, 2), (1, 0)} else 1


def shifted_t_direct(t: TijData) -> Series:
    return shift(hecke_f232_direct(t.x, t.y), t.c, t.sign)


def shifted_t_hm(t: TijData) -> Series:
    return shift(hm_f232(t.x, t.y, hm_ell_for_tij(t.i, t.j)), t.c, t.sign)


def theta(a: int, b: int = 2, low: int = 0, high: int = CHECK_DEG) -> Series:
    return j_series(a, b * a, low, high) if False else j_series(a, 2 * a, low, high)


def theta1() -> Series:
    return j_series(1, 2, 0, CHECK_DEG)


def theta9() -> Series:
    return j_series(9, 18, 0, CHECK_DEG)


def e_product(m: int, high: int = CHECK_DEG) -> Series:
    out: Series = {0: 1}
    for n in range(1, high // m + 1):
        out = mul(out, {0: 1, m * n: -1}, 0, high)
    return out


def rhs_series(high: int = CHECK_DEG) -> Series:
    e3 = e_product(3, high)
    e6 = e_product(6, high)
    e6_inv2 = inv_power_series(pow_series(e6, 2, 0, high), high)
    pent = j_series(12, 15, 0, high)
    return shift(mul(mul(pow_series(e3, 5, 0, high), e6_inv2, 0, high), pent, 0, high), 0, -1, 0, high)


def theta_weight_for_tij(i: int, j: int, high: int = CHECK_DEG) -> Series:
    th9 = theta9()
    th1 = theta1()
    th9_sq = pow_series(th9, 2, 0, high)
    th9_th1 = mul(th9, th1, 0, high)
    if i == 0 and j == 0:
        return add(add(th9_sq, shift(th9_th1, 0, -2, 0, high)), pow_series(th1, 2, 0, high))
    if i == 0:
        return add(th9_sq, shift(th9_th1, 0, -2, 0, high))
    return th9_sq


def delta_to_18(a: int, z: int, low: int = LOW, high: int = HIGH) -> Series:
    if z == 18:
        return {}
    return hm23_theta_quotient(a, 18, z, low, high)


def shifted_t_theta_correction(t: TijData, low: int = LOW, high: int = CHECK_DEG) -> Series:
    out: Series = {}
    for lead, j_a, m_a, m_z in hm_terms(t.x, t.y, hm_ell_for_tij(t.i, t.j)):
        if m_z == 18:
            continue
        delta = delta_to_18(m_a, m_z, low, HIGH)
        prefactor = shift(j_series(j_a, 18, low, HIGH), t.c + lead, t.sign, low, HIGH)
        out = add(out, mul(prefactor, delta, low, high))
    return out


def theta_correction_direct(high: int = CHECK_DEG) -> Series:
    out: Series = {}
    for i in range(3):
        for j in range(3):
            t = tij_data(i, j)
            weighted = mul(
                theta_weight_for_tij(i, j, high),
                shifted_t_theta_correction(t, LOW, high),
                0,
                high,
            )
            out = add(out, weighted)
    return restrict(out, 0, high)


def off_three_lattice_terms(s: Series, low: int = 0, high: int = CHECK_DEG) -> list[tuple[int, int]]:
    return [(e, s.get(e, 0)) for e in range(low, high + 1) if e % 3 != 0 and s.get(e, 0)]


def restrict(s: Series, low: int = 0, high: int = CHECK_DEG) -> Series:
    return {e: c for e, c in sorted(s.items()) if low <= e <= high and c}


def first_diffs(a: Series, b: Series, low: int = 0, high: int = CHECK_DEG) -> list[tuple[int, int, int]]:
    diffs = []
    for e in range(low, high + 1):
        ca = a.get(e, 0)
        cb = b.get(e, 0)
        if ca != cb:
            diffs.append((e, ca, cb))
    return diffs


def verify_def01_bridge() -> None:
    samples = [
        (36, 18),
        (36, 12),
        (21, -12),
        (-9, 18),
        (6, -24),
        (-39, 30),
        (21, 42),
    ]
    print("Checking HM Def. 0.1 quotient bridge j(z,90)*m(a,z)=numerator")
    for a, z in samples:
        lhs = mul(j_series(z, 90), appell_m(a, z))
        rhs = appell_numerator(a, z)
        diffs = first_diffs(lhs, rhs, -40, 80)
        status = "OK" if not diffs else f"FAIL first diffs={diffs[:8]}"
        print(f"m({a:+d},{z:+d}): {status}")
        if diffs:
            raise SystemExit(1)


def verify_hm23() -> None:
    samples = [
        (36, 12, 18),
        (21, -12, 18),
        (-9, 18, -18),
        (6, -24, 24),
        (36, -30, 30),
    ]
    print(f"Checking HM Theorem 2.3 change-of-z through Q^{CHECK_DEG}")
    for a, z0, z1 in samples:
        lhs = add(appell_m(a, z1), appell_m(a, z0), scale=-1)
        rhs = hm23_theta_quotient(a, z0, z1)
        diffs = first_diffs(lhs, rhs, -20, CHECK_DEG)
        status = "OK" if not diffs else f"FAIL first diffs={diffs[:8]}"
        print(f"a={a:+d}, z0={z0:+d}, z1={z1:+d}: {status}")
        if diffs:
            raise SystemExit(1)


def verify_theta_correction() -> None:
    corr = theta_correction_direct(CHECK_DEG)
    rhs = rhs_series()
    diffs = first_diffs(corr, rhs)
    off_lattice = off_three_lattice_terms(corr)
    print(
        "Corr weighted Delta-sum vs -E3^5*E6^-2*j(12,15) "
        f"through Q^{CHECK_DEG}: {'OK' if not diffs else 'FAIL'}"
    )
    print(f"Corr terms off 3Z through Q^{CHECK_DEG}: {off_lattice if off_lattice else 'none'}")
    if diffs:
        print(f"first diffs={diffs[:12]}")
        raise SystemExit(1)
    if off_lattice:
        raise SystemExit(1)
    sample = [(e, corr.get(e, 0)) for e in range(0, CHECK_DEG + 1) if corr.get(e, 0)]
    print("Corr nonzero coefficients through Q^44:")
    print(sample)


def main() -> None:
    verify_def01_bridge()
    verify_hm23()

    print(f"Checking shifted T_ij HM table against direct f_{{2,3,2}} through Q^{CHECK_DEG}")
    hm_terms: dict[tuple[int, int], Series] = {}
    direct_terms: dict[tuple[int, int], Series] = {}
    for i in range(3):
        for j in range(3):
            t = tij_data(i, j)
            direct = restrict(shifted_t_direct(t))
            hm = restrict(shifted_t_hm(t))
            direct_terms[(i, j)] = direct
            hm_terms[(i, j)] = hm
            diffs = first_diffs(direct, hm)
            status = "OK" if not diffs else f"FAIL first diffs={diffs[:8]}"
            print(
                f"T{i}{j}: sign={t.sign:+d}, C={t.c:2d}, X={t.x:2d}, Y={t.y:2d}, "
                f"ell={hm_ell_for_tij(i, j):+d}, "
                f"nonzero<=44 direct={len(direct):2d}, HM={len(hm):2d}: {status}"
            )
            if diffs:
                raise SystemExit(1)

    h00 = {}
    for s in hm_terms.values():
        h00 = add(h00, s)
    h10 = {}
    for j in range(3):
        h10 = add(h10, hm_terms[(0, j)])
    h11 = hm_terms[(0, 0)]

    lhs = add(
        add(
            mul(pow_series(theta9(), 2, 0, CHECK_DEG), h00, 0, CHECK_DEG),
            mul(mul(theta9(), theta1(), 0, CHECK_DEG), h10, 0, CHECK_DEG),
            scale=-2,
        ),
        mul(pow_series(theta1(), 2, 0, CHECK_DEG), h11, 0, CHECK_DEG),
    )
    rhs = rhs_series()
    diffs = first_diffs(lhs, rhs)
    print(f"Chan combination vs -E3^5*E6^-2*j(12,15) through Q^{CHECK_DEG}: {'OK' if not diffs else 'FAIL'}")
    if diffs:
        print(f"first diffs={diffs[:12]}")
        raise SystemExit(1)
    sample = [(e, lhs.get(e, 0)) for e in range(0, CHECK_DEG + 1) if lhs.get(e, 0)]
    print("nonzero coefficients through Q^44:")
    print(sample)
    verify_theta_correction()


if __name__ == "__main__":
    main()
