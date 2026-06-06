# codex-ch20-v3 reply

## PDF scan

`pdftotext` is not installed in this environment (`command not found`). I used a
temporary local `pypdf` install under `HANDOFF/tmp/python-pdf` to extract Chapter
20 text, then removed the temporary install and extracted text.

Chapter 20 contains these numbered theorem/lemma statements:

- Theorem 20.1: Ono partition congruences, stated as infinitely many congruences
  `p(An + B) ≡ 0 (mod m)` for `m >= 5`. The proof later works with prime
  `m >= 5`.
- Lemma 20.1: eta quotient `E_m(z) = eta(z)^m / eta(mz)` has modularity,
  congruence, and cusp-vanishing properties.
- Lemma 20.2: for prime `m >= 5`, the auxiliary form `f_m(z)` is congruent to
  the partition generating function `F_m(z)` modulo `m`.
- Lemma 20.3: for prime `m >= 5` and sufficiently large `tau`, `f_m(z)` is a
  half-integral-weight cusp form on `Gamma0(576m)` with character.

There are no Chapter 20 propositions. The only proposition mention is an
external citation to Proposition 2.22 in Ono (2003) for properties of `U_t` and
`V_t`.

## Formalization check

The actual Chapter 20 lemmas remain blocked by missing modular-form
infrastructure: eta-quotient modularity and cusp criteria, congruence subgroups
with characters, cusps, half-integral weights, `U_t`/`V_t` preservation theorems,
half-integral Hecke operators, Shimura correspondence, and Serre density.

The tau-related candidates are adjacent infrastructure, not numbered Chapter 20
theorems in the PDF. Among them, the only direct extension available from the
current `Chapter20.lean` data was finite Lehmer verification through the computed
tau table.

## Lean change

Added to `QseriesFormalization/Chapter20.lean`:

```lean
theorem ramanujanTau_ne_zero_through_fifty
    (n : Nat) (hn0 : 1 ≤ n) (hn50 : n ≤ 50) :
    ramanujanTau ℤ n ≠ 0
```

This proves `tau(n) != 0` for every `1 <= n <= 50` by interval splitting and the
existing explicit tau value theorems `ramanujanTau_one` through
`ramanujanTau_fifty`.

I did not add:

- new tau congruences beyond `p = 2, 3, 5, 7`: no such Chapter 20 theorem was
  found, and the naive statement `tau(p) ≡ 0 (mod p)` is already false at
  `p = 11`;
- general tau multiplicativity or Delta Hecke eigenform theorem: current code has
  finite spot checks only, not the modular-form Hecke theory needed for a general
  theorem;
- wrappers around Ono 20.1 or Lemmas 20.1--20.3.

## Verification

Ran:

```bash
lake env lean QseriesFormalization/Chapter20.lean
```

Result: passed with no output.

Also scanned the touched file for forbidden proof placeholders:

```bash
rg -n "sorry|admit|axiom" QseriesFormalization/Chapter20.lean
```

Result: no matches.
