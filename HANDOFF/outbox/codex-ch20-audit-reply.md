# Chapter 20 Audit: Chapter-Main Theorem

## Finding

The CHAPTER-MAIN theorem of Chan Chapter 20 is **Ono's Theorem 20.1**, not the basic Ramanujan tau/discriminant infrastructure.

In the PDF, Chapter 20 is titled:

> Excursus: modular forms and more congruences for the partition function

The chapter immediately states its purpose: to sketch the proof of a result of K. Ono (2000) about partition congruences. The theorem displayed at the start of the chapter is Theorem 20.1:

```text
For m >= 5, there are infinitely many congruences of the form
  p(An + B) == 0 (mod m).
```

The following sentence says that the chapter first gives a brief introduction to modular forms as the essential tools for proving Theorem 20.1, and then sketches the proof of the main result in three steps. Section 20.2 is explicitly titled "The proof of Theorem 20.1", and the proof closes by saying this proves Ono's theorem.

## What The Infrastructure Is Doing

The modular-form material in Section 20.1 is supporting machinery for Ono's theorem:

- congruence subgroups, cusps, modular forms, cusp forms, and Nebentypus;
- examples including Eisenstein series, the cusp form `Delta(z) = eta(z)^24`, and `eta(24z)`;
- `U_t`, `V_t`, and half-integral-weight Hecke operator `T(l^2)`;
- the eta quotient `E_m(z) = eta(z)^m / eta(mz)` and its modular/congruence/cusp properties.

This infrastructure is used in Section 20.2 to build `f_m(z)`, prove `f_m == F_m (mod m)`, prove `f_m` is a half-integral-weight cusp form for large enough exponent, and then apply Hecke operators plus Shimura/Serre input to obtain the partition congruences.

## Negative Finding: Not Tau Main

Chapter 20 does **not** present a Ramanujan tau-value development as its main theorem. In the chapter text, `Delta(z) = eta(z)^24` appears only as an example of a cusp form and later inside the auxiliary cusp-form check. I did not find a development of the Ramanujan tau function `tau(n)`, explicit tau values, or the full Hecke multiplicativity of `tau(n)` as the chapter target.

The symbol `tau` appearing in the proof is instead a positive integer exponent in the construction of `f_m(z)`, not Ramanujan's tau function.

## Formalization Implication

For chapter-accurate naming:

- `CHAPTER-MAIN` should point to an Ono/Theorem 20.1-style partition-congruence statement, at least as a high-level theorem or explicitly marked analytic/modular-form gap.
- The existing discriminant, tau values, and small Hecke-recursion infrastructure should be treated as auxiliary or adjacent formal-PS work, not as the main theorem of Chan Chapter 20.
- The current `QseriesFormalization/Chapter20.lean` header claim that Chan Ch20's main result is modular invariance of `Delta` and full multiplicativity of `tau(n)` is not supported by the PDF text.

No Lean code was written for this audit.
