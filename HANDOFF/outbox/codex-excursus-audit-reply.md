# Excursus Audit Reply: Ch10 and Ch20

## Short answer

Under the current playbook standard, **no**: an Excursus chapter should not be
classified as `PASS` merely because the repo contains rigorous infrastructure
that exceeds the level of detail in Chan's sketch, if the sketched chapter-main
theorem itself is not formalized.

The honest classification is:

- **Ch20: AUX / EXCURSUS-AUX**, not `PASS`.
- **Ch10: AUX / EXCURSUS-AUX**, not `PASS`.

If we want to recognize this kind of overachievement, use a separate label such
as `EXCURSUS-COVERED`, `AUX+`, or `SKETCH-SUPERSEDING-INFRA`. Do not overload
`PASS`.

## Source checks

I checked the local PDF and repo files.

For Ch20, Chan explicitly frames the chapter as an excursus whose purpose is to
"sketch a proof" of Ono's theorem. The chapter-main displayed theorem is
Theorem 20.1:

```text
For m >= 5, there are infinitely many congruences of the form
  p(An + B) == 0 (mod m).
```

The chapter then says it will give modular-form background and "sketch the proof
of the main result in three steps." Section 20.2 is titled "The proof of Theorem
20.1" and the proof closes by invoking Shimura correspondence plus Serre's
result, with a pointer to Ono (2000) for technical details.

For Ch10, the local PDF shows that the chapter is also titled as an Excursus.
It presents tenth-order mock theta functions `phi` and `psi`, announces Eq.
(10.10), and says the proof follows Zwegers (2010). In the proof of Lemma 10.1
Chan writes, "Let us sketch Zwegers' proof." The chapter also imports Choi
Hecke-type identities, a theta identity pushed to exercises, and Hickerson's
identity.

Repo-side checks:

- `PLAYBOOK_AUDIT.md` defines `PASS` as: chapter-main result is stated, fully
  proved, and all 11 points hold.
- `QseriesFormalization/Pending/Chapter10_MockTheta_PS.lean` says explicitly
  that it is **AUX-level scaffolding** and that Chan Ch10's chapter-main result
  is not closed. It formalizes a third-order Ramanujan mock theta `f(q)`, not
  Chan's tenth-order `phi/psi` target.
- `QseriesFormalization/Chapter20.lean` says explicitly that it is an **AUX
  chapter** and that full modularity/Ono-level modular-form content is open.
- `Chapter20_TauExtend.lean`, `Chapter20_TauMult.lean`, and
  `Pending/Chapter20_TauParity.lean` contain real tau/discriminant work:
  tau values through 50, many concrete Hecke multiplicativity/prime-power
  checks, and the tau parity theorem.

## Why "sketch" does not imply PASS

The playbook standard is theorem-centric, not effort-centric:

```text
PASS = chapter-main result stated + fully proved
```

So the audit question is not:

```text
Did we formalize something more rigorous than Chan wrote locally?
```

It is:

```text
Did we formalize the theorem Chan presents as the chapter's main result?
```

For an excursus, Chan's proof may be deliberately incomplete or externally
referential. That fact changes how we should describe the source chapter, but it
does not turn unrelated or adjacent infrastructure into a proof of the stated
theorem.

The clean rule:

1. If Chan states a main theorem and only sketches the proof, then `PASS`
   requires us to supply a complete Lean proof of that theorem, possibly by a
   different route.
2. If we only formalize definitions, examples, special cases, coefficient
   checks, or nearby infrastructure, the chapter remains `AUX`.
3. If the Lean theorem is conditional on the deep external result Chan cites
   and that external result is not formalized in the build graph, the result is
   not `PASS`; it is conditional/AUX under points 7 and 11.
4. If a chapter genuinely contains no theorem-proof target beyond exposition,
   the honest solution is a separate non-PASS category, not silent promotion.

## Ch20 classification

Ch20 should remain **AUX / EXCURSUS-AUX**.

The repo's Ch20 work is mathematically substantial, and in some tau/discriminant
directions it is more rigorous than Chan's local discussion. But it does not
formalize Ono's Theorem 20.1:

```text
for m >= 5, infinitely many partition congruences p(An+B) == 0 mod m.
```

Nor does it formalize the modular-form proof ingredients needed in Chan's
sketch: half-integral-weight forms, the relevant Hecke operators on cusp forms,
Shimura correspondence, Serre's result, and the construction proving the
infinitely-many congruences.

Therefore Ch20 can be advertised as:

```text
Substantive formal-PS/tau infrastructure exceeding Chan's local example-level
detail, but not a proof of the chapter-main Ono theorem.
```

It should not be advertised as:

```text
Chan Ch20 PASS.
```

## Ch10 classification

Ch10 should also remain **AUX / EXCURSUS-AUX**.

The current Lean file proves useful formal-power-series facts for Ramanujan's
third-order mock theta `f(q)` and coefficient stabilization through degree 10.
That is real work, but Chan Ch10's target is a tenth-order mock theta identity
involving `phi(q)`, `psi(q)`, a root-of-unity filter, and an equivalent
four-variable indefinite-theta / constant-term identity.

So Ch10 is even less eligible for `PASS` than Ch20 under strict statement
fidelity: the repo infrastructure is not merely missing the final sketched
proof; it is aimed at a different mock-theta family than Chan's displayed
chapter target.

## Recommended audit wording

Suggested wording for both chapters:

```text
Excursus chapter. Chan sketches, rather than gives, a complete proof of the
chapter-main theorem. The repository contains rigorous auxiliary infrastructure
that goes beyond the level of detail in Chan's sketch, but the stated/sketched
chapter-main theorem is not formalized. Verdict: AUX / EXCURSUS-AUX, not PASS.
```

For Ch20, add:

```text
The formalized tau/discriminant material is adjacent to the modular-form
background, but Ono's infinite-congruence theorem is not formalized.
```

For Ch10, add:

```text
The formalized mock-theta `f(q)` infrastructure is useful but does not yet state
or prove Chan's tenth-order Zwegers/Choi identity.
```

## Bottom line

Under the playbook's `chapter-main result stated+proved` standard, **Excursus
does not lower the bar to "we formalized more than the author wrote in the
sketch."** It only explains why the chapter may fairly remain AUX despite strong
formal infrastructure.

`PASS` is appropriate only after the sketched theorem itself is formalized and
proved end-to-end in Lean.
