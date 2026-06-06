# TASK (codex / gpt-5.5): close the mod-11 residue-extraction sorry

## Goal
Close the **single remaining `sorry`** in
`QseriesFormalization/Pending/Chapter17_Hirschhorn_Mod11.lean`, namely

```lean
theorem coeff_qPochInfPS_pow_twentyone_at_11n_plus_6_eq_zero :
    ∀ k, ((qPochInfPS (ZMod 11))^21).coeff (11 * k + 6) = 0 := by
  sorry
```

This is equivalent to `section11 6 (S^7) = 0` where `S := (qPochInfPS (ZMod 11))^3`.
(`((qPoch)^21).coeff (11k+6) = (S^7).coeff (11k+6)`, and ranging over all `k`
that is exactly `section11 6 (S^7) = 0`.)

**Hard constraints (playbook):** 0 `sorry`, 0 `axiom`, 0 `admit`, no new
hypotheses smuggled in, no `native_decide` hacks that hide the math. The file
must compile clean. Do NOT weaken any statement.

## What is ALREADY PROVEN in the repo (use these, do not reprove)
All in `QseriesFormalization/Pending/Chapter17_Hirschhorn_Mod11.lean` unless noted.

1. `section11 (R) (r) (φ) : R⟦X⟧` — keeps coeffs at indices `≡ r (mod 11)`.
   - `coeff_section11 R r φ n : (section11 R r φ).coeff n = if n % 11 = r then φ.coeff n else 0`
   - `sum_section11_eq R φ : ∑ r ∈ Finset.range 11, section11 R r φ = φ`
   - `coeff_section11_of_ne R r φ n (h : n % 11 ≠ r) : (section11 R r φ).coeff n = 0`
   - `coeff_section11_mul_section11_of_ne R r s φ ψ n (h : n % 11 ≠ (r+s) % 11) :
        (section11 R r φ * section11 R s ψ).coeff n = 0`

2. `J (i) : (ZMod 11)⟦X⟧ := section11 (ZMod 11) i ((qPochInfPS (ZMod 11))^3)`
   - `qPochInfPS_cube_decompose_mod_11 : (qPochInfPS (ZMod 11))^3 = J 0 + J 1 + J 3 + J 6 + J 10`

3. **Relations** (residue-r parts of `(qPoch)^12 = S^4` vanish):
   `coeff_qPochInfPS_pow_twelve_zero_off_pentagonal (r) (hr : r=3∨r=6∨r=8∨r=9∨r=10) (n) :
       ((qPochInfPS (ZMod 11))^12).coeff (11*n + r) = 0`
   Note `(qPoch)^12 = (S)^4` since `S = (qPoch)^3`. So `section11 r (S^4) = 0` for r∈{3,6,8,9,10}.

4. **The combination identity (the algebraic core, PROVEN)** in
   `QseriesFormalization/Pending/Chapter17_Hirschhorn_Combination.lean`:
   `HirschhornComb.hirschhorn_P_eq_combination {R} [CommRing R] [CharP R 11] (a b c d e : R) :
       P(a,b,c,d,e) = M3(a..e)*R3(a..e) + M6*R6 + M8*R8 + M9*R9 + M10*R10`
   where, with `a,b,c,d,e = J0,J1,J3,J6,J10`:
   - `P` = the residue-6 part of `(a+b+c+d+e)^7` (the explicit 30-monomial sum — see the file).
   - `R_r` = the residue-r part of `(a+b+c+d+e)^4` (explicit 6-monomial sums — see the file).
   - `M_r` = explicit degree-3 multipliers.
   The EXACT monomials are in the body of `hirschhorn_P_eq_combination`; copy them verbatim.

## Strategy (recommended; deviate if you find cleaner)
The two missing "extraction" facts:

  (E7)  `section11 6 (S^7) = P(J0,J1,J3,J6,J10)`            -- residue-6 part of S^7
  (E4)  for each r∈{3,6,8,9,10}, `R_r(J0,...,J10) = section11 r (S^4) = 0`

Then:
```
section11 6 (S^7) = P(J)                       -- (E7)
                  = Σ M_r(J) · R_r(J)          -- hirschhorn_P_eq_combination J0 J1 J3 J6 J10
                  = Σ M_r(J) · 0 = 0           -- (E4)
```
and `((qPoch)^21).coeff (11k+6) = (section11 6 (S^7)).coeff (11k+6) = 0`.

Recommended tool for (E7)/(E4): introduce a predicate
`IsRes (s) (φ) := ∀ n, n % 11 ≠ s → φ.coeff n = 0` (φ supported on residue s, s<11) and prove:
  - `J i` satisfies `IsRes i` for i∈{0,1,3,6,10}  (from `coeff_section11_of_ne`)
  - `IsRes` is closed under `*` (residues add mod 11) and under numeral `•`/`+` of same residue
  - if `IsRes s φ` then `section11 t φ = (if t = s then φ else 0)`
Then expand `S^k = (J0+J1+J3+J6+J10)^k` (e.g. `ring_nf` or iterated `add_pow`/`mul_add`),
push `section11 t` through the sum (it is additive: `(section11 R r).coeff` is additive,
and `section11 R r (φ+ψ) = section11 R r φ + section11 R r ψ` — prove this `add` lemma),
and each monomial collapses to itself (if its weighted residue ≡ t) or 0.
The residue of a monomial `J0^a J1^b J3^c J6^d J10^e` is `(0a+1b+3c+6d+10e) % 11`.

Beware: the degree-7 expansion has 330 monomial types (30 survive at residue 6). The
degree-4 expansion has 70 (6 survive per residue). `ring_nf` then a big `simp` collapse may
be heavy; consider proving a clean `section11_add` + a `section11_mul_of_isRes` collapsing
lemma so each monomial is one rewrite. Use `set_option maxHeartbeats 4000000 in` if needed.

## Build / verify (on this machine = the-build-server)
```
cd ~/repos/Q-series-and-Chan-s-work
export NVM_DIR=~/.nvm; source ~/.nvm/nvm.sh; nvm use 22 >/dev/null   # (already loaded if codex env)
~/.elan/bin/lake env lean QseriesFormalization/Pending/Chapter17_Hirschhorn_Mod11.lean
```
(That single-file check is ~10-30s with cached oleans. Only run full `lake build` at the very end.)
Confirm: no `error`, and crucially `grep -n "sorry" QseriesFormalization/Pending/Chapter17_Hirschhorn_Mod11.lean`
shows the headline sorry is GONE.

## Deliverable
Edit `QseriesFormalization/Pending/Chapter17_Hirschhorn_Mod11.lean` in place: add whatever
helper lemmas (`IsRes`, `section11_add`, extraction lemmas) you need above the theorem, and
replace the `sorry` with a real proof. When done, write a short summary to
`HANDOFF/outbox/codex-mod11-extraction-reply.md` (what you proved, any lemmas added, final
build status). Do not touch other files except the two Hirschhorn files if strictly needed.
