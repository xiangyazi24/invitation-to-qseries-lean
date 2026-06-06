# Chapter 9 Bailey N=8 — unblock strategy

**Source**: ChatGPT consultation 2026-05-14 (task `b8b0a00b`, returned for Q3).

## Diagnosis

The `ring`-tactic Gröbner-basis explosion on alpha_0 common-denominator
identity at N=8 is fundamental — it's a dense rational identity that's
the wrong shape for `ring`.

**STOP** trying to close it via one giant `ring`. Instead, use the
**q-Pfaff–Saalschütz kernel route**.

## Recommended path

### Primary target

```lean
theorem baileyKernelSum_eq_target
    (a q ρ₁ ρ₂ : ℂ) (n j : ℕ) (hj : j ≤ n) :
    baileyKernelSum a q ρ₁ ρ₂ n j = baileyKernelTarget a q ρ₁ ρ₂ n j
```

Or at minimum the special case `N = 8, j = 0`.

Then replace the N=8 alpha_0 common-denominator proof by invoking this
kernel identity.

### The q-Pfaff–Saalschütz specialization

After setting:
- `N = n - j`
- `r = k - j`
- `A = ρ₁ q^j`
- `B = ρ₂ q^j`
- `C = a q^(2j+1)`

the kernel inner sum becomes standard q-Pfaff–Saalschütz:

```
₃φ₂[q^(-N), A, B; C, ABq^(1-N)/C; q, q]
  = (C/A;q)_N · (C/B;q)_N / ((C;q)_N · (C/(AB);q)_N)
```

Substituting back:
- `AB q^(1-N) / C = ρ₁ ρ₂ q^(j-n) / a`
- `C/A = a q^(j+1) / ρ₁`
- `C/B = a q^(j+1) / ρ₂`
- `C/(AB) = a q / (ρ₁ ρ₂)`

The finite identity:
```
∑ r in range (N+1),
  (q^(-N);q)_r · (ρ₁ q^j;q)_r · (ρ₂ q^j;q)_r · q^r /
  ((q;q)_r · (a q^(2j+1);q)_r · (ρ₁ ρ₂ q^(j-n)/a;q)_r)
= (a q^(j+1)/ρ₁;q)_N · (a q^(j+1)/ρ₂;q)_N /
  ((a q^(2j+1);q)_N · (a q/(ρ₁ρ₂);q)_N)
```

### Fallback: if you must unblock the giant ring goal directly

**Don't run `ring` on the raw expression.** Instead:

1. **Atomize repeated factors** before `field_simp/ring`:
   ```lean
   set A1 : ℂ := 1 - q with hA1
   set A2 : ℂ := 1 - q^2 with hA2
   ...
   set B1 : ℂ := 1 - a*q with hB1
   ...
   ```
   Use `change` so the goal is rational in these atoms. Don't unfold before `ring`.

2. **Clear denominators manually**:
   ```lean
   have hD : D ≠ 0 := mul_ne_zero ...
   apply (mul_right_injective₀ hD)
   calc lhs * D = lhsNum := by ring_nf
     _ = rhsNum := by -- split this into 2-5 smaller identities
     _ = rhs * D := by ring_nf
   ```

3. **Split numerator equality** into grouped sub-identities:
   ```lean
   have h01 : term0 + term1 = block01 := by ring
   have h23 : term2 + term3 = block23 := by ring
   ...
   linear_combination h01 + h23 + ...
   ```
   This is where `linear_combination` shines — combining proved small
   polynomial identities, not solving one huge.

### Tactics NOT to use

- `polyrith` — wrong tool, doesn't help with single enormous rational identity.

### Tactics TO use (after atomizing)

- `field_simp [specific_nonzero_lemmas]`
- `ring_nf`
- `ring`
- `linear_combination`

## Concrete order

1. Prove specialized q-PS lemma in this codebase's notation for `N = 8, j = 0`.
2. Use it to replace the alpha_0 common-denominator identity.
3. Generalize to all `n, j`.
4. Delete/quarantine the giant explicit ring proof.

## Assignment

Per CHECKPOINT, Codex is on Ch9. This doc gives the q-PS-based unblock plan.
