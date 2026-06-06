# codex rawbridge reply

## Result

Edited `QseriesFormalization/Pending/Chapter10_PF.lean` for code.

Added the raw `branchInvCoeffAtPF` coefficient layer and proved the
raw-to-compressed bridge:

```lean
def thetaMulPFRawBranchTermPF (N : ℕ) (z k r : ℤ) : ℤ
def thetaMulPFRawPositiveCoeffPF (N : ℕ) (z : ℤ) : ℤ
def thetaMulPFRawNegativeCoeffPF (N : ℕ) (z : ℤ) : ℤ
def thetaMulPFRawCoeffPF (N : ℕ) (z : ℤ) : ℤ

theorem thetaMulPFRawPositiveBranchTerm_eq_compressedPF
theorem thetaMulPFRawNegativeBranchTerm_eq_compressedPF

theorem thetaMulPFRawPositiveCoeffPF_eq_thetaMulPFPositiveCoeffPF
    (N : ℕ) (z : ℤ) :
    thetaMulPFRawPositiveCoeffPF N z = thetaMulPFPositiveCoeffPF N z

theorem thetaMulPFRawNegativeCoeffPF_eq_thetaMulPFNegativeCoeffPF
    (N : ℕ) (z : ℤ) :
    thetaMulPFRawNegativeCoeffPF N z = thetaMulPFNegativeCoeffPF N z

theorem thetaMulPFRawCoeffPF_eq_thetaMulPFCoeffPF (N : ℕ) (z : ℤ) :
    thetaMulPFRawCoeffPF N z = thetaMulPFCoeffPF N z
```

The positive bridge uses `k ≥ 0`, `m = h-k`, `r = k+z-h`.  The negative
bridge uses denominator index `-c-1`, branch power `m = c-h`, and
`r = h+z-c`.  Both term lemmas keep `branchInvCoeffAtPF` visible and prove
the actual q-exponent and sign reindexing into the compressed families.

## Validation

```text
lake env lean QseriesFormalization/Pending/Chapter10_PF.lean
```

passed with no output.

Forbidden-token grep on `Chapter10_PF.lean` found no matches for
`native_decide`, `axiom`, `admit`, `opaque`, `sorry`, or `def .*: Prop`.

## Axioms

Source-copy `#print axioms`:

```text
'QseriesFormalization.Pending.Chapter10PF.thetaMulPFRawPositiveCoeffPF_eq_thetaMulPFPositiveCoeffPF' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Chapter10PF.thetaMulPFRawNegativeCoeffPF_eq_thetaMulPFNegativeCoeffPF' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Chapter10PF.thetaMulPFRawCoeffPF_eq_thetaMulPFCoeffPF' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Chapter10PF.thetaMul_PF_eq_qPochInfPS_pow_three' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```
