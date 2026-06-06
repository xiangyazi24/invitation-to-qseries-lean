# Task: Extend Ch20 τ values from τ(35) to τ(50)

## Context
`QseriesFormalization/Chapter20.lean` has Ramanujan τ values τ(0)..τ(35) and
Hecke multiplicativity/prime-power recursion instances.

## What to do
1. Read `Chapter20.lean` to understand the current state
2. Extend `ramanujanTau` computed values from τ(35) to τ(50)
3. Add new Hecke multiplicativity instances for coprime pairs up to 50
4. Add new prime-power Hecke recursion instances (p=2,3,5,7 at higher k)

## Proof pattern for τ values
Each τ(n) theorem follows the pattern:
```lean
theorem ramanujanTau_N : ramanujanTau ℤ N = <value> := by
  unfold ramanujanTau discriminantPS
  simp [etaPS, qPochInfPS, ...]
  -- or use Hecke recursion: τ(p·n) = τ(p)·τ(n) - p^11·τ(n/p)
```

For larger n, use Hecke recursion τ(p·k) = τ(p)·τ(k) - p^11·τ(k/p) (for prime p, gcd(k,p)=1 or p|k). This avoids expanding the full power series.

## Hecke multiplicativity pattern
For coprime m, n: `ramanujanTau_mul_m_n : τ(m*n) = τ(m) * τ(n)`
Proof: `rw [ramanujanTau_N, ramanujanTau_M, ramanujanTau_MN]; ring`

## Build
```
export PATH=$HOME/.elan/bin:$PATH
lake env lean QseriesFormalization/Chapter20.lean
```
WARNING: Chapter20 is in the main build graph. Do NOT introduce sorry or axiom.
Test with `lake env lean` first, then `lake build QseriesFormalization.Chapter20`.

## Constraints
- NO sorry, NO axiom, NO native_decide
- Each new theorem must compile
- Keep file organized: τ values section, then multiplicativity, then Hecke recursion
- Use existing naming conventions (look at τ(34), τ(35) for pattern)
