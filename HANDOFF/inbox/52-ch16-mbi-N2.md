# Task 52: Ch16 — MBI truncation N=2 explicit values

## Goal

In `Chapter16.lean`, add (extending t42 N=1 work):

```lean
theorem mbiLHSTrunc_two (q : R) :
    mbiLHSTrunc q 2 =
      (Ch01.partitionCount 4 : R) +
      (Ch01.partitionCount 9 : R) * q +
      (Ch01.partitionCount 14 : R) * q^2

-- Note: partitionCount 14 = 135 (proved in t22), which equals 27·5.
-- Demonstrating Ramanujan's p(5n+4) ≡ 0 mod 5 at n=2.

theorem mbiRHSNumeratorTrunc_two (q : R) :
    mbiRHSNumeratorTrunc q 2 = (1 - q^5)^5 * (1 - q^10)^5

theorem mbiRHSDenominatorTrunc_two (q : R) :
    mbiRHSDenominatorTrunc q 2 = (1 - q)^6 * (1 - q^2)^6
```

(For mbiLHSTrunc, use partitionCount_four=5, partitionCount_nine=30,
partitionCount_fourteen=135 from t22's extended table — but t22 only got
to p(11)=56. So `partitionCount 14` not yet proved. **Use only n's
that have explicit values: p(4)=5, p(9)=30**. Drop the q² term or note
TODO.)

Touch only Chapter16.lean. No axiom/sorry/native_decide. lake build clean.
