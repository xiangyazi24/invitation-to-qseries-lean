# Task 65: Ch9 — BaileyTerm zero / commutativity

In `Chapter09.lean`:

```lean
/-- BaileyTerm at k = 0 unfolds. -/
theorem BaileyTerm_zero (a q : R) (α : Nat → R) (n : Nat) :
    BaileyTerm a q α n 0 = α 0 / (qPochhammer q n * qPoch (a * q) q n)

/-- BaileyTerm only nonzero when k ≤ n (since (q;q)_{n-k} for k > n is …
   actually that's an issue: Nat sub truncates, so (q;q)_{n-k} = (q;q)_0 = 1
   for k > n. So BaileyTerm is non-trivial even out of range; that's a
   convention choice. Document this with a `theorem` or comment.) -/
theorem BaileyTerm_out_of_range_uses_truncated_pochhammer (a q : R)
    (α : Nat → R) (n k : Nat) (h : n < k) :
    BaileyTerm a q α n k =
      α k / (qPochhammer q 0 * qPoch (a * q) q (n + k)) := by
  unfold BaileyTerm
  rw [show n - k = 0 from Nat.sub_eq_zero_of_le (Nat.le_of_lt h)]
```

Touch only Chapter09.lean. No axiom/sorry/native_decide. lake build clean.
