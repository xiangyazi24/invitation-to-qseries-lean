# Task 69: Ch9 — Bailey term simplification at k=n

In `Chapter09.lean`:

```lean
theorem BaileyTerm_at_n (a q : R) (α : Nat → R) (n : Nat) :
    BaileyTerm a q α n n = α n / (qPochhammer q 0 * qPoch (a * q) q (2 * n)) := by
  unfold BaileyTerm
  rw [Nat.sub_self]
  ring_nf
  rfl

theorem BaileyTerm_at_n_simplified (a q : R) (α : Nat → R) (n : Nat) :
    BaileyTerm a q α n n = α n / qPoch (a * q) q (2 * n) := by
  rw [BaileyTerm_at_n]; simp [qPochhammer]
```

Touch only Chapter09.lean. No axiom/sorry/native_decide. lake build clean.
