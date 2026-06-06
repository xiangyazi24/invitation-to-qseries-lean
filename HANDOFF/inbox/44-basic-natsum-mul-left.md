# Task 44: Basic — natSum_mul_left helper

## Goal

Add `natSum_mul_left` to `Chapter03.lean` (mirror of `natSum_mul_right`):

```lean
lemma natSum_mul_left (a : R) (f : Nat → R) :
    ∀ n, natSum (fun k => a * f k) n = a * natSum f n
  | 0 => by simp
  | Nat.succ n => by
      rw [natSum_succ, natSum_succ, natSum_mul_left a f n]
      ring
```

Useful for downstream tasks. Touch only `Chapter03.lean`. No
axiom/sorry/native_decide. lake build clean.

## Deliverable

Modified file + reply.
