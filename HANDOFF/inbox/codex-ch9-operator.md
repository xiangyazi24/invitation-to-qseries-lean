# TASK (codex / gpt-5.5): Ch9 UNCONDITIONAL Bailey's lemma via Fubini reindex (Opus-designed, complete)

## Goal — the genuine unconditional Lemma 9.1 / Theorems 9.1 & 9.2 (NO kernel hypothesis)
Edit `QseriesFormalization/Chapter09_BaileyLemma.lean`. Prove the all-`n` operator identity
```
lemma91_operator : ∀ n, L x q (M x q α) n = M x q (D x q α) n
```
(with legitimate domain nonzero hyps on x,q — same `(q;q)_k ≠ 0`, `1 - x q^{k+1} ≠ 0` conditions that
`lemma91_matrix_entry_shifted` already carries; these are honest domain conditions, NOT the smuggled
kernel). Then derive **Theorem 9.1** `L (M α) = M (D α)` (= Bailey's lemma: if `β = Mα` then
`Lβ = M(Dα)`) and **Theorem 9.2** `L (L (Mα)) = M (D (Dα))` (i.e. `L²β = M D² α`) by one more application.
This is UNCONDITIONAL — it does NOT use `BaileyKernelIdentity`. (The kernel was only for the more
general ρ₁,ρ₂ `BaileyTransform`; the basic Lemma 9.1 needs only `lemma91_matrix_entry_shifted`.)

## The complete proof (Opus-derived + verified — this is bookkeeping, not new reasoning)
Recall the defs (your file):
- `L x q β n = ∑_{k=0}^n x^k q^{k²}/(q;q)_{n-k} · β k`
- `M x q α n = ∑_{j=0}^n α_j/((q;q)_{n-j}(xq;q)_{n+j})`   (BaileyBeta)
- `D x q α n = x^n q^{n²} · α n`

Step 1 — expand LHS:
```
L x q (M x q α) n = ∑_{k=0}^n x^k q^{k²}/(q;q)_{n-k} · (∑_{j=0}^k α_j/((q;q)_{k-j}(xq;q)_{k+j}))
                  = ∑_{k=0}^n ∑_{j=0}^k  α_j · x^k q^{k²} / ((q;q)_{n-k}(q;q)_{k-j}(xq;q)_{k+j})
```
Step 2 — **Fubini swap** the triangular region `{(k,j) : 0≤j≤k≤n}` to `∑_{j=0}^n ∑_{k=j}^n`
(Mathlib: `Finset.sum_sigma'` / `Finset.sum_comm'`, or `Finset.sum_range_succ`-style triangle lemma;
the region is `(k,j)` with `j ≤ k`, swap to fix `j` then `k ∈ Finset.Icc j n`):
```
= ∑_{j=0}^n α_j · (∑_{k=j}^n  x^k q^{k²}/((q;q)_{n-k}(q;q)_{k-j}(xq;q)_{k+j}))
```
Step 3 — reindex inner sum `k = j + k'`, `k' = 0..n-j`, then it is **exactly**
`lemma91_matrix_entry_shifted` with `m := j`, `N := n - j`:
```
∑_{k'=0}^{n-j} x^{j+k'} q^{(j+k')²}/((q;q)_{(n-j)-k'}(q;q)_{k'}(xq;q)_{k'+2j})
   = x^j q^{j²}/((q;q)_{n-j}(xq;q)_{(n-j)+2j})            -- lemma91_matrix_entry_shifted m=j N=n-j
   = x^j q^{j²}/((q;q)_{n-j}(xq;q)_{n+j}).
```
Step 4 — substitute back:
```
L x q (M x q α) n = ∑_{j=0}^n α_j · x^j q^{j²}/((q;q)_{n-j}(xq;q)_{n+j})
                  = ∑_{j=0}^n (x^j q^{j²} α_j)/((q;q)_{n-j}(xq;q)_{n+j})
                  = ∑_{j=0}^n (D x q α)_j /((q;q)_{n-j}(xq;q)_{n+j})
                  = M x q (D x q α) n.            ∎
```
(I verified Steps 1–4 align exactly with your `lemma91_matrix_entry_shifted` statement — the inner sum
matches its LHS at `m=j, N=n-j` and its RHS is the `M(Dα)` coefficient.)

## Rules
- Edit ONLY `Chapter09_BaileyLemma.lean`. The hard coefficient identity is DONE
  (`lemma91_matrix_entry_shifted`); this round is the Fubini reindex + assembly. NEVER native_decide;
  NEVER lake build; verify `lake env lean QseriesFormalization/Chapter09_BaileyLemma.lean`.
- 0 sorry/axiom/admit; clean-3 axioms. The all-`n` operator theorem + Thm 9.1/9.2 must be UNCONDITIONAL
  (only the q-Pochhammer/`1-xq^{k+1}` nonzero domain hyps; NO `BaileyKernelIdentity`).
- The derivation is verified — if a Lean step (esp. the Fubini reindex) resists, report the exact goal
  state, don't abandon. Reply to `HANDOFF/outbox/codex-ch9-operator-reply.md`.
