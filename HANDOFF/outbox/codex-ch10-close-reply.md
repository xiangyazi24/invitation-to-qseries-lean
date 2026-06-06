# Chan Ch10 close attempt

Status: blocked, not closed.

What I changed:
- `QseriesFormalization/Pending/Chapter10_TenthOrder.lean`
  now contains a precise formal-PS target for Chan Eq. (10.15) after
  substituting `q = Q^3`.
- Added:
  - `rhoInt`
  - `delta3Int`
  - `chan1015QExponent`
  - `chan1015CoeffTerm`
  - `chan1015LHSCoeff`
  - `chan1015LHSPS`
  - `qPochInfAtPowerPS`
  - `chan1015PentagonalPS`
  - `chan1015RHSPS`
  - `chan1015IdentityStatement`

The formal target is:

```lean
def chan1015IdentityStatement : Prop :=
  chan1015LHSPS ℚ = chan1015RHSPS
```

This is Eq. (10.15) in the `Q` variable:

```text
LHS coefficient of Q^N =
  finite four-variable coefficient sum for
  ρ_{r,s} (-1)^(k+l+r+s)
  (δ(k)-δ(r))(δ(l)-δ(s))
  Q^(k²+l²+r²+3rs+s²+3r+3s+1)

RHS =
  - (Q³;Q³)_∞^5 / (Q⁶;Q⁶)_∞^2
    * expand_3(∑_n (-1)^n Q^((5n²-3n)/2))
```

The final theorem is not asserted. I did not introduce any axiom or proof
hole.

Validation:
- `lake env lean QseriesFormalization/Pending/Chapter10_TenthOrder.lean`
  passes.
- `rg -n "sorry|admit|axiom" QseriesFormalization/Pending/Chapter10_TenthOrder.lean`
  returns no matches.
- A separate Python coefficient sanity check matched both sides through
  degree 15:
  `-1,0,0,6,0,0,-12,0,0,7,0,0,1,0,0,6`.

Irreducible blocker:
- The repo still lacks the theorem that actually proves the four-variable
  indefinite theta side equals the eta-product side.
- Chan's proof uses Lemma 10.1 and Lemma 10.2:
  - Lemma 10.1: the two-variable theta identity Eq. (10.34), proved in the
    book only by a sketch plus omitted functional-equation/zero-set details.
  - Lemma 10.2: Hickerson/Ramanujan `1ψ1` identity Eq. (10.39).
- I found no existing Mathlib or repo theorem equivalent to Lemma 10.2, and
  no existing two-variable Laurent constant-term framework sufficient to
  reproduce Chan's Step 3 formally.

Other notes:
- The requested `pdftotext` binary is not installed in this environment.
  I extracted Chapter 10 text from the local PDF via `pypdf` installed into
  `/tmp/codex_pdf`; no repo dependency was added.
- The prescribed non-interactive Gemini dispatch script
  `~/.openclaw/scripts/handoff-dispatch.sh` is not present on this machine,
  so I could not dispatch a subtask.
