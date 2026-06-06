# `QseriesFormalization/Pending/`

Files in this directory contain **statements only** (`theorem … := by sorry`)
of chapter-main results that are not yet proved.

This directory exists because of the playbook's point-4 / point-11 tension:

- Point 1 says "0 sorry repo-wide" — but only for results claimed as proved.
- Point 11 says targets must be stated honestly; the playbook explicitly
  allows `theorem … := by sorry` (and forbids `def : Prop := …` or
  `abbrev : Prop := …` to evade the count).

So instead of either
  (a) leaving the chapter-main result completely unstated in the file
      (which makes a SHADOW chapter undetectable from inside the repo), or
  (b) introducing `theorem … := by sorry` into the main chapter file
      (which contaminates the main repo's "0 sorry" property),

we place explicit `theorem … := by sorry` statements here, **outside the
main build graph**, so:

1. Anyone can see the precise Chan §N theorem statement in Lean syntax.
2. The main repo's `QseriesFormalization` root module remains 0-sorry.
3. When a chapter's main result is later proved in its real file, the
   corresponding `Pending/ChapterNN_*.lean` is deleted (not the proof
   moved to the file with sorry replacing the proof).

These files **are not** imported from `QseriesFormalization.lean`; the
root module's downstream consumers see only proved theorems.

Audit must skip this directory.  `PLAYBOOK_AUDIT.md` lists which chapters
have a `Pending/` stub vs. nothing at all.

## What counts as a valid Pending stub

A `Pending/ChapterNN_*.lean` file is only worth creating if a **precise
Lean statement** of the target theorem can be written.  If the precise
statement requires infrastructure that does not yet exist (e.g., mock-
modular completions for Watson's identity, or Gaussian polynomial sums
with floor-indexed arguments for Chan Thm 8.1), then the right move is
to leave the gap documented in `PLAYBOOK_AUDIT.md` / the chapter
disclosure header, and **not** to write a stub that fakes the statement.

In particular:
- `theorem foo : True := trivial` is a playbook point-4 violation
  (trivially-true conclusion) and must NOT be used as a placeholder.
- `def lhs := 0` followed by `theorem foo : lhs = 0 := rfl` is the
  same violation.  Defining the LHS as 0 makes the equality vacuous.

The MBI stub here is valid because the LHS uses `partitionGenFun.coeff`
which is genuine; the RHS uses `expand 5 (qPochInfPS R) ^ 5 *
partitionGenFun ^ 6` which is also genuine; their equality is the
non-trivial statement Chan proves.

— 2026-05-22

## Status (2026-05-23 update)

After the B2 chain closure (commit `2d55923`), most files in this directory
are now **SORRY-FREE** and have been added to the main `QseriesFormalization`
module graph:

  ✅ `JacobiCubeAnalyticToFormal.lean` — B2 `(qPochInfPS R)^3 = jacobiThetaPS R`
  ✅ `Chapter19_B2_FromCubeConvolution.lean` — derived cube convolution identity
  ✅ `Chapter17_Ramanujan5Conditional.lean` — Ramanujan's first congruence (unconditional)
  ✅ `Sylvester_TripleSum.lean` — Sylvester triple-sum theorems (via B2)
  ✅ `RamanujanTau_via_B2.lean` — τ(n+1) = ((jacobiThetaPS R)^8).coeff n
  ✅ `Watson_Mod25_SmallCases.lean` — 25 | p(24), 25 | p(49)

These should arguably be moved out of `Pending/` to a proper home (e.g.,
`Chapter17_Ramanujan/`, `Chapter19_B2/`).  Left in place for now to
preserve git history; downstream consumers reach them via the main module
graph regardless.

Only `Chapter16_MBI.lean` retains genuine sorries (the Most Beautiful
Identity — Chan §16, multi-week deep work).
