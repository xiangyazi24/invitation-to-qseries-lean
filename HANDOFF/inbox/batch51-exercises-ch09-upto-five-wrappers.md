# batch51: Ch09 Exercises wrappers for Bailey up-to five

Repository: `~/.openclaw/workspace/projects/Q-series-and-Chan-s-work`

## Constraints

- Edit only `QseriesFormalization/Exercises.lean`.
- Do not edit `QseriesFormalization/Chapter09.lean`.
- No `sorry`, no `axiom`, no `native_decide`.
- Build only:

```bash
lake build QseriesFormalization.Exercises
```

## Task

Add straightforward Chapter 9 exercise wrappers for the already-proved Ch09
`N = 5` finite Bailey interface:

- `PartII.Ch09.BaileyBeta_five_expand`
- `PartII.Ch09.IsBaileyPairUpTo.five`
- `PartII.Ch09.IsBaileyPairUpTo.one_of_five`
- `PartII.Ch09.IsBaileyPairUpTo.two_of_five`
- `PartII.Ch09.IsBaileyPairUpTo.three_of_five`
- `PartII.Ch09.IsBaileyPairUpTo.four_of_five`
- `PartII.Ch09.IsBaileyPairUpTo.of_five`
- `PartII.Ch09.isBaileyPairUpTo_five_iff`
- `PartII.Ch09.rrAlpha_five`

Follow the existing naming style in the `Chapter9Exercises` section, e.g.
`exercise9_...`.

## Verification

Run:

```bash
lake build QseriesFormalization.Exercises
rg -n "^\\s*sorry\\b|^\\s*axiom\\b|\\bnative_decide\\b" QseriesFormalization || true
```

Expected warning: the existing Ch02 `jacobiTripleProduct` `sorry` only.
