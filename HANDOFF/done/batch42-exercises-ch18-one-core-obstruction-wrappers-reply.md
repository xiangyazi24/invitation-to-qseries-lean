# Batch 42: Exercises — Ch18 one-core obstruction wrappers

## Declarations added

The following wrappers were added to `QseriesFormalization/Exercises.lean`:

- `exercise18_hasHookDivisibleBy_one_iff_exists_FerrersCell`
- `exercise18_not_oneCoreByHooks_of_FerrersCell`
- `exercise18_FerrersCell_cons_zero_zero`
- `exercise18_not_oneCoreByHooks_cons_pos`
- `exercise18_not_oneCoreByHooks_iff_exists_FerrersCell`

## Build result

`lake build QseriesFormalization.Exercises` completed successfully.

The build replayed Chapter 02 and printed the known warning:

```text
warning: QseriesFormalization/Chapter02.lean:98:8: declaration uses 'sorry'
```

## Forbidden-token check result

`rg -n "sorry|axiom|native_decide" QseriesFormalization/Chapter18.lean QseriesFormalization/Exercises.lean`
returned no matches.

## Note

Gemini encountered repeated backend `500` errors during dispatch. The partial
file edits were inspected locally; one additional wrapper was added locally;
validation and this report were completed locally.
