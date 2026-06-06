# Repository Guidelines

## Handoff Dispatch Rule
- Do not use the interactive `research-gemini` tmux pane for one-shot
  handoff tasks. Use
  `~/.openclaw/scripts/handoff-dispatch.sh gemini <task-file>` instead.
- Known failure mode: long prompts sent with `tmux send-keys` can remain in
  the terminal input line without a final Enter. If the pane is stuck, send
  only control keys or short commands; send `C-m` as a separate
  `tmux send-keys` call, then immediately verify with `tmux capture-pane`
  that the shell prompt is empty.

## Project Structure & Module Organization
This repository is currently document-focused. The root directory contains the primary asset: `An_Invitation_to_q_series.pdf`.

Use this layout as you contribute:
- Keep canonical published documents at the repository root or in a future `docs/` folder.
- Store editable source files (for example, `.tex`, `.md`, figures) in clearly named subfolders such as `src/` and `assets/`.
- Keep generated/exported artifacts separate from source files when possible.

## Build, Test, and Development Commands
There is no build pipeline configured yet. Use lightweight checks before submitting changes:

```bash
ls -lh
file An_Invitation_to_q_series.pdf
shasum -a 256 An_Invitation_to_q_series.pdf
```

- `ls -lh`: confirms file presence and expected size changes.
- `file ...pdf`: validates the artifact is a readable PDF.
- `shasum -a 256 ...pdf`: records a checksum for review and traceability.

## Coding Style & Naming Conventions
- Prefer descriptive, stable filenames.
- Follow the existing naming style for documents: `Title_With_Underscores.pdf`.
- Use ASCII filenames when possible; avoid spaces in new files to reduce tooling friction.
- Keep directory names short and purpose-driven (for example, `docs/`, `src/`, `assets/`).

## Testing Guidelines
- For document updates, perform visual review of changed pages before opening a PR.
- Verify metadata and page count are intentional after edits.
- If source files are added later (for example, LaTeX or scripts), include a reproducible build command in this guide and in the PR description.

## Commit & Pull Request Guidelines
Git history is not available in this workspace, so use a clear default convention:
- Commit format: `docs: short imperative summary` (example: `docs: update chapter 2 notation`).
- Keep commits focused on one change set (content update, rename, or asset cleanup).
- PRs should include:
  - What changed and why.
  - A short validation note (commands run, visual checks completed).
  - Before/after screenshots when layout or rendered pages change.
