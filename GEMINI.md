# GEMINI.md — Project Instructions

## Rules

1. **Never ask questions.** Execute tasks directly. If something is unclear, make a reasonable assumption and proceed.
2. **Never ask for permission.** You are in yolo mode. Read files, edit files, run commands — just do it.
3. **All task files are in this workspace.** Read them with @path relative to project root.
4. **After each edit, verify with `lake build`.** Fix errors yourself without asking.
5. **No sorry, no axiom, no native_decide.**
6. **Write results to HANDOFF/outbox/.** Don't just print to chat.
7. **Do not use the interactive `research-gemini` tmux pane for one-shot handoff tasks.** Those tasks must be launched through `~/.openclaw/scripts/handoff-dispatch.sh gemini <task-file>`, which uses headless `gemini -p` and avoids the known failure mode where a long prompt remains in the terminal input line without a final Enter.
8. **If `research-gemini` appears stuck, clear and verify before dispatching anything else.** Send only control keys (`tmux send-keys -t zinan:12 C-c` then `tmux send-keys -t zinan:12 C-m`) and immediately confirm with `tmux capture-pane -pt zinan:12 -S -20` that the shell prompt is empty. Never paste a long task prompt into this pane.
