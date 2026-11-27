# Providers and modes

The same skill works in **Claude Code** (from `.claude/skills/`) and **Codex** (from
`.agents/skills/`). `.claude/skills/` is the source; `~/.sigaba/bin/sigaba skills
sync` copies it, and a test checks that the copies are equal.

## Interactive mode (default)

You are the orchestrator in the user's session and start native subagents with the prompt files
`run next` returns. The watchdog (started by `run start`) posts checkpoints on time and marks a
worker stale when it reports nothing after its deadline, but it cannot interrupt a subagent.

## Supervised mode

`run start --backend claude` or `--backend codex`: the watchdog itself dispatches episodes as CLI
sessions in each task's worktree and terminates them at their deadline:

* Claude Code: `claude -p <prompt> --output-format stream-json --verbose --add-dir <core>
  --add-dir <SIGABA_HOME> --permission-mode acceptEdits`;
* Codex: `codex exec --json -C <worktree> --skip-git-repo-check --add-dir <core> --add-dir
  <SIGABA_HOME> --sandbox workspace-write <prompt>`.

Replace the permission arguments with `--worker-arg …` (repeatable) when the defaults do not let
the worker run `lake` and `python3`; do not grant broader permissions than that. Both use the
user's existing login; the controller never switches to a paid API or another account. A failed
worker process (quota, network, provider) is recorded as `infra_failure` and requeued, not counted
as failed mathematics. Logs: `~/.sigaba/state/runs/<run>/`.

## Hooks

`hooks install --provider claude|codex --task ID` writes command hooks into the task's worktree
only (`.claude/settings.local.json`, `.codex/hooks.json`; never global settings; other hooks are
kept). They record activity and make a checkpoint due when a session stops. Without hooks, the
watchdog does the same by its clock.
