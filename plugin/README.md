# The sigaba-neo plugin

Skills for cryptographic research with Sigaba-Neo, for Claude Code and Codex:
`sigaba-research` (the entry point: goals, tasks, runs), `sigaba-dag` (the DAG's rules) and
`sigaba-problem-author` (new primitives and goals). The protocol is the core's
`docs/RESEARCH_PROTOCOL.md`.

## Install

```text
# Claude Code
/plugin marketplace add MachinaIO/SigabaNeo
/plugin install sigaba-neo@sigaba-neo

# Codex
codex plugin marketplace add https://github.com/MachinaIO/SigabaNeo
codex plugin add sigaba-neo@sigaba-neo
```

The skills need the core (the controller and the Lean environment). On first use they run the
launcher, or run it yourself (from the installed plugin's directory):

```bash
scripts/sigaba install            # clone the pinned core into ~/.sigaba/releases/, build it
~/.sigaba/bin/sigaba doctor       # check git, gh, the DAG repository, the build, providers
```

Requirements: git, gh (logged in), Python 3.10+, Lean's elan (`lake`). The first build downloads
the Mathlib and cslib-frontier caches and takes a while.

`scripts/sigaba upgrade` moves to the plugin's current pin (`core.json`); `scripts/sigaba
uninstall` removes `~/.sigaba/bin/sigaba` and `~/.sigaba/core` and keeps releases, state and
worktrees. `SIGABA_HOME` moves everything away from `~/.sigaba`; `SIGABA_CORE` uses a checkout of
the core instead of the installed one.

The plugin installs no global hooks. The skills and the launcher are generated from the core's
`.claude/skills/` (`python3 python/sigaba_research.py skills sync`); do not edit `skills/` here.
