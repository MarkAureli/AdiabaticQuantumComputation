# Agent Instructions

## Issue Tracking

This project uses **bd (beads)** for issue tracking.
Run `bd prime` for workflow context, or install hooks (`bd hooks install`) for auto-injection.

**Quick reference:**
- `bd ready` - Find unblocked work
- `bd create "Title" --type task --priority 2` - Create issue
- `bd close <id>` - Complete work
- `bd sync` - Sync with git (run at session end)

For full workflow details: `bd prime`

## Build Command

```bash
lake build AdiabaticQuantumComputation 2>&1 | tail -40
```

**NEVER run bare `lake build`** — it rebuilds all of mathlib (~2 hours).

## Landing the Plane (Session Completion)

**When ending a work session**, you MUST complete ALL steps below. Work is NOT complete until `git push` succeeds.

**MANDATORY WORKFLOW:**

1. **File issues for remaining work** - Create issues for anything that needs follow-up
2. **Run quality gates** (if code changed) - `lake build AdiabaticQuantumComputation 2>&1 | tail -40`
3. **Update issue status** - Close finished work, update in-progress items
4. **Update HANDOFF.md session log** - Append what was done, current state, next steps
5. **PUSH TO REMOTE** - This is MANDATORY:
   ```bash
   git pull --rebase
   bd sync                          # exports .beads/issues.jsonl and stages it
   git add .beads/issues.jsonl
   git commit -m "chore: bd sync"  # commit the JSONL — required before push
   git push
   git status                       # MUST show "up to date with origin"
   ```
   Note: `bd sync` only exports the JSONL to disk; it does NOT create a git commit.
   The pre-push hook rejects pushes with uncommitted staged files, so the explicit
   `git commit` step is required.
6. **Verify** - All changes committed AND pushed
7. **Hand off** - Provide context for next session

**CRITICAL RULES:**
- Work is NOT complete until `git push` succeeds
- NEVER stop before pushing - that leaves work stranded locally
- NEVER say "ready to push when you are" - YOU must push
- If push fails, resolve and retry until it succeeds
