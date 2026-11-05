# 0002 Land direct to main: no pull requests, one coordinator (`scripts/land-direct`)

Status: accepted (the owner's decision, via main). Single-commit mode; the batch cycle is not ported.

## Decision
vbm-json has **no pull requests**. Agents work in worktrees of one clone, so they share one git common dir: that is where the single coordinator lives. A worker commits locally
(never pushes a branch), then runs `scripts/land-direct`, which lands the commits on `origin/main` itself. `scripts/land` (the PR lander) and `scripts/test_land.sh` are retired in the same change: nothing
else referenced them (the references in the docs, the hook message, the lint list and the protected set were moved to `land-direct`).

## What it does
Under one `flock` on `<git common dir>/land.lock` (90 s patience, `LAND_LOCK_WAIT_SECONDS`; exit 15 busy): hold check -> red-check (main's latest push run of `core.yml`: its `tier1` job failed, or `gh` unreachable = only a
`fix(ci):`/`fix(tests):`/revert commit lands; except a red that is infrastructure, `scripts/infra-re.sh`: a job that never started because of account payments or a spending limit, a lost runner, a network or service error in the failed job's annotations or log, which says nothing about the commit and does not freeze landing) -> fetch -> rebase onto `origin/main` in a scratch worktree (`<common>/vbm-json-land-direct/wt`, warm `.lake`) -> a conflict only in `scripts/generated-paths.txt`
takes main's file and regenerates it with the gates' own `--write` (`scripts/regen-baselines.sh`: improvements only; a worsening stops, exit 12) -> **local Tier 1** on that exact combination -> fetch: main moved
= rebase and run again (3 tries) -> hold and red checked again -> `git push origin <sha>:refs/heads/main`, plain, never forced (a refused push re-enters the loop). Each commit lands as itself (linear);
files Tier 1 re-renders land as one extra `chore:` commit of the lander. Land-time checks: Conventional subject; over 150 production lines under `LeanJson/` needs a `Diff-Budget:` trailer.
Exit codes: 0 landed, 1 stopped, 2 bad input, 10 main red, 11 rebase conflict (aborted, files named), 12 baseline worse, 13 Tier 1 fails (nothing lands), 14 held, 15 busy. The last stdout line is JSON
`{sha, commits, tier1_seconds, specified_share, result, exit}`. The hold marker: `scripts/land-direct --hold "<reason>"` / `--release` (`<common>/vbm-json-land-hold`).

## Consequences
After a landing the worker's branch still holds its pre-rebase commits: start the next task from a fresh worktree off `origin/main`. No GitHub-side review exists; the gates, the hold marker and the red-check are the
whole review, and the protected set is reported (not blocked) at landing: the owner reads it on main. The pushing identity needs push rights to `main` (`docs/branch-protection.md`). Tier 2 stays on main after the push.
Not ported from the originating gates: per-commit task trailers, the gate-diff and F3 checks, the metrics log, the batch cycle, the Tier 2 freeze.

## Update: the lander is a pinned copy of vbm-land
`scripts/land-direct` is now a three-line stub that runs `scripts/land/bin/land-direct`, a pinned, vendored copy of vbm-land (`scripts/land/PIN` names the release and the commit; `scripts/land/MANIFEST.sha256` the hash of every file).
It is read-only by contract: `scripts/land/bin/land-check` (Tier 1, and the lander itself on every rebased tree) fails on any difference, a stray file included; to change the tool, change vbm-land and update the pin
(`scripts/land/bin/land-update <tag>`, one `chore(land)` commit). What is this repository's own: `scripts/land.conf` (base, the CI workflow and job, Tier 1, the regeneration command and generated list, the size budget) and
`scripts/land.d/` (the hooks: `prepare` copies the warm `.lake`; `post-rebase` runs the protected-set report and the gate-diff judge; `post-tier1` runs the relabel-attack suite when a gate-defining file is touched; `json-fields` adds
`specified_share`). The judges are taken from `origin/main`, not from the proposed tree. The behaviour above is unchanged except: the lock, hold marker, freeze marker and scratch worktree live in `<git common dir>/vbm-land/`
(the hold is still `scripts/land-direct --hold` / `--release`; a freeze with an owner and expiry is new: `--freeze`, `--thaw`), the commit-subject check also accepts git's own `Revert "..."`, the infrastructure classifier is the pinned
`scripts/land/lib/infra-re.sh`, the run is appended to a metrics log (`<common>/vbm-land/metrics.jsonl`), and the old environment overrides (`TIER1_CMD`, `REGEN_CMD`, ...) are gone: policy comes from `scripts/land.conf` on main only.
The old script is removed. `scripts/land.d/`, `scripts/land.conf` and `scripts/land/` are in the protected set and in the gate-defining set judged by the relabel-attack suite (`scripts/attacks/08d`, `08e`, `07k`, `07l`).
