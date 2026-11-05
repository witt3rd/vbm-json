# Branch protection (recommendation, text only: the owner applies it)

Nothing here is applied by the repository. GitHub settings are the owner's (`@witt3rd`); `scripts/land-direct` and `scripts/githooks/pre-commit` are the local half
(the commit-on-main refusal, the protected-set report). Branch protection makes the same rules the server's, so an agent that skips the script is still stopped.

## Prerequisites (check first)

- **Actions are enabled** for the repository (Settings, Actions, General); hosted runners are free for a public repository. Tier 1 is
  about 20 s of checks on the skeleton plus a cold Lean install and build; budget a few minutes a run, `timeout-minutes` caps it at 15 (Tier 1) and 30 (Tier 2).
- The workflow (`.github/workflows/core.yml`) has run at least once on a PR: a required status check cannot be chosen until GitHub has seen its name.
- `scripts/land-direct` pushes to `main` itself (no PRs): if protection is applied, the pushing identity must be allowed to push to `main`, with force-push and deletion refused.

## Rule for `main` (a branch ruleset or a classic rule; the settings are the same)

1. **Require a pull request before merging.** No direct pushes to `main`, none by admins either (do not bypass).
2. **Require status checks to pass:** the check named **`tier1`** (the job id in `core.yml`; the check run is shown as `tier1`, or `core / tier1` in some views).
   **Require branches to be up to date** before merging (the lander rebases anyway). Do **not** require `tier2`: it runs only on push to `main`, after the merge
   (a required check that never runs on a PR blocks every PR); its failure on main means revert, then fix in a worktree.
3. **Require review from Code Owners.** `CODEOWNERS` already names `@witt3rd` for the specification (`LeanJson/`, `LeanJson.lean`, the ledger `LeanJsonProofs/Ledger.lean`),
   the ABI and trusted C (`abi/`, `runtime/`), the decisions and trust ledger, the pins (`lean-toolchain`, `mise.toml`, `lakefile.lean`), `AGENTS.md`, `CODEOWNERS`,
   `.github/workflows/`, `.config/` and all of `scripts/` (the gates, their baselines and the process scripts). With the rule on, a PR touching any of them cannot
   merge without the owner's approval; this is the server-side form of `scripts/protected-paths.txt`. One approval is enough; stale approvals dismissed on new commits.
4. **Block force pushes** and **deletion** of `main`. Require linear history (squash merges give it).
5. Keep **`LeanJsonProofs/` (except the ledger)** outside Code Owners, as now: proofs do not wait for the owner, because a proof cannot change what the specification says.

## Caveats

- Code-owner review applies to the **approver's** account: the owner cannot approve a PR they authored, so for an owner-authored change to a protected path either
  allow the owner to bypass for that one PR or have a second account (a bot or collaborator listed in CODEOWNERS) approve.
- An agent's token must not be an admin of the repository (and admins must not bypass), or the rules above are advisory to it.
- `CODEOWNERS` and `scripts/protected-paths.txt` are two lists of the same set; keep them equal.
- A PR that changes `core.yml` runs the new workflow file from the PR branch: review it as code that runs with the repository's token (read-only `contents` here).

## Settings for a public repository (the owner's clicks; none is applied by the repository)

- **Settings, Actions, General, "Fork pull request workflows":** require approval for all outside collaborators. (The workflow has no pull-request trigger at all, so fork code never runs in it; the setting is the second lock.)
- **Workflow permissions:** read-only by default, and "Allow GitHub Actions to create and approve pull requests" off.
- **Runners:** the workflow uses GitHub-hosted runners only (`scripts/lint-workflows.py` fails Tier 1 on a self-hosted label). Unregister any self-hosted runner still attached to the repository (Settings, Actions, Runners) and delete its labels.
- **Branch protection or a ruleset for `main`** as described above, with force-push and deletion refused. `scripts/land-direct` pushes to `main` itself, so the pushing maintainer identity must be allowed to; outside contributors' pull requests are landed by a maintainer (`CONTRIBUTING.md`).
- **Private vulnerability reporting:** enable it (Settings, Code security), since `SECURITY.md` points to it.
- **Old Actions runs and caches:** a repository that was private before may carry run logs and caches that name internal machines: delete them (Actions, each run, "Delete workflow run"; Actions, Caches) before the visibility change.
- **Wiki and unused features:** disable what is not used.
