---
name: update-vbm-land
description: >-
  Update the pinned, vendored copy of vbm-land in a repository (land-update), run the drift audit, and understand the manifest. Use when land-check reports drift or an advice about a newer release, or when asked to bump vbm-land.
---

# update-vbm-land

A repository vendors a pinned copy: `scripts/land/` (tool), `scripts/land/PIN` (source, version, 40-hex commit, manifest hash), the `scripts/land-direct` entry script (yours after the first install), and the vbm-land skills in `.agents/skills/`. `MANIFEST.sha256` lists the hash of every file; all of them are drift-checked.

## Check

```
scripts/land/bin/land-check              # offline: copy still equals its pin (exit 0 ok, 1 drift, 2 not installed)
scripts/land/bin/land-check --upstream   # also asks the source about the pinned commit; says if a newer release exists (exit 3: source unreachable)
```
From a vbm-land checkout, the rollout table across repositories: `bin/land-audit DIR...`.

## Update

1. Fresh worktree off `origin/main`.
2. `timeout 120 scripts/land/bin/land-update vX.Y.Z` (a tag or commit). It replaces `scripts/land/`, the skills and the PIN (never `scripts/land-direct` or `scripts/land.conf`), verifies each file against the manifest at that commit, and commits nothing.
3. `scripts/land/bin/land-check` then review `git status` and `CHANGELOG.md` of the release (new keys, exit codes).
4. One commit: `git add -A && git commit -m 'chore(land): vbm-land vX.Y.Z'`; land it with `scripts/land-direct` (the lander that lands it is the one already on main).

## Drift

`DRIFT:` lines name the file. Fix by **restoring**, not editing: `scripts/land/bin/land-update <pinned version>` (the version is in `scripts/land/PIN`). A local need becomes a config key or a hook in your own `scripts/land.d/`, or a change upstream.

## Do NOT

- Do not edit `scripts/land/`, `MANIFEST.sha256`, `PIN` or the vendored skills by hand, and never "fix" drift by regenerating the manifest in a consumer.
- Do not update to an untagged commit unless asked.
- Do not mix the update with other changes in one commit.
