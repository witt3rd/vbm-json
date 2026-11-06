# AGENTS.md: vbm-json

The first of the verified libraries split out of a larger Lean project: a **verified JSON codec written once in Lean** (RFC 8259) from which the C, WASM, Rust, TypeScript, C# and Python artifacts are
generated. Agent-built, no human code review. Public. Design and the pinned policies: `docs/decisions/0001-vbm-json.md` (read first). Direction:
verified by construction is priority 1; efficiency is priority 2. The standard is VBM (verified bare metal), the libraries are `vbm-<name>`; packages: crate `vbm-json`, npm `@witt3rd/vbm-json`, NuGet `Witt3rd.VbmJson`, PyPI `vbm-json` (names only, nothing published). The Lean namespace `LeanJson` and the `LeanJson*` file names stay (the implementation language); the ABI prefix is `vbm_json_`. `README.md` is the public face (written for humans, kept short); `CONTRIBUTING.md` explains the landing process to outsiders.

## Status
Scaffold (PR 0) plus the spec layer in three parts: PR 1a `Value`, the RFC 8259 grammar relation, the policies; PR 1b the reference parser and its theorems against the grammar; PR 1c the printer and the vector generator `lake exe vbm-json-vectors` (which of these have landed: `git log`). PR 2 adds the fast parser (`LeanJson/Parse.lean`, the closure gate's one entry point `LeanJson.parseFast`) and its refinement proof (`LeanJsonProofs/Fast.lean`: `parseFast_eq_parse`); the ledger's `proved` claims are about it. PR 0b (the CI workflow `.github/workflows/core.yml`) is the owner's merge; branch protection is recommended in `docs/branch-protection.md`. Toolchain: Lean 4.35.0, pinned in `mise.toml` and `lean-toolchain`
(no elan). Run everything as `mise exec -- ...`; the gate is `mise exec -- scripts/tier1.sh`.

## Hard rules
- **Forbidden anywhere in Lean:** `sorry`, `admit`, `axiom`, `unsafe`, `implemented_by`, `csimp` (Tier 1 scans for them; a comment may mention one only on a line marked `tier1-allow`). A proof is hard? Decompose it; never weaken the statement.
- **Spec first.** Behaviour lands as a specification and its proofs before any optimised code; the fast parser exists only with its refinement proof to the reference. Vectors come from the reference, never from the fast code.
- **No `sorry`, no exceptions, no unproved claim called verified.** Only `proved` in the obligation ledger (`LeanJsonProofs/Ledger.lean`, rendered to `docs/proof-ledger.md`) may be called verified.
- **The specified share is reported on every Tier 1 run** (`scripts/ClosureGate.lean`); the aim is that it only rises and the unverified set only shrinks, and nothing from `Std`, `Lean` or `LeanJsonProofs` is reachable from an export.
- **The boundary never decides.** C, loaders and bindings move bytes and read the tape; what is valid and what a value is, is decided in Lean only. A second decoder in a binding is counted as boundary and tested, never trusted.
- **Worktrees only, through `scripts/wt`** (`scripts/wt switch -c agent/<task>`); the primary clone stays on `main` and is never edited.
- **Land with `scripts/land-direct`, never open a PR** (the owner's decision; `docs/decisions/0002-land-direct.md`): commit locally in your worktree, run it; one lander at a time (flock), red-check, rebase onto `origin/main`, local Tier 1, fast-forward push. Never push to `main` yourself, never force-push it. (Outside contributors open PRs; a maintainer lands them: `CONTRIBUTING.md`.)
- **TTL 45 minutes without a passing build:** abort and decompose. **Small diffs.** Conventional Commits `type(scope): summary`.
- **No secrets in the repository.** No paid model calls from a test or a gate.
- **Anything in the repository may be edited and landed like any change** (spec, proofs, code, scripts, docs, this file); only the lander files and the signing keys are off limits. Do not weaken a check to make it pass.

## Library rules
- **Policy (PROPOSED, pending the owner):** strict text (no lone surrogates, no invalid UTF-8); numbers are lexemes (sign, digits, exponent; no floats in the core); duplicate keys kept in input order; a named `maxDepth` reported as an error code; `print` reproduces `Lean.Json.compress` bytes. Do not "fix" a policy in code: a policy change is a spec change.
- **Module roots:** `LeanJson` imports `Init` and other `LeanJson` modules only (Tier 1 scans the imports); `LeanJsonProofs` may import `Std` and `Lean` and is never linked, and nothing in `LeanJson` may import it. The closure of an export stays inside `LeanJson` plus `Init`.
- **ABI:** exports are `vbm_json_*`, bytes in and bytes out, caller-owned buffers with a "needed size" return, no allocator across the ABI, a flat tape of little-endian u64 words (two per node: kind and length, then offset or subtree size; `LeanJson/Tape.lean`, `include/vbm_json.h`). The ABI is described in `abi/vbm_json.abi.json` (checked against `include/vbm_json.h` by `scripts/check_abi.py`; the decision record planned it as Lean-written, which is not done); bindings are generated from it plus at most 100 hand-written lines each. An ABI change is an expand-and-contract change, reviewed by the owner.
- **Vectors:** `vbm-json-vectors-1`, generated by the Lean reference, run in every binding in CI; JSONTestSuite is vendored (MIT, with attribution). A vector set that must fail in a binding that skips UTF-8 checks is part of the suite.
- **The trust ledger** (`docs/trust-ledger.md`) lists everything outside our control; a new boundary (extern, C file, loader, workflow, tool) with no entry fails Tier 1. Entries for pieces not in the tree yet are written under "Planned" and promoted in the PR that adds the file.

## Gates (Tier 1 before landing; Tier 2 after merge)
- **Tier 1** (`scripts/tier1.sh`, about 45 s): the forbidden-constructs scan, the Init-only import scan, a zero-warning build of both libraries, the axiom gate (`scripts/AxiomGate.lean`), the trust ledger (`scripts/trust-ledger-check.sh`; a new boundary needs an entry), the shared vectors, and the real tests (ABI, WebAssembly, native, bindings). The specified share and closure counts are printed, never gated. Nothing else refuses a landing.
- **Tier 2** (`scripts/tier2.sh`, CI on main after merge): Tier 1 again, `leanchecker --fresh` on both libraries, nanoda over the exported proof. A failure on main means revert, then fix in a worktree.

## Layout
`LeanJson/` spec and code (Init only) · `LeanJsonProofs/` proofs (never linked) · `abi/` the ABI description and the C shim · `runtime/` the one freestanding runtime of the wasm32 and native builds (`runtime/rt.c`), trusted C · `bindings/` generated types and tape readers and thin loaders (Python, Rust; from `abi/vbm_json.abi.json`) · `vectors/`, `corpus/` (to come) · `scripts/` gates and process · `docs/` decisions, trust ledger, proof ledger (generated).
