# 0003 Lint: no proof by evaluation over big data (`scripts/lint-proof-eval.sh`)

Status: accepted (the owner approved the class fix).

## Incident
The deep-nesting theorems (`LeanJsonProofs/Policy.lean`) were first proved by evaluation: `decide +kernel` over a 100000-long list. The kernel accepted it, but the exported proof term was so deep that the
independent checker (nanoda) overflowed its stack. The fix restated the proof for every depth through a shallow lemma (`parseVal_open_brackets`, an induction), so no big literal is ever evaluated.

## Decision
A cheap Tier 1 lint scans `LeanJsonProofs/**` and fails, with `file:line`, on: `decide +kernel`, `native_decide`, `decide := true`/`kernel := true` configs (always); and, in a declaration that uses `rfl`,
`decide` or `Nat.rec`, a numeric literal over `NUM_MAX` (256), a list literal over `LIST_MAX` (256) elements, or bracket nesting over `DEPTH_MAX` (64). The bounds live at the top of the script, nowhere else.
The escape hatch is `scripts/proof-eval-allow.txt`: file, text of the flagged line, expiry date, reason; honoured through the expiry date, failing after it. The lint is a heuristic (it reads text, not terms):
it catches the shape that bit us; the real checks remain Tier 2 (`leanchecker`, nanoda).

## Self-tests
`scripts/lint-proof-eval.sh --selftest` (run by Tier 1) builds fixtures: each banned pattern is flagged; a fixture just under each bound passes; comments are ignored; an allowlisted entry passes until its
expiry and fails after; a missing, mismatched or reason-less entry does not allow anything.

## Consequences
Both files and the Tier 1 wiring are in the protected set (a gate-defining change waits for the owner; `scripts/land-direct` reports it). Two entries were needed at introduction (a 600-element `rfl` in `Policy.lean`,
and a false positive on hex place values in `Print.lean`), both expiring 2027-01-31.
