import LeanJson.Compat.Value
import LeanJson.Compat.Classes
import LeanJson.Compat.Print
import LeanJson.Compat.Parse
/-! # `LeanJson.Compat`: a drop-in, Init-only replacement for the slice of the toolchain's `Lean.Json` that products use

Goal: the same names as `Lean.Json` / `Lean.JsonNumber` / `Lean.ToJson` / `Lean.FromJson`, with no import beyond `Init`, so that an executable that reads or writes JSON does not link the toolchain's
`Lean.Data.Json` (which drags in the toolchain's static library at 66.5 MB). A product opens `LeanJson.Compat` in place of `Lean`.

Delivered in slices; this file is **slice c of 4** (slice d is split in three: d1 below) (slice a: `Value` and `Classes`; slice b: `Print`; slice c: `Parse`):
- `Compat/Value.lean`: `Json`, `JsonNumber` (with `toString`, `Nat`/`Int`/decimal conversions), the constructors, `mkObj` and every accessor; objects keep keys sorted and unique (`SMap`, `SMap.WF`), with the accessor and builder laws proved.
- `Compat/Classes.lean`: `ToJson` / `FromJson` and the instances for `Json`, `JsonNumber`, `Unit`, `Bool`, `Nat`, `Int`, `String`, `Option`, `List`, `Array`, pairs; `getObjValAs?`.
- `Compat/Print.lean` (slice b): `Json.compress`, `Json.pretty`, `renderString`/`escape`, `ToString Json`/`ToFormat Json`; byte-equal to the toolchain on the 500+ value corpus of `LeanJsonProofs/CompatDiff.lean` (checked at build time, a differential run, not a theorem).

- `Compat/Parse.lean` (slice c): `Json.parse`, same accept/refuse decisions and values as the toolchain's (differences listed in its docstring: error text, fuel-bounded recursion); the parsing half of the differential suite is in `LeanJsonProofs/CompatDiff.lean` (250+ texts, checked at build time).

Slice d1 (landed with this text): the object-key theorems (keys sorted and unique by construction) and `compress` injective, prefix-free, on values without numbers and without string escapes (`LeanJsonProofs/CompatRound.lean`, class `Plain`), and the size executable `compat-size` (`tests/compat/CompatSize.lean`, 2.86 MB stripped, recorded in `docs/trust-ledger.md`).
Not yet, what d2 and d3 add: the parse round trip `parse (compress v) = .ok v` for admitted values, and `compress` injective beyond `Plain` (numbers, escapes).
Not provided at all: the `deriving ToJson, FromJson` handlers (they need the elaborator).

Differences from the toolchain so far: an object is `SMap` (a member list, keys strictly increasing, built only through provably well-formed operations) rather than `Std.TreeMap.Raw`; error texts of `Classes` that embed a printed value still stop before it (`expected JSON array`, not `..., got '{j}'`): printing exists now, the text is changed in a later slice. -/
