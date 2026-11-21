import LeanJson.Compat.Value
import LeanJson.Compat.Classes
import LeanJson.Compat.Print
/-! # `LeanJson.Compat`: a drop-in, Init-only replacement for the slice of the toolchain's `Lean.Json` that products use

Goal: the same names as `Lean.Json` / `Lean.JsonNumber` / `Lean.ToJson` / `Lean.FromJson`, with no import beyond `Init`, so that an executable that reads or writes JSON does not link the toolchain's
`Lean.Data.Json` (which drags in the toolchain's static library at 66.5 MB). A product opens `LeanJson.Compat` in place of `Lean`.

Delivered in four slices; this file is **slice b of 4** (slice a: `Value` and `Classes`; slice b: `Print`):
- `Compat/Value.lean`: `Json`, `JsonNumber` (with `toString`, `Nat`/`Int`/decimal conversions), the constructors, `mkObj` and every accessor; objects keep keys sorted and unique (`SMap`, `SMap.WF`), with the accessor and builder laws proved.
- `Compat/Classes.lean`: `ToJson` / `FromJson` and the instances for `Json`, `JsonNumber`, `Unit`, `Bool`, `Nat`, `Int`, `String`, `Option`, `List`, `Array`, pairs; `getObjValAs?`.
- `Compat/Print.lean` (slice b): `Json.compress`, `Json.pretty`, `renderString`/`escape`, `ToString Json`/`ToFormat Json`; byte-equal to the toolchain on the 500+ value corpus of `LeanJsonProofs/CompatDiff.lean` (checked at build time, a differential run, not a theorem).

Not yet, and what the next slice (c) adds: `Compat/Parse.lean` (`Json.parse`, with its differences from the toolchain listed here), the parsing half of the differential suite and the round-trip proofs in `LeanJsonProofs`; then (d) the size executable and ledger entry.
Not provided at all: the `deriving ToJson, FromJson` handlers (they need the elaborator).

Differences from the toolchain so far: an object is `SMap` (a member list, keys strictly increasing, built only through provably well-formed operations) rather than `Std.TreeMap.Raw`; error texts of `Classes` that embed a printed value still stop before it (`expected JSON array`, not `..., got '{j}'`): printing exists now, the text is changed in a later slice. -/
