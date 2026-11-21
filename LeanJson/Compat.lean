import LeanJson.Compat.Value
import LeanJson.Compat.Classes
/-! # `LeanJson.Compat`: a drop-in, Init-only replacement for the slice of the toolchain's `Lean.Json` that products use

Goal: the same names as `Lean.Json` / `Lean.JsonNumber` / `Lean.ToJson` / `Lean.FromJson`, with no import beyond `Init`, so that an executable that reads or writes JSON does not link the toolchain's
`Lean.Data.Json` (which drags in the toolchain's static library at 66.5 MB). A product opens `LeanJson.Compat` in place of `Lean`.

Delivered in four slices; this file is **slice a of 4**:
- `Compat/Value.lean`: `Json`, `JsonNumber` (with `toString`, `Nat`/`Int`/decimal conversions), the constructors, `mkObj` and every accessor; objects keep keys sorted and unique (`SMap`, `SMap.WF`), with the accessor and builder laws proved.
- `Compat/Classes.lean`: `ToJson` / `FromJson` and the instances for `Json`, `JsonNumber`, `Unit`, `Bool`, `Nat`, `Int`, `String`, `Option`, `List`, `Array`, pairs; `getObjValAs?`.

Not in this slice, and what the next slice (b) adds: `Compat/Print.lean` (`Json.compress`, `Json.pretty`, byte-identical to the toolchain, and `ToString`/`Repr` of `Json`); then `Compat/Parse.lean` (`Json.parse`, the differences listed here), the differential suite and round-trip proofs in `LeanJsonProofs`, and the size executable.
Not provided at all: the `deriving ToJson, FromJson` handlers (they need the elaborator).

Differences from the toolchain so far: an object is `SMap` (a member list, keys strictly increasing, built only through provably well-formed operations) rather than `Std.TreeMap.Raw`; error texts that embed a printed value stop before it (until printing lands). -/
