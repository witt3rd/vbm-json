import LeanJson.Compat
/-! The size probe of `LeanJson.Compat`: an executable that imports ONLY `LeanJson.Compat` (so, beside this library, `Init`) and prints one small value through the drop-in `Json` API. Its stripped size is
recorded in `docs/trust-ledger.md`; the same program over the toolchain's `Lean.Data.Json` links about 66 MB more. Not part of any export; not linked into the library. -/
open LeanJson.Compat

def main : IO Unit := do
  let j := Json.mkObj [("b", Json.arr #[Json.null, Json.bool true, (7 : Nat)]), ("a", Json.str "x")]
  IO.println j.compress
  match Json.parse j.compress with
  | .ok v => IO.println v.compress
  | .error e => IO.println e
