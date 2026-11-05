import Lake
open System Lake DSL

package «vbm-json» where
  leanOptions := #[⟨`warningAsError, true⟩, ⟨`autoImplicit, false⟩]

/-- The library: specification and code, one Lean core. Imports `Init` only (checked by Tier 1): this is what is compiled to C, to WASM and into
every consumer, so nothing from `Std` or `Lean` may be in its closure (a `Lean.*` import forces full runtime initialisation). -/
@[default_target]
lean_lib LeanJson where
  -- every module under LeanJson/ is built, imported by the umbrella or not: a module cannot hide from the build
  globs := #[.andSubmodules `LeanJson]

/-- The proofs: may import `Std` and `Lean`; NEVER linked (nothing in `LeanJson` may import it, and no executable or export depends on it). -/
lean_lib LeanJsonProofs where
  globs := #[.andSubmodules `LeanJsonProofs]

/-- The vector generator (`vbm-json-vectors-1`): rows come from the Lean REFERENCE and printer only (`LeanJson.Vectors`); this executable only writes them. Not part of any export. -/
lean_exe «vbm-json-vectors» where
  srcDir := "vectors"
  root := `Main
