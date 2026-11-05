import Lake
open System Lake DSL

package «vbm-json» where
  leanOptions := #[⟨`warningAsError, true⟩, ⟨`autoImplicit, false⟩]

/-- The reusable verified bit-parallel kernels (the model of the vector operations, the proved kernels, the trusted shim header): a pinned dependency. -/
require «vbm-simd» from git "https://github.com/witt3rd/vbm-simd" @ "433268697353f3b5f0ad1197b2ab2475d270dae9"

/-- The library: specification and code, one Lean core. Imports `Init` only (checked by Tier 1): this is what is compiled to C, to WASM and into
every consumer, so nothing from `Std` or `Lean` may be in its closure (a `Lean.*` import forces full runtime initialisation). -/
@[default_target]
lean_lib LeanJson where
  -- every module under LeanJson/ is built, imported by the umbrella or not: a module cannot hide from the build
  globs := #[.andSubmodules `LeanJson]

/-- The bit-parallel structural stage and the index-driven parser (docs/perf/simd-plan.md): `LeanJson` plus the pinned dependency `VbmSimd` (checked by scripts/test_simd_imports.sh). Compiled with the dependency's trusted shim
header (static inline loads, stores and ctz) first in every generated C file. Not part of any export yet. -/
lean_lib LeanJsonSimd where
  globs := #[.andSubmodules `LeanJsonSimd]
  moreLeancArgs := #["-include", (__dir__ / ".lake" / "packages" / "vbm-simd" / "include" / "vbm_simd.h").toString]

/-- The proofs: may import `Std` and `Lean`; NEVER linked (nothing in `LeanJson` may import it, and no executable or export depends on it). -/
lean_lib LeanJsonProofs where
  globs := #[.andSubmodules `LeanJsonProofs]

/-- The vector generator (`vbm-json-vectors-1`): rows come from the Lean REFERENCE and printer only (`LeanJson.Vectors`); this executable only writes them. Not part of any export. -/
lean_exe «vbm-json-vectors» where
  srcDir := "vectors"
  root := `Main
