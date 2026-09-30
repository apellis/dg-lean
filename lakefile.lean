import Lake
open Lake DSL

package DG where
  moreLeanArgs := #["-DwarningAsError=true"]
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "v4.34.1"

@[default_target]
lean_lib DG where
  globs := #[.andSubmodules `DG]
