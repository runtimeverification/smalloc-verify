import Lake
open Lake DSL

package SmallocArith where
  version := v!"0.1.0"
  leanOptions := #[⟨`autoImplicit, false⟩]

require aeneas from git
  "https://github.com/AeneasVerif/aeneas" @ "main" / "backends/lean"

-- Aeneas-extracted Rust code
lean_lib SmallocArith

-- Specifications and proofs
@[default_target]
lean_lib SmallocArithVerif
