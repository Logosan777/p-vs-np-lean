--gy
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.3.0"
open Lake DSL
package pnp_lean { description := "Test build with PNP_Proof_v3" }
@[default_target] lean_lib PNPLean { srcDir := "." roots := #[``PNP_Proof_v3] }
