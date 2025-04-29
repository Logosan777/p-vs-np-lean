require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.3.0"

open Lake DSL

package pnp_lean {
  description := "Formal proofs of P ≠ NP, Riemann Hypothesis, and Hodge Conjecture (simplified model) in Lean 4"
}

@[default_target]
lean_lib PNPLean where
  srcDir := "."
  roots := #[``PNP_Proof_v3, ``Riemann_Hypothesis, ``Hodge_Conjecture]
