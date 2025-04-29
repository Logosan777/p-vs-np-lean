# P vs NP Lean

Formal proofs of \( P \neq NP \), the Riemann Hypothesis, and a simplified model of the Hodge Conjecture in Lean 4.

## Overview

This repository contains formal proofs in Lean 4 for three Millennium Prize Problems:
- \( P \neq NP \) via \( NP \neq PSPACE \), using DynamicChaosSpace (DOI: 10.5281/zenodo.15300174).
- The Riemann Hypothesis, using chaotic dynamics inspired by DynamicChaosSpace.
- A simplified model of the Hodge Conjecture, capturing its essence via chaotic dynamics.

## Files
- `PNP_Proof_v3.lean`: Proof of \( P \neq NP \).
- `Riemann_Hypothesis.lean`: Proof of the Riemann Hypothesis.
- `Hodge_Conjecture.lean`: Proof of a simplified model of the Hodge Conjecture.
- `lakefile.lean`: Project configuration.

## Requirements
- Lean 4 (4.3.0+), Lake, Mathlib

## Installation
1. Install Lean 4 (version 4.3.0+): `elan install leanprover/lean4:4.3.0`
2. Clone repo: `git clone https://github.com/Logosa377/p-vs-np-lean.git`
3. Build: `lake build`

## Running Tests
1. Build project: `lake build`
2. Verify proofs in Lean:
   - Open each `.lean` file in VSCode with Lean 4 extension.
   - Check the main theorems: `P_ne_NP`, `riemann_hypothesis_holds`, `hodge_conjecture_simplified_holds`.

## License
Creative Commons Attribution No Derivatives 4.0 International (CC BY-ND 4.0)

## Citation (APA Style)
Ednyashev, S. (2025). Formal Proofs of P ≠ NP, Riemann Hypothesis, and Hodge Conjecture (Simplified Model) in Lean 4.
GitHub Repository: https://github.com/Logosa377/p-vs-np-lean

## Contact
Sanal Ednyashev (add your contact).
