import Lake
open Lake DSL

/-! Lean core of the one-dimensional sparsity estimates (Lean 4.35.0, Mathlib 56a0058). -/
package Flagship1D where
  moreLeanArgs := #["-j1", "-M6144"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "56a005855ea17e0b0958f73ec801ae140b0a1679"

@[default_target]
lean_lib Flagship1D where
  globs := #[`Flagship1D.+]
