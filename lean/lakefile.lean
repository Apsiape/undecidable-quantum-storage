import Lake
open Lake DSL

package QuantumStorage where
  moreLeanArgs := #["-j1", "-M5000"]

require mathlib from git "https://github.com/leanprover-community/mathlib4" @
  "56a005855ea17e0b0958f73ec801ae140b0a1679"

@[default_target]
lean_lib QuantumStorage where
  globs := #[`QuantumStorage, `QuantumStorage.+]

lean_lib Challenge where
  roots := #[`Challenge]

lean_lib Solution where
  roots := #[`Solution]
