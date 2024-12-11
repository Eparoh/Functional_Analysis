import Lake
open Lake DSL

package «Functional_Analysis» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «Functional_Analysis» where
  -- add any library configuration options here

  @[default_target]
lean_lib «Topology» where
  -- add any library configuration options here

  @[default_target]
lean_lib «FunctionalAnalysis» where
  -- add any library configuration options here

  @[default_target]
lean_lib «CajonSastre» where
  -- add any library configuration options here
