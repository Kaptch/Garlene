import Lake
open Lake DSL

package "synth-dom" where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`experimental.module, true⟩
  ]
require "leanprover-community" / "mathlib" @ git "v4.33.1"

@[default_target]
lean_lib «SynthDom» where
  roots := #[`SynthDom]

lean_lib «Examples» where
  roots := #[`SynthDom.Examples]
