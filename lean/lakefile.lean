import Lake

open Lake DSL

package love

@[default_target]
lean_lib LoVe {
  roots := #[`LoVe]
  globs := #[Glob.submodules `LoVe]
}

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.4.0"
require loogle from git "https://github.com/nomeata/loogle.git"
require Ssreflect from git "https://github.com/verse-lab/ssr-lean" @"v1.0"
