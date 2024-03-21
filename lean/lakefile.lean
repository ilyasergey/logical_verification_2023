import Lake

open Lake DSL

package love

@[default_target]
lean_lib LoVe {
  roots := #[`LoVe]
  globs := #[Glob.submodules `LoVe]
}

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "master"
require loogle from git "https://github.com/nomeata/loogle.git"
require ssreflect from git "https://github.com/verse-lab/ssr-lean" @ "master"
