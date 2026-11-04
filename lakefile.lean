import Lake

open System Lake DSL

package Singmaster

require "leanprover-community" / mathlib @ git "v4.35.0"

@[default_target] lean_lib Singmaster where roots := #[`Singmaster]

/-- The challenge for `lake comparator` (see `comparator.json`). It is not a default target. -/
lean_lib Challenge

/-- `lake run`: build the development, then print the main theorem `statement_of_mrstt` and the
axioms its proof depends on. -/
@[default_script]
script axioms do
  let lake ← getLake
  let build ← (← IO.Process.spawn { cmd := lake.toString, args := #["build", "-q", "--log-level=error"] }).wait
  if build != 0 then
    return build
  (← IO.Process.spawn { cmd := lake.toString, args := #["env", "lean", "PrintAxioms.lean"] }).wait
