import Lake
open Lake DSL

package «leanCourse» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"v4.2.0"

@[default_target]
lean_lib «LeanCourse» {
  -- add any library configuration options here
}
