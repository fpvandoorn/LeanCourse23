import Lake
open Lake DSL

package «leanCourse» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"2b8dea43f8493550f0b20b7a4ec73287de62ba51"

@[default_target]
lean_lib «LeanCourse» {
  -- add any library configuration options here
}
