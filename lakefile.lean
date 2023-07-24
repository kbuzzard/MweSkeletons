import Lake
open Lake DSL

package «mweSkeletons» {
  -- add any package configuration options here
}

def weakLeanArgs :=
  if get_config? CI |>.isSome then
    #["-DwarningAsError=true"]
  else
    #[]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «MweSkeletons» {
  -- add any library configuration options here
}
