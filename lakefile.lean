import Lake
open Lake DSL

package "firstproject" where
  -- add package configuration options here

lean_lib «Firstproject» where
  -- add library configuration options here

@[default_target]
lean_exe "firstproject" where
  root := `Main
