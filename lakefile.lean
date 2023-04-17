import Lake
open Lake DSL

package «toyprog» {
  -- add package configuration options here
}

lean_lib «Toyprog» {
  -- add library configuration options here
}

@[default_target]
lean_exe «toyprog» {
  root := `Main
}
