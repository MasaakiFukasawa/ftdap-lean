import Lake
open Lake DSL

package ftdap where
  version := v!"0.1.0"
  leanOptions := #[⟨`warningAsError, true⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "5ed2965256430c3649e86755f9576b54eca72435"

@[default_target]
lean_lib FTDAP where
  srcDir := "src"
  roots := ((include_str "module-roots.txt").trimAscii.toString.splitOn "\n").toArray.map
    Lean.Name.mkSimple
