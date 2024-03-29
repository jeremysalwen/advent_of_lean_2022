import Lake
open Lake DSL


package «adventofcode» {
  -- add package configuration options here
}

lean_lib «adventofcode» {
  -- add library configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require aesop from git "https://github.com/JLimperg/aesop"

meta if get_config? env = some "dev" then -- dev is so not everyone has to build it
require «doc-gen4» from "../doc-gen4"