import Lake
open Lake DSL

package gdbh where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.29.1"

@[default_target]
lean_lib Gdbh where
