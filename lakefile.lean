import Lake
open Lake DSL

package "ParserCombinators" where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require "leanprover-community" / "mathlib"

require aesop from git "https://github.com/leanprover-community/aesop"

@[default_target]
lean_lib «ParserCombinators» where
  -- add any library configuration options here

@[default_target]
lean_exe «Main» where
  root := "Main".toName

@[default_target]
lean_exe «benchmark» where
  root := "BenchmarkWorker".toName
  srcDir := "benchmarking/adapters/lean"
