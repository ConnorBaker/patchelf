/-
  `patchelf` binary entry point.

  Argument parsing and dispatch live in `Patchelf.CLI`, which builds
  on the `Cli` library (lean4-cli).  Each operation is a subcommand;
  this module just hands argv to `cmdRoot.validate`.

  Exit codes:
    0 success
    1 bad arguments / usage
    2 parse error
    3 op precondition failed
    4 I/O error
    5 validate failed (output not loader-coherent; refused to write)
-/
module

public import Patchelf.CLI

@[expose] public section

open Patchelf.CLI

/-- Resolve `@file` argument values: any argument that begins with `@`
    is replaced by the contents of the file at that path (trimmed).
    Mirrors C++ patchelf's `resolveArgument`.  Applies to flag values
    and positional args alike. -/
def resolveArg (s : String) : IO String := do
  if s.startsWith "@" ∧ s.length > 1 then
    let path : String := s.drop 1 |>.toString
    try
      let body ← IO.FS.readFile (System.FilePath.mk path)
      return body.trimAscii.toString
    catch e =>
      throw <| IO.userError s!"reading @{path}: {e}"
  else
    return s

def main (args : List String) : IO UInt32 := do
  let resolved ← args.mapM resolveArg
  cmdRoot.validate resolved
