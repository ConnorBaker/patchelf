/-
  Patchelf.Log: a one-flag stderr logger.

  When `--debug` is passed, handlers can call `Log.debug "..."` to
  emit a leading-arrow trace line on stderr.  When the flag is off,
  the calls are pure no-ops at IO level (the message string is still
  formatted; if formatting becomes a hot path, callers can guard via
  `Log.isEnabled` themselves).

  Implementation note: state lives in an `IO.Ref` initialized at
  process start.  This avoids threading a logger handle through every
  pure-ish helper that already lives in `Except CliError _`.
-/
module

@[expose] public section

namespace Patchelf.Log

/-- Stderr-tracing flag.  Initialized at process start; set once by
    the main CLI handler when `--debug` is passed.  Never reset. -/
initialize debugRef : IO.Ref Bool ← IO.mkRef false

/-- Enable or disable debug tracing.  Idempotent. -/
def setEnabled (b : Bool) : IO Unit :=
  debugRef.set b

/-- Read the current tracing flag. -/
def isEnabled : IO Bool :=
  debugRef.get

/-- Emit a single trace line on stderr if `--debug` is enabled.
    Lines are prefixed with `  -> ` to distinguish from program output
    on stdout and from `error:` / `validate:` lines on stderr. -/
def debug (msg : String) : IO Unit := do
  if (← isEnabled) then
    IO.eprintln s!"  -> {msg}"

end Patchelf.Log
