/-
  CLI front end built on the `Cli` library (lean4-cli).

  Each patchelf operation is a subcommand:

    patchelf print-rpath <file>
    patchelf set-rpath [--force-rpath] <path> <file>
    patchelf add-needed <lib> <file>
    ...

  This is a deliberate divergence from the C++ tool's "stack of flags
  in argv order" CLI.  Subcommands eliminate the argv-order pitfalls
  (set-rpath-then-print-rpath ambiguity, repeated `--add-needed`
  flags overriding each other, `--allowed-rpath-prefixes` only
  applying to the preceding `--shrink-rpath`) and make `--help`
  per-op meaningful.  Multiple operations are achieved by chaining
  invocations:

    patchelf set-rpath /a foo &&
    patchelf add-needed libbar.so foo

  Implementation:
    * Each `Cmd` is built with the `[Cli|...]` macro DSL.
    * Mutating subcommands get `--output / --no-validate /
      --page-size / --debug` via the `mutatingFlagsExt` extension.
      Read-only subcommands (`print-*`, `validate`, `parse`)
      reject those flags as unknown — surfacing user mistakes.
    * Each handler decodes the file, runs the typed-algebra op,
      and routes through `runWith` → `runResultToIO`, which
      validates (unless `--no-validate`) and writes the result.
    * `Run` holds read-only accessors on `ElfFile`.
-/
module

public import Patchelf.Log
public import Patchelf.Elf.Parser
public import Patchelf.Elf.Encoder
public import Patchelf.Elf.Validate
public import Patchelf.Elf.Adapter
public import Patchelf.Elf.Ops.OsAbi
public import Patchelf.Elf.Ops.Execstack
public import Patchelf.Elf.Ops.AddDebugTag
public import Patchelf.Elf.Ops.NoDefaultLib
public import Patchelf.Elf.Ops.AddNeeded
public import Patchelf.Elf.Ops.Rpath
public import Patchelf.Elf.Ops.Soname
public import Patchelf.Elf.Ops.RemoveRPath
public import Patchelf.Elf.Ops.RemoveNeeded
public import Patchelf.Elf.Ops.Interpreter
public import Patchelf.Elf.Ops.ReplaceNeeded
public import Patchelf.Elf.Ops.ClearSymbolVersion
public import Patchelf.Elf.Ops.RenameDynamicSymbols
public import Patchelf.Elf.GnuHashRebuild
public import Patchelf.Elf.RelocRemap
public import Cli.Basic
public import Cli.Extensions

@[expose] public section

namespace Patchelf.CLI

open Cli
open Patchelf.Elf (OsAbi DynEntry DynTag StringTable)
open Patchelf.Elf (ElfFile ParsedElf parse encode)
open Patchelf.Elf (ValidateFailure validateBytes)
open Patchelf.Elf.Layout (PhType)
-- Cli.ParseError clashes with Patchelf.Elf.ParseError; keep the latter
-- fully qualified.

/-! ## Shared types -/

/-- Options bundle consumed by per-subcommand handlers.  Each field
    corresponds to a flag; flags appear only on subcommands that
    consume the corresponding field (see `mutatingFlags` and
    `mutatingFlagsExt` below). -/
structure Options where
  /-- `--output PATH`: write target override.  `none` = in-place. -/
  outputPath : Option System.FilePath := none
  /-- `--no-validate` flips this to `false`; default skips the
      loader-coherence check before write (UNSAFE). -/
  validate   : Bool := true
  /-- `--force-rpath`: emit DT_RPATH instead of DT_RUNPATH. -/
  forceRpath : Bool := false
  /-- `--page-size N`: override the layout engine's PT_LOAD alignment.
      `none` falls back to auto-detection from existing PT_LOAD
      `p_align` values. -/
  pageSize   : Option Nat := none
  /-- `--debug`: enable stderr tracing via `Patchelf.Log`. -/
  debug      : Bool := false
  deriving Repr

/-- CLI error classes; `exitCode` matches the previous shell tests. -/
inductive CliError
  | badArgs (message : String)
  | parseFailed (err : Patchelf.Elf.ParseError)
  | opPreconditionFailed (message : String)
  | ioError (message : String)
  | validateFailed (msg : String)
  deriving Repr

def CliError.exitCode : CliError → UInt32
  | .badArgs _              => 1
  | .parseFailed _          => 2
  | .opPreconditionFailed _ => 3
  | .ioError _              => 4
  | .validateFailed _       => 5

def CliError.message : CliError → String
  | .badArgs m              => s!"bad arguments: {m}"
  | .parseFailed e          => s!"parse failed: {repr e}"
  | .opPreconditionFailed m => s!"op precondition failed: {m}"
  | .ioError m              => s!"I/O error: {m}"
  | .validateFailed m       => s!"validate: {m}"

/-- Result of a subcommand: bytes to write back, text to print, or
    nothing (some print ops emit nothing when the queried tag is
    absent — match C++ patchelf print-soname). -/
inductive RunResult
  | bytes (bs : ByteArray)
  | print (s : String)
  | silent

/-! ## Read-only ElfFile accessors -/

namespace Run

def resolveDynstrName (e : ElfFile) (off : UInt64) : Option String :=
  match e.dynstr with
  | some ds => ds.lookup off.toNat |>.bind String.fromUTF8?
  | none => none

def neededLibs (e : ElfFile) : List String :=
  e.dynamic.map (·.toList.filterMap fun d =>
    if d.tag = DynTag.needed then resolveDynstrName e d.value else none)
    |>.getD []

def findDynstrByTag (e : ElfFile) (tag : DynTag) : Option String :=
  e.dynamic.bind (fun dyn =>
    dyn.toList.find? (fun d => d.tag = tag)
      |>.bind (fun d => resolveDynstrName e d.value))

def rpathValue (e : ElfFile) : Option String :=
  findDynstrByTag e DynTag.runpath |>.orElse fun _ => findDynstrByTag e DynTag.rpath

def sonameValue (e : ElfFile) : Option String :=
  findDynstrByTag e DynTag.soname

def execstackState (e : ElfFile) : Option Bool :=
  e.phdrs.foldl (init := none) fun acc ph =>
    match acc with
    | some _ => acc
    | none   =>
      if ph.type = PhType.PT_GNU_STACK then
        some ((ph.flags &&& Patchelf.Elf.ExecstackFlags.PF_X) =
              Patchelf.Elf.ExecstackFlags.PF_X)
      else none

def readInterpPath (ib : ByteArray) : Option ByteArray :=
  StringTable.findNullFrom ib 0 0

def badPrecondition (opName detail : String) : CliError :=
  .opPreconditionFailed s!"{opName}: bad precondition ({detail})"

end Run

/-! ## Op dispatch helpers (shared across subcommands) -/

/-- Wrap a typed-op that requires `e.dynamic.isSome`.  Routes
    bytes → typed → op → bytes → `encodeWith opts.pageSize`.

    `opts.pageSize` (from `--page-size`) is forwarded to the layout
    engine; `none` lets it auto-detect from the binary. -/
def runDynOp (opts : Options) (opName : String) (e : Patchelf.Elf.ElfFile)
    (f : (v : Patchelf.Elf.ValidElfFile) → v.dynamic.isSome → Patchelf.Elf.ValidElfFile) :
    Except CliError RunResult :=
  match Patchelf.Elf.Adapter.ofElfFile e with
  | .error err =>
      throw (Run.badPrecondition opName s!"adapter failed: {repr err}")
  | .ok v =>
      match h : v.dynamic with
      | none => throw (Run.badPrecondition opName "no dynamic section")
      | some _ =>
          let hSome : v.dynamic.isSome := by rw [h]; rfl
          let v' := f v hSome
          let e' := Patchelf.Elf.Adapter.toElfFile e v'
          .ok (.bytes (Patchelf.Elf.encodeWith opts.pageSize e'))

/-- No-precondition wrapper.  See `runDynOp` for the page-size note. -/
def runOpNoPre (opts : Options) (e : Patchelf.Elf.ElfFile)
    (f : Patchelf.Elf.ValidElfFile → Patchelf.Elf.ValidElfFile) :
    Except CliError RunResult :=
  match Patchelf.Elf.Adapter.ofElfFile e with
  | .error err =>
      throw (Run.badPrecondition "op" s!"adapter failed: {repr err}")
  | .ok tv =>
      let tv' := f tv
      let e' := Patchelf.Elf.Adapter.toElfFile e tv'
      .ok (.bytes (Patchelf.Elf.encodeWith opts.pageSize e'))

/-! ## Cli plumbing: extract Options + file from a Parsed -/

/-- Read the per-subcommand flags from a `Cli.Parsed` and bundle as
    `Options`.  Each flag is read with `hasFlag`, which returns
    `false` if the flag wasn't declared on this subcommand — so
    handlers for read-only subcommands that don't declare
    `--output`/`--no-validate` simply see the defaults.

    `--page-size 0` is rejected: page sizes must be positive. -/
def optionsOf (p : Parsed) : Except CliError Options := do
  let mut opts : Options := {}
  if p.hasFlag "output" then
    opts := { opts with outputPath := some (p.flag! "output" |>.as! String) }
  if p.hasFlag "no-validate" then
    opts := { opts with validate := false }
  if p.hasFlag "force-rpath" then
    opts := { opts with forceRpath := true }
  if p.hasFlag "page-size" then
    let n : Nat := p.flag! "page-size" |>.as! Nat
    if n = 0 then throw (.badArgs "--page-size requires a positive integer")
    opts := { opts with pageSize := some n }
  if p.hasFlag "debug" then
    opts := { opts with debug := true }
  return opts

/-- Read the positional `file` argument. -/
def fileOf (p : Parsed) : System.FilePath :=
  System.FilePath.mk (p.positionalArg! "file" |>.as! String)

/-! ## OS-ABI parsing -/

def parseOsAbi (s : String) : Except CliError OsAbi :=
  match s with
  | "System V" | "SysV" | "sysv" => .ok .systemV
  | "Linux"    | "linux"          => .ok .linux
  | "FreeBSD"  | "freebsd"        => .ok .freebsd
  | _ =>
    match s.toNat? with
    | some n => if n < 256 then .ok (OsAbi.ofByte n.toUInt8)
                else .error (.badArgs s!"OS/ABI byte out of range: {s}")
    | none => .error (.badArgs s!"unknown OS/ABI: {s}")

/-! ## Subcommand handlers

    Each handler reads its file, dispatches the op, and emits stdout
    or writes back per the `RunResult`.  Validation runs at the IO
    boundary in `runResultToIO` so every mutating handler has the
    same write semantics.
-/

/-- Write `out` to `target`, validating first unless `--no-validate`. -/
def writeWithValidation (opts : Options) (target : System.FilePath)
    (out : ByteArray) : IO UInt32 := do
  if opts.validate then
    Patchelf.Log.debug s!"validating {out.size} bytes"
    match validateBytes out with
    | .error f =>
        IO.eprintln s!"validate: {target}: {f.message}"
        IO.eprintln "(use --no-validate to bypass; output may not load at runtime)"
        return 5
    | .ok () => Patchelf.Log.debug "validate: PASS"
  else
    Patchelf.Log.debug "validate: SKIPPED (--no-validate)"
  Patchelf.Log.debug s!"writing {out.size} bytes to {target}"
  let wrOpt ← (IO.FS.writeBinFile target out : IO Unit).toBaseIO
  match wrOpt with
  | .ok _    => return 0
  | .error e => IO.eprintln s!"I/O error writing {target}: {e}"; return 4

/-- Render a `RunResult` to IO.

    `bytes`  — write to `--output` if set, else back to `file` (skip
               write when no mutation occurred).
    `print`  — emit on stdout.  Read-only subcommands return this.
    `silent` — emit nothing.  For prints whose tag is absent (e.g.
               `print-soname` on a binary without DT_SONAME). -/
def runResultToIO (opts : Options) (file : System.FilePath)
    (origBytes : ByteArray) (r : RunResult) :
    IO UInt32 := do
  match r with
  | .print s   => IO.println s; return 0
  | .silent    => return 0
  | .bytes out =>
    let target := opts.outputPath.getD file
    let shouldWrite := opts.outputPath.isSome ∨ out.data ≠ origBytes.data
    if !shouldWrite then return 0
    writeWithValidation opts target out

/-- Read a file, parse it, run a dispatcher, route through
    `runResultToIO`.  The dispatcher is `IO`-valued so handlers can
    do additional IO (read a rename-map file, probe the filesystem
    for `shrink-rpath`, etc.) before emitting a `RunResult`.

    Emits debug traces on stderr when `--debug` is enabled. -/
def runWith (p : Parsed)
    (dispatch : Options → ParsedElf → IO (Except CliError RunResult)) :
    IO UInt32 := do
  match optionsOf p with
  | .error ce => IO.eprintln ce.message; return ce.exitCode
  | .ok opts =>
    Patchelf.Log.setEnabled opts.debug
    Patchelf.Log.debug s!"opts = {repr opts}"
    let file := fileOf p
    Patchelf.Log.debug s!"reading {file}"
    let bsOpt ← (IO.FS.readBinFile file : IO ByteArray).toBaseIO
    match bsOpt with
    | .error e =>
        IO.eprintln s!"I/O error reading {file}: {e}"; return 4
    | .ok bs =>
      Patchelf.Log.debug s!"read {bs.size} bytes; parsing"
      match parse bs with
      | .error err =>
          IO.eprintln s!"parse failed: {repr err}"; return 2
      | .ok pe =>
        Patchelf.Log.debug s!"parsed: phnum={pe.elf.header.phnum} \
          shnum={pe.elf.header.shnum} \
          dynstr={pe.elf.dynstr.map (·.bytes.size) |>.getD 0}B"
        match (← dispatch opts pe) with
        | .error ce =>
            IO.eprintln ce.message; return ce.exitCode
        | .ok r =>
          (match r with
           | .print _ => Patchelf.Log.debug "result: print"
           | .silent  => Patchelf.Log.debug "result: silent"
           | .bytes b => Patchelf.Log.debug s!"result: bytes ({b.size} bytes)")
          runResultToIO opts file bs r

/-! ## Per-op handlers

    Each handler dispatches to the typed-algebra ops via `runDynOp` /
    `runOpNoPre` (returning `Except CliError RunResult`), then `pure`-
    lifts into the `IO` shape `runWith` expects.  Handlers that need
    intra-handler IO (file reads, FS probes) use the `do` form.

    The `printHandler` / `dynHandler` / `noPreHandler` combinators
    absorb the boilerplate `runWith p fun … => pure <| …` shell. -/

/-- A read-only handler emitting a `RunResult` from the parsed ELF. -/
def printHandler (mk : ParsedElf → RunResult) (p : Parsed) : IO UInt32 :=
  runWith p fun _ pe => pure (.ok (mk pe))

/-- Mutating handler dispatching through `runDynOp` (op requires
    `e.dynamic.isSome`).  `opName` is used in error messages. -/
def dynHandler (opName : String)
    (op : Parsed → Options → (tv : Patchelf.Elf.ValidElfFile)
            → tv.dynamic.isSome → Patchelf.Elf.ValidElfFile)
    (p : Parsed) : IO UInt32 :=
  runWith p fun opts pe => pure <| runDynOp opts opName pe.elf (op p opts)

/-- Mutating handler dispatching through `runOpNoPre` (header-only ops). -/
def noPreHandler
    (op : Parsed → Options → Patchelf.Elf.ValidElfFile → Patchelf.Elf.ValidElfFile)
    (p : Parsed) : IO UInt32 :=
  runWith p fun opts pe => pure <| runOpNoPre opts pe.elf (op p opts)

/-! ### Read-only handlers -/

def runPrintOsAbi : Parsed → IO UInt32 :=
  printHandler fun pe => .print pe.elf.header.ident.osAbi.display

def runPrintRpath : Parsed → IO UInt32 :=
  printHandler fun pe => .print (Run.rpathValue pe.elf |>.getD "")

def runPrintNeeded : Parsed → IO UInt32 :=
  printHandler fun pe => .print (String.intercalate "\n" (Run.neededLibs pe.elf))

def runPrintSoname : Parsed → IO UInt32 :=
  printHandler fun pe =>
    match Run.sonameValue pe.elf with
    | none   => .silent
    | some s => .print s

def runPrintExecstack : Parsed → IO UInt32 :=
  printHandler fun pe =>
    let c : Char :=
      match Run.execstackState pe.elf with
      | some true  => 'X'
      | some false => '-'
      | none       => '?'
    .print s!"execstack: {c}"

def runPrintInterpreter : Parsed → IO UInt32 :=
  printHandler fun pe =>
    .print <| match pe.elf.interp.bind Run.readInterpPath with
              | none    => "(no interpreter)"
              | some bs => (String.fromUTF8? bs).getD "(interpreter: invalid UTF-8)"

/-! ### Mutating handlers -/

def runSetOsAbi (p : Parsed) : IO UInt32 :=
  runWith p fun opts pe => pure do
    let abi ← parseOsAbi (p.positionalArg! "abi" |>.as! String)
    runOpNoPre opts pe.elf (fun tv => Patchelf.Elf.setOsAbi tv abi)

def runSetExecstack : Parsed → IO UInt32 :=
  noPreHandler fun _ _ tv => Patchelf.Elf.modifyExecstack tv .set

def runClearExecstack : Parsed → IO UInt32 :=
  noPreHandler fun _ _ tv => Patchelf.Elf.modifyExecstack tv .clear

def runRemoveRpath : Parsed → IO UInt32 :=
  dynHandler "removeRpath" fun _ _ tv h => Patchelf.Elf.removeRpath tv h

def runSetRpath : Parsed → IO UInt32 :=
  dynHandler "setRpath" fun p opts tv h =>
    Patchelf.Elf.modifyRPath tv opts.forceRpath .set
      (p.positionalArg! "path" |>.as! String) h

def runAddRpath (p : Parsed) : IO UInt32 :=
  runWith p fun opts pe =>
    let newPath := p.positionalArg! "path" |>.as! String
    let e := pe.elf
    match e.dynamic with
    | none => pure (throw (Run.badPrecondition "addRpath" "no dynamic section"))
    | some dyn =>
      let composed :=
        if dyn.any (·.isRpathish) then
          match Run.rpathValue e with
          | some old => if old.isEmpty then newPath else old ++ ":" ++ newPath
          | none     => newPath
        else newPath
      pure <| runDynOp opts "addRpath" e fun tv h =>
        Patchelf.Elf.modifyRPath tv opts.forceRpath .set composed h

def splitColonDelimited (s : String) : List String :=
  (s.splitOn ":").filter (fun t => !t.isEmpty)

/-- `shrink-rpath`: filter the existing rpath.  With `--allowed-prefixes`,
    keep only entries that start with one of the supplied prefixes.
    Without it, keep only entries that exist on disk (matches C++
    patchelf's default `--shrink-rpath` heuristic). -/
def runShrinkRpath (p : Parsed) : IO UInt32 :=
  runWith p fun opts pe => do
    let e := pe.elf
    match Run.rpathValue e with
    | none => pure (.ok .silent)  -- no rpath; nothing to shrink
    | some old =>
      let hasPrefixes := p.hasFlag "allowed-prefixes"
      let allowedPrefixes : List String :=
        if hasPrefixes then
          splitColonDelimited (p.flag! "allowed-prefixes" |>.as! String)
        else []
      let mut keep : List String := []
      for entry in old.splitOn ":" do
        if entry.isEmpty then continue
        let prefixOk :=
          !hasPrefixes ∨ allowedPrefixes.any (fun pfx => entry.startsWith pfx)
        if !prefixOk then continue
        if !hasPrefixes ∧ !(← System.FilePath.pathExists ⟨entry⟩) then continue
        keep := keep ++ [entry]
      let composed := String.intercalate ":" keep
      pure <| runDynOp opts "shrinkRpath" e fun tv h =>
        Patchelf.Elf.modifyRPath tv opts.forceRpath .set composed h

def runAddNeeded : Parsed → IO UInt32 :=
  dynHandler "addNeeded" fun p _ tv h =>
    Patchelf.Elf.addNeeded tv (p.positionalArg! "lib" |>.as! String) h

def runRemoveNeeded : Parsed → IO UInt32 :=
  dynHandler "removeNeeded" fun p _ tv h =>
    Patchelf.Elf.removeNeeded tv (p.positionalArg! "lib" |>.as! String) h

def runReplaceNeeded : Parsed → IO UInt32 :=
  dynHandler "replaceNeeded" fun p _ tv h =>
    let oldName := p.positionalArg! "old" |>.as! String
    let newName := p.positionalArg! "new" |>.as! String
    match tv.dynstr.findOffsetOf newName.toUTF8 with
    | some off => Patchelf.Elf.replaceNeededReuse tv oldName off h
    | none     => Patchelf.Elf.replaceNeeded tv oldName newName h

def runSetSoname : Parsed → IO UInt32 :=
  dynHandler "setSoname" fun p _ tv h =>
    Patchelf.Elf.modifySoname tv .set (p.positionalArg! "soname" |>.as! String) h

def runRemoveSoname : Parsed → IO UInt32 :=
  dynHandler "removeSoname" fun _ _ tv h => Patchelf.Elf.modifySoname tv .remove "" h

def runSetInterpreter : Parsed → IO UInt32 :=
  noPreHandler fun p _ tv =>
    Patchelf.Elf.setInterpreter tv (p.positionalArg! "path" |>.as! String)

def runAddDebugTag : Parsed → IO UInt32 :=
  dynHandler "addDebugTag" fun _ _ tv h => Patchelf.Elf.addDebugTag tv h

def runNoDefaultLib : Parsed → IO UInt32 :=
  dynHandler "noDefaultLib" fun _ _ tv h => Patchelf.Elf.noDefaultLib tv h

def runClearSymbolVersion (p : Parsed) : IO UInt32 :=
  runWith p fun opts pe => pure do
    let sym := p.positionalArg! "symbol" |>.as! String
    let e := pe.elf
    let tv ← match Patchelf.Elf.Adapter.ofElfFile e with
      | .error err =>
          throw (Run.badPrecondition "clearSymbolVersion" s!"adapter failed: {repr err}")
      | .ok tv => pure tv
    if hDs : tv.dynsym.isSome then
    if hVs : tv.versym.isSome then
      let hOk : Patchelf.Elf.ClearSymbolVersionOk tv := { hasDynsym := hDs, hasVersym := hVs }
      let tv' := Patchelf.Elf.clearSymbolVersion tv sym hOk
      let e'  := Patchelf.Elf.Adapter.toElfFile e tv'
      .ok (.bytes (Patchelf.Elf.encodeWith opts.pageSize e'))
    else throw (Run.badPrecondition "clearSymbolVersion" "no .gnu.version section")
    else throw (Run.badPrecondition "clearSymbolVersion" "no .dynsym section")

/-- Apply a single `(oldName, newName)` rename.  Returns the post-encode
    bytes, or an error if the typed-op's preconditions aren't met.

    Pipeline:
      1. Adapter decode → typed `ValidElfFile`.
      2. `renameDynamicSymbols` (rebuilds SysV hash if present).
      3. `gnuHashRebuildOp` (rebuilds `.gnu.hash` and reorders dynsym
         + versym; returns the dynsym permutation if `.gnu.hash`
         was present).
      4. Adapter encode → byte-layer `ElfFile`.
      5. (TODO) Apply the permutation to raw rel/rela section bytes
         in the encoded output.  Currently the rebuild produces a
         self-consistent `.gnu.hash` ↔ `.dynsym` view but reloc
         indices may be stale; see ROADMAP §3.3 follow-up. -/
def renameOnce (opts : Options) (e : ElfFile) (oldName newName : String) :
    Except CliError ByteArray := do
  let tv ← match Patchelf.Elf.Adapter.ofElfFile e with
    | .error err =>
        throw (Run.badPrecondition "renameDynamicSymbol" s!"adapter failed: {repr err}")
    | .ok tv => pure tv
  if hDs : tv.dynsym.isSome then
  if hFit : tv.dynstr.bytes.size + newName.toUTF8.size + 1 < UInt32.size then
    let hOk : Patchelf.Elf.RenameDynamicSymbolsOk tv newName :=
      { hasDynsym := hDs, offsetFits := hFit }
    let tv1 := Patchelf.Elf.renameDynamicSymbols tv oldName newName hOk
    let (tv2, perm) := Patchelf.Elf.gnuHashRebuildOp tv1
    let e' := (Patchelf.Elf.Adapter.toElfFile e tv2).remapRelocs perm
    .ok (Patchelf.Elf.encodeWith opts.pageSize e')
  else throw (Run.badPrecondition "renameDynamicSymbol" "UInt32 offset overflow")
  else throw (Run.badPrecondition "renameDynamicSymbol" "no .dynsym")

def runRenameDynamicSymbol (p : Parsed) : IO UInt32 :=
  runWith p fun opts pe => pure do
    let oldName := p.positionalArg! "old" |>.as! String
    let newName := p.positionalArg! "new" |>.as! String
    let bytes ← renameOnce opts pe.elf oldName newName
    .ok (.bytes bytes)

/-- Parse a rename-map file's text into a list of `(oldName, newName)` pairs. -/
def parseRenameMap (text : String) : List (String × String) :=
  text.splitOn "\n" |>.filterMap fun line =>
    let toks := (line.splitOn " ").flatMap (·.splitOn "\t") |>.filter (fun t => !t.isEmpty)
    match toks with
    | [o, n] => some (o, n)
    | _      => none

def runRenameDynamicSymbols (p : Parsed) : IO UInt32 :=
  runWith p fun opts pe => do
    let mapPath := System.FilePath.mk (p.positionalArg! "map-file" |>.as! String)
    match (← (IO.FS.readFile mapPath : IO String).toBaseIO) with
    | .error e => pure (throw (.ioError s!"reading {mapPath}: {e}"))
    | .ok mapText =>
      -- Apply renames sequentially: each iteration parses the post-encode
      -- bytes from the prior iteration to recover an ElfFile.
      let rec loop (buf : ByteArray) :
          List (String × String) → Except CliError ByteArray
        | [] => .ok buf
        | (o, n) :: rest => do
          let pe' ← parse buf |>.mapError .parseFailed
          let buf' ← renameOnce opts pe'.elf o n
          loop buf' rest
      pure do
        let bytes ← loop (Patchelf.Elf.encodeWith opts.pageSize pe.elf)
                          (parseRenameMap mapText)
        .ok (.bytes bytes)

/-- `roundtrip` — parse the input, re-encode, write the result.
    No semantic mutation.  Useful for codec testing: parse+encode
    should be byte-identity on already-laid-out inputs.  Honors
    `--output` (writing in place, with no-write elision when the
    bytes are unchanged). -/
def runRoundtrip (p : Parsed) : IO UInt32 :=
  runWith p fun opts pe =>
    pure (.ok (.bytes (Patchelf.Elf.encodeWith opts.pageSize pe.elf)))

def runValidate (p : Parsed) : IO UInt32 := do
  let file := fileOf p
  let bsOpt ← (IO.FS.readBinFile file : IO ByteArray).toBaseIO
  match bsOpt with
  | .error e => IO.eprintln s!"I/O error reading {file}: {e}"; return 4
  | .ok bs =>
    -- Dual-path: validateBytes (decidable Prop) + parseLoadable (typed
    -- result).  Both should agree on every input; any divergence is a
    -- bug worth surfacing.  Cross-check is cheap (parseLoadable
    -- shares the parse work via the implementation).
    match validateBytes bs, Patchelf.Elf.parseLoadable bs with
    | .ok (), .ok _ => return 0
    | .error f, _ =>
        IO.eprintln s!"validate: {file}: {f.message}"; return 5
    | .ok (), .error e =>
        IO.eprintln s!"validate: {file}: parseLoadable disagreed with \
          validateBytes (would have passed): {repr e}"
        return 5

def runInspect (p : Parsed) : IO UInt32 := do
  let file := fileOf p
  let bsOpt ← (IO.FS.readBinFile file : IO ByteArray).toBaseIO
  match bsOpt with
  | .error e =>
      IO.eprintln s!"I/O error reading {file}: {e}"; return 4
  | .ok bs =>
    match parse bs with
    | .error err =>
        IO.eprintln s!"parse failed: {repr err}"; return 2
    | .ok pe =>
        IO.println "ok"
        IO.println s!"  phnum    = {pe.elf.header.phnum}"
        IO.println s!"  shnum    = {pe.elf.header.shnum}"
        IO.println s!"  shstrndx = {pe.elf.header.shstrndx}"
        IO.println s!"  has dynstr  = {pe.elf.dynstr.isSome}"
        IO.println s!"  has dynamic = {pe.elf.dynamic.isSome}"
        IO.println s!"  has dynsym  = {pe.elf.dynsym.isSome}"
        return 0

/-! ## Subcommand definitions

    Each command is built with the `[Cli|...]` macro DSL.  Op-specific
    flags (e.g. `--force-rpath` for rpath ops, `--allowed-prefixes`
    for shrink-rpath) are declared inline.  The mutating-op flags
    (`--output`, `--no-validate`, `--page-size`, `--debug`) are
    injected into mutating subcommands ONLY via the
    `mutatingFlagsExt` extension.  Read-only subcommands (`print-*`,
    `parse`, `validate`) don't accept these flags — supplying one
    is a CLI error, surfacing user mistakes rather than silently
    ignoring them. -/

/-- Flags consumed by mutating ops:
    * `--output` / `-o` — write target override.
    * `--no-validate` — skip the loader-coherence validator.
    * `--page-size` — override the layout engine's page-alignment.
    * `--debug` — verbose stderr tracing. -/
def mutatingFlags : Array Flag := #[
  { shortName? := some "o", longName := "output",
    description := "write output to PATH instead of in-place",
    type := String },
  { longName := "no-validate",
    description := "skip the loader-coherence validator (UNSAFE)",
    type := Unit },
  { longName := "page-size",
    description := "page-size override for PT_LOAD alignment (e.g. 0x10000 on AArch64)",
    type := Nat },
  { longName := "debug",
    description := "emit verbose tracing on stderr",
    type := Unit }
]

/-- A subcommand is read-only iff its name starts with `print-` or it's
    one of the inspection-only verbs `validate` / `parse`.  Read-only
    subcommands DON'T accept mutating flags (`--output`, `--no-validate`,
    `--page-size`, `--debug`).  Deriving from the name (rather than a
    parallel string list) means new subcommands get the right treatment
    automatically — no drift surface. -/
def isReadOnlyName (name : String) : Bool :=
  name.startsWith "print-" || name = "validate" || name = "parse"

/-- Extension that injects `mutatingFlags` into every mutating
    subcommand.  This avoids 4-line flag repetition in every mutating
    subcommand's `[Cli|...]` block AND keeps the read-only subcommands
    clean — passing `--output` to `print-rpath` is a real bug surface
    (the user probably meant to chain commands differently), so the CLI
    rejects it with "Unknown flag". -/
def mutatingFlagsExt : Extension := {
  extend := fun cmd =>
    let augmentedSubs := cmd.subCmds.map fun sub =>
      if isReadOnlyName sub.meta.name then sub
      else
        let existing := sub.meta.flags
        sub.update (flags := existing ++ mutatingFlags)
    cmd.update (subCmds := augmentedSubs)
}

def cmdPrintOsAbi : Cmd := `[Cli|
  "print-os-abi" VIA runPrintOsAbi;
  "print the ELF header's EI_OSABI byte (canonical name)."
  ARGS:
    file : String;          "ELF file to operate on"
]

def cmdSetOsAbi : Cmd := `[Cli|
  "set-os-abi" VIA runSetOsAbi;
  "set EI_OSABI to <abi> (e.g. linux, sysv, freebsd, or a numeric byte 0..255)."
  ARGS:
    abi : String;           "target OS/ABI"
    file : String;          "ELF file to operate on"
]

def cmdSetExecstack : Cmd := `[Cli|
  "set-execstack" VIA runSetExecstack;
  "set PF_X on PT_GNU_STACK (allow executable stack)."
  ARGS:
    file : String;          "ELF file to operate on"
]

def cmdClearExecstack : Cmd := `[Cli|
  "clear-execstack" VIA runClearExecstack;
  "clear PF_X on PT_GNU_STACK (deny executable stack)."
  ARGS:
    file : String;          "ELF file to operate on"
]

def cmdPrintExecstack : Cmd := `[Cli|
  "print-execstack" VIA runPrintExecstack;
  "print execstack state (X = allowed, - = denied, ? = absent)."
  ARGS:
    file : String;          "ELF file to operate on"
]

def cmdRemoveRpath : Cmd := `[Cli|
  "remove-rpath" VIA runRemoveRpath;
  "strip DT_RPATH/DT_RUNPATH entries."
  ARGS:
    file : String;          "ELF file to operate on"
]

def cmdPrintRpath : Cmd := `[Cli|
  "print-rpath" VIA runPrintRpath;
  "print DT_RUNPATH (or DT_RPATH if no RUNPATH)."
  ARGS:
    file : String;          "ELF file to operate on"
]

def cmdSetRpath : Cmd := `[Cli|
  "set-rpath" VIA runSetRpath;
  "set DT_RUNPATH (or DT_RPATH with --force-rpath)."
  FLAGS:
    f, "force-rpath";       "emit DT_RPATH instead of DT_RUNPATH"
  ARGS:
    path : String;          "filesystem path"
    file : String;          "ELF file to operate on"
]

def cmdAddRpath : Cmd := `[Cli|
  "add-rpath" VIA runAddRpath;
  "append <path> to existing rpath with ':' separator."
  FLAGS:
    f, "force-rpath";       "emit DT_RPATH instead of DT_RUNPATH"
  ARGS:
    path : String;          "filesystem path"
    file : String;          "ELF file to operate on"
]

def cmdShrinkRpath : Cmd := `[Cli|
  "shrink-rpath" VIA runShrinkRpath;
  "drop rpath entries that don't exist on disk; with --allowed-prefixes also drop entries not matching any allowed prefix."
  FLAGS:
    f, "force-rpath";          "emit DT_RPATH instead of DT_RUNPATH"
    "allowed-prefixes" : String; "colon-separated whitelist of prefixes"
  ARGS:
    file : String;             "ELF file to operate on"
]

def cmdPrintNeeded : Cmd := `[Cli|
  "print-needed" VIA runPrintNeeded;
  "print DT_NEEDED library names, one per line."
  ARGS:
    file : String;          "ELF file to operate on"
]

def cmdAddNeeded : Cmd := `[Cli|
  "add-needed" VIA runAddNeeded;
  "insert DT_NEEDED <lib> at the front of the needed list."
  ARGS:
    lib : String;           "shared library name (e.g. libc.so.6)"
    file : String;          "ELF file to operate on"
]

def cmdRemoveNeeded : Cmd := `[Cli|
  "remove-needed" VIA runRemoveNeeded;
  "drop DT_NEEDED entries matching <lib>."
  ARGS:
    lib : String;           "shared library name (e.g. libc.so.6)"
    file : String;          "ELF file to operate on"
]

def cmdReplaceNeeded : Cmd := `[Cli|
  "replace-needed" VIA runReplaceNeeded;
  "rewrite DT_NEEDED <old> to <new>; reuse-existing-offset fast path when <new> is already in dynstr."
  ARGS:
    old : String;           "current library name"
    new : String;           "new library name"
    file : String;          "ELF file to operate on"
]

def cmdPrintSoname : Cmd := `[Cli|
  "print-soname" VIA runPrintSoname;
  "print DT_SONAME (or nothing if absent)."
  ARGS:
    file : String;          "ELF file to operate on"
]

def cmdSetSoname : Cmd := `[Cli|
  "set-soname" VIA runSetSoname;
  "set DT_SONAME to <soname> (typically the library's own name)."
  ARGS:
    soname : String;        "new SONAME"
    file : String;          "ELF file to operate on"
]

def cmdRemoveSoname : Cmd := `[Cli|
  "remove-soname" VIA runRemoveSoname;
  "strip DT_SONAME."
  ARGS:
    file : String;          "ELF file to operate on"
]

def cmdPrintInterpreter : Cmd := `[Cli|
  "print-interpreter" VIA runPrintInterpreter;
  "print PT_INTERP path."
  ARGS:
    file : String;          "ELF file to operate on"
]

def cmdSetInterpreter : Cmd := `[Cli|
  "set-interpreter" VIA runSetInterpreter;
  "rewrite PT_INTERP path."
  ARGS:
    path : String;          "filesystem path"
    file : String;          "ELF file to operate on"
]

def cmdAddDebugTag : Cmd := `[Cli|
  "add-debug-tag" VIA runAddDebugTag;
  "insert DT_DEBUG = 0 if absent (idempotent)."
  ARGS:
    file : String;          "ELF file to operate on"
]

def cmdNoDefaultLib : Cmd := `[Cli|
  "no-default-lib" VIA runNoDefaultLib;
  "OR DF_1_NODEFLIB into DT_FLAGS_1."
  ARGS:
    file : String;          "ELF file to operate on"
]

def cmdClearSymbolVersion : Cmd := `[Cli|
  "clear-symbol-version" VIA runClearSymbolVersion;
  "set the .gnu.version entry for <symbol> to VER_NDX_GLOBAL."
  ARGS:
    symbol : String;        "symbol name"
    file : String;          "ELF file to operate on"
]

def cmdRenameDynamicSymbol : Cmd := `[Cli|
  "rename-dynamic-symbol" VIA runRenameDynamicSymbol;
  "rewrite a single .dynsym entry's st_name from <old> to <new>."
  ARGS:
    old : String;           "current symbol name"
    new : String;           "new symbol name"
    file : String;          "ELF file to operate on"
]

def cmdRenameDynamicSymbols : Cmd := `[Cli|
  "rename-dynamic-symbols" VIA runRenameDynamicSymbols;
  "apply renames listed in <map-file> (one '<old> <new>' pair per line)."
  ARGS:
    "map-file" : String;    "rename map file (one '<old> <new>' pair per line)"
    file : String;          "ELF file to operate on"
]

def cmdValidate : Cmd := `[Cli|
  validate VIA runValidate;
  "check whether <file> is loader-coherent (decidable predicate; no mutation)."
  ARGS:
    file : String;          "ELF file to operate on"
]

def cmdRoundtrip : Cmd := `[Cli|
  roundtrip VIA runRoundtrip;
  "parse <file> and re-encode it (no mutation).  Useful for codec testing: parse+encode should be byte-identity on already-laid-out inputs."
  ARGS:
    file : String;          "ELF file to operate on"
]

def cmdParse : Cmd := `[Cli|
  parse VIA runInspect;
  "parse <file> and print a brief structural summary (debug/inspection)."
  ARGS:
    file : String;          "ELF file to operate on"
]

/-- The root command's `run` is reached only when no subcommand was
    given; print usage to stderr and exit non-zero.  `--help` and
    `--version` are intercepted by `Cmd.validate` before this fires. -/
def runRoot (_p : Parsed) : IO UInt32 := do
  IO.eprintln "no subcommand given; try `patchelf --help`"
  return 1

/-- Root command.  Subcommands are registered here.  We attach
    `helpSubCommand` as an extension so users can write
    `patchelf help` in addition to `patchelf --help`. -/
def cmdRoot : Cmd := `[Cli|
  patchelf VIA runRoot; ["patchelf (Lean 4 port)"]
  "ELF rewriter (Lean 4 port).\n\
   Run `patchelf <subcommand> --help` for per-command details."

  SUBCOMMANDS:
    cmdPrintOsAbi;
    cmdSetOsAbi;
    cmdSetExecstack;
    cmdClearExecstack;
    cmdPrintExecstack;
    cmdRemoveRpath;
    cmdPrintRpath;
    cmdSetRpath;
    cmdAddRpath;
    cmdShrinkRpath;
    cmdPrintNeeded;
    cmdAddNeeded;
    cmdRemoveNeeded;
    cmdReplaceNeeded;
    cmdPrintSoname;
    cmdSetSoname;
    cmdRemoveSoname;
    cmdPrintInterpreter;
    cmdSetInterpreter;
    cmdAddDebugTag;
    cmdNoDefaultLib;
    cmdClearSymbolVersion;
    cmdRenameDynamicSymbol;
    cmdRenameDynamicSymbols;
    cmdValidate;
    cmdRoundtrip;
    cmdParse

  EXTENSIONS:
    mutatingFlagsExt;
    helpSubCommand;
    versionSubCommand!
]

end Patchelf.CLI
