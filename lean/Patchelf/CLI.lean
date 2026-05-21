/-
  CLI: parse argv, dispatch a list of ops, emit modified bytes.

  Pipeline: byte parser → `Adapter.ofElfFile` → typed op
  (from `Patchelf/Elf/Ops/*.lean`) → `Adapter.toElfFile` → byte
  encoder.  The encoder runs DT_STRSZ sync + conditional
  layout-repack (see `Elf/Encoder.lean`) so size-growing ops
  produce valid ELF output automatically.

  Flag names mirror `src/patchelf.cc`. All 14 base ops + 6 read-only
  print ops + parity flags (`--force-rpath`, `--page-size`, `--output`,
  `--version`, `--debug`, `--no-sort`, `--no-clobber-old-sections`,
  `@file`).

  A single `patchelf` invocation can combine multiple flags; they
  are applied in argv order. Between ops we re-parse the intermediate
  bytes so each op sees a fully-validated input.

  Every mutating branch dispatches through a typed op via
  `Adapter.ofElfFile` → op → `Adapter.toElfFile`.  Precondition checks
  (e.g. `e.dynamic.isSome` for dynamic-section ops) are
  runtime-checked and build the `isSome` witness or return
  `CliError.opPreconditionFailed`.  Zero `sorry`.

  Test status: all 49 shell tests in `tests/cases/` pass.
-/

import Patchelf.Elf.Parser
import Patchelf.Elf.Encoder

-- 14 mutating ops + adapter live under Elf/Ops/ and Elf/
-- respectively.  The byte-level parser/encoder (Parser / Encoder)
-- are the byte-layer wire codecs.

import Patchelf.Elf.Adapter
import Patchelf.Elf.Ops.OsAbi
import Patchelf.Elf.Ops.Execstack
import Patchelf.Elf.Ops.AddDebugTag
import Patchelf.Elf.Ops.NoDefaultLib
import Patchelf.Elf.Ops.AddNeeded
import Patchelf.Elf.Ops.Rpath
import Patchelf.Elf.Ops.Soname
import Patchelf.Elf.Ops.RemoveRPath
import Patchelf.Elf.Ops.RemoveNeeded
import Patchelf.Elf.Ops.AddRpathEntry
import Patchelf.Elf.Ops.Interpreter
import Patchelf.Elf.Ops.ReplaceNeeded
import Patchelf.Elf.Ops.ClearSymbolVersion
import Patchelf.Elf.Ops.RenameDynamicSymbols

namespace Patchelf.CLI

open Patchelf.Elf (OsAbi ParseError DynEntry DynTag StringTable)
open Patchelf.Elf (ElfFile ParsedElf parse encode)
open Patchelf.Elf.Layout (PhType)

/-- How `--set-rpath`/`--add-rpath` should choose between DT_RPATH and
    DT_RUNPATH. `.default` uses the modern choice (DT_RUNPATH) unless
    the binary already has a DT_RPATH and no DT_RUNPATH, in which case
    C++ patchelf converts to RUNPATH anyway. `.force` (from
    `--force-rpath`) keeps DT_RPATH. -/
inductive RpathTagPolicy | default | force
  deriving DecidableEq, Repr

/-- One operation to run, derived from the parsed argv. Ops with
    context-dependent input (e.g. `--add-rpath` needs the existing
    rpath string) are resolved at runtime during the pipeline fold. -/
inductive Op
  -- Safe (no section growth): implemented
  | setOsAbi (abi : OsAbi)
  | setExecstack
  | clearExecstack
  | removeRpath
  | removeNeeded (lib : String)
  | removeSoname

  -- Read-only prints: implemented
  | printOsAbi
  | printInterpreter
  | printRpath
  | printNeeded
  | printSoname
  | printExecstack

  -- Mutating ops (the encoder handles growth implicitly via `encodedSize`).
  | setRpath (policy : RpathTagPolicy) (path : String)
  /-- `--add-rpath`: prepend the existing rpath to `newPath` with ':'.
      At runtime we read the current rpath via `rpathValue`, compose
      `oldRpath ++ ":" ++ newPath`, and dispatch as `setRpath`. -/
  | addRpath (policy : RpathTagPolicy) (path : String)
  /-- `--shrink-rpath`: keep only the entries whose string starts with
      one of the given allowed prefixes (or all entries when the list
      is empty — matches C++ rpShrink's filesystem-based heuristic's
      degenerate case). Composes with the current rpath at runtime. -/
  | shrinkRpath (policy : RpathTagPolicy) (allowedPrefixes : List String)
  | addNeeded (lib : String)
  | replaceNeeded (oldName newName : String)
  | setSoname (name : String)
  | setInterpreter (path : String)
  | addDebugTag
  | noDefaultLib
  | renameDynamicSymbols (mappingFile : System.FilePath)
  /-- Single-pair rename (CLI convenience; the map-file form is IO-bound
      so it lives in Main.lean, not the pure dispatcher). -/
  | renameDynamicSymbol (oldName newName : String)
  | clearSymbolVersion (sym : String)
  deriving Repr

/-- Global options that apply across the whole invocation, orthogonal
    to the list of ops. -/
structure Options where
  /-- Override target path for writes. `none` = write back in place. -/
  outputPath : Option System.FilePath := none
  /-- Alignment parameter accepted for C++ CLI parity. The CLI has no
      layout engine, so it's recorded but unused. -/
  pageSize : Nat := 4096
  /-- Enable verbose stderr tracing. Accepted-and-recorded; The CLI doesn't
      currently emit trace output. -/
  debug : Bool := false
  deriving Repr

/-- A parsed command line. -/
structure Invocation where
  ops    : List Op
  file   : System.FilePath
  opts   : Options
  deriving Repr

/-- Classified exit conditions. -/
inductive CliError
  | badArgs (message : String)
  | parseFailed (err : ParseError)
  | opPreconditionFailed (message : String)
  | ioError (message : String)
  deriving Repr

def CliError.exitCode : CliError → UInt32
  | .badArgs _               => 1
  | .parseFailed _           => 2
  | .opPreconditionFailed _  => 3
  | .ioError _               => 4

def CliError.message : CliError → String
  | .badArgs m              => s!"bad arguments: {m}"
  | .parseFailed e          => s!"parse failed: {repr e}"
  | .opPreconditionFailed m => s!"op precondition failed: {m}"
  | .ioError m              => s!"I/O error: {m}"

/-! ## Argument parsing -/

namespace Parse

/-- Look up a canonical OS/ABI name. Matches the names `patchelf --set-os-abi`
    accepts on the command line. -/
def parseOsAbi (s : String) : Except CliError OsAbi :=
  match s with
  | "System V" | "SysV" | "sysv" => .ok .systemV
  | "Linux" | "linux" => .ok .linux
  | "FreeBSD" | "freebsd" => .ok .freebsd
  | _ =>
    match s.toNat? with
    | some n => if n < 256 then .ok (OsAbi.ofByte n.toUInt8)
                else .error (.badArgs s!"OS/ABI byte out of range: {s}")
    | none => .error (.badArgs s!"unknown OS/ABI: {s}")

/-- Split a colon-delimited string, dropping empty fields. Used for
    `--allowed-rpath-prefixes`. -/
def splitColonDelimited (s : String) : List String :=
  (s.splitOn ":").filter (fun t => !t.isEmpty)

/-- Parser state: accumulated ops, options, positional files. -/
structure State where
  ops   : List Op       := []
  opts  : Options       := {}
  files : List String   := []
  /-- Set by `--force-rpath`. Applies to any SUBSEQUENT rpath set/add in
      the same invocation, matching C++ patchelf where the flag is a
      sticky boolean read at op time. -/
  forceRpath : Bool     := false
  deriving Repr

/-- Append one op to the state. -/
def State.push (s : State) (op : Op) : State := { s with ops := s.ops ++ [op] }

/-- Consumers left in `args` after we peel `n` tokens. The `--flag ARG`
    pattern threads as `consume 1 args k`, binding `arg` and the tail. -/
def needArg (flag : String) (args : List String)
    (k : String → List String → Except CliError State) : Except CliError State :=
  match args with
  | []      => .error (.badArgs s!"{flag}: missing argument")
  | a :: tl => k a tl

/-- The token-stream parser. Walks left-to-right, producing a `State` on
    success. -/
partial def parseLoop (st : State) : List String → Except CliError State
  | [] => .ok st
  | a :: rest =>
    let policy : RpathTagPolicy :=
      if st.forceRpath then .force else .default
    match a with
    -- Trivial flags.
    | "--set-execstack"   => parseLoop (st.push .setExecstack) rest
    | "--clear-execstack" => parseLoop (st.push .clearExecstack) rest
    | "--print-execstack" => parseLoop (st.push .printExecstack) rest
    | "--remove-rpath"    => parseLoop (st.push .removeRpath) rest
    | "--remove-soname"   => parseLoop (st.push .removeSoname) rest
    | "--print-os-abi"    => parseLoop (st.push .printOsAbi) rest
    | "--print-interpreter" => parseLoop (st.push .printInterpreter) rest
    | "--print-rpath"     => parseLoop (st.push .printRpath) rest
    | "--print-needed"    => parseLoop (st.push .printNeeded) rest
    | "--print-soname"    => parseLoop (st.push .printSoname) rest
    | "--add-debug-tag"   => parseLoop (st.push .addDebugTag) rest
    | "--no-default-lib"  => parseLoop (st.push .noDefaultLib) rest
    -- Sticky rpath-tag policy.
    | "--force-rpath"     => parseLoop { st with forceRpath := true } rest
    -- Parity no-ops (The layout engine doesn't reorder phdrs
    -- or clobber sections, so these flags are accepted as no-ops).
    | "--no-sort"                 => parseLoop st rest
    | "--no-clobber-old-sections" => parseLoop st rest
    -- Informational flags handled by the caller.
    | "--debug" => parseLoop { st with opts := { st.opts with debug := true } } rest
    -- Arg-taking flags.
    | "--set-os-abi" => needArg "--set-os-abi" rest fun abi rest' => do
        let a ← parseOsAbi abi
        parseLoop (st.push (.setOsAbi a)) rest'
    | "--remove-needed" => needArg "--remove-needed" rest fun lib rest' =>
        parseLoop (st.push (.removeNeeded lib)) rest'
    | "--set-rpath" => needArg "--set-rpath" rest fun p rest' =>
        parseLoop (st.push (.setRpath policy p)) rest'
    | "--add-rpath" => needArg "--add-rpath" rest fun p rest' =>
        parseLoop (st.push (.addRpath policy p)) rest'
    | "--shrink-rpath" =>
        parseLoop (st.push (.shrinkRpath policy [])) rest
    | "--allowed-rpath-prefixes" =>
        needArg "--allowed-rpath-prefixes" rest fun pfxStr rest' =>
          let pfx := splitColonDelimited pfxStr
          match st.ops.reverse with
          | .shrinkRpath pol _ :: earlierRev =>
              let ops' := (.shrinkRpath pol pfx :: earlierRev).reverse
              parseLoop { st with ops := ops' } rest'
          | _ =>
              .error (.badArgs
                "--allowed-rpath-prefixes must follow --shrink-rpath")
    | "--add-needed" => needArg "--add-needed" rest fun lib rest' =>
        parseLoop (st.push (.addNeeded lib)) rest'
    | "--replace-needed" =>
        needArg "--replace-needed (old)" rest fun o rest' =>
        needArg "--replace-needed (new)" rest' fun n rest'' =>
          parseLoop (st.push (.replaceNeeded o n)) rest''
    | "--set-soname" => needArg "--set-soname" rest fun name rest' =>
        parseLoop (st.push (.setSoname name)) rest'
    | "--set-interpreter" | "--interpreter" =>
        needArg "--set-interpreter" rest fun p rest' =>
          parseLoop (st.push (.setInterpreter p)) rest'
    | "--rename-dynamic-symbol" =>
        needArg "--rename-dynamic-symbol (old)" rest fun o rest' =>
        needArg "--rename-dynamic-symbol (new)" rest' fun n rest'' =>
          parseLoop (st.push (.renameDynamicSymbol o n)) rest''
    | "--rename-dynamic-symbols" =>
        needArg "--rename-dynamic-symbols" rest fun m rest' =>
          parseLoop (st.push (.renameDynamicSymbols (System.FilePath.mk m))) rest'
    | "--clear-symbol-version" =>
        needArg "--clear-symbol-version" rest fun s rest' =>
          parseLoop (st.push (.clearSymbolVersion s)) rest'
    | "--output" => needArg "--output" rest fun p rest' =>
        parseLoop { st with opts :=
          { st.opts with outputPath := some (System.FilePath.mk p) } } rest'
    | "--page-size" => needArg "--page-size" rest fun ps rest' =>
        match ps.toNat? with
        | some n =>
            if n > 0 then
              parseLoop { st with opts := { st.opts with pageSize := n } } rest'
            else .error (.badArgs s!"--page-size requires a positive integer, got: {ps}")
        | none => .error (.badArgs s!"--page-size: not a non-negative integer: {ps}")
    -- Recognized by caller, not here.
    | "--version" | "--help" | "-h" =>
        .error (.badArgs s!"{a} must be the only argument")
    -- Anything else is a positional (file) argument.
    | other =>
        if other.startsWith "--" then
          .error (.badArgs s!"unrecognized flag: {other}")
        else
          parseLoop { st with files := st.files ++ [other] } rest

end Parse

/-- Read an argument; if it begins with `@`, read the rest as a file path
    and return its contents (mirrors C++ `resolveArgument`). -/
def resolveArgument (s : String) : IO (Except CliError String) := do
  if s.startsWith "@" ∧ s.length > 1 then
    let path : String := s.drop 1 |>.toString
    try
      let body ← IO.FS.readFile (System.FilePath.mk path)
      return .ok body.trimAscii.toString
    catch e =>
      return .error (.ioError s!"reading @{path}: {e}")
  else
    return .ok s

/-- Rewrite `@file` arguments to their resolved contents. Only values
    starting with `@` are resolved; flag names and regular positional
    paths pass through unchanged. -/
def resolveArgs (args : List String) : IO (Except CliError (List String)) := do
  let rec loop : List String → IO (Except CliError (List String))
    | []      => return .ok []
    | a :: tl => do
      if a.startsWith "@" then
        match (← resolveArgument a) with
        | .error e  => return .error e
        | .ok body  =>
          match (← loop tl) with
          | .error e  => return .error e
          | .ok tl'   => return .ok (body :: tl')
      else
        match (← loop tl) with
        | .error e  => return .error e
        | .ok tl'   => return .ok (a :: tl')
  loop args

/-- Walk an argv list, producing an `Invocation`. The last positional
    argument is the file path; everything else is flags. -/
def parseArgs : List String → Except CliError Invocation
  | [] => .error (.badArgs "no arguments; try `patchelf --help`")
  | args => do
    let st ← Parse.parseLoop {} args
    match st.files with
    | []          => .error (.badArgs "missing file argument")
    | [filePath]  =>
        if st.ops.isEmpty then
          .error (.badArgs "no operation flags given")
        else
          .ok { ops := st.ops, file := filePath, opts := st.opts }
    | files       => .error (.badArgs s!"multiple files not supported yet: {files}")

/-! ## Read-only accessors on ElfFile

    Each one walks the pure-IR `ElfFile` for the bit of context the
    corresponding `print*` op needs. -/

namespace Run

/-- Lookup a C-string at an offset in `.dynstr`. -/
def resolveDynstrName (e : ElfFile) (off : UInt64) : Option String :=
  match e.dynstr with
  | some ds => ds.lookup off.toNat |>.bind String.fromUTF8?
  | none => none

/-- DT_NEEDED library names, each resolved via `.dynstr`. Entries whose
    name can't be resolved are dropped. -/
def neededLibs (e : ElfFile) : List String :=
  e.dynamic.map (·.toList.filterMap fun d =>
    if d.tag = DynTag.needed then resolveDynstrName e d.value else none)
    |>.getD []

/-- Find the first entry in `.dynamic` with a given tag and resolve its
    `value` as a `.dynstr` offset. Returns `none` if `.dynamic` is
    absent, no entry matches, or the offset doesn't resolve. -/
def findDynstrByTag (e : ElfFile) (tag : DynTag) : Option String :=
  e.dynamic.bind (fun dyn =>
    dyn.toList.find? (fun d => d.tag = tag)
      |>.bind (fun d => resolveDynstrName e d.value))

/-- DT_RPATH / DT_RUNPATH value. Real patchelf prefers RUNPATH when both
    are present. -/
def rpathValue (e : ElfFile) : Option String :=
  findDynstrByTag e DynTag.runpath |>.orElse fun _ => findDynstrByTag e DynTag.rpath

/-- DT_SONAME value. -/
def sonameValue (e : ElfFile) : Option String :=
  findDynstrByTag e DynTag.soname

/-- PF_X bit on PT_GNU_STACK: `some true` if set, `some false` if cleared,
    `none` if no PT_GNU_STACK segment. -/
def execstackState (e : ElfFile) : Option Bool :=
  e.phdrs.foldl (init := none) fun acc ph =>
    match acc with
    | some _ => acc
    | none   =>
      if ph.type = PhType.PT_GNU_STACK then
        some ((ph.flags &&& Patchelf.Elf.ExecstackFlags.PF_X) = Patchelf.Elf.ExecstackFlags.PF_X)
      else none

/-- Read the C-string at the start of a `.interp`-style byte array:
    everything up to the first NUL byte. Returns `none` on no NUL. -/
def readInterpPath (ib : ByteArray) : Option ByteArray :=
  StringTable.findNullFrom ib 0 0

end Run

/-- Run result: either bytes to write back to the file, or a string to
    print on stdout (for `--print-*` ops). -/
inductive RunResult
  | bytes (bs : ByteArray)
  | print (s : String)

/-! ## Op dispatch -/

namespace Run

/-- Shared precondition-failure wrapper. -/
private def badPrecondition (opName detail : String) : CliError :=
  .opPreconditionFailed s!"{opName}: bad precondition ({detail})"

/-- Convert the policy to the `forceRpath` Bool consumed by `modifyRPath`. -/
private def policyForce (p : RpathTagPolicy) : Bool :=
  match p with
  | .default => false
  | .force   => true

end Run

/-! ## Typed-op routing helpers.

    Most ops take `e : ValidElfFile → (args) → (_h : e.dynamic.isSome) → ValidElfFile`.
    This helper wires bytes → typed → op → bytes → encode,
    handling the `isSome` precondition via runtime match. -/
private def runDynOp (opName : String) (e : Patchelf.Elf.ElfFile)
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
          .ok (.bytes (encode e'))

/-- No-precondition wrapper (for ops like setOsAbi, modifyExecstack
    that don't require dynamic section). -/
private def runOpNoPre (e : Patchelf.Elf.ElfFile)
    (f : Patchelf.Elf.ValidElfFile → Patchelf.Elf.ValidElfFile) :
    Except CliError RunResult :=
  match Patchelf.Elf.Adapter.ofElfFile e with
  | .error err =>
      throw (Run.badPrecondition "op" s!"adapter failed: {repr err}")
  | .ok tv =>
      let tv' := f tv
      let e' := Patchelf.Elf.Adapter.toElfFile e tv'
      .ok (.bytes (encode e'))

/-- Apply an op to a validated ElfFile. For read-only (`print*`) ops,
    returns text to emit. For mutating ops, returns encoded bytes. -/
def runOp (_opts : Options) (op : Op) (v : ParsedElf) :
    Except CliError RunResult := do
  let e := v.elf
  match op with
  -- Base ops with no runtime precondition — routed through the typed algebra.
  | .setOsAbi abi =>
      runOpNoPre e (fun tv => Patchelf.Elf.setOsAbi tv abi)
  | .setExecstack =>
      runOpNoPre e (fun tv => Patchelf.Elf.modifyExecstack tv .set)
  | .clearExecstack =>
      runOpNoPre e (fun tv => Patchelf.Elf.modifyExecstack tv .clear)

  -- Dynamic-only ops — routed through the typed algebra.
  | .removeRpath =>
      runDynOp "removeRpath" e (fun tv h =>
        Patchelf.Elf.removeRpath tv h)
  | .removeNeeded lib =>
      runDynOp "removeNeeded" e (fun tv h =>
        Patchelf.Elf.removeNeeded tv lib h)
  | .removeSoname =>
      runDynOp "removeSoname" e (fun tv h =>
        Patchelf.Elf.modifySoname tv .remove "" h)

  -- Read-only prints.
  | .printOsAbi =>
      return .print e.header.ident.osAbi.display
  | .printInterpreter =>
      match e.interp.bind Run.readInterpPath with
      | none    => return .print "(no interpreter)"
      | some bs =>
        match String.fromUTF8? bs with
        | some s => return .print s
        | none   => return .print "(interpreter: invalid UTF-8)"
  | .printRpath =>
      return .print (Run.rpathValue e |>.getD "")
  | .printNeeded =>
      return .print (String.intercalate "\n" (Run.neededLibs e))
  | .printSoname =>
      return .print (Run.sonameValue e |>.getD "")
  | .printExecstack =>
      let c : Char :=
        match Run.execstackState e with
        | some true  => 'X'
        | some false => '-'
        | none       => '?'
      return .print s!"execstack: {c}"

  -- setInterpreter — typed-algebra-routed.
  | .setInterpreter newPath =>
      runOpNoPre e (fun tv => Patchelf.Elf.setInterpreter tv newPath)

  | .addDebugTag =>
      runDynOp "addDebugTag" e (fun tv h =>
        Patchelf.Elf.addDebugTag tv h)

  | .noDefaultLib =>
      runDynOp "noDefaultLib" e (fun tv h =>
        Patchelf.Elf.noDefaultLib tv h)

  | .replaceNeeded oldName newName =>
      -- try reuse first (look up newName in dynstr); fall back to grow path.
      runDynOp "replaceNeeded" e (fun tv h =>
        match tv.dynstr.findOffsetOf newName.toUTF8 with
        | some off => Patchelf.Elf.replaceNeededReuse tv oldName off h
        | none     => Patchelf.Elf.replaceNeeded tv oldName newName h)

  | .addNeeded lib =>
      runDynOp "addNeeded" e (fun tv h =>
        Patchelf.Elf.addNeeded tv lib h)

  | .setSoname name =>
      runDynOp "setSoname" e (fun tv h =>
        Patchelf.Elf.modifySoname tv .set name h)

  -- --set-rpath: retag existing DT_RPATH/RUNPATH if present; otherwise
  -- insert a fresh DT_RUNPATH (or DT_RPATH under `--force-rpath`).
  -- single modifyRPath op handles both paths (it's a typed record update).
  | .setRpath policy path =>
      runDynOp "setRpath" e (fun tv h =>
        Patchelf.Elf.modifyRPath tv (Run.policyForce policy) .set path h)

  -- --add-rpath: compose with existing rpath, then setRpath.
  | .addRpath policy newPath =>
      match e.dynamic with
      | none => throw (Run.badPrecondition "addRpath" "no dynamic section")
      | some dyn =>
        let composed :=
          if dyn.any (·.isRpathish) then
            match Run.rpathValue e with
            | some old => if old.isEmpty then newPath else old ++ ":" ++ newPath
            | none     => newPath
          else newPath
        runDynOp "addRpath" e (fun tv h =>
          Patchelf.Elf.modifyRPath tv (Run.policyForce policy) .set composed h)

  -- --shrink-rpath: filter the current rpath against the prefix whitelist
  -- and dispatch as setRpath.  typed-algebra-routed.
  | .shrinkRpath policy allowedPrefixes =>
      match Run.rpathValue e with
      | none => return .bytes (encode e)
      | some old =>
          let keep : List String :=
            (old.splitOn ":").filter fun entry =>
              !entry.isEmpty ∧
              (allowedPrefixes.isEmpty ∨
                allowedPrefixes.any (fun p => entry.startsWith p))
          let composed := String.intercalate ":" keep
          if composed = old then return .bytes (encode e)
          else
            runDynOp "shrinkRpath" e (fun tv h =>
              Patchelf.Elf.modifyRPath tv (Run.policyForce policy) .set composed h)

  | .renameDynamicSymbol oldName newName =>
      -- Typed op uses a RenameDynamicSymbolsOk structure; build it at runtime.
      match Patchelf.Elf.Adapter.ofElfFile e with
      | .error err => throw (Run.badPrecondition "renameDynamicSymbol"
          s!"adapter failed: {repr err}")
      | .ok tv =>
          if hDs : tv.dynsym.isSome then
          if hGh : tv.gnuHash.isNone then
          if hFit : tv.dynstr.bytes.size + newName.toUTF8.size + 1 < UInt32.size then
            let hOk : Patchelf.Elf.RenameDynamicSymbolsOk tv newName :=
              { hasDynsym := hDs, offsetFits := hFit, noGnuHash := hGh }
            let tv' := Patchelf.Elf.renameDynamicSymbols tv oldName newName hOk
            let e' := Patchelf.Elf.Adapter.toElfFile e tv'
            return .bytes (encode e')
          else throw (Run.badPrecondition "renameDynamicSymbol" "UInt32 offset overflow")
          else throw (Run.badPrecondition "renameDynamicSymbol" ".gnu.hash present")
          else throw (Run.badPrecondition "renameDynamicSymbol" "no .dynsym")

  -- The map-file form takes IO; intercepted by Main.runRenamePipeline
  -- before the pure dispatcher runs.
  | .renameDynamicSymbols _ => throw (.opPreconditionFailed
      "renameDynamicSymbols (map-file form) must go through Main.applyRenameMap")

  -- --clear-symbol-version <sym>: zero versym entries matching `sym`.
  | .clearSymbolVersion sym =>
      match Patchelf.Elf.Adapter.ofElfFile e with
      | .error err => throw (Run.badPrecondition "clearSymbolVersion"
          s!"adapter failed: {repr err}")
      | .ok tv =>
          if hDs : tv.dynsym.isSome then
          if hVs : tv.versym.isSome then
            let hOk : Patchelf.Elf.ClearSymbolVersionOk tv :=
              { hasDynsym := hDs, hasVersym := hVs }
            let tv' := Patchelf.Elf.clearSymbolVersion tv sym hOk
            let e' := Patchelf.Elf.Adapter.toElfFile e tv'
            return .bytes (encode e')
          else throw (Run.badPrecondition "clearSymbolVersion" "no .gnu.version section")
          else throw (Run.badPrecondition "clearSymbolVersion" "no .dynsym section")

end Patchelf.CLI
