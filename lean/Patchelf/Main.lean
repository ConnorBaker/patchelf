/-
  `patchelf` binary entry point.

  Sub-commands:
    patchelf --smoke                   run self-test
    patchelf --parse <file>            parse and print a summary (debug)
    patchelf --version                 print version string
    patchelf --help | -h               print usage
    patchelf <flag...> <file>          apply ops, write result

  Multi-op invocations are supported: each mutating op is applied in
  C++ patchelf source order, with a re-parse + write cycle between
  ops so every op sees a fully validated input.

  Exit codes:
    0 success
    1 bad arguments / usage
    2 parse error
    3 op precondition failed
    4 I/O error
-/

import Patchelf.CLI
import Patchelf.Elf.Parser

open Patchelf.CLI
open Patchelf.Elf (ParseError)
open Patchelf.Elf (parse ParsedElf)

/-- Version string exposed by `--version`. -/
def versionString : String := "patchelf prototype (Lean 4 port)"

def reportParse (v : ParsedElf) : IO Unit := do
  IO.println s!"ok"
  IO.println s!"  phnum    = {v.elf.header.phnum}"
  IO.println s!"  shnum    = {v.elf.header.shnum}"
  IO.println s!"  shstrndx = {v.elf.header.shstrndx}"
  IO.println s!"  has dynstr  = {v.elf.dynstr.isSome}"
  IO.println s!"  has dynamic = {v.elf.dynamic.isSome}"
  IO.println s!"  has dynsym  = {v.elf.dynsym.isSome}"

def usage : String :=
"usage:
  patchelf --smoke
  patchelf --parse <file>
  patchelf --version
  patchelf [op-flags...] [global-flags...] <file>

operation flags (zero or more per invocation):
  --set-os-abi <abi>          set EI_OSABI byte
  --print-os-abi              print EI_OSABI byte
  --set-execstack             set PF_X on PT_GNU_STACK
  --clear-execstack           clear PF_X on PT_GNU_STACK
  --print-execstack           print execstack state (X/-/?)
  --remove-rpath              strip DT_RPATH/DT_RUNPATH
  --remove-needed <lib>       drop DT_NEEDED entries matching <lib>
  --remove-soname             strip DT_SONAME
  --print-rpath               print first DT_RUNPATH (else RPATH)
  --print-needed              print DT_NEEDED names, one per line
  --print-soname              print DT_SONAME value
  --print-interpreter         print PT_INTERP phdr info
  --set-interpreter <path>    rewrite PT_INTERP path
  --set-rpath <path>          (re)set DT_RUNPATH or DT_RPATH
  --add-rpath <path>          append to existing rpath with ':' separator
  --shrink-rpath              filter rpath by --allowed-rpath-prefixes
  --allowed-rpath-prefixes <p:p:...>
                              whitelist for --shrink-rpath
  --force-rpath               emit DT_RPATH (not DT_RUNPATH) for subsequent
                              rpath changes
  --set-soname <name>         set DT_SONAME, grow .dynstr
  --add-needed <lib>          insert DT_NEEDED before DT_NULL
  --add-debug-tag             insert DT_DEBUG if absent
  --no-default-lib            OR DF_1_NODEFLIB into DT_FLAGS_1
  --replace-needed <old> <new> rewrite DT_NEEDED; fast path if <new> in dynstr
  --rename-dynamic-symbol <old> <new>
                              rewrite a single .dynsym entry's st_name
  --rename-dynamic-symbols <map-file>
                              apply many renames from '<old> <new>' lines
  --clear-symbol-version <sym>
                              zero the .gnu.version entry for matching symbols

global flags:
  --output <path>             write result to <path> instead of the input
  --page-size <N>             (accepted; the layout engine aligns
                              by section.addralign only, doesn't
                              enforce page-granularity PT_LOAD bounds)
  --no-sort                   (accepted; the layout engine doesn't reorder phdrs)
  --no-clobber-old-sections   (accepted; the layout engine doesn't clobber either)
  --debug                     verbose mode (accepted; no extra output yet)
  --version                   print version and exit
  --help, -h                  print this message

argument values prefixed with '@' are read from the named file (C++
patchelf-compatible resolveArgument behavior)."

/-- Print each assertion's status and return `true` iff any failed. -/
private def reportSuite (tag : String) (suite : List (String × Bool)) :
    IO Bool := do
  for (label, ok) in suite do
    IO.println s!"{tag} [{label}]: {if ok then "ok" else "FAIL"}"
  return suite.any (fun (_, ok) => ¬ ok)

/-- Smoke test pathway.  Smoke tests come from the shell test
    harness (`tests/run.sh`) rather than in-Lean assertions. -/
def runSmoke : IO UInt32 := do
  IO.println "smoke mode: run `tests/run.sh` for the shell test suite"
  return 0

/-- Parse-only debug mode. Uses the byte-layer parser. -/
def runParseOnly (path : String) : IO UInt32 := do
  let bs ← IO.FS.readBinFile path
  match parse bs with
  | .ok v => reportParse v; return 0
  | .error err =>
      IO.println s!"parse error: {repr err}"
      return 2

/-- Run one op against the current byte buffer. Returns the new buffer
    (for mutating ops) or leaves it unchanged (for prints), optionally
    emitting text on stdout. -/
def runOneOp (opts : Options) (op : Op) (bs : ByteArray) :
    IO (Except CliError ByteArray) := do
  let result : Except CliError RunResult :=
    match parse bs with
    | .ok v => runOp opts op v
    | .error err => .error (.parseFailed err)
  match result with
  | .error ce => return .error ce
  | .ok (.bytes newBytes) => return .ok newBytes
  | .ok (.print s) =>
      IO.println s
      return .ok bs

/-- Parse a rename-map file's text into a list of `(oldName, newName)`
    pairs. -/
def parseRenameMap (text : String) : List (String × String) :=
  text.splitOn "\n" |>.filterMap fun line =>
    let toks := (line.splitOn " ").flatMap (·.splitOn "\t")
                |>.filter (fun t => !t.isEmpty)
    match toks with
    | [o, n] => some (o, n)
    | _      => none

/-- Apply a single (old, new) rename by re-parsing, dispatching through
    the pure CLI op, and returning the encoded bytes. -/
def applyOneRename (opts : Options) (bs : ByteArray) (oldName newName : String) :
    Except CliError ByteArray :=
  match parse bs with
  | .error err => .error (.parseFailed err)
  | .ok v =>
    match runOp opts (Op.renameDynamicSymbol oldName newName) v with
    | .error ce => .error ce
    | .ok (.bytes outBytes) => .ok outBytes
    | .ok (.print _) =>
        .error (.opPreconditionFailed
          "renameDynamicSymbol returned print output (unexpected)")

/-- Resolve a rename-map form into a sequence of (old, new) renames and
    apply them to a byte buffer. -/
def applyRenameMap (opts : Options) (bs : ByteArray) (mapPath : System.FilePath) :
    IO (Except CliError ByteArray) := do
  let mapOpt ← (IO.FS.readFile mapPath : IO String).toBaseIO
  match mapOpt with
  | .error e => return .error (.ioError s!"reading {mapPath}: {e}")
  | .ok mapText =>
    let pairs := parseRenameMap mapText
    let rec loop (buf : ByteArray) : List (String × String) → Except CliError ByteArray
      | [] => .ok buf
      | (o, n) :: rest =>
          match applyOneRename opts buf o n with
          | .error ce => .error ce
          | .ok buf'  => loop buf' rest
    return loop bs pairs

/-- Fold an op list over a byte buffer. For each op: re-parse, apply,
    continue with the new bytes (or print-only). Errors propagate. -/
partial def runOps (opts : Options) (bs : ByteArray) :
    List Op → IO (Except CliError ByteArray)
  | [] => return .ok bs
  | op :: rest => do
    let step ← match op with
      | .renameDynamicSymbols mp => applyRenameMap opts bs mp
      | _                         => runOneOp opts op bs
    match step with
    | .error ce => return .error ce
    | .ok bs'   => runOps opts bs' rest

/-- Full pipeline: read, run ops in order, write back (or to --output). -/
def runPipeline (inv : Invocation) : IO UInt32 := do
  let bsOpt ← (IO.FS.readBinFile inv.file : IO ByteArray).toBaseIO
  match bsOpt with
  | .error e =>
      IO.eprintln s!"I/O error reading {inv.file}: {e}"
      return 4
  | .ok bs =>
    match (← runOps inv.opts bs inv.ops) with
    | .error ce =>
        IO.eprintln ce.message
        return ce.exitCode
    | .ok outBytes =>
      -- Only write back when bytes differ OR --output redirects.
      let target := inv.opts.outputPath.getD inv.file
      let shouldWrite := inv.opts.outputPath.isSome ∨ outBytes.data ≠ bs.data
      if shouldWrite then
        let wrOpt ← (IO.FS.writeBinFile target outBytes : IO Unit).toBaseIO
        match wrOpt with
        | .ok _ => return 0
        | .error e =>
            IO.println s!"I/O error writing {target}: {e}"
            return 4
      else
        return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--smoke"] => runSmoke
  | ["--parse", path] => runParseOnly path
  | ["--version"] =>
      IO.println versionString
      return 0
  | [] | ["--help"] | ["-h"] =>
      IO.println usage
      return 0
  | _ =>
      -- Resolve @file arguments before parsing flags.
      match (← resolveArgs args) with
      | .error ce =>
          IO.println ce.message
          return ce.exitCode
      | .ok resolved =>
        match parseArgs resolved with
        | .error ce =>
            IO.println ce.message
            IO.println ""
            IO.println usage
            return ce.exitCode
        | .ok inv => runPipeline inv
