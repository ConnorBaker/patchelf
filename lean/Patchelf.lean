/-
  Top-level aggregator for the Patchelf library.

  Two tiers:
    * Byte layer (Basic, Layout, Parser, Encoder, LayoutEngine,
      ByteRoundtrip): pure-IR `ElfFile` model + byte-level wire
      codec.  This is how bytes come in and go out.
    * Typed algebra (ValidElfFile + {String,Dynamic,Symbol,Aux,
      Interp}Section + Adapter + the 14 ops under `Elf/Ops/`):
      string-ref offsets are `Fin ds.size`, so cross-section
      bounds are vacuous by construction.  This is where ops
      live and where observable theorems are proved.

  The CLI parses bytes with the byte layer, converts to the
  typed algebra via `Adapter.ofElfFile`, runs an op, converts
  back with `Adapter.toElfFile`, and encodes to bytes.
-/
module

-- Core primitives
public import Patchelf.Elf.Basic
public import Patchelf.Elf.Layout
public import Patchelf.Elf.Reader
public import Patchelf.Elf.Writer
public import Patchelf.Elf.Serialize
public import Patchelf.Elf.ByteLevel
public import Patchelf.Elf.SchemaDSL
public import Patchelf.Elf.Schemas
public import Patchelf.Elf.Decode

-- Byte-level layer (parser / encoder / layout / byte roundtrip)
public import Patchelf.Elf.ElfFile
public import Patchelf.Elf.Parser
public import Patchelf.Elf.Encoder
public import Patchelf.Elf.LayoutEngine
public import Patchelf.Elf.GrowEOF
public import Patchelf.Elf.ByteRoundtrip
public import Patchelf.Elf.SectionOps
public import Patchelf.Elf.Validate

-- Typed-section algebra + adapter + round-trip
public import Patchelf.Elf.StringSection
public import Patchelf.Elf.DynamicSection
public import Patchelf.Elf.SymbolSection
public import Patchelf.Elf.AuxSections
public import Patchelf.Elf.InterpSection
public import Patchelf.Elf.ValidElfFile
public import Patchelf.Elf.DynamicParse
public import Patchelf.Elf.DynamicEncode
public import Patchelf.Elf.Adapter
public import Patchelf.Elf.AdapterRoundtrip
public import Patchelf.Elf.GnuHashRebuild
public import Patchelf.Elf.RelocRemap

-- Observable-correctness combinators
public import Patchelf.Elf.ObservableCombinators

-- Ops
public import Patchelf.Elf.Ops.OsAbi
public import Patchelf.Elf.Ops.Execstack
public import Patchelf.Elf.Ops.AddDebugTag
public import Patchelf.Elf.Ops.NoDefaultLib
public import Patchelf.Elf.Ops.AddNeeded
public import Patchelf.Elf.Ops.AddRpathEntry
public import Patchelf.Elf.Ops.RemoveNeeded
public import Patchelf.Elf.Ops.RemoveRPath
public import Patchelf.Elf.Ops.Rpath
public import Patchelf.Elf.Ops.Soname
public import Patchelf.Elf.Ops.ReplaceNeeded
public import Patchelf.Elf.Ops.ClearSymbolVersion
public import Patchelf.Elf.Ops.RenameDynamicSymbols
public import Patchelf.Elf.Ops.Interpreter

public import Patchelf.Elf.OpAdapterPreservation
public import Patchelf.Elf.OpToElfFactor

@[expose] public section
