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

-- Core primitives
import Patchelf.Elf.Basic
import Patchelf.Elf.Layout
import Patchelf.Elf.Reader
import Patchelf.Elf.Writer
import Patchelf.Elf.Serialize
import Patchelf.Elf.ByteLevel
import Patchelf.Elf.SchemaDSL
import Patchelf.Elf.Schemas
import Patchelf.Elf.Decode

-- Byte-level layer (parser / encoder / layout / byte roundtrip)
import Patchelf.Elf.ElfFile
import Patchelf.Elf.Parser
import Patchelf.Elf.Encoder
import Patchelf.Elf.LayoutEngine
import Patchelf.Elf.ByteRoundtrip
import Patchelf.Elf.SectionOps

-- Typed-section algebra + adapter + round-trip
import Patchelf.Elf.StringSection
import Patchelf.Elf.DynamicSection
import Patchelf.Elf.SymbolSection
import Patchelf.Elf.AuxSections
import Patchelf.Elf.InterpSection
import Patchelf.Elf.ValidElfFile
import Patchelf.Elf.DynamicParse
import Patchelf.Elf.DynamicEncode
import Patchelf.Elf.Adapter
import Patchelf.Elf.AdapterRoundtrip

-- Observable-correctness combinators
import Patchelf.Elf.ObservableCombinators

-- Ops
import Patchelf.Elf.Ops.OsAbi
import Patchelf.Elf.Ops.Execstack
import Patchelf.Elf.Ops.AddDebugTag
import Patchelf.Elf.Ops.NoDefaultLib
import Patchelf.Elf.Ops.AddNeeded
import Patchelf.Elf.Ops.AddRpathEntry
import Patchelf.Elf.Ops.RemoveNeeded
import Patchelf.Elf.Ops.RemoveRPath
import Patchelf.Elf.Ops.Rpath
import Patchelf.Elf.Ops.Soname
import Patchelf.Elf.Ops.ReplaceNeeded
import Patchelf.Elf.Ops.ClearSymbolVersion
import Patchelf.Elf.Ops.RenameDynamicSymbols
import Patchelf.Elf.Ops.Interpreter
