# Research Directory Conventions

This directory contains research documents supporting the long-term goal of
rewriting patchelf in Lean 4 with formal proofs of correctness.

## Purpose

PatchELF has historically suffered from subtle correctness issues that are
difficult to root-cause. Before attempting a rewrite, we must thoroughly
understand:

1. The ELF specification itself (all versions and extensions)
2. The structural invariants that ELF files must satisfy
3. What patchelf does and what can go wrong
4. What properties a correct implementation must preserve

## Document Naming

Use lowercase with hyphens. Prefix documents with a zero-padded number
to indicate reading order:

- `00-overview.md` — high-level map of all research topics
- `01-elf-specification.md` — the ELF standard: history, versions, structure
- `02-gnu-extensions.md` — GNU/Linux extensions to ELF
- `03-dynamic-linking.md` — dynamic linking mechanics in depth
- `04-patchelf-invariants.md` — invariants patchelf must maintain
- `05-edge-cases-and-gaps.md` — ELF edge cases, patchelf gaps, known bug patterns

## Writing Conventions

### Citations

Every factual claim must have an inline footnote citation. Use markdown
footnote syntax:

```markdown
The ELF format was introduced as part of System V Release 4.[^1]

[^1]: AT&T, *System V Application Binary Interface*, Edition 4.1, 1997,
      Section 4 "Object Files".
      http://www.sco.com/developers/gabi/latest/contents.html
```

Footnotes are numbered per-document. Place footnote definitions at the
bottom of the document under a `## References` heading.

For specifications, cite:
- **Document title** (italicized)
- **Author/organization**
- **Edition, version, or date**
- **Section or page number** when referencing a specific claim
- **URL** if available

For source code references, cite:
- **Repository and file path**
- **Line numbers** (or commit hash for stability)
- **Brief description of what the code does**

### Structure

Each document should have:

1. A title (`# Title`)
2. A brief abstract or summary (2-3 sentences)
3. Clearly delineated sections with `##` headings
4. A `## Open Questions` section near the end listing unresolved items
5. A `## References` section at the very end with all footnote definitions

### Accuracy

- Do not speculate. If something is uncertain, mark it with
  `[UNVERIFIED]` and add it to Open Questions.
- Prefer primary sources (specs, RFCs, source code) over secondary
  sources (blog posts, Stack Overflow).
- When specs conflict or are ambiguous, document all interpretations.
- When describing behavior, distinguish between "the spec requires X"
  and "implementations typically do X".

### Scope

Each document should be self-contained enough to read independently, but
may cross-reference other documents in the research directory using
relative links: `[see dynamic linking](03-dynamic-linking.md)`.

## Relationship to the Lean 4 Rewrite

These documents will inform:

- Type definitions for ELF structures
- Theorem statements about structural invariants
- Proof obligations for each patchelf operation
- Test case generation from specification edge cases
