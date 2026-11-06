# Explicit Stability of the Weak Simplex Bound: verified Lean supplement

Release: 6 November 2026. Constructed only on DESKTOP-BRJD313, physical E drive,
outside synchronized directories. No local construction.

The fresh certificate verifies 216 source modules and 91 selected public
declarations. Lean 4.31.0, Mathlib fabf563a7c95a166b8d7b6efca11c8b4dc9d911f,
trust level zero. All audited dependencies are limited to propext,
Classical.choice and Quot.sound. Run: 20261106-180522-470580.

This release adds the original exact global quantitative comparison,
centroid estimate, geometric and decoding recovery, rank/energy corollaries,
and actual spherical mean width. It also preserves and rechecks the previous
crossing, strict-normal optimizer and O(rho^6) results.

## Reproduce

Install elan/Lean and Python, then run from the extracted directory:

    lake update
    lake exe cache get
    lake env python reproduce.py

The pinned dependencies are downloaded by Lake. Project compiled binaries
are not bundled or trusted. reproduce.py snapshots the complete source closure
and compiles it into a fresh empty build. It fails closed on source/import
policy violations, compiler failures, source hash changes or axiom mismatches.
Unsupported import header syntax is rejected rather than silently ignored.

## Inspect

- PROOF_MAP_GLOBAL.md: scope and theorem correspondence.
- SOURCE_INDEX.json: exact source/dependency index.
- AUDIT_THEOREMS_GLOBAL.json: audited entry names.
- evidence/verification.json and evidence/logs/: kernel evidence.
- evidence/reviews/: bounded independent Grok Build and agent reviews,
  including the closeout of previously conditional application interfaces.
- VENDOR_PROVENANCE.json and licenses/: upstream sources and attribution.
- SHA256SUMS.json: all packaged file hashes (excluding that manifest itself).

Earlier review reports describe the source state at their recorded time.
CROSS_REVIEW_CLOSEOUT.md records how later modules discharge their remaining
obligations. Raw Grok reasoning logs, credentials and runtime caches are
excluded. The separate paper bundle contains the PDF, TeX and visual QA.
