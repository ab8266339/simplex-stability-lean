# Verifier enhancement review

Both requested enhancements are implemented and independently exercised on BRJD E:. No coordinator, kernel-global, theorem source, or frozen vendor source was edited.

## Integration

Copy verify_full.py and its new required sibling verification_guards.py into the final verifier directory. Retain the current source_audit.py and audit_output.py. Include test_verification_guards.py as the independent regression test. verify_full.diff is the concise patch against the coordinator copy; ENHANCEMENT_HASHES.json records the final file hashes.

The module snapshot creation hash must equal the dependency-visit source hash. Immediately before and after every compiler invocation, the actual snapshot file is hashed and checked against that expected hash. A precompile mismatch prevents the compiler from running; a postcompile mismatch changes even a successful compiler result to failure while preserving its original exit code. The generated Audit source has a separate creation hash and the same before/after checks. The final passed flag additionally requires every compiled hash, current snapshot hash, and Audit hash to match.

Environment validation uses the actual compiler executable and effective LEAN_PATH after project-path isolation. It enforces Lean 4.31.0, finds the first Mathlib provider without skipping shadows, walks its ancestors to the actual source repository, checks that it is its own git root, and enforces HEAD fabf563a7c95a166b8d7b6efca11c8b4dc9d911f. Missing tools, source provenance, or mismatching pins fail closed. Existing project lean-toolchain/lakefile pins are retained unmodified and their hashes recorded when present.

## Evidence

- GUARD_TESTS.log: 13 tests passed, independently rerun with exit 0.
- ENVIRONMENT_PROBE.json: real Lake environment, Lean 4.31.0 and exact Mathlib commit passed.
- verification/20261106-180249-214021/verification.json: new empty build, one real Lean module plus generated Audit, both compiled with -j 2 -t 0; passed true.
- compiled_snapshot_hashes_match, snapshot_sources_unchanged, audit_snapshot_hash_matches and environment_pins.passed are all true.
- The smoke theorem axiom audit admitted only propext, Classical.choice and Quot.sound.
- Actual Mathlib source root: E:/claude-lean-work/hsfnlean/.lake/packages/mathlib; provider was its .lake/build/lib/lean directory.

The tests cover mutation before compilation, mutation/deletion during compilation, genuine compiler failure, wrong Lean release/nightly, wrong Mathlib HEAD, wrong git root, missing git/provider, and an earlier shadow Mathlib provider.

These are before/after/final integrity checks, not an operating-system immutable-file guarantee. The Mathlib check certifies the effective provider's source repository HEAD, not a new from-source rebuild of Mathlib. The separate full project fresh build remains the root coordinator's final verification responsibility.

Final hashes:
- verify_full.py: f1afdcb652b394ee6272028fbbeace201ea555a5975e7607a87088af58cda419
- verification_guards.py: 3882272d172fb896fec17351ba178f14efc0712ed2e2c69f01676845546cff52
- test_verification_guards.py: 13f4c88069a7271a294d1c8999c73a1fd799396afe002795a8af63945aae6172
