# Restored foundations review

Verdict: the collaborator statements inspected here are the paper rectangle lemma and Theorem global on `A_m`, singular covariances included. Their existing `-t 0` logs name only `propext`, `Classical.choice`, and `Quot.sound`. This review did not rebuild.

Lean 4.31.0. Mathlib `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`, recorded in `vendor-staging/PROVENANCE.json` and in both upstream `lake-manifest.json` files. Weak-simplex HEAD `f59d449132ca8a08f48093efce41e80cbd772d04`. Uniqueness HEAD `54eaa804e722cf3e763c87492056b27702ac526e`, and its lakefile requires weak-simplex `f59d449132ca8a08f48093efce41e80cbd772d04`. Those two commits are different repositories, and the require line ties them.

## Provenance and the 52-module closure

`PROVENANCE.json` and `foundation-audit/CUSTOM_SOURCE_CLOSURE.json` list the same 52 modules in the same topological order: 47 `WeakSimplexConjectureLean` modules, the bare root `WeakSimplexConjectureLean`, and 4 `SimplexUniquenessLean` modules. Every provenance `changes` field is `none`. Rehashed local staging bytes equal the recorded sha256 and equal the original upstream bytes, licenses included. Vendor run `vendor-staging/verification/20261106-075019-854450` records 52 oleans, `passed: true`, and FoundationProbe axioms `{propext, Classical.choice, Quot.sound}`. This review did not repeat that build.

`centered_product_of_posDef` stays positive-definite. `centeredProduct_gt` and `symmetricRectangle_gt_iid` take `IsCorrelation` and allow a singular matrix. `exists_adaptiveWitnesses_of_isWeakSimplexCov` supplies witnesses for singular weak-simplex covariances.

## Three foundation-audit modules

Current bytes match the existing json `source_sha256` values. Each log is exit 0 under Lean 4.31.0 `-j 2 -t 0`.

`GlobalFoundationBridge` is a qualitative decoding and MGF comparison. `decodingSuccess_gram_le_simplex` uses `IsCorrelation`, so a singular Gram is included. It does not state the rectangle constant. The log has unused-simp warnings. Printed axioms are the three standard ones.

`GlobalComparisonProduct.normalizedSelfConvolution_product_ge_one` states `1 ≤ ∫ ∏ normalizedSelfConvolution` for centered tilted half-lines on every `IsCorrelation`, with no invertibility hypothesis. The proof regularizes to a positive-definite correlation and passes to the PSD limit. Printed axioms are the three standard ones. The statement is this tilted family. A general centered product for discontinuous log-concave factors on a singular correlation is not this theorem.

`GlobalWitnessOrthantBound.orthant_mass_eq_tilted_product` equates orthant mass to the tilted product for `PosSemidef` once an `AdaptiveWitnesses` value is given. `exp_adaptive_value_le_orthant_of_ne_one` needs `IsWeakSimplexCov` and `R ≠ 1`, and its text makes no maximization claim. The log contains a `ring_nf` hint and exit code 0. Printed axioms are the three standard ones. Coordinator copies of the bridge and orthant files matched these foundation-audit bytes. `GlobalComparisonProduct.lean` has no coordinator twin.

## Rectangle lemma and Theorem global

`SimplexFull.GlobalRectangle.rectangleK` is `ℓ² exp(-4T²/3) (2Φ(ℓ)-1)^(m-2) / (4π m (m-1))`. `symmetricRectangle_gap` multiplies it by `∑∑ ((R-1) k l)²` for `2 ≤ m`, `PosSemidef`, unit diagonal, and radii in `[ℓ, T]`. The pair proof has an explicit `|ρ| = 1` branch. That is the paper rectangle lemma, singular correlations included.

`SimplexFull.GlobalComparison.quantitative_lowerOrthant` states both the square-root form and the `paperKappa` form of Theorem global for `2 ≤ m`, `IsWeakSimplexCov`, and `c ∈ [u, v]`. Paper `A_m` is unit diagonal and `R - J/m ≽ 0`, which is this predicate. The identity covariance is a separate case inside `orthant_sqrt_comparison`. Geometry certificate `SimplexFull.GlobalComparison.latest.json` has exit 0, `-t 0`, source sha256 `bcd7064747863e5ca8752a8894caaf508701d4e4203000072ad132ce4b62ab97`, matching the current file, and the stdout lists the three standard axioms. This review did not recompile it. Those modules should stay as they are.

## Coordinator source-only checker

Current `coordinator/source_audit.py` and `verify_full.py` were read after the isolation edit.

`fresh_lean_path` drops the new build, `source_root/build`, any path entry that contains a project-prefix directory, and any entry that contains a bare `Prefix.olean`, `.olean.private`, `.olean.server`, or `.ilean`. The bare-file clause covers the sibling root `WeakSimplexConjectureLean.olean`.

`import_names` accepts a conventional one-line import and rejects an empty import continuation, an import after a declaration, an unrecognized header line, a non-identifier import token, and an unaudited import root.

`forbidden_constructs` rejects `sorry`, `admit`, `axiom`, `unsafe`, `native_decide`, and `debug.skipKernelTC` on comment-stripped and string-stripped text. `verify_full.py` runs that scan on the snapshotted closure, compiles with `lean -j 2 -t 0`, and accepts a run only when the audit exit code is 0, `check_axiom_output` passes, and the original sources still match the visit hashes. `audit_output.py` allows only `propext`, `Classical.choice`, and `Quot.sound`. Lean 4.31.0 documents `-t` as `--trust`: level 0 typechecks imported modules and does not trust macros. The coordinator reports 30 tests passed. This review did not re-execute them.

## Remaining issues

`verify_full.py` does not read `PROVENANCE.json` and does not check the Mathlib commit. Surviving `LEAN_PATH` entries are lake package oleans, re-typechecked at trust 0.

`passed` compares each live coordinator source with its visit hash. The snapshot hash stored in the compile record is not required to equal that visit hash.

`Audit.lean` is written after the lexical scan. It contains the requested imports and `#print axioms` lines.

`foundation-audit/compile_module.py` is a separate compiler. Its path is the vendor build, the audit build, then `E:\simplex-lean-full-20261106\build`, which contains `SimplexFull`. Those owned-module logs are trust-0 rechecks and can load prior `SimplexFull` oleans. `VERIFIED_FOUNDATION_MODULES.json` already leaves the integrated source-only closure to the coordinator. The stored staging crosscheck `parser_sha256` is the previous `source_audit.py`, not the current file `494835267f09fc99b40a4b2db8e4e72cd4b210fbaa99de3d4c6e01288114cf9e`.

The vendor probe prints axioms for its nine target theorems. The 52 compile records do not each print every declaration.

The general singular centered product for arbitrary discontinuous log-concave factors remains unproved. The tilted family used for `Q₁ ≥ 1` is the theorem above. Correlations outside `IsWeakSimplexCov` are outside Theorem global and remain inside the rectangle lemma when they are PSD with unit diagonal. The `m(m-1)` statements start at `m ≥ 2`.

No source-versus-certificate hash mismatch turned up for the three named modules or for `GlobalComparison.lean`. Local `foundations/SimplexFull/GlobalFoundations*.lean` files are outside this certificate.
