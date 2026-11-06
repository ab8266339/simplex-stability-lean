# Final global audit recommendations

Read-only review by lean_bridge, BRJD E: only. Checkpoint 2026-11-06 17:30.
This is an integration recommendation, not the final kernel certificate.

## Current independently checked evidence

GLOBAL_LOG_INVENTORY.json scanned foundation-audit, geometry-agent, scalar-agent,
and coordinator. At 17:28:45 it found 93 current Global*.lean source copies,
representing 62 distinct modules. Every distinct module had a successful
development compile matching its current source SHA. The logs contained 190
recognized axiom reports, all within propext, Classical.choice, Quot.sound.
There were no missing requested prints, repeated reports within a module,
forbidden source constructs, or different hashes among same-name copies.
These counts are a live checkpoint; new root assemblies and the resumed Grok
spherical-width task must be incorporated before the final fresh run.

The 52-module vendor closure was independently built from source in an empty
build directory, including the bare WeakSimplexConjectureLean.lean root.
STAGING_CROSSCHECK.json and VERIFIED_FOUNDATION_MODULES.json retain that evidence
and the 11 owned foundation-module hashes. An inherited development olean
must never substitute for a final source dependency.

Pinned environment was checked again:
- Lean toolchain: leanprover/lean4:v4.31.0.
- Mathlib commit: fabf563a7c95a166b8d7b6efca11c8b4dc9d911f.

## Verifier review and issue states

The current verify_full.py recursively snapshots all three project prefixes,
compiles the dependency closure in topological order into a new build
directory, uses -j2 -t0, and performs one joint Audit import. audit_output.py
requires exactly one recognized report for every requested name, rejects
duplicate requests/reports, missing reports, unexpected names, and nonstandard
axioms. This is the appropriate final workflow.

1. Bare root olean isolation: FIXED and read back. fresh_lean_path now rejects
   paths containing any of the three project prefix directories OR bare
   .olean, .olean.private, .olean.server, or .ilean files. The 25-test log passed.
2. debug.skipKernelTC: independently read back and called; the final scanner rejects it. All current reviewed source scans already found zero uses.
3. setup_verifier.py still contains the old directory-only isolation template:
   root confirms it is scratch, will not be rerun or published. Keep it out
   of the release. Release only the updated verifier/parser/tests.
4. Cross-line import syntax and public meta import: FIXED and independently
   rechecked. Two real Lean-accepted layouts were previously missed:
   ImportLayoutProbe.lean (import followed by a newline before its module),
   and MetaImportProbe.lean (module; public meta import Lean.Meta.Basic).
   Lean 4.31 compiled both at -t0. The final parser explicitly rejects
   unsupported cross-line and modifier layouts before any body classification.
   Direct calls confirmed rejection of five such variants, acceptance of the
   ordinary supported public import, and detection of debug.skipKernelTC.
   PARSER_POSTFIX_CHECK.json records the final parser/verifier SHA and calls.
   The Lean grammar was also inspected at src/lean/Lean/Parser/Module/Syntax.lean:
   optional public, optional meta, import, optional all, module identifier.
   The final policy supports conventional one-line imports and rejects the
   other layouts; it does not silently ignore them. Current project imports
   use the supported form, so these fixes do not weaken or alter the proof.
   The separately tested ImportContinuationProbe.lean is invalid Lean syntax
   and is retained only to distinguish that case from the valid probes.
5. Record the pinned Mathlib commit alongside the already recorded Lean
   version. Prefer explicit expected-version checks in the release verifier
   or a release manifest that the verifier validates.
6. For complete hash accounting, compare each compiled snapshot source SHA
   with its initial module source_sha256 before marking passed, in addition
   to the existing end-of-run live-source unchanged check. Current matching
   development records showed no hash changes.

## Primary new audit entries

Retain the old 31 local/Taylor entries and the 9 vendor foundation entries
unchanged. Add the following exact names as meaningful new end-to-end or
semantic anchor entries, rather than counting every algebra helper.

1. SimplexFull.GlobalRectangle.symmetricRectangle_gap
   Actual PSD Gaussian rectangle, m >= 2, unit diagonal, ell > 0,
   ell <= every radius <= T. The conclusion uses the exact paper rectangleK,
   actual Gaussian mass, actual independent slab product, and square
   Frobenius entry sum. No derivative, pair-rate, nonsingularity, or
   Gaussian-comparison assumption remains.
2. SimplexFull.GlobalComparison.quantitative_lowerOrthant
   Actual IsWeakSimplexCov R, m >= 2, c in [u,v]. Includes strict positivity
   of exact K and kappa and both square-root and linear deficits. No supplied
   adaptive witness, variational maximizer, doubling property, or analytic
   hypothesis appears in the final statement.
3. SimplexFull.GlobalCentroid.centroid_matrix_penalty
   Actual admissible PSD R, m >= 2, c in [0,1]; exact eta/alpha centroid
   excess lower bound. The identity-covariance zero-defect case is discharged.
4. SimplexFull.GlobalComparison.normalizedSelfConvolution_product_ge_one
   Actual normalized tilted factors with their explicit scalar integrals and
   scalar centering. PSD regularization is proved, not an extra hypothesis.
5. SimplexFull.GlobalComparison.paperK_factorization
   Exact exponential/rectangle/box-mass factorization, including exponent 2m-2.
6. SimplexFull.GlobalComparison.paperKappa_defect_le_sqrt_gap
   Exact rationalization using the proved covarianceDefect <= m(m-1).
7. SimplexFull.GlobalScalar.M0_attained
   M0 is the maximum of the actual negative second derivative on the paper's
   compact interval, not a replacement endpoint estimate.
8. SimplexFull.Geometry.global_procrustesSq_attained
   The actual sInf over O(d) is attained; source assumptions are a reference
   with the regular simplex Gram and m >= 2.
9. SimplexFull.Geometry.global_procrustesSq_le_gram_centroid
   Actual configuration Gram/centroid and actual sInf distance; arbitrary
   vector lengths are allowed. No rank, PSD, or alignment oracle is supplied.
10. SimplexFull.Geometry.global_rank_deficiency_gap
    Actual PSD unit-diagonal Gram, rank <= d, 1 <= d < m-1. Gives the positive
    exact obstruction m^2(1/d-1/(m-1)).
11. SimplexFull.GlobalTail.gaussianMaxMean_centroid_penalty
    Actual expected maxima, actual correlation matrix, exact eta/sqrt(alpha).
12. SimplexFull.GlobalTail.decodingSuccess_centroid_penalty
    Actual unit configuration and lambda > 0; correct transformed signal
    lambda/sqrt(alpha), exact centroid decoder constant.
13. SimplexFull.GlobalTail.ball_decoder_unused_energy
    Actual operational decoderSuccess for a ball configuration; no hunit
    comparison hypothesis remains.
14. SimplexFull.GlobalTail.ball_bayes_unused_energy
    The same actual Bayes quantity, including the nonunit energy correction.

The final root assembly must ALSO add its concrete names for:
- the exact covariance/Gram decoder penalty with paper kappa instantiated;
- the final decoder-to-Procrustes stability constant c_P;
- the covariance/Gram Gaussian-maximum bound with kappa instantiated;
- the final ball mean-width/Procrustes bound and unused-energy bound;
- any operational rank-deficiency corollary claimed in the final scope.
These names were still being finalized at this checkpoint. Do not substitute
a theorem ending in _of_thresholdDeficit or _of_unit_bounds for one of these
complete claims. Those helpers explicitly have the intended comparison as
an input and therefore are not final proof entry points.

It is useful to place explicit expected-type examples for these final entries
in the final combined audit module. Merely finding a declaration by name or
printing its axioms does not by itself document its mathematical scope.

## Semantics and quantifiers checked

- Phi/phi/q/h are the actual Gaussian CDF/density functions; the vendor
  definitions are linked by proved equalities.
- The rectangle proof covers rho = -1 and rho = 1 directly using the
  zero-variance conditional Gaussian law. The open-interval Plackett
  derivative is instantiated into that actual measure.
- K/kappa are the manuscript formulas; their constants depend on m,u,v,
  not the covariance or ambient dimension. c in [u,v] is the only interval
  input at the final orthant theorem.
- The centroid tau is exactly min(h(0)/(2 alpha m),
  q(1)/(1+M0 alpha m)); eta has the stated 2^-m factor. M0 is an attained
  actual compact maximum of -Psi''.
- The geometric bound uses the actual sInf over orthogonal motions.
  A regular reference Gram is supplied; no artificial scalar distance is
  substituted. The arbitrary-length geometry underlies the ball theorem.
- The width factor uses the ORIGINAL ambient dimension d, not the lifted
  dimension d+m used in the Jensen argument.
- The currently compiled normalizedGaussianWidth is defined by the exact
  displayed manuscript formula 2 E max_i <g,X_i> / E||g||. It is not presently
  a spherical-measure integral definition. Root has assigned a resumed Grok
  task to prove the independent spherical identity. Until that succeeds,
  describe the verified width quantity explicitly by this Gaussian formula;
  do not claim a separately formalized sphere polar-decomposition theorem.
- Lambda > 0 is the stated decoder range. The final theorem must not silently
  strengthen this to a bounded signal interval or m >= 4; the global bounds
  being formalized apply for m >= 2. The earlier m = 3/local switch discussion
  is a separate theorem chain.

## Release selection

Use current source hashes from the owning directories, then freeze one
authoritative copy of each module in the final package. The checkpoint found
no differing duplicate copies, but this must be rechecked after new Grok work
and final assembly. Include the two vendor root trees AND their same-level
bare .lean root file; copying only prefix directories previously caused a
downstream staging error.

The final bundle must contain fresh compilation logs, complete source closure,
all requested axiom reports, the corrected parser/tests, manifest/library pins,
and a scope statement updated to the actual successful final entry list.
Keep numerical experiments, original training data, and any unproved separate
spherical identity outside the verified claim.

Post-fix review: all concrete import-isolation/parser/skipKernelTC findings above are resolved. Items 5-6 are additional release-record/hash-accounting recommendations, not observed source or proof failures.
