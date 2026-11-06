# Restored audit: Lemma 4 centroid penalty

Role cwd is `centroid`. The old proof task is stopped. This file is a read-only audit of scalar-agent sources. No scalar-agent module was rewritten. Lean was not re-run. SHA-256 below was recomputed from the current bytes and matches the recorded `-t 0` logs.

Compiler recorded in those logs: `leanprover/lean4:v4.31.0`. Frozen Mathlib pin in `snapshot/lean/lakefile.toml` and `snapshot/lean/ENVIRONMENT.json`: `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`. This audit did not re-resolve the Mathlib checkout.

## Exact eight

`scalar-agent/SimplexFull` has these Lean files. There is no `GlobalCentroidGeometry.lean`. `Geometry` is the imported namespace (`Geometry.alpha`, `Geometry.Config`, `Geometry.gram`).

Certificate eight, in dependency order:

1. `GlobalCentroidMatrix.lean`
2. `GlobalCentroidEnergy.lean`
3. `GlobalCentroidConstants.lean`
4. `GlobalCentroidRows.lean`
5. `GlobalCentroidPotential.lean`
6. `GlobalCentroidGrowth.lean`
7. `GlobalCentroidOrthant.lean`
8. `GlobalCentroidConfig.lean`

`GlobalScalarTaylor.lean` is the scalar second-order bound those modules import. `GlobalScalarCurvature.lean` defines `M0`. `GlobalScalarPsi.lean` defines `Psi`.

Also present, and outside this eight: `GlobalCentroidDecoder.lean`, `GlobalCentroidDecoderEnergy.lean`, `GlobalCentroidDecoderGram.lean`, `GlobalCentroidDecoderNormalization.lean`.

## Paper target

`snapshot/paper_source/paper_main.tex` lines 372–404, Lemma `lem:centroid`, equation `eq:eta`.

- `R = α G + J/m` with `α = (m-1)/m`, and `A_m` is the set of unit-diagonal matrices with `R - J/m` positive semidefinite (`eq:normalization`).
- `M_0 = max_{y ∈ [H(0)/2, 3H(1)/2]} (-Ψ''(y))`.
- `τ = min{ H(0)/(2 α m), r(1)/(1 + M_0 α m) }`.
- `η = 2^{-m} (α r(1) τ) / 2`.
- For unit vectors, `c ∈ [0,1]`, `D_R(c) ≥ η ‖s_X‖²`, including singular `R`.

Frozen scalar names match the paper: `q c = phi c / Phi c`, `h c = c + q c`, `sigma c = 1 - q c * h c` (`snapshot/lean/SimplexFull/GaussianBase.lean`). `Geometry.alpha m = ((m:Real)-1)/(m:Real)`.

## What the Lean statements say

`GlobalScalar.psiCurvature y = q (hInv y) * y / sigma (hInv y)`. `deriv (deriv Psi) y = -psiCurvature y` for `y > 0`. `M0` is `psiCurvature` at a point chosen by `isCompact_Icc.exists_isMaxOn` on `Icc (h 0 / 2) (3 * h 1 / 2)`, so it is the attained maximum of `-Ψ''` on that interval.

`tau m = min (h 0 / (2 * alpha m * (m:Real))) (q 1 / (1 + M0 * alpha m * (m:Real)))`. Because `alpha m * m = m - 1`, this is the paper `τ`. The proved bounds are `tau m * (m - 1) ≤ h 0 / 2` and `tau m * (1 + M0 * (m - 1)) ≤ q 1`.

`eta m = (2:Real)⁻¹ ^ m * (alpha m * q 1 * tau m / 2)`. The orthant proof's identity `(eta m / alpha m) * centroidExcess R = 2^{-m} * g` is closed by `field_simp`.

`orthantCDF R c = (multivariateGaussian 0 R (lowerOrthant c)).toReal`. `thresholdDeficit R c = orthantCDF R c - (Phi c)^m`.

`centroid_matrix_penalty` (`2 ≤ m`, `IsWeakSimplexCov R`, `c ∈ Icc 0 1`):

`(eta m / alpha m) * centroidExcess R ≤ thresholdDeficit R c`,

where `centroidExcess R = qform R (allOnesVector m) - m`. Hypotheses are only dimension, admissible covariance, and the interval. The target inequality is not a hypothesis.

`centroid_penalty` (`2 ≤ m`, `UnitConfig X`, `c ∈ Icc 0 1`), ambient dimension `d` arbitrary:

`eta m * ‖∑ i, X i‖² ≤ thresholdDeficit (normalizedCovariance (gram X)) c`.

`normalizedCovariance G = alpha m • G + (m:Real)⁻¹ • onesMatrix m`, which is `α G + J/m`. `centroidExcess` of that matrix equals `alpha m * ‖∑ i, X i‖²`.

## Checks

PSD variational gain. `adaptive_value_centroid_gain` is derived. A real `AdaptiveWitnesses` value is at least the trial value (`adaptive_value_ge_centroid_trial`) by the concave supporting line of `Psi` and `centroid_energy_lower`. The energy bound is `qform` positivity of `R - J/m` on `a - t • 1`, with the square `(⟨1, a⟩ - m r)²`. Row squares use the PSD discriminant Cauchy form on the centered matrix: `∑ (rowDisplacement R i)² ≤ (m - 1) * centroidExcess R`. Taylor plus `tau_curvature_le` produces the coefficient `q 1 * tau m / 2`. No inverse appears in Matrix, Energy, Rows, Potential, Growth, Orthant, Config, or Taylor.

Covariance `I`. `centroidExcess (1 : Matrix (Fin m) (Fin m) Real) = 0`. The `R = 1` branch substitutes that identity and uses `thresholdDeficit_nonneg`, which is `WeakSimplex.lowerOrthant_ge_iid` applied to the same Gaussian measure. The regular simplex normalizes to this matrix and has `s_X = 0`, so the paper inequality is the same nonnegativity.

`m = 2`. Every quantitative lemma assumes `2 ≤ m`. At `m = 2`, `alpha = 1/2` and the row factor is `m - 1 = 1`. Denominators use `alpha m * m = 1`, which is positive. There is no division by `m - 2`.

Singular matrices. `IsWeakSimplexCov` is unit diagonal, `R.PosSemidef`, and `(R - (1/(m:Real)) • allOnesMatrix m).PosSemidef`. For `R ≠ 1` the proof calls `exists_adaptiveWitnesses_of_isWeakSimplexCov` (stated for every admissible covariance, singular included) and `exp_adaptive_value_le_orthant_of_ne_one`. That orthant theorem is `exp(adaptiveValue w) ≤ orthantCDF R c` via the tilted half-line identity and `centeredProduct_gt`. The `change` in `centroid_matrix_penalty` typechecks, so `adaptiveValue` matches that exponential bound. `qform_rankOne_dom` uses the quadratic form of `R - J/m`.

Actual CDF and the final numerical step. The deficit subtracts `(Phi c)^m` from the multivariate Gaussian orthant mass. `Phi 0 = 1/2` is `Phi_add_Phi_neg`. `exp(g) ≥ 1 + g` is `Real.add_one_le_exp`. `(Phi c)^m ≥ 2^{-m}` uses monotonicity of `Phi` on `[0,1]`.

`GlobalScalarTaylor`. `Psi_taylor_lower` is the second-order lower bound on `curvatureInterval` from convexity of `Psi y + M0 * y^2 / 2`, using `M0 - psiCurvature ≥ 0`. `centroid_scalar_taylor` applies it at `h c + z` for `c ∈ [0,1]` and `|z| ≤ h 0 / 2`.

Forbidden tokens. A search of scalar-agent `GlobalCentroid*.lean` and `GlobalScalar*.lean` found no `sorry`, `admit`, `axiom`, `unsafe`, `native_decide`, or `opaque`.

Axiom prints in the hash-matched logs are exactly `[propext, Classical.choice, Quot.sound]` for `centroid_matrix_penalty`, `centroid_penalty`, `adaptive_value_centroid_gain`, `sum_rowDisplacement_sq_le`, `centroid_energy_lower`, `Psi_taylor_lower`, `centroid_scalar_taylor`, `M0_pos`, and `hasDerivAt_Psi`. `Classical.choice` is the standard axiom used by the attained maximum. Earlier logs from discarded drafts named `sorryAx`. Those logs do not match the current hashes. The current entrypoint logs do not name `sorryAx`.

## O(ρ^6) scope

The sixth-order statement is local. `paper_main.tex` lines 1163–1170 and `sections/new_results.tex` theorem `thm:normal-taylor`: for fixed `m ≥ 3` and `λ` in the strict-normal gap, there exist `C, r > 0` such that the small-shell deficit equals the quartic polynomial plus a remainder bounded by `C |ρ|^6` for `|ρ| < r`. Odd terms vanish. The radius depends on `m` and `λ`. The same paragraph says that Lean coverage of the transition, strict-normal optimizer, and remainder does not include the global constants.

Frozen Lean agrees. `snapshot/lean/SimplexFull/EvenTaylor.lean` `evenTaylor_bound` is an `|rho| < r` bound. `TaylorShell.lean` `UniformTaylorNormalShell` quantifies `0 < rho < rho0` on the strict-normal chart `normalConfig`, uniformly in the embedding dimension.

The eight centroid modules and `GlobalScalarTaylor` contain no `rho` claim. Their interval is `c ∈ [0,1]` for every `m ≥ 2`, which is Lemma 4. They do not extend the small-shell remainder to all `ρ`, to `m = 2`, or to arbitrary configurations.

Decoder statements, read only for scope, feed `decodingSuccess (simplexGram) λ - decodingSuccess (gram X) λ` by `centroidDecoderConstant m λ * ‖∑ i, X i‖²`. That constant is the manuscript weight times `eta`, the second display of `thm:code` (`δ_λ(G) ≥ c_s ‖∑ x_i‖²`). They contain no `ρ^6` hypothesis. The Frobenius display `δ_λ(G) ≥ c_g ‖G - G_Δ‖_F²` and the Procrustes constant `c_P` stay outside this certificate. Decoder proof bodies were not line-audited.

## Diagnostics

Hash-matched logs warn that `ring` is unused after `field_simp` in `GlobalCentroidRows.lean` lines 37 and 46, and `GlobalCentroidOrthant.lean` line 77. The goals are closed. Exit code of each matched log is 0. This is not a mathematical defect.

`centroid/SimplexFull/GlobalCentroidScalar.lean` is a leftover of the stopped proof task. It is not part of the scalar-agent certificate.

## Hashes

Recomputed SHA-256. Each matches the log named beside it. Olean hashes were recomputed and match those logs.

| Source | SHA-256 | Matched log |
| --- | --- | --- |
| `GlobalCentroidMatrix.lean` | `e42631143441186b552ddb007129af84c962e417fc61190a8e13550c4373a9dc` | `SimplexFull.GlobalCentroidMatrix-20261106-162846-445981` |
| `GlobalCentroidEnergy.lean` | `e70a71e282009cc29c317ec062f417d3b310bec41f6fbade1c5200b819ffbeb4` | `SimplexFull.GlobalCentroidEnergy-20261106-162627-798150` |
| `GlobalCentroidConstants.lean` | `cc4b6eb89aa9a14e647d6c096b139745020e877d7890fe8aca383cc8403ab505` | `SimplexFull.GlobalCentroidConstants-20261106-162746-582756` |
| `GlobalCentroidRows.lean` | `55906b0fec4b2dc97d19c730b6181aa6c49d284f7ee65caf864ceded2cffd3c6` | `SimplexFull.GlobalCentroidRows-20261106-163416-723206` |
| `GlobalCentroidPotential.lean` | `bcefbf671069d4fc5a33a29beabbc6ca5bba73ec46620e0f5b90d6ff77142382` | `SimplexFull.GlobalCentroidPotential-20261106-163545-986384` |
| `GlobalCentroidGrowth.lean` | `c12885577096bf049e88612b9b25eb3dea92715fa50ba6f6f1d21722ce1e8ca9` | `SimplexFull.GlobalCentroidGrowth-20261106-165658-567015` |
| `GlobalCentroidOrthant.lean` | `fea1a2497f2d14688af053875dd4b5da9cd75c556cb9f9eddb2952285e7900da` | `SimplexFull.GlobalCentroidOrthant-20261106-170332-831296` |
| `GlobalCentroidConfig.lean` | `897ad4d73646cb002fa9721d010a79352d903baaedbd73dbe0ab8f231f4092cb` | `SimplexFull.GlobalCentroidConfig-20261106-170708-471903` |
| `GlobalScalarTaylor.lean` | `7ddc7a13a5ed04917417f8dd47fe7f7dbdce4c3acd11d2a1b731e99bf83f879d` | `SimplexFull.GlobalScalarTaylor-20261106-160516-997959` |
| `GlobalScalarCurvature.lean` | `5b6b2c7b06c8c22860b2281030310d1f015141ccb40f8b230946ddea0c26c6b3` | `SimplexFull.GlobalScalarCurvature-20261106-155754-729617` |
| `GlobalScalarPsi.lean` | `5ac00effd8cbfd5cadd6c3c8842ae276b6c814b1399b5caf95e36a86db02fd2e` | `SimplexFull.GlobalScalarPsi-20261106-155234-104442` |

## Remaining obligations

- Leave the eight modules, `GlobalScalarTaylor`, `GlobalScalarCurvature`, and `GlobalScalarPsi` unchanged. Reviewers should not rewrite them.
- Leave `centroid/SimplexFull/GlobalCentroidScalar.lean` untouched. It is not the certificate.
- The `c_g` Gram-defect display and the `c_P` Procrustes bound of `thm:code` are still outside this certificate.
- The `O(ρ^6)` theorem stays the frozen local statement (`m ≥ 3`, `|ρ| < r`, strict-normal chart).
- Decoder modules were checked at statement level for that scope boundary. Their proofs were not line-audited here.
- Dependency sources (`GlobalWitnessOrthantBound`, `SingularWitnesses`, `lowerOrthant_ge_iid`) were read for their statements. Their oleans were not rehashed. The entrypoint axiom prints are the transitive check, and only for the hashes above.
- This audit did not re-execute Lean.
