# Review restored

Construction is stopped. This review reads the nine named sources and does not rewrite them. Hashes below were recomputed in this session and match the recorded Lean 4.31.0 logs (`exit_code` 0). Those logs’ `#print axioms` lines are `propext`, `Classical.choice`, and `Quot.sound`. This session did not recompile. The nine sources, and the rest of `coordinator/SimplexFull` and `scalar-agent/SimplexFull`, contain no `sorry`, `admit`, `unsafe`, or `native_decide`.

The four scalar-agent files are byte-identical to the coordinator copies of the same names. `GlobalTailMean` and `GlobalGaussianNormalization` exist as sources only under `coordinator/SimplexFull`; the scalar modules import them.

Paper target: `snapshot/paper_source/paper_main.tex`, normalization and `Pc` (lines 57–86), centroid and decoding (370–504), mean width (506–557).

## Coverage

Expectation equality. `integral_sub_eq_integral_cdf_gap` states, for one measurable integrable real function on two probability spaces,

`(∫ f ∂ν) − (∫ f ∂μ) = ∫ (μ.real {f ≤ t} − ν.real {f ≤ t})`.

The integrand is the centered kernel `1_{t < f(x)} − 1_{t < 0}`. Each section integrates to `f(x)`, the product is integrable because the sectionwise `L¹` norm integrates to `‖f‖`, and Fubini is `integral_integral_swap` under `[SFinite]`. The `t < 0` constants cancel, so the proof integrates the CDF difference and leaves `F` and `1−F` unsplit on `ℝ`. `integrable_cdf_gap` is that integrability theorem. Orientation agrees with the manuscript: the measure with the larger closed-sublevel function has the smaller expectation.

`gaussianMaxMean_gap_eq_integral` is that identity for `maxCoord` under `multivariateGaussian 0`. With `cdf_gap_eq_thresholdDeficit`, the integrand for `(S, R) = (1, R)` is `thresholdDeficit R = orthantCDF R − Φ^m`, i.e. `D_R`. `identity_orthantCDF` proves `orthantCDF 1 c = (Phi c)^m` by the product of standard normal slabs. `Phi` and `WeakSimplex.normalCDF` are definitionally equal (`GlobalFoundationBridge.normalCDF_eq_Phi`).

Quantitative window. If `F_ν(f ≤ ·) ≤ F_μ(f ≤ ·)` everywhere and the gap is at least `A ≥ 0` on `[0,1]`, then `integral_difference_ge_of_cdf_gap` gives `A ≤ ∫ f ∂ν − ∫ f ∂μ`. The unit interval has real volume 1. Both domination and the numerical floor are explicit hypotheses.

MGF window. `exp_integral_difference_ge_of_cdf_gap` applies the same equality to `exp(a · f)` for `a > 0`. On the level interval `[1, exp a]`, whose length is `exp a − 1`, the sublevel `{exp(a f) ≤ t}` is `{f ≤ log t / a}` and that threshold runs through `[0,1]`. The resulting bound is `A * (exp a − 1)`. For a constant gap `A` on `[0,1]` and a nonnegative gap elsewhere, this is the same number as `a ∫_0^1 exp(a c) A dc`. `decodingSuccess_gap_ge_of_cdf` multiplies by `exp(−a²/2) / m`. The coefficient is `expWindowWeight m a = exp(−a²/2) * (exp a − 1) / m`.

Normalization, once. `gramMgf_normalization_identity` already folds `exp(λ²/(2n))` into `exp(−μ²/2)`. `decodingSuccess_normalizedCovariance` therefore states `Pc(G, λ) = Pc(R, μ)` for `μ = λ / √α` and `R = normalizedCovariance G`, under `2 ≤ m` and `IsCorrelation`. `decodingSuccess_simplex_normalized` adds `R = I` when `G = simplexGram`. The centroid decoder applies this pair once. `gaussianMaxMean_normalizedCovariance` differentiates the same identity at `0`; the chain-rule factor `1/√α` yields `gaussianMaxMean R = √α * gaussianMaxMean G`.

Centroid constant `c_s`. `centroid_penalty` and `centroid_entrySum_penalty` give `D_R(c) ≥ η ‖s‖²` on `[0,1]`, after `centroidExcess R = α * 1ᵀ G 1` cancels the `η / α` factor in `centroid_matrix_penalty`. `decodingSuccess_centroid_penalty` concludes

`centroidDecoderConstant m λ * ‖∑ x_i‖² ≤ Pc(G_Δ, λ) − Pc(G, λ)`

with `centroidDecoderConstant = expWindowWeight m μ * η`, which is the manuscript `c_s = W_{m,λ} η`.

Frobenius factor. For `2 ≤ m`, `normalizedCovariance G − 1 = α • (G − simplexGram)` and `frobSq` scales by `α²` (`global_frobSq_smul`).

Singular covariances and `m ≥ 2`. `IsWeakSimplexCov` is PSD with unit diagonal and `R − J/m` PSD, so singular admissible matrices are included. `lowerOrthant_ge_iid` is the source of `D_R ≥ 0`; it regularizes to the positive-definite case and uses unit diagonal to kill hyperplanes. `integrable_exp_mul_maxCoord` requires `PosSemidef`, so exponential theorems accept singular PSD matrices. Every theorem that divides by `√α` or rewrites `simplexGram` assumes `2 ≤ m`. `Matrix.PosSemidef.one` supplies the identity covariance.

Hypotheses that match the desired sign are written in the statements. `hdom` and `hl` are arguments of the general comparison lemmas. The centroid path discharges them by `centroid_penalty`. The κ path is not assumed inside these nine files.

## Defects

`gaussianMaxMean_gap_eq_integral` and `integrable_maxCoord_mvg` quantify over every real matrix. Mathlib defines `multivariateGaussian μ S` as Dirac at `μ` when `S` is not positive semidefinite (`multivariateGaussian_of_not_posSemidef`). The equality remains true for that Dirac measure. A caller who reads it as a Gaussian identity for a non-PSD matrix is outside the theorem’s measure.

`normalizedCovariance`, `centroidDecoderConstant`, and division by `Real.sqrt (Geometry.alpha m)` are unprotected definitions. At `m = 1`, `alpha = 0` and Lean division by zero returns `0`, so those expressions are degenerate. The theorems that use them assume `2 ≤ m`.

`integral_ge_const_of_unit_interval` takes `0 ≤ A` and never uses it. The integral of the constant over `Icc 0 1` is `A` for either sign.

## Remaining obligations

These nine files do not state the manuscript’s weighted equality

`E exp(μ max Z) − E exp(μ max X') = μ ∫_ℝ exp(μ c) D_R(c) dc`.

They prove the window lower bound `A (exp μ − 1)` that this equality produces when `D_R ≥ A` on `[0,1]` and `D_R ≥ 0` elsewhere. Adding the equality should be a new lemma on top of `integral_sub_eq_integral_cdf_gap`; the existing modules can stay as they are.

`∫ D_R` for the transformed maxima is the composite of `gaussianMaxMean_gap_eq_integral` at `(1, R)` and `cdf_gap_eq_thresholdDeficit`. It has no single name in these files.

The original-scale mean inequalities and the Gram decoding constant `c_g` are outside the nine files:

- `coordinator/SimplexFull/GlobalUnitMeanBounds.lean` (`9ffb6924…`) has `E max(G_Δ) − E max(G) = (E max I − E max R) / √α` and the centroid coefficient `η / √α`.
- `scalar-agent/SimplexFull/GlobalApplicationsCore.lean` instantiates the κ window. `meanGramConstant = κ α² / √α`, and `GlobalApplicationConstants.meanGramConstant_eq_sqrt` rewrites it as `κ α^{3/2}`. `gramDecoderConstant = expWindowWeight μ * κ * α²`, which is `c_g`, and `decodingSuccess_gram_penalty` is the corresponding `Pc` bound.
- That κ input is `GlobalComparison.orthant_linear_comparison` on `[0,1]` (`geometry-agent/SimplexFull/GlobalComparison.lean`): `paperKappa * ‖R−I‖_F² ≤ orthantMass − Φ^m`. `covarianceDefect` and `Geometry.frobSq` are the same sum of squares, and `orthantMass` is `orthantCDF`. This review did not re-audit that comparison proof.

Still outside this layer: Procrustes `c_P`, the rank corollary, the non-unit energy lift, and normalized spherical mean width.

## Source hashes (sha256)

| File | sha256 |
| --- | --- |
| `coordinator/SimplexFull/GlobalTailMean.lean` | `93521d1b8b89161ee02ac58c6bd6c1ecebd75bb7a34347aebffbe18c03dfca87` |
| `coordinator/SimplexFull/GlobalTailBounds.lean` | `ec1491f663f1e56af33e9f56c190329a31e3054380ccd8c6d8bb386a1908aa4c` |
| `coordinator/SimplexFull/GlobalGaussianCDF.lean` | `5d2d26c2785055a5e4276cd7ff38e18245a79ae7ce1c56a9d77acebffc5a48f2` |
| `coordinator/SimplexFull/GlobalGaussianNormalization.lean` | `740cf8e24c1065c88e235f16ed132bcb099a0721229af76a4eb23dd8e5ae961d` |
| `coordinator/SimplexFull/GlobalNormalizationAlgebra.lean` | `fdec58c8df02be92415629da6974c3615c3b8464267e681566e7f2b084932600` |
| `scalar-agent/SimplexFull/GlobalTailExponential.lean` | `bee72b4ddcf0564de425310aaf61f54317d4d6c40d57caeba9a28f0b5bad8fb1` |
| `scalar-agent/SimplexFull/GlobalTailExponentialGaussian.lean` | `b6253ad7fb2506038e6fa3a938451443e5c49387a5f0003a6797a4a867ecde67` |
| `scalar-agent/SimplexFull/GlobalCentroidDecoderNormalization.lean` | `f6400d6ace9844fbb1fff1f09689960b4fa2097e58e76782ec756edc4cda5c47` |
| `scalar-agent/SimplexFull/GlobalCentroidDecoder.lean` | `1def9828803b59bbb58e3f0dfe98e7be928d9232f9a82a49eb8b0c0b70a6a814` |
