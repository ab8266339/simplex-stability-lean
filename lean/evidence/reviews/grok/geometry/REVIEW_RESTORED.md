# Restored cross-review

Independent read of geometry-agent's frozen 14 modules. The old implementation task is stopped. No module was rewritten. Sources below are `geometry-agent/SimplexFull/`. Paper text is `snapshot/paper_source/paper_main.tex`: Theorem 5 (`thm:code`, lines 415–469), Corollary 6 (`cor:operational`, lines 474–503), Theorem 7 (`thm:width`, lines 522–557).

`procrustesSq` is `sInf` of `procrustesEnergy` over `OrthogonalMotion d`, the full linear-isometry group of Euclidean space (`snapshot/lean/SimplexFull/Procrustes.lean`). Latest compile logs for the current source hashes exit 0 under Lean v4.31.0. Each printed dependency list on those latest logs is `propext`, `Classical.choice`, `Quot.sound`. This session did not rebuild the modules. The Mathlib pin `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` was not rechecked. Older logs in `geometry-agent/` still record `sorryAx`; their sources are not the current hashes.

## Verdict

| Check | Result | Carrier |
| --- | --- | --- |
| Infimum over the orthogonal group | Proved, and attained | `global_procrustesSq_centeredRoot`, `global_procrustesSq_attained` |
| Arbitrary lengths | Proved for the geometric bound | `global_procrustesSq_le_gram_centroid` |
| Singular matrices | Proved | `global_polar_alignment`, `global_frobSq_root_sub_centering_le` |
| Rank versus ambient dimension | Proved as separate statements | `GlobalRankBound.lean` |
| Ball lift | Proved for the orthogonal lift | `orthogonalUnitLift` |
| Unequal-energy Bayes likelihood | Proved as a likelihood integral | `energyLikelihood`, `gaussianBayesValue_le_add` |

No reviewed theorem hides a premise while claiming the full paper conclusion. Analytic constants remain named hypotheses. That is the remaining work.

## Proved geometric core

Hypotheses for the equality and the final geometric bound are `2 ≤ m`, both configurations live in dimension `d`, and `gram V = simplexGram m`. There is no unit-length, invertibility, rank, or positive-semidefinite hypothesis on `X`.

- `global_procrustesSq_centeredRoot`: `procrustesSq X V = trace(gram X) + m − 2/α · trace(centeredRoot X)`. The lower bound is `le_csInf` over every orthogonal motion. The upper bound is one polar witness.
- `global_procrustesSq_attained`: some `U` has `procrustesEnergy X V U = procrustesSq X V`, including singular `X`.
- `global_polar_alignment`: a positive-semidefinite, `P`-supported square root, possibly singular, is realized by an orthogonal motion. It calls `exists_orthogonal_of_gram_eq`.
- `global_procrustesSq_decomposition`: `procrustesSq X V = ‖∑ X i‖²/m + α⁻¹ ‖centeredRoot X − P‖_F²`.
- `global_frobSq_centeredRoot_le`: for `1 ≤ m` and any `X`, the CFC root is at most as far from `P` as its square. The certificate is the trace of `(T−P)(T²+T+T)(T−P)`, so a zero eigenvalue needs no division.
- `global_frobSq_compressed_gram_sub_simplex_le`: compression by `P` contracts Frobenius norm for an arbitrary matrix.
- `global_procrustesSq_le_gram_centroid`: `procrustesSq X V ≤ α ‖gram X − simplexGram m‖_F² + ‖∑ X i‖²/m`.

This is the paper's geometric chain `d_P² = ‖s‖²/m + ∑(√λ_j − α^{-1/2})² ≤ ‖s‖²/m + α‖PGP−G_Δ‖_F² ≤ ‖s‖²/m + α‖G−G_Δ‖_F²`. Here `centeredGram = α • (P G P)` and `simplexGram = P/α`, so the CFC eigenvalues reproduce the paper's sum. The paper's scalar `(√t−√a)² ≤ (t−a)²/a` is replaced by the polynomial certificate above. The old snapshot formula `procrustesSq_sqrt`, which asks for `m ≥ 3`, unit signals, and an invertible shift, is not the theorem used here.

## Rank and ambient dimension

`global_trace_sq_le_rank_mul_trace_square` is Cauchy–Schwarz on the nonzero eigenvalues of a Hermitian matrix: `(trace G)² ≤ rank(G) · trace(G²)`.

For `2 ≤ m`, a symmetric unit-diagonal matrix, the exact identity is

`‖G−G_Δ‖_F² = trace(G²) − m²/(m−1) + 2/(m−1) · entrySum G`.

For a positive-semidefinite unit-diagonal matrix of rank at most `d ≥ 1`,

`m²(1/d − 1/(m−1)) ≤ ‖G−G_Δ‖_F²`

(`global_simplex_frobSq_lower_of_rank_le`). The matrix need not come from a configuration of dimension `d`.

Configurations are separate:

- `global_gram_rank_le_ambient`: `rank(gram X) ≤ ambient`.
- `global_config_simplex_frobSq_lower_of_rank_le`: the same numerical bound from a rank hypothesis, with ambient dimension independent of that rank.
- `global_config_simplex_frobSq_lower_of_ambient`: the bound obtained because rank is at most the ambient dimension.
- `global_rank_deficiency_gap`: when `1 ≤ d < m−1`, the coefficient is positive and the Gram gap follows. There is no ambient-dimension restriction.

Unit diagonal is required, as in the paper's unit-signal corollary. Latest `GlobalRankBound` stdout has two linter warnings (`tac1 <;> tac2`, an unused `ring`) and exit code 0.

`rank(simplexGram m) = m−1` is not proved in these 14 modules. A regular simplex in the ambient space is the hypothesis `gram V = simplexGram m`. Theorem 7's `m−1 ≤ d` is an explicit hypothesis of `ball_mean_width_of_unit_bounds`, used to obtain `1 ≤ d` for the Gaussian radius.

## Ball lift

`BallConfig` means `‖X i‖ ≤ 1`. `orthogonalUnitLift` appends a private coordinate `√(1−‖X i‖²) e_i` in dimension `d+m`.

Proved for every ball configuration: the lifted Gram is `gram X + diagonal(energyDeficit)`; the lift is a unit configuration; its centroid square is `‖∑ X i‖² + ∑(1−‖X i‖²)`; and

`‖gram X − G_Δ‖_F² = ‖gram(lift) − G_Δ‖_F² + ∑(1−‖X i‖²)²`.

`global_procrustesSq_le_lift_errors` then gives `procrustesSq X V ≤ α ‖gram(lift)−G_Δ‖_F² + ‖∑ lift i‖²` for a simplex `V` in the original dimension. The paper's mean-width proof uses this orthogonal lift and the coarser comparison `d_P² ≤ α T_g + T_s`.

Corollary 6 in the paper writes one shared extra coordinate, `q_i = √(1−‖x_i‖²)`, on the same axis. That construction is not formalized. The unused-energy inequality is obtained from the orthogonal lift instead.

## Mean width

`configGaussianMax X` is the expected largest coordinate of `N(0, gram X)`. `scoreMap` pushes standard Gaussian space noise to that law, and `scoreMap_apply` is the inner product `⟪X i, z⟫`. `normalizedGaussianWidth X = 2 · configGaussianMax X / gaussianRadiusMean d`, with `gaussianRadiusMean d = ∫ ‖z‖` over `stdGaussian` on `ℝ^d`. The factor `2/E‖g‖` is this quotient. `gaussianRadiusMean_pos` covers `1 ≤ d`.

`gaussianMaxMean_le_add` is Jensen for the finite maximum against an added centered Gaussian, through the characteristic function of the sum. `configGaussianMax_le_orthogonalUnitLift` applies it to the diagonal energy deficit.

`UnitGaussianMaxBounds m bg bs` says that every positive-semidefinite unit-diagonal Gram satisfies both

`bg ‖G−G_Δ‖_F² ≤ E max(Δ) − E max(G)` and `bs · entrySum G ≤ E max(Δ) − E max(G)`.

The module states that this predicate is an input. Under that input, `0 < bg`, `0 < bs`, `2 ≤ m`, a ball configuration, and a simplex reference in the same dimension:

- `ball_gaussian_max_procrustes_of_unit` is `(α/bg + 1/bs)⁻¹ procrustesSq X V ≤ configGaussianMax V − configGaussianMax X`.
- `ball_normalized_width_procrustes_of_unit` multiplies by `2/gaussianRadiusMean d`.
- `ball_mean_width_of_unit_bounds` packages that inequality with the normalized unused-energy bound, under the additional hypothesis `m−1 ≤ d`.

The paper's unnormalized sentence `b_s ∑(1−‖y_i‖²) ≤ E max(Δ) − E max(K)` is the centroid-free consequence of `ball_gaussian_max_bounds_of_unit`. The named unused-energy theorem is the normalized one, `ball_normalized_width_unused_energy_of_unit`.

No declaration of a proof of `UnitGaussianMaxBounds` was found in the workspace. The paper values `b_g = κ α^{3/2}` and `b_s = η/√α` are not instantiated here. `GlobalComparison*` was not part of this 14-module review; those files do not mention `gaussianMaxMean`.

## Bayes likelihood

`classLikelihood` in `vendor-staging/WeakSimplexConjectureLean/Coding/BayesValue.lean` is `exp(⟪λ code_i, y⟫ − ‖λ code_i‖²/2)`. `bayesValue` is `(1/m) ∫ max_i classLikelihood`. `decoderSuccess` is the uniform average of the Gaussian measures of the maximum-likelihood regions, and `mlDecoder_success_eq_bayesValue` identifies them for any code, with no unit-length hypothesis.

`energyLikelihood G λ i x = exp(λ x_i − λ² G_ii/2)` keeps the individual diagonal. `integral_energyLikelihood_eq_one` shows each class integrates to one against `N(0,G)`. `bayesValue_eq_gaussianBayesValue` and `decoderSuccess_eq_gaussianBayesValue` transport the foundation quantities onto this Gram form for an arbitrary configuration.

`gaussianBayesValue_le_add` adds an independent positive-semidefinite covariance and compares the likelihood integrals. `bayesValue_le_orthogonalUnitLift` and `decoderSuccess_le_orthogonalUnitLift` apply that result to `diagonal(energyDeficit)`. The original non-unit configuration is never passed to the equal-energy formula.

`decodingSuccess` in `snapshot/lean/SimplexFull/Decoder.lean` is the equal-energy expression `exp(−λ²/2)/m · ∫ exp(λ maxCoord)`. `bayesValue_eq_decodingSuccess_of_unit` uses it only for `UnitConfig` and `0 ≤ λ`.

`UnitDecoderCentroidBound m λ cs` says every positive-semidefinite unit-diagonal Gram satisfies `cs · entrySum G ≤ Pc(G_Δ,λ) − Pc(G,λ)` in that equal-energy formula. `ball_decoder_unused_energy_of_unit` and `ball_bayes_unused_energy_of_unit` conclude

`cs ∑(1−‖X i‖²) ≤ decoderSuccess(V) − decoderSuccess(X)`

and the same difference of `bayesValue`, for `2 ≤ m`, `0 < λ`, `0 ≤ cs`, a ball configuration in dimension `d`, and a simplex reference in an independent dimension `refdim`. The proof applies the predicate to the lifted unit Gram, then uses likelihood monotonicity back to `X`.

These 14 modules do not prove `UnitDecoderCentroidBound`. Elsewhere, `scalar-agent/SimplexFull/GlobalCentroidDecoder.lean` defines `centroidDecoderConstant m λ = expWindowWeight m (λ/√α) · η` and describes it as the manuscript `c_s = W η`. `GlobalCentroidDecoderGram.lean` states the predicate for that constant. This review did not audit that proof or its compile log.

## Coverage against the paper

Proved inside the 14, for the hypotheses named above:

- Theorem 5's geometric conversion, for signals of any length, once a simplex reference exists.
- Corollary 6's Gram lower bound `m²(1/d − 1/(m−1))`, both from rank and from ambient dimension.
- Theorem 7's orthogonal lift, Gaussian-maximum monotonicity, normalized factor `2/E‖g‖`, and harmonic combination, conditional on `UnitGaussianMaxBounds`.
- Corollary 6's unused-energy comparison for the operational Bayes value, conditional on `UnitDecoderCentroidBound`.

Still open relative to the paper text:

1. Discharge `UnitGaussianMaxBounds` at `b_g` and `b_s`, or at proved positive substitutes. Until then Theorem 7 is a transfer theorem.
2. Discharge `UnitDecoderCentroidBound` and compose it with `ball_bayes_unused_energy_of_unit`. The constant must be checked against `c_s = W η` by the owner of that proof.
3. Prove `δ_λ(G) ≥ c_g ‖G−G_Δ‖_F²`, `δ_λ(G) ≥ c_s ‖∑ x_i‖²`, and `δ_λ(G) ≥ c_P d_P²`. The geometric input is `global_procrustesSq_le_gram_centroid`. No Frobenius-to-decoder inequality is in these 14 modules.
4. Compose the missing `c_g` bound with `global_rank_deficiency_gap` to obtain Corollary 6's decoder rank inequality.
5. Prove `rank(simplexGram m) = m−1` if the obstruction "a realized simplex forces ambient dimension at least `m−1`" is required as its own theorem.
6. The shared-axis lift of Corollary 6 is optional. The orthogonal lift already supports the unused-energy statement under the centroid hypothesis.
7. A one-line unnormalized mean-width unused-energy corollary can be cut from `ball_gaussian_max_bounds_of_unit` by dropping the nonnegative centroid term.

## Source hashes

SHA-256 of the current `.lean` files. Each `SimplexFull.<module>.latest.json` records the same hash, `exit_code` 0, and `unchanged_during_compile: true`.

| Module | SHA-256 |
| --- | --- |
| GlobalProcrustes | `4e38bf70e0ac7396863567224fe61afcce5ab3a662f733cdf7465bc350586179` |
| GlobalProcrustesDecomp | `ad595fc62e865689218c460a0b94fda31fc596767a9b340900e9925088ca4370` |
| GlobalProcrustesBound | `bd17c96378c06ec21fb5ecb9012d4dc245a4a3cea23e35d0e4f47d118be34a68` |
| GlobalSqrtContraction | `67431f57b2795b83a16416233e5788a44c4eacd93b924a0139ef66ab174c4fc7` |
| GlobalProjectionContraction | `90f5f70b9e0ac191017f2004ec4cdcce308cd271e2e791dedeb65d6f97114606` |
| GlobalRankBound | `605ba76eab7b64dc48ee50b1a6768aa8103636fb5915d09e90e18d87852e5caf` |
| GlobalMeanWidth | `83ca63748bb2b06169458eb8ec8cb81041e322f47651ad8d837e09af50e14b28` |
| GlobalMeanWidthBase | `99a35e19c5d0bfb2953864e6ac731b43363d4167182893abd63ab945393b8040` |
| GlobalMeanWidthGeometry | `39aee2f2688245c2a920dc3e0d90478cffd0384fe4937718af161384e1cabf16` |
| GlobalMeanWidthLift | `1923834228419b1d8816fef30d64fededa2e19dbb0d8c63c3b8bee1ff2205297` |
| GlobalMeanWidthNoise | `5296f28940d5f5525c2ed8a42df475a78e8ac168d83e0cb73dd0054b03b508ea` |
| GlobalEnergy | `2fd920cae5170aaedf16ab7a9e8fa5c9b316a215810860caac43826ff92396e8` |
| GlobalEnergyBase | `814a6be3daa6785e41db744c4a2ab5ec38fafcd56edd6beb8e6f189e7d46fcfa` |
| GlobalEnergyNoise | `0bc37374ef718b6f09f32d945eb97e6fd11a914e6f259522e97cefd6c02cdb51` |
