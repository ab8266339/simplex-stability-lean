# Theorem 2 audit (restored)

Audit only. Geometry sources were not modified. Complete modules should stay as they are.

Paper statement: `snapshot/paper_source/paper_main.tex`, Theorem `thm:global` (lines 241–248) and its proof (lines 289–368), for `m ≥ 2`, every `R ∈ A_m`, and every `c ∈ [u,v]`, singular `R` included. Lean name of that class is `WeakSimplex.IsWeakSimplexCov`: unit diagonal, `R.PosSemidef`, and `(R - (1/m) • J).PosSemidef`.

## Verdict

`geometry-agent/SimplexFull/GlobalComparison.lean` proves the paper inequality. Current source hash equals the exit-0 log below. The three closing theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`.

- `orthant_sqrt_comparison` (line 9): `(Φ(u))^m (√(1 + K defect) - 1) ≤ F_R(c) - (Φ(c))^m`
- `orthant_linear_comparison` (line 46): `κ · defect ≤ F_R(c) - (Φ(c))^m`
- `quantitative_lowerOrthant` (line 54): both, for `c ∈ Icc u v`, with `K > 0` and `κ > 0`

`F_R(c)` is `orthantMass` (Defs line 29): `multivariateGaussian 0 R` on `lowerOrthant c = {x | ∀ i, x i ≤ c}`. `defect` is `covarianceDefect` (Defs line 31): `∑ i, ∑ j, ((R - 1) i j)^2`.

## Witness compact bounds

`GlobalComparisonWitness.lean`, for an `AdaptiveWitnesses R c` with `u ≤ c ≤ v`.

| Claim | Line | Type |
|---|---|---|
| `a_i ≤ A_0` | 38 | `w.a i ≤ capA m u` |
| `β ≤ b_i` | 46 | `beta m u ≤ h (w.s i)` |
| `b_i = c + (Ra)_i` | 63 | `h (w.s i) = c + matrixMul R w.a i` |
| `½ aᵀ R a ≤ -L_0` | 54 | `qform R w.a ≤ -2 * logFloor m u` |
| `b_i ≤ B_0` | 92 | `h (w.s i) ≤ capB m u v` |

`logFloor`, `beta`, `capA`, `capB` (Defs lines 11–16) are `L_0`, `Ψ⁻¹(L_0)`, `Ψ'(β)`, and `v + √(-2 L_0/m) + √(-2 α L_0)`. Each `Ψ(b_i) ≥ L_0` is `localLogMass_ge` (`R.PosSemidef`). `Ψ'` is decreasing, so `a_i = r(s_i) ≤ A_0`. The upper endpoint uses PSD Cauchy `qform_cauchy` on `R` at the coordinate basis, then `paper_sqrt_envelope` (Witness lines 74–90): `√(-2 L_0) ≤ √(-2 L_0/m) + √(-2 α L_0)`. The resulting cap is the paper `B_0`, so `T = √2 B_0 + ℓ` is the paper `T`.

## Doubling identity

`GlobalComparisonDoubling.lean` line 8, `doubling_identity`. For measurable, nonnegative, bounded scalar factors, and any covariance matrix:

`(∫ ∏ h_i dμ)^2 - ∫ ∏ Dh_i dμ = ∫ (∫ ∏ fixedAverageFactor h_i u_i v_i dμ(v) - ∏ Dh_i(u_i)) dμ(u)`

`μ = multivariateGaussian 0 R`. `Dh` is `normalizedSelfConvolution`. `fixedAverageFactor` is `h((u+v)/√2) h((u-v)/√2)` (Rotation lines 11–13). Rotation by `-π/4` (Rotation lines 148–170) preserves `μ ⊗ μ` through `IsGaussian.map_rotation_eq_self`, singular PSD included. `doubling_lower_of_indicator` (line 80) integrates a measurable-box lower bound.

## Pointwise deficit

`GlobalComparisonFactors.lean` line 68, `tilt_gap_formula`. For `a_i ≥ 0` and `μ_i > 0`, the conditional gap equals

`(∏ μ_i⁻² exp(√2 a_i u_i)) · (μ{ |v_i| ≤ √2 b_i - u_i } - ∏ γ[-r_i, r_i])`.

The factor identity is `fixedAverageFactor_tilted`. Off the central box, `tilt_gap_nonneg` (line 80) gives a nonnegative gap for `R ≠ 1`, including nonpositive radii. The identity matrix is the separate case in `orthant_sqrt_comparison` (lines 14–22): `F_I(c) = (Φ(c))^m` and `defect = 0`.

`GlobalComparisonBox.lean`:

- line 8, `tilt_weights_lower`: on `|u_i| ≤ ℓ = β/√2`, with `0 ≤ a_i ≤ A_0` and `μ_i ∈ (0,1]`, the weight product is at least `exp(-m A_0 β)`
- line 41, `fixed_radii_bounds`: those radii lie in `[ℓ, T]`
- line 62, `central_box_mass_lower`: `P(B) ≥ b(ℓ)^m` for every correlation, singular included

## Exact K

`paperK` (Defs lines 21–25) is the paper formula, including `b(ℓ)^{2m-2}` and the denominator `4 π m (m-1)`. `paperKappa` (lines 26–28) matches `κ`.

`foundation-audit/SimplexFull/GlobalComparisonConstants.lean` line 21, `paperK_factorization`:

`paperK = exp(-m A_0 β) * rectangleK m ℓ T * b(ℓ)^m`

`rectangleK` (`foundation-audit/SimplexFull/GlobalRectangleBound.lean` line 42) is `ℓ² exp(-4 T²/3) b(ℓ)^{m-2} / (4 π m (m-1))`. `symmetricRectangle_gap` (line 48) is the paper rectangle lemma for PSD unit-diagonal matrices.

`GlobalComparisonTilt.lean` line 9, `tilt_doubling_lower`, multiplies the weight, the rectangle coefficient, and `b(ℓ)^m`. `witness_doubling_lower` (Actual lines 85–95) instantiates it at the witness bounds, so `K · defect ≤ Q_0² - Q_1` for `R ≠ 1`. `witnessQ1_ge_one` (Actual line 39) is `Q_1 ≥ 1`. `orthantMass_eq_witness` (Actual line 56) is `F_R(c) = exp(J_*) Q_0` for `R.PosSemidef`. `witnessValue_exp_lower` gives `exp(J_*) ≥ (Φ(c))^m`. The closing `nlinarith` turns `Q_0² ≥ 1 + K · defect` and `Q_0 ≥ 0` into the square-root bound, then uses `(Φ(c))^m ≥ (Φ(u))^m`. `paperKappa_defect_le_sqrt_gap` rationalizes at the proved bound `defect ≤ m(m-1)`.

## Dependencies inside the same axiom cone

These are imported and typechecked by the closing compile. They are proved inputs of the chain.

- Singular witness existence: `exists_adaptiveWitnesses_of_isWeakSimplexCov`
- Singular Esscher shift: `integral_exp_inner_sub_quadratic_mul` on `R.PosSemidef`, through `CFC.sqrt`
- Singular `Q_1 ≥ 1`: `normalizedSelfConvolution_product_ge_one` by positive-definite regularization
- Rectangle transport: `rectangle_bound_of_pair_bound` and `pair_rectangle_gap`, with the `|ρ| = 1` endpoint

## Coverage

Discharged for Theorem 2: constants, witness bounds needed for `[ℓ, T]`, doubling identity, pointwise weighted rectangle gap, nonnegativity off the box, exact `K` and `κ`, identity covariance, singular `R`, and both displayed inequalities.

The separate bounds `|q - c| ≤ √(-2 L_0/m)` and `‖w‖ ≤ √(-2 L_0/α)` are not exported lemmas. The endpoint `b_i ≤ B_0` is the bound the rectangle uses.

## Remaining obligations

None for `thm:global` under `m ≥ 2`, `IsWeakSimplexCov`, and `c ∈ [u,v]`.

Theorems after the global comparison in the paper (centroid, decoding, mean width, local coefficient) are outside this audit.

## Compile evidence

`geometry-agent/SimplexFull.GlobalComparison-20261106-172539-394652`, exit code 0, Lean 4.31.0, `-t 0`. `unchanged_during_compile` is true. Current `GlobalComparison.lean` SHA-256 equals that log: `bcd7064747863e5ca8752a8894caaf508701d4e4203000072ad132ce4b62ab97`. Import timestamps are at or before that compile. This review did not rerun Lean.

Stdout axiom lines:

- `orthant_sqrt_comparison`: `[propext, Classical.choice, Quot.sound]`
- `orthant_linear_comparison`: `[propext, Classical.choice, Quot.sound]`
- `quantitative_lowerOrthant`: `[propext, Classical.choice, Quot.sound]`
