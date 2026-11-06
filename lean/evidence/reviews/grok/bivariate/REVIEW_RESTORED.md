# Restored audit: quantitative symmetric rectangle

No source was rewritten. Current bytes of every audited file match the recorded exit-0 compilation. Printed axioms on the checked theorems are only `propext`, `Classical.choice`, and `Quot.sound`. No `sorry`, `admit`, new axiom, `unsafe`, or `native_decide` appears in these modules. No counterexample to the stated bounds was found.

## Verified statement

`SimplexFull.GlobalRectangle.symmetricRectangle_gap` is the paper’s rectangle lemma. For `2 ≤ m`, a positive-semidefinite unit-diagonal `R`, and radii `r i ∈ [ell, T]` with `0 < ell`,

```text
rectangleK m ell T * ‖R - I‖_F^2
  ≤ P(|V_i| ≤ r i for all i) - ∏ P(|Z| ≤ r i)
```

with the actual centered Gaussian `multivariateGaussian 0 R` on `symmetricRectangle`, and

```text
rectangleK = ell^2 * exp(-4 T^2 / 3) * (2 Phi ell - 1)^(m - 2)
             / (4 π m (m - 1)).
```

`slab_toReal_eq` identifies `2 Phi ell - 1` with the standard slab. `rectangleK_pos` holds for `2 ≤ m` and `0 < ell`.

The bivariate piece is `pair_rectangle_gap`: the same hypotheses on a `2 × 2` correlation matrix give

```text
ell^2 / (4 π) * exp(-4 T^2 / 3) * (R 0 1)^2
  ≤ P(|X| ≤ r 0, |Y| ≤ r 1) - P(|Z| ≤ r 0) P(|Z| ≤ r 1).
```

This includes both singular endpoints `|R 0 1| = 1`.

## Checks

Conditional law. `variance_pair_residual` gives `Var(x 0 - (R 0 1) x 1) = 1 - (R 0 1)^2`. `pair_rectangle_eq_conditional` writes the rectangle as the Gaussian integral over the second coordinate of that residual law. For `|ρ| < 1`, `shifted_conditional_mass` scales `gaussianReal 0 1` by `sqrt(1-ρ^2)` using `gaussianReal_map_const_mul`, whose variance factor is `c^2`. `pair_probability_eq_rectangleIntegral` equates the probability with `rectangleIntegral`. At `|ρ| = 1`, `pair_endpoint_mass` uses the Dirac residual and obtains `P(|Z| ≤ min(r 0, r 1))` for both signs.

Plackett derivative. For `|r| < 1`, `hasDerivAt_rectangleIntegral` differentiates the compact integral of `conditional` by `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`. The neighborhood `(r±1)/2` stays inside `(-1, 1)`, and the `ρ`-derivative is bounded by continuity on a compact rectangle. `integral_conditionalD_eq_corners` integrates the spatial derivative of `corner`. `corners_eq_rate` turns the four corners into

```text
2 / (π sqrt(1-r^2)) * exp(-(a^2+b^2)/(2(1-r^2))) * sinh(r a b / (1-r^2)).
```

The prefactor matches `phi(z) phi(t) / sqrt(1-r^2)` and the identity `2(e^u - e^{-u}) / (2π s) = 2 sinh(u) / (π s)`.

Constant `1/(4π)`. On `[0, 1/2]`, `plackettRate_lower` uses `sinh u ≥ u`, `1-r^2 ≥ 3/4`, and `(a^2+b^2)/(2(1-r^2)) ≤ 4 T^2/3`. At `r = 1/2` and `a = b = T` the exponent is exactly `4 T^2/3`. FTC gives a gap of at least `(ell^2/π) exp(-4 T^2/3) r^2` on `[0, 1/2]`. Monotonicity on `[0, 1)` and evenness reduce every `|r| < 1` to `(ell^2/(4π)) exp r^2`. At `|r| = 1` the same constant is the value of that bound at `r = 1/2`, and `rectangleIntegral (1/2)` is at most the minimum slab because the rectangle sits inside it.

Dimension and Frobenius factor. The dimension variable is `m`, with `m = 2` as the peel base: `tailProd = 1` and the denominator is `2`. `exists_perm_pair` sends a maximizing off-diagonal pair to coordinates `0, 1`. `exists_pair_sq_ge_average` proves `‖R-I‖_F^2 ≤ m(m-1) max_{i≠j} (R i j)^2` after the unit diagonal kills the diagonal of `R-I`. Equality holds when every off-diagonal square equals that maximum. `block_peel` supplies `P(rect) ≥ P(pair) * ∏_{k≥2} P(|Z|≤r k)` for singular PSD matrices, and `tailProd_lower_bound` replaces the `m-2` tail slabs by `b(ell)`.

`ell` and `T`. The gap theorems assume `0 < ell` and `ell ≤ r i ≤ T` for every `i`. Then `T ≥ ell > 0`. A larger uniform `T` only weakens the exponential, which remains a valid lower bound.

## Not a gap

The probability export is the paper’s `1/(4π)` form. The stronger integral bound with factor `ell^2/π` on `[0, 1/2]` is `rectangleIntegral_small_gap`. The endpoint proof does not take a limit of the singular density; `sd` vanishes there, and the Dirac regression is used instead.

`GlobalRectangleBound` imports coordinator-owned `GlobalBivariateEndpoint`. The coordinator copy of `GlobalBivariateProbability` is byte-identical to the foundation-audit file. This audit did not launch a fresh rebuild.
