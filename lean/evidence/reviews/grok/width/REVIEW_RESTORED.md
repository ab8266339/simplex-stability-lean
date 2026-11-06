# Restored review (width)

Lean 4.31.0, Mathlib `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`. Paper `snapshot/paper_source/paper_main.tex` theorem `thm:width` is unchanged. This directory has no new Lean module and no compile. Collaborator modules were not rewritten.

## Attempted work

The restored session stopped the broad mean-width development. The search that was completed located Mathlib’s polar law in `MeasureTheory/Constructions/HaarToSphere.lean`: `Measure.toSphere` and `measurePreserving_homeomorphUnitSphereProd`. `Metric.sphere` is only the underlying set. No `GlobalSphericalWidth*.lean` was written, no olean was copied, and nothing was compiled. scalar-agent owns the independent implementation in `GlobalSphereGaussian*`. At review time `scalar-agent/SimplexFull` contains no file of that name.

## Coverage already proved elsewhere

Geometry’s Gaussian-ratio stack, namespace `SimplexFull.Geometry`:

- `GlobalMeanWidthBase.lean` defines `normalizedGaussianWidth X := 2 * configGaussianMax X / gaussianRadiusMean d`, with `configGaussianMax_eq_integral` and `gaussianRadiusMean_pos` for `1 ≤ d`.
- `GlobalMeanWidthLift.lean`, `GlobalMeanWidthNoise.lean`, `GlobalMeanWidthGeometry.lean` build the orthogonal unit lift, noise monotonicity, and the Procrustes combination.
- `GlobalMeanWidth.lean` transfers those gaps onto `normalizedGaussianWidth`. The packaged statement is `ball_mean_width_of_unit_bounds` (`2 ≤ m`, `m - 1 ≤ d`, ball configuration, `gram V = simplexGram m`).
- `GlobalFiniteHullSupport.lean` defines `realSupport K g := sSup ((fun y => ⟪g, y⟫) '' K)` and proves, for `[NeZero m]` and `X : Config m d`,
  - `realSupport_convexHull_range`: `realSupport (convexHull ℝ (range X)) g = maxCoord (scoreMap X g)`
  - `integral_realSupport_convexHull_range`: the `stdGaussian` integral of that support equals `configGaussianMax X`

No `sorry`, `admit`, `axiom`, `unsafe`, or `native_decide` appears in those six sources.

## Defect

`normalizedGaussianWidth` is the Gaussian ratio. The stability theorems quantify that ratio. The paper’s `w(K)` is the normalized spherical mean width, and the proof’s last sentence invokes the polar decomposition. That identification is not a theorem in the geometry modules. `integral_realSupport_convexHull_range` integrates the support against `stdGaussian`, which is still the Gaussian side.

`ball_mean_width_of_unit_bounds` takes `UnitGaussianMaxBounds m bg bs` as an explicit hypothesis. Discharging `b_g = κ α^{3/2}` and `b_s = η/√α` is outside the sphere identity and outside this role.

## API map for scalar-agent `GlobalSphereGaussian*`

Work in scalar-agent’s own files and namespace. Import `SimplexFull.GlobalFiniteHullSupport` (which imports `GlobalMeanWidthBase`). Use the compiled oleans already produced for those modules. Do not redefine `normalizedGaussianWidth`, `realSupport`, or `configGaussianMax`.

Ambient space `E = EuclideanSpace ℝ (Fin d)`.

### Mathlib objects

- `homeomorphUnitSphereProd E : ({0}ᶜ : Set E) ≃ₜ (sphere (0:E) 1 × Ioi (0:ℝ))`. Forward map: `x ↦ (‖x‖⁻¹ • x, ‖x‖)`. Inverse: `(θ, r) ↦ r • θ.val`.
- `(volume : Measure E).toSphere : Measure (sphere (0:E) 1)`, characterized by `toSphere_apply'`.
- `measurePreserving_homeomorphUnitSphereProd`: that homeomorphism pushes `volume.comap Subtype.val` to `volume.toSphere.prod (volumeIoiPow (Module.finrank ℝ E - 1))`.
- `toSphere_real_apply_univ`, `toSphere_ne_zero`, and `IsFiniteMeasure` on `toSphere` for a nontrivial finite-dimensional Haar measure.
- `stdGaussian E`, `map_pi_eq_stdGaussian`, `gaussianReal_of_var_ne_zero`, `gaussianPDFReal`, `PiLp.volume_preserving_toLp`, `volume_pi`.
- `integral_fun_norm_addHaar` is only the radial special case. The identity needs the same homeomorphism applied to `realSupport (convexHull ℝ (range X)) z * ρ(‖z‖)`.

### Definitions scalar owns

For `1 ≤ d`, `volume.toSphere` is finite and has positive total mass (`finrank = d` and the unit ball is a nonempty open of positive Haar measure). Define the probability

```text
uniformSphere d :=
  ENNReal.ofReal ((volume.toSphere).real univ)⁻¹ • (volume : Measure E).toSphere
```

Define the spherical mean width from the width function, using geometry’s support:

```text
sphericalMeanWidth X :=
  ∫ θ, realSupport (convexHull ℝ (range X)) θ.val
       + realSupport (convexHull ℝ (range X)) (-θ.val)
    ∂ uniformSphere d
```

This is an integral on `volume.toSphere`. It is not an abbreviation of `normalizedGaussianWidth`.

### Theorem to prove

```text
sphericalMeanWidth_eq_normalizedGaussianWidth
  {d : ℕ} (hd : 1 ≤ d) (X : Config m d) :
  sphericalMeanWidth X = normalizedGaussianWidth X
```

Context `[NeZero m]`, because `maxCoord` and `realSupport_convexHull_range` use it. No extra hypothesis that `h(r•θ) = r h(θ)`, and no extra hypothesis that the radial integral equals `gaussianRadiusMean`.

### Lemma order

1. Product density, by induction on `n` with `measurePreserving_piFinSuccAbove` and `prod_withDensity`: `(Measure.pi fun _ : Fin n => gaussianReal 0 1)` equals volume on `Fin n → ℝ` with density `∏ i, gaussianPDF 0 1 (x i)`.
2. Push by `MeasurableEquiv.toLp 2` along `PiLp.volume_preserving_toLp`. Conclude `stdGaussian E = volume.withDensity (fun z => ENNReal.ofReal ((2*π)^(-(d:ℝ)/2) * exp(-‖z‖^2/2)))`. The coordinate calculation is `gaussianPDFReal 0 1` times `EuclideanSpace.real_norm_sq_eq`.
3. General polar integral: for integrable `f`, the integral of `f` on `E` equals the integral of `f (r • θ.val)` on `volume.toSphere.prod (volumeIoiPow (d-1))`, because `{0}` is null (`NoAtoms` for Haar on a nontrivial finite-dimensional space) and `measurePreserving_homeomorphUnitSphereProd.integral_comp`.
4. Prove scaling inside the development: `scoreMap` is linear, and `0 ≤ r` gives `maxCoord (r • v) = r * maxCoord v`. Transport to `realSupport (convexHull ℝ (range X))` by `realSupport_convexHull_range`.
5. Substitute the degree-1 support times the radial Gaussian density into step 3. `integral_prod_mul` splits off one radial integral `I`. The same `I` multiplies `(volume.toSphere).real univ` in `gaussianRadiusMean`.
6. `gaussianRadiusMean_pos` and positive finite sphere mass give `I ≠ 0`, so `∫ support ∂stdGaussian / gaussianRadiusMean d` equals the `toSphere` average of the support.
7. Negation preserves `volume` (`IsHaarMeasure.isInvInvariant_of_innerRegular`, then `measure_preimage_neg`) and preserves cones, hence preserves `volume.toSphere`. Therefore the averages of `realSupport K` and of `θ ↦ realSupport K (-θ)` agree. The width integral is twice the support average, which is `normalizedGaussianWidth X`. `integral_realSupport_convexHull_range` supplies the numerator `configGaussianMax X`.

The final statement’s only geometric input from outside Mathlib is the support identification and the already compiled Gaussian moments. Homogeneity and the radial factor are lemmas inside this chain.

## Remaining obligation

`sphericalMeanWidth_eq_normalizedGaussianWidth` is unproved. It belongs to scalar-agent’s `GlobalSphereGaussian*` line. This role does not open a second development. The unit-covariance hypothesis `UnitGaussianMaxBounds` remains open in `ball_mean_width_of_unit_bounds` and is a separate obligation.
