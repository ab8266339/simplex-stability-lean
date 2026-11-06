# Sphere final review

Audit of scalar-agent `SimplexFull/GlobalSphereGaussianPolar.lean`, `GlobalSphereGaussian.lean`, `GlobalSphereGaussianWidth.lean`, and `GlobalSphereGaussianSymmetry.lean`. Namespace `SimplexFull.SphereGaussian`. Lean 4.31.0. Each latest log is `lean -j 2 -t 0`, exit code 0, and the log `source_sha256` matches the file on disk. Every `#print axioms` line in those logs is `propext`, `Classical.choice`, `Quot.sound`.

## Verdict

The missing spherical identification is proved for a finite configuration in its own ambient dimension. `normalizedSphereMeasure d` is the probability normalization of Mathlib `volume.toSphere` on `Metric.sphere (0 : EuclideanSpace Real (Fin d)) 1`. `meanWidth (convexHull Real (range X))` equals `Geometry.normalizedGaussianWidth X` for `[NeZero d]`. `ball_mean_width` transports the stability inequality onto that spherical width. `widthIntegral` is the average of `h(u) + h(-u)`, and it equals `meanWidth` on the same convex hull.

## Measure and dimension

`Space d` is `EuclideanSpace Real (Fin d)`. `Sphere d` is `Metric.sphere (0 : Space d) 1`.

```text
normalizedSphereMeasure d :=
  ((volume : Measure (Space d)).toSphere univ)^{-1} •
    (volume : Measure (Space d)).toSphere
```

`sphere_mass_ne_zero` uses `Measure.toSphere_ne_zero`. `sphereMass_pos` uses that fact and `measure_ne_top`. `normalizedSphereMeasure_isProbability` is `ENNReal.inv_mul_cancel` on the whole sphere. The section variable is `[NeZero d]`, which for `Nat` is `1 <= d`. `sphere_integral_eq_gaussian_ratio` calls `gaussianRadiusMean_pos` on that same bound, so the division by `Geometry.gaussianRadiusMean d` has a proved positive denominator.

`integral_polar` is the integral form of `measurePreserving_homeomorphUnitSphereProd`: the integral of `f` on `Space d` equals the integral of `f (r • u)` on `volume.toSphere.prod (Measure.volumeIoiPow (d - 1))`. The zero vector is removed by `restrict_compl_singleton`. The radial exponent is the ambient rank minus one.

## Density, homogeneity, and the ambient factor

`radialDensity d r = (Real.sqrt ((2 * Real.pi) ^ d))^{-1} * Real.exp (-(r ^ 2) / 2)`. `rho_one_radial` identifies `Covariance.rho` of the identity covariance with this radial function. `radialFirstMoment d` integrates `radialDensity d r * r` against `volumeIoiPow (d - 1)`.

`gaussian_integral_homogeneous` takes positive 1-homogeneity as its hypothesis and returns

```text
integral f d(stdGaussian) = (integral f d(volume.toSphere)) * radialFirstMoment d
```

`gaussianRadiusMean_eq_sphere_mass_mul_radial` applies this to the norm, which is homogeneous, and uses `integral_const` on the unit sphere. `sphere_integral_eq_gaussian_ratio` then divides by `sphereMass d`. The radial moment is computed in the proof. It is not a hypothesis of the final width theorem.

`finiteHullSupport_homogeneous` discharges homogeneity for the hull: `Geometry.realSupport_convexHull_range`, linearity of `scoreMap` through `map_smul`, and `maxCoord_smul_nonneg`. `meanWidth_convexHull_eq_normalizedGaussianWidth` has hypothesis `[NeZero d]` and an actual `Geometry.Config m d` only. It rewrites the sphere integral by the ratio lemma, replaces the Gaussian integral by `Geometry.integral_realSupport_convexHull_range`, and unfolds `normalizedGaussianWidth`.

`meanWidth` and `ball_mean_width` use this same `d` for the sphere and for `gaussianRadiusMean d`. The stability coefficient remains `(2 / Geometry.gaussianRadiusMean d)` times the gram and centroid constants `GlobalApplication.meanGramConstant m` and `GlobalTail.centroidMeanConstant m`. Hypotheses of `ball_mean_width`: `2 <= m`, `m - 1 <= d`, `Geometry.BallConfig X`, and `Geometry.gram V = Geometry.simplexGram m`. From `2 <= m` and `m - 1 <= d` the proof builds `NeZero d`.

## Two-sided width

`meanWidth K` is `2` times the normalized-sphere integral of `Geometry.realSupport K`. `widthIntegral K` integrates `realSupport K u + realSupport K (-u)` against the same probability. `gaussian_integral_neg_eq` uses `stdGaussian_map` of `LinearIsometryEquiv.neg` and requires `Continuous f`. `sphere_support_neg_integral` applies the ratio lemma to `x |-> realSupport (convexHull (range X)) (-x)`, whose homogeneity is `finiteHullSupport_homogeneous` after `smul_neg`. `widthIntegral_convexHull_eq_meanWidth` adds the two integrable sphere functions and uses that equality. Both sphere integrands are continuous on a compact sphere.

## Integrability default

`integral_polar`, `gaussian_integral_homogeneous`, and `sphere_integral_eq_gaussian_ratio` quantify over every `Space d -> Real`. They do not assume `Integrable`. The Bochner integral of a non-integrable function is `0`, and `integral_prod_mul` uses that same convention, so those three lemmas do not by themselves stop a `0 = 0` reading for a wild homogeneous function.

The convex-hull theorem is tied to integrable data. `integrable_finiteHullSupport_sphere` proves the sphere integrand is integrable because it is continuous and the sphere is compact. The Gaussian side is `integral_realSupport_convexHull_range`. The equality proof does not cite the sphere integrability lemma; the value travels through the general ratio lemma. On this integrand the sphere function is continuous on a probability space, so that value is the surface average.

`rho_one_radial` and `gaussian_integral_neg_eq` carry an unused `[NeZero d]` section variable. The `rho_one_radial` simp list contains an unused `Covariance.matrix_inv_one`. Both are linter warnings in the successful logs. They do not change the axiom set.

## Compile records

| module | source sha256 | olean sha256 | log |
| --- | --- | --- | --- |
| GlobalSphereGaussianPolar | `77e79f71ede3e689220c01a27f54054bb7b7e5dfe0d1b3d85cc8639d43ee3152` | `b227b4d4581c33919dc7241d131da7ba73fd981acbb9c3590c9c2ade3bf8093f` | `scalar-agent/logs/SimplexFull.GlobalSphereGaussianPolar-20261106-174908-824567` |
| GlobalSphereGaussian | `65f8fc8b1b113af2ca5a3684d8375a441b74ac42ee935dbbf9457e0cbafd73ff` | `bdcb11df8f5e8ed004af751909352b6178cc38804e3c27aac37460622ec0df62` | `scalar-agent/logs/SimplexFull.GlobalSphereGaussian-20261106-175214-261817` |
| GlobalSphereGaussianWidth | `8777146416aafb52b71735d793ab574e061096407161c0702348a847e09888cd` | `bec1b584c465dd6dd2fa8494942436b737ea613b0989f9923cae0ae55aeaa7a0` | `scalar-agent/logs/SimplexFull.GlobalSphereGaussianWidth-20261106-175330-892962` |
| GlobalSphereGaussianSymmetry | `ad2a4e52232876e559a2cdad4125cbb14da6843ac4720129c5fc476ddf48c477` | `8b05565b576d5502e35f24dbd4da91e0b95309dbd344918e15009ab70d70dcf6` | `scalar-agent/logs/SimplexFull.GlobalSphereGaussianSymmetry-20261106-175743-822741` |
