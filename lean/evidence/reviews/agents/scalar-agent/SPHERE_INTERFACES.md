# Genuine sphere integral and mean width: complete

Four modules: GlobalSphereGaussianPolar, GlobalSphereGaussian, GlobalSphereGaussianWidth, GlobalSphereGaussianSymmetry. Public namespace SimplexFull.SphereGaussian. All sources are frozen and all ten printed entrypoints passed Lean -j2 -t0 with exactly propext, Classical.choice, Quot.sound.

Sphere d is Metric.sphere (0 : EuclideanSpace Real (Fin d)) 1. normalizedSphereMeasure d is defined directly as (volume.toSphere univ) inverse scaling volume.toSphere. The probability instance is proved for d>=1 (NeZero d). It is not defined from a Gaussian ratio.

integral_polar uses the actual HaarToSphere measure-preserving homeomorphism on nonzero Euclidean vectors. gaussian_integral_homogeneous combines this with the previously verified actual standard Gaussian Lebesgue density and integral_prod_mul, separating angular support from the radial first moment. Evaluating the same identity at norm proves that the radial moment times sphere mass equals the actual Gaussian mean radius. sphere_integral_eq_gaussian_ratio then divides by this strictly positive mean radius. The only function hypothesis is positive degree-one homogeneity, not a polar formula.

For finite convex hulls, finiteHullSupport_homogeneous follows from the actual support equals finite maximum theorem. integrable_finiteHullSupport_sphere proves real surface integrability by continuity and compactness. meanWidth K is defined as twice the actual normalized surface integral of realSupport K. meanWidth_convexHull_eq_normalizedGaussianWidth identifies that independent geometric definition with the Gaussian representation.

SphereGaussian.ball_mean_width is the complete quantitative Procrustes and unused-energy conclusion with this genuine surface-integral mean width. Its hypotheses are exactly m>=2,d>=m-1,BallConfig X,gram V=simplexGram. The radial constant uses the original ambient d. No hunit, desired CDF, or polar-identity assumptions remain.

The conventional direction width is also explicit: widthIntegral K is the surface integral of hK(u)+hK(-u). Gaussian negation invariance is proved using stdGaussian_map applied to the negation linear isometry. sphere_support_neg_integral transfers it through the proved polar identity, and widthIntegral_convexHull_eq_meanWidth proves equality with twice the support average. Both support summands are genuinely integrable.

VERIFIED_SPHERE.json records four current source hashes, successful compilation evidence and ten entrypoints. All earlier local, scalar, centroid, decoder and application sources remain unchanged.
