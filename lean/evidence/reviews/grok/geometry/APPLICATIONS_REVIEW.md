# Application discharge audit

Follow-up to the frozen 14-module review. That review is unchanged. This note covers only the five scalar-agent modules named below, their success logs, and the finite-hull support file. Nothing was recompiled.

Sources:

- scalar-agent/SimplexFull/GlobalApplicationsCore.lean
- scalar-agent/SimplexFull/GlobalApplicationsMeanWidth.lean
- scalar-agent/SimplexFull/GlobalApplicationsDecoder.lean
- scalar-agent/SimplexFull/GlobalCentroidDecoderGram.lean
- scalar-agent/SimplexFull/GlobalCentroidDecoderEnergy.lean
- geometry-agent/SimplexFull/GlobalFiniteHullSupport.lean

Paper formulas are eq:codeconstants and eq:meanconstants in snapshot/paper_source/paper_main.tex, with kappa = kappa_{m,[0,1]} and eta from eq:eta.

## Premises

The finished application theorems do not take a targetCDF hypothesis or an hunit hypothesis. The two predicates left open by the earlier review are proved and then passed in:

- unitGaussianMaxBounds, for 2 <= m, is Geometry.UnitGaussianMaxBounds at meanGramConstant and centroidMeanConstant.
- unitDecoderCentroidBound, for 2 <= m and 0 < lam, is Geometry.UnitDecoderCentroidBound at centroidDecoderConstant.

Latest stdout dependency lists are propext, Classical.choice, and Quot.sound. stderr is empty. Current source SHA-256 values match the success logs, and each exit code is 0. GlobalApplicationsCore prints one unused-section-variable warning.

## Constants

Let alpha = (m-1)/m, mu = lam / sqrt(alpha), and

    W(m,lam) = exp(-mu^2/2) * (exp(mu) - 1) / m.

This is expWindowWeight m (lam / sqrt(alpha)), the paper weight W_{m,lam}.

kappa is paperKappa m 0 1. Its factors K and kappa match the paper display: L0 = m log Phi(u), beta = Psi^{-1}(L0), A0 = Psi'(beta), B0 = v + sqrt(-2 L0/m) + sqrt(-2 alpha L0), ell = beta/sqrt(2), T = sqrt(2) B0 + ell, b(t) = 2 Phi(t) - 1, and

    K = exp(-m A0 beta) ell^2 exp(-4 T^2/3) b(ell)^(2m-2) / (4 pi m (m-1)),
    kappa = Phi(u)^m K / (1 + sqrt(1 + K m (m-1))),

evaluated at u = 0 and v = 1.

r(c) = phi(c)/Phi(c) is q(c), and H(c) = c + r(c) is h(c). M0 is the maximum of -Psi'' on [H(0)/2, 3 H(1)/2]. Then

    tau = min( H(0)/(2 alpha m), r(1)/(1 + M0 alpha m) ),
    eta = 2^(-m) * alpha * r(1) * tau / 2.

The packaged constants are:

    cg = gramDecoderConstant m lam = W(m,lam) * kappa * alpha^2
    cs = centroidDecoderConstant m lam = W(m,lam) * eta
    cP = procrustesDecoderConstant m lam
       = (alpha/cg + 1/(m*cs))^(-1)
    bg = meanGramConstant m = kappa * alpha^2 / sqrt(alpha)
       = kappa * alpha^(3/2)
    bs = centroidMeanConstant m = eta / sqrt(alpha)

The last two identifications are meanGramConstant_eq_sqrt and the definition of centroidMeanConstant. Those definition files are byte-identical in coordinator/SimplexFull and kernel-global/SimplexFull. scalar-agent currently has the oleans for GlobalApplicationConstants, GlobalUnitMeanBounds, and GlobalComparisonDefs, and does not have those three .lean files. The formula text above was read from the coordinator copy. The application proofs use these names, and the recorded compiles loaded the oleans.

## Decoder

decodingSuccess_gram_penalty, for 2 <= m, a correlation matrix G, and 0 < lam:

    cg * ||G - G_Delta||_F^2 <= Pc(G_Delta, lam) - Pc(G, lam).

The comparison on [0,1] is thresholdDeficit_ge_kappa, which calls the orthant comparison at thresholds 0 and 1. No external CDF bound is an argument.

decodingSuccess_procrustes_penalty, for 2 <= m, unit signals X, a simplex reference V in the same dimension, and 0 < lam:

    cP * procrustesSq X V <= Pc(G_Delta, lam) - Pc(gram X, lam).

The proof inserts global_procrustesSq_le_gram_centroid and keeps the factor 1/m on the centroid term, which is the paper combination for cP.

Rank and ambient dimension stay separate:

- decodingSuccess_rank_penalty takes a correlation matrix of rank at most rankBound, with 1 <= rankBound. The realization dimension is not an argument. It multiplies cg by the Gram bound m^2 (1/rankBound - 1/(m-1)).
- decodingSuccess_rank_deficiency adds 1 <= rankBound < m-1 and records that the same quantity is positive.
- decodingSuccess_ambient_penalty is the rank theorem applied to a unit configuration in dimension d, using rank(gram X) <= d.

## Mean width

ball_gaussian_max_bounds, for 2 <= m, a ball configuration, and a simplex Gram in the same dimension, gives the unnormalized lift bounds with bg and bs. There is no hunit argument.

ball_mean_width adds m-1 <= d and concludes

    (2 / gaussianRadiusMean d) * (alpha/bg + 1/bs)^(-1) * procrustesSq X V
      <= normalizedGaussianWidth V - normalizedGaussianWidth X

and

    (2 / gaussianRadiusMean d) * bs * sum_i (1 - ||X i||^2)
      <= normalizedGaussianWidth V - normalizedGaussianWidth X.

gaussianRadiusMean d is the integral of ||g|| against standard Gaussian measure on R^d. The certificate VERIFIED_APPLICATIONS.json says that identification with a sphere surface integral is outside its scope. That sphere surface-average identity remains a separate active task.

The paper also states the unnormalized bound bs * sum_i (1 - ||y_i||^2). ball_gaussian_max_bounds has the stronger form bs * (||sum X i||^2 + sum energyDeficit) against the Gaussian-maximum gap. A separate name for the centroid-free unnormalized sentence is not in these modules.

## Unused energy

unitDecoderCentroidBound removes the predicate from the ball decoder. For 2 <= m, 0 < lam, a ball configuration in dimension d, and a simplex reference in an independent dimension refdim:

- ball_decoder_centroid_energy bounds ||sum X i||^2 + sum (1 - ||X i||^2) by cs times the operational decoder gap.
- ball_decoder_unused_energy drops the centroid and bounds sum (1 - ||X i||^2).
- ball_bayes_unused_energy is the same bound for bayesValue.

The original non-unit configuration is handled by the orthogonal lift already audited. These three theorems have no hunit argument.

## Finite convex hull

geometry-agent/SimplexFull/GlobalFiniteHullSupport.lean proves that the support function of convexHull of the vertex set is the attained score maximum:

    realSupport (convexHull (range X)) g = maxCoord (scoreMap X g).

The Gaussian integral of that support equals configGaussianMax X. The latest log matches the current source hash, exits 0, has empty stderr, and prints the same three dependency names. This identifies the Gaussian mean width of the finite convex hull with the configuration formula. It does not identify that formula with spherical surface measure.

## Hashes

| File | SHA-256 | Exit |
| --- | --- | --- |
| GlobalApplicationsCore.lean | eaea2f3d3637c93d709f6a8e5ec4ceb79bacc8316c30c7bcf071c8a8b1176dce | 0 |
| GlobalApplicationsMeanWidth.lean | c7832df1611d0025c0fe9238b2d519f5baee954ac1bd91fc5c047a7687ce3efb | 0 |
| GlobalApplicationsDecoder.lean | 8a326dd79d126ee5d3ea89e00098a748f17b0edc5c08cd4829c96697990546cb | 0 |
| GlobalCentroidDecoderGram.lean | f4437f741257ebbea69f0ba238913e61f90c1db05ac8f56205a28f4a29efad26 | 0 |
| GlobalCentroidDecoderEnergy.lean | 31f6b4a5d89663d954a451a7057e30156a30e65612519c30454fbb7d3e8c2e8d | 0 |
| GlobalFiniteHullSupport.lean | 5e3f2015b20bedff498e868d6978fd9d04febe0904e438f39721751c779d0a08 | 0 |

Log bases are the 20261106-172833, 172918, 173106, 172006, 172248, and 173416 certificates. Lean command lines record toolchain v4.31.0.
