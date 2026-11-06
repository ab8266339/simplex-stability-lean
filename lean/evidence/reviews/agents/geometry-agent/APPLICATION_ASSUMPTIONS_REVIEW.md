# Independent application-assumption review

Reviewed read-only against paper/paper_main.tex Theorem 5, Corollary 6 and Theorem 7.
No source outside geometry-agent was changed.

## Verdict
No mathematical or assumption mismatch was found in the final global application
assembly. The Gaussian representation of mean width is complete. The separate
identification with normalized spherical surface average is being supplied by
the width task and is not certified by this report.

## Frozen sources reviewed
- scalar-agent/SimplexFull/GlobalApplicationsCore.lean
  eaea2f3d3637c93d709f6a8e5ec4ceb79bacc8316c30c7bcf071c8a8b1176dce
- scalar-agent/SimplexFull/GlobalApplicationsMeanWidth.lean
  c7832df1611d0025c0fe9238b2d519f5baee954ac1bd91fc5c047a7687ce3efb
- scalar-agent/SimplexFull/GlobalApplicationsDecoder.lean
  8a326dd79d126ee5d3ea89e00098a748f17b0edc5c08cd4829c96697990546cb
- scalar-agent/SimplexFull/GlobalCentroidDecoderEnergy.lean
  31f6b4a5d89663d954a451a7057e30156a30e65612519c30454fbb7d3e8c2e8d

## Checks
1. Core comparison is the actual PSD Gaussian orthant law, with the admissible
   weak-simplex rank-one domination condition. Singular matrices are included.
   The unit Gaussian maximum bounds and actual unit decoder centroid bounds are
   now instantiated, not remaining hypotheses.
2. Constants match the manuscript: bg=kappa*alpha^(3/2), bs=eta/sqrt(alpha),
   cg=W*kappa*alpha^2, cs=W*eta, and
   cP=(alpha/cg + 1/(m*cs))^-1. The factor m is present only in the decoder
   Procrustes denominator, while the ball-width denominator has 1/bs.
3. Decoder and Gram claims apply to m>=2 and lambda>0. NeZero m is a redundant
   typeclass under m>=2, not a stronger mathematical assumption.
4. Procrustes uses the actual orthogonal-isometry infimum. The geometric chain
   proves attainment and its Gram formula. An actual reference V with
   gram V=simplexGram is supplied, as in the manuscript. Omitting an explicit
   d>=m-1 hypothesis in that theorem causes no weakening: existence of such V
   already entails the necessary dimension.
5. Rank penalty uses Matrix.rank G <= rankBound, with arbitrary realization
   dimension; it is not merely an ambient-d specialization. The positivity
   corollary retains 1<=rankBound<m-1.
6. Unused-energy claims concern WeakSimplex.decoderSuccess and bayesValue of
   original nonunit signals. The equal-unit-energy decoding formula is used only
   for the lifted unit configuration and the regular reference. The mathematical
   orthogonal-coordinate lift does not impose an extra channel-use assumption.
   Original and reference ambient dimensions are independent.
7. Mean-width transfer uses arbitrary ball configurations and original ambient
   gaussianRadiusMean d. The added noise coordinates never replace this radial
   factor by the larger lifted dimension. The original d>=m-1 assumption implies
   d>=1, proving that radial expectation is positive.
8. The unnormalized unused-energy bound follows directly from the second
   ball_gaussian_max_bounds inequality, by dropping the nonnegative centroid term.
9. The actual finite convex hull support=max-coordinate bridge is supplied
   separately by geometry-agent/SimplexFull/GlobalFiniteHullSupport.lean; it is
   valid for every ambient dimension and every nonempty finite configuration.
   Spherical surface-measure normalization remains a distinct width-task proof.

## Scope
This is an independent mathematical and interface review of the application
assembly, not a replacement for root's fresh full source build and axiom audit.
