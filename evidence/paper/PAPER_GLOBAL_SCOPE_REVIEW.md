# Paper integration and final Lean scope review

Reviewed input: global-formalization-20261106/update_global_paper.py
Reviewed script SHA-256: 3dfe13bd01d1038d911d5e4aaaaf17fae1aa348431b018f7d284d4c6398a5485
Status: mathematical scope accepted after the factor-two correction; final rendered
paper, archive hash, and combined sphere-inclusive certificate remain to be checked
after root executes the staging script. No shared source was edited.

## Findings

PG-01 — Resolved, mathematical wording
The initial added Objects paragraph identified a sphere support average with
2 E max / E norm. The actual sphere average is E max / E norm; twice that is mean
width. Root changed the text to “twice its support average (equivalently, the
average of h_K(u)+h_K(-u))”. The reviewed script contains this correction and it
matches GlobalSphereGaussian and GlobalSphereGaussianSymmetry exactly.

PG-02 — Resolved guard; final artifact still pending
The previously completed combined run 20261106-174738-700587 has 81 audit entries
and predates the four sphere modules. It cannot alone support the new spherical
scope. Root is preparing a later full certificate. The script currently asserts
sphere_verified=True; it should additionally verify that the supplied final
certificate contains at least SphereGaussian.ball_mean_width and
SphereGaussian.widthIntegral_convexHull_eq_meanWidth, and the sphere source
closure. This is a safeguard against using the earlier otherwise-passing run,
not a missing mathematical proof: VERIFIED_SPHERE.json proves all four modules
and ten selected declarations separately with the standard three axioms.

PG-03 — Resolved mapping clarity
The width row currently leads with GlobalApplication.ball_mean_width and refers
to a separate source index for sphere entries. The direct final spherical entry
is SimplexFull.SphereGaussian.ball_mean_width in GlobalSphereGaussianWidth.lean.
The conventional-width equality is
SimplexFull.SphereGaussian.widthIntegral_convexHull_eq_meanWidth in
GlobalSphereGaussianSymmetry.lean. Listing them directly would make the final
Theorem 7 correspondence immediate.

PG-04 — Resolved product wording
“The normalized self-convolution has integral at least one” should preferably say
“The product of the normalized self-convolution factors has Gaussian integral at
least one.” The actual result is Q1=integral product_i D h_i >=1. Each scalar
factor individually has standard-Gaussian integral exactly one.

## Mathematics and assumptions checked

- Original exact K and kappa: beta=Psi inverse(m log Phi u), derivative cap A0,
  the two-term B0 envelope, ell=beta/sqrt(2), T=sqrt(2)B0+ell, exponent 2m-2,
  denominator 4*pi*m*(m-1), and square-root rationalization are unchanged.
  The actual PSD adaptive-witness bounds, rectangle estimate, rotation/Fubini
  identity, Q1 bound and tilt identity are proved; no desired CDF inequality is
  retained as a final hypothesis. Singular covariance and R=I are included.
- The bivariate narrative accurately describes the actual conditional Gaussian
  law, compact-integral differentiation, derivative estimate on [0,1/2],
  evenness/monotonicity, and singular endpoint mass. The many-coordinate
  pair selection and slab factors account for m(m-1) and exponent m-2.
- Psi, M0, tau and eta are concrete, with the actual inverse, attained compact
  curvature maximum and proved Taylor lower bound. No scalar smoothness or
  target Taylor bound is assumed by the final centroid theorem.
- The CDF-to-expectation identity uses a proved centered signed-tail/Fubini
  identity. Exponential integration retains e^mu-1. Normalization gives the
  manuscript constants cg=W*kappa*alpha^2, cs=W*eta,
  cP=(alpha/cg+1/(m*cs))^-1, bg=kappa*alpha^(3/2), bs=eta/sqrt(alpha).
- Operational unequal-energy likelihood retains
  exp(lambda*inner(x_i,z)-lambda^2*norm(x_i)^2/2). The old equal-energy formula
  is used only for unit configurations. Actual ML/Bayes identity and lift
  monotonicity are proved. The extra coordinates are a mathematical comparison,
  not an assumption that the original physical channel permits added uses.
- Rank deficiency uses actual Matrix.rank G <= rankBound, not a restriction on
  the ambient realization dimension.
- Arbitrary-length Procrustes uses the actual infimum over whole-space
  orthogonal automorphisms and has a proved attaining alignment.
- Mean width uses the original dimension d in E norm(g), even though the
  independent-coordinate unit lift has dimension d+m. Actual convex-hull
  support is attained and equals the finite score maximum.
- normalizedSphereMeasure is the probability normalization of volume.toSphere;
  neither the sphere measure nor meanWidth is defined by a Gaussian ratio.
  The ratio follows from genuine HaarToSphere polar integration and the actual
  standard-Gaussian density. Finite-hull support integrability is proved.
  The conventional h_K(u)+h_K(-u) average equals twice the support average.
  The final sphere theorem retains m>=2,d>=m-1 and the original ball assumption.
- The earlier O(rho^6) claim is not enlarged. normalTaylor_bound and
  normalTaylor_isBigO concern the actual simplex-success function and its
  actual first/second derivatives, m>=3, with genuine C3 regularity.
  Identifying this expansion with the exact shell minimum additionally requires
  lambda>0 and the strict-normal gap (m>=4 or the separate m=3 branch).
  The original uniform quantifier order gives C and rho0 independent of ambient
  dimension and reference embedding. No effective radius or numerical constant
  is claimed. No tangential finite-radius or equal-curvature-boundary minimizer
  is claimed.
- The exclusions of numerical/learning diagnostics and historical priority
  claims are retained, as is the explicit statement that the certificate is not
  a formal counterpart of every sentence of the manuscript.

## Remaining artifact checks
After staging: confirm the exact script substitutions took effect once, the old
94 local source hashes are unchanged, sphere entries occur in the final combined
certificate, all stated module/entry counts and archive SHA match that certificate,
and the generated paper contains the corrected factor-two sentence and full
source mappings. Those are final artifact checks, not open proof assumptions.

## Post-fix confirmation
All four findings are resolved in update_global_paper.py SHA 3dfe13bd01d1038d911d5e4aaaaf17fae1aa348431b018f7d284d4c6398a5485. The PG-02--04 paragraphs above record the original recommendations, not current defects. The script now hard-checks all four sphere modules and both final spherical/width audit entries. The table directly names SphereGaussian.ball_mean_width and widthIntegral_convexHull_eq_meanWidth. The Q1 sentence explicitly describes the product of normalized self-convolution factors. The factor-two correction remains in place. No unresolved mathematical or scope issue remains in the proposed text. Final staged-file and certificate/hash matching are still pending root's generation step.
