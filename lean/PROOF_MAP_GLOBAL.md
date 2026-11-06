# Global and local proof map

All listed results use actual mathematical objects. The main entry is
SimplexFull.VerifiedGlobal; reproduce.py compiles its entire source closure
in a fresh directory with Lean trust level zero and performs the selected
axiom audit. AUDIT_THEOREMS_GLOBAL.json lists the exact audited declarations.

| Paper result | Final declaration or module |
| --- | --- |
| Exact global sqrt and linear orthant comparison, including singular PSD | GlobalComparison.quantitative_lowerOrthant |
| Quantitative symmetric rectangles, including correlations +1 and -1 | GlobalRectangle.symmetricRectangle_gap |
| Exact centroid penalty eta, m>=2 | GlobalCentroid.centroid_penalty |
| Actual arbitrary-length Procrustes bound and attainment | Geometry.global_procrustesSq_le_gram_centroid; Geometry.global_procrustesSq_attained |
| cg Gram decoding bound | GlobalApplication.decodingSuccess_gram_penalty |
| cs centroid decoding bound | GlobalTail.decodingSuccess_centroid_penalty |
| cP Procrustes decoding bound | GlobalApplication.decodingSuccess_procrustes_penalty |
| Actual rank deficiency, independent of ambient realization | GlobalApplication.decodingSuccess_rank_deficiency |
| Operational nonunit ML and Bayes unused energy | GlobalTail.ball_decoder_unused_energy; GlobalTail.ball_bayes_unused_energy |
| Gaussian expected-max comparison with exact bg,bs | GlobalApplication.unitGaussianMaxBounds |
| Actual finite convex-hull support | Geometry.realSupport_convexHull_range |
| Actual normalized surface measure and Gaussian ratio | SphereGaussian.sphere_integral_eq_gaussian_ratio |
| Actual spherical mean-width stability | SphereGaussian.ball_mean_width |
| Ordered and triangular channel crossings | gaussian_ordered_crossings; gaussian_triangular_unique_crossing |
| Exact uniform strict-normal shell optimizer | Geometry.gaussian_uniform_exact_normal_shell_m4 / _m3 |
| Quantified O(rho^6), odd derivatives and curvature coefficient | Geometry.normalTaylor_bound; normalTaylor_isBigO; GaussianTaylor/TaylorParity/TaylorCoefficient |

All declaration names above are in SimplexFull unless a nested namespace
is shown. Global constants retain the paper formulas: K,kappa,eta,tau,
cg=W*kappa*alpha^2, cs=W*eta, cP=(alpha/cg+1/(m*cs))^-1,
bg=kappa*alpha^2/sqrt(alpha)=kappa*alpha^(3/2), bs=eta/sqrt(alpha).
W=exp(-mu^2/2)*(exp(mu)-1)/m and mu=lambda/sqrt(alpha).

The final global/application theorems do not take an adaptive-witness bound,
a target probability gap, a desired CDF inequality or UnitGaussianMaxBounds
as an extra hypothesis. Intermediate transfer lemmas are labeled as such
and their inputs are discharged in the final declarations.

Global theorems start at m>=2 and include singular covariance. Positive
decoder coefficients require lambda>0. Mean width retains the original
ambient d in 2/E||g_d||, and the actual rank hypothesis is not replaced by
an ambient-dimension hypothesis. Nonunit decoding retains individual
likelihood energy corrections.

The old 94 local modules are byte-identical to the reviewed release.
Their m>=3, strict-normal curvature gap and sufficiently small radius
hypotheses are unchanged. Uniform local C,r are existential, not numerical
certificates. Numerical diagnostics, experiments, priority, tangential
finite-radius optimizers and equality-boundary minimizers are not certified.

52 vendored source modules provide the actual Gaussian foundation proofs.
VENDOR_PROVENANCE.json records upstream commits and source hashes;
licenses/ preserves original licenses and attribution. These source modules
are freshly compiled alongside all SimplexFull modules, not taken from an
inherited custom build.
