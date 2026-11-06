# Read-only compatibility audit: passed

The global centroid/decoder chain and the original sixth-order shell result are consistent. No source change is required by this audit.

1. Scope and hypotheses. Global centroid Lemma 4 and its exact cs=W*eta decoder consequence hold for m>=2, positive signal, arbitrary ambient dimension, and singular correlation Grams. The physical exact normal-shell minimum is asserted only for m>=3, d>=m and the strict existing in-plane curvature gaps. For m>=4 the condition is a_m(mu)>m/2; for m=3 it is a_3(mu)+b_3(mu)>2. Neither the new global inequalities nor the Taylor estimate remove these shell hypotheses. At a crossing equality the shell optimizer claim remains excluded.

2. Quantifiers. TaylorShell.UniformTaylorNormalShell places both C>0 and rho0>0 before forall d,V. One normal z is chosen before all small radii. The equality condition is the actual orthogonal orbit, not merely covariance equivalence. This agrees with new_results.tex. GaussianTaylor.normalTaylor_bound is stronger as a real analytic-expression bound for all real lambda and a two-sided rho interval; physical minimization is supplied separately by the strict-normal theorem.

3. Signal and constants. Both chains use mu=lambda/sqrt(alpha), alpha=(m-1)/m, and the identical actual decodingSuccess. Global cs is exp(-mu^2/2)*(exp(mu)-1)*eta/m. The shell coefficient is lambda*p'(lambda)/(2m)=(m-1)*gaussianC(m,mu)/2, as proved in TaylorCoefficient. There is no additional alpha factor to insert in either formula.

4. Remainder and sign. normalDeficit=p(lambda)-p(lambda*(1-rho^2/(2m))). Its exact quadratic term is positive lambda*p'/2m and its quartic term is negative lambda^2*p''/8m^2. A third-order error in signal displacement becomes O(rho^6), because the displacement is quadratic in rho. Negative rho denotes the even real extension, not a physical negative-distance shell. TaylorParity proves the odd-derivative conclusion for that extension.

5. Compatibility of rates. Along the actual normal family, norm(sum N)^2=m*rho^2-rho^4/4. The global centroid estimate therefore has order rho^2, consistently below the sharp local normal coefficient. The squared Gram defect on the same family has order rho^4, so a global Frobenius-square lower bound alone does not imply the sharp Procrustes-shell rate. No such inference is made by the new chain.

Read-only audited source SHA256 values:
paper\sections\new_results.tex 767799a3b1609fda85c720804eaa77b7c27589cfcba6f92ef75bdc1fb91295f4
paper\sections\normal_proof.tex 494163b59cda4ce4f7745de7dd0756e00c21c4eec410bafe91704727c1883d57
SimplexFull\TaylorDefinitions.lean 0ed4e719bd8ae8e6c7986001adb311d137a89efda34d30eb86e44482f55c4741
SimplexFull\GaussianTaylor.lean 2e05a55a884257b88ce1f83e1909b1398aa4899d8675ed450709fad56d078c8e
SimplexFull\TaylorShell.lean 5956d10f78c21620921e239f904167fbcba4d136f6cfc957d50fac33a576ee11
SimplexFull\TaylorCoefficient.lean 950f44ae1efc308be38578fedee2ab9d3e380a81eb1f8c96b59d1bcf97f032ac
SimplexFull\TaylorParity.lean a7db49558317c2393bf05a1c7fa1df9e37823eb6821261468be1c79b54003c96
