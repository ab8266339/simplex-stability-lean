# Exact global quantitative orthant comparison — frozen handoff

All files were constructed and compiled only on BRJD E:.
The nine source modules listed in INTEGRATION_COMPARISON.json compile with Lean 4.31, -j2 -t0.
The final three public theorems depend only on propext, Classical.choice, Quot.sound.

## Public interface
Import SimplexFull.GlobalComparison.
Namespace: SimplexFull.GlobalComparison.

orthant_sqrt_comparison {m} (hm : 2 ≤ m)
  (R : Matrix (Fin m) (Fin m) ℝ) (hR : WeakSimplex.IsWeakSimplexCov R)
  (u v c : ℝ) (huc : u ≤ c) (hcv : c ≤ v) :
  (Phi u)^m * (sqrt (1 + paperK m u v * covarianceDefect R) - 1)
    ≤ orthantMass R c - (Phi c)^m

orthant_linear_comparison, same parameters:
  paperKappa m u v * covarianceDefect R ≤ orthantMass R c - (Phi c)^m

quantitative_lowerOrthant additionally packages positivity of both exact constants
and both comparisons, with c ∈ Icc u v.

covarianceDefect R := ∑ i, ∑ j, ((R - 1) i j)^2
orthantMass R c := (multivariateGaussian (0 : WeakSimplex.Coord m) R
  (WeakSimplex.lowerOrthant c)).toReal

The constants beta, capA, capB, ell, radiusT, paperK, paperKappa are exactly the
original paper expressions. In particular capB retains both square-root terms,
and paperK retains exp(-m*A0*beta), ell², exp(-4*T²/3), b(ell)^(2m-2),
and denominator 4*pi*m*(m-1).

## Concrete mathematical content
- Actual PSD adaptive witnesses, including singular covariance.
- Derives all witness coordinate bounds from the actual witness value inequality
  and PSD quadratic Cauchy; no witness bounds are supplied as hypotheses.
- Actual Gaussian orthogonal rotation and integrable Fubini identity.
- Actual fixed-average factor equals weighted symmetric-rectangle indicator.
- Exact rectangle gap, weight lower bound, and positive box mass yield quantitative
  doubling Q0²-Q1 ≥ K * covarianceDefect.
- Actual normalized self-convolution Q1 ≥ 1, including PSD covariances.
- Actual Gaussian tilt identity F_R = exp(J) Q0.
- Square-root comparison and exact rationalized linear comparison.
- R=I handled by actual independent Gaussian orthant equality; no limit assumption.

## Source/build order and external verified inputs
Owned modules: GlobalComparisonDefs, Witness, Rotation, Doubling, Factors, Box,
Tilt, Actual, GlobalComparison (each prefix GlobalComparison).

Before Factors, compile foundation-audit's GlobalRectangleBound dependency closure
and GlobalComparisonProduct. Before Actual, compile foundation-audit's
GlobalComparisonConstants (it depends on our Defs).
Defs depends on scalar-agent's actual GlobalScalarBounds closure,
GlobalCentroidMatrix, and foundation-audit's GlobalWitnessOrthantBound and
GlobalFoundationBridge; all are verified inputs, not axiomatic assumptions.

Sources: geometry-agent/SimplexFull
Objects: geometry-agent/build/SimplexFull
Original 14 geometry/mean-width/energy modules remain frozen, as do original
project sources. This archive contains only the new nine owned modules and their
verification evidence. External input sources remain in their owners' directories.

Rotation helpers and Gaussian rotation/Fubini setup adapt the MIT-licensed
weak-simplex-conjecture-lean/SimplexUniquenessLean proof, with attribution in source.
The quantitative bounds, original constants, actual witness assembly and final
Theorem 2 are new to this phase.
