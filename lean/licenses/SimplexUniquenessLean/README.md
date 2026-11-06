# The Equality Cases of the Weak Simplex Conjecture in Lean

[![Lean CI](https://github.com/Tongji708A/simplex-uniqueness-lean/actions/workflows/lean_action_ci.yml/badge.svg?branch=main)](https://github.com/Tongji708A/simplex-uniqueness-lean/actions/workflows/lean_action_ci.yml)

This repository contains a Lean 4 companion formalization for *The Equality
Cases of the Weak Simplex Conjecture: A Response to Mulgund's Open Problem
8.1* by Mengwei Su, Kaiwen Yang, Hao Xu and Chih-Lin I. It builds on
[mathlib](https://github.com/leanprover-community/mathlib4) and on the
formalization accompanying
[Mulgund's resolution of the Weak Simplex Conjecture](https://github.com/abhmul/weak-simplex-conjecture-lean),
pinned to Lean 4.31.0.

## What is formalized

The repository machine-checks both halves of Mulgund's Open Problem 8.1.

The single-threshold theorem (Theorem 1 of the paper) is formalized along the
paper's own route, for every admissible covariance including singular ones:

1. a strict form of the Šidák–Khatri symmetric rectangle inequality
   (Lemma 1), whose grouping step uses only the slab-peeling step of
   Šidák's inequality, so Royen's Gaussian correlation theorem is not
   needed;
2. a strict product inequality for centered truncated exponential factors
   (Lemma 2), obtained by injecting Lemma 1 into one normalized
   self-convolution step of Mulgund's product argument;
3. adaptive tilt witnesses for singular covariance, obtained from Mulgund's
   positive-definite witnesses by a compactness argument, and the
   change-of-measure assembly.

Together these give, for a correlation matrix `R` with `R - J/m ⪰ 0` and
`R ≠ I`, that `P {X ≤ c·1} > Φ(c)^m` at every finite threshold `c`, so that
equality at a single threshold holds if and only if `R = I`.

The moment-generating half is also checked along a distributional route that
is independent of the strict product inequality:

1. stochastic domination combined with equality of one strictly increasing
   moment forces equality of laws, and
2. a correlated Gaussian vector satisfying `R - J/(n+1) ⪰ 0` whose
   coordinate maximum carries the independent-maximum distribution at every
   threshold must have `R = I`.

Together these give, for any single moment-generating parameter, that
equality with the regular-simplex value forces the regular-simplex Gram
matrix. The Gram-rigidity step identifying the code geometrically is also
formalized.

| Paper result | Lean declaration | Source |
|---|---|---|
| Lemma 1: strict symmetric rectangle inequality, singular covariance allowed | `symmetricRectangle_gt_iid` | [`StrictRectangle.lean`](SimplexUniquenessLean/StrictRectangle.lean) |
| Lemma 2: strict product inequality for truncated exponentials | `tiltedHalfLine_product_gt`, `tiltedHalfLine_product_gt_of_posDef` | [`StrictProduct.lean`](SimplexUniquenessLean/StrictProduct.lean) |
| Adaptive tilt witnesses for singular covariance | `exists_adaptiveWitnesses_of_isWeakSimplexCov` | [`SingularWitnesses.lean`](SimplexUniquenessLean/SingularWitnesses.lean) |
| Theorem 1: single-threshold strictness and its equality form | `lowerOrthant_gt_iid`, `lowerOrthant_eq_iid_at_iff`, `eq_one_of_lowerOrthant_eq_iid_at` (and the `_of_posDef` variants, the assembly `lowerOrthant_gt_iid_of_witnesses`) | [`SingleThreshold.lean`](SimplexUniquenessLean/SingleThreshold.lean) |
| Strict-monotone rigidity of stochastic domination | `measure_eq_of_iic_le_of_integral_eq`, `measure_eq_of_iic_le_of_mgf_eq` | [`StrictMonoDomination.lean`](SimplexUniquenessLean/StrictMonoDomination.lean) |
| All-threshold rigidity: independent maximum law forces `R = I` | `eq_one_of_lowerOrthant_eq_iid` | [`TailRigidity.lean`](SimplexUniquenessLean/TailRigidity.lean) |
| Normal upper-tail bound, bivariate pair-tail lower bound | `gaussianReal_tail_le_pdf_div`, `bivariate_pair_tail_lower_bound` | [`TailRigidity.lean`](SimplexUniquenessLean/TailRigidity.lean) |
| Gram rigidity: equal Gram matrices of spanning families are orthogonally equivalent | `exists_linearIsometryEquiv_of_gram_eq` | [`GramRigidity.lean`](SimplexUniquenessLean/GramRigidity.lean) |

## Scope

The coding and mean-width consequences in the paper (Theorem 3 and the
corollary on the Simplex Mean Width Conjecture) are not formalized as
standalone Lean theorems. The equality form of Theorem 1 is formalized in the
direction that equality at one threshold forces `R = I`; the converse is the
elementary independent case.

## Axiom audit

[`SimplexUniquenessLean/Audit/Axioms.lean`](SimplexUniquenessLean/Audit/Axioms.lean)
prints the transitive axioms of every paper-level declaration listed in the
table above, which covers every helper lemma they use. The accepted
output for each is exactly `[propext, Classical.choice, Quot.sound]`. The
same audit applied to the dependency reproduces the clean result reported
there.

## Building

Install Lean via [elan](https://lean-lang.org/install/), then

```bash
lake exe cache get
lake build
lake env lean SimplexUniquenessLean/Audit/Axioms.lean
```

The build pulls the dependency at the pinned revision recorded in
`lakefile.toml`.

## License

MIT. See [LICENSE](LICENSE).
