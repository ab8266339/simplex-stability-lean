# Restored constants audit

Independent read-only check of the frozen scalar and comparison-constant sources against `snapshot/paper_source/paper_main.tex`. No collaborator file was edited. This review did not invoke Lean again. Each current source SHA256 equals the recorded exit-0 compile hash below.

**Verdict: no-defect.** The checked formulas for `Psi`, its inverse, curvature, Taylor, `L0`, `beta`, `A0`, `B0`, `ell`, `T`, `b`, `K`, and `kappa` agree with the paper. Printed axioms on the latest logs are `propext`, `Classical.choice`, and `Quot.sound`. The frozen sources contain no `sorry`, `admit`, `unsafe`, or `native_decide`.

Theorem 2 and the downstream applications are outside this audit. They are recorded as already passed and are not reopened here. Reviewers should not rewrite these modules.

## Scope

Phase root: `E:/simplex-lean-full-20261106/global-formalization-20261106`. Lean 4.31.0. Recorded commands use `leanprover--lean4---v4.31.0` with `-j 2 -t 0`. This review did not re-resolve the Mathlib git object; the required pin remains `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`.

Audited sources:

- `scalar-agent/SimplexFull/GlobalScalarPsi.lean`
- `scalar-agent/SimplexFull/GlobalScalarCurvature.lean`
- `scalar-agent/SimplexFull/GlobalScalarRange.lean`
- `scalar-agent/SimplexFull/GlobalScalarTaylor.lean`
- `scalar-agent/SimplexFull/GlobalScalarBounds.lean`
- `geometry-agent/SimplexFull/GlobalComparisonDefs.lean`
- `foundation-audit/SimplexFull/GlobalComparisonConstants.lean`

Read dependency of the `K` factorization, not one of the seven targets: `foundation-audit/SimplexFull/GlobalRectangleBound.lean`. Its `rectangleK` matches the paper rectangle coefficient. `foundation-audit` has no `GlobalComparisonDefs.lean`; the constants module imports the geometry-agent definitions.

Paper anchors: `α=(m-1)/m` (opening notation), (eq:scalar), (eq:psi-derivative), (eq:bounds), (eq:K), and the `M0` window in (eq:eta). Sections 3–4 constants `c_g`, `c_s`, `c_P`, `η`, `τ`, `b_g`, `b_s`, and `W` are outside this frozen set.

The stopped draft `constants/SimplexFull/GlobalConstantsBasic.lean` is not part of this audit and is not certified.

## Formula agreement

Snapshot scalar base: `q = phi/Phi`, `h = id + q`, `sigma = 1 - q*h`.

| Paper | Lean | Agreement |
| --- | --- | --- |
| `Ψ(H(s)) = log Φ(s) + r(s)^2/2` | `psiPull s = log (Phi s) + q s^2/2`, `Psi y = psiPull (hInv y)`, `Psi (h s) = psiPull s` | exact |
| `Ψ'(H(s)) = r(s)` | `HasDerivAt Psi (q (hInv y))`, and `deriv Psi (h s) = q s` | exact |
| `Ψ''(H(s)) = -r H/(1-r H)` | `psiCurvature y = q(hInv y)*y/sigma(hInv y)`, `deriv (deriv Psi) y = -psiCurvature y` | exact on `y>0` |
| `L0 = m log Φ(u)` | `logFloor m u` | exact |
| `β = Ψ^{-1}(L0)` | `beta = psiInv (logFloor)` | exact on the inverse domain below |
| `A0 = Ψ'(β)` | `capA = deriv Psi beta` | exact |
| `B0 = v + sqrt(-2 L0/m) + sqrt(-2 α L0)` | `capB` with `α = ((m:ℝ)-1)/m` hardcoded | exact displayed form |
| `ℓ = β/√2`, `T = √2 B0 + ℓ` | `ell`, `radiusT` | exact |
| `b(t) = 2Φ(t)-1` | `centralMass` | exact |
| `K` numerator `e^{-m A0 β} ℓ^2 e^{-4 T^2/3} b(ℓ)^{2m-2}`, denominator `4 π m (m-1)` | `paperK` | exact |
| `κ = Φ(u)^m K / (1 + sqrt(1 + K m (m-1)))` | `paperKappa` | exact |
| rectangle coefficient `ℓ^2 e^{-4 T^2/3} b(ℓ)^{m-2} / (4 π m (m-1))` | `rectangleK` | exact |
| `M0 = max (-Ψ'')` on `[H(0)/2, 3 H(1)/2]` | `curvatureInterval` and `M0` via `IsMaxOn` | exact window and maximum |
| centroid scalar Taylor | `centroid_scalar_taylor` for `c ∈ [0,1]` and `\|z\| ≤ H(0)/2` | exact inequality and hypotheses |

`paperK_factorization` is the identity `K = e^{-m A0 β} * rectangleK(ℓ,T) * b(ℓ)^m`, from `2m-2 = (m-2)+m`. That is the paper assembly of the exponential weight, the rectangle coefficient, and `b(ℓ)^m`.

`paperKappa_mul_le_sqrt_gap` is the paper rationalization: for `2 ≤ m` and `0 ≤ d ≤ m(m-1)`,

`κ d ≤ Φ(u)^m (sqrt(1+K d)-1)`.

`covarianceDefect` is `‖R-I‖_F^2`. For `IsCorrelation` (positive semidefinite with unit diagonal, singular matrices included) it is at most `m(m-1)`, by vanishing diagonal terms and `|Rij| ≤ 1` on `2×2` principal submatrices. `paperKappa_defect_le_sqrt_gap` applies the rationalization to that defect.

For `m ≥ 1`, the paper `B0` also equals `v + (1+sqrt(m-1)) sqrt(-2 log Φ(u))`. `capB` keeps the displayed two-square-root form. The collapsed form is not a separate named lemma.

## Positivity and intervals

`capB_pos` assumes `0 < m` and `u ≤ v`, with `u` and `v` otherwise arbitrary reals. Equality `u = v` is allowed. There is no `u ≥ 0` split.

The proof cancels `m` in the first radicand, then uses `0 < u + sqrt(-2 log Φ(u))`. That strict bound holds for every real `u`, including large negative `u`, because `h(u) = u + q(u) > 0` and `q(u) < sqrt(-2 log Φ(u))` from `psiPull u < 0`. Since `v ≥ u`, the first two terms of `B0` are already positive. The `α` term is used only through `Real.sqrt ≥ 0`. For `m ≥ 2`, `α = (m-1)/m > 0` and `L0 < 0`, so the second radicand `-2(m-1) log Φ(u)` is positive and Lean's square root is the ordinary real square root.

`ell_pos` follows from `beta_pos`. With `capB_pos`, `radiusT = √2 * capB + ell` is strictly larger than `ell`. That comparison is unnamed in the audited files. It is a one-line corollary, not a formula error, and it is not an open obligation of the passed Theorem 2.

`paperK_pos` and `paperKappa_pos` assume `2 ≤ m` and quantify over all real `u, v`. They do not require `u ≤ v`. Every factor is positive from `ell > 0`, `exp`, `b(ell) > 0`, and the denominator `4 π m (m-1)` for `m ≥ 2`, whether or not `B0` is positive. The raw `paperK` definition is total; the positivity theorems are the paper regime `m ≥ 2`.

`Psi_psiInv` needs `L < 0`, and `psiInv_Psi` needs `y > 0`. Those are the two-sided inverse statements. `psiInv_pos` and `beta_pos` are only positivity of `h`. For `0 < m`, `logFloor_neg` supplies `L0 < 0`, so `Psi (beta m u) = logFloor m u` is `Psi_psiInv` applied to that fact. `capA` is then `q` at the scalar preimage by `deriv_Psi_h`.

`q_le_deriv_Psi_psiInv` is the paper direction `a ≤ A0`: if `L < 0` and `L ≤ psiPull s`, then `q s ≤ deriv Psi (psiInv L)`.

`threshold_envelope_pos` takes a free real `alpha` and no sign hypothesis. If `alpha < 0`, the second radicand is negative and Lean `Real.sqrt` returns `0`. The inequality of that Lean expression still holds. `capB` does not use this free parameter; it inserts the paper `α`.

`M0` is `Classical.choose` of a maximizer. The printed axiom is the existing `Classical.choice`. `psiCurvature_le_M0` and `M0_attained` make it the maximum of `-Ψ''` on the paper interval.

The centroid Taylor endpoints land in that interval: `c ∈ [0,1]` gives `H(c) ∈ [H(0), H(1)]`, and `|z| ≤ H(0)/2` with `H(0) ≤ H(1)` keeps `H(c)+z` inside `[H(0)/2, 3 H(1)/2]`.

## Non-blocking remarks

These do not change the no-defect verdict and do not call for edits to the frozen modules.

- Unused-variable lint: `i`, `j` in `GlobalComparisonConstants.lean` at the defect nonnegativity proof; `y` in `GlobalScalarCurvature.lean` and `GlobalScalarRange.lean`. Exit code remains 0.
- Stale Taylor stdout logs `SimplexFull.GlobalScalarTaylor-20261106-155955-711460` and `...-160143-284522` still mention `sorryAx`. The current Taylor source does not. The log that matches the current hash is `...-160516-997959`, whose printed axioms omit `sorryAx`.
- `GlobalComparisonConstants` was compiled with `-R foundation-audit` while `GlobalComparisonDefs` lives in `geometry-agent`. The current defs hash matches that module's own exit-0 record. This review did not rebuild the import closure.

## Compile records matched to current bytes

| Module | SHA256 | Record | Exit |
| --- | --- | --- | --- |
| `GlobalScalarPsi` | `5ac00effd8cbfd5cadd6c3c8842ae276b6c814b1399b5caf95e36a86db02fd2e` | `scalar-agent/logs/SimplexFull.GlobalScalarPsi-20261106-155234-104442` | 0 |
| `GlobalScalarCurvature` | `5b6b2c7b06c8c22860b2281030310d1f015141ccb40f8b230946ddea0c26c6b3` | `scalar-agent/logs/SimplexFull.GlobalScalarCurvature-20261106-155754-729617` | 0 |
| `GlobalScalarRange` | `61efb456691406d01fe87e2d0b907a43e9d5a0423b192ba6edfd3512b932ca0f` | `scalar-agent/logs/SimplexFull.GlobalScalarRange-20261106-160439-201650` | 0 |
| `GlobalScalarTaylor` | `7ddc7a13a5ed04917417f8dd47fe7f7dbdce4c3acd11d2a1b731e99bf83f879d` | `scalar-agent/logs/SimplexFull.GlobalScalarTaylor-20261106-160516-997959` | 0 |
| `GlobalScalarBounds` | `7200f32ecd360a4b61fbdaa7b86cbb1f8bdf04fccd63aa9e0e6ecd21224ab8db` | `scalar-agent/logs/SimplexFull.GlobalScalarBounds-20261106-160750-470181` | 0 |
| `GlobalComparisonDefs` | `8548d191842bc285e3a72ed425ab28e93aa5651e6644312b00948bdde5352215` | `geometry-agent/SimplexFull.GlobalComparisonDefs-20261106-171152-351251` | 0 |
| `GlobalComparisonConstants` | `5dcb47f9809551604be3d480547a39c8cef22ad3e0f236c9a49575eb980649af` | `foundation-audit/SimplexFull.GlobalComparisonConstants.json` | 0 |
| `GlobalRectangleBound` (dependency) | `0b0713a725920cd3f71ed7c4f71699502dd6cb7cb78517977331c002417a798f` | `foundation-audit/SimplexFull.GlobalRectangleBound.json` | 0 |

Remaining obligations inside this frozen constant scope: none.
