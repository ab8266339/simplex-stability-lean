import SimplexFull.OrthantMomentTable
import SimplexFull.OrthantMomentBridge
import SimplexFull.GaussianPolynomial
import SimplexFull.OrthantLimits
import SimplexFull.GramCoordinates
import Mathlib.Topology.Separation.Hausdorff

/-!
# Orthant integrals of the covariance density coefficients

`firstDensityCoeff A` is `ρ(I, x) * (xᵀ A x) / 2`. On `orthantIic c`, a zero
diagonal removes the variance terms, and `Phi_pow_mul_q_sq` rewrites the pair
moments as `φ(c)² Φ(c)^(m-2) * halfEntrySum A`.

`secondDensityCoeff A` contracts against the pair table `moment2 (-q) σ` and the
four-index table `moment4 (-q) σ`. `gaussian_second_factor` rewrites that
truncated integral in the `h`, `q` coordinates. Both full-space integrals are `0`.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace SimplexFull.Covariance

open SimplexFull.Geometry

variable {m : ℕ} [NeZero m]

lemma measurableSet_orthantIic (c : ℝ) : MeasurableSet (orthantIic (m := m) c) := by
  rw [orthantIic_eq_maxCoord_le]
  exact measurableSet_le measurable_maxCoord measurable_const

omit [NeZero m] in
lemma coordMonomial_pair (i j : Fin m) (x : EuclideanSpace ℝ (Fin m)) :
    coordMonomial (fun t => singleCount i 1 t + singleCount j 1 t) x = x i * x j := by
  rw [coordMonomial_add_counts, monomial_singleCount, monomial_singleCount, pow_one, pow_one]

omit [NeZero m] in
lemma integrableOn_rho_mul_pair (i j : Fin m) (c : ℝ) :
    IntegrableOn (fun x : EuclideanSpace ℝ (Fin m) => rho 1 x * (x i * x j)) (orthantIic c) := by
  simpa only [coordMonomial_pair] using
    integrableOn_orthant_coordMonomial (fun t => singleCount i 1 t + singleCount j 1 t) c

omit [NeZero m] in
lemma rho_mul_quad_eq_sum (A : Matrix (Fin m) (Fin m) ℝ) (x : EuclideanSpace ℝ (Fin m)) :
    rho 1 x * quad A x = ∑ i, ∑ j, A i j * (rho 1 x * (x i * x j)) := by
  unfold quad
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

lemma integral_rho_quad_orthant (A : Matrix (Fin m) (Fin m) ℝ) (c : ℝ) :
    ∫ x in orthantIic c, rho 1 x * quad A x =
      ∑ i, ∑ j, A i j * ∫ x in orthantIic c, rho 1 x * (x i * x j) := by
  rw [setIntegral_congr_fun (measurableSet_orthantIic c) (fun x _ => rho_mul_quad_eq_sum A x)]
  rw [integral_finsetSum Finset.univ]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum Finset.univ]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_const_mul]
    · intro j _
      exact Integrable.const_mul (integrableOn_rho_mul_pair i j c) (A i j)
  · intro i _
    exact integrable_finsetSum Finset.univ fun j _ =>
      Integrable.const_mul (integrableOn_rho_mul_pair i j c) (A i j)

omit [NeZero m] in
/-- Zero diagonal: every pair, including the diagonal, contributes `Aᵢⱼ Φ^m q²`. -/
lemma pair_integral_zeroDiagonal {A : Matrix (Fin m) (Fin m) ℝ} (hZ : zeroDiagonal A)
    (c : ℝ) (i j : Fin m) :
    A i j * ∫ x in orthantIic c, rho 1 x * (x i * x j) =
      Phi c ^ m * (q c) ^ 2 * A i j := by
  by_cases hij : i = j
  · subst hij
    rw [zeroDiagonal_apply hZ i]
    simp only [zero_mul, mul_zero]
  · rw [integral_orthant_pair_distinct_normalized c hij]
    ring

lemma integral_orthant_firstDensityCoeff_q {A : Matrix (Fin m) (Fin m) ℝ}
    (hZ : zeroDiagonal A) (c : ℝ) :
    ∫ x in orthantIic c, firstDensityCoeff A x =
      Phi c ^ m * (q c) ^ 2 * halfEntrySum A := by
  have hpt : EqOn (firstDensityCoeff A) (fun x => (1 / 2 : ℝ) * (rho 1 x * quad A x))
      (orthantIic c) := by
    intro x _
    unfold firstDensityCoeff
    ring
  rw [setIntegral_congr_fun (measurableSet_orthantIic c) hpt, integral_const_mul,
    integral_rho_quad_orthant]
  simp_rw [pair_integral_zeroDiagonal hZ, ← Finset.mul_sum]
  simp only [halfEntrySum, entrySum]
  ring

/-- For `m ≥ 2` and a zero diagonal, the truncated first coefficient is
`φ(c)² Φ(c)^(m-2)` times half the sum of the entries. -/
theorem integral_orthant_firstDensityCoeff_zeroDiagonal (hm : 2 ≤ m)
    {A : Matrix (Fin m) (Fin m) ℝ} (hZ : zeroDiagonal A) (c : ℝ) :
    ∫ x in orthantIic c, firstDensityCoeff A x =
      (phi c) ^ 2 * Phi c ^ (m - 2) * halfEntrySum A := by
  rw [integral_orthant_firstDensityCoeff_q hZ c, Phi_pow_mul_q_sq hm c]

/-- The full-space integral of the first density coefficient vanishes on a zero diagonal. -/
theorem integral_firstDensityCoeff_zero {A : Matrix (Fin m) (Fin m) ℝ}
    (hZ : zeroDiagonal A) :
    ∫ x, firstDensityCoeff A x = 0 := by
  have hlim1 : Tendsto (fun c : ℝ => ∫ x in orthantIic c, firstDensityCoeff A x) atTop
      (𝓝 (∫ x, firstDensityCoeff A x)) := by
    simpa only [orthantIic] using tendsto_integral_orthant_atTop (integrable_firstDensityCoeff A)
  have hlim2 : Tendsto (fun c : ℝ => ∫ x in orthantIic c, firstDensityCoeff A x) atTop
      (𝓝 0) := by
    have hfun : (fun c : ℝ => ∫ x in orthantIic c, firstDensityCoeff A x) =
        fun c => Phi c ^ m * (q c) ^ 2 * entrySum A / 2 := by
      funext c
      rw [integral_orthant_firstDensityCoeff_q hZ c]
      simp only [halfEntrySum]
      ring
    rw [hfun]
    exact tendsto_first_orthant_expression (entrySum A)
  exact tendsto_nhds_unique hlim1 hlim2

omit [NeZero m] in
lemma one_sub_sigma (c : ℝ) : 1 - sigma c = q c * h c := by
  unfold sigma
  ring

omit [NeZero m] in
lemma coordMonomial_four (i j k l : Fin m) (x : EuclideanSpace ℝ (Fin m)) :
    coordMonomial (fun t =>
      ((singleCount i 1 t + singleCount j 1 t) + singleCount k 1 t) + singleCount l 1 t) x =
      x i * x j * x k * x l := by
  rw [coordMonomial_add_counts, coordMonomial_add_counts, coordMonomial_add_counts,
    monomial_singleCount, monomial_singleCount, monomial_singleCount, monomial_singleCount,
    pow_one, pow_one, pow_one, pow_one]

omit [NeZero m] in
lemma integrableOn_rho_mul_four (i j k l : Fin m) (c : ℝ) :
    IntegrableOn (fun x : EuclideanSpace ℝ (Fin m) =>
      rho 1 x * (x i * x j * x k * x l)) (orthantIic c) := by
  simpa only [coordMonomial_four] using
    integrableOn_orthant_coordMonomial (fun t =>
      ((singleCount i 1 t + singleCount j 1 t) + singleCount k 1 t) + singleCount l 1 t) c

omit [NeZero m] in
lemma rho_mul_quad_sq_eq_sum (A : Matrix (Fin m) (Fin m) ℝ) (x : EuclideanSpace ℝ (Fin m)) :
    rho 1 x * (quad A x) ^ 2 =
      ∑ i, ∑ j, ∑ k, ∑ l,
        (A i j * A k l) * (rho 1 x * (x i * x j * x k * x l)) := by
  rw [quad_sq_monomials]
  simp_rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

omit [NeZero m] in
lemma integral_orthant_sum4 (c : ℝ)
    (f : Fin m → Fin m → Fin m → Fin m → EuclideanSpace ℝ (Fin m) → ℝ)
    (hf : ∀ i j k l, IntegrableOn (f i j k l) (orthantIic c)) :
    ∫ x in orthantIic c, ∑ i, ∑ j, ∑ k, ∑ l, f i j k l x =
      ∑ i, ∑ j, ∑ k, ∑ l, ∫ x in orthantIic c, f i j k l x := by
  rw [integral_finsetSum Finset.univ]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum Finset.univ]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_finsetSum Finset.univ]
      · refine Finset.sum_congr rfl fun k _ => ?_
        rw [integral_finsetSum Finset.univ (fun l _ => hf i j k l)]
      · intro k _
        exact integrable_finsetSum Finset.univ fun l _ => hf i j k l
    · intro j _
      exact integrable_finsetSum Finset.univ fun k _ =>
        integrable_finsetSum Finset.univ fun l _ => hf i j k l
  · intro i _
    exact integrable_finsetSum Finset.univ fun j _ =>
      integrable_finsetSum Finset.univ fun k _ =>
        integrable_finsetSum Finset.univ fun l _ => hf i j k l

/-- Pair table: `∫ ρ xᵢ xⱼ = Φ^m * moment2 (-q, σ)`. -/
lemma integral_orthant_quad_moment (B : Matrix (Fin m) (Fin m) ℝ) (c : ℝ) :
    ∫ x in orthantIic c, rho 1 x * quad B x =
      Phi c ^ m * quadMoment (-q c) (sigma c) B := by
  rw [integral_rho_quad_orthant]
  simp_rw [integral_orthant_pair_moment2 c]
  have hre : ∀ i j, B i j * (Phi c ^ m * moment2 (-q c) (sigma c) i j) =
      Phi c ^ m * (B i j * moment2 (-q c) (sigma c) i j) := by
    intro i j
    ring
  simp_rw [hre, ← Finset.mul_sum]
  unfold quadMoment
  rfl

omit [NeZero m] in
/-- A zero diagonal kills every summand whose first or second pair repeats an index.
On the remaining summands the four-index table is the orthant moment. -/
lemma quad_monomial_integral_zeroDiagonal {A : Matrix (Fin m) (Fin m) ℝ}
    (hZ : zeroDiagonal A) (c : ℝ) (i j k l : Fin m) :
    (A i j * A k l) * ∫ x in orthantIic c, rho 1 x * (x i * x j * x k * x l) =
      Phi c ^ m * (A i j * A k l * moment4 (-q c) (sigma c) i j k l) := by
  by_cases hij : i = j
  · have h0 : A i j = 0 := by
      simpa [hij] using zeroDiagonal_apply hZ i
    simp only [h0, zero_mul, mul_zero]
  · by_cases hkl : k = l
    · have h0 : A k l = 0 := by
        simpa [hkl] using zeroDiagonal_apply hZ k
      simp only [h0, zero_mul, mul_zero]
    · rw [integral_orthant_quad_moment4 c hij hkl]
      ring

lemma integral_orthant_quad_sq_moment {A : Matrix (Fin m) (Fin m) ℝ}
    (hZ : zeroDiagonal A) (c : ℝ) :
    ∫ x in orthantIic c, rho 1 x * (quad A x) ^ 2 =
      Phi c ^ m * quadSquareMoment (-q c) (sigma c) A := by
  rw [setIntegral_congr_fun (measurableSet_orthantIic c)
    (fun x _ => rho_mul_quad_sq_eq_sum A x)]
  rw [integral_orthant_sum4 c
    (fun i j k l x => (A i j * A k l) * (rho 1 x * (x i * x j * x k * x l)))
    (fun i j k l => Integrable.const_mul (integrableOn_rho_mul_four i j k l c)
      (A i j * A k l))]
  simp_rw [integral_const_mul, quad_monomial_integral_zeroDiagonal hZ, ← Finset.mul_sum]
  unfold quadSquareMoment
  rfl

lemma integrableOn_rho (c : ℝ) :
    IntegrableOn (fun x : EuclideanSpace ℝ (Fin m) => rho 1 x) (orthantIic c) := by
  simpa [zero_mul, Real.exp_zero, one_mul] using
    (integrable_exp_max_rho_one (0 : ℝ)).integrableOn (s := orthantIic c)

lemma integrableOn_rho_quad (B : Matrix (Fin m) (Fin m) ℝ) (c : ℝ) :
    IntegrableOn (fun x => rho 1 x * quad B x) (orthantIic c) := by
  simpa [zero_mul, Real.exp_zero, one_mul] using
    (integrable_exp_max_rho_one_mul_quad (0 : ℝ) B).integrableOn (s := orthantIic c)

lemma integrableOn_rho_quad_sq (A : Matrix (Fin m) (Fin m) ℝ) (c : ℝ) :
    IntegrableOn (fun x => rho 1 x * (quad A x) ^ 2) (orthantIic c) := by
  simpa [zero_mul, Real.exp_zero, one_mul] using
    (integrable_exp_max_rho_one_mul_quad_sq (0 : ℝ) A).integrableOn (s := orthantIic c)

/-- Truncated second coefficient, as `Φ(c)^m` times the moment-table contraction. -/
theorem integral_orthant_secondDensityCoeff_moment {A : Matrix (Fin m) (Fin m) ℝ}
    (hZ : zeroDiagonal A) (c : ℝ) :
    ∫ x in orthantIic c, secondDensityCoeff A x =
      Phi c ^ m * quadDensityCoeffMoment (-q c) (sigma c) A := by
  have hpt : EqOn (secondDensityCoeff A) (fun x =>
      (Matrix.trace (A * A) / 4) * rho 1 x +
      (1 / 8 : ℝ) * (rho 1 x * (quad A x) ^ 2) -
      (1 / 2 : ℝ) * (rho 1 x * quad (A * A) x)) (orthantIic c) := by
    intro x _
    unfold secondDensityCoeff
    ring
  rw [setIntegral_congr_fun (measurableSet_orthantIic c) hpt]
  have hf : IntegrableOn (fun x => (Matrix.trace (A * A) / 4) * rho 1 x) (orthantIic c) :=
    Integrable.const_mul (integrableOn_rho (m := m) c) (Matrix.trace (A * A) / 4)
  have hg : IntegrableOn (fun x => (1 / 8 : ℝ) * (rho 1 x * (quad A x) ^ 2))
      (orthantIic c) :=
    Integrable.const_mul (integrableOn_rho_quad_sq A c) ((1 : ℝ) / 8)
  have hh : IntegrableOn (fun x => (1 / 2 : ℝ) * (rho 1 x * quad (A * A) x))
      (orthantIic c) :=
    Integrable.const_mul (integrableOn_rho_quad (A * A) c) ((1 : ℝ) / 2)
  change ∫ x in orthantIic c,
      (((fun x : EuclideanSpace ℝ (Fin m) => (Matrix.trace (A * A) / 4) * rho 1 x) +
        (fun x : EuclideanSpace ℝ (Fin m) => (1 / 8 : ℝ) * (rho 1 x * (quad A x) ^ 2)) -
        (fun x : EuclideanSpace ℝ (Fin m) => (1 / 2 : ℝ) * (rho 1 x * quad (A * A) x))) x) = _
  rw [integral_sub' (hf.add hg) hh, integral_add' hf hg, integral_const_mul,
    integral_const_mul, integral_const_mul, integral_orthant_rho,
    integral_orthant_quad_sq_moment hZ, integral_orthant_quad_moment]
  unfold quadDensityCoeffMoment
  ring

/-- The same integral in the `φ² Φ^(m-2)` normalization, with `F`, `R`, `T`
replaced by `frobSq`, `rowSumSq`, and `entrySum`. -/
theorem integral_orthant_secondDensityCoeff_factor (hm : 2 ≤ m)
    {A : Matrix (Fin m) (Fin m) ℝ} (hA : A.IsSymm) (hZ : zeroDiagonal A) (c : ℝ) :
    ∫ x in orthantIic c, secondDensityCoeff A x =
      (phi c) ^ 2 * Phi c ^ (m - 2) *
        ((h c) ^ 2 * frobSq A / 4 - q c * h c * rowSumSq A / 2 +
          (q c) ^ 2 * (entrySum A / 2) ^ 2 / 2) := by
  rw [integral_orthant_secondDensityCoeff_moment hZ c,
    quadDensityCoeffMoment_truncGauss hA hZ (one_sub_sigma c)]
  have halign :
      Phi c ^ m * ((q c * h c) ^ 2 / 4 * frobSq A -
        (q c) ^ 2 * (q c * h c) / 2 * rowSumSq A +
        (q c) ^ 4 / 8 * (entrySum A) ^ 2) =
      Phi c ^ m * ((1 - sigma c) ^ 2 * frobSq A / 4 -
        (q c) ^ 2 * (1 - sigma c) * rowSumSq A / 2 +
        (q c) ^ 4 * (entrySum A) ^ 2 / 8) := by
    rw [one_sub_sigma c]
    ring
  rw [halign, gaussian_second_factor hm c (frobSq A) (rowSumSq A) (entrySum A)]

/-- The full-space integral of the second density coefficient vanishes for a
symmetric zero-diagonal matrix. The orthant expression is the raw `σ`, `q` form. -/
theorem integral_secondDensityCoeff_zero {A : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.IsSymm) (hZ : zeroDiagonal A) :
    ∫ x, secondDensityCoeff A x = 0 := by
  have hlim1 : Tendsto (fun c : ℝ => ∫ x in orthantIic c, secondDensityCoeff A x) atTop
      (𝓝 (∫ x, secondDensityCoeff A x)) := by
    simpa only [orthantIic] using
      tendsto_integral_orthant_atTop (integrable_secondDensityCoeff A)
  have hlim2 : Tendsto (fun c : ℝ => ∫ x in orthantIic c, secondDensityCoeff A x) atTop
      (𝓝 0) := by
    have hfun : (fun c : ℝ => ∫ x in orthantIic c, secondDensityCoeff A x) =
        fun c => Phi c ^ m * ((1 - sigma c) ^ 2 * frobSq A / 4 -
          (q c) ^ 2 * (1 - sigma c) * rowSumSq A / 2 +
          (q c) ^ 4 * (entrySum A) ^ 2 / 8) := by
      funext c
      rw [integral_orthant_secondDensityCoeff_moment hZ c,
        quadDensityCoeffMoment_truncGauss hA hZ (one_sub_sigma c), one_sub_sigma c]
      ring
    rw [hfun]
    exact tendsto_second_orthant_expression (frobSq A) (rowSumSq A) (entrySum A)
  exact tendsto_nhds_unique hlim1 hlim2

#print axioms integral_orthant_firstDensityCoeff_zeroDiagonal
#print axioms integral_firstDensityCoeff_zero
#print axioms integral_orthant_secondDensityCoeff_moment
#print axioms integral_orthant_secondDensityCoeff_factor
#print axioms integral_secondDensityCoeff_zero

end SimplexFull.Covariance
