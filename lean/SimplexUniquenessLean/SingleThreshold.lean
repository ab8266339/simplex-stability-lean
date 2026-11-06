import SimplexUniquenessLean.StrictProduct
import SimplexUniquenessLean.SingularWitnesses

/-!
# Single-threshold strictness

Theorem 1 of the paper. If `R ≠ I` is a correlation matrix with `R - J/m ⪰ 0`,
possibly singular, and `X ∼ N(0, R)`, then `P {X ≤ c·1} > Φ(c)^m` at every
finite threshold `c`. Consequently equality at a single finite threshold holds
if and only if `R = I`. The positive-definite case is also stated separately,
together with the assembly lemma `lowerOrthant_gt_iid_of_witnesses`, which
needs only a positive-semidefinite covariance.
-/

noncomputable section

namespace SimplexUniqueness

open MeasureTheory Set WeakSimplex ProbabilityTheory
open scoped ENNReal Matrix BigOperators InnerProductSpace

namespace Assembly

-- Adapted from weak-simplex-conjecture-lean (Mulgund),
-- Orthant/PositiveDefiniteConditional.lean, MIT
private def adaptiveEndpointSet
    {m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ} {c : ℝ}
    (w : AdaptiveWitnesses R c) : Set (Coord m) :=
  {x | ∀ i, x i ≤ H (w.s i)}

private def adaptiveEndpointIndicator
    {m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ} {c : ℝ}
    (w : AdaptiveWitnesses R c) (x : Coord m) : ℝ :=
  (adaptiveEndpointSet w).indicator (fun _ ↦ 1) x

private theorem measurableSet_adaptiveEndpointSet
    {m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ} {c : ℝ}
    (w : AdaptiveWitnesses R c) :
    MeasurableSet (adaptiveEndpointSet w) := by
  rw [adaptiveEndpointSet, Set.setOf_forall]
  exact MeasurableSet.iInter fun i ↦
    measurableSet_le (by fun_prop) measurable_const

private theorem measurable_adaptiveEndpointIndicator
    {m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ} {c : ℝ}
    (w : AdaptiveWitnesses R c) :
    Measurable (adaptiveEndpointIndicator w) := by
  exact measurable_const.indicator (measurableSet_adaptiveEndpointSet w)

private theorem centeredTiltedHalfLine_le (s x : ℝ) :
    centeredTiltedHalfLine s x ≤ Real.exp (r s * H s) := by
  by_cases hx : x ≤ H s
  · simp only [centeredTiltedHalfLine, tiltedHalfLine, Set.mem_Iic, hx,
      Set.indicator_of_mem]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hx (r_pos s).le)
  · simp [centeredTiltedHalfLine, tiltedHalfLine, hx, Real.exp_nonneg]

private theorem adaptiveProduct_nonneg
    {m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ} {c : ℝ}
    (w : AdaptiveWitnesses R c) (x : Coord m) :
    0 ≤ ∏ i, centeredTiltedHalfLine (w.s i) (x i) := by
  exact Finset.prod_nonneg fun i _ ↦ centeredTiltedHalfLine_nonneg (w.s i) (x i)

private theorem measurable_adaptiveProduct
    {m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ} {c : ℝ}
    (w : AdaptiveWitnesses R c) :
    Measurable (fun x : Coord m ↦
      ∏ i, centeredTiltedHalfLine (w.s i) (x i)) := by
  have hmeas : ∀ S : Finset (Fin m),
      Measurable (fun x : Coord m ↦
        ∏ i ∈ S, centeredTiltedHalfLine (w.s i) (x i)) := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact measurable_const
    | @insert i S hi ih =>
        simpa only [Finset.prod_insert hi, Function.comp_apply] using
          ((measurable_centeredTiltedHalfLine (w.s i)).comp (by
            simpa only [EuclideanSpace.coe_proj] using
              (EuclideanSpace.proj (𝕜 := ℝ) i).measurable)).mul ih
  simpa using hmeas Finset.univ

private theorem integrable_adaptiveProduct
    {m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ} {c : ℝ}
    (w : AdaptiveWitnesses R c) :
    Integrable (fun x : Coord m ↦ ∏ i, centeredTiltedHalfLine (w.s i) (x i))
      (multivariateGaussian 0 R) := by
  apply Integrable.of_bound (C := ∏ i, Real.exp (r (w.s i) * H (w.s i)))
  · exact (measurable_adaptiveProduct w).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (adaptiveProduct_nonneg w x)]
    exact Finset.prod_le_prod
      (fun i _ ↦ centeredTiltedHalfLine_nonneg (w.s i) (x i))
      (fun i _ ↦ centeredTiltedHalfLine_le (w.s i) (x i))

private theorem adaptiveProduct_eq_exp_mul_indicator
    {m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ} {c : ℝ}
    (w : AdaptiveWitnesses R c) (x : Coord m) :
    (∏ i, centeredTiltedHalfLine (w.s i) (x i)) =
      Real.exp ⟪w.a, x⟫_ℝ * adaptiveEndpointIndicator w x := by
  classical
  by_cases hx : x ∈ adaptiveEndpointSet w
  · have hxi : ∀ i, x i ≤ H (w.s i) := hx
    rw [adaptiveEndpointIndicator, Set.indicator_of_mem hx, mul_one]
    calc
      (∏ i, centeredTiltedHalfLine (w.s i) (x i)) =
          ∏ i, Real.exp (r (w.s i) * x i) := by
        apply Finset.prod_congr rfl
        intro i _
        simp [centeredTiltedHalfLine, tiltedHalfLine, hxi i]
      _ = Real.exp (∑ i, r (w.s i) * x i) :=
        (Real.exp_sum Finset.univ (fun i ↦ r (w.s i) * x i)).symm
      _ = Real.exp ⟪w.a, x⟫_ℝ := by
        congr 1
        rw [PiLp.inner_apply]
        apply Finset.sum_congr rfl
        intro i _
        simp [w.a_eq_r, mul_comm]
  · obtain ⟨i, hi⟩ : ∃ i, ¬x i ≤ H (w.s i) := by
      simpa only [adaptiveEndpointSet, Set.mem_setOf_eq] using not_forall.mp hx
    rw [adaptiveEndpointIndicator, Set.indicator_of_notMem hx, mul_zero]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [centeredTiltedHalfLine, tiltedHalfLine, hi]

private theorem lintegral_adaptiveIndicator_shift
    {m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ} {c : ℝ}
    (w : AdaptiveWitnesses R c) :
    (∫⁻ x, ENNReal.ofReal
        (adaptiveEndpointIndicator w (x + matrixMul R w.a))
      ∂multivariateGaussian 0 R) =
      (multivariateGaussian 0 R) (lowerOrthant c) := by
  calc
    (∫⁻ x, ENNReal.ofReal
          (adaptiveEndpointIndicator w (x + matrixMul R w.a))
        ∂multivariateGaussian 0 R) =
        ∫⁻ x, (lowerOrthant c).indicator (fun _ ↦ (1 : ℝ≥0∞)) x
          ∂multivariateGaussian 0 R := by
      congr 1
      funext x
      by_cases hx : x ∈ lowerOrthant c
      · have hshift := (w.shift_le_H_iff x).2 hx
        have hmem : x + matrixMul R w.a ∈ adaptiveEndpointSet w := hshift
        rw [adaptiveEndpointIndicator, Set.indicator_of_mem hmem,
          Set.indicator_of_mem hx]
        norm_num
      · have hshift : ¬∀ i, (x + matrixMul R w.a) i ≤ H (w.s i) := by
          exact mt (w.shift_le_H_iff x).1 hx
        have hmem : x + matrixMul R w.a ∉ adaptiveEndpointSet w := hshift
        rw [adaptiveEndpointIndicator, Set.indicator_of_notMem hmem,
          Set.indicator_of_notMem hx]
        norm_num
    _ = (multivariateGaussian 0 R) (lowerOrthant c) :=
      lintegral_indicator_one (measurableSet_lowerOrthant c)

private theorem lintegral_weighted_adaptiveIndicator
    {m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ} {c : ℝ}
    (w : AdaptiveWitnesses R c) :
    (∫⁻ x, ENNReal.ofReal
        (Real.exp (⟪w.a, x⟫_ℝ - qform R w.a / 2) *
          adaptiveEndpointIndicator w x)
      ∂multivariateGaussian 0 R) =
      ENNReal.ofReal
        (Real.exp (-qform R w.a / 2) *
          ∫ x, ∏ i, centeredTiltedHalfLine (w.s i) (x i)
            ∂multivariateGaussian 0 R) := by
  let g : Coord m → ℝ := fun x ↦
    ∏ i, centeredTiltedHalfLine (w.s i) (x i)
  have hg_nonneg : ∀ x, 0 ≤ g x := adaptiveProduct_nonneg w
  have hg_int : Integrable g (multivariateGaussian 0 R) := integrable_adaptiveProduct w
  have hg_meas : Measurable g := measurable_adaptiveProduct w
  calc
    (∫⁻ x, ENNReal.ofReal
          (Real.exp (⟪w.a, x⟫_ℝ - qform R w.a / 2) *
            adaptiveEndpointIndicator w x)
        ∂multivariateGaussian 0 R) =
        ∫⁻ x, ENNReal.ofReal (Real.exp (-qform R w.a / 2)) *
          ENNReal.ofReal (g x) ∂multivariateGaussian 0 R := by
      congr 1
      funext x
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _),
        show Real.exp (-qform R w.a / 2) * g x =
            Real.exp (⟪w.a, x⟫_ℝ - qform R w.a / 2) *
              adaptiveEndpointIndicator w x by
          dsimp only [g]
          rw [adaptiveProduct_eq_exp_mul_indicator]
          rw [← mul_assoc, ← Real.exp_add]
          congr 2
          ring]
    _ = ENNReal.ofReal (Real.exp (-qform R w.a / 2)) *
        ∫⁻ x, ENNReal.ofReal (g x) ∂multivariateGaussian 0 R := by
      rw [lintegral_const_mul]
      exact hg_meas.ennreal_ofReal
    _ = ENNReal.ofReal (Real.exp (-qform R w.a / 2)) *
        ENNReal.ofReal (∫ x, g x ∂multivariateGaussian 0 R) := by
      rw [ofReal_integral_eq_lintegral_ofReal hg_int (ae_of_all _ hg_nonneg)]
    _ = ENNReal.ofReal
        (Real.exp (-qform R w.a / 2) *
          ∫ x, ∏ i, centeredTiltedHalfLine (w.s i) (x i)
            ∂multivariateGaussian 0 R) := by
      rw [ENNReal.ofReal_mul (Real.exp_nonneg _)]

private theorem adaptiveProduct_mass_eq
    {m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ} {c : ℝ}
    (w : AdaptiveWitnesses R c) :
    (∏ i, ∫ x, centeredTiltedHalfLine (w.s i) x ∂gaussianReal 0 1) =
      Real.exp (⟪w.a, w.a⟫_ℝ / 2) * ∏ i, normalCDF (w.s i) := by
  simp_rw [integral_centeredTiltedHalfLine]
  rw [Finset.prod_mul_distrib, ← Real.exp_sum]
  congr 1
  rw [PiLp.inner_apply]
  congr 1
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [w.a_eq_r]
  simp

private theorem adaptiveValue_exp_bound
    {m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ} {c : ℝ}
    (w : AdaptiveWitnesses R c) :
    normalCDF c ^ m ≤
      Real.exp
        ((⟪w.a, w.a⟫_ℝ - ⟪w.a, matrixMul R w.a⟫_ℝ) / 2) *
        ∏ i, normalCDF (w.s i) := by
  have h := Real.exp_le_exp.mpr w.value_bound
  rw [Real.exp_add, Real.exp_sum] at h
  simp_rw [Real.exp_log (normalCDF_pos _)] at h
  have hc : Real.exp ((m : ℝ) * Real.log (normalCDF c)) = normalCDF c ^ m := by
    rw [show (m : ℝ) * Real.log (normalCDF c) =
        (m : ℕ) * Real.log (normalCDF c) by rfl,
      Real.exp_nat_mul, Real.exp_log (normalCDF_pos c)]
  rw [hc] at h
  simpa only [mul_comm] using h

/-- `H` is strictly positive. -/
theorem H_pos (s : ℝ) : 0 < H s := by
  have hnonneg : ∀ t : ℝ, 0 ≤ H t := by
    intro t
    by_cases ht : 0 ≤ t
    · exact add_nonneg ht (r_pos t).le
    · have ht' : 0 < -t := by linarith
      have hm := mills_upper (-t) ht'
      rw [neg_neg] at hm
      have hsym : normalPDF (-t) = normalPDF t := by
        simp [normalPDF, gaussianPDFReal]
      have hΦ := normalCDF_pos t
      have h1 := (le_div_iff₀ ht').1 hm
      rw [hsym] at h1
      have h2 : -t ≤ r t := by
        rw [r, le_div_iff₀ hΦ]; linarith
      unfold H; linarith
  have hmono : StrictMono H := by
    apply strictMono_of_deriv_pos
    intro x
    rw [(hasDerivAt_H x).deriv]
    exact H_deriv_pos x
  have := hmono (show s - 1 < s by linarith)
  have := hnonneg (s - 1)
  linarith

end Assembly

/-- Assembly: adaptive witnesses plus a strict centered product inequality at the witness factors
give strict lower-orthant comparison. Positive semidefinite `R` suffices. -/
theorem lowerOrthant_gt_iid_of_witnesses
    {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) (hR : R.PosSemidef) (c : ℝ)
    (w : AdaptiveWitnesses R c)
    (hprod : (∏ i, ∫ x, centeredTiltedHalfLine (w.s i) x ∂gaussianReal 0 1) <
      ∫ x, ∏ i, centeredTiltedHalfLine (w.s i) (x i) ∂multivariateGaussian (0 : Coord m) R) :
    (gaussianReal 0 1) (Iic c) ^ m < (multivariateGaussian (0 : Coord m) R) (lowerOrthant c) := by
  open Assembly in
  have hreal :
      normalCDF c ^ m <
        Real.exp (-qform R w.a / 2) *
          ∫ x, ∏ i, centeredTiltedHalfLine (w.s i) (x i)
            ∂multivariateGaussian 0 R := by
    calc
      normalCDF c ^ m ≤
          Real.exp
              ((⟪w.a, w.a⟫_ℝ - ⟪w.a, matrixMul R w.a⟫_ℝ) / 2) *
            ∏ i, normalCDF (w.s i) := adaptiveValue_exp_bound w
      _ = Real.exp (-qform R w.a / 2) *
          (Real.exp (⟪w.a, w.a⟫_ℝ / 2) *
            ∏ i, normalCDF (w.s i)) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        simp only [qform]
        ring
      _ = Real.exp (-qform R w.a / 2) *
          ∏ i, ∫ x, centeredTiltedHalfLine (w.s i) x
            ∂gaussianReal 0 1 := by
        rw [adaptiveProduct_mass_eq]
      _ < Real.exp (-qform R w.a / 2) *
          ∫ x, ∏ i, centeredTiltedHalfLine (w.s i) (x i)
            ∂multivariateGaussian 0 R :=
        mul_lt_mul_of_pos_left hprod (Real.exp_pos _)
  have hmeasure :
      (multivariateGaussian 0 R) (lowerOrthant c) =
        ENNReal.ofReal
          (Real.exp (-qform R w.a / 2) *
            ∫ x, ∏ i, centeredTiltedHalfLine (w.s i) (x i)
              ∂multivariateGaussian 0 R) := by
    calc
      (multivariateGaussian 0 R) (lowerOrthant c) =
          ∫⁻ x, ENNReal.ofReal
              (adaptiveEndpointIndicator w (x + matrixMul R w.a))
            ∂multivariateGaussian 0 R :=
        (lintegral_adaptiveIndicator_shift w).symm
      _ = ∫⁻ x, ENNReal.ofReal
            (Real.exp (⟪w.a, x⟫_ℝ - qform R w.a / 2) *
              adaptiveEndpointIndicator w x)
          ∂multivariateGaussian 0 R := by
        exact (integral_exp_inner_sub_quadratic_mul hR w.a
          (measurable_adaptiveEndpointIndicator w)).symm
      _ = ENNReal.ofReal
          (Real.exp (-qform R w.a / 2) *
            ∫ x, ∏ i, centeredTiltedHalfLine (w.s i) (x i)
              ∂multivariateGaussian 0 R) :=
        lintegral_weighted_adaptiveIndicator w
  rw [hmeasure, ← normalCDF_eq_measure_Iic,
    ← ENNReal.ofReal_pow (normalCDF_pos c).le]
  exact (ENNReal.ofReal_lt_ofReal_iff
    (lt_of_le_of_lt (pow_nonneg (normalCDF_pos c).le _) hreal)).2 hreal

/-- Centered strict product inequality at adaptive witness factors, positive-definite case. -/
theorem centeredProduct_gt_of_posDef
    {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) (hR : IsCorrelation R) (hpd : R.PosDef)
    (hne : R ≠ 1) (s : Fin m → ℝ) :
    (∏ i, ∫ x, centeredTiltedHalfLine (s i) x ∂gaussianReal 0 1) <
      ∫ x, ∏ i, centeredTiltedHalfLine (s i) (x i) ∂multivariateGaussian (0 : Coord m) R :=
  tiltedHalfLine_product_gt_of_posDef R hR hpd hne (fun i ↦ r (s i)) (fun i ↦ H (s i))
    (fun _ ↦ r_pos _) (fun _ ↦ Assembly.H_pos _)
    (fun i ↦ integral_mul_centeredTiltedHalfLine (s i))

/-- Centered strict product inequality at adaptive witness factors. Singular `R` is allowed. -/
theorem centeredProduct_gt
    {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) (hR : IsCorrelation R)
    (hne : R ≠ 1) (s : Fin m → ℝ) :
    (∏ i, ∫ x, centeredTiltedHalfLine (s i) x ∂gaussianReal 0 1) <
      ∫ x, ∏ i, centeredTiltedHalfLine (s i) (x i) ∂multivariateGaussian (0 : Coord m) R :=
  tiltedHalfLine_product_gt R hR hne (fun i ↦ r (s i)) (fun i ↦ H (s i))
    (fun _ ↦ r_pos _) (fun _ ↦ Assembly.H_pos _)
    (fun i ↦ integral_mul_centeredTiltedHalfLine (s i))

/-- Theorem 1 (single-threshold strictness), positive-definite case. -/
theorem lowerOrthant_gt_iid_of_posDef
    {m : ℕ} (hm : 0 < m)
    (R : Matrix (Fin m) (Fin m) ℝ)
    (hR : IsWeakSimplexCov R) (hpd : R.PosDef) (hne : R ≠ 1)
    (c : ℝ) :
    (gaussianReal 0 1) (Iic c) ^ m <
      (multivariateGaussian (0 : Coord m) R) (lowerOrthant c) := by
  obtain ⟨w⟩ := exists_adaptiveWitnesses hm R hpd hR.2 c
  exact lowerOrthant_gt_iid_of_witnesses R hR.1.1 c w
    (centeredProduct_gt_of_posDef R hR.1 hpd hne w.s)

/-- Theorem 1, equality form, positive-definite case: equality at one finite
threshold forces `R = I`. -/
theorem eq_one_of_lowerOrthant_eq_iid_at_of_posDef
    {m : ℕ} (hm : 0 < m)
    (R : Matrix (Fin m) (Fin m) ℝ)
    (hR : IsWeakSimplexCov R) (hpd : R.PosDef)
    (c : ℝ)
    (heq : (multivariateGaussian (0 : Coord m) R) (lowerOrthant c) =
      (gaussianReal 0 1) (Iic c) ^ m) :
    R = 1 := by
  by_contra hne
  exact (lowerOrthant_gt_iid_of_posDef hm R hR hpd hne c).ne' heq

/-- Theorem 1 (single-threshold strictness). Singular `R` is allowed. -/
theorem lowerOrthant_gt_iid
    {m : ℕ} (hm : 0 < m)
    (R : Matrix (Fin m) (Fin m) ℝ)
    (hR : IsWeakSimplexCov R) (hne : R ≠ 1)
    (c : ℝ) :
    (gaussianReal 0 1) (Iic c) ^ m <
      (multivariateGaussian (0 : Coord m) R) (lowerOrthant c) := by
  obtain ⟨w⟩ := exists_adaptiveWitnesses_of_isWeakSimplexCov hm R hR c
  exact lowerOrthant_gt_iid_of_witnesses R hR.1.1 c w (centeredProduct_gt R hR.1 hne w.s)

/-- Theorem 1, equality form: equality at one finite threshold forces `R = I`.
Singular `R` is allowed. -/
theorem eq_one_of_lowerOrthant_eq_iid_at
    {m : ℕ} (hm : 0 < m)
    (R : Matrix (Fin m) (Fin m) ℝ)
    (hR : IsWeakSimplexCov R)
    (c : ℝ)
    (heq : (multivariateGaussian (0 : Coord m) R) (lowerOrthant c) =
      (gaussianReal 0 1) (Iic c) ^ m) :
    R = 1 := by
  by_contra hne
  exact (lowerOrthant_gt_iid hm R hR hne c).ne' heq

-- Adapted from weak-simplex-conjecture-lean (Mulgund), Maxima/StochasticOrder.lean, MIT
/-- Independent coordinates attain the benchmark at every threshold. -/
theorem lowerOrthant_eq_iid_of_eq_one
    {m : ℕ} (c : ℝ) :
    (multivariateGaussian (0 : Coord m) (1 : Matrix (Fin m) (Fin m) ℝ)) (lowerOrthant c) =
      (gaussianReal 0 1) (Iic c) ^ m := by
  rw [multivariateGaussian_zero_one, ← map_pi_eq_stdGaussian]
  rw [Measure.map_apply (by fun_prop) (measurableSet_lowerOrthant c)]
  rw [show (WithLp.toLp 2) ⁻¹' lowerOrthant c =
      Set.pi Set.univ (fun _ : Fin m ↦ Set.Iic c) by
    ext x
    simp only [Set.mem_preimage, lowerOrthant, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ,
      true_implies, Set.mem_Iic]]
  rw [Measure.pi_pi]
  exact Fin.prod_const m ((gaussianReal 0 1) (Set.Iic c))

/-- Theorem 1, equivalence form: equality at one finite threshold holds if and only if
`R = I`. Singular `R` is allowed. -/
theorem lowerOrthant_eq_iid_at_iff
    {m : ℕ} (hm : 0 < m)
    (R : Matrix (Fin m) (Fin m) ℝ)
    (hR : IsWeakSimplexCov R)
    (c : ℝ) :
    (multivariateGaussian (0 : Coord m) R) (lowerOrthant c) =
        (gaussianReal 0 1) (Iic c) ^ m ↔
      R = 1 := by
  constructor
  · exact eq_one_of_lowerOrthant_eq_iid_at hm R hR c
  · rintro rfl
    exact lowerOrthant_eq_iid_of_eq_one c

end SimplexUniqueness
