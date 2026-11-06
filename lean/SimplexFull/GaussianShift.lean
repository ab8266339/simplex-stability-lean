import Mathlib.Algebra.Order.Chebyshev
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Distributions.Gaussian.CharFun
import SimplexFull.Decoder
import SimplexFull.GaussianMaps
import SimplexFull.GeometryBase

/-!
Independent common Gaussian shift.

For `κ ≥ 0` and `σ : ℝ`, the law of `κ • x + (σ * z) • 1` under
`(multivariateGaussian 0 G).prod (gaussianReal 0 1)` is
`multivariateGaussian 0 (κ² • G + σ² • 1)`, when `G` is positive semidefinite.
The coordinate maximum adds the same constant, so the exponential moment factors
by the scalar Gaussian mgf `exp((λ σ)² / 2)`. If `κ² + σ² = 1`, this is the
identity `Pc(κ² G + σ² J, λ) = Pc(G, λ κ)`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Finset Matrix
open scoped RealInnerProductSpace

namespace SimplexFull

variable {m : ℕ}

/-- The all-ones vector in Euclidean space. -/
def onesEuclid (m : ℕ) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 fun _ : Fin m ↦ (1 : ℝ)

@[simp] lemma onesEuclid_apply (m : ℕ) (i : Fin m) : onesEuclid m i = 1 := rfl

/-- Linear map `(x, z) ↦ κ • x + z • (σ • 1)`. -/
def shiftCLM {m : ℕ} (κ σ : ℝ) :
    EuclideanSpace ℝ (Fin m) × ℝ →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  κ • ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin m)) ℝ +
    (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin m)) ℝ).smulRight (σ • onesEuclid m)

theorem shiftCLM_apply {m : ℕ} (κ σ : ℝ) (x : EuclideanSpace ℝ (Fin m)) (z : ℝ) :
    shiftCLM κ σ (x, z) = κ • x + (σ * z) • onesEuclid m := by
  ext i
  simp [shiftCLM, _root_.add_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', PiLp.add_apply, PiLp.smul_apply,
    onesEuclid_apply, smul_eq_mul]
  ring

lemma posSemidef_onesMatrix : (Geometry.onesMatrix m).PosSemidef := by
  have hform : Geometry.onesMatrix m =
      vecMulVec (fun _ : Fin m ↦ (1 : ℝ)) (fun _ : Fin m ↦ (1 : ℝ)) := by
    ext i j
    simp [Geometry.onesMatrix, vecMulVec_apply]
  rw [hform]
  simpa using posSemidef_vecMulVec_self_star (fun _ : Fin m ↦ (1 : ℝ))

lemma posSemidef_shift (G : Matrix (Fin m) (Fin m) ℝ) (hG : G.PosSemidef) (κ σ : ℝ) :
    (κ ^ 2 • G + σ ^ 2 • Geometry.onesMatrix m).PosSemidef :=
  (hG.smul (sq_nonneg κ)).add (posSemidef_onesMatrix.smul (sq_nonneg σ))

lemma inner_onesEuclid (t : EuclideanSpace ℝ (Fin m)) :
    ⟪onesEuclid m, t⟫ = ∑ i, t i := by
  simp [PiLp.inner_apply, onesEuclid_apply]

lemma mulVec_onesMatrix (x : Fin m → ℝ) :
    Geometry.onesMatrix m *ᵥ x = fun _ ↦ ∑ i, x i := by
  ext i
  simp [Geometry.onesMatrix, mulVec, dotProduct]

lemma dot_onesMatrix (x : Fin m → ℝ) :
    x ⬝ᵥ Geometry.onesMatrix m *ᵥ x = (∑ i, x i) ^ 2 := by
  rw [mulVec_onesMatrix]
  simp only [dotProduct]
  rw [← Finset.sum_mul]
  ring

lemma dot_smul_vec (c : ℝ) (A : Matrix (Fin m) (Fin m) ℝ) (t : EuclideanSpace ℝ (Fin m)) :
    (c • t) ⬝ᵥ A *ᵥ (c • t) = c ^ 2 * (t ⬝ᵥ A *ᵥ t) := by
  simp only [WithLp.ofLp_smul, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

lemma dot_smul_matrix (c : ℝ) (A : Matrix (Fin m) (Fin m) ℝ) (t : EuclideanSpace ℝ (Fin m)) :
    t ⬝ᵥ (c • A) *ᵥ t = c * (t ⬝ᵥ A *ᵥ t) := by
  rw [smul_mulVec, dotProduct_smul, smul_eq_mul]

lemma dot_add_matrix (A B : Matrix (Fin m) (Fin m) ℝ) (t : EuclideanSpace ℝ (Fin m)) :
    t ⬝ᵥ (A + B) *ᵥ t = t ⬝ᵥ A *ᵥ t + t ⬝ᵥ B *ᵥ t := by
  rw [add_mulVec, dotProduct_add]

lemma quadForm_shift (κ σ : ℝ) (G : Matrix (Fin m) (Fin m) ℝ)
    (t : EuclideanSpace ℝ (Fin m)) :
    t ⬝ᵥ (κ ^ 2 • G + σ ^ 2 • Geometry.onesMatrix m) *ᵥ t =
      (κ • t) ⬝ᵥ G *ᵥ (κ • t) + (σ * ⟪onesEuclid m, t⟫) ^ 2 := by
  rw [dot_add_matrix, dot_smul_matrix, dot_smul_matrix, dot_smul_vec, dot_onesMatrix,
    inner_onesEuclid]
  ring

lemma charFun_centered (G : Matrix (Fin m) (Fin m) ℝ) (hG : G.PosSemidef)
    (t : EuclideanSpace ℝ (Fin m)) :
    charFun (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) G) t =
      Complex.exp (-(t ⬝ᵥ G *ᵥ t) / 2) := by
  rw [charFun_multivariateGaussian hG]
  simp
  ring_nf

lemma charFun_stdNormal (t : ℝ) :
    charFun (gaussianReal 0 1) t = Complex.exp (-(t ^ 2) / 2) := by
  rw [charFun_gaussianReal]
  congr 1
  simp only [mul_zero, zero_mul, NNReal.coe_one, Complex.ofReal_zero, Complex.ofReal_one,
    sub_eq_add_neg, one_mul, neg_div]
  ring_nf

/-- Law of `κ x + σ z 1` when `x ∼ N(0, G)` is independent of `z ∼ N(0, 1)`. -/
theorem map_shiftCLM_eq_multivariateGaussian (G : Matrix (Fin m) (Fin m) ℝ)
    (hG : G.PosSemidef) (κ σ : ℝ) :
    ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) G).prod (gaussianReal 0 1)).map
        (shiftCLM κ σ) =
      multivariateGaussian 0 (κ ^ 2 • G + σ ^ 2 • Geometry.onesMatrix m) := by
  set Gshift := κ ^ 2 • G + σ ^ 2 • Geometry.onesMatrix m
  have hGshift : Gshift.PosSemidef := posSemidef_shift G hG κ σ
  set μ : Measure (EuclideanSpace ℝ (Fin m) × ℝ) :=
    (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) G).prod (gaussianReal 0 1)
  haveI : IsProbabilityMeasure (μ.map (shiftCLM κ σ)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  apply Measure.ext_of_charFun
  ext t
  rw [charFun_apply, integral_map (by fun_prop) (by fun_prop)]
  have hinner : ∀ (x : EuclideanSpace ℝ (Fin m)) (z : ℝ),
      ⟪shiftCLM κ σ (x, z), t⟫ = ⟪x, κ • t⟫ + z * (σ * ⟪onesEuclid m, t⟫) := by
    intro x z
    rw [shiftCLM_apply, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      real_inner_smul_right]
    ring
  have hsplit : ∀ p : EuclideanSpace ℝ (Fin m) × ℝ,
      Complex.exp (⟪shiftCLM κ σ p, t⟫ * Complex.I) =
        Complex.exp (⟪p.1, κ • t⟫ * Complex.I) *
          Complex.exp ((p.2 * (σ * ⟪onesEuclid m, t⟫)) * Complex.I) := by
    rintro ⟨x, z⟩
    rw [hinner x z, Complex.ofReal_add, add_mul, Complex.exp_add]
    congr 1
    simp [Complex.ofReal_mul]
  simp_rw [hsplit]
  have hmul := integral_prod_mul
    (fun x : EuclideanSpace ℝ (Fin m) ↦ Complex.exp (⟪x, κ • t⟫ * Complex.I))
    (fun z : ℝ ↦ Complex.exp ((z * (σ * ⟪onesEuclid m, t⟫)) * Complex.I))
    (μ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) G)
    (ν := gaussianReal 0 1)
  rw [hmul]
  have hsecond :
      ∫ z : ℝ, Complex.exp ((z * (σ * ⟪onesEuclid m, t⟫)) * Complex.I) ∂gaussianReal 0 1 =
        charFun (gaussianReal 0 1) (σ * ⟪onesEuclid m, t⟫) := by
    rw [charFun_apply]
    congr
    ext z
    simp [RCLike.inner_apply, Complex.ofReal_mul]
    ring_nf
  rw [← charFun_apply, hsecond, charFun_centered G hG (κ • t), charFun_stdNormal,
    charFun_centered Gshift hGshift t, ← Complex.exp_add]
  congr 1
  rw [quadForm_shift]
  simp only [Complex.ofReal_add]
  have hsq : (Complex.ofReal (σ * ⟪onesEuclid m, t⟫)) ^ 2 =
      Complex.ofReal (σ ^ 2 * ⟪onesEuclid m, t⟫ ^ 2) := by
    rw [← Complex.ofReal_pow]
    congr 1
    ring_nf
  rw [hsq, Complex.ofReal_pow, hsq, ← add_div, ← neg_add]
  simp only [WithLp.ofLp_smul]

lemma isHermitian_centering : (Geometry.centering m).IsHermitian := by
  ext i j
  simp [Geometry.centering, Geometry.onesMatrix, Matrix.conjTranspose_apply, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.one_apply, eq_comm, star_trivial]

lemma dot_centering (x : Fin m → ℝ) :
    x ⬝ᵥ Geometry.centering m *ᵥ x = ∑ i, x i ^ 2 - (m : ℝ)⁻¹ * (∑ i, x i) ^ 2 := by
  rw [Geometry.centering, sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul,
    one_mulVec, dot_onesMatrix]
  simp [dotProduct, sq]

/-- Score inner products of a configuration are `N(0, gram)`. -/
theorem gaussian_score_law_gram {d : ℕ} (X : Geometry.Config m d) :
    (stdGaussian (EuclideanSpace ℝ (Fin d))).map (scoreMap X) =
      multivariateGaussian 0 (Geometry.gram X) := by
  simpa [Geometry.gram] using gaussian_score_law X

variable [NeZero m]

lemma alpha_nonneg : 0 ≤ Geometry.alpha m := by
  unfold Geometry.alpha
  apply div_nonneg
  · have hm : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne m)
    linarith
  · exact_mod_cast (NeZero.pos m).le

/-- Adding a constant to every coordinate adds that constant to the maximum. -/
theorem maxCoord_add_const (x : EuclideanSpace ℝ (Fin m)) (c : ℝ) :
    maxCoord (x + c • onesEuclid m) = maxCoord x + c := by
  unfold maxCoord
  apply le_antisymm
  · rw [sup'_le_iff]
    intro i hi
    have hi' : (x + c • onesEuclid m) i = x i + c := by
      simp [PiLp.add_apply, PiLp.smul_apply, onesEuclid_apply]
    rw [hi']
    have hle : x i ≤ univ.sup' univNonempty (fun j ↦ x j) := le_sup' _ hi
    linarith
  · obtain ⟨i, hi, hx⟩ := exists_mem_eq_sup' univNonempty fun j ↦ x j
    have hi' : (x + c • onesEuclid m) i = x i + c := by
      simp [PiLp.add_apply, PiLp.smul_apply, onesEuclid_apply]
    calc
      univ.sup' univNonempty (fun j ↦ x j) + c = x i + c := by rw [hx]
      _ = (x + c • onesEuclid m) i := by rw [hi']
      _ ≤ univ.sup' univNonempty (fun j ↦ (x + c • onesEuclid m) j) := le_sup' _ hi

/-- Nonnegative scaling passes through the coordinate maximum. -/
theorem maxCoord_smul_nonneg {κ : ℝ} (hκ : 0 ≤ κ) (x : EuclideanSpace ℝ (Fin m)) :
    maxCoord (κ • x) = κ * maxCoord x := by
  unfold maxCoord
  apply le_antisymm
  · rw [sup'_le_iff]
    intro i hi
    rw [PiLp.smul_apply]
    exact mul_le_mul_of_nonneg_left (le_sup' (fun j ↦ x j) hi) hκ
  · obtain ⟨i, hi, hx⟩ := exists_mem_eq_sup' univNonempty fun j ↦ x j
    calc
      κ * univ.sup' univNonempty (fun j ↦ x j) = κ * x i := by rw [hx]
      _ = (κ • x) i := by simp [PiLp.smul_apply]
      _ ≤ univ.sup' univNonempty (fun j ↦ (κ • x) j) := le_sup' _ hi

/-- `max(κ x + σ z 1) = κ max(x) + σ z` for `κ ≥ 0`. -/
theorem maxCoord_commonShift {κ : ℝ} (hκ : 0 ≤ κ) (σ z : ℝ)
    (x : EuclideanSpace ℝ (Fin m)) :
    maxCoord (κ • x + (σ * z) • onesEuclid m) = κ * maxCoord x + σ * z := by
  rw [maxCoord_add_const, maxCoord_smul_nonneg hκ]

theorem maxCoord_shiftCLM {κ : ℝ} (hκ : 0 ≤ κ) (σ : ℝ)
    (x : EuclideanSpace ℝ (Fin m)) (z : ℝ) :
    maxCoord (shiftCLM κ σ (x, z)) = κ * maxCoord x + σ * z := by
  rw [shiftCLM_apply, maxCoord_commonShift hκ]

/-- Exponential moment of the shifted maximum factors by `exp((λ σ)² / 2)`. -/
theorem integral_exp_maxCoord_commonShift (G : Matrix (Fin m) (Fin m) ℝ)
    (hG : G.PosSemidef) {κ : ℝ} (hκ : 0 ≤ κ) (σ lam : ℝ) :
    (∫ x, Real.exp (lam * maxCoord x)
        ∂multivariateGaussian 0 (κ ^ 2 • G + σ ^ 2 • Geometry.onesMatrix m)) =
      Real.exp ((lam * σ) ^ 2 / 2) *
        ∫ x, Real.exp ((lam * κ) * maxCoord x) ∂multivariateGaussian 0 G := by
  rw [← map_shiftCLM_eq_multivariateGaussian G hG κ σ]
  rw [integral_map (by fun_prop)
    (((continuous_maxCoord.measurable.const_mul lam).exp).aestronglyMeasurable)]
  have hpoint : ∀ p : EuclideanSpace ℝ (Fin m) × ℝ,
      Real.exp (lam * maxCoord (shiftCLM κ σ p)) =
        Real.exp ((lam * κ) * maxCoord p.1) * Real.exp ((lam * σ) * p.2) := by
    rintro ⟨x, z⟩
    rw [maxCoord_shiftCLM hκ]
    have hmul : lam * (κ * maxCoord x + σ * z) =
        (lam * κ) * maxCoord x + (lam * σ) * z := by ring
    rw [hmul, Real.exp_add]
  simp_rw [hpoint]
  have hmul := integral_prod_mul
    (fun x : EuclideanSpace ℝ (Fin m) ↦ Real.exp ((lam * κ) * maxCoord x))
    (fun z : ℝ ↦ Real.exp ((lam * σ) * z))
    (μ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) G)
    (ν := gaussianReal 0 1)
  rw [hmul]
  have hmgf := congr_fun (mgf_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : NNReal))) (lam * σ)
  simp only [mgf, id_eq, zero_mul, zero_add, NNReal.coe_one, one_mul] at hmgf
  rw [hmgf, mul_comm]

/-- If `κ² + σ² = 1` and `κ ≥ 0`, the success probability only rescales `λ`. -/
theorem decodingSuccess_commonShift (G : Matrix (Fin m) (Fin m) ℝ) (hG : G.PosSemidef)
    {κ σ : ℝ} (hκ : 0 ≤ κ) (hquad : κ ^ 2 + σ ^ 2 = 1) (lam : ℝ) :
    decodingSuccess (κ ^ 2 • G + σ ^ 2 • Geometry.onesMatrix m) lam =
      decodingSuccess G (lam * κ) := by
  unfold decodingSuccess
  rw [integral_exp_maxCoord_commonShift G hG hκ σ lam]
  have hexp : Real.exp (-(lam ^ 2) / 2) * Real.exp ((lam * σ) ^ 2 / 2) =
      Real.exp (-((lam * κ) ^ 2) / 2) := by
    rw [← Real.exp_add]
    congr 1
    have hσ : σ ^ 2 = 1 - κ ^ 2 := by linarith
    calc
      -(lam ^ 2) / 2 + (lam * σ) ^ 2 / 2
          = -(lam ^ 2) / 2 + (lam ^ 2 * σ ^ 2) / 2 := by ring
      _ = -(lam ^ 2) / 2 + (lam ^ 2 * (1 - κ ^ 2)) / 2 := by rw [hσ]
      _ = -((lam * κ) ^ 2) / 2 := by ring
  calc
    Real.exp (-(lam ^ 2) / 2) / (m : ℝ) *
        (Real.exp ((lam * σ) ^ 2 / 2) *
          ∫ x, Real.exp ((lam * κ) * maxCoord x) ∂multivariateGaussian 0 G) =
        (Real.exp (-(lam ^ 2) / 2) * Real.exp ((lam * σ) ^ 2 / 2)) / (m : ℝ) *
          ∫ x, Real.exp ((lam * κ) * maxCoord x) ∂multivariateGaussian 0 G := by ring
    _ = Real.exp (-((lam * κ) ^ 2) / 2) / (m : ℝ) *
          ∫ x, Real.exp ((lam * κ) * maxCoord x) ∂multivariateGaussian 0 G := by
      rw [hexp]

/-- Normal-configuration scaling: `σ = sqrt(1 - κ²)` for `κ ∈ [0, 1]`. -/
theorem decodingSuccess_normalScale (G : Matrix (Fin m) (Fin m) ℝ) (hG : G.PosSemidef)
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (lam : ℝ) :
    decodingSuccess (κ ^ 2 • G + (1 - κ ^ 2) • Geometry.onesMatrix m) lam =
      decodingSuccess G (lam * κ) := by
  have hnn : 0 ≤ 1 - κ ^ 2 := by nlinarith
  have hquad : κ ^ 2 + (Real.sqrt (1 - κ ^ 2)) ^ 2 = 1 := by
    rw [Real.sq_sqrt hnn]
    ring
  simpa [Real.sq_sqrt hnn] using decodingSuccess_commonShift G hG hκ0 hquad lam

/-- Independence covariance `R = α G + J / m`, with `κ = sqrt α` and `σ = 1 / sqrt m`. -/
theorem decodingSuccess_independenceCov (G : Matrix (Fin m) (Fin m) ℝ) (hG : G.PosSemidef)
    (lam : ℝ) :
    decodingSuccess (Geometry.alpha m • G + (m : ℝ)⁻¹ • Geometry.onesMatrix m) lam =
      decodingSuccess G (lam * Real.sqrt (Geometry.alpha m)) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast NeZero.pos m
  set κ : ℝ := Real.sqrt (Geometry.alpha m)
  set σ : ℝ := 1 / Real.sqrt (m : ℝ)
  have hκ : 0 ≤ κ := Real.sqrt_nonneg _
  have hσsq : σ ^ 2 = (m : ℝ)⁻¹ := by
    unfold σ
    rw [div_pow, one_pow, Real.sq_sqrt hmpos.le]
    field_simp
  have hκsq : κ ^ 2 = Geometry.alpha m := Real.sq_sqrt alpha_nonneg
  have hquad : κ ^ 2 + σ ^ 2 = 1 := by
    rw [hκsq, hσsq, Geometry.alpha]
    field_simp
    ring
  have hmatrix : κ ^ 2 • G + σ ^ 2 • Geometry.onesMatrix m =
      Geometry.alpha m • G + (m : ℝ)⁻¹ • Geometry.onesMatrix m := by
    rw [hκsq, hσsq]
  simpa [hmatrix, κ] using decodingSuccess_commonShift G hG hκ hquad lam

theorem posSemidef_centering : (Geometry.centering m).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg isHermitian_centering fun x ↦ ?_
  rw [star_trivial, dot_centering]
  have hcs : (∑ i, x i) ^ 2 ≤ (m : ℝ) * ∑ i, x i ^ 2 := by
    simpa [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
      (sq_sum_le_card_mul_sum_sq (s := univ) (f := x))
  have hm : (0 : ℝ) < m := by exact_mod_cast NeZero.pos m
  have hdiv : (m : ℝ)⁻¹ * (∑ i, x i) ^ 2 ≤ ∑ i, x i ^ 2 := by
    rw [inv_mul_le_iff₀ hm]
    exact hcs
  linarith

theorem simplexGram_posSemidef : (Geometry.simplexGram m).PosSemidef :=
  posSemidef_centering.smul (inv_nonneg.mpr alpha_nonneg)

/-- Simplex normal configuration: `Pc(κ² G_Δ + (1-κ²) J, λ) = Pc(G_Δ, λ κ)`. -/
theorem decodingSuccess_simplex_normal {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (lam : ℝ) :
    decodingSuccess
        (κ ^ 2 • Geometry.simplexGram m + (1 - κ ^ 2) • Geometry.onesMatrix m) lam =
      decodingSuccess (Geometry.simplexGram m) (lam * κ) :=
  decodingSuccess_normalScale _ simplexGram_posSemidef hκ0 hκ1 lam

#print axioms shiftCLM_apply
#print axioms maxCoord_commonShift
#print axioms map_shiftCLM_eq_multivariateGaussian
#print axioms integral_exp_maxCoord_commonShift
#print axioms decodingSuccess_commonShift
#print axioms decodingSuccess_normalScale
#print axioms decodingSuccess_independenceCov
#print axioms simplexGram_posSemidef
#print axioms decodingSuccess_simplex_normal

end SimplexFull
