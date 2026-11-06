import SimplexFull.DensityCalculus
import SimplexFull.GaussianDomination
import SimplexFull.SmoothIntegral
import Mathlib.Analysis.Normed.Operator.NormedSpace
import SimplexFull.GaussianLocalBounds
import SimplexFull.Decoder
import Mathlib.Analysis.Calculus.FDeriv.Mul
noncomputable section
open MeasureTheory Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace Topology
namespace SimplexFull.Covariance
variable {m : ℕ}
local instance : NormedAddCommGroup (Matrix (Fin m) (Fin m) ℝ →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (Matrix (Fin m) (Fin m) ℝ →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (Matrix (Fin m) (Fin m) ℝ →L[ℝ] (Matrix (Fin m) (Fin m) ℝ →L[ℝ] ℝ)) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (Matrix (Fin m) (Fin m) ℝ →L[ℝ] (Matrix (Fin m) (Fin m) ℝ →L[ℝ] ℝ)) :=
  ContinuousLinearMap.toNormedSpace
def quadLinear (x : EuclideanSpace ℝ (Fin m)) : Matrix (Fin m) (Fin m) ℝ →ₗ[ℝ] ℝ where
  toFun M := quad M x
  map_add' M N := quad_add M N x
  map_smul' c M := by simpa using quad_smul c M x

def quadCLM (x : EuclideanSpace ℝ (Fin m)) : Matrix (Fin m) (Fin m) ℝ →L[ℝ] ℝ :=
  (quadLinear x).mkContinuous (‖x‖^2) (fun M => by
    simpa only [quadLinear, LinearMap.coe_mk, AddHom.coe_mk, Real.norm_eq_abs, mul_comm] using quad_abs_le_norm M x)
@[simp] theorem quadCLM_apply (x : EuclideanSpace ℝ (Fin m)) (M : Matrix (Fin m) (Fin m) ℝ) :
    quadCLM x M = quad M x := rfl
 theorem quadCLM_norm_le (x : EuclideanSpace ℝ (Fin m)) : ‖quadCLM x‖ ≤ ‖x‖^2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (sq_nonneg ‖x‖)
  intro M
  simpa only [quadCLM_apply, Real.norm_eq_abs, mul_comm] using quad_abs_le_norm M x

def precisionLinear (x : EuclideanSpace ℝ (Fin m)) : Matrix (Fin m) (Fin m) ℝ →L[ℝ] ℝ :=
  (-1/2 : ℝ) • quadCLM x
variable [NeZero m]
def precisionKernel (lam : ℝ) (M : Matrix (Fin m) (Fin m) ℝ)
    (x : EuclideanSpace ℝ (Fin m)) : ℝ :=
  Real.exp (lam * maxCoord x) * Real.exp (precisionLinear x M)
def precisionD1 (lam : ℝ) (M : Matrix (Fin m) (Fin m) ℝ)
    (x : EuclideanSpace ℝ (Fin m)) := precisionKernel lam M x • precisionLinear x
def precisionD2 (lam : ℝ) (M : Matrix (Fin m) (Fin m) ℝ)
    (x : EuclideanSpace ℝ (Fin m)) :=
  precisionKernel lam M x • (precisionLinear x).smulRight (precisionLinear x)

theorem hasFDerivAt_precisionKernel (lam : ℝ) (M : Matrix (Fin m) (Fin m) ℝ)
    (x : EuclideanSpace ℝ (Fin m)) :
    HasFDerivAt (fun S => precisionKernel lam S x) (precisionD1 lam M x) M := by
  have h := ((precisionLinear x).hasFDerivAt (x := M)).exp.const_mul (Real.exp (lam * maxCoord x))
  convert! h using 1
  ext A
  simp [precisionD1, precisionKernel, ContinuousLinearMap.smul_apply]
  ring

theorem hasFDerivAt_precisionD1 (lam : ℝ) (M : Matrix (Fin m) (Fin m) ℝ)
    (x : EuclideanSpace ℝ (Fin m)) :
    HasFDerivAt (fun S => precisionD1 lam S x) (precisionD2 lam M x) M := by
  have h := (hasFDerivAt_precisionKernel lam M x).smul_const (precisionLinear x)
  convert! h using 1
  ext A B
  simp [precisionD2, precisionD1, ContinuousLinearMap.smulRight_apply]
  ring

theorem continuous_precisionD2_parameter (lam : ℝ) (x : EuclideanSpace ℝ (Fin m)) :
    Continuous (fun M => precisionD2 lam M x) := by
  unfold precisionD2 precisionKernel
  exact (continuous_const.mul (Real.continuous_exp.comp (precisionLinear x).continuous)).smul continuous_const

theorem precisionLinear_norm_le (x : EuclideanSpace ℝ (Fin m)) :
    ‖precisionLinear x‖ ≤ ‖x‖^2 := by
  have hq := quadCLM_norm_le x
  rw [precisionLinear, norm_smul]
  norm_num
  nlinarith [norm_nonneg (quadCLM x), sq_nonneg ‖x‖]

theorem precisionKernel_nonneg (lam : ℝ) (M : Matrix (Fin m) (Fin m) ℝ)
    (x : EuclideanSpace ℝ (Fin m)) : 0 ≤ precisionKernel lam M x :=
  (mul_pos (Real.exp_pos _) (Real.exp_pos _)).le

theorem precisionKernel_bound (lam : ℝ) {M : Matrix (Fin m) (Fin m) ℝ}
    (hM : ‖M-1‖ ≤ 1/2) (x : EuclideanSpace ℝ (Fin m)) :
    precisionKernel lam M x ≤ Real.exp (lam * maxCoord x) * Real.exp (-‖x‖^2/4) := by
  have hq := quad_lower_of_close hM x
  unfold precisionKernel
  gcongr
  simp only [precisionLinear, _root_.smul_apply, smul_eq_mul, quadCLM_apply]
  linarith

theorem precisionD1_bound (lam : ℝ) {M : Matrix (Fin m) (Fin m) ℝ}
    (hM : ‖M-1‖ ≤ 1/2) (x : EuclideanSpace ℝ (Fin m)) :
    ‖precisionD1 lam M x‖ ≤ ‖x‖^2 * Real.exp (lam * maxCoord x) * Real.exp (-‖x‖^2/4) := by
  rw [precisionD1, norm_smul, Real.norm_eq_abs, abs_of_nonneg (precisionKernel_nonneg lam M x)]
  calc
    _ ≤ (Real.exp (lam * maxCoord x) * Real.exp (-‖x‖^2/4)) * ‖x‖^2 :=
      mul_le_mul (precisionKernel_bound lam hM x) (precisionLinear_norm_le x) (norm_nonneg _) (by positivity)
    _ = _ := by ring



theorem precisionD2_bound (lam : ℝ) {M : Matrix (Fin m) (Fin m) ℝ}
    (hM : ‖M-1‖ ≤ 1/2) (x : EuclideanSpace ℝ (Fin m)) :
    ‖precisionD2 lam M x‖ ≤ ‖x‖^4 * Real.exp (lam * maxCoord x) * Real.exp (-‖x‖^2/4) := by
  rw [precisionD2, norm_smul, Real.norm_eq_abs, abs_of_nonneg (precisionKernel_nonneg lam M x),
    ContinuousLinearMap.norm_smulRight_apply]
  have hq := precisionLinear_norm_le x
  have hq2 : ‖precisionLinear x‖ * ‖precisionLinear x‖ ≤ ‖x‖^4 := by
    calc
      _ ≤ (‖x‖^2) * (‖x‖^2) := mul_le_mul hq hq (norm_nonneg _) (sq_nonneg _)
      _ = _ := by ring
  calc
    _ ≤ (Real.exp (lam * maxCoord x) * Real.exp (-‖x‖^2/4)) * ‖x‖^4 :=
      mul_le_mul (precisionKernel_bound lam hM x) hq2 (by positivity) (by positivity)
    _ = _ := by ring

theorem quadCLM_eq_sum (x : EuclideanSpace ℝ (Fin m)) :
    quadCLM x = ∑ i, ∑ j, (x i * x j) • (entryLinearMap i j).toContinuousLinearMap := by
  ext M
  simp [quad, entryLinearMap, mul_assoc, mul_left_comm, mul_comm]

theorem continuous_quadCLM : Continuous (quadCLM : EuclideanSpace ℝ (Fin m) → _) := by
  have heq : (quadCLM : EuclideanSpace ℝ (Fin m) → _) =
      fun x => ∑ i, ∑ j, (x i * x j) • (entryLinearMap i j).toContinuousLinearMap :=
    funext quadCLM_eq_sum
  rw [heq]
  fun_prop

theorem continuous_precisionLinear : Continuous (precisionLinear : EuclideanSpace ℝ (Fin m) → _) :=
  continuous_const.smul continuous_quadCLM

theorem continuous_precisionKernel (lam : ℝ) (M : Matrix (Fin m) (Fin m) ℝ) :
    Continuous (precisionKernel lam M) := by
  unfold precisionKernel
  exact (Real.continuous_exp.comp (continuous_const.mul continuous_maxCoord)).mul
    (Real.continuous_exp.comp (continuous_precisionLinear.clm_apply continuous_const))

theorem continuous_precisionD1 (lam : ℝ) (M : Matrix (Fin m) (Fin m) ℝ) :
    Continuous (precisionD1 lam M) :=
  (continuous_precisionKernel lam M).smul continuous_precisionLinear

theorem continuous_precisionD2 (lam : ℝ) (M : Matrix (Fin m) (Fin m) ℝ) :
    Continuous (precisionD2 lam M) := by
  unfold precisionD2
  apply (continuous_precisionKernel lam M).smul
  exact ((ContinuousLinearMap.smulRightL ℝ (Matrix (Fin m) (Fin m) ℝ) (Matrix (Fin m) (Fin m) ℝ →L[ℝ] ℝ)).continuous.comp continuous_precisionLinear).clm_apply continuous_precisionLinear

def precisionBound (n : ℕ) (lam : ℝ) (x : EuclideanSpace ℝ (Fin m)) : ℝ :=
  ‖x‖^n * Real.exp (lam * maxCoord x) * Real.exp (-‖x‖^2/4)

theorem integrable_precisionBound (n : ℕ) (lam : ℝ) : Integrable (precisionBound (m := m) n lam) := by
  have hi := integrable_norm_pow_exp_max_mul_gaussian (m := m) n lam (c := 1/4) (by norm_num)
  have heq : (fun x : EuclideanSpace ℝ (Fin m) => ‖x‖^n * Real.exp (lam * maxCoord x) *
      Real.exp (-(1/4 : ℝ)*‖x‖^2)) = precisionBound n lam := by
    funext x
    unfold precisionBound
    congr 2
    ring
  rwa [heq] at hi

theorem integrable_precisionKernel (lam : ℝ) {M : Matrix (Fin m) (Fin m) ℝ}
    (hM : ‖M-1‖ ≤ 1/2) : Integrable (precisionKernel lam M) := by
  refine (integrable_precisionBound (m := m) 0 lam).mono'
    (continuous_precisionKernel lam M).aestronglyMeasurable (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (precisionKernel_nonneg lam M x)]
  simpa [precisionBound] using precisionKernel_bound lam hM x

def precisionIntegral (lam : ℝ) (M : Matrix (Fin m) (Fin m) ℝ) : ℝ :=
  ∫ x, precisionKernel lam M x

theorem precisionIntegral_regular (lam : ℝ) :
    ContDiffOn ℝ 2 (precisionIntegral (m := m) lam) (Metric.ball 1 (1/2)) ∧
    (∀ M ∈ Metric.ball 1 (1/2), fderiv ℝ (precisionIntegral (m := m) lam) M = ∫ x, precisionD1 lam M x) ∧
    (∀ M ∈ Metric.ball 1 (1/2), fderiv ℝ (fderiv ℝ (precisionIntegral (m := m) lam)) M = ∫ x, precisionD2 lam M x) := by
  have hb {M : Matrix (Fin m) (Fin m) ℝ} (hM : M ∈ Metric.ball 1 (1/2)) : ‖M-1‖ ≤ 1/2 :=
    (show ‖M-1‖ < 1/2 by simpa only [Metric.mem_ball, dist_eq_norm] using hM).le
  have hh := SmoothIntegral.contDiffOn_integral
    (F0 := precisionKernel lam) (F1 := precisionD1 lam) (F2 := precisionD2 lam)
    (s := Metric.ball 1 (1/2)) (b1 := precisionBound 2 lam) (b2 := precisionBound 4 lam)
    Metric.isOpen_ball
    (fun x M _ => hasFDerivAt_precisionKernel lam M x)
    (fun x M _ => hasFDerivAt_precisionD1 lam M x)
    (fun M _ => (continuous_precisionKernel lam M).aestronglyMeasurable)
    (fun M _ => (continuous_precisionD1 lam M).aestronglyMeasurable)
    (fun M _ => (continuous_precisionD2 lam M).aestronglyMeasurable)
    (fun M hM => integrable_precisionKernel lam (hb hM))
    (ae_of_all _ fun x M hM => precisionD1_bound lam (hb hM) x)
    (integrable_precisionBound 2 lam)
    (ae_of_all _ fun x M hM => precisionD2_bound lam (hb hM) x)
    (integrable_precisionBound 4 lam)
    (fun x => (continuous_precisionD2_parameter lam x).continuousOn)
  exact hh



theorem contDiffOn_precisionIntegral (lam : ℝ) :
    ContDiffOn ℝ 2 (precisionIntegral (m := m) lam) (Metric.ball 1 (1/2)) :=
  (precisionIntegral_regular lam).1

theorem fderiv_precisionIntegral (lam : ℝ) {M : Matrix (Fin m) (Fin m) ℝ}
    (hM : M ∈ Metric.ball 1 (1/2)) :
    fderiv ℝ (precisionIntegral (m := m) lam) M = ∫ x, precisionD1 lam M x :=
  (precisionIntegral_regular lam).2.1 M hM

theorem second_fderiv_precisionIntegral (lam : ℝ) {M : Matrix (Fin m) (Fin m) ℝ}
    (hM : M ∈ Metric.ball 1 (1/2)) :
    fderiv ℝ (fderiv ℝ (precisionIntegral (m := m) lam)) M = ∫ x, precisionD2 lam M x :=
  (precisionIntegral_regular lam).2.2 M hM
#print axioms precisionIntegral_regular
#print axioms contDiffOn_precisionIntegral
#print axioms fderiv_precisionIntegral
#print axioms second_fderiv_precisionIntegral
end SimplexFull.Covariance

