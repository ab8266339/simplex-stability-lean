import SimplexFull.Orthant
import SimplexFull.GaussianPolynomial
import SimplexFull.LayerCake

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace SimplexFull.Covariance

theorem tendsto_integral_sublevel_atTop {X : Type*} [MeasurableSpace X]
    {mu : Measure X} {u g : X → ℝ} (hu : Measurable u) (hg : Integrable g mu) :
    Tendsto (fun c : ℝ => ∫ x in {x | u x ≤ c}, g x ∂mu) atTop (𝓝 (∫ x, g x ∂mu)) := by
  have hs : (⋃ c : ℝ, {x | u x ≤ c}) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact ⟨u x, le_rfl⟩
  have hmono : Monotone (fun c : ℝ => {x | u x ≤ c}) := by
    intro a b hab x hx
    exact hx.trans hab
  have ht := tendsto_setIntegral_of_monotone (fun c => measurableSet_le hu measurable_const)
    hmono hg.integrableOn
  simpa only [hs, Measure.restrict_univ] using ht

theorem tendsto_integral_orthant_atTop {m : ℕ} [NeZero m]
    {g : EuclideanSpace ℝ (Fin m) → ℝ} (hg : Integrable g) :
    Tendsto (fun c : ℝ => ∫ x in {x | ∀ i, x i ≤ c}, g x) atTop (𝓝 (∫ x, g x)) := by
  simpa only [SimplexFull.maxCoord_le_iff] using
    tendsto_integral_sublevel_atTop SimplexFull.measurable_maxCoord hg

theorem tendsto_Phi_atTop_one_orthant : Tendsto Phi atTop (𝓝 1) := by
  have ht := tendsto_integral_sublevel_atTop (u := fun x : ℝ => x) measurable_id integrable_phi
  change Tendsto (fun c : ℝ => ∫ x in Iic c, phi x) atTop (𝓝 1)
  convert ht using 1
  · funext c; congr 1
  · rw [integral_phi_eq_one]

theorem tendsto_q_atTop_zero_orthant : Tendsto q atTop (𝓝 0) := by
  have ht := tendsto_phi_atTop_zero.div tendsto_Phi_atTop_one_orthant (by norm_num : (1:ℝ) ≠ 0)
  change Tendsto (fun c => phi c / Phi c) atTop (𝓝 0)
  convert ht using 1
  · funext c; rfl
  · norm_num

theorem tendsto_sigma_atTop_one_orthant : Tendsto sigma atTop (𝓝 1) := by
  have ht := tendsto_id_mul_phi_atTop_zero.div tendsto_Phi_atTop_one_orthant
    (by norm_num : (1:ℝ) ≠ 0)
  have htq := tendsto_q_atTop_zero_orthant.pow 2
  have he : sigma = fun c => 1 - (c*phi c)/Phi c - (q c)^2 := by
    ext c
    unfold sigma h q
    ring
  rw [he]
  simpa using (tendsto_const_nhds.sub ht).sub htq

#print axioms tendsto_integral_orthant_atTop
#print axioms tendsto_sigma_atTop_one_orthant

theorem Phi_pow_mul_q_sq {m : ℕ} (hm : 2 ≤ m) (c : ℝ) :
    Phi c^m*(q c)^2 = phi c^2*Phi c^(m-2) := by
  have he : Phi c^m = Phi c^(m-2)*Phi c^2 := by
    rw [← pow_add, Nat.sub_add_cancel hm]
  rw [he]
  unfold q
  have hp := (Phi_pos c).ne'
  field_simp

theorem gaussian_second_factor {m : ℕ} (hm : 2 ≤ m) (c F R T : ℝ) :
    Phi c^m*((1-sigma c)^2*F/4-(q c)^2*(1-sigma c)*R/2+(q c)^4*T^2/8) =
      phi c^2*Phi c^(m-2)*((h c)^2*F/4-q c*h c*R/2+(q c)^2*(T/2)^2/2) := by
  rw [← Phi_pow_mul_q_sq hm c]
  unfold sigma
  ring

theorem tendsto_first_orthant_expression {m : ℕ} (T : ℝ) :
    Tendsto (fun c => Phi c^m*(q c)^2*T/2) atTop (𝓝 0) := by
  have ht := ((tendsto_Phi_atTop_one_orthant.pow m).mul
    (tendsto_q_atTop_zero_orthant.pow 2)).mul_const T
  simpa using ht.div_const 2

theorem tendsto_second_orthant_expression {m : ℕ} (F R T : ℝ) :
    Tendsto (fun c => Phi c^m*((1-sigma c)^2*F/4-
      (q c)^2*(1-sigma c)*R/2+(q c)^4*T^2/8)) atTop (𝓝 0) := by
  have hs : Tendsto (fun c => 1-sigma c) atTop (𝓝 0) := by
    simpa using tendsto_sigma_atTop_one_orthant.const_sub 1
  have hf := ((hs.pow 2).mul_const F).div_const 4
  have hr := (((tendsto_q_atTop_zero_orthant.pow 2).mul hs).mul_const R).div_const 2
  have ht := ((tendsto_q_atTop_zero_orthant.pow 4).mul_const (T^2)).div_const 8
  simpa using (tendsto_Phi_atTop_one_orthant.pow m).mul ((hf.sub hr).add ht)

end SimplexFull.Covariance