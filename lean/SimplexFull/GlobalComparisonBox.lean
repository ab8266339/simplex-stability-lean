import SimplexFull.GlobalComparisonFactors
noncomputable section
open MeasureTheory Set WeakSimplex ProbabilityTheory
open scoped ENNReal Matrix BigOperators
namespace SimplexFull.GlobalComparison
open Rotation

theorem tilt_weights_lower {m : ℕ} (a M : Fin m → ℝ) {A beta : ℝ}
    (ha : ∀ i, 0 ≤ a i) (haA : ∀ i, a i ≤ A)
    (hM : ∀ i, 0 < M i) (hM1 : ∀ i, M i ≤ 1)
    (hb : 0 < beta) (u : Coord m)
    (hu : u ∈ symmetricRectangle (fun _ => beta / Real.sqrt 2)) :
    Real.exp (-(m : ℝ)*A*beta) ≤
      ∏ i, (M i)⁻¹^2 * Real.exp (Real.sqrt 2*a i*u i) := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have he : 0 ≤ beta / Real.sqrt 2 := (div_pos hb hs).le
  have hi (i : Fin m) : 1 ≤ (M i)⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ (hM i)]
    simpa using hM1 i
  have hw (i : Fin m) : Real.exp (-A*beta) ≤
      (M i)⁻¹^2 * Real.exp (Real.sqrt 2*a i*u i) := by
    have h1 := mul_le_mul_of_nonneg_left (hu i).1 (ha i)
    have h2 := mul_le_mul_of_nonneg_right (haA i) he
    have h3 : -A*(beta/Real.sqrt 2) ≤ a i*u i := by nlinarith
    have h4 := mul_le_mul_of_nonneg_left h3 hs.le
    have hid : Real.sqrt 2 * (-A*(beta/Real.sqrt 2)) = -A*beta := by
      field_simp <;> ring
    rw [hid] at h4
    have hex : Real.exp (-A*beta) ≤ Real.exp (Real.sqrt 2*a i*u i) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hsq : 1 ≤ (M i)⁻¹^2 := by nlinarith [hi i]
    exact hex.trans (by nlinarith [Real.exp_pos (Real.sqrt 2*a i*u i)])
  have hp := Finset.prod_le_prod (s := Finset.univ) (fun i _ => (Real.exp_pos (-A*beta)).le)
    (fun i _ => hw i)
  have hx : (Real.exp (-A*beta))^m = Real.exp (-(m : ℝ)*A*beta) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, hx] using hp

theorem fixed_radii_bounds {m : ℕ} (b : Fin m → ℝ) {beta B : ℝ}
    (hlo : ∀ i, beta ≤ b i) (hhi : ∀ i, b i ≤ B) (u : Coord m)
    (hu : u ∈ symmetricRectangle (fun _ => beta / Real.sqrt 2)) :
    (∀ i, beta / Real.sqrt 2 ≤ Real.sqrt 2*b i-u i) ∧
    (∀ i, Real.sqrt 2*b i-u i ≤ Real.sqrt 2*B+beta/Real.sqrt 2) := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have he : Real.sqrt 2*beta = 2*(beta/Real.sqrt 2) := by
    field_simp
    rw [hsq]
    ring
  constructor
  · intro i
    have hm := mul_le_mul_of_nonneg_left (hlo i) hs.le
    have hh := (hu i).2
    linarith
  · intro i
    have hm := mul_le_mul_of_nonneg_left (hhi i) hs.le
    have hh := (hu i).1
    linarith

theorem central_box_mass_lower {m : ℕ} (hm : 2 ≤ m)
    (R : Matrix (Fin m) (Fin m) ℝ) (hR : IsCorrelation R) {ell : ℝ} (hell : 0 < ell) :
    (centralMass ell)^m ≤
      (multivariateGaussian (0 : Coord m) R).real (symmetricRectangle (fun _ => ell)) := by
  have hg := GlobalRectangle.symmetricRectangle_gap hm R hR.1 hR.2 (fun _ => ell)
    hell (fun _ => le_rfl) (fun _ => le_rfl)
  have hk := (GlobalRectangle.rectangleK_pos hm (T:=ell) hell).le
  have hd : 0 ≤ ∑ i, ∑ j, ((R-1) i j)^2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hnn := mul_nonneg hk hd
  have hp : (∏ _i : Fin m, gaussianReal 0 1 (Icc (-ell) ell)).toReal =
      (centralMass ell)^m := by
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ENNReal.toReal_pow]
    rw [GlobalBivariate.slab_toReal_eq hell.le]
    rfl
  rw [hp] at hg
  exact sub_nonneg.mp (hnn.trans hg)

#print axioms tilt_weights_lower
#print axioms fixed_radii_bounds
#print axioms central_box_mass_lower
end SimplexFull.GlobalComparison
