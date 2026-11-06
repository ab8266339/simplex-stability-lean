import SimplexFull.GlobalBivariateCalculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

noncomputable section
open MeasureTheory Set Real Filter
open scoped Topology Interval
namespace SimplexFull.GlobalBivariate

def plackettRate (r a b : ℝ) : ℝ :=
  2/(Real.pi*sd r) * Real.exp (-(a^2+b^2)/(2*sd r^2)) *
    Real.sinh (r*a*b/sd r^2)

theorem phi_neg_eq (x : ℝ) : phi (-x)=phi x := by
  simp only [phi_eq_exp,neg_sq]

theorem corner_simultaneous_neg (r a b : ℝ) : corner r (-a) (-b)=corner r a b := by
  have hz : z r (-a) (-b) = -z r a b := by unfold z; ring
  simp [corner,hz,phi_neg_eq]

theorem corner_exp_split {r : ℝ} (hr : |r|<1) (a b : ℝ) :
    corner r a b = 1/(2*Real.pi*sd r) *
      Real.exp (-(a^2+b^2)/(2*sd r^2)+r*a*b/sd r^2) := by
  have hs := sd_sq hr
  have hn := ne_of_gt (sd_pos hr)
  have hpi : 0≤2*Real.pi := by positivity
  have he : -(z r a b)^2/2 + -(b^2)/2 =
      -(a^2+b^2)/(2*sd r^2)+r*a*b/sd r^2 := by
    unfold z
    field_simp
    nlinarith [hs]
  calc
    corner r a b = (Real.sqrt (2*Real.pi)^2*sd r)⁻¹ *
        Real.exp (-(z r a b)^2/2 + -(b^2)/2) := by
      unfold corner
      rw [phi_eq_exp,phi_eq_exp,Real.exp_add]
      ring
    _ = _ := by rw [Real.sq_sqrt hpi,he]; ring

theorem corners_eq_rate {r : ℝ} (hr : |r|<1) (a b : ℝ) :
    (corner r a b-corner r (-a) b) -
      (corner r a (-b)-corner r (-a) (-b)) = plackettRate r a b := by
  have hsym : corner r (-a) b = corner r a (-b) := by
    simpa using corner_simultaneous_neg r a (-b)
  rw [hsym,corner_simultaneous_neg]
  rw [corner_exp_split hr,corner_exp_split hr]
  unfold plackettRate
  simp only [neg_sq,Real.exp_add,Real.sinh_eq]
  rw [show r*a*(-b)/sd r^2=-(r*a*b/sd r^2) by ring]
  ring

theorem plackett {r : ℝ} (hr : |r|<1) (a b : ℝ) :
    HasDerivAt (fun s => rectangleIntegral s a b) (plackettRate r a b) r := by
  simpa only [corners_eq_rate hr] using plackett_corners hr a b

theorem plackettRate_nonneg {r : ℝ} (hr : |r|<1) (hr0 : 0≤r)
    {a b : ℝ} (ha : 0≤a) (hb : 0≤b) : 0≤plackettRate r a b := by
  unfold plackettRate
  have hs := (sd_pos hr).le
  have hu : 0≤r*a*b/sd r^2 := by positivity
  exact mul_nonneg (by positivity) (Real.sinh_nonneg_iff.mpr hu)

#print axioms plackett
#print axioms plackettRate_nonneg
end SimplexFull.GlobalBivariate

namespace SimplexFull.GlobalBivariate

theorem plackettRate_lower {r ell T a b : ℝ}
    (hr0 : 0≤r) (hrh : r≤1/2) (hell : 0<ell)
    (ha : ell≤a) (hb : ell≤b) (haT : a≤T) (hbT : b≤T) :
    (2*ell^2/Real.pi)*Real.exp (-4*T^2/3)*r ≤ plackettRate r a b := by
  have hr : |r|<1 := by rw [abs_of_nonneg hr0]; linarith
  have hs := sd_pos hr
  have hs2 := sd_sq hr
  have hslo : (3:ℝ)/4 ≤ sd r^2 := by nlinarith
  have hshi : sd r ≤ 1 := by nlinarith [sq_nonneg r]
  have hs2hi : sd r^2 ≤ 1 := by nlinarith [sq_nonneg r]
  have ha0 : 0≤a := le_trans hell.le ha
  have hb0 : 0≤b := le_trans hell.le hb
  have hT0 : 0≤T := le_trans ha0 haT
  have hsqab : a^2+b^2 ≤ 2*T^2 := by nlinarith
  have hexponent : -4*T^2/3 ≤ -(a^2+b^2)/(2*sd r^2) := by
    apply (le_div_iff₀ (by positivity : 0<2*sd r^2)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hslo (sq_nonneg T)]
  have hexp := Real.exp_le_exp.mpr hexponent
  have hfac : (2:ℝ)/Real.pi ≤ 2/(Real.pi*sd r) := by
    apply (div_le_div_iff₀ Real.pi_pos (mul_pos Real.pi_pos hs)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hshi Real.pi_pos.le]
  have hab : ell^2 ≤ a*b := by
    nlinarith [mul_le_mul ha hb hell.le ha0]
  have hu : r*ell^2 ≤ r*a*b/sd r^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hs)).mpr
    calc
      r*ell^2*(sd r)^2 ≤ r*ell^2 := mul_le_of_le_one_right (by positivity) hs2hi
      _ ≤ r*a*b := by nlinarith [mul_le_mul_of_nonneg_left hab hr0]
  have hu0 : 0≤r*a*b/sd r^2 := by positivity
  have hsin := hu.trans (Real.self_le_sinh_iff.mpr hu0)
  have hh := mul_le_mul
    (mul_le_mul hfac hexp (Real.exp_nonneg _) (by positivity))
    hsin (by positivity : 0≤r*ell^2) (by positivity)
  unfold plackettRate
  calc
    (2*ell^2/Real.pi)*Real.exp (-4*T^2/3)*r =
      2/Real.pi*Real.exp (-4*T^2/3)*(r*ell^2) := by ring
    _ ≤ _ := hh

theorem rectangleIntegral_monotone_nonneg {a b : ℝ} (ha : 0≤a) (hb : 0≤b) :
    MonotoneOn (fun r => rectangleIntegral r a b) (Ico 0 1) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ico 0 1)
  · intro r hr
    exact (plackett (by rw [abs_of_nonneg hr.1]; exact hr.2) a b).continuousAt.continuousWithinAt
  · intro r hr
    have hmem : r ∈ Ico (0:ℝ) 1 := interior_subset hr
    exact (plackett (by rw [abs_of_nonneg hmem.1]; exact hmem.2) a b).hasDerivWithinAt
  · intro r hr
    have hmem : r ∈ Ico (0:ℝ) 1 := interior_subset hr
    exact plackettRate_nonneg (by rw [abs_of_nonneg hmem.1]; exact hmem.2) hmem.1 ha hb

#print axioms plackettRate_lower
#print axioms rectangleIntegral_monotone_nonneg
end SimplexFull.GlobalBivariate

namespace SimplexFull.GlobalBivariate

theorem rectangleIntegral_even (r a b : ℝ) :
    rectangleIntegral (-r) a b = rectangleIntegral r a b := by
  have hf : conditional (-r) a = fun t => conditional r a (-t) := by
    ext t
    have hz (c : ℝ) : z (-r) c t = z r c (-t) := by
      unfold z sd
      simp only [neg_sq]
      congr 1 <;> ring
    simp [conditional,hz,phi_neg_eq]
  unfold rectangleIntegral
  rw [hf,intervalIntegral.integral_comp_neg]
  simp

theorem rectangleIntegral_small_gap {r ell T a b : ℝ}
    (hr0 : 0≤r) (hrh : r≤1/2) (hell : 0<ell)
    (ha : ell≤a) (hb : ell≤b) (haT : a≤T) (hbT : b≤T) :
    (ell^2/Real.pi)*Real.exp (-4*T^2/3)*r^2 ≤
      rectangleIntegral r a b-rectangleIntegral 0 a b := by
  let c := ell^2/Real.pi*Real.exp (-4*T^2/3)
  let g : ℝ→ℝ := fun x => rectangleIntegral x a b-c*x^2
  have hd (x : ℝ) (hx : x ∈ Icc (0:ℝ) (1/2)) :
      HasDerivAt g (plackettRate x a b-2*c*x) x := by
    have hxx : |x|<1 := by rw [abs_of_nonneg hx.1]; linarith [hx.2]
    convert! (plackett hxx a b).sub ((hasDerivAt_pow 2 x).const_mul c) using 1 <;> ring
  have hn (x : ℝ) (hx : x ∈ Icc (0:ℝ) (1/2)) :
      0≤plackettRate x a b-2*c*x := by
    apply sub_nonneg.mpr
    convert plackettRate_lower hx.1 hx.2 hell ha hb haT hbT using 1 <;> dsimp [c] <;> ring
  have hm : MonotoneOn g (Icc (0:ℝ) (1/2)) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hd x (interior_subset hx)).hasDerivWithinAt)
      (fun x hx => hn x (interior_subset hx))
  have hh := hm (by constructor <;> norm_num) ⟨hr0,hrh⟩ hr0
  change c*r^2 ≤ _
  dsimp [g] at hh
  nlinarith

theorem rectangleIntegral_nonneg_gap {r ell T a b : ℝ}
    (hr0 : 0≤r) (hr1 : r<1) (hell : 0<ell)
    (ha : ell≤a) (hb : ell≤b) (haT : a≤T) (hbT : b≤T) :
    ell^2/(4*Real.pi)*Real.exp (-4*T^2/3)*r^2 ≤
      rectangleIntegral r a b-rectangleIntegral 0 a b := by
  let c := ell^2/Real.pi*Real.exp (-4*T^2/3)
  have hc : 0≤c := by dsimp [c]; positivity
  change ell^2/(4*Real.pi)*Real.exp (-4*T^2/3)*r^2 ≤ _
  have he : ell^2/(4*Real.pi)*Real.exp (-4*T^2/3)*r^2 = c/4*r^2 := by dsimp [c]; ring
  rw [he]
  by_cases hrh : r≤1/2
  · have hh := rectangleIntegral_small_gap hr0 hrh hell ha hb haT hbT
    change c*r^2 ≤ _ at hh
    nlinarith [mul_nonneg hc (sq_nonneg r)]
  · have hhalf := rectangleIntegral_small_gap (r := (1:ℝ)/2) (by norm_num) (by norm_num)
      hell ha hb haT hbT
    change c*(1/2)^2 ≤ _ at hhalf
    have hmono := rectangleIntegral_monotone_nonneg (hell.le.trans ha) (hell.le.trans hb)
      (show (1:ℝ)/2 ∈ Ico 0 1 by constructor <;> norm_num) ⟨hr0,hr1⟩ (le_of_not_ge hrh)
    have hrsq : r^2 ≤ 1 := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hrsq hc
    nlinarith

theorem rectangleIntegral_gap {r ell T a b : ℝ}
    (hr : |r|<1) (hell : 0<ell)
    (ha : ell≤a) (hb : ell≤b) (haT : a≤T) (hbT : b≤T) :
    ell^2/(4*Real.pi)*Real.exp (-4*T^2/3)*r^2 ≤
      rectangleIntegral r a b-rectangleIntegral 0 a b := by
  have hh := rectangleIntegral_nonneg_gap (abs_nonneg r) hr hell ha hb haT hbT
  rw [sq_abs] at hh
  by_cases hr0 : 0≤r
  · simpa only [abs_of_nonneg hr0] using hh
  · simpa only [abs_of_neg (lt_of_not_ge hr0),rectangleIntegral_even] using hh

#print axioms rectangleIntegral_gap
end SimplexFull.GlobalBivariate
