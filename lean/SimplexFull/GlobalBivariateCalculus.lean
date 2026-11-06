import SimplexFull.GaussianBase
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory Set Real Filter
open scoped Topology Interval
namespace SimplexFull.GlobalBivariate

def sd (r : ℝ) : ℝ := Real.sqrt (1-r^2)
def z (r a t : ℝ) : ℝ := (a-r*t)/sd r
def corner (r a t : ℝ) : ℝ := phi (z r a t)*phi t/sd r
def conditional (r a t : ℝ) : ℝ := (Phi (z r a t)-Phi (z r (-a) t))*phi t
def conditionalD (r a t : ℝ) : ℝ :=
  (phi (z r a t)*(r*a-t)/sd r^3 -
   phi (z r (-a) t)*(r*(-a)-t)/sd r^3)*phi t
def rectangleIntegral (r a b : ℝ) : ℝ := ∫ t in (-b)..b, conditional r a t

theorem sd_pos {r : ℝ} (hr : |r|<1) : 0<sd r := by
  apply Real.sqrt_pos.2
  have := abs_lt.mp hr
  nlinarith
theorem sd_sq {r : ℝ} (hr : |r|<1) : sd r^2=1-r^2 := by
  apply Real.sq_sqrt
  have := abs_lt.mp hr
  nlinarith
theorem hasDerivAt_sd {r : ℝ} (hr : |r|<1) :
    HasDerivAt sd (-r/sd r) r := by
  have hd : HasDerivAt (fun s : ℝ => 1-s^2) (-(2*r)) r := by
    convert! (hasDerivAt_const r (1:ℝ)).sub (hasDerivAt_pow 2 r) using 1 <;> ring
  have hz : 1-r^2 ≠ 0 := by have := sd_sq hr; have := sd_pos hr; nlinarith
  convert! (hd.sqrt hz).congr_deriv (by dsimp [sd]; ring : -(2*r)/(2*Real.sqrt (1-r^2)) = -r/sd r) using 1

theorem hasDerivAt_z_param {r : ℝ} (hr : |r|<1) (a t : ℝ) :
    HasDerivAt (fun s => z s a t) ((r*a-t)/sd r^3) r := by
  have hn : HasDerivAt (fun s : ℝ => a-s*t) (-t) r := by
    convert! (hasDerivAt_const r a).sub ((hasDerivAt_id r).mul_const t) using 1 <;> simp
  convert! hn.div (hasDerivAt_sd hr) (ne_of_gt (sd_pos hr)) using 1
  have hs := sd_sq hr
  field_simp [ne_of_gt (sd_pos hr)]
  rw [hs]
  ring

theorem hasDerivAt_conditional_param {r : ℝ} (hr : |r|<1) (a t : ℝ) :
    HasDerivAt (fun s => conditional s a t) (conditionalD r a t) r := by
  convert! (((hasDerivAt_Phi (z r a t)).comp r (hasDerivAt_z_param hr a t)).sub
    ((hasDerivAt_Phi (z r (-a) t)).comp r (hasDerivAt_z_param hr (-a) t))).mul_const (phi t) using 1
  dsimp [conditionalD]
  ring

theorem hasDerivAt_corner_space {r : ℝ} (hr : |r|<1) (a t : ℝ) :
    HasDerivAt (corner r a) (phi (z r a t)*(r*a-t)/sd r^3*phi t) t := by
  have hz : HasDerivAt (z r a) (-r/sd r) t := by
    convert! ((hasDerivAt_const t a).sub ((hasDerivAt_id t).const_mul r)).div_const (sd r) using 1 <;> simp [z]
  convert! (((hasDerivAt_phi (z r a t)).comp t hz).mul (hasDerivAt_phi t)).div_const (sd r) using 1
  have hs := sd_sq hr
  have hn := ne_of_gt (sd_pos hr)
  dsimp [z]
  field_simp [ne_of_gt (sd_pos hr)]
  rw [hs]
  ring

#print axioms hasDerivAt_conditional_param
#print axioms hasDerivAt_corner_space
end SimplexFull.GlobalBivariate

namespace SimplexFull.GlobalBivariate
attribute [local fun_prop] continuous_phi continuous_Phi

theorem continuous_conditional (r a : ℝ) : Continuous (conditional r a) := by
  unfold conditional z
  fun_prop

theorem continuous_conditionalD (r a : ℝ) : Continuous (conditionalD r a) := by
  unfold conditionalD z
  fun_prop

theorem continuousAt_conditionalD_pair (a : ℝ) (p : ℝ × ℝ) (hp : |p.1|<1) :
    ContinuousAt (fun q : ℝ × ℝ => conditionalD q.1 a q.2) p := by
  have hn : sd p.1 ≠ 0 := ne_of_gt (sd_pos hp)
  have hs : ContinuousAt (fun q : ℝ × ℝ => sd q.1) p := by unfold sd; fun_prop
  have hz (c : ℝ) : ContinuousAt (fun q : ℝ × ℝ => z q.1 c q.2) p := by
    exact (by fun_prop : ContinuousAt (fun q : ℝ × ℝ => c-q.1*q.2) p).div hs hn
  have hpz (c : ℝ) : ContinuousAt (fun q : ℝ × ℝ => phi (z q.1 c q.2)) p :=
    continuous_phi.continuousAt.comp (hz c)
  have term (c : ℝ) : ContinuousAt
      (fun q : ℝ × ℝ => phi (z q.1 c q.2)*(q.1*c-q.2)/sd q.1^3) p :=
    ((hpz c).mul (by fun_prop)).div (hs.pow 3) (pow_ne_zero 3 hn)
  exact ((term a).sub (term (-a))).mul (continuous_phi.continuousAt.comp continuousAt_snd)

theorem hasDerivAt_rectangleIntegral {r : ℝ} (hr : |r|<1) (a b : ℝ) :
    HasDerivAt (fun s => rectangleIntegral s a b)
      (∫ t in (-b)..b, conditionalD r a t) r := by
  let u := (r-1)/2
  let v := (r+1)/2
  have hr' := abs_lt.mp hr
  have hur : u<r := by dsimp [u]; linarith
  have hrv : r<v := by dsimp [v]; linarith
  have huv (s : ℝ) (hs : s ∈ Icc u v) : |s|<1 := by
    rw [abs_lt]
    dsimp [u,v] at hs
    constructor <;> linarith [hs.1,hs.2]
  have hcont : ContinuousOn (fun p : ℝ × ℝ => conditionalD p.1 a p.2)
      (Icc u v ×ˢ uIcc (-b) b) := by
    intro p hp
    exact (continuousAt_conditionalD_pair a p (huv p.1 hp.1)).continuousWithinAt
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod isCompact_uIcc).exists_bound_of_continuousOn hcont
  have hh := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s t => conditional s a t) (F' := fun s t => conditionalD s a t)
    (bound := fun _ => C) (μ := volume) (a := -b) (b := b)
    (Icc_mem_nhds hur hrv)
    (Filter.Eventually.of_forall fun s => (continuous_conditional s a).aestronglyMeasurable)
    ((continuous_conditional r a).intervalIntegrable (-b) b)
    (continuous_conditionalD r a).aestronglyMeasurable
    (ae_of_all _ fun t ht s hs => hC (s,t) ⟨hs,uIoc_subset_uIcc ht⟩)
    (intervalIntegrable_const)
    (ae_of_all _ fun t _ s hs => hasDerivAt_conditional_param (huv s hs) a t)
  exact hh.2

theorem integral_conditionalD_eq_corners {r : ℝ} (hr : |r|<1) (a b : ℝ) :
    (∫ t in (-b)..b, conditionalD r a t) =
      (corner r a b - corner r (-a) b) -
      (corner r a (-b) - corner r (-a) (-b)) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t _
    convert! (hasDerivAt_corner_space hr a t).sub
      (hasDerivAt_corner_space hr (-a) t) using 1
    dsimp [conditionalD]
    ring
  · exact ((continuous_conditionalD r a).intervalIntegrable (-b) b)

theorem plackett_corners {r : ℝ} (hr : |r|<1) (a b : ℝ) :
    HasDerivAt (fun s => rectangleIntegral s a b)
      ((corner r a b - corner r (-a) b) -
       (corner r a (-b) - corner r (-a) (-b))) r := by
  simpa only [integral_conditionalD_eq_corners hr] using hasDerivAt_rectangleIntegral hr a b

#print axioms hasDerivAt_rectangleIntegral
#print axioms plackett_corners
end SimplexFull.GlobalBivariate
