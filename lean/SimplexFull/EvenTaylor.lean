import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Tactic
noncomputable section
open Filter Set
open scoped Topology Asymptotics
namespace SimplexFull.Taylor
lemma quadratic_remainder_isBigO {p : ℝ → ℝ} {a : ℝ} (hp : ContDiffAt ℝ 3 p a) :
    (fun x => p x-p a-deriv p a*(x-a)-deriv (deriv p) a/2*(x-a)^2)
      =O[𝓝 a] (fun x => (x-a)^3) := by
  obtain ⟨u,hu,hU⟩ := hp.contDiffOn (m:=3) le_rfl (by simp)
  obtain ⟨r,hr,hrU⟩ := Metric.mem_nhds_iff.mp hu
  have hOn : ContDiffOn ℝ 3 p (Metric.ball a r) := hU.mono hrU
  have hmem : a ∈ Metric.ball a r := Metric.mem_ball_self hr
  have hnhds : Metric.ball a r ∈ 𝓝 a := Metric.ball_mem_nhds a hr
  have hT := taylor_isLittleO (convex_ball a r) hmem hOn
  rw [nhdsWithin_eq_nhds.mpr hnhds] at hT
  have h1 : iteratedDerivWithin 1 p (Metric.ball a r) a=deriv p a := by
    rw [iteratedDerivWithin_eq_iteratedDeriv Metric.isOpen_ball.uniqueDiffOn
      (hp.of_le (m:=1) (by norm_num)) hmem]
    simp [iteratedDeriv_succ]
  have h2 : iteratedDerivWithin 2 p (Metric.ball a r) a=deriv (deriv p) a := by
    rw [iteratedDerivWithin_eq_iteratedDeriv Metric.isOpen_ball.uniqueDiffOn
      (hp.of_le (m:=2) (by norm_num)) hmem]
    simp [iteratedDeriv_succ]
  have h3 : iteratedDerivWithin 3 p (Metric.ball a r) a=iteratedDeriv 3 p a :=
    iteratedDerivWithin_eq_iteratedDeriv Metric.isOpen_ball.uniqueDiffOn hp hmem
  have hexp (x : ℝ) : taylorWithinEval p 3 (Metric.ball a r) a x=
      p a+deriv p a*(x-a)+deriv (deriv p) a/2*(x-a)^2+
        iteratedDeriv 3 p a/6*(x-a)^3 := by
    norm_num [taylorWithinEval_succ,taylor_within_zero_eval,h1,h2,h3]
    <;> ring
  have hthird : (fun x : ℝ => iteratedDeriv 3 p a/6*(x-a)^3)
      =O[𝓝 a] (fun x => (x-a)^3) :=
    (Asymptotics.isBigO_refl (fun x : ℝ => (x-a)^3) (𝓝 a)).const_mul_left _
  have heq : (fun x => p x-p a-deriv p a*(x-a)-deriv (deriv p) a/2*(x-a)^2) =
      (fun x => p x-taylorWithinEval p 3 (Metric.ball a r) a x+
        iteratedDeriv 3 p a/6*(x-a)^3) := by
    funext x
    rw [hexp]
    ring
  rw [heq]
  exact hT.isBigO.add hthird
#print axioms quadratic_remainder_isBigO

/-- A quadratic signal displacement converts a cubic Taylor bound into a true
sixth-order radius bound. The signal may be zero or negative. -/
theorem evenTaylor_isBigO {p : ℝ → ℝ} {lam m : ℝ} (hm : 0 < m)
    (hp : ContDiffAt ℝ 3 p lam) :
    (fun rho => p lam-p (lam*(1-rho^2/(2*m)))-
      (lam*deriv p lam/(2*m)*rho^2-lam^2*deriv (deriv p) lam/(8*m^2)*rho^4))
      =O[𝓝 0] (fun rho : ℝ => rho^6) := by
  have hlim : Tendsto (fun rho : ℝ => lam*(1-rho^2/(2*m))) (𝓝 0) (𝓝 lam) := by
    have hc : Continuous (fun rho : ℝ => lam*(1-rho^2/(2*m))) := by fun_prop
    simpa using hc.continuousAt.tendsto (x:=0)
  have hq := (quadratic_remainder_isBigO hp).comp_tendsto hlim
  simp only [Function.comp_def] at hq
  have hshift (rho : ℝ) : lam*(1-rho^2/(2*m))-lam=-(lam/(2*m))*rho^2 := by ring
  have heq : (fun rho => p lam-p (lam*(1-rho^2/(2*m)))-
      (lam*deriv p lam/(2*m)*rho^2-lam^2*deriv (deriv p) lam/(8*m^2)*rho^4)) =
      (fun rho => -(p (lam*(1-rho^2/(2*m)))-p lam-
        deriv p lam*(lam*(1-rho^2/(2*m))-lam)-
        deriv (deriv p) lam/2*(lam*(1-rho^2/(2*m))-lam)^2)) := by
    funext rho
    rw [hshift]
    field_simp [ne_of_gt hm]
    ring
  have heqR : (fun rho : ℝ => (lam*(1-rho^2/(2*m))-lam)^3) =
      (fun rho => (-(lam/(2*m)))^3*rho^6) := by
    funext rho
    rw [hshift]
    ring
  have hpow : (fun rho : ℝ => (lam*(1-rho^2/(2*m))-lam)^3)
      =O[𝓝 0] (fun rho : ℝ => rho^6) := by
    rw [heqR]
    exact (Asymptotics.isBigO_refl (fun rho : ℝ => rho^6) (𝓝 0)).const_mul_left _
  rw [heq]
  exact hq.neg_left.trans hpow
#print axioms evenTaylor_isBigO

/-- Quantified O(rho^6), with positive constants chosen before the radius. -/
theorem evenTaylor_bound {p : ℝ → ℝ} {lam m : ℝ} (hm : 0 < m)
    (hp : ContDiffAt ℝ 3 p lam) :
    ∃ C > 0, ∃ r > 0, ∀ rho : ℝ, |rho| < r →
      |p lam-p (lam*(1-rho^2/(2*m)))-
        (lam*deriv p lam/(2*m)*rho^2-lam^2*deriv (deriv p) lam/(8*m^2)*rho^4)|
        ≤ C*|rho|^6 := by
  obtain ⟨C,hC,hB⟩ := (evenTaylor_isBigO hm hp).exists_pos
  have hnb : {rho : ℝ | |p lam-p (lam*(1-rho^2/(2*m)))-
      (lam*deriv p lam/(2*m)*rho^2-lam^2*deriv (deriv p) lam/(8*m^2)*rho^4)|
      ≤ C*|rho|^6} ∈ 𝓝 0 := by
    simpa only [Filter.Eventually,Real.norm_eq_abs,abs_pow] using hB.bound
  obtain ⟨r,hr,hinc⟩ := Metric.mem_nhds_iff.mp hnb
  refine ⟨C,hC,r,hr,?_⟩
  intro rho hrho
  exact hinc (by simpa [Metric.mem_ball,Real.dist_eq] using hrho)
/-- The exact remainder is even, independently of differentiability. -/
theorem evenTaylor_even (p : ℝ → ℝ) (lam m rho : ℝ) :
    p lam-p (lam*(1-(-rho)^2/(2*m)))-
      (lam*deriv p lam/(2*m)*(-rho)^2-lam^2*deriv (deriv p) lam/(8*m^2)*(-rho)^4) =
    p lam-p (lam*(1-rho^2/(2*m)))-
      (lam*deriv p lam/(2*m)*rho^2-lam^2*deriv (deriv p) lam/(8*m^2)*rho^4) := by
  simp only [neg_sq, show (-rho)^4=rho^4 by ring]
#print axioms evenTaylor_bound
#print axioms evenTaylor_even
end SimplexFull.Taylor
