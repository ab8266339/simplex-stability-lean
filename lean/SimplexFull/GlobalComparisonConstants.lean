import SimplexFull.GlobalComparisonDefs
import SimplexFull.GlobalRectangleBound

noncomputable section
open MeasureTheory ProbabilityTheory Set Real WeakSimplex
open scoped BigOperators
namespace SimplexFull.GlobalComparison

theorem centralMass_pos {t : ℝ} (ht : 0<t) : 0<centralMass t := by
  have hmono : StrictMono Phi := by
    apply strictMono_of_deriv_pos
    intro x
    rw [(hasDerivAt_Phi x).deriv]
    exact phi_pos x
  have hp := hmono ht
  have hz := Phi_add_Phi_neg 0
  simp only [neg_zero] at hz
  unfold centralMass
  linarith

theorem paperK_factorization {m : ℕ} (hm : 2≤m) (u v : ℝ) :
    paperK m u v = Real.exp (-(m:ℝ)*capA m u*beta m u) *
      GlobalRectangle.rectangleK m (ell m u) (radiusT m u v) *
      (centralMass (ell m u))^m := by
  unfold paperK GlobalRectangle.rectangleK centralMass
  rw [show 2*m-2=(m-2)+m by omega,pow_add]
  ring

theorem paperK_pos {m : ℕ} (hm : 2≤m) (u v : ℝ) : 0<paperK m u v := by
  rw [paperK_factorization hm]
  exact mul_pos (mul_pos (Real.exp_pos _)
    (GlobalRectangle.rectangleK_pos hm (ell_pos m u)))
    (pow_pos (centralMass_pos (ell_pos m u)) m)

theorem paperKappa_pos {m : ℕ} (hm : 2≤m) (u v : ℝ) : 0<paperKappa m u v := by
  unfold paperKappa
  have hK := paperK_pos hm u v
  have hp := Phi_pos u
  positivity

theorem covarianceDefect_nonneg {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) :
    0≤covarianceDefect R :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _

theorem covarianceDefect_le {m : ℕ} (hm : 2≤m)
    (R : Matrix (Fin m) (Fin m) ℝ) (hR : IsCorrelation R) :
    covarianceDefect R ≤ (m:ℝ)*((m:ℝ)-1) := by
  classical
  have he (i j : Fin m) : (R i j)^2 ≤ 1 := by
    let f : Fin 2→Fin m := ![i,j]
    have hh := GlobalBivariate.pair_correlation_abs_le_one (hR.1.submatrix f)
      (fun k => hR.2 (f k))
    have hh' : |R i j|≤1 := by simpa [f] using hh
    nlinarith [sq_abs (R i j),abs_nonneg (R i j)]
  let t : Finset (Fin m × Fin m) := Finset.univ.offDiag
  have hfrob : covarianceDefect R = ∑ q ∈ t, (R q.1 q.2)^2 := by
    have hset : t = (Finset.univ ×ˢ Finset.univ).filter
        (fun q : Fin m × Fin m => q.1≠q.2) := by ext q; simp [t]
    unfold covarianceDefect
    rw [hset,Finset.sum_filter,Finset.sum_product]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : i=j
    · subst j
      simp [Matrix.sub_apply,hR.2]
    · simp [Matrix.sub_apply,Matrix.one_apply_ne hij,hij]
  have hc : t.card = m*(m-1) := by simp [t,Finset.offDiag_card,Nat.mul_sub_left_distrib]
  calc
    covarianceDefect R = ∑ q ∈ t, (R q.1 q.2)^2 := hfrob
    _ ≤ ∑ _q ∈ t, (1:ℝ) := Finset.sum_le_sum fun q _ => he q.1 q.2
    _ = (m:ℝ)*((m:ℝ)-1) := by
      simp only [Finset.sum_const,nsmul_eq_mul,mul_one,hc,Nat.cast_mul]
      rw [Nat.cast_sub (by omega : 1≤m),Nat.cast_one]

/-- Exact rationalization of the square-root deficit, with its uniform
denominator taken at the proved correlation-matrix defect bound. -/
theorem paperKappa_mul_le_sqrt_gap {m : ℕ} (hm : 2≤m) (u v : ℝ) {d : ℝ}
    (hd0 : 0≤d) (hd1 : d≤(m:ℝ)*((m:ℝ)-1)) :
    paperKappa m u v*d ≤
      (Phi u)^m*(Real.sqrt (1+paperK m u v*d)-1) := by
  let K := paperK m u v
  have hK : 0≤K := (paperK_pos hm u v).le
  have hx : 0≤1+K*d := by positivity
  have hden : 0<1+Real.sqrt (1+K*d) := by positivity
  have hM : 0<1+Real.sqrt (1+K*(m:ℝ)*((m:ℝ)-1)) := by positivity
  have hs : Real.sqrt (1+K*d) ≤ Real.sqrt (1+K*(m:ℝ)*((m:ℝ)-1)) := by
    apply Real.sqrt_le_sqrt
    nlinarith [mul_le_mul_of_nonneg_left hd1 hK]
  have hfrac : K*d/(1+Real.sqrt (1+K*(m:ℝ)*((m:ℝ)-1))) ≤
      K*d/(1+Real.sqrt (1+K*d)) :=
    div_le_div_of_nonneg_left (mul_nonneg hK hd0) hden (by linarith)
  have hrat : K*d/(1+Real.sqrt (1+K*d)) = Real.sqrt (1+K*d)-1 := by
    apply (div_eq_iff hden.ne').mpr
    nlinarith [Real.sq_sqrt hx]
  rw [hrat] at hfrac
  have hh := mul_le_mul_of_nonneg_left hfrac (pow_nonneg (Phi_pos u).le m)
  unfold paperKappa
  change (Phi u)^m*K/(1+Real.sqrt (1+K*(m:ℝ)*((m:ℝ)-1)))*d ≤ _
  calc
    (Phi u)^m*K/(1+Real.sqrt (1+K*(m:ℝ)*((m:ℝ)-1)))*d =
      (Phi u)^m*(K*d/(1+Real.sqrt (1+K*(m:ℝ)*((m:ℝ)-1)))) := by ring
    _ ≤ _ := hh

theorem paperKappa_defect_le_sqrt_gap {m : ℕ} (hm : 2≤m)
    (R : Matrix (Fin m) (Fin m) ℝ) (hR : IsCorrelation R) (u v : ℝ) :
    paperKappa m u v*covarianceDefect R ≤
      (Phi u)^m*(Real.sqrt (1+paperK m u v*covarianceDefect R)-1) :=
  paperKappa_mul_le_sqrt_gap hm u v (covarianceDefect_nonneg R) (covarianceDefect_le hm R hR)

#print axioms paperK_factorization
#print axioms paperK_pos
#print axioms paperKappa_pos
#print axioms covarianceDefect_le
#print axioms paperKappa_defect_le_sqrt_gap
end SimplexFull.GlobalComparison
