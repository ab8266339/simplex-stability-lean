import SimplexFull.GlobalRectangleQuantitative

noncomputable section
open MeasureTheory Set Real Filter ProbabilityTheory WeakSimplex
open scoped Topology Interval ENNReal
namespace SimplexFull.GlobalRectangle

/-- Algebraic lifting of a proved bivariate rate. The final Gaussian theorem
instantiates this helper with the actual Plackett bound, including singular endpoints. -/
theorem rectangle_bound_of_pair_bound {m : ℕ} (hm : 2≤m)
    (R : Matrix (Fin m) (Fin m) ℝ) (hR : R.PosSemidef) (hdiag : ∀ i,R i i=1)
    (r : Fin m→ℝ) {ell T C : ℝ} (hell : 0<ell)
    (hrlo : ∀ i,ell≤r i) (hrhi : ∀ i,r i≤T) (hC : 0≤C)
    (hpair : ∀ (S : Matrix (Fin 2) (Fin 2) ℝ), S.PosSemidef→
      (∀ i,S i i=1)→∀ (s : Fin 2→ℝ),(∀ i,ell≤s i)→(∀ i,s i≤T)→
      C*(S 0 1)^2 ≤
        (multivariateGaussian (0 : Coord 2) S (symmetricRectangle s)).toReal -
        (gaussianReal 0 1 (Icc (-s 0) (s 0))*gaussianReal 0 1 (Icc (-s 1) (s 1))).toReal) :
    C/((m:ℝ)*((m:ℝ)-1)) *
      (gaussianReal 0 1 (Icc (-ell) ell)).toReal^(m-2) *
      (∑ k,∑ l,((R-1) k l)^2) ≤
    (multivariateGaussian (0 : Coord m) R (symmetricRectangle r)).toReal -
      (∏ i,gaussianReal 0 1 (Icc (-r i) (r i))).toReal := by
  classical
  obtain ⟨i,j,hij,hfrob⟩ := exists_pair_sq_ge_average hm R hdiag
  obtain ⟨σ,hσ0,hσ1⟩ := Peel.exists_perm_pair hm hij
  let S := R.submatrix σ σ
  let s : Fin m→ℝ := r ∘ σ
  have hS : S.PosSemidef := hR.submatrix σ
  have hSdiag (k : Fin m) : S k k=1 := hdiag (σ k)
  have hslo (k : Fin m) : ell≤s k := hrlo (σ k)
  have hshi (k : Fin m) : s k≤T := hrhi (σ k)
  have hpeel := rectangle_gap_ge_first_pair_gap hm S hS hSdiag s
    (fun k => hell.le.trans (hslo k))
  have hp := hpair (S.submatrix (Fin.castLE hm) (Fin.castLE hm)) (hS.submatrix _)
    (fun k => hSdiag _) (s ∘ Fin.castLE hm) (fun k => hslo _) (fun k => hshi _)
  have hpentry : (S.submatrix (Fin.castLE hm) (Fin.castLE hm)) 0 1 = R i j := by
    simp [S,hσ0,hσ1]
  rw [hpentry] at hp
  have htail := ENNReal.toReal_mono (by
    unfold Peel.tailProd
    apply ENNReal.prod_ne_top
    intro k _
    split_ifs <;> simp [measure_ne_top]) (tailProd_lower_bound hm ell s hslo)
  rw [ENNReal.toReal_pow] at htail
  have htail0 : 0≤(Peel.tailProd s).toReal := ENNReal.toReal_nonneg
  have hbase0 : 0≤(gaussianReal 0 1 (Icc (-ell) ell)).toReal^(m-2) := by positivity
  have hbound := (mul_le_mul_of_nonneg_right hp htail0).trans hpeel
  have hlift := mul_le_mul_of_nonneg_left htail (mul_nonneg hC (sq_nonneg (R i j)))
  have hperm := Peel.multivariateGaussian_symmetricRectangle_perm hR σ r
  have hprod : (∏ k,gaussianReal 0 1 (Icc (-r k) (r k))) =
      ∏ k,gaussianReal 0 1 (Icc (-s k) (s k)) :=
    (Equiv.prod_comp σ fun k => gaussianReal 0 1 (Icc (-r k) (r k))).symm
  have hgap :
      (multivariateGaussian (0 : Coord m) S (symmetricRectangle s)).toReal -
        (∏ k,gaussianReal 0 1 (Icc (-s k) (s k))).toReal =
      (multivariateGaussian (0 : Coord m) R (symmetricRectangle r)).toReal -
        (∏ k,gaussianReal 0 1 (Icc (-r k) (r k))).toReal := by
    dsimp [S,s]
    rw [hperm]
    congr 1
    exact congrArg ENNReal.toReal hprod.symm
  rw [hgap] at hbound
  have hmR : (2:ℝ)≤(m:ℝ) := by exact_mod_cast hm
  have hden : 0<(m:ℝ)*((m:ℝ)-1) := mul_pos (by linarith) (by linarith)
  have hf : (∑ k,∑ l,((R-1) k l)^2)/((m:ℝ)*((m:ℝ)-1)) ≤ (R i j)^2 :=
    (div_le_iff₀ hden).mpr (by simpa only [mul_comm] using hfrob)
  have hmul := mul_le_mul_of_nonneg_left hf (mul_nonneg hC hbase0)
  calc
    C/((m:ℝ)*((m:ℝ)-1)) *
        (gaussianReal 0 1 (Icc (-ell) ell)).toReal^(m-2) *
        (∑ k,∑ l,((R-1) k l)^2) =
      (C*(gaussianReal 0 1 (Icc (-ell) ell)).toReal^(m-2)) *
        ((∑ k,∑ l,((R-1) k l)^2)/((m:ℝ)*((m:ℝ)-1))) := by ring
    _ ≤ (C*(gaussianReal 0 1 (Icc (-ell) ell)).toReal^(m-2))*(R i j)^2 := hmul
    _ = C*(R i j)^2*(gaussianReal 0 1 (Icc (-ell) ell)).toReal^(m-2) := by ring
    _ ≤ C*(R i j)^2*(Peel.tailProd s).toReal := hlift
    _ ≤ _ := hbound

#print axioms rectangle_bound_of_pair_bound
end SimplexFull.GlobalRectangle
