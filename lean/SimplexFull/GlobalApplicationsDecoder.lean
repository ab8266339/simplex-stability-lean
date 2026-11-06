import SimplexFull.GlobalApplicationsCore
noncomputable section
open scoped BigOperators
namespace SimplexFull.GlobalApplication
variable {m : Nat} [NeZero m]

/-- Exact cP stability for the actual Procrustes infimum and unit signals. -/
theorem decodingSuccess_procrustes_penalty {d : Nat} (hm : 2≤m)
    (X V : Geometry.Config m d) (hX : Geometry.UnitConfig X)
    (hV : Geometry.gram V = Geometry.simplexGram m) {lam : Real} (hlam : 0<lam) :
    procrustesDecoderConstant m lam*Geometry.procrustesSq X V ≤
      decodingSuccess (Geometry.simplexGram m) lam-decodingSuccess (Geometry.gram X) lam := by
  let delta := decodingSuccess (Geometry.simplexGram m) lam-decodingSuccess (Geometry.gram X) lam
  have hcg := gramDecoderConstant_pos hm hlam
  have hcs := GlobalTail.centroidDecoderConstant_pos hm hlam
  have hmR : (0:Real)<m := by exact_mod_cast (show 0<m by omega)
  have ha := GlobalCentroid.alpha_pos hm
  have hg := decodingSuccess_gram_penalty hm (Geometry.gram X)
    (GlobalFoundation.gram_isCorrelation X hX) hlam
  have hs := GlobalTail.decodingSuccess_centroid_penalty hm X hX hlam
  have hgp : Geometry.frobSq (Geometry.gram X-Geometry.simplexGram m) ≤
      delta/gramDecoderConstant m lam := (le_div_iff₀ hcg).mpr (by simpa [mul_comm] using hg)
  have hsp : ‖∑ i, X i‖^2 ≤ delta/GlobalTail.centroidDecoderConstant m lam :=
    (le_div_iff₀ hcs).mpr (by simpa [mul_comm] using hs)
  have hden : 0 < Geometry.alpha m/gramDecoderConstant m lam +
      1/((m:Real)*GlobalTail.centroidDecoderConstant m lam) :=
    add_pos (div_pos ha hcg) (one_div_pos.mpr (mul_pos hmR hcs))
  have hcomb : Geometry.procrustesSq X V ≤
      (Geometry.alpha m/gramDecoderConstant m lam +
        1/((m:Real)*GlobalTail.centroidDecoderConstant m lam))*delta := by
    calc
      _ ≤ Geometry.alpha m*Geometry.frobSq (Geometry.gram X-Geometry.simplexGram m)+
          ‖∑ i, X i‖^2/(m:Real) := Geometry.global_procrustesSq_le_gram_centroid hm X V hV
      _ ≤ Geometry.alpha m*(delta/gramDecoderConstant m lam)+
          (delta/GlobalTail.centroidDecoderConstant m lam)/(m:Real) :=
        add_le_add (mul_le_mul_of_nonneg_left hgp ha.le) (div_le_div_of_nonneg_right hsp hmR.le)
      _ = _ := by ring
  rw [procrustesDecoderConstant, inv_mul_eq_div]
  exact (div_le_iff₀ hden).mpr (by simpa only [mul_comm] using hcomb)

/-- Rank-constrained correlation matrices; the realization dimension is unrestricted. -/
theorem decodingSuccess_rank_penalty {rankBound : Nat} (hm : 2≤m) (hd : 1≤rankBound)
    (G : Matrix (Fin m) (Fin m) Real) (hG : WeakSimplex.IsCorrelation G)
    (hrank : G.rank ≤ rankBound) {lam : Real} (hlam : 0<lam) :
    gramDecoderConstant m lam * ((m:Real)^2*(1/(rankBound:Real)-1/((m:Real)-1))) ≤
      decodingSuccess (Geometry.simplexGram m) lam-decodingSuccess G lam := by
  have hgeom := Geometry.global_simplex_frobSq_lower_of_rank_le hm hd G hG.1 hG.2 hrank
  exact (mul_le_mul_of_nonneg_left hgeom (gramDecoderConstant_pos hm hlam).le).trans
    (decodingSuccess_gram_penalty hm G hG hlam)

/-- Strictly positive rank-deficiency obstruction in the manuscript range. -/
theorem decodingSuccess_rank_deficiency {rankBound : Nat} (hd : 1≤rankBound)
    (hdm : rankBound<m-1) (G : Matrix (Fin m) (Fin m) Real)
    (hG : WeakSimplex.IsCorrelation G) (hrank : G.rank ≤ rankBound)
    {lam : Real} (hlam : 0<lam) :
    0 < gramDecoderConstant m lam*((m:Real)^2*(1/(rankBound:Real)-1/((m:Real)-1))) ∧
    gramDecoderConstant m lam*((m:Real)^2*(1/(rankBound:Real)-1/((m:Real)-1))) ≤
      decodingSuccess (Geometry.simplexGram m) lam-decodingSuccess G lam := by
  have hm : 2≤m := by omega
  exact ⟨mul_pos (gramDecoderConstant_pos hm hlam)
      (Geometry.global_rank_deficiency_coefficient_pos hd hdm),
    decodingSuccess_rank_penalty hm hd G hG hrank hlam⟩

theorem decodingSuccess_ambient_penalty {d : Nat} (hm : 2≤m) (hd : 1≤d)
    (X : Geometry.Config m d) (hX : Geometry.UnitConfig X) {lam : Real} (hlam : 0<lam) :
    gramDecoderConstant m lam*((m:Real)^2*(1/(d:Real)-1/((m:Real)-1))) ≤
      decodingSuccess (Geometry.simplexGram m) lam-decodingSuccess (Geometry.gram X) lam :=
  decodingSuccess_rank_penalty hm hd (Geometry.gram X)
    (GlobalFoundation.gram_isCorrelation X hX) (Geometry.global_gram_rank_le_ambient X) hlam

#print axioms decodingSuccess_procrustes_penalty
#print axioms decodingSuccess_rank_penalty
#print axioms decodingSuccess_rank_deficiency
#print axioms decodingSuccess_ambient_penalty
end SimplexFull.GlobalApplication
