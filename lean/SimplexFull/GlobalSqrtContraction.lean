import SimplexFull.GlobalProjectionContraction

noncomputable section
open Finset Matrix
open scoped Matrix Matrix.Norms.L2Operator RealInnerProductSpace
namespace SimplexFull.Geometry

/-- The polynomial certificate underlying the square-root Frobenius estimate. -/
theorem global_sqrt_contraction_identity {m : ℕ} (hm : m ≠ 0)
    (T : Matrix (Fin m) (Fin m) ℝ)
    (hPT : centering m * T = T) (hTP : T * centering m = T) :
    (T*T-centering m)*(T*T-centering m) -
        (T-centering m)*(T-centering m) =
      (T-centering m) * (T*T+T+T) * (T-centering m) := by
  have hleft (A : Matrix (Fin m) (Fin m) ℝ) : centering m * (T * A) = T * A := by
    rw [← Matrix.mul_assoc, hPT]
  simp only [add_mul, mul_add, sub_mul, mul_sub]
  simp only [Matrix.mul_assoc, hPT, hTP, hleft, centering_mul_self hm]
  noncomm_ring

/-- For a PSD root supported on P, its Frobenius distance to P is bounded by
the Frobenius distance of its square to P. This includes singular roots. -/
theorem global_frobSq_root_sub_centering_le {m : ℕ} (hm : m ≠ 0)
    (T : Matrix (Fin m) (Fin m) ℝ) (hT : T.PosSemidef)
    (hPT : centering m * T = T) (hTP : T * centering m = T) :
    frobSq (T-centering m) ≤ frobSq (T*T-centering m) := by
  have hsym : T.IsSymm := (isHermitian_iff_isSymm).1 hT.isHermitian
  have hT2 : (T*T).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, hsym.eq] using
      Matrix.posSemidef_conjTranspose_mul_self T
  have hM : (T*T+T+T).PosSemidef := (hT2.add hT).add hT
  have hAsym : (T-centering m).IsSymm := by
    unfold Matrix.IsSymm
    rw [Matrix.transpose_sub, hsym.eq, (centering_isSymm m).eq]
  have hBsym : (T*T-centering m).IsSymm := by
    unfold Matrix.IsSymm
    rw [Matrix.transpose_sub, Matrix.transpose_mul, hsym.eq, (centering_isSymm m).eq]
  have hnonneg := (hM.conjTranspose_mul_mul_same (T-centering m)).trace_nonneg
  simp only [Matrix.conjTranspose_eq_transpose_of_trivial, hAsym.eq] at hnonneg
  rw [← global_sqrt_contraction_identity hm T hPT hTP, Matrix.trace_sub] at hnonneg
  rw [global_frobSq_eq_trace_mul_of_isSymm hAsym,
    global_frobSq_eq_trace_mul_of_isSymm hBsym]
  linarith

/-- The preceding estimate for the actual centered CFC square root of any configuration. -/
theorem global_frobSq_centeredRoot_le {m d : ℕ} (hm : 1 ≤ m) (X : Config m d) :
    frobSq (centeredRoot X-centering m) ≤
      frobSq (centeredGram X-centering m) := by
  obtain ⟨hPT,hTP⟩ := centered_mul_centering (centeredRoot_centered X hm)
  simpa only [centeredRoot_mul_self X hm] using
    global_frobSq_root_sub_centering_le (by omega) (centeredRoot X)
      (centeredRoot_posSemidef X) hPT hTP

#print axioms global_sqrt_contraction_identity
#print axioms global_frobSq_root_sub_centering_le
#print axioms global_frobSq_centeredRoot_le
end SimplexFull.Geometry
