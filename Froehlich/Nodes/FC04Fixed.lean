import Froehlich.Nodes.FC04Energy

/-! Global sharp field-energy control and the uniform fixed-energy weight
comparison on bounded external momentum sets. -/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace Froehlich

theorem movingCanonicalField_sharp_bound (P : GW.Space) (x : OperatorGraphSpace P) :
    ‖movingCanonicalField P x‖ ^ 2 ≤ ‖freeActionOnGraph P x‖ ^ 2 := by
  rw [movingCanonicalField, LinearIsometryEquiv.norm_map, GW.Analysis.lp_norm_sq,
    GW.Fock.carrier_norm_sq]
  have hs := (GW.Analysis.memℓp_two_iff_sq _).mp (freeActionOnGraph P x).property
  have hsucc : (∑' n : ℕ, ‖freeActionOnGraph P x (n+1)‖ ^ 2) ≤
      ∑' n : ℕ, ‖freeActionOnGraph P x n‖ ^ 2 := by
    rw [hs.tsum_eq_zero_add]
    exact le_add_of_nonneg_left (sq_nonneg _)
  apply le_trans _ hsucc
  apply Summable.tsum_le_tsum
  · intro n
    change ‖movingCanonicalSectorField P x n‖ ^ 2 ≤ _
    rw [movingCanonicalSectorField_norm]
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
      (movingEnergySectorField_norm_le P x n)
  · exact (GW.Analysis.memℓp_two_iff_sq _).mp (movingCanonicalSectorSum P x).property
  · exact (summable_nat_add_iff 1).mpr hs

theorem movingEnergySlice_exact_integral (P : GW.Space) (x : OperatorGraphSpace P) :
    (∫ k : GW.Space, ‖movingEnergySlice P x k‖ ^ 2) =
      ∑' n : ℕ, ∫ K : GW.Fock.Coordinates (n+1), (n+1 : ℝ) * freeSymbol P (n+1) K *
        ‖physicalSector (n+1) (graphEmbedding P x (n+1)) K‖ ^ 2 := by
  have he : (fun k : GW.Space => ‖movingEnergySlice P x k‖ ^ 2) =
      (fun k => ‖movingCanonicalField P x k‖ ^ 2) := by
    funext k
    exact congrArg (fun r : ℝ => r^2) ((energyCoordinates (P-k)).symm.norm_map _)
  rw [he, ← GW.Analysis.l2_norm_sq (𝕜 := ℂ), movingCanonicalField_norm_sq,
    movingEnergyAmbientField_norm_sq]

theorem movingEnergySlice_integral_bound (P : GW.Space) (x : OperatorGraphSpace P) :
    (∫ k : GW.Space, ‖movingEnergySlice P x k‖ ^ 2) ≤ ‖freeActionOnGraph P x‖ ^ 2 := by
  have he : (fun k : GW.Space => ‖movingEnergySlice P x k‖ ^ 2) =
      (fun k => ‖movingCanonicalField P x k‖ ^ 2) := by
    funext k
    exact congrArg (fun r : ℝ => r^2) ((energyCoordinates (P-k)).symm.norm_map _)
  rw [he, ← GW.Analysis.l2_norm_sq (𝕜 := ℂ)]
  exact movingCanonicalField_sharp_bound P x

def fixedEnergyFieldConstant (P : GW.Space) (R : ℝ) : ℝ :=
  Real.sqrt (2 * (1 + (‖P‖ + R)^2))

theorem fixedEnergyWeight_bound (P k : GW.Space) (R : ℝ) (hR : 0 ≤ R) (hk : ‖k‖ ≤ R)
    (n : ℕ) (K : GW.Fock.Coordinates n) :
    energyWeight 0 n K ≤ fixedEnergyFieldConstant P R * energyWeight (P-k) n K := by
  dsimp only [fixedEnergyFieldConstant]
  apply (sq_le_sq₀ (zero_le_one.trans (energyWeight_ge_one 0 n K))
    (mul_nonneg (Real.sqrt_nonneg _) (zero_le_one.trans (energyWeight_ge_one _ _ _)))).mp
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  have ht : ‖0-(P-k)‖ ≤ ‖P‖ + R := by
    simpa only [zero_sub, norm_neg] using (norm_sub_le P k).trans (add_le_add (le_refl ‖P‖) hk)
  have hs := (sq_le_sq₀ (norm_nonneg (0-(P-k))) (by positivity : 0 ≤ ‖P‖+R)).mpr ht
  exact (energyWeight_change_sq 0 (P-k) n K).trans
    (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _))

end Froehlich
