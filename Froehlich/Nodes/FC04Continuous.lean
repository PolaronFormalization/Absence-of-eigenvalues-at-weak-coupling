import Froehlich.Nodes.FC04Map

/-! Physical identification and quantitative bounds for the fixed-energy field. -/
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace Classical ENNReal
namespace Froehlich
section FixedSet
variable (P : GW.Space) (K : Set GW.Space) (hK : MeasurableSet K)
  (R : ℝ) (hR : 0 ≤ R) (hKR : ∀ k ∈ K, ‖k‖ ≤ R)

theorem fixedCanonicalField_physical (x : OperatorGraphSpace P) :
    ∀ᵐ k ∂(volume : Measure GW.Space), ∀ n,
      physicalSector n (fixedCanonicalField P K hK R hR hKR x k n) =
        fixedEnergyAmbientSectorField P K hK R hR hKR x n k := by
  have ha := GW.Fock.bochnerReconstruct_ae (volume : Measure GW.Space) GW.Fock.Sector
    (fixedCanonicalSectorSum P K hK R hR hKR x)
  filter_upwards [ha, ae_all_iff.mpr (fixedCanonicalSectorField_physical P K hK R hR hKR x)] with k hk hs
  intro n
  have he : fixedCanonicalField P K hK R hR hKR x k n =
      fixedCanonicalSectorField P K hK R hR hKR x n k := hk n
  rw [he]
  exact hs n

theorem fixedEnergyField_embedding (x : OperatorGraphSpace P) :
    ∀ᵐ k ∂(volume : Measure GW.Space),
      energyEmbedding 0 (fixedEnergyField P K hK R hR hKR x k) =
        K.indicator (annihilationField (freeGraphNumberCoordinates P x)) k := by
  filter_upwards [fixedCanonicalField_physical P K hK R hR hKR x,
    fixedEnergyAmbientSectorField_physical P K hK R hR hKR x,
    ((energyCoordinates 0).symm.toLinearIsometry.toContinuousLinearMap).coeFn_compLp
      (fixedCanonicalField P K hK R hR hKR x)] with k hc hp he
  have he' : fixedEnergyField P K hK R hR hKR x k =
      (energyCoordinates 0).symm (fixedCanonicalField P K hK R hR hKR x k) := he
  rw [he']
  apply lp.ext
  funext n
  apply (physicalSector n).injective
  apply Lp.ext
  have hw := sectorEnergyEmbedding_weighted_ae 0 n (fixedCanonicalField P K hK R hR hKR x k n)
  filter_upwards [hw, hp n] with L hw hpL
  apply mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr
    (ne_of_gt (zero_lt_one.trans_le (energyWeight_ge_one 0 n L))))
  have hcoordinates : energyEmbedding 0 ((energyCoordinates 0).symm
      (fixedCanonicalField P K hK R hR hKR x k)) n =
      sectorEnergyEmbedding 0 n (fixedCanonicalField P K hK R hR hKR x k n) := by
    rw [energyEmbedding_apply, LinearIsometryEquiv.apply_symm_apply]
  rw [hcoordinates]
  have hcL := congrArg (fun v : GW.Fock.AmbientSector n => v L) (hc n)
  simpa only [smul_eq_mul] using hw.trans (hcL.trans hpL.symm)

theorem fixedCanonicalField_norm_le (x : OperatorGraphSpace P) :
    ‖fixedCanonicalField P K hK R hR hKR x‖ ≤
      fixedEnergyFieldConstant P R * ‖movingCanonicalField P x‖ := by
  have hC : 0 ≤ fixedEnergyFieldConstant P R := Real.sqrt_nonneg _
  rw [fixedCanonicalField, movingCanonicalField, LinearIsometryEquiv.norm_map,
    LinearIsometryEquiv.norm_map]
  have h : ‖fixedCanonicalSectorSum P K hK R hR hKR x‖ ≤
      ‖(fixedEnergyFieldConstant P R : ℂ) • movingCanonicalSectorSum P x‖ := by
    apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    intro n
    change ‖fixedCanonicalSectorField P K hK R hR hKR x n‖ ≤
      ‖(fixedEnergyFieldConstant P R : ℂ) • movingCanonicalSectorField P x n‖
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hC,
      movingCanonicalSectorField_norm]
    exact fixedCanonicalSectorField_bound P K hK R hR hKR x n
  simpa only [norm_smul, Complex.norm_real, Real.norm_of_nonneg hC] using h

theorem fixedEnergyField_norm (x : OperatorGraphSpace P) :
    ‖fixedEnergyField P K hK R hR hKR x‖ = ‖fixedCanonicalField P K hK R hR hKR x‖ := by
  have hn : ∀ᵐ k ∂(volume : Measure GW.Space),
      ‖fixedEnergyField P K hK R hR hKR x k‖ = ‖fixedCanonicalField P K hK R hR hKR x k‖ := by
    filter_upwards [((energyCoordinates 0).symm.toLinearIsometry.toContinuousLinearMap).coeFn_compLp
      (fixedCanonicalField P K hK R hR hKR x)] with k hk
    have he : fixedEnergyField P K hK R hR hKR x k =
        (energyCoordinates 0).symm (fixedCanonicalField P K hK R hR hKR x k) := hk
    rw [he, LinearIsometryEquiv.norm_map]
  exact le_antisymm (Lp.norm_le_norm_of_ae_le (hn.mono (fun _ h => h.le)))
    (Lp.norm_le_norm_of_ae_le (hn.mono (fun _ h => h.symm.le)))

theorem fixedEnergyField_bound (x : OperatorGraphSpace P) :
    ‖fixedEnergyField P K hK R hR hKR x‖ ≤ fixedEnergyFieldConstant P R * ‖x‖ := by
  rw [fixedEnergyField_norm]
  have hfree : ‖freeActionOnGraph P x‖ ≤ ‖x‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    have h := graph_norm_identity P x
    nlinarith [sq_nonneg ‖graphEmbedding P x‖]
  have hmove : ‖movingCanonicalField P x‖ ≤ ‖freeActionOnGraph P x‖ :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (movingCanonicalField_sharp_bound P x)
  exact (fixedCanonicalField_norm_le P K hK R hR hKR x).trans
    (mul_le_mul_of_nonneg_left (hmove.trans hfree) (Real.sqrt_nonneg _))

end FixedSet
end Froehlich
