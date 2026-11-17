import Froehlich.Nodes.FC04FixedEnergy

/-! Canonical fixed-energy Bochner reconstruction on a bounded external set. -/
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace Classical
namespace Froehlich
section FixedSet
variable (P : GW.Space) (K : Set GW.Space) (hK : MeasurableSet K)
  (R : ℝ) (hR : 0 ≤ R) (hKR : ∀ k ∈ K, ‖k‖ ≤ R)

def fixedCanonicalSectorField (x : OperatorGraphSpace P) (n : ℕ) :
    Lp (GW.Fock.Sector n) 2 (volume : Measure GW.Space) :=
  GW.Fock.amplify volume (sectorSliceProjection n)
    (fixedEnergyAmbientSectorField P K hK R hR hKR x n)

theorem fixedCanonicalSectorField_physical (x : OperatorGraphSpace P) (n : ℕ) :
    ∀ᵐ k ∂(volume : Measure GW.Space),
      physicalSector n (fixedCanonicalSectorField P K hK R hR hKR x n k) =
        fixedEnergyAmbientSectorField P K hK R hR hKR x n k := by
  filter_upwards [GW.Fock.amplify_ae volume (sectorSliceProjection n)
    (fixedEnergyAmbientSectorField P K hK R hR hKR x n),
    fixedEnergyAmbientSectorField_physical P K hK R hR hKR x] with k hk hp
  have hs := weightedPhysical_symmetric 0 n
    ((K.indicator (annihilationField (freeGraphNumberCoordinates P x)) k) n) _ (hp n)
  rw [show fixedCanonicalSectorField P K hK R hR hKR x n k =
    sectorSliceProjection n (fixedEnergyAmbientSectorField P K hK R hR hKR x n k) from hk]
  exact symmetric_sliceProjection_physical n _ hs

theorem fixedCanonicalSectorField_bound (x : OperatorGraphSpace P) (n : ℕ) :
    ‖fixedCanonicalSectorField P K hK R hR hKR x n‖ ≤
      fixedEnergyFieldConstant P R * ‖movingEnergySectorField P x n‖ := by
  have h : ‖fixedCanonicalSectorField P K hK R hR hKR x n‖ ≤
      ‖fixedEnergyAmbientSectorField P K hK R hR hKR x n‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [GW.Fock.amplify_ae volume (sectorSliceProjection n)
      (fixedEnergyAmbientSectorField P K hK R hR hKR x n)] with k hk
    rw [show fixedCanonicalSectorField P K hK R hR hKR x n k = _ from hk]
    exact sectorSliceProjection_norm_le n _
  have hb := fixedEnergyProductClass_norm P K hK R hR hKR x n
  have hf : ‖fixedEnergyAmbientSectorField P K hK R hR hKR x n‖ =
      ‖fixedEnergyProductClass P K hK R hR hKR x n‖ :=
    (GW.Fock.productUnitary volume (GW.Fock.sectorMeasure n)).symm.norm_map _
  have hm : ‖movingEnergySectorField P x n‖ = ‖movingEnergySectorClass P x n‖ :=
    (GW.Fock.productUnitary volume (GW.Fock.sectorMeasure n)).symm.norm_map _
  rw [hf] at h
  exact h.trans (by simpa only [hm] using hb)

def fixedCanonicalSectorSum (x : OperatorGraphSpace P) :
    GW.Fock.BochnerSectorSum (volume : Measure GW.Space) GW.Fock.Sector := by
  have hb : Summable (fun n => (fixedEnergyFieldConstant P R * ‖movingEnergySectorField P x n‖)^2) := by
    simpa only [mul_pow] using (movingEnergySectorFields_summable P x).mul_left (fixedEnergyFieldConstant P R ^ 2)
  exact ⟨fun n => fixedCanonicalSectorField P K hK R hR hKR x n,
    GW.Analysis.dominated_memℓp hb (fixedCanonicalSectorField_bound P K hK R hR hKR x)⟩

def fixedCanonicalField (x : OperatorGraphSpace P) : Lp GW.Fock.Carrier 2 (volume : Measure GW.Space) :=
  GW.Fock.bochnerUnitary volume GW.Fock.Sector (fixedCanonicalSectorSum P K hK R hR hKR x)

def fixedEnergyField (x : OperatorGraphSpace P) : Lp (EnergySpace 0) 2 (volume : Measure GW.Space) :=
  ((energyCoordinates 0).symm.toLinearIsometry.toContinuousLinearMap).compLp
    (fixedCanonicalField P K hK R hR hKR x)

end FixedSet
end Froehlich
