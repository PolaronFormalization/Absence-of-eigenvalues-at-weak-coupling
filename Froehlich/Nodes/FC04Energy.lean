import Froehlich.Nodes.FC04Domain

/-! Canonical symmetric energy coordinates assembled with the retained
Bochner direct-sum unitary. -/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace Froehlich

def movingCanonicalSectorField (P : GW.Space) (x : OperatorGraphSpace P) (n : ℕ) :
    Lp (GW.Fock.Sector n) 2 (volume : Measure GW.Space) :=
  GW.Fock.amplify volume (sectorSliceProjection n) (movingEnergySectorField P x n)

theorem movingCanonicalSectorField_ae (P : GW.Space) (x : OperatorGraphSpace P) (n : ℕ) :
    ∀ᵐ k ∂(volume : Measure GW.Space),
      physicalSector n (movingCanonicalSectorField P x n k) = movingEnergySectorField P x n k := by
  filter_upwards [GW.Fock.amplify_ae volume (sectorSliceProjection n) (movingEnergySectorField P x n),
    movingEnergySectorField_symmetric P x] with k hk hs
  rw [show movingCanonicalSectorField P x n k =
    sectorSliceProjection n (movingEnergySectorField P x n k) from hk]
  exact symmetric_sliceProjection_physical n _ (hs n)

theorem movingCanonicalSectorField_norm (P : GW.Space) (x : OperatorGraphSpace P) (n : ℕ) :
    ‖movingCanonicalSectorField P x n‖ = ‖movingEnergySectorField P x n‖ := by
  have hn : ∀ᵐ k ∂(volume : Measure GW.Space),
      ‖movingCanonicalSectorField P x n k‖ = ‖movingEnergySectorField P x n k‖ :=
    (movingCanonicalSectorField_ae P x n).mono (fun k hk => by
      rw [← hk, LinearIsometry.norm_map])
  exact le_antisymm (Lp.norm_le_norm_of_ae_le (hn.mono (fun _ h => h.le)))
    (Lp.norm_le_norm_of_ae_le (hn.mono (fun _ h => h.symm.le)))

def movingCanonicalSectorSum (P : GW.Space) (x : OperatorGraphSpace P) :
    GW.Fock.BochnerSectorSum (volume : Measure GW.Space) GW.Fock.Sector :=
  ⟨fun n => movingCanonicalSectorField P x n,
    (GW.Analysis.memℓp_two_iff_sq _).mpr (by
      simpa only [movingCanonicalSectorField_norm] using movingEnergySectorFields_summable P x)⟩

def movingCanonicalField (P : GW.Space) (x : OperatorGraphSpace P) :
    Lp GW.Fock.Carrier 2 (volume : Measure GW.Space) :=
  GW.Fock.bochnerUnitary volume GW.Fock.Sector (movingCanonicalSectorSum P x)

theorem movingCanonicalField_physical (P : GW.Space) (x : OperatorGraphSpace P) :
    ∀ᵐ k ∂(volume : Measure GW.Space), ∀ n,
      physicalSector n (movingCanonicalField P x k n) = movingEnergySectorField P x n k := by
  have ha := GW.Fock.bochnerReconstruct_ae (volume : Measure GW.Space) GW.Fock.Sector
    (movingCanonicalSectorSum P x)
  filter_upwards [ha, ae_all_iff.mpr (movingCanonicalSectorField_ae P x)] with k hk hs
  intro n
  have he : movingCanonicalField P x k n = movingCanonicalSectorField P x n k := hk n
  rw [he]
  exact hs n

theorem movingCanonicalField_norm_sq (P : GW.Space) (x : OperatorGraphSpace P) :
    ‖movingCanonicalField P x‖ ^ 2 = ‖movingEnergyAmbientField P x‖ ^ 2 := by
  rw [movingCanonicalField, movingEnergyAmbientField, LinearIsometryEquiv.norm_map,
    LinearIsometryEquiv.norm_map, GW.Analysis.lp_norm_sq, GW.Analysis.lp_norm_sq]
  apply tsum_congr
  intro n
  exact congrArg (fun r : ℝ => r^2) (movingCanonicalSectorField_norm P x n)

/-- An actual isolated moving-energy coordinate, obtained from an honest
canonical Fock-valued L² class. -/
def movingEnergySlice (P : GW.Space) (x : OperatorGraphSpace P) (k : GW.Space) : EnergySpace (P-k) :=
  (energyCoordinates (P-k)).symm (movingCanonicalField P x k)

theorem movingEnergySlice_embedding (P : GW.Space) (x : OperatorGraphSpace P) :
    ∀ᵐ k ∂(volume : Measure GW.Space),
      energyEmbedding (P-k) (movingEnergySlice P x k) =
        annihilationField (freeGraphNumberCoordinates P x) k := by
  filter_upwards [movingCanonicalField_physical P x, movingEnergySectorField_physical P x]
    with k hc hp
  apply lp.ext
  funext n
  apply (physicalSector n).injective
  apply Lp.ext
  have he := sectorEnergyEmbedding_weighted_ae (P-k) n (movingCanonicalField P x k n)
  filter_upwards [he, hp n] with K hK hpK
  apply mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr
    (ne_of_gt (zero_lt_one.trans_le (energyWeight_ge_one (P-k) n K))))
  have hcoordinates : energyEmbedding (P-k) (movingEnergySlice P x k) n =
      sectorEnergyEmbedding (P-k) n (movingCanonicalField P x k n) := by
    rw [energyEmbedding_apply]
    change sectorEnergyEmbedding (P-k) n
      (energyCoordinates (P-k) ((energyCoordinates (P-k)).symm (movingCanonicalField P x k)) n) = _
    rw [LinearIsometryEquiv.apply_symm_apply]
  rw [hcoordinates]
  have hcK := congrArg (fun v : GW.Fock.AmbientSector n => v K) (hc n)
  simpa only [smul_eq_mul] using hK.trans (hcK.trans hpK.symm)

theorem annihilationField_movingEnergy_domain (P : GW.Space) (x : OperatorGraphSpace P) :
    ∀ᵐ k ∂(volume : Measure GW.Space),
      annihilationField (freeGraphNumberCoordinates P x) k ∈ (energyWeightOperator (P-k)).domain := by
  filter_upwards [movingEnergySlice_embedding P x] with k hk
  rw [← hk]
  exact energyEmbedding_mem_domain (P-k) _

end Froehlich
