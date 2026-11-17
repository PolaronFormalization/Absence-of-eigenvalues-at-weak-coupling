import GW.Fock.Bochner

/-! MS03 is direct reuse on the prescribed GW sectors and momentum measure. -/
noncomputable section
open MeasureTheory
namespace Froehlich

abbrev SectorFieldSum := GW.Fock.BochnerSectorSum (volume : Measure GW.Space) GW.Fock.Sector
abbrev FockField := GW.Fock.BochnerFock (volume : Measure GW.Space) GW.Fock.Sector

abbrev assembleFields : SectorFieldSum ≃ₗᵢ[ℂ] FockField :=
  GW.Fock.bochnerUnitary volume GW.Fock.Sector

theorem assembleFields_ae (u : SectorFieldSum) :
    ∀ᵐ k, ∀ n, assembleFields u k n = u n k :=
  GW.Fock.bochnerReconstruct_ae volume GW.Fock.Sector u

theorem assembleFields_coordinate (u : SectorFieldSum) (n : ℕ) :
    GW.Fock.bochnerCoordinate volume GW.Fock.Sector n (assembleFields u) = u n :=
  GW.Fock.bochnerCoordinate_reconstruct volume GW.Fock.Sector u n

theorem assembleFields_norm_sq (u : SectorFieldSum) :
    ‖assembleFields u‖ ^ 2 = ∑' n, ‖u n‖ ^ 2 := by
  rw [assembleFields.norm_map]
  exact GW.Analysis.lp_norm_sq u

end Froehlich
