import Froehlich.Nodes.SP01Inverse
import Froehlich.Nodes.MN02Vacuum
import Froehlich.Nodes.FB02VacuumColumn

/-! The vacuum column of the full singular form. The vacuum is used in
the form domain only; the free operator graph supplies its free column. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

theorem freeFiberForm_vacuum_column (P : GW.Space) (w : EnergySpace P) :
    freeFiberForm P w (vacuumEnergyLift P) =
      (‖P‖^2 : ℂ) * ⟪energyEmbedding P w,GW.Fock.vacuum⟫_ℂ := by
  obtain ⟨x,hx,hw⟩ := (freeFiberOperator_graph_weak_iff P _ _).mp
    (freeFiberOperator_vacuum_graph P)
  have he : x = vacuumEnergyLift P :=
    energyEmbedding_injective P (hx.trans (vacuumEnergyLift_embedding P).symm)
  rw [he] at hw
  simpa only [inner_smul_right] using hw w

theorem fiberForm_vacuum_column (g : ℝ) (P : GW.Space) (w : EnergySpace P) :
    (fiberFormData g P none).form w (vacuumEnergyLift P) =
      (‖P‖^2 : ℂ) * ⟪energyEmbedding P w,GW.Fock.vacuum⟫_ℂ + fiberSourceLoad g P w := by
  rw [fiberFormData_singular_apply,freeFiberForm_vacuum_column,singularInteraction_vacuum_column]

theorem highEnergyEmbedding_vacuum_orthogonal (P : GW.Space) (w : HighEnergySpace P 1) :
    ⟪energyEmbedding P (w : EnergySpace P),GW.Fock.vacuum⟫_ℂ = 0 := by
  have hp := (highSector_mem_iff 1 (highEnergyEmbedding P 1 w)).mp
    (highEnergyEmbedding P 1 w).property
  rw [highEnergyEmbedding_apply] at hp
  have hz := congrArg (fun u : GW.Fock.Carrier => u 0) hp
  have hz' : (energyEmbedding P (w : EnergySpace P)) 0 = 0 := by
    simpa only [highSectorProjection_apply,show ¬1 ≤ (0 : ℕ) by omega,ite_false] using hz.symm
  have hv := vacuumInclusion_pairing 1 (energyEmbedding P (w : EnergySpace P))
  rw [vacuumInclusion_one,hz'] at hv
  have hv0 : ⟪GW.Fock.vacuum,energyEmbedding P (w : EnergySpace P)⟫_ℂ = 0 := by
    apply hv.trans
    change ⟪(1 : ℂ),(0 : ℂ)⟫_ℂ = 0
    exact inner_zero_right _
  have hc := inner_conj_symm (𝕜 := ℂ) GW.Fock.vacuum
    (energyEmbedding P (w : EnergySpace P))
  rw [hv0] at hc
  exact (starRingEnd ℂ).injective (hc.trans (map_zero (starRingEnd ℂ)).symm)

theorem fiberForm_high_vacuum_column (g : ℝ) (P : GW.Space) (w : HighEnergySpace P 1) :
    (fiberFormData g P none).form (w : EnergySpace P) (vacuumEnergyLift P) =
      highFiberSourceLoad g P 1 w := by
  rw [fiberForm_vacuum_column,highEnergyEmbedding_vacuum_orthogonal,mul_zero,zero_add]
  rfl

end Froehlich
