import Froehlich.Nodes.FC07CutoffAction
import Froehlich.Nodes.FC07Momentum

/-! The exact free distinguished-momentum shift on actual core inputs. -/
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace ENNReal
namespace Froehlich

def coreFreeActionCore (P : GW.Space) (u : boundedMomentumCore) : boundedMomentumCore :=
  ⟨coreFreeAction P u,freeFiberOperator_preserves_core P (coreFreeInput P u) u.property⟩

theorem freeSymbol_insert_zero (P k : GW.Space) (n : ℕ) (K : GW.Fock.Coordinates n) :
    freeSymbol P (n+1) ((GW.Fock.splitCoordinates n 0).symm (k,K)) =
      freeSymbol (P-k) n K + 1 := by
  calc
    _ = energyWeight (P-k) n K ^ 2 := (movingEnergyWeight_exact P k n K).symm
    _ = 1 + freeSymbol (P-k) n K := energyWeight_sq (P-k) n K
    _ = _ := add_comm _ _

theorem annihilationField_free_sections (P : GW.Space) (u : boundedMomentumCore) (n : ℕ) :
    ∀ᵐ k ∂(volume : Measure GW.Space), ∀ᵐ K ∂GW.Fock.sectorMeasure n,
      physicalSector n ((annihilationField (coreNumberLift (coreFreeActionCore P u)) k) n) K =
        ((freeSymbol (P-k) n K + 1 : ℝ) : ℂ) •
          physicalSector n ((annihilationField (coreNumberLift u) k) n) K := by
  have hgraph : ((u : GW.Fock.Carrier),(coreFreeActionCore P u : GW.Fock.Carrier)) ∈
      (freeFiberOperator P).graph := (freeFiberOperator P).mem_graph (coreFreeInput P u)
  have hg := (freeFiberOperator_graph_ae_iff P _ _).mp hgraph (n+1)
  have hp := Measure.ae_ae_of_ae_prod
    ((GW.Fock.splitCoordinates_inverse_preserving n 0).quasiMeasurePreserving.ae hg)
  have hU := annihilationField_physical_sections (coreNumberLift u) n
  have hV := annihilationField_physical_sections (coreNumberLift (coreFreeActionCore P u)) n
  rw [coreNumberLift_embedding] at hU hV
  filter_upwards [hp,hU,hV] with k hk hu hv
  filter_upwards [hk,hu,hv] with K hK hu hv
  rw [hu,hv]
  change (Real.sqrt (n+1 : ℕ) : ℂ) • physicalSector (n+1)
    ((coreFreeActionCore P u : GW.Fock.Carrier) (n+1))
      ((GW.Fock.splitCoordinates n 0).symm (k,K)) = _
  rw [← hK,freeSymbol_insert_zero]
  exact smul_comm _ _ _

/-- The moving free multiplier acts on almost every genuine annihilation
slice, and its value is the difference of two canonical L² fields. -/
theorem annihilationField_free_graph (P : GW.Space) (u : boundedMomentumCore) :
    ∀ᵐ k ∂(volume : Measure GW.Space),
      (annihilationField (coreNumberLift u) k,
        annihilationField (coreNumberLift (coreFreeActionCore P u)) k -
          annihilationField (coreNumberLift u) k) ∈ (freeFiberOperator (P-k)).graph := by
  filter_upwards [ae_all_iff.mpr (annihilationField_free_sections P u)] with k hk
  apply (freeFiberOperator_graph_ae_iff (P-k) _ _).mpr
  intro n
  have he : physicalSector n
      ((annihilationField (coreNumberLift (coreFreeActionCore P u)) k -
        annihilationField (coreNumberLift u) k) n) =
      physicalSector n ((annihilationField (coreNumberLift (coreFreeActionCore P u)) k) n) -
        physicalSector n ((annihilationField (coreNumberLift u) k) n) := by
    change physicalSector n (_ - _) = _
    exact map_sub _ _ _
  rw [he]
  filter_upwards [hk n,Lp.coeFn_sub
    (physicalSector n ((annihilationField (coreNumberLift (coreFreeActionCore P u)) k) n))
    (physicalSector n ((annihilationField (coreNumberLift u) k) n))] with K hK hsub
  simp only [Pi.sub_apply] at hsub
  rw [hsub,hK,Complex.ofReal_add,Complex.ofReal_one,add_smul,one_smul,add_sub_cancel_right]

def freeShiftField (P : GW.Space) (u : boundedMomentumCore) :
    Lp GW.Fock.Carrier 2 (volume : Measure GW.Space) :=
  annihilationField (coreNumberLift (coreFreeActionCore P u)) - annihilationField (coreNumberLift u)

theorem freeShiftField_graph (P : GW.Space) (u : boundedMomentumCore) :
    ∀ᵐ k ∂(volume : Measure GW.Space),
      (annihilationField (coreNumberLift u) k,freeShiftField P u k) ∈ (freeFiberOperator (P-k)).graph := by
  filter_upwards [annihilationField_free_graph P u,
    Lp.coeFn_sub (annihilationField (coreNumberLift (coreFreeActionCore P u)))
      (annihilationField (coreNumberLift u))] with k hk hsub
  have he : freeShiftField P u k = annihilationField (coreNumberLift (coreFreeActionCore P u)) k -
      annihilationField (coreNumberLift u) k := hsub
  rwa [he]

end Froehlich
