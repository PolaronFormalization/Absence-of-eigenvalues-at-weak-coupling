import Froehlich.Nodes.FC07Multipliers
import Froehlich.Nodes.FC07CoreSlices
import Froehlich.Nodes.FC04

/-! The source total-momentum commutation on actual canonical core vectors. -/
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace ENNReal
namespace Froehlich

def coreMomentumInput (a : Fin 3) (u : boundedMomentumCore) :
    (fockRealMultiplier (fun n k => totalMomentum n k a)).domain :=
  ⟨u,by
    obtain ⟨v,hv,hg⟩ := core_momentum_component_graph a u
    exact (fockRealMultiplier _).mem_domain_of_mem_graph hg⟩

def coreMomentumAction (a : Fin 3) (u : boundedMomentumCore) : boundedMomentumCore :=
  ⟨fockRealMultiplier (fun n k => totalMomentum n k a) (coreMomentumInput a u),
    multiplier_graph_preserves_core _ u _ ((fockRealMultiplier _).mem_graph (coreMomentumInput a u))⟩

theorem coreMomentumAction_graph (a : Fin 3) (u : boundedMomentumCore) :
    ((u : GW.Fock.Carrier),(coreMomentumAction a u : GW.Fock.Carrier)) ∈
      (fockRealMultiplier (fun n k => totalMomentum n k a)).graph :=
  (fockRealMultiplier _).mem_graph (coreMomentumInput a u)

theorem annihilationField_physical_sections (x : NumberFormSpace) (n : ℕ) :
    ∀ᵐ k ∂(volume : Measure GW.Space),
      (physicalSector n ((annihilationField x k) n) : GW.Fock.Coordinates n → ℂ) =ᵐ[GW.Fock.sectorMeasure n]
        (fun K => (Real.sqrt (n+1 : ℕ) : ℂ) • GW.Fock.sectorInclusion n
          (numberFormEmbedding x (n+1)) ((GW.Fock.splitCoordinates n 0).symm (k,K))) := by
  filter_upwards [annihilationField_representative_common_ae x] with k hk
  have hkn := hk n
  rw [kernelRepresentative_physical] at hkn
  exact hkn

theorem annihilationField_momentum_sections (a : Fin 3) (u : boundedMomentumCore) (n : ℕ) :
    ∀ᵐ k ∂(volume : Measure GW.Space), ∀ᵐ K ∂GW.Fock.sectorMeasure n,
      physicalSector n ((annihilationField (coreNumberLift (coreMomentumAction a u)) k) n) K =
        ((totalMomentum n K a + k a : ℝ) : ℂ) •
          physicalSector n ((annihilationField (coreNumberLift u) k) n) K := by
  have hg := (fockRealMultiplier_graph_ae_iff _ _ _).mp (coreMomentumAction_graph a u) (n+1)
  have hp := Measure.ae_ae_of_ae_prod
    ((GW.Fock.splitCoordinates_inverse_preserving n 0).quasiMeasurePreserving.ae hg)
  have hU := annihilationField_physical_sections (coreNumberLift u) n
  have hV := annihilationField_physical_sections (coreNumberLift (coreMomentumAction a u)) n
  rw [coreNumberLift_embedding] at hU hV
  filter_upwards [hp,hU,hV] with k hk hu hv
  filter_upwards [hk,hu,hv] with K hK hu hv
  rw [hu,hv]
  change (Real.sqrt (n+1 : ℕ) : ℂ) •
      physicalSector (n+1) ((coreMomentumAction a u : GW.Fock.Carrier) (n+1))
        ((GW.Fock.splitCoordinates n 0).symm (k,K)) = _
  rw [← hK, totalMomentum_insert_zero]
  simp only [PiLp.add_apply]
  have hadd : k a + totalMomentum n K a = totalMomentum n K a + k a := add_comm _ _
  rw [hadd]
  exact smul_comm _ _ _

/-- The unbounded momentum action is asserted on its actual maximal graph.
No ambient pointwise momentum operator on all Fock vectors is introduced. -/
theorem annihilationField_momentum_graph (a : Fin 3) (u : boundedMomentumCore) :
    ∀ᵐ k ∂(volume : Measure GW.Space),
      (annihilationField (coreNumberLift u) k,
        annihilationField (coreNumberLift (coreMomentumAction a u)) k -
          (k a : ℂ) • annihilationField (coreNumberLift u) k) ∈
        (fockRealMultiplier (fun n K => totalMomentum n K a)).graph := by
  filter_upwards [ae_all_iff.mpr (annihilationField_momentum_sections a u)] with k hk
  apply (fockRealMultiplier_graph_ae_iff _ _ _).mpr
  intro n
  have he : physicalSector n
      ((annihilationField (coreNumberLift (coreMomentumAction a u)) k -
        (k a : ℂ) • annihilationField (coreNumberLift u) k) n) =
      physicalSector n ((annihilationField (coreNumberLift (coreMomentumAction a u)) k) n) -
        (k a : ℂ) • physicalSector n ((annihilationField (coreNumberLift u) k) n) := by
    change physicalSector n (_ - (k a : ℂ) • _) = _
    rw [map_sub,map_smul]
  rw [he]
  filter_upwards [hk n,
    Lp.coeFn_sub
      (physicalSector n ((annihilationField (coreNumberLift (coreMomentumAction a u)) k) n))
      ((k a : ℂ) • physicalSector n ((annihilationField (coreNumberLift u) k) n)),
    Lp.coeFn_smul (k a : ℂ) (physicalSector n ((annihilationField (coreNumberLift u) k) n))]
      with K hK hsub hsmul
  simp only [Pi.sub_apply, Pi.smul_apply] at hsub hsmul
  rw [hsub,hsmul,hK,Complex.ofReal_add,add_smul,add_sub_cancel_right]

end Froehlich
