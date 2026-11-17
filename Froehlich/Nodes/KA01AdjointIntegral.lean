import Froehlich.Nodes.KA01TwoParticle
import Froehlich.Nodes.FC04Domain

/-! The physical adjoint integral is valid on the whole high-sector Hilbert space. -/
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace
namespace Froehlich

def twoParticleCoordinates (k l : GW.Space) : GW.Fock.Coordinates 2 :=
  (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => GW.Space)).symm (k,l)

theorem twoParticleCoordinates_preserving :
    MeasurePreserving (fun p : GW.Space × GW.Space => twoParticleCoordinates p.1 p.2)
      ((volume : Measure GW.Space).prod volume) (GW.Fock.sectorMeasure 2) :=
  (measurePreserving_piFinTwo (fun _ : Fin 2 => (volume : Measure GW.Space))).symm _

theorem oneParticleCoordinates_inverse_preserving :
    MeasurePreserving (MeasurableEquiv.funUnique (Fin 1) GW.Space).symm
      (volume : Measure GW.Space) (GW.Fock.sectorMeasure 1) :=
  (measurePreserving_funUnique (volume : Measure GW.Space) (Fin 1)).symm _

theorem insert_oneParticleCoordinates (l k : GW.Space) :
    (GW.Fock.splitCoordinates 1 0).symm
      (l,(MeasurableEquiv.funUnique (Fin 1) GW.Space).symm k) = twoParticleCoordinates l k := by
  funext i
  fin_cases i
  · exact GW.Fock.insertCoordinate_same 1 0 l _
  · exact GW.Fock.insertCoordinate_succAbove 1 0 l _ (0 : Fin 1)

theorem twoParticleCoordinates_swap (k l : GW.Space) :
    (fun i => twoParticleCoordinates k l ((Equiv.swap (0 : Fin 2) 1) i)) =
      twoParticleCoordinates l k := by
  funext i
  fin_cases i <;> simp [twoParticleCoordinates]

theorem physical_twoParticle_symmetry_ae (z : GW.Fock.Sector 2) :
    ∀ᵐ k ∂(volume : Measure GW.Space), ∀ᵐ l ∂(volume : Measure GW.Space),
      physicalSector 2 z (twoParticleCoordinates l k) =
        physicalSector 2 z (twoParticleCoordinates k l) := by
  have hs := (GW.Fock.symmetricSector_mem_iff 2 (physicalSector 2 z)).mp
    (physicalSector_symmetric 2 z) (Equiv.swap (0 : Fin 2) 1)
  have hp := twoParticleCoordinates_preserving.quasiMeasurePreserving.ae hs
  have hprod : ∀ᵐ p ∂((volume : Measure GW.Space).prod volume),
      physicalSector 2 z (twoParticleCoordinates p.2 p.1) =
        physicalSector 2 z (twoParticleCoordinates p.1 p.2) := by
    filter_upwards [hp] with p hp
    exact (congrArg (fun K => physicalSector 2 z K)
      (twoParticleCoordinates_swap p.1 p.2)).symm.trans hp
  exact Measure.ae_ae_of_ae_prod hprod

theorem oneToHighAdjoint_integral (v : GW.OnePhonon) (z : HighSectorSpace 2) :
    ∀ᵐ k ∂(volume : Measure GW.Space),
      Integrable (fun l : GW.Space => (starRingEnd ℂ) (v l) *
        physicalSector 2 ((z : GW.Fock.Carrier) 2) (twoParticleCoordinates k l)) volume ∧
      oneToHighAdjoint v z k = (Real.sqrt 2 : ℂ) *
        ∫ l : GW.Space, (starRingEnd ℂ) (v l) *
          physicalSector 2 ((z : GW.Fock.Carrier) 2) (twoParticleCoordinates k l) := by
  have hi := oneParticleCoordinates_inverse_preserving.quasiMeasurePreserving.ae
    (smeared_annihilation_sector_integral v 1 ((z : GW.Fock.Carrier) 2))
  have he : oneParticleCoordinate (oneToHighAdjoint v z) =
      GW.Fock.sectorAnnihilation GW.Fock.ordinarySectorKernel (GW.Fock.ordinaryKernel v) 1
        ((z : GW.Fock.Carrier) 2) := by
    rw [oneToHighAdjoint_sector,oneParticleCoordinate.apply_symm_apply]
  have hr := oneParticleCoordinate_ae (oneToHighAdjoint v z)
  rw [he] at hr
  have hr' := oneParticleCoordinates_inverse_preserving.quasiMeasurePreserving.ae hr
  filter_upwards [hi,hr',physical_twoParticle_symmetry_ae ((z : GW.Fock.Carrier) 2)] with k hk hr hs
  have hfun : (fun l : GW.Space => (starRingEnd ℂ) (v l) *
      GW.Fock.sectorInclusion 1 ((z : GW.Fock.Carrier) 2)
        ((GW.Fock.splitCoordinates 1 0).symm
          (l,(MeasurableEquiv.funUnique (Fin 1) GW.Space).symm k))) =
      (fun l : GW.Space => (starRingEnd ℂ) (v l) *
        physicalSector 2 ((z : GW.Fock.Carrier) 2) (twoParticleCoordinates l k)) := by
    funext l
    rw [insert_oneParticleCoordinates]
    rfl
  have hint : Integrable (fun l : GW.Space => (starRingEnd ℂ) (v l) *
      physicalSector 2 ((z : GW.Fock.Carrier) 2) (twoParticleCoordinates l k)) volume := by
    have hi0 := hk.1
    rw [hfun] at hi0
    exact hi0
  have hcongr : (fun l : GW.Space => (starRingEnd ℂ) (v l) *
      physicalSector 2 ((z : GW.Fock.Carrier) 2) (twoParticleCoordinates l k)) =ᵐ[volume]
      (fun l : GW.Space => (starRingEnd ℂ) (v l) *
        physicalSector 2 ((z : GW.Fock.Carrier) 2) (twoParticleCoordinates k l)) := by
    filter_upwards [hs] with l hl
    rw [hl]
  refine ⟨hint.congr hcongr, ?_⟩
  have hvalue : oneToHighAdjoint v z k = (Real.sqrt 2 : ℂ) *
      ∫ l : GW.Space, (starRingEnd ℂ) (v l) *
        physicalSector 2 ((z : GW.Fock.Carrier) 2) (twoParticleCoordinates l k) := by
    have hv := hk.2
    rw [hfun] at hv
    exact hr.symm.trans hv
  exact hvalue.trans (congrArg (fun a : ℂ => (Real.sqrt 2 : ℂ) * a) (integral_congr_ae hcongr))

end Froehlich
