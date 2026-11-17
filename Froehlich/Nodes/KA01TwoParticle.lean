import Froehlich.Nodes.KA01FirstMap

/-! Literal symmetric two-particle creation, on the retained physical sectors. -/
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace
namespace Froehlich

theorem oneParticleCoordinate_ae (f : GW.OnePhonon) :
    (physicalSector 1 (oneParticleCoordinate f) : GW.Fock.Coordinates 1 → ℂ) =ᵐ[GW.Fock.sectorMeasure 1]
      fun K => f (K 0) := by
  change (GW.Fock.sectorInclusion 0 (oneParticleCoordinate f) : GW.Fock.Coordinates 1 → ℂ) =ᵐ[_] _
  rw [oneParticleCoordinate_representative]
  exact Lp.coeFn_compMeasurePreserving f GW.Fock.oneBosonCoordinate_preserving

theorem oneToHighMap_twoParticle_ae (v f : GW.OnePhonon) :
    (physicalSector 2 ((oneToHighMap v f : GW.Fock.Carrier) 2) : GW.Fock.Coordinates 2 → ℂ)
      =ᵐ[GW.Fock.sectorMeasure 2] fun K =>
        (v (K 0) * f (K 1) + v (K 1) * f (K 0)) / (Real.sqrt 2 : ℂ) := by
  have hc := GW.Fock.ordinaryCreationSector_ae v 1 (oneParticleCoordinate f)
  have hf := oneParticleCoordinate_ae f
  have hd : ∀ᵐ K ∂GW.Fock.sectorMeasure 2, ∀ j : Fin 2,
      physicalSector 1 (oneParticleCoordinate f) (fun i => K (j.succAbove i)) =
        f ((fun i => K (j.succAbove i)) 0) := by
    apply ae_all_iff.mpr
    intro j
    exact (ae_coordinate_deleted 1 j (Eventually.of_forall (fun _ => True.intro)) hf).mono
      (fun _ h => h.2)
  rw [oneToHighMap_physical,lp.single_apply_self]
  filter_upwards [hc,hd] with K hK hD
  change physicalSector 2
    (GW.Fock.sectorCreation GW.Fock.ordinarySectorKernel (GW.Fock.ordinaryKernel v) 1
      (oneParticleCoordinate f)) K = _
  change physicalSector 2
    (GW.Fock.sectorCreation GW.Fock.ordinarySectorKernel (GW.Fock.ordinaryKernel v) 1
      (oneParticleCoordinate f)) K = _ at hK
  rw [hK]
  change ((Real.sqrt (1+1 : ℕ) : ℂ)⁻¹) *
    (∑ j : Fin 2, v (K j) * physicalSector 1 (oneParticleCoordinate f) (fun i => K (j.succAbove i))) = _
  simp only [hD,Fin.sum_univ_two]
  change (Real.sqrt 2 : ℂ)⁻¹ * (v (K 0) * f (K 1) + v (K 1) * f (K 0)) = _
  ring

theorem oneToHighMap_exchange (v f : GW.OnePhonon) : oneToHighMap v f = oneToHighMap f v := by
  apply Subtype.ext
  apply lp.ext
  funext n
  by_cases hn : n = 2
  · subst n
    apply (physicalSector 2).injective
    apply Lp.ext
    filter_upwards [oneToHighMap_twoParticle_ae v f,oneToHighMap_twoParticle_ae f v] with K hv hf
    rw [hv,hf]
    ring
  · rw [oneToHighMap_physical,oneToHighMap_physical,
      lp.single_apply_ne _ _ _ hn,lp.single_apply_ne _ _ _ hn]

theorem oneToHighAdjoint_sector (v : GW.OnePhonon) (z : HighSectorSpace 2) :
    oneToHighAdjoint v z = oneParticleCoordinate.symm
      (GW.Fock.sectorAnnihilation GW.Fock.ordinarySectorKernel (GW.Fock.ordinaryKernel v) 1
        ((z : GW.Fock.Carrier) 2)) := by
  apply ext_inner_left ℂ
  intro f
  rw [← oneToHighAdjoint_pairing]
  change ⟪(oneToHighMap v f : GW.Fock.Carrier),(z : GW.Fock.Carrier)⟫_ℂ = _
  rw [oneToHighMap_physical,lp.inner_single_left,smeared_sector_pairing]
  have he := oneParticleCoordinate.inner_map_map f (oneParticleCoordinate.symm
    (GW.Fock.sectorAnnihilation GW.Fock.ordinarySectorKernel (GW.Fock.ordinaryKernel v) 1
      ((z : GW.Fock.Carrier) 2)))
  rw [oneParticleCoordinate.apply_symm_apply] at he
  exact he

end Froehlich
