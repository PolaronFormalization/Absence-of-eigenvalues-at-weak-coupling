import Froehlich.Nodes.KA01AdjointIntegral
import Froehlich.Nodes.FC07Momentum

/-! Annihilation-field notation for the adjoint is used only on its genuine
number-form domain, with the physical embedding identified explicitly. -/
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace
namespace Froehlich

theorem oneParticleExtraction_representative_ae (u : GW.Fock.Carrier) :
    (physicalSector 1 (u 1) : GW.Fock.Coordinates 1 → ℂ) =ᵐ[GW.Fock.sectorMeasure 1]
      fun K => oneParticleExtraction u (K 0) := by
  have h := oneParticleCoordinate_ae (oneParticleExtraction u)
  have he : oneParticleCoordinate (oneParticleExtraction u) = u 1 := by
    rw [oneParticleExtraction_apply,oneParticleCoordinate.apply_symm_apply]
  rw [he] at h
  exact h

theorem oneToHighAdjoint_numberField_ae
    (v : GW.OnePhonon) (x : NumberFormSpace) (z : HighSectorSpace 2)
    (hphysical : numberFormEmbedding x = (z : GW.Fock.Carrier)) :
    ∀ᵐ k ∂(volume : Measure GW.Space),
      oneToHighAdjoint v z k = ⟪oneParticleInclusion v,annihilationField x k⟫_ℂ := by
  have hsections := annihilationField_physical_sections x 1
  rw [hphysical] at hsections
  filter_upwards [hsections,oneToHighAdjoint_integral v z] with k hk hi
  have hp := oneParticleCoordinates_inverse_preserving.quasiMeasurePreserving.ae hk
  have hr := oneParticleCoordinates_inverse_preserving.quasiMeasurePreserving.ae
    (oneParticleExtraction_representative_ae (annihilationField x k))
  have hextract : ∀ᵐ l ∂(volume : Measure GW.Space),
      oneParticleExtraction (annihilationField x k) l = (Real.sqrt 2 : ℂ) *
        physicalSector 2 ((z : GW.Fock.Carrier) 2) (twoParticleCoordinates k l) := by
    filter_upwards [hp,hr] with l hl hr
    calc
      oneParticleExtraction (annihilationField x k) l =
          physicalSector 1 ((annihilationField x k) 1)
            ((MeasurableEquiv.funUnique (Fin 1) GW.Space).symm l) := hr.symm
      _ = (Real.sqrt 2 : ℂ) *
          physicalSector 2 ((z : GW.Fock.Carrier) 2) (twoParticleCoordinates k l) := by
        have hins := insert_oneParticleCoordinates k l
        change physicalSector 1 ((annihilationField x k) 1)
            ((MeasurableEquiv.funUnique (Fin 1) GW.Space).symm l) =
          (Real.sqrt 2 : ℂ) * physicalSector 2 ((z : GW.Fock.Carrier) 2) (twoParticleCoordinates k l)
        exact hl.trans (by rw [hins]; rfl)
  symm
  rw [oneParticleInclusion_pairing,L2.inner_def]
  calc
    (∫ l : GW.Space, ⟪v l,oneParticleExtraction (annihilationField x k) l⟫_ℂ) =
        ∫ l : GW.Space, (Real.sqrt 2 : ℂ) * ((starRingEnd ℂ) (v l) *
          physicalSector 2 ((z : GW.Fock.Carrier) 2) (twoParticleCoordinates k l)) := by
      apply integral_congr_ae
      filter_upwards [hextract] with l hl
      rw [hl]
      simp only [RCLike.inner_apply]
      ring
    _ = (Real.sqrt 2 : ℂ) * ∫ l : GW.Space, (starRingEnd ℂ) (v l) *
          physicalSector 2 ((z : GW.Fock.Carrier) 2) (twoParticleCoordinates k l) :=
      integral_const_mul _ _
    _ = oneToHighAdjoint v z k := hi.2.symm

end Froehlich
