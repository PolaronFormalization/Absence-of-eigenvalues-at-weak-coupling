import Froehlich.Nodes.FC01Density

/-! FC02: the retained canonical annihilation field, characterized by its
literal almost-everywhere core sections. No fixed-momentum evaluation map is
introduced. -/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace Froehlich

/-- The source core formula, including one common outer null set for all
particle sectors and the literal distinguished-coordinate representative. -/
def HasCoreAnnihilationFormula
    (A : NumberFormSpace →L[ℂ] Lp GW.Fock.Carrier 2 (volume : Measure GW.Space)) : Prop :=
  ∀ u : boundedMomentumCore, ∀ᵐ k ∂(volume : Measure GW.Space), ∀ n,
    (GW.Fock.kernelFixedInclusion n
      (GW.Fock.ordinarySectorKernel n ((A (coreNumberLift u) k) n)) : GW.Fock.AmbientSector n)
      =ᵐ[GW.Fock.sectorMeasure n]
        (fun K => (Real.sqrt (n+1 : ℕ) : ℂ) •
          GW.Fock.sectorInclusion n ((u : GW.Fock.Carrier) (n+1))
            ((GW.Fock.splitCoordinates n 0).symm (k,K)))

theorem annihilationField_core_formula : HasCoreAnnihilationFormula annihilationField := by
  intro u
  simpa only [coreNumberLift_embedding] using
    annihilationField_representative_common_ae (coreNumberLift u)

theorem coreAnnihilationFormula_agreement
    (A : NumberFormSpace →L[ℂ] Lp GW.Fock.Carrier 2 (volume : Measure GW.Space))
    (hA : HasCoreAnnihilationFormula A) (u : boundedMomentumCore) :
    A (coreNumberLift u) = annihilationField (coreNumberLift u) := by
  apply Lp.ext
  filter_upwards [hA u, annihilationField_core_formula u] with k hk hcanonical
  apply lp.ext
  funext n
  apply (GW.Fock.ordinarySectorKernel n).injective
  apply (GW.Fock.kernelFixedInclusion n).injective
  exact Lp.ext ((hk n).trans (hcanonical n).symm)

/-- Uniqueness uses density in the actual number graph norm. -/
theorem annihilationField_unique
    (A : NumberFormSpace →L[ℂ] Lp GW.Fock.Carrier 2 (volume : Measure GW.Space))
    (hA : HasCoreAnnihilationFormula A) : A = annihilationField := by
  apply DFunLike.ext'
  apply A.continuous.ext_on coreNumberLift_denseRange annihilationField.continuous
  rintro x ⟨u, rfl⟩
  exact coreAnnihilationFormula_agreement A hA u

theorem existsUnique_coreAnnihilationField :
    ∃! A : NumberFormSpace →L[ℂ] Lp GW.Fock.Carrier 2 (volume : Measure GW.Space),
      HasCoreAnnihilationFormula A :=
  ⟨annihilationField, annihilationField_core_formula, fun A hA => annihilationField_unique A hA⟩

theorem coreAnnihilationField_norm_sq (x : NumberFormSpace) :
    ‖annihilationField x‖ ^ 2 =
      ∑' n : ℕ, (n : ℝ) * ‖numberFormEmbedding x n‖ ^ 2 :=
  (annihilationField_norm_sq x).trans (numberFormRoot_norm x)

theorem coreAnnihilationField_numberRoot_norm (x : NumberFormSpace) :
    ‖annihilationField x‖ ^ 2 =
      ‖GW.Fock.numberPower GW.Fock.Sector (1/2) (numberFormRootInput x)‖ ^ 2 :=
  annihilationField_norm_sq x

theorem coreAnnihilationField_projection (m : ℕ) (x : NumberFormSpace) :
    annihilationField (numberFormHighProjection (m+1) x) =
      (highSectorProjection m).compLp (annihilationField x) :=
  annihilationField_highProjection m x

theorem coreAnnihilationField_vacuum : annihilationField numberVacuumLift = 0 :=
  annihilationField_vacuum

theorem coreAnnihilationField_oneParticle (f : GW.OnePhonon) :
    ∀ᵐ k ∂(volume : Measure GW.Space),
      annihilationField (numberOneParticleLift f) k = f k • GW.Fock.vacuum :=
  annihilationField_oneParticle_ae f

end Froehlich
