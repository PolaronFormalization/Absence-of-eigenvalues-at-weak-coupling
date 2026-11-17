import Froehlich.Nodes.PT03ScalarPairing
import Froehlich.Nodes.PT03ScalarSymmetry
import Froehlich.Nodes.PT03KernelDefinitions
import Froehlich.Nodes.PT02CutoffIdentity

set_option autoImplicit false

/-! The one-particle scalar source identity is proved for every fixed
parameter before any varying-parameter substitution in PT03. -/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace Froehlich

theorem number_oneParticle_pairing_integral (f : GW.OnePhonon) (z : NumberFormSpace) :
    Integrable (fun k => f k * ⟪annihilationField z k,GW.Fock.vacuum⟫_ℂ) volume ∧
    ⟪numberFormEmbedding z,oneParticleInclusion f⟫_ℂ =
      ∫ k, f k * ⟪annihilationField z k,GW.Fock.vacuum⟫_ℂ := by
  have h := smearedCreation_test_integral f (coreNumberLift vacuumCore) z
  rw [coreNumberLift_embedding,creationRestriction_vacuum] at h
  have he (k : GW.Space) :
      (starRingEnd ℂ) ((starRingEnd ℂ) (f k) * ⟪GW.Fock.vacuum,annihilationField z k⟫_ℂ) =
        f k * ⟪annihilationField z k,GW.Fock.vacuum⟫_ℂ := by
    simp only [map_mul,Complex.star_def,Complex.conj_conj,inner_conj_symm]
  constructor
  · have hc : Integrable (fun k => (starRingEnd ℂ)
        ((starRingEnd ℂ) (f k) * ⟪GW.Fock.vacuum,annihilationField z k⟫_ℂ)) volume :=
      h.1.mono (Complex.conjCLE.continuous.comp_aestronglyMeasurable h.1.aestronglyMeasurable)
        (Filter.Eventually.of_forall (fun k => le_of_eq (Complex.norm_conj _)))
    exact hc.congr (Filter.Eventually.of_forall he)
  · have hi := congrArg (starRingEnd ℂ) h.2
    rw [←integral_conj] at hi
    have hi' := (integral_congr_ae (Filter.Eventually.of_forall he)).symm.trans hi
    simpa only [Complex.star_def,inner_conj_symm] using hi'.symm

theorem cutoffGroundSource_oneParticle_pairing (e : ℝ) (q : GW.Space)
    (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (Λ : GW.Operators.PositiveCutoff)
    (f : GW.OnePhonon) :
    Integrable (fun k => f k * (cutoffFormFactor g Λ.val k : ℂ) *
      ⟪GW.Fock.vacuum-cutoffThresholdSourceVector e he g hg hs Λ q,
        cutoffAuxiliaryZ e (q+k) he Λ g hg hs GW.Fock.vacuum⟫_ℂ) volume ∧
    ⟪cutoffThresholdSourceVector e he g hg hs Λ q,oneParticleInclusion f⟫_ℂ =
      ∫ k, f k * (cutoffFormFactor g Λ.val k : ℂ) *
        ⟪GW.Fock.vacuum-cutoffThresholdSourceVector e he g hg hs Λ q,
          cutoffAuxiliaryZ e (q+k) he Λ g hg hs GW.Fock.vacuum⟫_ℂ := by
  have h := number_oneParticle_pairing_integral f (cutoffGroundSourceNumber e q he g hg hs Λ)
  have hphysical : numberFormEmbedding (cutoffGroundSourceNumber e q he g hg hs Λ) =
      cutoffThresholdSourceVector e he g hg hs Λ q :=
    energyNumberCoordinates_intertwines (-q) _
  have hrow : (fun k => f k * ⟪annihilationField (cutoffGroundSourceNumber e q he g hg hs Λ) k,
      GW.Fock.vacuum⟫_ℂ) =ᵐ[volume] (fun k => f k * (cutoffFormFactor g Λ.val k : ℂ) *
        ⟪GW.Fock.vacuum-cutoffThresholdSourceVector e he g hg hs Λ q,
          cutoffAuxiliaryZ e (q+k) he Λ g hg hs GW.Fock.vacuum⟫_ℂ) := by
    filter_upwards [cutoffGroundSource_pullthrough e q he g hg hs Λ] with k hk
    rw [hk,inner_smul_left,Complex.conj_ofReal]
    have hp : ⟪cutoffAuxiliaryZ e (q+k) he Λ g hg hs
        (GW.Fock.vacuum-cutoffThresholdSourceVector e he g hg hs Λ q),GW.Fock.vacuum⟫_ℂ =
      ⟪GW.Fock.vacuum-cutoffThresholdSourceVector e he g hg hs Λ q,
        cutoffAuxiliaryZ e (q+k) he Λ g hg hs GW.Fock.vacuum⟫_ℂ :=
      (pt03_cutoffExtendedResolvent_pairing 0 e (q+k) he Λ g hg hs
        (GW.Fock.vacuum-cutoffThresholdSourceVector e he g hg hs Λ q) GW.Fock.vacuum).symm
    change f k * ((cutoffFormFactor g Λ.val k : ℂ) *
      ⟪cutoffAuxiliaryZ e (q+k) he Λ g hg hs
        (GW.Fock.vacuum-cutoffThresholdSourceVector e he g hg hs Λ q),GW.Fock.vacuum⟫_ℂ) = _
    rw [hp]
    ring
  rw [hphysical] at h
  exact ⟨h.1.congr hrow,h.2.trans (integral_congr_ae hrow)⟩

end Froehlich
