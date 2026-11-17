import Froehlich.Nodes.PT03ScalarCreation
import Froehlich.Nodes.PT03KernelDefinitions
import Froehlich.Nodes.PT02CutoffSource
import Froehlich.Nodes.PT02XField

set_option autoImplicit false

/-! PT03 Step 1: finite-cutoff algebra on the actual two-particle source.
The one-particle test input is any L² vector. -/
noncomputable section
open MeasureTheory
namespace Froehlich
variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (Λ : GW.Operators.PositiveCutoff)

theorem cutoffThresholdSourceVector_eq_Y (q : GW.Space) :
    cutoffAuxiliaryY e q he Λ g hg hs
      (oneParticleInclusion (cutoffFormFactorL2 g Λ.val Λ.property)) =
        cutoffThresholdSourceVector e he g hg hs Λ q := by
  calc
    _ = (cutoffAuxiliaryResolvent 1 e q he Λ g hg hs (cutoffOneParticleSource g Λ) :
        GW.Fock.Carrier) :=
      cutoffAuxiliaryExtendedResolvent_on_high 1 e q he Λ g hg hs (cutoffOneParticleSource g Λ)
    _ = _ := (congrArg (fun u : HighSectorSpace 1 => (u : GW.Fock.Carrier))
      (cutoffGroundSourceEnergy_physical e q he g hg hs Λ)).symm

theorem cutoffOneToHighSolution_field (P : GW.Space) (f : GW.OnePhonon) :
    ∀ᵐ k ∂volume,
      annihilationField (cutoffAuxiliaryXNumber e he g hg hs Λ P
        (oneToHighMap (cutoffFormFactorL2 g Λ.val Λ.property) f)) k =
      f k • cutoffThresholdSourceVector e he g hg hs Λ (k-P) +
        (cutoffFormFactor g Λ.val k : ℂ) • cutoffAuxiliaryY e (k-P) he Λ g hg hs
          (oneParticleInclusion f - cutoffAuxiliaryX e he Λ g hg hs P
            (oneToHighMap (cutoffFormFactorL2 g Λ.val Λ.property) f : GW.Fock.Carrier)) := by
  let v := cutoffFormFactorL2 g Λ.val Λ.property
  let z := oneToHighNumberMap v f
  have hz : numberFormEmbedding z ∈ HighSectorSpace 2 := oneToHighNumberMap_high v f
  have hi : (⟨numberFormEmbedding z,hz⟩ : HighSectorSpace 2) = oneToHighMap v f :=
    Subtype.ext (oneToHighNumberMap_physical v f)
  have hpt := cutoffAuxiliaryX_pullthrough e he g hg hs Λ P z hz
  rw [hi] at hpt
  filter_upwards [hpt,annihilationField_oneToHighMap v f,cutoffFormFactorL2_ae g Λ.val Λ.property]
    with k hk ha hv
  change annihilationField z k = _ at ha
  change v k = (cutoffFormFactor g Λ.val k : ℂ) at hv
  rw [ha,oneToHighNumberMap_physical,hv] at hk
  have hrow : f k • oneParticleInclusion v + (cutoffFormFactor g Λ.val k : ℂ) • oneParticleInclusion f -
      (cutoffFormFactor g Λ.val k : ℂ) • cutoffAuxiliaryX e he Λ g hg hs P (oneToHighMap v f : GW.Fock.Carrier) =
    f k • oneParticleInclusion v + (cutoffFormFactor g Λ.val k : ℂ) •
      (oneParticleInclusion f-cutoffAuxiliaryX e he Λ g hg hs P (oneToHighMap v f : GW.Fock.Carrier)) := by
    rw [smul_sub,add_sub_assoc]
  rw [hrow,map_add,map_smul,map_smul,cutoffThresholdSourceVector_eq_Y] at hk
  simpa only [v,z] using hk

end Froehlich
