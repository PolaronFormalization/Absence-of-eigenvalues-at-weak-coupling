import Froehlich.Nodes.PT02CutoffSource
import Froehlich.Nodes.PT01CoreCutoffGlobal
import Froehlich.Nodes.UV01Fields

/-! Finite-cutoff PT02, applied only to the genuine L² one-particle source. -/
noncomputable section
open MeasureTheory
namespace Froehlich
variable (e : ℝ) (p : GW.Space) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
  (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant * |g| ≤ 1/2)

def cutoffGroundSourceNumber (Λ : GW.Operators.PositiveCutoff) : NumberFormSpace :=
  energyNumberCoordinates (-p) (cutoffGroundSourceEnergy e p he g hg hs Λ : EnergySpace (-p))

theorem cutoffGroundSourceNumber_graph (Λ : GW.Operators.PositiveCutoff) :
    cutoffGroundSourceNumber e p he g hg hs Λ =
      freeGraphNumberCoordinates (-p)
        (cutoffAuxiliaryGraphCoordinate 1 e p (by norm_num) he Λ g hg hs (cutoffOneParticleSource g Λ)) := by
  apply numberFormEmbedding_injective
  rw [cutoffGroundSourceNumber,energyNumberCoordinates_intertwines,
    freeGraphNumberCoordinates_embedding,cutoffAuxiliaryGraphCoordinate_physical]
  exact congrArg (fun u : HighSectorSpace 1 => (u : GW.Fock.Carrier))
    (cutoffGroundSourceEnergy_physical e p he g hg hs Λ)

theorem cutoffGroundSource_pullthrough (Λ : GW.Operators.PositiveCutoff) :
    ∀ᵐ k ∂volume, annihilationField (cutoffGroundSourceNumber e p he g hg hs Λ) k =
      (cutoffFormFactor g Λ.val k : ℂ) •
        cutoffAuxiliaryZ e (p+k) he Λ g hg hs
          (GW.Fock.vacuum - energyEmbedding (-p)
            (cutoffGroundSourceEnergy e p he g hg hs Λ : EnergySpace (-p))) := by
  let F := numberOneParticleLift (cutoffFormFactorL2 g Λ.val Λ.property)
  have hF : numberFormEmbedding F ∈ HighSectorSpace (0+1) := by
    rw [show numberFormEmbedding F = (cutoffOneParticleSource g Λ : GW.Fock.Carrier) from
      cutoffOneParticleSource_number g Λ]
    exact (cutoffOneParticleSource g Λ).property
  have hi : (⟨numberFormEmbedding F,hF⟩ : HighSectorSpace (0+1)) = cutoffOneParticleSource g Λ :=
    Subtype.ext (cutoffOneParticleSource_number g Λ)
  have hpt := cutoffPullthrough_global_source_domain 0 e p (by norm_num) he Λ g hg hs F hF
  rw [hi] at hpt
  have hh := congrArg (fun u : HighSectorSpace 1 => (u : GW.Fock.Carrier))
    (cutoffGroundSourceEnergy_physical e p he g hg hs Λ)
  rw [highEnergyEmbedding_apply] at hh
  rw [cutoffGroundSourceNumber_graph]
  filter_upwards [hpt,coreAnnihilationField_oneParticle (cutoffFormFactorL2 g Λ.val Λ.property),
    cutoffFormFactorL2_ae g Λ.val Λ.property] with k hk ha hv
  obtain ⟨q,hq,hout⟩ := hk
  change annihilationField F k = _ at ha
  rw [ha,hv,←hh,←smul_sub] at hq
  calc
    _ = (cutoffAuxiliaryResolvent 0 e (p+k) he Λ g hg hs q : GW.Fock.Carrier) := hout
    _ = cutoffAuxiliaryZ e (p+k) he Λ g hg hs (q : GW.Fock.Carrier) :=
      (cutoffAuxiliaryExtendedResolvent_on_high 0 e (p+k) he Λ g hg hs q).symm
    _ = _ := by rw [hq,map_smul]

end Froehlich
