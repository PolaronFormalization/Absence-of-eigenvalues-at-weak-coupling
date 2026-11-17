import Froehlich.Nodes.PT02SourceField
import Froehlich.Nodes.PT02ProjectionConvention
import Froehlich.Nodes.PT01

/-! PT02 / lem:sourcePT and the X/Y projection conventions. All source
solutions use the same reference e; no annihilation of the singular non-L²
form factor occurs. Smallness is chosen before g and every momentum. -/
noncomputable section
open MeasureTheory
namespace Froehlich

def PT02SourceReference (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant * |g| ≤ 1/2) : Prop :=
  ∀ p : GW.Space,
    numberFormEmbedding (groundSourceNumber e p he g hg hs) = auxiliaryGroundSourceVector e p he g hg hs ∧
    (∀ (K : Set GW.Space) (hK : MeasurableSet K) (hKb : Bornology.IsBounded K)
      (R : ℝ) (hKR : ∀ k ∈ K, ‖k‖ ≤ R),
      LpToLpRestrictCLM GW.Space GW.Fock.Carrier ℂ volume 2 K
        (annihilationField (groundSourceNumber e p he g hg hs)) =
      (HighSectorSpace 0).subtypeL.compLp
        (localSingularInverseField 0 e p (by norm_num) he g hg hs K hK hKb
          (sourcePullthroughLocalField K (auxiliaryGroundSourceVector e p he g hg hs)
            (fun k => (fiberFormFactor g k : ℂ))
            (regularSource_local_formFactor_memLp g K hK R hKR)))) ∧
    (∀ᵐ k ∂volume, annihilationField (groundSourceNumber e p he g hg hs) k =
      (fiberFormFactor g k : ℂ) • auxiliaryZ e (p+k) he g hg hs
        (GW.Fock.vacuum-auxiliaryGroundSourceVector e p he g hg hs)) ∧
    (∀ Λ : GW.Operators.PositiveCutoff,
      numberFormEmbedding (cutoffGroundSourceNumber e p he g hg hs Λ) =
        energyEmbedding (-p) (cutoffGroundSourceEnergy e p he g hg hs Λ : EnergySpace (-p)) ∧
      ∀ᵐ k ∂volume, annihilationField (cutoffGroundSourceNumber e p he g hg hs Λ) k =
        (cutoffFormFactor g Λ.val k : ℂ) • cutoffAuxiliaryZ e (p+k) he Λ g hg hs
          (GW.Fock.vacuum-energyEmbedding (-p)
            (cutoffGroundSourceEnergy e p he g hg hs Λ : EnergySpace (-p))))

def PT02XReference (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant * |g| ≤ 1/2) : Prop :=
  (∀ (P : GW.Space) (z : NumberFormSpace) (hz : numberFormEmbedding z ∈ HighSectorSpace 2),
    numberFormEmbedding (auxiliaryXNumber e he g hg hs P ⟨numberFormEmbedding z,hz⟩) =
      auxiliaryX e he g hg hs P (numberFormEmbedding z) ∧
    (∀ᵐ k ∂volume, annihilationField (auxiliaryXNumber e he g hg hs P ⟨numberFormEmbedding z,hz⟩) k =
      auxiliaryY e (k-P) he g hg hs (annihilationField z k-(fiberFormFactor g k : ℂ) •
        auxiliaryX e he g hg hs P (numberFormEmbedding z))) ∧
    (∀ Λ : GW.Operators.PositiveCutoff,
      numberFormEmbedding (cutoffAuxiliaryXNumber e he g hg hs Λ P ⟨numberFormEmbedding z,hz⟩) =
        cutoffAuxiliaryX e he Λ g hg hs P (numberFormEmbedding z) ∧
      ∀ᵐ k ∂volume, annihilationField (cutoffAuxiliaryXNumber e he g hg hs Λ P ⟨numberFormEmbedding z,hz⟩) k =
        cutoffAuxiliaryY e (k-P) he Λ g hg hs (annihilationField z k-(cutoffFormFactor g Λ.val k : ℂ) •
          cutoffAuxiliaryX e he Λ g hg hs P (numberFormEmbedding z)))) ∧
  (∀ (P : GW.Space) (z : NumberFormSpace), numberFormEmbedding z ∈ HighSectorSpace 1 →
    numberFormEmbedding (projectedAuxiliaryXNumber e he g hg hs P z) =
      auxiliaryX e he g hg hs P (numberFormEmbedding z) ∧
    (∀ᵐ k ∂volume, auxiliaryY e (k-P) he g hg hs (annihilationField (numberFormHighProjection 2 z) k) =
      auxiliaryY e (k-P) he g hg hs (annihilationField z k)) ∧
    (∀ᵐ k ∂volume, annihilationField (projectedAuxiliaryXNumber e he g hg hs P z) k =
      auxiliaryY e (k-P) he g hg hs (annihilationField z k-(fiberFormFactor g k : ℂ) •
        auxiliaryX e he g hg hs P (numberFormEmbedding z))) ∧
    (∀ Λ : GW.Operators.PositiveCutoff,
      numberFormEmbedding (projectedCutoffAuxiliaryXNumber e he g hg hs Λ P z) =
        cutoffAuxiliaryX e he Λ g hg hs P (numberFormEmbedding z) ∧
      ∀ᵐ k ∂volume, annihilationField (projectedCutoffAuxiliaryXNumber e he g hg hs Λ P z) k =
        cutoffAuxiliaryY e (k-P) he Λ g hg hs (annihilationField z k-(cutoffFormFactor g Λ.val k : ℂ) •
          cutoffAuxiliaryX e he Λ g hg hs P (numberFormEmbedding z))))

theorem finalPT02_uniform (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant * |g| ≤ 1/2) :
    PT02SourceReference e he g hg hs ∧ PT02XReference e he g hg hs := by
  constructor
  · intro p
    refine ⟨groundSourceNumber_physical e p he g hg hs,?_,
      groundSource_pullthrough_global e p he g hg hs,?_⟩
    · intro K hK hKb R hKR
      exact groundSource_pullthrough_local e p he g hg hs K hK hKb R hKR
    · intro Λ
      exact ⟨energyNumberCoordinates_intertwines (-p) _,cutoffGroundSource_pullthrough e p he g hg hs Λ⟩
  · constructor
    · intro P z hz
      refine ⟨auxiliaryXNumber_physical e he g hg hs P ⟨numberFormEmbedding z,hz⟩,
        auxiliaryX_pullthrough e he g hg hs P z hz,?_⟩
      intro Λ
      exact ⟨cutoffAuxiliaryXNumber_physical e he g hg hs Λ P ⟨numberFormEmbedding z,hz⟩,
        cutoffAuxiliaryX_pullthrough e he g hg hs Λ P z hz⟩
    · intro P z _hz
      refine ⟨projectedAuxiliaryXNumber_physical e he g hg hs P z,
        auxiliaryY_annihilation_projection e he g hg hs P z,
        projectedAuxiliaryX_pullthrough e he g hg hs P z,?_⟩
      intro Λ
      exact ⟨projectedCutoffAuxiliaryXNumber_physical e he g hg hs Λ P z,
        projectedCutoffAuxiliaryX_pullthrough e he g hg hs Λ P z⟩

theorem finalPT02 : ∃ s : ℝ, 0 < s ∧ ∀ g : ℝ, |g| < s →
    ∃ he : groundEnergy (fiberHamiltonian g 0) ∈ Set.Icc (-1/4 : ℝ) 0,
    ∃ hg : |g| ≤ 1, ∃ hs : auxiliaryResolventConstant * |g| ≤ 1/2,
      PT02SourceReference (groundEnergy (fiberHamiltonian g 0)) he g hg hs ∧
      PT02XReference (groundEnergy (fiberHamiltonian g 0)) he g hg hs := by
  obtain ⟨s,hs,hGround⟩ := auxiliarySelfEnergy_zero_groundEnergy
  refine ⟨s,hs,?_⟩
  intro g hgSmall
  obtain ⟨he,hg,hsmall,_⟩ := hGround g hgSmall
  exact ⟨he,hg,hsmall,finalPT02_uniform _ he g hg hsmall⟩

end Froehlich
