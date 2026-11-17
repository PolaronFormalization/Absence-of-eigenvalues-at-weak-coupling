import Froehlich.Nodes.SE02CutoffNumber
import Froehlich.Nodes.PT02XField

/-! The two pull-through vector identities have FIXED source and parameter
zero. Their finite intersection supports subsequent tests by h_k, without
substituting p=k into a parameter-dependent AE assertion. -/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace Froehlich
variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
  (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant * |g| ≤ 1/2)

def se02CutoffXHighVector (Λ : GW.Operators.PositiveCutoff) : HighSectorSpace 2 :=
  cutoffAuxiliaryResolvent 2 e (-(0 : GW.Space)) he Λ g hg hs
    (highEnergyEmbedding 0 2 (cutoffGroundSourceHighEnergy e he g hg hs Λ))

def se02CutoffXHighNumber (Λ : GW.Operators.PositiveCutoff) : NumberFormSpace :=
  cutoffAuxiliaryXNumber e he g hg hs Λ 0
    (highEnergyEmbedding 0 2 (cutoffGroundSourceHighEnergy e he g hg hs Λ))

theorem se02CutoffXHighVector_physical (Λ : GW.Operators.PositiveCutoff) :
    (se02CutoffXHighVector e he g hg hs Λ : GW.Fock.Carrier) =
      cutoffAuxiliaryX e he Λ g hg hs 0
        (energyEmbedding 0 (cutoffGroundSourceHighEnergy e he g hg hs Λ : EnergySpace 0)) :=
  (cutoffAuxiliaryExtendedResolvent_on_high 2 e (-(0 : GW.Space)) he Λ g hg hs
    (highEnergyEmbedding 0 2 (cutoffGroundSourceHighEnergy e he g hg hs Λ))).symm

theorem se02CutoffXHighNumber_physical (Λ : GW.Operators.PositiveCutoff) :
    numberFormEmbedding (se02CutoffXHighNumber e he g hg hs Λ) =
      (se02CutoffXHighVector e he g hg hs Λ : GW.Fock.Carrier) :=
  ptRegularCutoffNumberVector_physical 2 e (-(0 : GW.Space)) (by norm_num) he g hg hs
    (highEnergyEmbedding 0 2 (cutoffGroundSourceHighEnergy e he g hg hs Λ)) Λ

theorem se02_cutoff_source_vector_field (Λ : GW.Operators.PositiveCutoff) :
    ∀ᵐ k ∂volume, annihilationField (cutoffGroundSourceNumber e 0 he g hg hs Λ) k =
      (cutoffFormFactor g Λ.val k : ℂ) • cutoffAuxiliaryZ e k he Λ g hg hs
        (GW.Fock.vacuum-cutoffThresholdSourceVector e he g hg hs Λ 0) := by
  simpa only [zero_add,cutoffThresholdSourceVector] using cutoffGroundSource_pullthrough e 0 he g hg hs Λ

theorem se02_cutoff_high_vector_field (Λ : GW.Operators.PositiveCutoff) :
    ∀ᵐ k ∂volume, annihilationField (se02CutoffXHighNumber e he g hg hs Λ) k =
      cutoffAuxiliaryY e k he Λ g hg hs
        (annihilationField (se02CutoffHighNumber e he g hg hs Λ) k -
          (cutoffFormFactor g Λ.val k : ℂ) • (se02CutoffXHighVector e he g hg hs Λ : GW.Fock.Carrier)) := by
  have hR := se02CutoffHighNumber_high e he g hg hs Λ
  have h := cutoffAuxiliaryX_pullthrough e he g hg hs Λ 0 (se02CutoffHighNumber e he g hg hs Λ) hR
  have hi : (⟨numberFormEmbedding (se02CutoffHighNumber e he g hg hs Λ),hR⟩ : HighSectorSpace 2) =
      highEnergyEmbedding 0 2 (cutoffGroundSourceHighEnergy e he g hg hs Λ) :=
    Subtype.ext (se02CutoffHighNumber_physical e he g hg hs Λ)
  rw [hi,se02CutoffHighNumber_physical,←se02CutoffXHighVector_physical] at h
  simpa only [se02CutoffXHighNumber,sub_zero] using h

theorem se02_cutoff_adjoint_field (Λ : GW.Operators.PositiveCutoff) :
    ∀ᵐ k ∂volume,
      oneToHighAdjoint (cutoffFormFactorL2 g Λ.val Λ.property) (se02CutoffXHighVector e he g hg hs Λ) k =
        ⟪oneParticleInclusion (cutoffFormFactorL2 g Λ.val Λ.property),
          annihilationField (se02CutoffXHighNumber e he g hg hs Λ) k⟫_ℂ :=
  oneToHighAdjoint_numberField_ae (cutoffFormFactorL2 g Λ.val Λ.property)
    (se02CutoffXHighNumber e he g hg hs Λ) (se02CutoffXHighVector e he g hg hs Λ)
    (se02CutoffXHighNumber_physical e he g hg hs Λ)

theorem se02_cutoff_fixed_field_set (Λ : GW.Operators.PositiveCutoff) :
    ∀ᵐ k ∂volume,
      annihilationField (cutoffGroundSourceNumber e 0 he g hg hs Λ) k =
        (cutoffFormFactor g Λ.val k : ℂ) • cutoffAuxiliaryZ e k he Λ g hg hs
          (GW.Fock.vacuum-cutoffThresholdSourceVector e he g hg hs Λ 0) ∧
      annihilationField (se02CutoffXHighNumber e he g hg hs Λ) k =
        cutoffAuxiliaryY e k he Λ g hg hs
          (annihilationField (se02CutoffHighNumber e he g hg hs Λ) k -
            (cutoffFormFactor g Λ.val k : ℂ) • (se02CutoffXHighVector e he g hg hs Λ : GW.Fock.Carrier)) ∧
      annihilationField (cutoffGroundSourceNumber e 0 he g hg hs Λ) k =
        oneParticleEnergyEmbedding 0 (cutoffGroundSourceOneEnergy e he g hg hs Λ) k • GW.Fock.vacuum +
          annihilationField (se02CutoffHighNumber e he g hg hs Λ) k ∧
      annihilationField (se02CutoffHighNumber e he g hg hs Λ) k ∈ HighSectorSpace 1 ∧
      oneToHighAdjoint (cutoffFormFactorL2 g Λ.val Λ.property) (se02CutoffXHighVector e he g hg hs Λ) k =
        ⟪oneParticleInclusion (cutoffFormFactorL2 g Λ.val Λ.property),
          annihilationField (se02CutoffXHighNumber e he g hg hs Λ) k⟫_ℂ := by
  filter_upwards [se02_cutoff_source_vector_field e he g hg hs Λ,
    se02_cutoff_high_vector_field e he g hg hs Λ,se02CutoffSource_annihilation_split e he g hg hs Λ,
    se02CutoffHigh_annihilation_high e he g hg hs Λ,se02_cutoff_adjoint_field e he g hg hs Λ]
    with k hsource hhigh hsplit hsector hadjoint
  exact ⟨hsource,hhigh,hsplit,hsector,hadjoint⟩

end Froehlich
