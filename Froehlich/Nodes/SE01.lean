import Froehlich.Nodes.SE01HighInverse
import Froehlich.Nodes.SE01CutoffInverse
import Froehlich.Nodes.SE01RadialSource
import Froehlich.Nodes.SE01Lambda
import Froehlich.Nodes.PT02
import Froehlich.Nodes.PT03FormCorrectionGround

/-! SE01 / lem:groundPT. Actual zero-source vectors, full form equations,
fixed-reference cutoff equations and the real Seiringer lambda. No positive
c₀ assumption and no cutoff ground energy occur. -/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace Froehlich

def SE01SectorReference (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant * |g| ≤ 1/2) : Prop :=
  energyEmbedding 0 (groundSourceZeroEnergy e he g hg hs : EnergySpace 0) =
    auxiliaryGroundSourceVector e 0 he g hg hs ∧
  oneParticleEnergyEmbedding 0 (groundSourceOneEnergy e he g hg hs) =
    oneParticleExtraction (auxiliaryGroundSourceVector e 0 he g hg hs) ∧
  energyEmbedding 0 (groundSourceHighEnergy e he g hg hs : EnergySpace 0) =
    highSectorProjection 2 (auxiliaryGroundSourceVector e 0 he g hg hs) ∧
  (∀ f : OneParticleEnergySpace 0,
    ⟪f,(1-(e : ℂ) • onePhononMassOperator 0) (groundSourceOneEnergy e he g hg hs) +
      (twoSectorCoupling g 0).adjoint (groundSourceHighEnergy e he g hg hs)⟫_ℂ =
      isolatedFiberSourceLoad g 0 f) ∧
  twoSectorOperator g 0 (e+1) (groundSourceHighEnergy e he g hg hs) +
    (highEnergyEmbedding 0 2).adjoint (highEnergyEmbedding 0 2 (groundSourceHighEnergy e he g hg hs)) =
      -(twoSectorCoupling g 0 (groundSourceOneEnergy e he g hg hs)) ∧
  singularTwoSectorReferenceInverse e 0 he g hg hs
    ((highEnergyEmbedding 0 2).adjoint (highEnergyEmbedding 0 2 (groundSourceHighEnergy e he g hg hs))) =
    -(groundSourceHighEnergy e he g hg hs)-groundSourceCouplingResponseEnergy e he g hg hs ∧
  auxiliaryX e he g hg hs 0 (energyEmbedding 0 (groundSourceHighEnergy e he g hg hs : EnergySpace 0)) =
    -(energyEmbedding 0 (groundSourceHighEnergy e he g hg hs : EnergySpace 0))-
      energyEmbedding 0 (groundSourceCouplingResponseEnergy e he g hg hs : EnergySpace 0)

def SE01CutoffReference (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant * |g| ≤ 1/2) : Prop :=
  ∀ Λ : GW.Operators.PositiveCutoff,
    energyEmbedding 0 (cutoffGroundSourceZeroEnergy e he g hg hs Λ : EnergySpace 0) =
      cutoffThresholdSourceVector e he g hg hs Λ 0 ∧
    oneParticleEnergyEmbedding 0 (cutoffGroundSourceOneEnergy e he g hg hs Λ) =
      oneParticleExtraction (cutoffThresholdSourceVector e he g hg hs Λ 0) ∧
    energyEmbedding 0 (cutoffGroundSourceHighEnergy e he g hg hs Λ : EnergySpace 0) =
      highSectorProjection 2 (cutoffThresholdSourceVector e he g hg hs Λ 0) ∧
    (∀ f : OneParticleEnergySpace 0,
      ⟪f,cutoffGroundSourceOneEnergy e he g hg hs Λ⟫_ℂ +
        ⟪f,(cutoffTwoSectorCoupling g 0 Λ).adjoint (cutoffGroundSourceHighEnergy e he g hg hs Λ)⟫_ℂ -
        (e : ℂ)*⟪oneParticleEnergyEmbedding 0 f,
          oneParticleEnergyEmbedding 0 (cutoffGroundSourceOneEnergy e he g hg hs Λ)⟫_ℂ =
        isolatedCutoffFiberSourceLoad g 0 Λ.val f) ∧
    (∀ w : HighEnergySpace 0 2,
      (fiberFormData g 0 (some Λ)).form (w : EnergySpace 0)
          (cutoffGroundSourceHighEnergy e he g hg hs Λ : EnergySpace 0) -
        (e : ℂ)*⟪energyEmbedding 0 (w : EnergySpace 0),
          energyEmbedding 0 (cutoffGroundSourceHighEnergy e he g hg hs Λ : EnergySpace 0)⟫_ℂ =
        -⟪w,cutoffTwoSectorCoupling g 0 Λ (cutoffGroundSourceOneEnergy e he g hg hs Λ)⟫_ℂ) ∧
    cutoffTwoSectorReferenceInverse e 0 he g hg hs Λ
      ((highEnergyEmbedding 0 2).adjoint (highEnergyEmbedding 0 2 (cutoffGroundSourceHighEnergy e he g hg hs Λ))) =
      -(cutoffGroundSourceHighEnergy e he g hg hs Λ)-cutoffGroundSourceCouplingResponseEnergy e he g hg hs Λ ∧
    cutoffAuxiliaryX e he Λ g hg hs 0
      (energyEmbedding 0 (cutoffGroundSourceHighEnergy e he g hg hs Λ : EnergySpace 0)) =
      -(energyEmbedding 0 (cutoffGroundSourceHighEnergy e he g hg hs Λ : EnergySpace 0))-
        energyEmbedding 0 (cutoffGroundSourceCouplingResponseEnergy e he g hg hs Λ : EnergySpace 0)

def SE01FieldReference (C : ℝ) (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant * |g| ≤ 1/2) : Prop :=
  MemLp (fun k : GW.Space => (‖k‖ : ℂ)*oneParticleEnergyEmbedding 0 (groundSourceOneEnergy e he g hg hs) k) 2 volume ∧
  (groundSourceRadialVector e he g hg hs =ᵐ[volume]
    (fun k => (‖k‖ : ℂ)*oneParticleEnergyEmbedding 0 (groundSourceOneEnergy e he g hg hs) k)) ∧
  numberFormEmbedding (groundSourceZeroNumber e he g hg hs) = auxiliaryGroundSourceVector e 0 he g hg hs ∧
  (∀ (K : Set GW.Space) (hK : MeasurableSet K) (hKb : Bornology.IsBounded K)
    (R : ℝ) (hKR : ∀ k ∈ K, ‖k‖ ≤ R),
    LpToLpRestrictCLM GW.Space GW.Fock.Carrier ℂ volume 2 K
      (annihilationField (groundSourceZeroNumber e he g hg hs)) =
    (HighSectorSpace 0).subtypeL.compLp
      (localSingularInverseField 0 e 0 (by norm_num) he g hg hs K hK hKb
        (sourcePullthroughLocalField K (auxiliaryGroundSourceVector e 0 he g hg hs)
          (fun k => (fiberFormFactor g k : ℂ)) (regularSource_local_formFactor_memLp g K hK R hKR)))) ∧
  (∀ᵐ k ∂volume, annihilationField (groundSourceZeroNumber e he g hg hs) k =
    (fiberFormFactor g k : ℂ) • auxiliaryZ e k he g hg hs
      (GW.Fock.vacuum-auxiliaryGroundSourceVector e 0 he g hg hs)) ∧
  Continuous (groundSourceLambda e he g hg hs) ∧
  (∀ k : GW.Space, |groundSourceLambda e he g hg hs k| ≤ C ∧
    (groundSourceLambda e he g hg hs k : ℂ) =
      ⟪GW.Fock.vacuum-auxiliaryGroundSourceVector e k he g hg hs,
        auxiliaryZ e k he g hg hs (GW.Fock.vacuum-auxiliaryGroundSourceVector e 0 he g hg hs)⟫_ℂ +
      ⟪auxiliaryGroundSourceVector e k he g hg hs,
        auxiliaryX e he g hg hs 0 (auxiliaryGroundSourceVector e 0 he g hg hs)⟫_ℂ) ∧
  kernelConstant e he g hg hs 0 = (1+e)⁻¹-groundSourceLambda e he g hg hs 0 ∧
  ∀ k : GW.Space, kernelPsi e he g hg hs 0 k =
    groundSourceLambda e he g hg hs 0-groundSourceLambda e he g hg hs k

def SE01FixedReference (C : ℝ) (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant * |g| ≤ 1/2) : Prop :=
  SE01SectorReference e he g hg hs ∧ SE01CutoffReference e he g hg hs ∧ SE01FieldReference C e he g hg hs

theorem finalSE01_uniform : ∃ C : ℝ, 0 < C ∧
    ∀ (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
      (hs : auxiliaryResolventConstant * |g| ≤ 1/2) (hquarter : |g| ≤ 1/4)
      (heLower : -sectorEnergyConstant * |g|^2 ≤ e) (hquadratic : sectorQuadraticConstant * |g|^2 ≤ 1/8),
      SE01FixedReference C e he g hg hs := by
  obtain ⟨C,hC,hBound⟩ := groundSourceLambda_uniform_bound
  refine ⟨C,hC,?_⟩
  intro e he g hg hs hquarter heLower hquadratic
  refine ⟨?_,?_,?_⟩
  · exact ⟨groundSourceZeroEnergy_physical e he g hg hs,groundSourceOneEnergy_physical e he g hg hs,
      groundSourceHighEnergy_physical e he g hg hs,groundSource_one_equation e he g hg hs,
      groundSource_high_shifted_equation e he g hg hs,
      groundSource_high_inverse_energy e he g hg hs hquarter heLower hquadratic,
      groundSource_high_inverse_physical e he g hg hs hquarter heLower hquadratic⟩
  · intro Λ
    exact ⟨cutoffGroundSourceZeroEnergy_physical e he g hg hs Λ,
      cutoffGroundSourceOneEnergy_physical e he g hg hs Λ,cutoffGroundSourceHighEnergy_physical e he g hg hs Λ,
      cutoffGroundSource_one_equation e he g hg hs Λ,cutoffGroundSource_high_equation_test e he g hg hs Λ,
      cutoffGroundSource_high_inverse_energy e he g hg hs Λ,cutoffGroundSource_high_inverse_physical e he g hg hs Λ⟩
  · refine ⟨oneParticleRadial_memLp (groundSourceOneEnergy e he g hg hs),groundSourceRadialVector_ae e he g hg hs,?_,
      groundSource_zero_pullthrough_local e he g hg hs,groundSource_zero_pullthrough e he g hg hs,
      groundSourceLambda_continuous e he g hg hs,?_,kernelConstant_zero_lambda e he g hg hs,
      kernelPsi_zero_lambda e he g hg hs⟩
    · rw [groundSourceZeroNumber_eq,groundSourceNumber_physical]
    · intro k
      exact ⟨hBound e he g hg hs k,groundSourceLambda_physical e he g hg hs k⟩

theorem finalSE01 : ∃ s : ℝ, 0 < s ∧ ∃ C : ℝ, 0 < C ∧ ∀ g : ℝ, |g| < s →
    ∃ he : groundEnergy (fiberHamiltonian g 0) ∈ Set.Icc (-1/4 : ℝ) 0,
    ∃ hg : |g| ≤ 1, ∃ hs : auxiliaryResolventConstant * |g| ≤ 1/2,
    ∃ hquarter : |g| ≤ 1/4,
    ∃ heLower : -sectorEnergyConstant * |g|^2 ≤ groundEnergy (fiberHamiltonian g 0),
    ∃ hquadratic : sectorQuadraticConstant * |g|^2 ≤ 1/8,
      SE01FixedReference C (groundEnergy (fiberHamiltonian g 0)) he g hg hs := by
  obtain ⟨s,hs,hSmall⟩ := pt03_ground_reference_smallness
  obtain ⟨C,hC,hUniform⟩ := finalSE01_uniform
  refine ⟨s,hs,C,hC,?_⟩
  intro g hgSmall
  obtain ⟨he,hg,haux,hquarter,heLower,hquadratic⟩ := hSmall g hgSmall
  exact ⟨he,hg,haux,hquarter,heLower,hquadratic,
    hUniform _ he g hg haux hquarter heLower hquadratic⟩

end Froehlich
