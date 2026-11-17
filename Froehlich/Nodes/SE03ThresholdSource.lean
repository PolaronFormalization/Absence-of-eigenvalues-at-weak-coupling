import Froehlich.Nodes.SE03ZeroTranslation
import Froehlich.Nodes.SE03SourcePairing

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2)
    (hquarter : |g| ≤ 1/4) (heLower : -sectorEnergyConstant*|g|^2 ≤ e)
    (hquadratic : sectorQuadraticConstant*|g|^2 ≤ 1/8)

/-- The first zero-momentum source equality in the saturation proof, on all Q1 tests. -/
theorem se03_threshold_source_pairing
    (hanchor : auxiliarySelfEnergy e 0 he g hg hs = e) (w : OneParticleEnergySpace 0) :
    translatedThresholdForm e he g hquarter heLower hquadratic 0 (by simp)
        w (groundSourceOneEnergy e he g hg hs) =
      se02RightLoad e he g hg hs w-
        ((e/(1+e) : ℝ) : ℂ)*(starRingEnd ℂ) (translatedLinearSource g 0 w) := by
  let f0 := groundSourceOneEnergy e he g hg hs
  have hbase := congrArg (fun L : ConjugateLoad (OneParticleEnergySpace 0) => L w)
    (se02_threshold_source_dual_identity e he g hg hs hquarter heLower hquadratic)
  have hbase' : ⟪w,f0⟫_ℂ-((1+e : ℝ) : ℂ)*
      ⟪oneParticleEnergyEmbedding 0 w,oneParticleEnergyEmbedding 0 f0⟫_ℂ-
      ⟪w,onePhononHighCorrection g e 0 0 hquarter heLower he.2 (by norm_num) hquadratic f0⟫_ℂ =
        se02RightLoad e he g hg hs w := by
    change ⟪w,(1-(((1+e : ℝ) : ℂ) • onePhononMassOperator 0)-
      onePhononHighCorrection g e 0 0 hquarter heLower he.2 (by norm_num) hquadratic) f0⟫_ℂ = _ at hbase
    simpa only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.one_apply,
      ContinuousLinearMap.smul_apply,inner_sub_right,inner_smul_right,
      pt03_onePhononMassOperator_pairing] using hbase
  have hform := untranslatedThresholdForm_components e he g hquarter heLower hquadratic 0 (by simp) w f0
  have hell := se03_ground_source_linear_pairing_of_anchor e he g hg hs hanchor
  unfold translatedThresholdForm
  rw [se03_energyTranslation_zero_symm,se03_energyTranslation_zero_symm]
  rw [hform,hbase',se03_sourceOperator_zero_pairing,hell]
  simp only [norm_zero,zero_pow (by norm_num : (2 : ℕ) ≠ 0),sub_zero,
    div_eq_mul_inv,Complex.ofReal_mul,Complex.ofReal_inv]
  ring

end Froehlich
