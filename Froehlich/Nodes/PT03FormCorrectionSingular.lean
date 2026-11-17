import Froehlich.Nodes.UV01CorrectionConvergence
import Froehlich.Nodes.SP03Correction

/-! The UV singular correction is SP03's actual threshold correction.
The inverse identification uses full original-domain form representatives
and their proved inverse equations, rather than a supplied equality. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich
variable (e : ℝ) (P : GW.Space) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
  (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant * |g| ≤ 1/2)

theorem singularTwoSectorReferenceInverse_weak (f w : HighEnergySpace P 2) :
    (compressedFiberFormData g P 2 none).form w (singularTwoSectorReferenceInverse e P he g hg hs f) -
      ((e+1 : ℝ) : ℂ) * ⟪highEnergyEmbedding P 2 w,
        highEnergyEmbedding P 2 (singularTwoSectorReferenceInverse e P he g hg hs f)⟫_ℂ = ⟪w,f⟫_ℂ := by
  have haux : ∀ f w : HighEnergySpace (-(-P)) 2,
      (compressedFiberFormData g (-(-P)) 2 none).form w
        (auxiliaryCompressedEnergyInverse 2 e (-P) (by norm_num) he g hg hs f) -
      ((e-1+(2 : ℝ) : ℝ) : ℂ) * ⟪highEnergyEmbedding (-(-P)) 2 w,
        highEnergyEmbedding (-(-P)) 2
          (auxiliaryCompressedEnergyInverse 2 e (-P) (by norm_num) he g hg hs f)⟫_ℂ = ⟪w,f⟫_ℂ := by
    intro f w
    have hspec := auxiliaryCompressedEnergyOperator_spec 2 e (-P) (by norm_num) he g w
      (auxiliaryCompressedEnergyInverse 2 e (-P) (by norm_num) he g hg hs f)
    have hr := congrArg (fun A : HighEnergySpace (-(-P)) 2 →L[ℂ] HighEnergySpace (-(-P)) 2 => A f)
      (auxiliaryCompressedEnergyInverse_right 2 e (-P) (by norm_num) he g hg hs)
    exact hspec.symm.trans (congrArg (fun u : HighEnergySpace (-(-P)) 2 => ⟪w,u⟫_ℂ) hr)
  have hfw := haux f w
  change (compressedFiberFormData g (-(-P)) 2 none).form w
      (auxiliaryCompressedEnergyInverse 2 e (-P) (by norm_num) he g hg hs f) -
    ((e-1+(2 : ℝ) : ℝ) : ℂ) * ⟪highEnergyEmbedding (-(-P)) 2 w,
      highEnergyEmbedding (-(-P)) 2
        (auxiliaryCompressedEnergyInverse 2 e (-P) (by norm_num) he g hg hs f)⟫_ℂ = ⟪w,f⟫_ℂ at hfw
  rw [show e-1+(2 : ℝ)=e+1 by ring,neg_neg] at hfw
  simpa only [singularTwoSectorReferenceInverse] using hfw

variable (hquarter : |g| ≤ 1/4) (heLower : -sectorEnergyConstant * |g|^2 ≤ e)
  (hquadratic : sectorQuadraticConstant * |g|^2 ≤ 1/8)

theorem singularTwoSectorReferenceInverse_eq_threshold :
    singularTwoSectorReferenceInverse e P he g hg hs =
      twoSectorEnergyInverse g e 0 P hquarter heLower he.2 (by norm_num) hquadratic := by
  apply ContinuousLinearMap.ext
  intro f
  have hr : twoSectorOperator g P (e+1)
      (singularTwoSectorReferenceInverse e P he g hg hs f) = f := by
    apply ext_inner_left ℂ
    intro w
    rw [twoSectorOperator_spec]
    exact singularTwoSectorReferenceInverse_weak e P he g hg hs f w
  have hl := twoSectorEnergyInverse_left_apply g e 0 P hquarter heLower he.2 (by norm_num)
    hquadratic (singularTwoSectorReferenceInverse e P he g hg hs f)
  simp only [sub_zero] at hl
  exact hl.symm.trans (congrArg
    (twoSectorEnergyInverse g e 0 P hquarter heLower he.2 (by norm_num) hquadratic) hr)

theorem singularEnergySchurCorrection_eq_threshold :
    singularEnergySchurCorrection e P he g hg hs =
      onePhononHighCorrection g e 0 P hquarter heLower he.2 (by norm_num) hquadratic := by
  unfold singularEnergySchurCorrection onePhononHighCorrection
  rw [singularTwoSectorReferenceInverse_eq_threshold e P he g hg hs hquarter heLower hquadratic]

end Froehlich
